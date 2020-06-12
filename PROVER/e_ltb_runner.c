/*-----------------------------------------------------------------------

File  : e_ltb_runner.c

Author: Stephan Schulz

Contents

Hack for the LTB category of CASC-2012 (rehacked for later versions) -
parse an LTB spec file, and run E on the various problems.

  Copyright 2010-2019 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

Changes

<1> Mon Jun 28 02:15:05 CEST 2010
    New

-----------------------------------------------------------------------*/

#include <clb_defines.h>
#include <cio_commandline.h>
#include <cio_output.h>
#include <ccl_relevance.h>
#include <cio_signals.h>
#include <ccl_formulafunc.h>
#include <cco_batch_spec.h>
#include <ccl_sine.h>
#include <e_version.h>


/*---------------------------------------------------------------------*/
/*                  Data types                                         */
/*---------------------------------------------------------------------*/

#define NAME         "e_ltb_runner"

typedef enum
{
   OPT_NOOPT=0,
   OPT_HELP,
   OPT_VERSION,
   OPT_VERBOSE,
   OPT_OUTPUT,
   OPT_OUTDIR,
   OPT_VARIANTS,
   OPT_NEWSCHEDULE,
   OPT_INTERACTIVE,
   OPT_PRINT_STATISTICS,
   OPT_SILENT,
   OPT_OUTPUTLEVEL,
   OPT_GLOBAL_WTCLIMIT,
   OPT_DUMMY
}OptionCodes;



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/


OptCell opts[] =
{
   {OPT_HELP,
    'h', "help",
    NoArg, NULL,
    "Print a short description of program usage and options."},

   {OPT_VERSION,
    'V', "version",
    NoArg, NULL,
    "Print the version number of the prover. Please include this"
    " with all bug reports (if any)."},

   {OPT_VERBOSE,
    'v', "verbose",
    OptArg, "1",
    "Verbose comments on the progress of the program. This differs "
    "from the output level (below) in that technical information is "
    "printed to stderr, while the output level determines which "
    "logical manipulations of the clauses are printed to stdout."},

   {OPT_OUTPUT,
    'o', "output-file",
    ReqArg, NULL,
   "Redirect output into the named file."},

   {OPT_OUTDIR,
    'd', "output-dir",
    ReqArg, NULL,
   "Directory for individual problem output files. Default is the current"
    " working directory."},

   {OPT_VARIANTS,
    0, "variants27",
    NoArg,  NULL,
    "Handle different variants for each problem base name as required for "
    "CASC-27. This is very specific hack."},

   {OPT_INTERACTIVE,
    'i', "interactive",
    NoArg, NULL,
    "For each batch file, enter interactive mode after processing "
    "batch the batch problems. Interactive mode allows the processing "
    "of additional jobs with respect to the loaded axioms set. Jobs "
    "are entered via stdin and print to stdout."},

   {OPT_SILENT,
    's', "silent",
    NoArg, NULL,
    "Equivalent to --output-level=0."},

   {OPT_OUTPUTLEVEL,
    'l', "output-level",
    ReqArg, NULL,
    "Select an output level, greater values imply more verbose "
    "output. Level 0 produces "
    "nearly no output, level 1 will output each clause as it is "
    "processed, level 2 will output generating inferences, "
    "level 3 will give a full protocol including rewrite steps and "
    "level 4 will include some internal clause renamings. Levels >= 2"
    " also imply PCL2 or TSTP formats (which can be post-processed"
    " with suitable tools)."},

   {OPT_GLOBAL_WTCLIMIT,
    'w', "wtc-limit",
    ReqArg, NULL,
    "Set the global wall-clock limit for each batch (if any)."},

   {OPT_NOOPT,
    '\0', NULL,
    NoArg, NULL,
    NULL}
};

char              *outname        = NULL;
char              *outdir         = NULL;
long              total_wtc_limit = 0;
bool              interactive     = false;
bool              app_encode      = false;
bool              use_variants    = false;
ProblemType problemType  = PROBLEM_NOT_INIT;


char* variants[] = {"+1", "+2", "_1", "_2", NULL};

/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/

CLState_p process_options(int argc, char* argv[]);
void print_help(FILE* out);

/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/

int main(int argc, char* argv[])
{
   CLState_p        state;
   Scanner_p        in;
   BatchSpec_p      spec;
   StructFOFSpec_p   ctrl;
   char             *prover    = "eprover";
   char             *category  = NULL;
   char             *train_dir = NULL;
   long             now, start, res;

   assert(argv[0]);

   InitIO(NAME);
   DocOutputFormat = tstp_format;
   OutputFormat = TSTPFormat;

   state = process_options(argc, argv);

   OpenGlobalOut(outname);

   if((state->argc < 1) || (state->argc > 2))
   {
      Error("Usage: e_ltb_runner <spec> [<path-to-eprover>] \n",
            USAGE_ERROR);
   }
   if(state->argc >= 2)
   {
      prover = state->argv[1];
   }

   in = CreateScanner(StreamTypeFile, state->argv[0], true, NULL,true);
   ScannerSetFormat(in, TSTPFormat);

   AcceptDottedId(in, "division.category");
   category = ParseDottedId(in);

   if(TestInpId(in, "division"))
   {
      //AcceptDottedId(in, "division.category.training_directory");
      AcceptDottedId(in, "division.category.training_data");
      train_dir = ParseContinous(in);
   }

   while(!TestInpTok(in, NoToken))
   {
      start = GetSecTime();
      spec = BatchSpecParse(in, prover, category, train_dir, TSTPFormat);

      /* BatchSpecPrint(GlobalOut, spec); */

      if(total_wtc_limit && !spec->total_wtc_limit)
      {
         spec->total_wtc_limit = total_wtc_limit;
      }
      if(spec->per_prob_limit<=0 && spec->total_wtc_limit<=0)
      {
         Error("Either the per-problem time limit or the global "
               "time limit must be set to a value > 0", USAGE_ERROR);
      }
      /* BatchSpecPrint(stdout, spec); */
      if(!use_variants)
      {
         ctrl = StructFOFSpecAlloc();
         BatchStructFOFSpecInit(spec, ctrl, ScannerGetDefaultDir(in));
         now = GetSecTime();
         res = BatchProcessProblems(spec, ctrl,
                                    MAX(0,spec->total_wtc_limit-(now-start)),
                                    ScannerGetDefaultDir(in),
                                    outdir);
         now = GetSecTime();
         fprintf(GlobalOut, "\n\n# == WCT: %4lds, Solved: %4ld/%4ld    ==\n",
                 now-start, res, BatchSpecProblemNo(spec));
         fprintf(GlobalOut, "# =============== Batch done ===========\n\n");
         if(interactive)
         {
            BatchProcessInteractive(spec, ctrl, stdout);
         }
         StructFOFSpecFree(ctrl);
      }
      else
      {
         BatchProcessVariants(spec, variants, start, ScannerGetDefaultDir(in), outdir);
         fprintf(GlobalOut, "# =============== Variant batch done ===========\n\n");
      }
      BatchSpecFree(spec);
   }
   DestroyScanner(in);

   if(category)
   {
      FREE(category);
   }
   if(train_dir)
   {
      FREE(train_dir);
   }

   CLStateFree(state);

   OutClose(GlobalOut);
   ExitIO();
#ifdef CLB_MEMORY_DEBUG
   MemFlushFreeList();
   MemDebugPrintStats(stdout);
#endif

   return 0;
}


/*-----------------------------------------------------------------------
//
// Function: process_options()
//
//   Read and process the command line option, return (the pointer to)
//   a CLState object containing the remaining arguments.
//
// Global Variables: opts, Verbose, TBPrintInternalInfo
//
// Side Effects    : Sets variables, may terminate with program
//                   description if option -h or --help was present
//
/----------------------------------------------------------------------*/

CLState_p process_options(int argc, char* argv[])
{
   Opt_p handle;
   CLState_p state;
   char*  arg;

   state = CLStateAlloc(argc,argv);

   while((handle = CLStateGetOpt(state, &arg, opts)))
   {
      switch(handle->option_code)
      {
      case OPT_VERBOSE:
       Verbose = CLStateGetIntArg(handle, arg);
       break;
      case OPT_HELP:
       print_help(stdout);
       exit(NO_ERROR);
      case OPT_VERSION:
       fprintf(stdout, NAME " " VERSION " " E_NICKNAME "\n");
       exit(NO_ERROR);
      case OPT_OUTPUT:
       outname = arg;
       break;
      case OPT_OUTDIR:
            outdir = arg;
            break;
      case OPT_VARIANTS:
            use_variants = true;
      case OPT_INTERACTIVE:
            interactive = true;
            break;
      case OPT_SILENT:
       OutputLevel = 0;
       break;
      case OPT_OUTPUTLEVEL:
       OutputLevel = CLStateGetIntArg(handle, arg);
       break;
      case OPT_GLOBAL_WTCLIMIT:
       total_wtc_limit = CLStateGetIntArg(handle, arg);
       break;
      default:
       assert(false && "Unknown option");
       break;
      }
   }
   return state;
}

void print_help(FILE* out)
{
   fprintf(out, "\n"
NAME " " VERSION " \"" E_NICKNAME "\"\n\
\n\
Usage: " NAME " [options] [Batchfile] [PATH_TO_EPROVER]\n\
\n\
Read a CASC LTB batch specification file and process it.\n\
\n");
   PrintOptions(stdout, opts, "Options:\n\n");
   fprintf(out, "\n\n" E_FOOTER);
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/
