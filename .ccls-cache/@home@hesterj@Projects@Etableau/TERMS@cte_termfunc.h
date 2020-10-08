/*-----------------------------------------------------------------------

  File  : cte_termfunc.h

  Author: Stephan Schulz

  Contents

  Most of the user-level functionality for unshared terms.

  Copyright 1998-2017 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.


  Created: Wed Feb 25 16:50:36 MET 1998 (Ripped from cte_terms.h)

-----------------------------------------------------------------------*/

#ifndef CTE_TERMFUNC

#define CTE_TERMFUNC

#include <clb_numtrees.h>
#include <cte_termvars.h>


/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/

/* Variable normalization style */
typedef enum
{
   NSNone = -1,      /* none */
   NSUnivar = 0,     /* unify all variables */
   NSAlpha = 1       /* alpha-rename variables (DeBruin) */
}VarNormStyle;

/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/


extern bool      TermPrintLists; /* Using [...] notation */
extern bool      TermPrintTypes;

#define TermStartToken (SigSupportLists?                        \
                        (FuncSymbStartToken|OpenSquare|Mult):   \
                        (FuncSymbStartToken|Mult))

void   VarPrint(FILE* out, FunCode var);
void TermPrintFO(FILE* out, Term_p term, Sig_p sig, DerefType deref);
#ifdef ENABLE_LFHO
void TermPrintHO(FILE* out, Term_p term, Sig_p sig, DerefType deref);
#define TermPrint(out, term, sig, deref) (problemType == PROBLEM_HO ? \
        TermPrintHO(out, term, sig, deref) : TermPrintFO(out, term, sig, deref))
#else
#define TermPrint(out, term, sig, deref) TermPrintFO(out, term, sig, deref)
#endif
void   TermPrintArgList(FILE* out, Term_p *args, int arity, Sig_p sig, DerefType deref);
void   TermFOOLPrint(FILE* out, Sig_p sig, Term_p form);
FuncSymbType TermParseOperator(Scanner_p in, DStr_p id);
FunCode       TermSigInsert(Sig_p sig, const char* name, int arity, bool
                            special_id, FuncSymbType type);
Term_p TermParse(Scanner_p in, Sig_p sig, VarBank_p vars);
int    TermParseArgList(Scanner_p in, Term_p** arg_anchor, Sig_p sig,
                         VarBank_p vars);
Term_p TermCopy(Term_p source, VarBank_p vars, DerefType deref);
Term_p TermCopyKeepVars(Term_p source, DerefType deref);
static inline Term_p TermEquivCellAlloc(Term_p source, VarBank_p vars);

bool   TermStructEqual(Term_p t1, Term_p t2);
bool   TermStructEqualNoDeref(Term_p t1, Term_p t2);
bool   TermStructEqualDeref(Term_p t1, Term_p t2, DerefType deref_1, DerefType deref_2);
bool   TermStructPrefixEqual(Term_p l, Term_p r, DerefType d_l, DerefType d_r, int remaining, Sig_p sig);

long   TermStructWeightCompare(Term_p t1, Term_p t2);

long   TermLexCompare(Term_p t1, Term_p t2);

bool   TermIsSubterm(Term_p super, Term_p test, DerefType deref);

bool    TermIsSubtermDeref(Term_p super, Term_p test, DerefType
            deref_super, DerefType deref_test);

long    TermWeightCompute(Term_p term, long vweight, long fweight);
#define TermWeight(term, vweight, fweight) \
        (TermIsShared(term)? \
         (assert(((term)->v_count*vweight + (term)->f_count*fweight) == TermWeightCompute((term),(vweight),(fweight))), \
          ((term)->v_count*vweight + (term)->f_count*fweight)) : \
         TermWeightCompute((term),(vweight),(fweight)))

#define TermDefaultWeight(term) TermWeightCompute((term), DEFAULT_VWEIGHT, DEFAULT_FWEIGHT)
#define TermStandardWeight(term) \
        (TermIsShared(term)? \
         (assert((term)->weight == TermDefaultWeight((term))),(term)->weight) : \
         TermDefaultWeight((term)))

long    TermFsumWeight(Term_p term, long vweight, long flimit,
                       long *fweights, long default_fweight, long* typefreqs);

long    TermNonLinearWeight(Term_p term, long vlweight, long vweight, long fweight);
long    TermSymTypeWeight(Term_p term, long vweight, long fweight, long cweight, long pweight);
long    TermDepth(Term_p term);

bool    TermIsDefTerm(Term_p term, int min_arity);

bool    TermHasFCode(Term_p term, FunCode f);

bool    TermHasUnboundVariables(Term_p term);
bool    TermIsGroundCompute(Term_p term);
/* #define TermIsGround(term)                                          \
//        (TermIsShared(term)?                                          \
//         (assert((TBTermIsGround((term))) == TermIsGroundCompute((term))),TBTermIsGround((term))): \
//         TermIsGroundCompute((term))) */
#define TermIsGround(term) \
        (TermIsShared(term)? \
         TBTermIsGround((term)): \
         TermIsGroundCompute((term)))

FunCode TermFindMaxVarCode(Term_p term);

long    VarBankCheckBindings(FILE* out, VarBank_p bank, Sig_p sig);

#define TermAddSymbolDistribution(term, dist_array)\
        TermAddSymbolDistributionLimited((term),(dist_array), LONG_MAX)
void    TermAddSymbolDistributionLimited(Term_p term, long *dist_array,
                                         long limit);
void    TermAddSymbolDistExist(Term_p term, long *dist_array,
                               PStack_p exists);
void    TermAddSymbolFeaturesLimited(Term_p term, long depth,
                                     long *freq_array, long* depth_array,
                                     long limit);
void    TermAddTypeDistribution(Term_p term, Sig_p sig, long* type_arr);

void    TermAddSymbolFeatures(Term_p term, PStack_p mod_stack,
                              long depth, long *feature_array, long offset);

void    TermComputeFunctionRanks(Term_p term, long *rank_array, long *count);
long    TermCollectPropVariables(Term_p term, PTree_p *tree,
                                 TermProperties prop);
long    TermCollectVariables(Term_p term, PTree_p *tree);

long    TermAddFunOcc(Term_p term, PDArray_p f_occur, PStack_p res_stack);

long    TermLinearize(PStack_p stack, Term_p term);

Term_p  TermCheckConsistency(Term_p term, DerefType deref);
void    TermAssertSameSort(Sig_p sig, Term_p t1, Term_p t2);
bool    TermIsUntyped(Term_p t);

Term_p TermCreatePrefix(Term_p orig, int up_to);
Term_p TermAppEncode(Term_p orig, Sig_p sig);

bool TermFindFOOLSubterm(Term_p t, PStack_p pos);

#define TERM_APPLY_APP_VAR_MULT(w, t, p) (TermIsAppliedVar(t) ? (w)*(p) : (w))

#define PRINT_HO_PAREN(out, ch) ((problemType == PROBLEM_HO) ? \
                                    (fputc((ch), (out))) : 0)
Term_p TermCopyUnifyVars(VarBank_p vars, Term_p term);
Term_p TermCopyRenameVars(NumTree_p* renaming, Term_p term);
Term_p TermCopyNormalizeVarsAlpha(VarBank_p vars, Term_p term);
Term_p TermCopyNormalizeVars(VarBank_p vars, Term_p term,
                             VarNormStyle var_norm);

/*-----------------------------------------------------------------------
//
// Function: TermEquivCellAlloc()
//
//   Return a pointer to a unshared termcell equivalent to source. If
//   source is a variable, get the cell from the varbank, otherwise
//   copy the cell via TermTopCopy().
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

static inline Term_p TermEquivCellAlloc(Term_p source, VarBank_p vars)
{
   if(TermIsVar(source))
   {
      return VarBankVarAssertAlloc(vars, source->f_code, source->type);
   }
   else
   {
      return TermTopCopy(source);
   }
}


#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/
