#include "etab_tableauproc.h"
#define _GNU_SOURCE
#include <fcntl.h>
#include <cpp_interface.h>

/*  Global Variables
*/

int branch_number = 0;
long num_axioms = 0;
long dive_depth = 10;

/*  Forward Declarations
*/

extern void c_smoketest();

/*  Function Definitions
*/


/*
** This selection function returns the first branch found shallower than max depth.
*/

ClauseTableau_p branch_select3(TableauSet_p open_branches, int max_depth)
{
	assert(open_branches);
	ClauseTableau_p selected = NULL;
	ClauseTableau_p branch = open_branches->anchor->succ;
	while (branch != open_branches->anchor)
	{
		assert(branch);
		assert(branch->label);
		assert(branch->arity == 0);
		assert(branch->children == NULL);
		assert(branch->label);
		if (branch->depth < max_depth)
		{
			return branch;
		}
		branch = branch->succ;
	}
	return selected;
}

/*
** This selection function returns the deepest branch found shallower than max depth.
*/

ClauseTableau_p branch_select5(TableauSet_p open_branches, int max_depth)
{
	assert(open_branches);
	ClauseTableau_p selected = NULL;
	int selected_depth = 0;
	ClauseTableau_p branch = open_branches->anchor->succ;
	while (branch != open_branches->anchor)
	{
		assert(branch);
		assert(branch->label);
		assert(branch->arity == 0);
		assert(branch->children == NULL);
		assert(branch->label);
		if (branch->depth < max_depth && branch->depth > selected_depth)
		{
			selected_depth = branch->depth;
			selected = branch;
		}
		branch = branch->succ;
	}
	return selected;
}
/*
** This selection function returns the first branch found shallower than max depth that has not been previously selected.
*/

ClauseTableau_p branch_select4(TableauSet_p open_branches, int max_depth)
{
	assert(open_branches);
	ClauseTableau_p selected = NULL;
	ClauseTableau_p branch = open_branches->anchor->succ;
	while (branch != open_branches->anchor)
	{
		assert(branch);
		assert(branch->label);
		assert(branch->arity == 0);
		assert(branch->children == NULL);
		assert(branch->label);
		if (branch->depth < max_depth && !ClauseTableauQueryProp(branch, TUPHasBeenPreviouslySelected))
		{
			ClauseTableauSetProp(branch, TUPHasBeenPreviouslySelected);
			return branch;
		}
		branch = branch->succ;
	}
	return selected;
}

/*-----------------------------------------------------------------------
//
// Function: tableau_select()
//
//   This function will hopefully emulate hcb_select at some point.
//   Returns an arbitrary tableaux, but they could be ordered by
//   the number of open branches or a more sophisticated method at some point.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

ClauseTableau_p tableau_select(TableauControl_p tableaucontrol, TableauSet_p set)
{
	assert(!TableauSetEmpty(set));
	ClauseTableau_p tab = set->anchor->succ;
	return tab;
}


/*-----------------------------------------------------------------------
//
// Function: ClauseSetMoveUnits()
//
//   Move all unit-clauses from set to units, return number of
//   clauses moved.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

long ClauseSetMoveUnits(ClauseSet_p set, ClauseSet_p units)
{
   Clause_p handle;

   assert(set);
   assert(units);
   //assert(!set->demod_index);
   //assert(!set->demod_index);

   handle = set->anchor->succ;
   long count = 0;
   //printf("%p\n", set->anchor);
   while(handle != set->anchor)
   {
	   ClauseRecomputeLitCounts(handle);
		assert(handle);
      if(ClauseLiteralNumber(handle) == 1)
      {
			count++;
			handle = handle->succ;
			assert(handle->pred);
			Clause_p unit = ClauseSetExtractEntry(handle->pred);
			ClauseSetInsert(units, unit);
      }
      else
      {
			handle = handle->succ;
	  }
   }
   return count;
}

/*-----------------------------------------------------------------------
//
// Function: ClauseSetCopyUnits()
//
//   Copy all unit-clauses from set to units, return number of
//   clauses moved.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

long ClauseSetCopyUnits(TB_p bank, ClauseSet_p set, ClauseSet_p units)
{
   Clause_p handle;

   assert(set);
   assert(units);
   //assert(!set->demod_index);

   handle = set->anchor->succ;
   long count = 0;
   while(handle != set->anchor)
   {
		assert(handle);
		ClauseRecomputeLitCounts(handle);
      if(ClauseLiteralNumber(handle) == 1)
      {
			count++;
			Clause_p unit = ClauseCopy(handle, bank);
			assert(unit != handle);
			ClauseSetInsert(units, unit);
      }
		handle = handle->succ;
   }
   return count;
}

/*-----------------------------------------------------------------------
//
// Function: ClauseSetFreeUnits()
//
//   Free all unit-clauses from set to units, return number of
//   clauses freed.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

long ClauseSetFreeUnits(ClauseSet_p set)
{
   Clause_p handle;

   assert(set);
   assert(!set->demod_index);

   handle = set->anchor->succ;
   long count = 0;
   while(handle != set->anchor)
   {
		assert(handle);
      if(ClauseLiteralNumber(handle) == 1)
      {
			count++;
			handle = handle->succ;
			assert(handle->pred);
			Clause_p unit = ClauseSetExtractEntry(handle->pred);
			ClauseFree(unit);
      }
      else
      {
			handle = handle->succ;
		}
   }
   return count;
}

/*-----------------------------------------------------------------------
//  Identify a single negated conjecture to form the tableau branches.
//  If there is no conjecture return NULL.
//  Returns the first conjecture found, if there are multiple they will not affect the tableau.
/----------------------------------------------------------------------*/

WFormula_p ProofStateGetConjecture(ProofState_p state)
{
	WFormula_p handle = state->f_axioms->anchor->succ;
	while (handle != state->f_axioms->anchor)
	{
		if (FormulaIsConjecture(handle))
		{
			//FormulaSetExtractEntry(handle);
			return handle;
		}
		handle = handle->succ;
	}
	return NULL;
}

/*-----------------------------------------------------------------------
//
// Function: EtableauHailMary(...)
//
//   If no more tableaux could be created for some reason, try to do a 
//   deep saturation on a tableau that will be deleted.  If this closes 
//   the tableau return it.
//
// Side Effects    :  Calls Saturate, so many.
//
/----------------------------------------------------------------------*/

ClauseTableau_p EtableauHailMary(TableauControl_p tableaucontrol)
{
	// If no new tableaux were created, we will do a "hail mary" saturation attempt on the remaining branches
	// of some tableau...
	Warning("Hail Mary");
	fprintf(GlobalOut, "# No tableaux could be created.  Saturating branches.\n");
	if (PStackEmpty(tableaucontrol->tableaux_trash))
	{
		fprintf(GlobalOut, "# SZS status Unknown\n");
		Error("# Could not find a tableau to saturate in the trash... Exiting", RESOURCE_OUT);
	}
	ClauseTableau_p some_tableau = PStackElementP(tableaucontrol->tableaux_trash, 0);
	assert(some_tableau);
	assert(some_tableau->master == some_tableau);
	some_tableau = some_tableau->master;  // Whe want to call saturation method on the root node only
	CloseBranchesWithEprover(tableaucontrol, some_tableau, LONG_MAX);
	if (some_tableau->open_branches->members == 0)
	{
		return some_tableau;
	}
	return NULL;
}


/*-----------------------------------------------------------------------
//
// Function: EtableauGetStartRuleCandidates(...)
//
//   Find conjectures from the axiom specification, and insert them into the 
//   returned set start_rule_candidates.  If there are no conjectures found,
//   search for them in the axiom archive and do the same.  If there are really
//   no conjectures, every clause in the specification is inserted into start_rule_candidates.
//
// Side Effects    :  Memory operations, active
//
/----------------------------------------------------------------------*/

ClauseSet_p EtableauGetStartRuleCandidates(ProofState_p proofstate, ClauseSet_p active)
{
   PList_p conjectures = PListAlloc();
   PList_p non_conjectures = PListAlloc();
   ClauseSet_p start_rule_candidates = NULL;
   long number_of_conjs = 0;
   
   number_of_conjs = ClauseSetSplitConjectures(active, conjectures, non_conjectures);

   
   if (PListEmpty(conjectures))
   {
		fprintf(GlobalOut, "# No conjectures after preprocessing.  Attempting to resurrect them from ax_archive.\n");
		ClauseSet_p axiom_archive = proofstate->ax_archive;
		assert(axiom_archive);
		number_of_conjs = ClauseSetSplitConjectures(axiom_archive, conjectures, non_conjectures);
		if (PListEmpty(conjectures))
		{
			fprintf(GlobalOut, "# No conjectures.\n");
			start_rule_candidates = ClauseSetAlloc();
			ClauseSetInsertSet(start_rule_candidates, active);
			goto return_point;
		}
	}
	assert(!PListEmpty(conjectures));
	fprintf(GlobalOut, "# Creating start rules for all %ld conjectures.\n", number_of_conjs);
	start_rule_candidates = ClauseSetAlloc();
	PList_p handle;
	for(handle=conjectures->succ;
		 handle != conjectures;
		 handle = handle->succ)
	{
		Clause_p conj_handle = handle->key.p_val;
		ClauseSetExtractEntry(conj_handle);
		//ClauseSetProp(conj_handle, CPTypeConjecture);
		ClauseSetInsert(start_rule_candidates, conj_handle);
	}
		
	return_point:
	PListFree(non_conjectures);
	PListFree(conjectures);
	assert(start_rule_candidates);
	assert(!ClauseSetEmpty(start_rule_candidates));
	return start_rule_candidates;
}

/*-----------------------------------------------------------------------
//
// Function: EtableauCreateStartRules(...)
//
//   This function creates an initial "blank" tableau and creates instances
//   of the start rule for tableaux, corresponding to the clauses in start_rule_candidates.
//   They are returned in the TableauSet_p.
//
// Side Effects    :  Memory operations, proofstate->freshvars and bank->vars
//
/----------------------------------------------------------------------*/

TableauSet_p EtableauCreateStartRules(TB_p bank,
									  ClauseSet_p unit_axioms,
									  ClauseSet_p start_rule_candidates,
									  TableauControl_p tableaucontrol,
									  unsigned long maximum_depth)

{
	ProofState_p proofstate = tableaucontrol->proofstate;
	ProofControl_p proofcontrol = tableaucontrol->proofcontrol;
	ClauseTableau_p initial_tab = ClauseTableauAlloc(tableaucontrol);
	initial_tab->open_branches = TableauSetAlloc();
	TableauSet_p open_branches = initial_tab->open_branches;
	TableauSetInsert(open_branches, initial_tab);

	VarBankSetVCountsToUsed(bank->vars);
	VarBankSetVCountsToUsed(proofstate->freshvars);
	initial_tab->terms = bank;
	initial_tab->signature = bank->sig;
	initial_tab->state = proofstate;
	initial_tab->control = proofcontrol;
	initial_tab->unit_axioms = NULL;
	initial_tab->maximum_depth = maximum_depth;

	ClauseTableau_p beginning_tableau = NULL;
	TableauSet_p distinct_tableaux_set = TableauSetAlloc();
	// Create a tableau for each axiom using the start rule
	Clause_p start_label = start_rule_candidates->anchor->succ;
	while (start_label != start_rule_candidates->anchor)
	{
		beginning_tableau = ClauseTableauMasterCopy(initial_tab);
		beginning_tableau->unit_axioms = ClauseSetCopy(initial_tab->terms, unit_axioms);
		beginning_tableau = TableauStartRule(beginning_tableau, start_label);
		TableauSetInsert(distinct_tableaux_set, beginning_tableau->master);
		//ClauseTableauUpdateVariables(beginning_tableau->master); //unnecessary, is done before any uni attempts
		start_label = start_label->succ;
	}

	TableauSetExtractEntry(initial_tab);
	ClauseTableauFree(initial_tab);
	return distinct_tableaux_set;
}

TableauStack_p EtableauCreateStartRulesStack(TB_p bank,
											 ClauseSet_p unit_axioms,
											 ClauseSet_p start_rule_candidates,
											 TableauControl_p tableaucontrol,
											 unsigned long maximum_depth)
{
	PStack_p stack = PStackAlloc();
	TableauSet_p dt = EtableauCreateStartRules(bank,
											   unit_axioms,
											   start_rule_candidates,
											   tableaucontrol,
											   maximum_depth);
	while (!TableauSetEmpty(dt))
	{
		ClauseTableau_p tab = TableauSetExtractFirst(dt);
		FoldUpCloseCycle(tab);
		if (tab->open_branches->members == 0)
		{
			printf("# Found closed tableau while making start rule\n");
			tableaucontrol->closed_tableau = tab;
			while (!TableauSetEmpty(dt))
			{
				ClauseTableau_p trash = TableauSetExtractFirst(dt);
				ClauseTableauFree(trash);
			}
		}
		PStackPushP(stack, tab);
	}
	TableauSetFree(dt);
	return stack;
}


bool EtableauWait(int num_cores_available, EPCtrlSet_p process_set)
{
	bool proof_found = false;
	int num_children_exited = 0;
	while (num_children_exited < num_cores_available)
	{
		int exit_status = -1;
		int return_status = -1;
		//fprintf(stdout, "# Waiting...\n");
		pid_t exited_child = wait(&exit_status);
		if (WIFEXITED(exit_status))
		{
			return_status = WEXITSTATUS(exit_status);
		}
		else 
		{
			EPCtrlSetFree(process_set, false);
			fprintf(stderr, "(%ld) %d %s\n", (long) exited_child, exit_status, strerror(exit_status));
			fflush(stderr);
			fflush(GlobalOut);
			Error("Child did not exit normally", 1);
		}
		switch(return_status)
		{
			case PROOF_FOUND:
			{
				// kill all the children and move towards exit
				EPCtrl_p successful_process = EPCtrlSetFindProc(process_set, exited_child);
				if (successful_process)
				{
					proof_found = true;
					fprintf(stdout, "# Child (%ld) has found a proof.\n", (long) exited_child);
					fflush(stdout);
					char readbuf[EPCTRL_BUFSIZE];
					int fd_in = fileno(successful_process->pipe);
					int err = read(fd_in, readbuf, EPCTRL_BUFSIZE);
					if (err == -1)
					{
						Error("Read error", 1);
					}
					fprintf(GlobalOut, "%s\n", readbuf);
					fflush(GlobalOut);
				}
				else
				{
					Error("# A child reported success but could not be found...", 1);
				}
				EPCtrlSetFree(process_set, false);
				return proof_found;
			}
			case SATISFIABLE:
			{
				proof_found = true;
				EPCtrlSetFree(process_set, false);
				fprintf(GlobalOut, "# Satisfiable branch\n");
				fflush(GlobalOut);
				return proof_found;
			}
			case OUT_OF_MEMORY:
			{
				EPCtrlSetFree(process_set, false);
				return false;
			}
			case SYNTAX_ERROR:
			{
				EPCtrlSetFree(process_set, false);
				Error("# Syntax error", 1);
			}
			case USAGE_ERROR:
			{
				EPCtrlSetFree(process_set, false);
				Error("# Usage error", 1);
			}
			case FILE_ERROR:
			{
				EPCtrlSetFree(process_set, false);
				Error("# File error", 1);
			}
			case SYS_ERROR:
			{
				EPCtrlSetFree(process_set, false);
				Error("# Sys error", 1);
			}
			case CPU_LIMIT_ERROR:
			{
				EPCtrlSetFree(process_set, false);
				return false;
			}
			case RESOURCE_OUT:
			{
#ifndef NDEBUG
				fprintf(stdout, "# A child has run out of resources, likely tableaux.  Allowing others to continue.\n");
				fflush(stdout);
#endif
				break;
			}
			case INCOMPLETE_PROOFSTATE:
			{
				EPCtrlSetFree(process_set, false);
				Error("# Incomplete proofstate error", 1);
			}
			case OTHER_ERROR:
			{
				EPCtrlSetFree(process_set, false);
				Error("# Other error", 1);
			}
			case INPUT_SEMANTIC_ERROR:
			{
				EPCtrlSetFree(process_set, false);
				Error("# Input semantic error", 1);
			}
			case INTERFACE_ERROR:
			{
				EPCtrlSetFree(process_set, false);
				Error("# Interface error", 1);
			}
			default:
			{
				fprintf(GlobalOut, "# Received strange output from child: %d\n", return_status);
				EPCtrlSetFree(process_set, false);
				Error("# Unknown status from child", 1);
			}
		}
		num_children_exited++;
	}
	return proof_found;
}

int TableauControlGetCores(TableauControl_p tableaucontrol)
{
	int num_cores = tableaucontrol->multiprocessing_active;
	int nprocs = get_nprocs();
	fprintf(GlobalOut, "# Requested %d, %d cores available to the main process.\n", num_cores, nprocs);
	if (num_cores > nprocs)
	{
		Warning("# Requested more cores than are available to the program...");
	}
	if (num_cores == -1)
	{
		fprintf(GlobalOut, "# Using all %d available cores\n", nprocs);
		return nprocs;
	}
	return num_cores;
}
