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

/*  Return a clause set of equality axioms appropriate for alternating
 *  path relevance.  If substitution is true, create substitution axioms
 *  for all non-internal symbols and are not symbols resulting from
 *  skolemization.
 *
*/

ClauseSet_p EqualityAxiomsWithSubstitution(TB_p bank, ClauseSet_p set, bool substitution)
{
	Sig_p sig = bank->sig;
	long *symbol_distrib = SizeMalloc((sig->size)*sizeof(long));
	for(long i=0; i< sig->size; i++)
	{
		symbol_distrib[i] = 0;
	}
	ClauseSetAddSymbolDistribution(set, symbol_distrib);
	//Setup
	printf("# Creating equality axioms\n");
	Type_p i_type = bank->sig->type_bank->i_type;
	Term_p x = VarBankGetFreshVar(bank->vars, i_type);
	Term_p y = VarBankGetFreshVar(bank->vars, i_type);
	Term_p z = VarBankGetFreshVar(bank->vars, i_type);
	ClauseSet_p equality_axioms = ClauseSetAlloc();

	// Reflexivity
	Eqn_p x_equals_x = EqnAlloc(x, x, bank, true);
	Clause_p clause1 = ClauseAlloc(x_equals_x);
	ClauseRecomputeLitCounts(clause1);
	ClauseSetInsert(equality_axioms, clause1);

	// Symmetry clause 1
	Eqn_p y_equals_x = EqnAlloc(y, x, bank, true);
	Eqn_p x_neq_y = EqnAlloc(x, y, bank, false);
	EqnListAppend(&y_equals_x, x_neq_y);
	Clause_p clause2 = ClauseAlloc(y_equals_x);
	ClauseRecomputeLitCounts(clause2);
	ClauseSetInsert(equality_axioms, clause2);


	// Symmetry clause 2
	Eqn_p x_equals_y = EqnAlloc(x, y, bank, true);
	Eqn_p y_neq_x = EqnAlloc(y, x, bank, false);
	EqnListAppend(&x_equals_y, y_neq_x);
	Clause_p clause3 = ClauseAlloc(x_equals_y);
	ClauseRecomputeLitCounts(clause2);
	ClauseSetInsert(equality_axioms, clause3);

	// Transitivity
	Eqn_p x_equals_z = EqnAlloc(x, z, bank, true);
	Eqn_p x_neq_y2 = EqnAlloc(x, y, bank, false);
	Eqn_p y_neq_z = EqnAlloc(y, z, bank, false);
	EqnListAppend(&x_equals_z, x_neq_y2);
	EqnListAppend(&x_equals_z, y_neq_z);
	Clause_p clause4 = ClauseAlloc(x_equals_z);
	ClauseRecomputeLitCounts(clause4);
	ClauseSetInsert(equality_axioms, clause4);

	//printf("# (1) Created %ld equality axioms.\n", equality_axioms->members);
	//ClauseSetPrint(stdout, equality_axioms, true);
	// Function/Predicate equality substitution axioms
	// There must be one for every f-code of a pred or non const func.

	FunCode f_count = sig->f_count; // Max used f_code

	if (substitution)
	{
		for (FunCode f_code = sig->internal_symbols + 1; f_code <= f_count; f_code++)
		{
			int arity = SigFindArity(sig, f_code);
			if (!arity || !symbol_distrib[f_code]) continue;
			PStack_p x_variables = PStackAlloc();
			PStack_p y_variables = PStackAlloc();
			Term_p x_0 = VarBankGetFreshVar(bank->vars, i_type);
			PStackPushP(x_variables, x_0);
			Term_p y_0 = VarBankGetFreshVar(bank->vars, i_type);
			//Term_p y_0 = VarBankGetAltVar(bank->vars, x_0);
			PStackPushP(y_variables, y_0);
			Eqn_p subst_axiom = EqnAlloc(x_0, y_0, bank, false);
			for (int i=1; i<arity; i++)
			{
				Term_p x_i = VarBankGetFreshVar(bank->vars, i_type);
				PStackPushP(x_variables, x_i);
				Term_p y_i = VarBankGetFreshVar(bank->vars, i_type);
				//Term_p y_i = VarBankGetAltVar(bank->vars, x_i);
				PStackPushP(y_variables, y_i);
				Eqn_p xi_neq_yi = EqnAlloc(x_i, y_i, bank, false);
				EqnListAppend(&subst_axiom, xi_neq_yi);
			}

			Term_p left_handle = TermDefaultCellAlloc();
			left_handle->arity = arity;
			left_handle->args = TermArgArrayAlloc(arity);
			left_handle->f_code = f_code;

			for (int i=0; i<arity; i++)
			{
				left_handle->args[i] = PStackElementP(x_variables, i);
			}
			left_handle->v_count = arity;
			left_handle = TBTermTopInsert(bank, left_handle);
			TypeInferSort(bank->sig, left_handle, NULL);
			Term_p right_handle = NULL;
			if (SigIsFunction(sig, f_code))
			{
				right_handle = TermDefaultCellAlloc();
				right_handle->arity = arity;
				right_handle->f_code = f_code;
				right_handle->args = TermArgArrayAlloc(arity);
				for (int i=0; i<arity; i++)
				{
					right_handle->args[i] = PStackElementP(y_variables, i);
				}
				right_handle->v_count = arity;
				right_handle = TBTermTopInsert(bank, right_handle);
				TypeInferSort(bank->sig, right_handle, NULL);
				Eqn_p final = EqnAlloc(left_handle, right_handle, bank, true);
				EqnListAppend(&subst_axiom, final);
			}
			else if (SigIsPredicate(sig, f_code))
			{
				right_handle = bank->true_term;
				assert(left_handle);
				assert(right_handle);
				Eqn_p seq = EqnAlloc(left_handle, right_handle, bank, false);
				EqnListAppend(&subst_axiom, seq);

				left_handle = TermDefaultCellAlloc();
				left_handle->arity = arity;
				left_handle->args = TermArgArrayAlloc(arity);
				left_handle->f_code = f_code;
				//left_handle->type = SigGetType(bank->sig, f_code);
				for (int i=0; i<arity; i++)
				{
					left_handle->args[i] = PStackElementP(y_variables, i);
				}
				left_handle->v_count = arity;
				left_handle = TBTermTopInsert(bank, left_handle);
				TypeInferSort(bank->sig, left_handle, NULL);
				Eqn_p final = EqnAlloc(left_handle, right_handle, bank, true);
				EqnListAppend(&subst_axiom, final);
			}
			else // These are skolem symbols I think
			{
				//printf("What is this f_code %s\n", SigFindName(sig, f_code));
				EqnListFree(subst_axiom);
				PStackFree(x_variables);
				PStackFree(y_variables);
				continue;
			}

			Clause_p subst_axiom_clause = ClauseAlloc(subst_axiom);
			ClauseRecomputeLitCounts(subst_axiom_clause);
			ClauseSetInsert(equality_axioms, subst_axiom_clause);
			//printf("Substitution axiom:\n");
			//ClausePrint(GlobalOut, subst_axiom_clause, true);
			//printf("\n");
			PStackFree(x_variables);
			PStackFree(y_variables);
		}
	}

	SizeFree(symbol_distrib,(sig->size)*sizeof(long));
	//printf("# Created %ld equality axioms.\n", equality_axioms->members);
	//ClauseSetPrint(stdout, equality_axioms, true);
	return equality_axioms;
}




// End of file
