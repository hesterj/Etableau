#include "tableauproc.h"

/*  Global Variables
*/

int branch_number = 0;
long num_axioms = 0;
long dive_depth = 10;

/*  Forward Declarations
*/

long move_new_tableaux_to_distinct(TableauSet_p distinct_tableaux, PStack_p new_tableaux);

/*  Function Definitions
*/

long move_new_tableaux_to_distinct(TableauSet_p distinct_tableaux, PStack_p new_tableaux)
{
	long num_moved = 0;
	while (!PStackEmpty(new_tableaux))
	{
		ClauseTableau_p new_tab = PStackPopP(new_tableaux);
		//~ printf("moving %p\n", new_tab);
		//~ if (new_tab->master_set == distinct_tableaux)
		//~ {
			//~ printf("This tab is already part of distinct tableaux...\n");
		//~ }
		assert(new_tab->master_set == NULL);
		assert(new_tab->set == NULL);
		TableauMasterSetInsert(distinct_tableaux, new_tab);
		num_moved += 1;
	}
	return num_moved;
}

/*-----------------------------------------------------------------------
//
// Function: ClauseSetMoveNonUnits()
//
//   Move all unit-clauses from set to nonunits, return number of
//   clauses moved.xc
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
   assert(!set->demod_index);
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
			ClauseSetInsert(units, unit);
         //ClauseSetMoveClause(units, handle->pred);
      }
      else
      {
			handle = handle->succ;
		}
   }
   return count;
}


/*  Identify a single negated conjecture to form the tableau branches.
 *  If there is no conjecture return NULL.  
 *  Returns the first conjecture found, if there are multiple they will not affect the tableau.
 * 
*/

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

/*  As ConnectionTableauSerial, but builds tableau on all start rule
 *  applications at once.  Does not use any multhreading.
*/

Clause_p ConnectionTableauBatch(TableauControl_p tableaucontrol, ProofState_p proofstate, ProofControl_p proofcontrol, TB_p bank, ClauseSet_p active, int max_depth, int tableauequality)
{
	assert(proofstate);
	assert(proofcontrol);
	assert(active->members > 0);
   problemType = PROBLEM_FO;
   PList_p conjectures = PListAlloc();
   PList_p non_conjectures = PListAlloc();
   //bool conjectures_present = false;
   ClauseSet_p extension_candidates = NULL;
   fprintf(GlobalOut, "# %ld active clauses before start rule.\n", active->members);
   ClauseSetSplitConjectures(active, conjectures, non_conjectures);
   if (PListEmpty(conjectures))
   {
		fprintf(GlobalOut, "# No conjectures.\n");
		extension_candidates = ClauseSetCopy(bank, active);
	}
	else
	{
		//conjectures_present = true;
		extension_candidates = ClauseSetAlloc();
		PList_p handle;
		for(handle=conjectures->succ;
		handle != conjectures;
		handle = handle->succ)
		{
			Clause_p conj_handle = handle->key.p_val;
			//printf("# Conjecture clause: ");ClausePrint(GlobalOut, conj_handle, true);printf("\n");
			ClauseSetExtractEntry(conj_handle);
			ClauseSetProp(conj_handle, CPTypeConjecture);
			ClauseSetInsert(extension_candidates, conj_handle);
		}
		
	}
	PListFree(non_conjectures);
	fprintf(GlobalOut, "# %ld active clauses.  %ld extension candidates.\n", active->members, extension_candidates->members);
   assert(max_depth);
   ClauseSet_p unit_axioms = ClauseSetAlloc();
   
   ClauseTableau_p initial_tab = ClauseTableauAlloc();
   ClauseTableau_p resulting_tab = NULL;
   TableauSet_p distinct_tableaux = TableauMasterSetAlloc();
   
   initial_tab->open_branches = TableauSetAlloc();
   TableauSet_p open_branches = initial_tab->open_branches;
   TableauSetInsert(open_branches, initial_tab);
   
   FunCode max_var = ClauseSetGetMaxVar(active);
   assert(max_var <= 0);
   
   initial_tab->terms = bank;
   initial_tab->signature = NULL;
   initial_tab->state = proofstate;
   initial_tab->control = proofcontrol;
   
   //  Move all of the unit clauses to be on the initial tableau
   initial_tab->unit_axioms = unit_axioms;
   
	ClauseTableau_p beginning_tableau = NULL;
	
	// Create a tableau for each axiom using the start rule
   Clause_p start_label = extension_candidates->anchor->succ;
   while (start_label != extension_candidates->anchor)
   {
		if (ClauseQueryProp(start_label, CPTypeConjecture))
		{
			fprintf(GlobalOut, "#");
		}
		beginning_tableau = ClauseTableauMasterCopy(initial_tab);
		beginning_tableau->max_var = max_var;
		TableauMasterSetInsert(distinct_tableaux, beginning_tableau);
		beginning_tableau = TableauStartRule(beginning_tableau, start_label);
		start_label = start_label->succ;
	}
	fprintf(GlobalOut, "\n");
	if (active->members > 0)
	{
		while (!ClauseSetEmpty(active))
		{
			Clause_p non_conj = ClauseSetExtractFirst(active);
			ClauseSetInsert(extension_candidates, non_conj);
		}
	}
	if (tableauequality)
	{
		ClauseSet_p equality_axioms = EqualityAxioms(bank);
		ClauseSetInsertSet(extension_candidates, equality_axioms);
		ClauseSetFree(equality_axioms);
	}
	ClauseTableauFree(initial_tab);  // Free the  initialization tableau used to make the tableaux with start rule
	VarBankPushEnv(bank->vars);
	PStack_p new_tableaux = PStackAlloc();  // The collection of new tableaux made by extionsion rules.
	// New tableaux are added to the collection of distinct tableaux when the depth limit is increased, as new
	// tableaux are already at the max depth.
	fprintf(GlobalOut, "# Beginning tableaux proof search with %ld extension candidates.\n", extension_candidates->members);  
	for (int current_depth = 1; current_depth < max_depth; current_depth++)
	{
		assert(proofstate);
		assert(proofcontrol);
		assert(distinct_tableaux);
		assert(extension_candidates);
		assert(current_depth);
		assert(new_tableaux);
		int max_num_threads = 2;
		#pragma omp parallel num_threads(max_num_threads)
		{
			#pragma omp single
			{
				resulting_tab = ConnectionTableauProofSearch(tableaucontrol, 
																			proofstate, 
																			proofcontrol, 
																			distinct_tableaux,
																			extension_candidates, 
																			current_depth,
																			new_tableaux);
			}
		}
		if (resulting_tab)
		{
			long neg_conjectures = tableaucontrol->neg_conjectures;
			if (!tableaucontrol->satisfiable)
			{
				if(neg_conjectures)
				{
					fprintf(GlobalOut, "# SZS status Theorem for %s\n", tableaucontrol->problem_name);
				}
				else
				{
					fprintf(GlobalOut, "# SZS status Unsatisfiable for %s\n", tableaucontrol->problem_name);
				}
			}
			else
			{
				if (neg_conjectures)
				{
					fprintf(GlobalOut, "# SZS status CounterSatisfiable for %s\n", tableaucontrol->problem_name);
				}
				else
				{
					fprintf(GlobalOut, "# SZS status Satisfiable for %s\n", tableaucontrol->problem_name);
				}
			}
			//ClauseTableauPrintDOTGraph(resulting_tab);
			fprintf(GlobalOut, "# SZS output start CNFRefutation for %s\n", tableaucontrol->problem_name);
			ClauseTableauPrint(resulting_tab);
			fprintf(GlobalOut, "# SZS output end CNFRefutation for %s\n", tableaucontrol->problem_name);
			fprintf(GlobalOut, "# Branches closed with saturation will be marked with an \"s\"\n");
			break;
		}
		fprintf(GlobalOut, "# Moving %ld tableaux to active set...\n", PStackGetSP(new_tableaux));
		long num_moved = move_new_tableaux_to_distinct(distinct_tableaux, new_tableaux);
		if (num_moved == 0) printf("# No new tableaux???\n");
		fprintf(GlobalOut, "# Increasing maximum depth to %d\n", current_depth + 1);
	}
	
	PStackFree(new_tableaux);
	ClauseSetFree(extension_candidates);
	ClauseSetFree(unit_axioms);
	VarBankPopEnv(bank->vars);
   
   //printf("# Connection tableau proof search finished.\n");

   if (distinct_tableaux) // Free the tableaux
   {
		TableauMasterSetFree(distinct_tableaux);
		distinct_tableaux = NULL;
	}
   if (!resulting_tab) // failure
   {
	  fprintf(GlobalOut, "# ConnectionTableauProofSearch returns NULL. Failure.\n");
	  fprintf(GlobalOut, "# SZS status ResourceOut for %s\n", tableaucontrol->problem_name);
	  return NULL;
   }
   if (resulting_tab) // success
   {
		//assert(resulting_tab == tableaucontrol->closed_tableau);
		printf("# Proof search success!\n");
		//ClauseTableauPrintDOTGraph(resulting_tab);
		Clause_p empty = EmptyClauseAlloc();
		return empty;
	}
	
	return NULL;
}

ClauseTableau_p ConnectionTableauProofSearch(TableauControl_p tableaucontrol,
											  ProofState_p proofstate, 
											  ProofControl_p proofcontrol, 
											  TableauSet_p distinct_tableaux,
										     ClauseSet_p extension_candidates,
										     int max_depth,
										     PStack_p new_tableaux)
{
	assert(distinct_tableaux);
	assert(distinct_tableaux->anchor->master_succ);
	ClauseTableau_p active_tableau = distinct_tableaux->anchor->master_succ;
	ClauseTableau_p open_branch = NULL;
	
	// tableau_select method instead of iteration?
	 
	while (active_tableau != distinct_tableaux->anchor) // iterate over the active tableaux
	{
		assert(active_tableau->master_pred == distinct_tableaux->anchor);
		assert(active_tableau->label);
		assert(active_tableau->master_set);
		assert(active_tableau->master == active_tableau);
		
		#ifndef DNDEBUG
		ClauseTableauAssertCheck(active_tableau);
		#endif
		
		if (tableaucontrol->closed_tableau)
		{
			return tableaucontrol->closed_tableau;
		}
		if (active_tableau->open_branches->members == 0)
		{
			return active_tableau;
		}
		
		ClauseTableau_p closed_tableau = ConnectionCalculusExtendOpenBranches(active_tableau, 
																					   new_tableaux, 
																					   tableaucontrol,
																					   distinct_tableaux,
																					   extension_candidates,
																					   max_depth);
		if (closed_tableau)
		{
			return closed_tableau;
		}
		TableauMasterSetExtractEntry(active_tableau);
		ClauseTableauFree(active_tableau);
		active_tableau = distinct_tableaux->anchor->master_succ;
	}
	return NULL;  // Went through all possible tableaux... failure
}

ClauseTableau_p ConnectionCalculusExtendOpenBranches(ClauseTableau_p active_tableau, PStack_p new_tableaux,
																							TableauControl_p control,
																							TableauSet_p distinct_tableaux,
																							ClauseSet_p extension_candidates,
																							int max_depth)
{
	PStack_p tab_tmp_store = PStackAlloc();
	int number_of_extensions = 0;
	
	ClauseTableau_p open_branch = active_tableau->open_branches->anchor->succ;
	while (open_branch != active_tableau->open_branches->anchor) // iterate over the open branches of the current tableau
	{
		if (open_branch->depth > max_depth)
		{
			open_branch = open_branch->succ;
			continue;
		}
		
		Clause_p selected = extension_candidates->anchor->succ;
		while (selected != extension_candidates->anchor) // iterate over the clauses we can split on the branch
		{
			number_of_extensions += ClauseTableauExtensionRuleAttemptOnBranch(control,
																									open_branch,
																									distinct_tableaux,
																									selected,
																									tab_tmp_store);
			if (control->closed_tableau)
			{
				fprintf(GlobalOut, "# Success\n");
				return control->closed_tableau;
			}
			selected = selected->succ;
		}
		if (number_of_extensions == 0)
		{
			//fprintf(GlobalOut, "Unextendable branch... discarding tableaux\n");
			while (PStackGetSP(tab_tmp_store))
			{
				ClauseTableau_p trash = PStackPopP(tab_tmp_store);
				ClauseTableauFree(trash);
			}
			break;
		}
		else if (number_of_extensions > 0) // If we extended on the open branch with one or more clause, we need to move to a new active tableau.
		{
			PStackPushStack(new_tableaux, tab_tmp_store);
			break;
		}
		else 
		{
			Error("ConnectionCalculusExtendOpenBranches error.", 1);
		}
		open_branch = open_branch->succ;
	}
	PStackFree(tab_tmp_store);
	return NULL;
}
