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
   assert(!set->demod_index);
   assert(!set->demod_index);

   handle = set->anchor->succ;
   long count = 0;
   //printf("%p\n", set->anchor);
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

Clause_p ConnectionTableauBatch(TableauControl_p tableaucontrol, 
											ProofState_p proofstate, 
											ProofControl_p proofcontrol, 
											TB_p bank, 
											ClauseSet_p active, 
											int max_depth, 
											int tableauequality)
{
	fprintf(GlobalOut, "# %ld beginning clauses after preprocessing and clausification\n", active->members);
	assert(proofstate);
	assert(proofcontrol);
	ClauseSet_p extension_candidates = ClauseSetCopy(bank, active);
	ClauseSet_p unit_axioms = ClauseSetAlloc();
   problemType = PROBLEM_FO;
   PList_p conjectures = PListAlloc();
   PList_p non_conjectures = PListAlloc();
   FunCode max_var = ClauseSetGetMaxVar(extension_candidates);
   ClauseSet_p start_rule_candidates = NULL;
   
   ClauseSetSplitConjectures(extension_candidates, conjectures, non_conjectures);
   
   if (PListEmpty(conjectures))
   {
		fprintf(GlobalOut, "# No conjectures.\n");
		start_rule_candidates = ClauseSetAlloc();
		ClauseSetInsertSet(start_rule_candidates, extension_candidates);
	}
	else
	{
		fprintf(GlobalOut, "# Creating start rules for all conjectures.\n");
		start_rule_candidates = ClauseSetAlloc();
		PList_p handle;
		for(handle=conjectures->succ;
			 handle != conjectures;
			 handle = handle->succ)
		{
			Clause_p conj_handle = handle->key.p_val;
			ClauseSetExtractEntry(conj_handle);
			ClauseSetProp(conj_handle, CPTypeConjecture);
			ClauseSetInsert(start_rule_candidates, conj_handle);
		}
		
	}
	
	
	ClauseSetMoveUnits(extension_candidates, unit_axioms);
	ClauseSetCopyUnits(bank, start_rule_candidates, unit_axioms);
	
	
	PListFree(non_conjectures);
	PListFree(conjectures);
	
   assert(max_depth);
   
   ClauseTableau_p initial_tab = ClauseTableauAlloc();
   ClauseTableau_p resulting_tab = NULL;
   PStack_p distinct_tableaux_stack = PStackAlloc();
   
   initial_tab->open_branches = TableauSetAlloc();
   TableauSet_p open_branches = initial_tab->open_branches;
   TableauSetInsert(open_branches, initial_tab);
   
   
   initial_tab->terms = bank;
   initial_tab->signature = bank->sig;
   initial_tab->state = proofstate;
   initial_tab->control = proofcontrol;
   initial_tab->unit_axioms = unit_axioms;
   
   fprintf(GlobalOut, "# %ld unit axioms, %ld start rules, and %ld other extension candidates.\n", 
																													unit_axioms->members, 
																													start_rule_candidates->members, 
																													extension_candidates->members);
   
	ClauseTableau_p beginning_tableau = NULL;
	
	// Create a tableau for each axiom using the start rule
   Clause_p start_label = start_rule_candidates->anchor->succ;
   while (start_label != start_rule_candidates->anchor)
   {
		if (ClauseQueryProp(start_label, CPTypeConjecture))
		{
			fprintf(GlobalOut, "#");
		}
		beginning_tableau = ClauseTableauMasterCopy(initial_tab);
		beginning_tableau->max_var = max_var;
		//TableauMasterSetInsert(distinct_tableaux, beginning_tableau);
		PStackPushP(distinct_tableaux_stack, beginning_tableau);
		beginning_tableau = TableauStartRule(beginning_tableau, start_label);
		start_label = start_label->succ;
	}
	
	ClauseSetFreeUnits(start_rule_candidates);
	ClauseSetInsertSet(extension_candidates, start_rule_candidates);
	
	ClauseSetFree(start_rule_candidates);
	
	if (tableauequality)
	{
		ClauseSet_p equality_axioms = EqualityAxioms(bank);
		ClauseSetInsertSet(extension_candidates, equality_axioms);
		ClauseSetFree(equality_axioms);
	}
	initial_tab->unit_axioms = NULL;
	ClauseTableauFree(initial_tab);  // Free the  initialization tableau used to make the tableaux with start rule
	VarBankPushEnv(bank->vars);
	PStack_p new_tableaux = PStackAlloc();  // The collection of new tableaux made by extionsion rules.
	// New tableaux are added to the collection of distinct tableaux when the depth limit is increased, as new
	// tableaux are already at the max depth.
	fprintf(GlobalOut, " Beginning tableaux proof search with %ld start rule applications.\n", PStackGetSP(distinct_tableaux_stack));
	//~ fprintf(GlobalOut, "# Extension candidates:\n");
	//~ ClauseSetPrint(GlobalOut, extension_candidates, true);
	//~ fprintf(GlobalOut, "# Unit axioms:\n");
	//~ ClauseSetPrint(GlobalOut, unit_axioms, true);
	
	for (int current_depth = 2; current_depth < max_depth; current_depth++)
	{
		assert(proofstate);
		assert(proofcontrol);
		assert(extension_candidates);
		assert(current_depth);
		assert(new_tableaux);
		int max_num_threads = 2;
		#pragma omp parallel num_threads(4)
		{
			#pragma omp single
			resulting_tab = ConnectionTableauProofSearch(tableaucontrol, 
															proofstate, 
															proofcontrol, 
															distinct_tableaux_stack,
															extension_candidates, 
															current_depth,
															new_tableaux);
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
			ClauseTableauPrintDOTGraph(resulting_tab);
			fprintf(GlobalOut, "# SZS output start CNFRefutation for %s\n", tableaucontrol->problem_name);
			ClauseTableauPrint(resulting_tab);
			fprintf(GlobalOut, "# SZS output end CNFRefutation for %s\n", tableaucontrol->problem_name);
			fprintf(GlobalOut, "# Branches closed with saturation will be marked with an \"s\"\n");
			break;
		}
		TableauStackFreeTableaux(distinct_tableaux_stack);
		assert(PStackEmpty(distinct_tableaux_stack));
		fprintf(GlobalOut, "# Moving %ld tableaux to active set...\n", PStackGetSP(new_tableaux));
		PStackPushStack(distinct_tableaux_stack, new_tableaux);
		PStackReset(new_tableaux);
		//long num_moved = move_new_tableaux_to_distinct(distinct_tableaux, new_tableaux);
		fprintf(GlobalOut, "# Increasing maximum depth to %d\n", current_depth + 1);
	}
	
	TableauStackFreeTableaux(new_tableaux);
	PStackFree(new_tableaux);
	ClauseSetFree(extension_candidates);
	ClauseSetFree(unit_axioms);
	VarBankPopEnv(bank->vars);
   
   //printf("# Connection tableau proof search finished.\n");
   TableauStackFreeTableaux(distinct_tableaux_stack);
	PStackFree(distinct_tableaux_stack);
		
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
											  PStack_p distinct_tableaux_stack,
										     ClauseSet_p extension_candidates,
										     int max_depth,
										     PStack_p new_tableaux)
{
	assert(distinct_tableaux_stack);
	ClauseTableau_p active_tableau = NULL;
	//assert(distinct_tableaux->anchor->master_succ);
	//ClauseTableau_p active_tableau = distinct_tableaux->anchor->master_succ;
	
	// tableau_select method instead of iteration?
	 
	//while (active_tableau != distinct_tableaux->anchor) // iterate over the active tableaux
	for (PStackPointer i=0; i<PStackGetSP(distinct_tableaux_stack); i++)
	{
		//fprintf(GlobalOut, "# %ld\n", i);
		active_tableau = PStackElementP(distinct_tableaux_stack, i);
		assert(active_tableau);
		assert(active_tableau->label);
		assert(active_tableau->master == active_tableau);
		assert(active_tableau->open_branches);
		
		//~ #ifndef DNDEBUG
		//~ ClauseTableauAssertCheck(active_tableau);
		//~ #endif
		
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
																					   NULL,
																					   extension_candidates,
																					   max_depth);
		if (closed_tableau)
		{
			return closed_tableau;
		}
		//TableauMasterSetExtractEntry(active_tableau);
		//ClauseTableauFree(active_tableau);
		//active_tableau = distinct_tableaux->anchor->master_succ;
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
