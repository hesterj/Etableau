#include "tableauproc.h"

/*  Global Variables
*/

int branch_number = 0;
long num_axioms = 0;
long dive_depth = 10;

/*  Forward Declarations
*/

ClauseTableau_p tableau_select(TableauControl_p tableaucontrol, TableauSet_p set);


/*  Function Definitions
*/

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

int ConnectionTableauBatch(TableauControl_p tableaucontrol, 
											ProofState_p proofstate, 
											ProofControl_p proofcontrol, 
											TB_p bank, 
											ClauseSet_p active, 
											int max_depth, 
											int tableauequality)
{
	problemType = PROBLEM_FO;
	FunCode max_var = ClauseSetGetMaxVar(active);
	tableaucontrol->unprocessed = ClauseSetCopy(bank, proofstate->unprocessed);
	fprintf(GlobalOut, "# %ld beginning clauses after preprocessing and clausification\n", active->members);
	ClauseSet_p extension_candidates = ClauseSetCopy(bank, active);
  	if (tableauequality)
	{
		ClauseSet_p equality_axioms = EqualityAxioms(bank);
		ClauseSetInsertSet(extension_candidates, equality_axioms);
		ClauseSetFree(equality_axioms);
	}
	ClauseSet_p start_rule_candidates = EtableauGetStartRuleCandidates(proofstate, extension_candidates);
	
	ClauseSet_p unit_axioms = ClauseSetAlloc();
	ClauseSetMoveUnits(extension_candidates, unit_axioms);
	ClauseSetCopyUnits(bank, start_rule_candidates, unit_axioms);
   assert(max_depth);
	
	TableauSet_p distinct_tableaux_set = EtableauCreateStartRules(proofstate,
																					  proofcontrol,
																					  bank,
																					  max_var,
																					  unit_axioms,
																					  start_rule_candidates);
																					  
	ClauseSetFreeUnits(start_rule_candidates);
	ClauseSetInsertSet(extension_candidates, start_rule_candidates);
	ClauseSetFree(start_rule_candidates);
	VarBankPushEnv(bank->vars);
	TableauStack_p new_tableaux = PStackAlloc();  // The collection of new tableaux made by extionsion rules.
	
	assert(proofstate);
	assert(proofcontrol);
	assert(extension_candidates);
	assert(new_tableaux);
	assert(!ClauseSetEmpty(extension_candidates));
	ClauseTableau_p resulting_tab = NULL;
	for (int current_depth = 2; current_depth < max_depth; current_depth++)
	{
		resulting_tab = ConnectionTableauProofSearch(tableaucontrol, 
														proofstate, 
														proofcontrol, 
														distinct_tableaux_set,
														extension_candidates, 
														current_depth,
														new_tableaux);
		if (PStackEmpty(new_tableaux) && !resulting_tab && tableaucontrol->branch_saturation_enabled)
		{
			resulting_tab = EtableauHailMary(tableaucontrol);
		}
		if (resulting_tab)  // We successfully found a closed tableau- handle it and report results
		{
			EtableauStatusReport(tableaucontrol, active, resulting_tab);
			break;
		}
		fprintf(GlobalOut, "# Moving %ld tableaux to active set...\n", PStackGetSP(new_tableaux));
		while (!PStackEmpty(new_tableaux))
		{
			ClauseTableau_p distinct = PStackPopP(new_tableaux);
			TableauSetInsert(distinct_tableaux_set, distinct);
		}
		fprintf(GlobalOut, "# Increasing maximum depth to %d\n", current_depth + 1);
	}
	
	assert(TableauSetEmpty(distinct_tableaux_set));
	printf("# Freeing tableaux trash\n");
	TableauStackFreeTableaux(tableaucontrol->tableaux_trash);
	printf("\n# Freeing distinct tableaux\n");
	printf("\n# Freeing new tableaux\n");
	TableauStackFreeTableaux(new_tableaux);
	PStackFree(new_tableaux);
	TableauSetFree(distinct_tableaux_set);
	ClauseSetFree(extension_candidates);
	ClauseSetFree(unit_axioms);
	ClauseSetFree(tableaucontrol->unprocessed);
	VarBankPopEnv(bank->vars);
	
	// Memory is cleaned up...
	
   if (resulting_tab) // success
   {
		printf("# Proof search success for %s!\n", tableaucontrol->problem_name);
		//ClauseTableauPrintDOTGraph(resulting_tab);
		return 1;
	}
	// failure
	fprintf(GlobalOut, "# ConnectionTableauProofSearch returns NULL. Failure.\n");
	fprintf(GlobalOut, "# SZS status ResourceOut for %s\n", tableaucontrol->problem_name);
	return 0;
}

ClauseTableau_p ConnectionTableauProofSearch(TableauControl_p tableaucontrol,
											  ProofState_p proofstate, 
											  ProofControl_p proofcontrol, 
											  TableauSet_p distinct_tableaux_set,
										     ClauseSet_p extension_candidates,
										     int max_depth,
										     TableauStack_p new_tableaux)
{
	assert(distinct_tableaux_set);
	ClauseTableau_p active_tableau = NULL;
	ClauseTableau_p closed_tableau = NULL;
	TableauStack_p max_depth_tableaux = PStackAlloc();
	TableauStack_p newly_created_tableaux = PStackAlloc();
	
	while (!TableauSetEmpty(distinct_tableaux_set))
	{
		//fprintf(GlobalOut, "# %ld\n", i);
		active_tableau = tableau_select(tableaucontrol, distinct_tableaux_set);
		assert(active_tableau);
		assert(active_tableau->label);
		assert(active_tableau->master == active_tableau);
		assert(active_tableau->open_branches);
		TableauSetExtractEntry(active_tableau);
		ClauseTableau_ref selected_ref = &active_tableau;
		
		// At this point, there could be tableaux to be extended on at this depth in newly_created_tableaux
		do  // Attempt to create extension tableaux until they are all at max depth or a closed tableau is found
		{
			closed_tableau = ConnectionCalculusExtendOpenBranches(*selected_ref, 
																				newly_created_tableaux, 
																				tableaucontrol,
																				NULL,
																				extension_candidates,
																				max_depth, max_depth_tableaux);
			if (closed_tableau)
			{
				assert(tableaucontrol->closed_tableau);
				PStackPushStack(new_tableaux, newly_created_tableaux);
				TableauSetDrainToStack(tableaucontrol->tableaux_trash, distinct_tableaux_set);
				assert(TableauSetEmpty(distinct_tableaux_set));
				goto return_point;
			}
			else if (PStackEmpty(newly_created_tableaux)) break;
			ClauseTableau_p new = PStackPopP(newly_created_tableaux);
			selected_ref = &new;
		} while (true);
		PStackReset(newly_created_tableaux);
	}
	return_point:
	PStackPushStack(new_tableaux, max_depth_tableaux);
	PStackFree(max_depth_tableaux);
	PStackFree(newly_created_tableaux);
	// Went through all possible tableaux at this depth...
	return closed_tableau;
}

ClauseTableau_p ConnectionCalculusExtendOpenBranches(ClauseTableau_p active_tableau, TableauStack_p newly_created_tableaux,
																							TableauControl_p tableaucontrol,
																							TableauSet_p distinct_tableaux,
																							ClauseSet_p extension_candidates,
																							int max_depth, TableauStack_p max_depth_tableaux)
{
	TableauStack_p tab_tmp_store = PStackAlloc();
	ClauseTableau_p closed_tableau = NULL;
	int number_of_extensions = 0;
	int num_branches_at_max_depth = 0;
	
	TableauSet_p open_branches = active_tableau->open_branches;
	ClauseTableau_p open_branch = active_tableau->open_branches->anchor->succ;
	while (open_branch != active_tableau->open_branches->anchor) // iterate over the open branches of the current tableau
	{
		if (open_branch->depth > max_depth)
		{
			open_branch = open_branch->succ;
			num_branches_at_max_depth++;
			continue;
		}
		
		Clause_p selected = extension_candidates->anchor->succ;
		while (selected != extension_candidates->anchor) // iterate over the clauses we can split on the branch
		{
			number_of_extensions += ClauseTableauExtensionRuleAttemptOnBranch(tableaucontrol,
																									open_branch,
																									NULL,
																									selected,
																									tab_tmp_store);
			if (tableaucontrol->closed_tableau)
			{
				closed_tableau = tableaucontrol->closed_tableau;
				fprintf(GlobalOut, "# Success\n");
				goto return_point;
			}
			selected = selected->succ;
		}
		open_branch = open_branch->succ;
	}
	
	if (num_branches_at_max_depth == open_branches->members) // Save these for processing at the next depth
	{
		PStackPushP(max_depth_tableaux, active_tableau);
	}
	else  // Extended or not, active should have no references to it elsewhere and has been worked on so can be discarded
	{
		PStackPushP(tableaucontrol->tableaux_trash, active_tableau);
	}
	
	return_point:
	PStackPushStack(newly_created_tableaux, tab_tmp_store);
	PStackFree(tab_tmp_store);
	return closed_tableau;
}

ClauseTableau_p EtableauHailMary(TableauControl_p tableaucontrol)
{
	// If no new tableaux were created, we will do a "hail mary" saturation attempt on the remaining branches
	// of some tableau...
	fprintf(GlobalOut, "# No tableaux could be created.  Saturating branches.\n");
	ClauseTableau_p some_tableau = PStackElementP(tableaucontrol->tableaux_trash, 0);
	assert(some_tableau);
	assert(some_tableau->master == some_tableau);
	some_tableau = some_tableau->master;  // Whe want to call saturation method on the root node only
	BranchSaturation_p branch_saturation = BranchSaturationAlloc(tableaucontrol->proofstate, 
																					 tableaucontrol->proofcontrol, 
																					 some_tableau,
																					 LONG_MAX);
	AttemptToCloseBranchesWithSuperpositionSerial(tableaucontrol, 
																 branch_saturation);
	BranchSaturationFree(branch_saturation);
	if (some_tableau->open_branches->members == 0)
	{
		return some_tableau;
	}
	return NULL;
}

void EtableauStatusReport(TableauControl_p tableaucontrol, ClauseSet_p active, ClauseTableau_p resulting_tab)
{
	assert(resulting_tab);
	assert(resulting_tab->derivation);
	assert(PStackGetSP(resulting_tab->derivation));
	assert(resulting_tab == tableaucontrol->closed_tableau);
	
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
	
	fprintf(GlobalOut, "# SZS output start CNFRefutation for %s\n", tableaucontrol->problem_name);
	if (tableaucontrol->clausification_buffer)
	{
		fprintf(GlobalOut, "# Begin clausification derivation\n");
		fprintf(GlobalOut, "%s\n", tableaucontrol->clausification_buffer);
		fprintf(GlobalOut, "# End clausification derivation\n");
		fprintf(GlobalOut, "# Begin listing active clauses obtained from FOF to CNF conversion\n");
		ClauseSetPrint(GlobalOut, active, true);
		fprintf(GlobalOut, "# End listing active clauses.  There is an equivalent clause to each of these in the clausification!\n");
	}
	else
	{
		Error("No record of clausification?", 1);
	}
	fprintf(GlobalOut, "# Begin printing tableau\n");
	ClauseTableauPrint(resulting_tab);
	fprintf(GlobalOut, "# End printing tableau\n");
	fprintf(GlobalOut, "# SZS output end CNFRefutation for %s\n", tableaucontrol->problem_name);
	fprintf(GlobalOut, "# Branches closed with saturation will be marked with an \"s\"\n");
	return;
}

ClauseSet_p EtableauGetStartRuleCandidates(ProofState_p proofstate, ClauseSet_p active)
{
   PList_p conjectures = PListAlloc();
   PList_p non_conjectures = PListAlloc();
   ClauseSet_p start_rule_candidates = NULL;
   
   ClauseSetSplitConjectures(active, conjectures, non_conjectures);
   
   if (PListEmpty(conjectures))
   {
		ClauseSet_p axiom_archive = proofstate->ax_archive;
		assert(axiom_archive);
		ClauseSetSplitConjectures(axiom_archive, conjectures, non_conjectures);
		if (PListEmpty(conjectures))
		{
			fprintf(GlobalOut, "# No conjectures.\n");
			start_rule_candidates = ClauseSetAlloc();
			ClauseSetInsertSet(start_rule_candidates, active);
			goto return_point;
		}
	}
	assert(!PListEmpty(conjectures));
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
		
	return_point:
	PListFree(non_conjectures);
	PListFree(conjectures);
	assert(start_rule_candidates);
	assert(!ClauseSetEmpty(start_rule_candidates));
	return start_rule_candidates;
}

TableauSet_p EtableauCreateStartRules(ProofState_p proofstate, 
												  ProofControl_p proofcontrol, 
												  TB_p bank, 
												  FunCode max_var,
												  ClauseSet_p unit_axioms,
												  ClauseSet_p start_rule_candidates)
{
   ClauseTableau_p initial_tab = ClauseTableauAlloc();
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
   
	ClauseTableau_p beginning_tableau = NULL;
	TableauSet_p distinct_tableaux_set = TableauSetAlloc();
	// Create a tableau for each axiom using the start rule
   Clause_p start_label = start_rule_candidates->anchor->succ;
   while (start_label != start_rule_candidates->anchor)
   {
		beginning_tableau = ClauseTableauMasterCopy(initial_tab);
		beginning_tableau ->unit_axioms = ClauseSetCopy(initial_tab->terms, unit_axioms);
		beginning_tableau->max_var = max_var;
		beginning_tableau = TableauStartRule(beginning_tableau, start_label);
		TableauSetInsert(distinct_tableaux_set, beginning_tableau->master);
		start_label = start_label->succ;
	}
	
	ClauseTableauFree(initial_tab);
	return distinct_tableaux_set;
}
