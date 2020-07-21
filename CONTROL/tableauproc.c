#include "tableauproc.h"

/*  Global Variables
*/

int branch_number = 0;
long num_axioms = 0;
long dive_depth = 10;

/*  Forward Declarations
*/


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
	fprintf(GlobalOut, "# %ld beginning clauses after preprocessing and clausification\n", active->members);
	assert(proofstate);
	assert(proofcontrol);
	ClauseSet_p extension_candidates = ClauseSetCopy(bank, active);
	ClauseSet_p unit_axioms = ClauseSetAlloc();
	ClauseSet_p axioms_archive = ClauseSetCopy(bank, proofstate->unprocessed);
	tableaucontrol->unprocessed = axioms_archive;
   problemType = PROBLEM_FO;
   PList_p conjectures = PListAlloc();
   PList_p non_conjectures = PListAlloc();
   FunCode max_var = ClauseSetGetMaxVar(extension_candidates);
   ClauseSet_p start_rule_candidates = NULL;
   
   ClauseSetSplitConjectures(extension_candidates, conjectures, non_conjectures);
   
   if (PListEmpty(conjectures))
   {
		ClauseSet_p axiom_archive = proofstate->ax_archive;
		assert(axiom_archive);
		ClauseSetSplitConjectures(axiom_archive, conjectures, non_conjectures);
		if (!PListEmpty(conjectures))
		{
			fprintf(GlobalOut, "# Conjectures eliminated in preprocessing, restoring them\n");
		}
		else
		{
			fprintf(GlobalOut, "# No conjectures.\n");
			start_rule_candidates = ClauseSetAlloc();
			ClauseSetInsertSet(start_rule_candidates, extension_candidates);
		}
	}
	
	if (!PListEmpty(conjectures))
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
   TableauStack_p distinct_tableaux_stack = PStackAlloc();
   
   initial_tab->open_branches = TableauSetAlloc();
   TableauSet_p open_branches = initial_tab->open_branches;
   TableauSetInsert(open_branches, initial_tab);
   
  	if (tableauequality)
	{
		ClauseSet_p equality_axioms = EqualityAxioms(bank);
		ClauseSetInsertSet(extension_candidates, equality_axioms);
		ClauseSetFree(equality_axioms);
	}
   
   VarBankSetVCountsToUsed(bank->vars);
   VarBankSetVCountsToUsed(proofstate->freshvars);
   initial_tab->terms = bank;
   initial_tab->signature = bank->sig;
   initial_tab->state = proofstate;
   initial_tab->control = proofcontrol;
   //initial_tab->unit_axioms = unit_axioms;
   initial_tab->unit_axioms = NULL;
   
   fprintf(GlobalOut, "# %ld unit axioms, %ld start rules, and %ld other extension candidates.\n", 
																													unit_axioms->members, 
																													start_rule_candidates->members, 
																													extension_candidates->members);
   
	ClauseTableau_p beginning_tableau = NULL;
	// Print start rule candidates
	fprintf(GlobalOut, "# Start rule candidates:\n");
	ClauseSetPrint(GlobalOut, start_rule_candidates, true);
	// Create a tableau for each axiom using the start rule
   Clause_p start_label = start_rule_candidates->anchor->succ;
   while (start_label != start_rule_candidates->anchor)
   {
		if (ClauseQueryProp(start_label, CPTypeConjecture))
		{
			fprintf(GlobalOut, "#");
		}
		beginning_tableau = ClauseTableauMasterCopy(initial_tab);
		beginning_tableau ->unit_axioms = ClauseSetCopy(initial_tab->terms, unit_axioms);
		//beginning_tableau->unit_axioms = NULL;
		beginning_tableau->max_var = max_var;
		PStackPushP(distinct_tableaux_stack, beginning_tableau);
		beginning_tableau = TableauStartRule(beginning_tableau, start_label);
		start_label = start_label->succ;
	}
	
	ClauseSetFreeUnits(start_rule_candidates);
	ClauseSetInsertSet(extension_candidates, start_rule_candidates);
	
	ClauseSetFree(start_rule_candidates);

	initial_tab->unit_axioms = NULL;
	ClauseTableauFree(initial_tab);
	VarBankPushEnv(bank->vars);
	TableauStack_p new_tableaux = PStackAlloc();  // The collection of new tableaux made by extionsion rules.
	TableauStack_p old_tableaux = PStackAlloc(); // These are the garbage tableaux kept around for tracing the proof
	// New tableaux are added to the collection of distinct tableaux when the depth limit is increased, as new
	// tableaux are already at the max depth.
	fprintf(GlobalOut, "# Beginning tableaux proof search with %ld start rule applications.\n", PStackGetSP(distinct_tableaux_stack));
	//~ fprintf(GlobalOut, "# Extension candidates:\n");
	//~ ClauseSetPrint(GlobalOut, extension_candidates, true);
	//~ fprintf(GlobalOut, "# Unit axioms:\n");
	//~ ClauseSetPrint(GlobalOut, unit_axioms, true);
	
	//ClauseSetInsertSet(extension_candidates, unit_axioms); // TEMPORARY
	// BELOW IS FOR MULTIPROCESSING
	
	//~ fprintf(GlobalOut, "# Forking version..\n");
	//~ pid_t pool[num_open_branches];
	//~ int return_status[num_open_branches];
	//~ PStack_p job_bank = PStackAlloc();
	//~ for (PStackPointer j=0; j<6; j++)
	//~ {
		//~ PStack_p uniq_distinct_tableaux_stack = PStackAlloc();
		//~ pool[j] = -1;
		//~ return_status[j] = -1;
	//~ }
	//~ PStackPointer job_location = 0;
	//~ while (!PStackEmpty(distinct_tableaux_stack))
	//~ {
		//~ ClauseTableau_p starting = PStackPopP(distinct_tableaux_stack);
		//~ PStack_p uniq_dist_tab_stack = PStackElementP(job_bank, job_location);
		//~ PStackPushP(uniq_dist_tab_stack, starting);
		//~ job_location++;
		//~ job_location = job_location % 6;
	//~ }
	
	// FINISH SETUP FOR MULTIPROCESSING
	for (int current_depth = 2; current_depth < max_depth; current_depth++)
	{
		assert(proofstate);
		assert(proofcontrol);
		assert(extension_candidates);
		assert(current_depth);
		assert(new_tableaux);
		resulting_tab = ConnectionTableauProofSearch(tableaucontrol, 
														proofstate, 
														proofcontrol, 
														distinct_tableaux_stack,
														extension_candidates, 
														current_depth,
														new_tableaux);
		if (PStackEmpty(new_tableaux) && !resulting_tab && tableaucontrol->branch_saturation_enabled)
		{
			// If no new tableaux were created, we will do a "hail mary" saturation attempt on the remaining branches
			// of some tableau...
			fprintf(GlobalOut, "# No tableaux could be created.  Saturating branches.\n");
			ClauseTableau_p some_tableau = PStackElementP(distinct_tableaux_stack, 0);
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
				resulting_tab = some_tableau;
			}
		}
		if (resulting_tab)  // We successfully found a closed tableau- handle it and report results
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
			break;
		}
		//TableauStackFreeTableaux(distinct_tableaux_stack);
		PStackPushStack(old_tableaux, distinct_tableaux_stack);  // Store the old tableaux for proof printing
		PStackReset(distinct_tableaux_stack); // Reset the stack for the next stage of proof search
		fprintf(GlobalOut, "# Moving %ld tableaux to active set...\n", PStackGetSP(new_tableaux));
		PStackPushStack(distinct_tableaux_stack, new_tableaux); // Move the newly created tableaux to the working stack
		PStackReset(new_tableaux);  // Reset the storage for new tableaux created in next iteration
		fprintf(GlobalOut, "# Increasing maximum depth to %d\n", current_depth + 1);
	}
	
	// TODO
	// There needs to be something to wait here, while the various start rules are multiprocessed!
	
	// Now, we are freeing the tableaux.
	// There may be multiple references to a given tableaux around.
	// The references are in stacks of pointers, so sort/merge the stacks while discarding duplicates.
	printf("# Freeing tableaux trash\n");
	TableauStackFreeTableaux(tableaucontrol->tableaux_trash);
	printf("\n# Freeing old tableaux\n");
	TableauStackFreeTableaux(old_tableaux);
	printf("\n# Freeing distinct tableaux\n");
	TableauStackFreeTableaux(distinct_tableaux_stack);
	printf("\n# Freeing new tableaux\n");
	TableauStackFreeTableaux(new_tableaux);
	PStackFree(new_tableaux);
	PStackFree(old_tableaux);
	PStackFree(distinct_tableaux_stack);
	ClauseSetFree(extension_candidates);
	ClauseSetFree(unit_axioms);
	ClauseSetFree(axioms_archive);
	VarBankPopEnv(bank->vars);
	
	// Memory is cleaned up...
	
   if (resulting_tab) // success
   {
		//assert(resulting_tab == tableaucontrol->closed_tableau);
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
											  TableauStack_p distinct_tableaux_stack,
										     ClauseSet_p extension_candidates,
										     int max_depth,
										     TableauStack_p new_tableaux)
{
	assert(distinct_tableaux_stack);
	ClauseTableau_p active_tableau = NULL;
	ClauseTableau_p closed_tableau = NULL;
	TableauStack_p max_depth_tableaux = PStackAlloc();
	TableauStack_p newly_created_tableaux = PStackAlloc();
	
	// tableau_select method instead of iteration?
	for (PStackPointer i=0; i<PStackGetSP(distinct_tableaux_stack); i++)
	{
		//fprintf(GlobalOut, "# %ld\n", i);
		active_tableau = PStackElementP(distinct_tableaux_stack, i);
		assert(active_tableau);
		assert(active_tableau->label);
		assert(active_tableau->master == active_tableau);
		assert(active_tableau->open_branches);
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
				PStackReset(newly_created_tableaux);
				goto return_point;
			}
			else if (PStackEmpty(newly_created_tableaux)) break;
			ClauseTableau_p new = PStackPopP(newly_created_tableaux);
			PStackPushP(tableaucontrol->tableaux_trash, new);  // This is causing a double free error!!!
			selected_ref = &new;
		} while (true);
		PStackReset(newly_created_tableaux);
	}
	return_point:
	assert(PStackEmpty(newly_created_tableaux));
	PStackPushStack(new_tableaux, max_depth_tableaux);
	PStackFree(max_depth_tableaux);
	PStackFree(newly_created_tableaux);
	// Went through all possible tableaux at this depth...
	return closed_tableau;
}

ClauseTableau_p ConnectionCalculusExtendOpenBranches(ClauseTableau_p active_tableau, TableauStack_p newly_created_tableaux,
																							TableauControl_p control,
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
			number_of_extensions += ClauseTableauExtensionRuleAttemptOnBranch(control,
																									open_branch,
																									distinct_tableaux,
																									selected,
																									tab_tmp_store);
			if (control->closed_tableau)
			{
				closed_tableau = control->closed_tableau;
				fprintf(GlobalOut, "# Success\n");
				goto return_point;
			}
			selected = selected->succ;
		}
		open_branch = open_branch->succ;
	}
	
	if (num_branches_at_max_depth == open_branches->members)
	{
		PStackPushP(max_depth_tableaux, active_tableau);
	}
	
	return_point:
	PStackPushStack(newly_created_tableaux, tab_tmp_store);
	PStackFree(tab_tmp_store);
	return closed_tableau;
}
