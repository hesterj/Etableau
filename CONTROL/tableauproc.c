#include "tableauproc.h"
#define _GNU_SOURCE
#include <fcntl.h>

/*  Global Variables
*/

int branch_number = 0;
long num_axioms = 0;
long dive_depth = 10;

/*  Forward Declarations
*/

ClauseTableau_p tableau_select(TableauControl_p tableaucontrol, TableauSet_p set);
ClauseTableau_p branch_select(TableauSet_p open_branches, int max_depth);


/*  Function Definitions
*/

ClauseTableau_p branch_select(TableauSet_p open_branches, int max_depth)
{
	int deepest_depth = 0;
	ClauseTableau_p deepest = NULL;
	ClauseTableau_p branch = open_branches->anchor->succ;
	while (branch != open_branches->anchor)
	{
		if (branch->depth > deepest_depth && branch->depth <= max_depth)
		{
			deepest_depth = branch->depth;
			deepest = branch;
		}
		branch = branch->succ;
	}
	return deepest;
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
// Function: Etableau(...)
//
//   This is the entry point into Etableau proof search.
//
// Side Effects    : Proofstate, proofcontrol, bank, everything.
//
/----------------------------------------------------------------------*/

int Etableau(TableauControl_p tableaucontrol, 
											ProofState_p proofstate, 
											ProofControl_p proofcontrol, 
											TB_p bank, 
											ClauseSet_p active, 
											int max_depth, 
											int tableauequality)
{
	if(geteuid() == 0) Error("# Please do not run Etableau as root.", 1);
	APRVerify();
	bool proof_found = false;
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
	fprintf(GlobalOut, "# There are %ld start rule candidates:\n", start_rule_candidates->members);
	//ClauseSetPrint(GlobalOut, start_rule_candidates, true);
	
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
																					  
	
	// Alternating path relevance experimentation zone
	int relevance_distance = 2;
	PList_p start_rule_candidates_list = ClauseSetToPList(start_rule_candidates);
	fprintf(GlobalOut, "# Attempting APR relevance on extension candidates\n");
	PStack_p apr_relevant_extension_candidates = APRRelevanceNeighborhood(bank->sig, 
												 extension_candidates, 
												 start_rule_candidates_list, 
												 relevance_distance, 
												 false, 
												 false);
	fprintf(GlobalOut, "# Experimental: Number of extension candidates within %d relevance of conjecture: %ld of %ld\n", 
																				 relevance_distance,
																				 PStackGetSP(apr_relevant_extension_candidates),
																				 extension_candidates->members);
	PListFree(start_rule_candidates_list);
	PStackFree(apr_relevant_extension_candidates);
	// End APR zone
	
	ClauseSetFreeUnits(start_rule_candidates);
	ClauseSetInsertSet(extension_candidates, start_rule_candidates);
	ClauseSetFree(start_rule_candidates);
	fprintf(GlobalOut, "# %ld start rule tableaux created.\n", distinct_tableaux_set->members);
	fprintf(GlobalOut, "# %ld extension rule candidate clauses\n", extension_candidates->members);
	//ClauseSetPrint(GlobalOut, extension_candidates, true);
	printf("\n");
	
	TableauStack_p new_tableaux = PStackAlloc();  // The collection of new tableaux made by extension rules.
	
	if (tableaucontrol->multiprocessing_active) // multiprocess proof search
	{
		proof_found = EtableauMultiprocess(tableaucontrol, 
								  proofstate, 
								  proofcontrol, 
								  distinct_tableaux_set,
								  extension_candidates,
								  active, 
								  3, // starting depth
								  max_depth,
								  new_tableaux);
	}
	else // single core with this process
	{
		proof_found = EtableauProofSearch(tableaucontrol, 
						  proofstate, 
						  proofcontrol, 
						  distinct_tableaux_set,
						  extension_candidates,
						  active, 
						  3, // starting depth
						  max_depth,
						  new_tableaux);
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
	
	// Memory is cleaned up...
	
   if (proof_found) // success
   {
		printf("# Proof search success for %s!\n", tableaucontrol->problem_name);
		//ClauseTableauPrintDOTGraph(resulting_tab);
		return 1;
	}
	// failure
	if (proof_found == false)
	{
		fprintf(GlobalOut, "# SZS status ResourceOut for %s\n", tableaucontrol->problem_name);
	}
	return 0;
}

/*-----------------------------------------------------------------------
//
// Function: ConnectionTableauProofSearchAtDepth(...)
//
//   Try to extend on all the open branches of tableaux from distinct_tableaux_set.
//   After an extension is done, the resulting tableaux can be extended on again 
//   if there are potential new branches that do not exceed the depth limit.
//
// Side Effects    :  Calls Saturate, so many.
//
/----------------------------------------------------------------------*/

ClauseTableau_p ConnectionTableauProofSearchAtDepth(TableauControl_p tableaucontrol,
																	 ProofState_p proofstate, 
																	 ProofControl_p proofcontrol, 
																	 TableauSet_p distinct_tableaux_set,
																	 ClauseSet_p extension_candidates,
																	 int max_depth,
																	 TableauStack_p new_tableaux,
																	 int desired_num_tableaux)
{
	assert(distinct_tableaux_set);
	ClauseTableau_p active_tableau = NULL;
	ClauseTableau_p closed_tableau = NULL;
	TableauStack_p max_depth_tableaux = PStackAlloc();
	TableauStack_p newly_created_tableaux = PStackAlloc();
	int num_tableaux = 0;
	
	restart:
	while (!TableauSetEmpty(distinct_tableaux_set))
	{
		//fprintf(GlobalOut, "# %ld\n", distinct_tableaux_set->members);
		active_tableau = tableau_select(tableaucontrol, distinct_tableaux_set);
		assert(active_tableau);
		assert(active_tableau->label);
		assert(active_tableau->master == active_tableau);
		assert(active_tableau->open_branches);
		TableauSetExtractEntry(active_tableau);
		
		//ClauseTableauPrint(active_tableau);
		// At this point, there could be tableaux to be extended on at this depth in newly_created_tableaux
		// Attempt to create extension tableaux until they are all at max depth or a closed tableau is found
		while (true)
		{
			num_tableaux = (int) distinct_tableaux_set->members + (int) PStackGetSP(newly_created_tableaux);
			num_tableaux += (int) PStackGetSP(max_depth_tableaux);
			//fprintf(GlobalOut, "# Num tableaux: %ld\n", num_tableaux);
			closed_tableau = ConnectionCalculusExtendOpenBranches(active_tableau, 
																				newly_created_tableaux, 
																				tableaucontrol,
																				NULL,
																				extension_candidates,
																				max_depth, max_depth_tableaux);
			//~ closed_tableau = ConnectionCalculusExtendSelectedBranch(active_tableau, 
																				//~ newly_created_tableaux, 
																				//~ tableaucontrol,
																				//~ NULL,
																				//~ extension_candidates,
																				//~ max_depth, max_depth_tableaux);
			if (closed_tableau)
			{
				assert(tableaucontrol->closed_tableau);
				PStackPushStack(new_tableaux, newly_created_tableaux);
				TableauSetDrainToStack(tableaucontrol->tableaux_trash, distinct_tableaux_set);
				goto return_point;
			}
			else if (desired_num_tableaux && num_tableaux >= desired_num_tableaux)
			{
				//  There can be tableaux in the distinct tableaux set, newly created tableaux, or max_depth_tableaux
				fprintf(GlobalOut, "# Populating...\n");
				TableauSetDrainToStack(new_tableaux, distinct_tableaux_set);
				PStackPushStack(new_tableaux, newly_created_tableaux);
				goto return_point;
			}
			else if (PStackEmpty(newly_created_tableaux)) break;
			active_tableau = PStackPopP(newly_created_tableaux);
		}
	}
	if (desired_num_tableaux && num_tableaux < desired_num_tableaux)
	{
		max_depth++;  // rare situation, couldn't create enough tableaux at depth
		TableauStackDrainToSet(distinct_tableaux_set, max_depth_tableaux);
		goto restart;
	}
	return_point:
	PStackPushStack(new_tableaux, max_depth_tableaux);
	PStackFree(max_depth_tableaux);
	PStackFree(newly_created_tableaux);
	// Went through all possible tableaux at this depth...
	return closed_tableau;
}

/*-----------------------------------------------------------------------
//
// Function: ConnectionCalculusExtendOpenBranches(...)
//
//   Create all of the extension rules possible off of open branches of active_tableau,
//   limited by max_depth.  Open tableaux with all of their branches at max_depth
//   are added to max_depth_tableaux to be extended on later.  newly_created_tableaux
//   contains just that, tableaux that will be extended on later at the next iteration
//   and are likely at max depth.  
//
// Side Effects    :  Calls Saturate, so many.
//
/----------------------------------------------------------------------*/

ClauseTableau_p ConnectionCalculusExtendOpenBranches(ClauseTableau_p active_tableau, TableauStack_p newly_created_tableaux,
																							TableauControl_p tableaucontrol,
																							TableauSet_p distinct_tableaux,
																							ClauseSet_p extension_candidates,
																							int max_depth, TableauStack_p max_depth_tableaux)
{
	assert(active_tableau);
	assert(active_tableau->open_branches);
	TableauStack_p tab_tmp_store = PStackAlloc();
	ClauseTableau_p closed_tableau = NULL;
	int number_of_extensions = 0;
	int num_branches_at_max_depth = 0;
	//fprintf(GlobalOut, "d: %d\n", active_tableau->depth);
	
	TableauSet_p open_branches = active_tableau->open_branches;
	ClauseTableau_p open_branch = active_tableau->open_branches->anchor->succ;
	while (open_branch != active_tableau->open_branches->anchor) // iterate over the open branches of the current tableau
	{
		//fprintf(GlobalOut, "! %d %ld\n", open_branch->depth, open_branches->members);
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
		//PStackPushP(tableaucontrol->tableaux_trash, active_tableau);
		ClauseTableauFree(active_tableau->master);
	}
	
	return_point:
	PStackPushStack(newly_created_tableaux, tab_tmp_store);
	PStackFree(tab_tmp_store);
	return closed_tableau;
}

/*-----------------------------------------------------------------------
//
// Function: ConnectionCalculusExtendSelectedBranches(...)
//
//   As ConnectionCalculusExtendOpenBranches, but rather than extending
//   on all open branches, only on the selected. 
//
// Side Effects    :  Calls Saturate, so many.
//
/----------------------------------------------------------------------*/

ClauseTableau_p ConnectionCalculusExtendSelectedBranch(ClauseTableau_p active_tableau, TableauStack_p newly_created_tableaux,
																							TableauControl_p tableaucontrol,
																							TableauSet_p distinct_tableaux,
																							ClauseSet_p extension_candidates,
																							int max_depth, TableauStack_p max_depth_tableaux)
{
	assert(active_tableau);
	assert(active_tableau->open_branches);
	ClauseTableau_p closed_tableau = NULL;
	int number_of_extensions = 0;
	//fprintf(GlobalOut, "d: %d\n", active_tableau->depth);
	
	TableauSet_p open_branches = active_tableau->open_branches;
	ClauseTableau_p open_branch = branch_select(open_branches, max_depth);
	
	if (open_branch == NULL) // All max depth branches
	{
		PStackPushP(max_depth_tableaux, active_tableau);
		return NULL;
	}
	
	TableauStack_p tab_tmp_store = PStackAlloc();
	Clause_p selected = extension_candidates->anchor->succ;
	while (selected != extension_candidates->anchor) // iterate over the clauses we can split on the branch
	{
		//ClauseTableauPrint(open_branch->master);
		int new_extensions = ClauseTableauExtensionRuleAttemptOnBranch(tableaucontrol,
																								open_branch,
																								NULL,
																								selected,
																								tab_tmp_store);
		//~ if (new_extensions == 0)
		//~ {
			//~ fprintf(GlobalOut, "# Could not extend on a branch...\n");
		//~ }
		number_of_extensions += new_extensions;
		//printf("did %d extensions, there are %ld in the tab_tmp_store\n", number_of_extensions, PStackGetSP(tab_tmp_store));
		if (tableaucontrol->closed_tableau)
		{
			closed_tableau = tableaucontrol->closed_tableau;
			fprintf(GlobalOut, "# Success\n");
			goto return_point;
		}
		selected = selected->succ;
	}
	
	ClauseTableauFree(active_tableau->master);
	
	return_point:
	PStackPushStack(newly_created_tableaux, tab_tmp_store);
	//printf("newly created tableaux: %ld\n", PStackGetSP(newly_created_tableaux));
	//printf("max depth tableaux: %ld\n", PStackGetSP(max_depth_tableaux));
	PStackFree(tab_tmp_store);
	return closed_tableau;
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
	fprintf(GlobalOut, "# No tableaux could be created.  Saturating branches.\n");
	if (PStackEmpty(tableaucontrol->tableaux_trash))
	{
		Error("# Could not find a tableau to saturate in the trash... Exiting", RESOURCE_OUT);
	}
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

/*-----------------------------------------------------------------------
//
// Function: EtableauStatusReport(...)
//
//   If a closed tableau was found (resulting_tab), interpret the specification
//   to report an appropriate SZS status.  
//
// Side Effects    :  None
//
/----------------------------------------------------------------------*/

void EtableauStatusReport(TableauControl_p tableaucontrol, ClauseSet_p active, ClauseTableau_p resulting_tab)
{
	assert(resulting_tab);
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
	if (false && tableaucontrol->clausification_buffer) // Disabled for sanity
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
		fprintf(GlobalOut, "# Clausification printing disabled or no record found\n");
	}
	fprintf(GlobalOut, "# Begin printing tableau\n");
	ClauseTableauPrint(resulting_tab);
	ClauseTableauTPTPPrint(resulting_tab);
	fprintf(GlobalOut, "# End printing tableau\n");
	fprintf(GlobalOut, "# SZS output end CNFRefutation for %s\n", tableaucontrol->problem_name);
	fprintf(GlobalOut, "# Branches closed with saturation will be marked with an \"s\"\n");
	return;
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
   
   ClauseSetSplitConjectures(active, conjectures, non_conjectures);
   
   if (PListEmpty(conjectures))
   {
		fprintf(GlobalOut, "# No conjectures after preprocessing.  Attempting to resurrect them from ax_archive.\n");
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
		//ClauseTableauUpdateVariables(beginning_tableau->master); //unnecessary, is done before any uni attempts
		start_label = start_label->succ;
	}
	
	ClauseTableauFree(initial_tab);
	return distinct_tableaux_set;
}

bool EtableauProofSearch(TableauControl_p tableaucontrol,
									  ProofState_p proofstate,
									  ProofControl_p proofcontrol,
									  TableauSet_p distinct_tableaux_set,
									  ClauseSet_p extension_candidates,
									  ClauseSet_p active,
									  int starting_depth,
									  int max_depth,
									  PStack_p new_tableaux)
{
	//OutputLevel = 0;
	ClauseTableau_p resulting_tab = NULL;
	for (int current_depth = 2; current_depth < max_depth; current_depth++)
	{
		resulting_tab = ConnectionTableauProofSearchAtDepth(tableaucontrol, 
																			 proofstate, 
																			 proofcontrol, 
																			 distinct_tableaux_set,
																			 extension_candidates, 
																			 current_depth,
																			 new_tableaux,
																			 0);
		if (PStackEmpty(new_tableaux) && !resulting_tab && tableaucontrol->branch_saturation_enabled)
		{
			resulting_tab = EtableauHailMary(tableaucontrol);
		}
		if (resulting_tab)  // We successfully found a closed tableau- handle it and report results
		{
			EtableauStatusReport(tableaucontrol, active, resulting_tab);
			if (tableaucontrol->multiprocessing_active) exit(PROOF_FOUND);
			return true;		
		}
		fprintf(GlobalOut, "# Moving %ld tableaux to active set...\n", PStackGetSP(new_tableaux));
		while (!PStackEmpty(new_tableaux))
		{
			ClauseTableau_p distinct = PStackPopP(new_tableaux);
			TableauSetInsert(distinct_tableaux_set, distinct);
		}
		fprintf(GlobalOut, "# Increasing maximum depth to %d\n", current_depth + 1);
	}
	fprintf(GlobalOut, "# Ran out of tableaux... %d\n", RESOURCE_OUT);
	if (tableaucontrol->multiprocessing_active) exit(RESOURCE_OUT);
	return false;
}

bool EtableauWait(int num_cores_available, EPCtrlSet_p process_set)
{
	bool proof_found = false;
	int num_children_exited = 0;
	while (num_children_exited < num_cores_available)
	{
		int exit_status = -1;
		int return_status = -1;
		fprintf(stdout, "# Waiting...\n");
		pid_t exited_child = wait(&exit_status);
		if (WIFEXITED(exit_status))
		{
			return_status = WEXITSTATUS(exit_status);
		}
		else 
		{
			EPCtrlSetFree(process_set, false);
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
					fprintf(stdout, "# Child has found a proof.\n");
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
				EPCtrlSetFree(process_set, false);
				Error("# A branch is satisfiable- this is highly unlikely", 1);
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
				fprintf(GlobalOut, "# A child has run out of resources, likely tableaux.  Allowing others to continue.\n");
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

bool EtableauMultiprocess(TableauControl_p tableaucontrol,
									  ProofState_p proofstate,
									  ProofControl_p proofcontrol,
									  TableauSet_p distinct_tableaux_set,
									  ClauseSet_p extension_candidates,
									  ClauseSet_p active,
									  int starting_depth,
									  int max_depth,
									  PStack_p new_tableaux)
{
	OutputLevel = 0;
	bool proof_found = false;
	int num_cores_available = TableauControlGetCores(tableaucontrol);
	assert(num_cores_available);
	//  Create enough tableaux so that we can fork
	assert(proofstate);
	assert(proofcontrol);
	assert(extension_candidates);
	assert(new_tableaux);
	assert(!ClauseSetEmpty(extension_candidates));
	int desired_number_of_starting_tableaux = num_cores_available;
	fprintf(GlobalOut, "# Desiring %d worker processes and at least %d tableaux.\n", num_cores_available, desired_number_of_starting_tableaux);
	ClauseTableau_p resulting_tab = ConnectionTableauProofSearchAtDepth(tableaucontrol, 
																		 proofstate, 
																		 proofcontrol, 
																		 distinct_tableaux_set,
																		 extension_candidates, 
																		 3,
																		 new_tableaux,
																		 desired_number_of_starting_tableaux);
	if (resulting_tab)
	{
		fprintf(GlobalOut, "# Found closed tableau during pool population.\n");
		EtableauStatusReport(tableaucontrol, active, resulting_tab);
		return true;
	}
	///////////////////////////  Actually fork
	fprintf(GlobalOut, "# There are %ld tableaux, should be ready to fork.\n", PStackGetSP(new_tableaux));
	if (PStackGetSP(new_tableaux) < desired_number_of_starting_tableaux)
	{
		Error("# Trying to fork with too few tableaux...", 1);
	}
	assert(TableauSetEmpty(distinct_tableaux_set));
	
	EPCtrlSet_p process_set = EPCtrlSetAlloc();
	
	PStack_p buckets = PStackAlloc();
	for (int i=0; i < num_cores_available; i++)
	{
		PStackPushP(buckets, TableauSetAlloc());
	}
	int tableaux_distributor = 0;
	while (!PStackEmpty(new_tableaux))
	{
		tableaux_distributor = tableaux_distributor % num_cores_available;
		ClauseTableau_p tab = PStackPopP(new_tableaux);
		TableauSet_p process_bucket = PStackElementP(buckets, tableaux_distributor);
		TableauSetInsert(process_bucket, tab);
		tableaux_distributor++;
	}
	
	for (int i=0; i < num_cores_available; i++)
	{
		int pipefd[2];
		EPCtrl_p proc = EPCtrlAlloc((char*) &i);
		if (pipe(pipefd) == -1)
		{
			Error("# Pipe error", 1);
		}
		fflush(GlobalOut);
		pid_t worker = fork();
		if (worker == 0) // child process
		{
			SilentTimeOut = true;
			fprintf(GlobalOut, "# Hello from worker %d...\n", i);
			fflush(GlobalOut);
			TableauSet_p process_starting_tableaux = PStackElementP(buckets, i);
			TableauSetMoveClauses(distinct_tableaux_set, process_starting_tableaux);
			int starting_depth = 2;
			// should be good to go...
			proc->pipe = fdopen(pipefd[1], "w");
			GlobalOut = proc->pipe;
			close(pipefd[0]);
			tableaucontrol->process_control = proc;
			EtableauProofSearch(tableaucontrol, 
									  proofstate, 
									  proofcontrol, 
									  distinct_tableaux_set,
									  extension_candidates,
									  active, 
									  starting_depth,
									  max_depth,
									  new_tableaux);
		}
		else if (worker > 0) // parent
		{
			proc->pipe = fdopen(pipefd[0], "r");
			close(pipefd[1]);
			proc->pid = worker;
			proc->fileno = worker; // Since the problem is transmitted through memory, the fileno is the pid
			EPCtrlSetAddProc(process_set, proc);
		}
		else 
		{
			fprintf(GlobalOut, "# Fork error!\n"); // Really important...
			Error("Fork error", 1);
		}
	}
	
	// Wait for the children to exit...
	proof_found = EtableauWait(num_cores_available, process_set);
	while (!PStackEmpty(buckets))
	{
		TableauSet_p trash = PStackPopP(buckets);
		TableauSetFree(trash);
	}
	PStackFree(buckets);
	return proof_found;
}

int TableauControlGetCores(TableauControl_p tableaucontrol)
{
	int num_cores = tableaucontrol->multiprocessing_active;
	int nprocs = get_nprocs();
	fprintf(GlobalOut, "# %d cores available to the main process.\n", nprocs);
	if (num_cores > nprocs)
	{
		Error("# Requested more cores than are available to the program...", 1);
	}
	if (num_cores == 1)
	{
		return nprocs;
	}
	return num_cores;
}
