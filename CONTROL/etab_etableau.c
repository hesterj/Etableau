#include <etab_etableau.h>
#include <omp.h>

// Forward declaration

int process_saturation_output(TableauControl_p tableau_control,
										pid_t *pool, 
										int *return_status, 
										ClauseTableau_p *branches, 
										int num_open_branches);
void process_branch(ProofState_p proofstate, 
						  ProofControl_p proofcontrol, 
						  pid_t *pool, 
						  int *return_status, 
						  ClauseTableau_p *branches, 
						  int i);

// Function definitions 

BranchSaturation_p BranchSaturationAlloc(ProofState_p proofstate, 
													  ProofControl_p proofcontrol, 
													  ClauseTableau_p master,
													  long max_proc)
{
	BranchSaturation_p branch_sat = BranchSaturationCellAlloc();
	branch_sat->proofstate = proofstate;
	branch_sat->proofcontrol = proofcontrol;
	branch_sat->master = master;
	branch_sat->max_proc = max_proc;
	return branch_sat;
}

void BranchSaturationFree(BranchSaturation_p branch_sat)
{
	BranchSaturationCellFree(branch_sat);
}


int process_branch_nofork(ProofState_p proofstate, 
						  ProofControl_p proofcontrol,
						  ClauseTableau_p branch,
						  TableauControl_p tableau_control,
						  long max_proc)
{
	long selected_number_of_clauses_to_process = max_proc;
	long previously_saturated = branch->previously_saturated; 
	assert(branch);

	// Process more clauses on tableaux with fewer open branches
	switch (branch->open_branches->members)
	{
		case 1:
		{
			selected_number_of_clauses_to_process = 10000;
			break;
		}
		case 2:
		{
			selected_number_of_clauses_to_process = 1000;
			break;
		}
		default:
		{
			selected_number_of_clauses_to_process = 100;
			break;
		}
	}

	// Do not duplicate work.
	if (previously_saturated >= selected_number_of_clauses_to_process)
	{
		//fprintf(stdout, "# Do not replicate work...\n");
		return RESOURCE_OUT;
	}
	else
	{
		//fprintf(stdout, "# Saturating branch...\n");
		//ClauseTableauPrintBranch(branch);
		//fprintf(stdout, "# Done printing branch\n");
	}

	// Large number of clauses to process, for last ditch attempts
	if (max_proc == LONG_MAX) selected_number_of_clauses_to_process = LONG_MAX;

	//SilentTimeOut = true;
	//proofcontrol->heuristic_parms.prefer_initial_clauses = true;
	ClauseSet_p unprocessed = ClauseSetCopy(branch->terms, tableau_control->unprocessed);
	EtableauProofStateResetClauseSets(proofstate);
	ProofStateResetProcessedSet(proofstate, proofcontrol, unprocessed);
	int branch_status = ECloseBranchProcessBranchFirstSerial(proofstate, 
																				proofcontrol, 
																				branch, 
																				selected_number_of_clauses_to_process);
	EtableauProofStateResetClauseSets(proofstate);
	TermCellStoreDeleteRWLinks(&(proofstate->terms->term_store));
	branch->previously_saturated = selected_number_of_clauses_to_process;
	ClauseSetFree(unprocessed);
	return branch_status;
}


int ECloseBranchProcessBranchFirstSerial(ProofState_p proofstate, 
													  ProofControl_p proofcontrol, 
													  ClauseTableau_p branch, 
													  long max_proc)
{
	Clause_p success = NULL;
	assert(proofstate);
	assert(proofcontrol);
	
	int early_return_status = EtableauInsertBranchClausesIntoUnprocessed(proofstate, proofcontrol, branch);
	if (early_return_status == PROOF_FOUND) // Maybe a contradiction can be found via superposition within the branch...
	{
		return PROOF_FOUND;	
	}
	proofcontrol->heuristic_parms.sat_check_grounding = GMNoGrounding; // This disables calls to SAT solver
	success = Saturate(proofstate, proofcontrol, max_proc,
							 LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
							 LLONG_MAX, LONG_MAX);
	if (success)
	{
		return PROOF_FOUND;
	}
    //GCCollect(proofstate->terms->gc);
	return RESOURCE_OUT;
}




int AttemptToCloseBranchesWithSuperpositionSerial(TableauControl_p tableau_control, BranchSaturation_p jobs)
{
	ProofState_p proofstate = jobs->proofstate;
	ProofControl_p proofcontrol = jobs->proofcontrol;
	ClauseTableau_p master = jobs->master;
	long max_proc = jobs->max_proc;
	TableauSet_p open_branches = master->open_branches;
	
	ClauseTableau_p handle = open_branches->anchor->succ;
	int num_local_branches = 0;
	int successful_count = 0;
	while (handle != open_branches->anchor)
	{
		assert(handle != master->open_branches->anchor);
		if ((open_branches->members == 1) || BranchIsLocal(handle))
		{
			num_local_branches++;
			//fprintf(GlobalOut, "# Saturating branch...\n");
			//fprintf(GlobalOut, "# Tree address: %p Nodes: %ld Branch: %p\n", &tableau_control->feature_tree, PTreeNodes(tableau_control->feature_tree), handle);
			DTreeBranchRepresentations(handle, &tableau_control->feature_tree);
			tableau_control->number_of_saturation_attempts++;
			//ResetAllOccurrences(&tableau_control->feature_tree);
			int branch_status = process_branch_nofork(proofstate, 
																	proofcontrol, 
																	handle, 
																	tableau_control, 
																	max_proc);
			//fprintf(GlobalOut, "# Done.\n");
			if (branch_status == PROOF_FOUND)
			{
				//fprintf(stdout, "# Proof found on branch. %ld remain.\n", handle->set->members - 1);
				TableauSetExtractEntry(handle);
				handle->open = false;
				handle->saturation_closed = true;
				handle->mark_int = 0;
				ClauseTableauRegisterStep(handle);
				DStrAppendStr(handle->info, " Saturation closed ");
				DStrAppendInt(handle->info, tableau_control->number_of_saturation_attempts);
				successful_count++;
				handle = open_branches->anchor->succ;
				//return 1;
				continue;
			}
		}
		handle = handle->succ;
	}
	if (open_branches->members == 0)
	{
		tableau_control->closed_tableau = master;
	}
	// Exit and return to tableaux proof search
	return successful_count;
}

/*-----------------------------------------------------------------------
//
// Function: ProofStateResetClauseSets()
//
//   Empty _all_ clause and formula sets in proof state. Keep the
//   signature and term bank.
// 
//   Copied in case this needs to be changed, but looks like it should be ok...
//
// Global Variables: -
//
// Side Effects    : Memory operations.
//
/----------------------------------------------------------------------*/

void EtableauProofStateResetClauseSets(ProofState_p state)
{
   ClauseSetFreeClauses(state->axioms);
   FormulaSetFreeFormulas(state->f_axioms);
   FormulaSetFreeFormulas(state->f_ax_archive);
   ClauseSetFreeClauses(state->processed_pos_rules);
   ClauseSetFreeClauses(state->processed_pos_eqns);
   ClauseSetFreeClauses(state->processed_neg_units);
   ClauseSetFreeClauses(state->processed_non_units);
   ClauseSetFreeClauses(state->unprocessed);
   ClauseSetFreeClauses(state->tmp_store);
   ClauseSetFreeClauses(state->eval_store);
   ClauseSetFreeClauses(state->archive);
   ClauseSetFreeClauses(state->ax_archive);
   FormulaSetFreeFormulas(state->f_ax_archive);
   GlobalIndicesReset(&(state->gindices));
   if(state->watchlist)
   {
      ClauseSetFreeClauses(state->watchlist);
      GlobalIndicesReset(&(state->wlindices));
   }
}

/*-----------------------------------------------------------------------
//
// Function: ProofStateResetProcessedSet()
//
//   Move all label clauses on branch into state->unprocessed.
//   Modified from ProofStateResetProcessedSet
//   As the clauses are put into state->unprocessed, process them
//   This is a "cargo cult" approach to ensure they are processed properly
//
// Global Variables: -
//
// Side Effects    : Many, processes clauses
//
/----------------------------------------------------------------------*/

int EtableauInsertBranchClausesIntoUnprocessed(ProofState_p state,
                                 ProofControl_p control,
                                 ClauseTableau_p branch)
{
	ClauseTableau_p branch_handle = branch;
	if (branch->master == branch)
	{
		return RESOURCE_OUT;
	}
	while (branch_handle)
	{
		Clause_p label = branch_handle->label;
		int status = ProcessSpecificClauseWrapper(state, control, label);
		if (status == PROOF_FOUND)
		{
			return PROOF_FOUND;	
		}
		if (branch_handle->folding_labels)
		{
			int folding_status = ProcessSpecificClauseSetWrapper(state, control, branch_handle->folding_labels);
			if (folding_status == PROOF_FOUND)
			{
				return PROOF_FOUND;
			}
		}
		branch_handle = branch_handle->parent;
	}
	return RESOURCE_OUT;
}

int ProcessSpecificClauseWrapper(ProofState_p state, ProofControl_p control, Clause_p clause)
{
	Clause_p handle = ClauseCopy(clause, state->terms);
	//Clause_p tmpclause = ClauseFlatCopy(handle);
	//ClausePushDerivation(tmpclause, DCCnfQuote, handle, NULL);
	//ClauseSetInsert(state->archive, handle);
	//handle = tmpclause;
	HCBClauseEvaluate(control->hcb, handle);
	ClauseDelProp(handle, CPIsOriented);
	ClauseDelProp(handle, CPLimitedRW);
	ClauseSetProp(handle, CPInitial);
	DocClauseQuoteDefault(6, handle, "move_eval");
	EvalListChangePriority(handle->evaluations, -PrioLargestReasonable);
	ClauseSetInsert(state->unprocessed, handle);
	Clause_p success = ProcessSpecificClause(state, control, handle, LONG_MAX);
	if (success)
	{
		return PROOF_FOUND;	
	}
	return RESOURCE_OUT;
}

int ProcessSpecificClauseSetWrapper(ProofState_p state, ProofControl_p control, ClauseSet_p set)
{
	Clause_p handle = set->anchor->succ;
	while (handle != set->anchor)
	{
		int status = ProcessSpecificClauseWrapper(state, control, handle);
		if (status == PROOF_FOUND)
		{
			return PROOF_FOUND;	
		}
		handle = handle->succ;
	}
	return RESOURCE_OUT;
}
/*-----------------------------------------------------------------------
//
// Function: TermTreeDeleteRWLinks()
//
//   Delete all the rewrite links of terms in the tree.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void TermTreeDeleteRWLinks(Term_p root)
{
   PStack_p stack = PStackAlloc();

   PStackPushP(stack, root);

   while(!PStackEmpty(stack))
   {
      root = PStackPopP(stack);
      if(root)
      {
    TermDeleteRWLink(root);
    PStackPushP(stack, root->lson);
    PStackPushP(stack, root->rson);
      }
   }
   PStackFree(stack);
}

/*-----------------------------------------------------------------------
//
// Function: TermCellStoreDeleteRWLinks()
//
//   Free the trees in a term cell storage.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
//
/----------------------------------------------------------------------*/

void TermCellStoreDeleteRWLinks(TermCellStore_p store)
{
   int i;

   for(i=0; i<TERM_STORE_HASH_SIZE; i++)
   {
		TermTreeDeleteRWLinks(store->store[i]);
   }
}



