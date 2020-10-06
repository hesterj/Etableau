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

void process_branch(ProofState_p proofstate, 
						  ProofControl_p proofcontrol, 
						  pid_t *pool, 
						  int *return_status, 
						  ClauseTableau_p *branches, 
						  int i)
{
	pid_t worker = fork();
	if (worker == 0) // We are in the child process 
	{
		ClauseTableau_p branch = branches[i];
		assert(branches[i]);
		//SilentTimeOut = true;
		int branch_status = ECloseBranchProcessBranchFirst(proofstate, proofcontrol, branch);
		//~ #ifndef DNDEBUG
		//~ fprintf(GlobalOut, "# FORK FINAL REPORT %ld processed clauses, branch_status %d, branch %p\n", ProofStateProcCardinality(proofstate), branch_status, branch);
		//~ #endif
		exit(branch_status);
	}
	else if (worker > 0)  // parent process
	{
		pool[i] = worker;
		return_status[i] = RESOURCE_OUT;
	}
	else 
	{
		fprintf(GlobalOut, "# Fork failure\n");
		Error("Fork failure", 1);
	}
}

int process_branch_nofork(ProofState_p proofstate, 
						  ProofControl_p proofcontrol,
						  ClauseTableau_p branch,
						  TableauControl_p tableau_control,
						  long max_proc)
{
	long selected_number_of_clauses_to_process = max_proc;
	long previously_saturated = branch->previously_saturated; 

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
	//if (previously_saturated >= selected_number_of_clauses_to_process)
	if (previously_saturated > selected_number_of_clauses_to_process)
	{
		return RESOURCE_OUT;
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
	ClauseSetFree(unprocessed);
	return branch_status;
}

int ECloseBranchProcessBranchFirst(ProofState_p proofstate, ProofControl_p proofcontrol, 
					  ClauseTableau_p branch)
{
	Clause_p success = NULL;
	ClauseTableau_p node = branch;
	assert(proofstate);
	assert(proofcontrol);
	//long proc_limit = 500;
	
	// Collect the clauses of the branch
	
	while (node)
	{
		if (node != node->master)
		{
			Clause_p label = node->label;
			label->weight = ClauseStandardWeight(label);
			assert(!label->set);
			assert(!label->evaluations);
			ClauseSetProp(label, CPInitial);
			success = ProcessSpecificClause(proofstate, proofcontrol, label, LONG_MAX);
			if (success)
			{
				//fprintf(GlobalOut, "# Saturate returned empty clause on branch.\n");
				//ProofStateStatisticsPrint(GlobalOut, proofstate);
				return PROOF_FOUND;
			}
		}
		if (node->folding_labels) // Process the folding labels, if there are any
		{
			ClauseSetSetProp(node->folding_labels, CPInitial);
			assert(node->folding_labels->members == 0);
			//ClauseSetPrint(GlobalOut, node->folding_labels, true);printf("\n");
			while (!ClauseSetEmpty(node->folding_labels))
			{
				Clause_p fold_label = ClauseSetExtractFirst(node->folding_labels);
				fold_label->weight = ClauseStandardWeight(fold_label);
				success = ProcessSpecificClause(proofstate, 
														  proofcontrol, 
														  fold_label, 
														  LONG_MAX);
				if (success)
				{
					//fprintf(GlobalOut, "# Saturate returned empty clause on folds.\n");
					//ProofStateStatisticsPrint(GlobalOut, proofstate);
					return PROOF_FOUND;
				}
			}
		}
		//~ if (node->unit_axioms) // Process the units, if there are any
		//~ {
			//~ ClauseSetSetProp(node->unit_axioms, CPInitial);
			//~ while (!ClauseSetEmpty(node->unit_axioms))
			//~ {
				//~ Clause_p unit = ClauseSetExtractFirst(node->unit_axioms);
				//~ unit->weight = ClauseStandardWeight(unit);
				//~ success = ProcessSpecificClause(proofstate, 
														  //~ proofcontrol, 
														  //~ unit, 
														  //~ LONG_MAX);
				//~ if (success)
				//~ {
					//~ //fprintf(GlobalOut, "# Saturate returned empty clause on units.\n");
					//~ //ProofStateStatisticsPrint(GlobalOut, proofstate);
					//~ return PROOF_FOUND;
				//~ }
			//~ }
		//~ }
		node = node->parent;
	}
	
	//~ // Now do normal saturation
	if (branch->open_branches->members == 1 && branch->depth > 8)
	{
		//fprintf(GlobalOut, "# Beginning deep saturation check (p)\n");
		success = Saturate(proofstate, proofcontrol, 10000,
								 LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
								 LLONG_MAX, LONG_MAX);
		//fprintf(GlobalOut, "# Deep saturation check done\n");
		if (success)
		{
			//fprintf(GlobalOut, "# Saturate returned empty clause %p on a branch.\n", success);
			//ProofStateStatisticsPrint(GlobalOut, proofstate);
			return PROOF_FOUND;
		}
	}
	
	//~ fprintf(GlobalOut, "# Surrendering\n");
	return RESOURCE_OUT;
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
	return RESOURCE_OUT;
}

int AttemptToCloseBranchesWithSuperposition(TableauControl_p tableau_control, BranchSaturation_p jobs)
{
	Error("Function is disabled to prevent warnings", 1);
	//~ ProofState_p proofstate = jobs->proofstate;
	//~ ProofControl_p proofcontrol = jobs->proofcontrol;
	//~ ClauseTableau_p master = jobs->master;
	//~ TableauSet_p open_branches = master->open_branches;
	
	//~ int num_open_branches = (int) open_branches->members;
	
	//~ // Collect the local branches in an array
	//~ pid_t pool[num_open_branches];  // Uninitialized array
	//~ int return_status[num_open_branches]; // Uninitialized array
	//~ ClauseTableau_p branches[num_open_branches]; // Uninitialized array
	//~ // Initialize the arrays: We are only interested in local branches
	//~ ClauseTableau_p handle = open_branches->anchor->succ;
	//~ int num_local_branches = 0;
	//~ for (int i=0; i<num_open_branches; i++)
	//~ {
		//~ assert(handle != master->open_branches->anchor);
		//~ //VarBankSetVCountsToUsed(proofstate->freshvars);
		//~ if (BranchIsLocal(handle))
		//~ {
			//~ num_local_branches++;
			//~ branches[i] = handle;
			//~ pool[i] = 0;
			//~ return_status[i] = RESOURCE_OUT;
		//~ }
		//~ else 
		//~ {
			//~ branches[i] = NULL;
			//~ pool[i] = -1;
			//~ return_status[i] = RESOURCE_OUT;
		//~ }
		//~ handle = handle->succ;
	//~ }
	//~ #pragma omp task
	//~ {
		//~ for (int i=0; i<num_open_branches; i++)
		//~ {
			//~ if (branches[i]) // Branch is local, so we will try to close it
			//~ {
				//~ process_branch(proofstate, proofcontrol, pool, return_status, branches, i);
			//~ }
		//~ }
		//~ #pragma omp critical
		//~ process_saturation_output(tableau_control, pool, return_status, branches, num_open_branches);
	//~ }
	//~ fflush(GlobalOut);
	// Exit and return to tableaux proof search
	return 0;
}

int process_saturation_output(TableauControl_p tableau_control,
										pid_t *pool, 
										int *return_status, 
										ClauseTableau_p *branches, 
										int num_open_branches)
{
	int raw_status = 0, status = OTHER_ERROR;
	int successful_count = 0;
	ClauseTableau_p closed_branch = NULL;
	for (int i=0; i<num_open_branches; i++)
	{
		pid_t respid = -1;
		while(respid == -1)
		{
			pid_t worker = pool[i];
			//fprintf(GlobalOut, "#");
			if (worker == -1) break;
			assert(branches[i]);
			respid = waitpid(worker, &raw_status, 0);
			if (WIFEXITED(raw_status))
         {
				//fprintf(GlobalOut, "# Fork %d dead, respid %d, status %d.\n", worker, respid, raw_status);
            status = WEXITSTATUS(raw_status);
            if (status == SATISFIABLE)
            {
					return_status[i] = SATISFIABLE;
					ClauseTableau_p satisfiable_branch = branches[i];
					fprintf(GlobalOut, "# Satisfiable branch!\n");
					tableau_control->closed_tableau = satisfiable_branch;
					tableau_control->satisfiable = true;
					successful_count++;
					return successful_count;
				}
            if (status == PROOF_FOUND)
            {
					//fprintf(GlobalOut, "# Branch %d of %d detected with exit status %d, raw status %d\n", i, num_open_branches, status, raw_status);
					assert(respid);
					closed_branch = branches[i];
					TableauSetExtractEntry(closed_branch);
					closed_branch->open = false;
					closed_branch->saturation_closed = true;
					closed_branch->mark_int = 0;
					//DStrAppendStr(closed_branch->info, "Saturation closed");
					return_status[i] = PROOF_FOUND;
					successful_count++;
					break;
            }
         }
         else if (WIFSIGNALED(raw_status))
         {
				fprintf(GlobalOut, "# %d %d Signalled termination\n", raw_status, respid);
			}
         else
         {
            fprintf(GlobalOut, "# %d %d Abnormal termination\n", raw_status, respid);
         }
		}
	}
	if (successful_count == num_open_branches)
	{
		fprintf(GlobalOut, "# All %d remaining open branches were closed with E.\n", successful_count);
		if (tableau_control->closed_tableau) 
		{
			return successful_count;
		}
		else
		{ 
			tableau_control->closed_tableau = closed_branch->master;
		}
	}
	return successful_count;
}

/*  ONLY call this function on a branch if it is local!
 *  Otherwise the prover becomes unsound!
*/

int ECloseBranch(ProofState_p proofstate, 
					  ProofControl_p proofcontrol,
					  TableauControl_p tableaucontrol, 
					  ClauseTableau_p branch)
{
	int status = process_branch_nofork(proofstate, 
												  proofcontrol, 
												  branch, 
												  tableaucontrol, 
												  10000);
	if (status == PROOF_FOUND)
	{
		branch->open = false;
		TableauSetExtractEntry(branch);
		return PROOF_FOUND;
	}
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
		if (BranchIsLocal(handle))
		{
			num_local_branches++;
			int branch_status = process_branch_nofork(proofstate, 
																	proofcontrol, 
																	handle, 
																	tableau_control, 
																	max_proc);
			if (branch_status == PROOF_FOUND)
			{
				ClauseTableau_p new_handle = handle->succ;
				TableauSetExtractEntry(handle);
				handle->open = false;
				handle->saturation_closed = true;
				handle->mark_int = 0;
				ClauseTableauRegisterStep(handle);
				DStrAppendStr(handle->info, " Saturation closed");
				successful_count++;
				handle = new_handle;
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
	Clause_p handle = ClauseCopyOpt(clause);
	Clause_p tmpclause = ClauseFlatCopy(handle);
	ClausePushDerivation(tmpclause, DCCnfQuote, handle, NULL);
	ClauseSetInsert(state->archive, handle);
	handle = tmpclause;
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
//   John Hester
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



