#include "etab_etableau.h"
#include "etab_backtrack.h"
#include <omp.h>

// Forward declaration

extern bool inf_sys_complete;

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


ErrorCodes ECloseBranchWrapper(ProofState_p proofstate,
							   ProofControl_p proofcontrol,
							   ClauseTableau_p branch,
							   TableauControl_p tableau_control,
							   long max_proc)
{
	long selected_number_of_clauses_to_process = max_proc;
	long previously_saturated = branch->previously_saturated; 
	assert(branch);

	if (tableau_control->quicksat)
	{
		selected_number_of_clauses_to_process = tableau_control->quicksat;
	}
	else
	// Process more clauses on tableaux with fewer open branches
	{
		switch (branch->open_branches->members)
		{
			case 1:
			{
				//selected_number_of_clauses_to_process = 1000*branch->depth;
				selected_number_of_clauses_to_process = 10000;
				break;
			}
			case 2:
			{
				//selected_number_of_clauses_to_process = 100*branch->depth;
				selected_number_of_clauses_to_process = 1000;
				break;
			}
			default:
			{
				//selected_number_of_clauses_to_process = 100;
				selected_number_of_clauses_to_process = 100;
				break;
			}
		}
	}

	// Do not duplicate work.
	if (previously_saturated >= selected_number_of_clauses_to_process)
	{
		return RESOURCE_OUT;
	}

	// Large number of clauses to process, for last ditch attempts
	if (max_proc == LONG_MAX) selected_number_of_clauses_to_process = LONG_MAX;

	BacktrackProofState(proofstate, proofcontrol, tableau_control, tableau_control->backup);

	ErrorCodes branch_status = ECloseBranchWithInterreduction(proofstate,
															  proofcontrol,
															  branch,
															  selected_number_of_clauses_to_process);

	branch->previously_saturated = selected_number_of_clauses_to_process;

	return branch_status;
}

//ErrorCodes OLD_ECloseBranchWrapper(ProofState_p proofstate,
							   //ProofControl_p proofcontrol,
							   //ClauseTableau_p branch,
							   //TableauControl_p tableau_control,
							   //long max_proc)
//{
	//long selected_number_of_clauses_to_process = max_proc;
	//long previously_saturated = branch->previously_saturated;
	//assert(branch);
//
	//if (tableau_control->quicksat)
	//{
		//fprintf(stdout, "# Processing %ld clauses\n", tableau_control->quicksat);
		//fflush(stdout);
		//selected_number_of_clauses_to_process = tableau_control->quicksat;
	//}
	//else
	//// Process more clauses on tableaux with fewer open branches
	//{
		//switch (branch->open_branches->members)
		//{
			//case 1:
			//{
				////selected_number_of_clauses_to_process = 1000*branch->depth;
				//selected_number_of_clauses_to_process = 10000;
				//break;
			//}
			//case 2:
			//{
				////selected_number_of_clauses_to_process = 100*branch->depth;
				//selected_number_of_clauses_to_process = 1000;
				//break;
			//}
			//default:
			//{
				////selected_number_of_clauses_to_process = 100;
				//selected_number_of_clauses_to_process = 100;
				//break;
			//}
		//}
	//}
//
	//// Do not duplicate work.
	//if (previously_saturated >= selected_number_of_clauses_to_process)
	//{
		////fprintf(stdout, "# (%ld) Do not replicate work...\n", (long) getpid());
		//return RESOURCE_OUT;
	//}
//
	//// Large number of clauses to process, for last ditch attempts
	//if (max_proc == LONG_MAX) selected_number_of_clauses_to_process = LONG_MAX;
//
	////proofcontrol->heuristic_parms.prefer_initial_clauses = true;
//
	////ClauseSet_p unprocessed = NULL;
	////bool old_reset = false;
	////if (old_reset)
	////{
		////// This is the old way of resetting the saturation proofstate
		////unprocessed = ClauseSetCopy(branch->terms, tableau_control->unprocessed);
		////EtableauProofStateResetClauseSets(proofstate);
		////ProofStateResetProcessedSet(proofstate, proofcontrol, unprocessed);
		////TermCellStoreDeleteRWLinks(&(proofstate->terms->term_store));
	////}
	////else // Presaturated Etableau core
	////{
		////BacktrackProofState(proofstate, proofcontrol, tableau_control, tableau_control->backup);
	////}
//
	//BacktrackProofState(proofstate, proofcontrol, tableau_control, tableau_control->backup);
//
	//ErrorCodes branch_status = ECloseBranchWithInterreduction(proofstate,
															  //proofcontrol,
															  //branch,
															  //selected_number_of_clauses_to_process);
//
	////EtableauProofStateResetClauseSets(proofstate);
	////TermCellStoreDeleteRWLinks(&(proofstate->terms->term_store));
//
	//branch->previously_saturated = selected_number_of_clauses_to_process;
//
	////if (unprocessed) // Needed if we are using the old style proof reset
	////{
		////ClauseSetFree(unprocessed);
	////}
//
//
	//return branch_status;
//}

ErrorCodes ECloseBranchWithInterreduction(ProofState_p proofstate,
										  ProofControl_p proofcontrol,
										  ClauseTableau_p branch,
										  long max_proc)
{
	Clause_p success = NULL;
	Clause_p success_ref = NULL;
	PStack_p branch_labels = PStackAlloc();
	ErrorCodes status = RESOURCE_OUT;
	bool process_branch_clauses_first = true;
	bool interreduction = false;
	bool full_saturation = true;
	assert(proofstate);
	assert(proofcontrol);
	PStack_p debug_branch_labels = NULL;

#ifdef QUICKSAT
	max_proc = 100;
#endif

	long number_found __attribute__((unused)) = ClauseTableauCollectBranchCopyLabels(branch, proofstate->unprocessed, debug_branch_labels);

	// This is the interreduction step!

	if (interreduction)
	{
		LiteralSelectionFun sel_strat =
			proofcontrol->heuristic_parms.selection_strategy;
		proofcontrol->heuristic_parms.selection_strategy = SelectNoGeneration;
		success = Saturate(proofstate, proofcontrol, LONG_MAX, // This is the interreduction
						   LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
						   LLONG_MAX, LONG_MAX);
		proofcontrol->heuristic_parms.selection_strategy = sel_strat;
		assert(ProofStateProcCardinality(proofstate));
		ProofStateResetProcessedNoCopy(proofstate, proofcontrol, branch_labels);
	}

    if(LIKELY(!success)) // First we will process the clauses of the branch, and then the full saturation
    {
		assert(!ClauseSetEmpty(proofstate->unprocessed));
		proofcontrol->heuristic_parms.sat_check_grounding = GMNoGrounding; // This disables calls to SAT solver
		if (process_branch_clauses_first)
		{
			status = ProcessSpecificClauseStackWrapperNoCopy(proofstate, proofcontrol, branch_labels, &success_ref); // Process the branch clauses first
		}
		if (UNLIKELY(status == PROOF_FOUND)) // A contradiction was found while processing the branch clauses
		{
			assert(success_ref);
			success = success_ref;
		}
		else if (full_saturation) // Now do the full branch saturation
		{
			// max_proc is passed as the step limit to Saturate
			success = Saturate(proofstate, proofcontrol, max_proc,
							   LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
							   LLONG_MAX, LONG_MAX);
		}
	}

	bool out_of_clauses = ClauseSetEmpty(proofstate->unprocessed);
	if (!success &&
		out_of_clauses &&
		inf_sys_complete &&
		proofstate->state_is_complete &&
		!(proofstate->has_interpreted_symbols))
	{
		branch->master->tableaucontrol->satisfiable = true;
		fprintf(stdout, "# %ld Satisfiable branch\n", (long) getpid());
		fflush(stdout);
		status = SATISFIABLE;
	}
	if (success)
	{
		Sig_p sig = proofstate->signature;
		assert(success->derivation);
		//fprintf(stdout, "# Derivation of pid (%ld)\n", (long) getpid());
		//DerivationStackTSTPPrint(stdout, sig, success->derivation);
		//fprintf(stdout, "\nDone.\n");
		//fflush(stdout);
		assert(ClauseLiteralNumber(success) == 0);
		status = PROOF_FOUND;
	}
	PStackFree(branch_labels); // The branch labels are free'd elsewhere, so no need to worry about losing the pointers to them.
	return status;
}




int AttemptToCloseBranchesWithSuperpositionSerial(TableauControl_p tableau_control, BranchSaturation_p jobs)
{
	ProofState_p proofstate = jobs->proofstate;
	ProofControl_p proofcontrol = jobs->proofcontrol;
	assert(tableau_control);
	assert(proofstate);
	assert(proofcontrol);
	ClauseTableau_p master = jobs->master;
	long max_proc = jobs->max_proc;
	TableauSet_p open_branches = master->open_branches;
	assert(open_branches);
	
	ClauseTableau_p handle = open_branches->anchor->succ;
	int num_local_branches = 0;
	int successful_count = 0;
	int branch_status = RESOURCE_OUT;
	while (handle != open_branches->anchor)
	{
		assert(handle);
		assert(handle != master->open_branches->anchor);
		assert(handle->info);
		if ((!handle->saturation_blocked) && ((open_branches->members == 1) || BranchIsLocal(handle)))
		{
			num_local_branches++;
			tableau_control->number_of_saturation_attempts++;
			//ResetAllOccurrences(&tableau_control->feature_tree);
			branch_status = ECloseBranchWrapper(proofstate,
												proofcontrol,
												handle,
												tableau_control,
												max_proc);
			//EqnBranchRepresentationsList(handle, tableau_control->feature_list, branch_status);
			//XGBoostTest();
			if (branch_status == PROOF_FOUND)
			{
				//fprintf(stdout, "# PROOF_FOUND found on branch. %ld remain.\n", handle->set->members - 1);
				fflush(stdout);
				TableauSetExtractEntry(handle);
				handle->open = false;
				handle->saturation_closed = true;
				handle->mark_int = 0;
				ClauseTableauRegisterStep(handle);
				DStrAppendStr(handle->info, " Saturation closed ");
				DStrAppendInt(handle->info, tableau_control->number_of_saturation_attempts);
				successful_count++;
				tableau_control->number_of_successful_saturation_attempts++;
				//return 1;
				//fprintf(stdout, "# (%ld) Saturation attempt %ld successful\n", (long) getpid(), (long) tableau_control->number_of_saturation_attempts);
				//fflush(stdout);

				// Create the backtrack for the etableau closure rule...
				Subst_p empty_subst = SubstAlloc(); // No substitutions are applied to the tableau in Etableau closure rule applications
				Backtrack_p backtrack = BacktrackAlloc(handle, empty_subst, 0, ETABLEAU_RULE);
				backtrack->completed = true;
				assert(BacktrackIsEtableauStep(backtrack));
				assert(handle->arity == 0);
				PStackPushP(handle->backtracks, backtrack);
				PStack_p position_copy = PStackCopy(backtrack->position);
				PStackPushP(handle->master->master_backtracks, position_copy);
				assert(handle->set == NULL);

				handle = open_branches->anchor->succ;
				continue;
			}
			else if (branch_status == SATISFIABLE)
			{
				fprintf(GlobalOut, "# Satisfiable branch found.\n");
				fflush(GlobalOut);
				successful_count++;
				assert(tableau_control->satisfiable);
				DStrAppendStr(handle->info, " Satisfiable ");
				DStrAppendInt(handle->info, tableau_control->number_of_saturation_attempts);
				break;
			}
		}
		handle = handle->succ;
	}
	if (open_branches->members == 0 || branch_status == SATISFIABLE)
	{
#ifndef NDEBUG
		fprintf(stdout, "# (%ld) Found closed tableau\n", (long) getpid());
		fflush(stdout);
#endif
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
	Clause_p handle = ClauseCopyAndPrepareForSaturation(clause, state->terms, control->hcb);
	ClauseSetInsert(state->unprocessed, handle);
	Clause_p success = ProcessSpecificClause(state, control, handle, LONG_MAX);
	// For some reason this can yield false positives...
	if (success)
	{
		return PROOF_FOUND;	
	}
	return RESOURCE_OUT;
}

int ProcessSpecificClauseWrapperNoCopy(ProofState_p state, ProofControl_p control, Clause_p clause, Clause_p *success_ref)
{
	assert(clause->set);
	assert(clause->set == state->unprocessed);
	Clause_p success = ProcessSpecificClause(state, control, clause, LONG_MAX);
	if (success)
	{
		//printf("%ld setting success_ref\n", (long) getpid());
		*success_ref = success;
		assert(*success_ref);
		return PROOF_FOUND;
	}
	else if (UNLIKELY(ClauseSetEmpty(state->unprocessed)))
	{
		fprintf(stdout, "# Bizzare behavior: Satisfiable branch in ProcessSpecificClauseWrapperNoCopy?\n");
		fflush(stdout);
		assert(false);
	}
	return RESOURCE_OUT;
}

ErrorCodes ProcessSpecificClauseSetWrapper(ProofState_p state, ProofControl_p control, ClauseSet_p set)
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


ErrorCodes ProcessSpecificClauseStackWrapper(ProofState_p state, ProofControl_p control, ClauseStack_p stack)
{
	while (!PStackEmpty(stack))
	{
		Clause_p handle = PStackPopP(stack);
		int status = ProcessSpecificClauseWrapper(state, control, handle);
		if (status == PROOF_FOUND)
		{
			return PROOF_FOUND;
		}
		handle = handle->succ;
	}
	return RESOURCE_OUT;
}

ErrorCodes ProcessSpecificClauseStackWrapperNoCopy(ProofState_p state, ProofControl_p control, ClauseStack_p stack, Clause_p *success_ref)
{
	Clause_p success = NULL;
	while (!PStackEmpty(stack))
	{
		Clause_p handle = PStackPopP(stack);
		//int status = ProcessSpecificClauseWrapperNoCopy(state, control, handle, success_ref);
		int status = ProcessSpecificClauseWrapperNoCopy(state, control, handle, &success);
		if (status == PROOF_FOUND)
		{
			assert(success);
			*success_ref = success;
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
//   Delete the rewrite links in the term cell storage.
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

bool EtableauSaturateAllTableauxInStack(TableauControl_p tableaucontrol, TableauStack_p distinct_tableaux_stack, ClauseSet_p active, long maximum)
{
	for (PStackPointer p=0; p<PStackGetSP(distinct_tableaux_stack); p++)
	{
		if (p >= maximum)
		{
			fprintf(GlobalOut, "# Unsuccessfully attempted saturation on %ld start tableaux, moving on.\n", maximum);
			break;
		}
		ClauseTableau_p saturation_tableau = PStackElementP(distinct_tableaux_stack, p);
		BranchSaturation_p branch_sat = BranchSaturationAlloc(tableaucontrol->proofstate,
															  tableaucontrol->proofcontrol,
															  saturation_tableau,
															  10000);
		AttemptToCloseBranchesWithSuperpositionSerial(tableaucontrol, branch_sat);
		BranchSaturationFree(branch_sat);
		if (tableaucontrol->closed_tableau)
		{
			assert(tableaucontrol->closed_tableau == saturation_tableau);
			EtableauStatusReport(tableaucontrol, active, tableaucontrol->closed_tableau);
			return true;
		}
	}
	return false;
}

long ClauseTableauCollectBranchCopyLabels(ClauseTableau_p branch, ClauseSet_p set, PStack_p branch_labels)
{
	assert(branch);
	assert(set);
	ClauseTableau_p branch_handle = branch;
	while (branch_handle)
	{
		assert(branch_handle);
		Clause_p label = ClauseCopyAndPrepareForSaturation(branch_handle->label, branch->terms, branch->control->hcb);
		assert(label);
		assert(label->set == NULL);
		assert(ClauseLiteralNumber(label));
		ClauseSetInsert(set, label);
		if (branch_labels)
		{
			PStackPushP(branch_labels, label);
		}
		ClauseSetProp(label, CPIsTableauClause);
#ifdef SATURATION_USES_FOLDING_LABELS
		if (branch_handle->folding_labels)
		{
			//printf("there are %ld folding labels at a node of depth %d\n", branch_handle->folding_labels->members, branch_handle->depth);
			ClauseSetCopyInsertAndPrepareForSaturation(branch_handle->folding_labels, set, branch->terms, branch->control->hcb, branch_labels);
		}
#endif
		branch_handle = branch_handle->parent;
	}
	return set->members;
}

Clause_p ClauseCopyAndPrepareForSaturation(Clause_p clause, TB_p bank, HCB_p hcb)
{
	assert(clause);
	assert(bank);
	assert(hcb);
#ifdef  DEBUG
	ClauseRecomputeLitCounts(clause);
	assert(ClauseLiteralNumber(clause));
#endif
	Clause_p handle = ClauseCopy(clause, bank);
#ifdef  DEBUG
	ClauseRecomputeLitCounts(handle);
	assert(ClauseLiteralNumber(handle));
#endif
	HCBClauseEvaluate(hcb, handle);
	ClauseDelProp(handle, CPIsOriented);
	ClauseDelProp(handle, CPLimitedRW);
	ClauseSetProp(handle, CPInitial);
	DocClauseQuoteDefault(6, handle, "move_eval");
	EvalListChangePriority(handle->evaluations, -PrioLargestReasonable);
	return handle;
}

long ClauseSetCopyInsertAndPrepareForSaturation(ClauseSet_p from, ClauseSet_p to, TB_p bank, HCB_p hcb, PStack_p branch_labels)
{
	assert(from);
	assert(to);
	assert(bank);
	assert(hcb);
	Clause_p handle = from->anchor->succ;
	while (handle != from->anchor)
	{
		Clause_p copied = ClauseCopyAndPrepareForSaturation(handle, bank, hcb);
		//if (ClauseGetIdent(copied) == 4511) printf("# inserting the evil clause...\n");
		ClauseSetInsert(to, copied);
		//PStackPushP(branch_labels, copied);
		ClauseSetProp(copied, CPIsTableauClause);
		handle = handle->succ;
	}

	return to->members;
}

/*-----------------------------------------------------------------------
//
// Function: TermTreeUnbind()
//
//   Unbind all of the bindings of the term and subterms.
//   Returns number of terms unbound.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

long TermTreeUnbind(Term_p root)
{
   PStack_p stack = PStackAlloc();
   long     res   = 0;

   PStackPushP(stack, root);

   while(!PStackEmpty(stack))
   {
      root = PStackPopP(stack);
      if(root)
      {
         PStackPushP(stack, root->lson);
         PStackPushP(stack, root->rson);
		 if (CAN_DEREF(root))
		 {
			 root->binding = NULL;
		 }
         res++;
      }
   }
   PStackFree(stack);

   return res;
}

/*-----------------------------------------------------------------------
//
// Function: TermCellStoreUnbindAll()
//
//   Return the number of nodes in the term cell store.
//   Unbind all the terms found in the termcellstore.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

long TermCellStoreUnbindAll(TermCellStore_p store)
{
   long res = 0;
   int i;

   for(i=0; i<TERM_STORE_HASH_SIZE; i++)
   {
      res+=TermTreeUnbind(store->store[i]);
   }
   return res;
}

long TermBankUnbindAll(TB_p bank)
{
	return TermCellStoreUnbindAll(&(bank->term_store));
}

BackupProofState_p BackupProofstateAlloc(ProofState_p original)
{
	BackupProofState_p backup = BackupProofStateCellAlloc();
	backup->num_processed = ProofStateProcCardinality(original);
	backup->processed_neg_units = ClauseSetCopyOpt(original->processed_neg_units);
	backup->processed_non_units = ClauseSetCopyOpt(original->processed_non_units);
	backup->processed_pos_eqns = ClauseSetCopyOpt(original->processed_pos_eqns);
	backup->processed_pos_rules = ClauseSetCopyOpt(original->processed_pos_rules);
	backup->unprocessed = ClauseSetCopyOpt(original->unprocessed);
	return backup;

}
void BackupProofStateFree(BackupProofState_p junk)
{
	ClauseSetFree(junk->processed_non_units);
	ClauseSetFree(junk->processed_pos_eqns);
	ClauseSetFree(junk->processed_pos_rules);
	ClauseSetFree(junk->processed_neg_units);
	ClauseSetFree(junk->unprocessed);
	BackupProofStateCellFree(junk);
}

long BacktrackProofState(ProofState_p proofstate, ProofControl_p proofcontrol, TableauControl_p tableaucontrol, BackupProofState_p backup)
{
	//printf("start backtracking %ld\n", tableaucontrol->number_of_saturation_attempts);
	ClauseSet_p unprocessed = NULL;
	assert(proofstate);
	assert(proofcontrol);
	assert(backup);
	assert(tableaucontrol);


	if (ClauseSetCardinality(backup->unprocessed))
	{
		unprocessed = ClauseSetCopyOpt(backup->unprocessed);
	}
	else
	{
		unprocessed = ClauseSetCopyOpt(tableaucontrol->unprocessed);
	}



	EtableauProofStateResetClauseSets(proofstate);

	//ProofStateResetProcessedSet(proofstate, proofcontrol, unprocessed);
	//
	proofstate->state_is_complete = false;
	//assert(ClauseSetEmpty(unprocessed));

	ClauseSetFree(unprocessed);
	ClauseSetFree(proofstate->processed_neg_units);
	ClauseSetFree(proofstate->processed_non_units);
	ClauseSetFree(proofstate->processed_pos_eqns);
	ClauseSetFree(proofstate->processed_pos_rules);

	proofstate->processed_neg_units = ClauseSetCopyIndexedOpt(backup->processed_neg_units);
	proofstate->processed_non_units = ClauseSetCopyIndexedOpt(backup->processed_non_units);
	proofstate->processed_pos_eqns  = ClauseSetCopyIndexedOpt(backup->processed_pos_eqns);
	proofstate->processed_pos_rules = ClauseSetCopyIndexedOpt(backup->processed_pos_rules);

	proofstate->processed_pos_rules->demod_index = PDTreeAlloc(proofstate->terms);
	proofstate->processed_pos_eqns->demod_index  = PDTreeAlloc(proofstate->terms);
	proofstate->processed_neg_units->demod_index = PDTreeAlloc(proofstate->terms);

	proofstate->demods[0]            = proofstate->processed_pos_rules;
	proofstate->demods[1]            = proofstate->processed_pos_eqns;
	proofstate->demods[2]            = NULL;

	TermCellStoreDeleteRWLinks(&(proofstate->terms->term_store));
	//assert(ProofStateProcCardinality(proofstate));
	//assert(ClauseSetCardinality(proofstate->unprocessed));
	//printf("done backtracking %ld\n", tableaucontrol->number_of_saturation_attempts);
	return 0;
}
