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
long clauseset_delete_rw_links(ClauseSet_p set);
long clause_delete_rw_links(Clause_p clause);
long eqn_delete_rw_links(Eqn_p eqn);
ClauseSet_p clauseset_flatcopy_deleterw(ClauseSet_p set);

void etableau_proof_state_free(ProofState_p junk);
ProofState_p etableau_proof_state_alloc(ProofState_p main_proof_state);
long clauseset_insert_copy(TB_p bank, ClauseSet_p to, ClauseSet_p from);

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

    //printf("about to saturate a branch\n");

    ProofState_p new_proofstate = BacktrackProofStateNew2(proofstate,
                                                          proofcontrol,
                                                          tableau_control,
                                                          tableau_control->backup);

    ErrorCodes branch_status = ECloseBranchWithInterreduction(new_proofstate,
                                                              proofcontrol,
                                                              branch,
                                                              selected_number_of_clauses_to_process);

    branch->previously_saturated = selected_number_of_clauses_to_process;
    etableau_proof_state_free(new_proofstate);
    //printf("finished freeing temporary proof state\n");
    return branch_status;
}

ErrorCodes ECloseBranchWithInterreduction(ProofState_p proofstate,
                                          ProofControl_p proofcontrol,
                                          ClauseTableau_p branch,
                                          long max_proc)
{
    TB_p terms = proofstate->terms;
    Clause_p success = NULL;
    Clause_p success_ref = NULL;
    TableauControl_p tableaucontrol = branch->master->tableaucontrol;
    PStack_p branch_labels = PStackAlloc();
    ErrorCodes status = RESOURCE_OUT;
    bool process_branch_clauses_first = true;
    bool interreduction = true;
    bool full_saturation = true;
    assert(proofstate);
    assert(proofcontrol);
    PStack_p debug_branch_labels = NULL;
    assert(!ClauseSetEmpty(proofstate->unprocessed));

    long number_found __attribute__((unused)) =
        ClauseTableauCollectBranchCopyLabels(terms,
                                             branch,
                                             proofstate->unprocessed,
                                             debug_branch_labels);

    // This is the interreduction step!

    if (interreduction)
    {
        LiteralSelectionFun sel_strat =
            proofcontrol->heuristic_parms.selection_strategy;
        proofcontrol->heuristic_parms.selection_strategy = SelectNoGeneration;
        success = Saturate(proofstate, proofcontrol, LONG_MAX, // This is the interreduction
                           LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
                           LLONG_MAX, LONG_MAX);
        if (success)
        {
            ClauseTableauSetProp(branch, TUPSaturationClosedInterreduction);
            (tableaucontrol->number_of_saturations_closed_in_interreduction)++;
        }
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
            status = ProcessSpecificClauseStackWrapperNoCopy(proofstate,
                                                             proofcontrol,
                                                             branch_labels,
                                                             &success_ref); // Process the branch clauses first
        }
        if (UNLIKELY(status == PROOF_FOUND)) // A contradiction was found while processing the branch clauses
        {
            assert(success_ref);
            ClauseTableauSetProp(branch, TUPSaturationClosedOnBranch);
            (tableaucontrol->number_of_saturations_closed_on_branch)++;
            success = success_ref;
        }
        else if (full_saturation) // Now do the full branch saturation
        {
            // max_proc is passed as the step limit to Saturate
            success = Saturate(proofstate, proofcontrol, max_proc,
                               LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
                               LLONG_MAX, LONG_MAX);
            if (success)
            {
                ClauseTableauSetProp(branch, TUPSaturationClosedAfterBranch);
                (tableaucontrol->number_of_saturations_closed_after_branch)++;
            }
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
        assert(success->derivation);
#ifndef NDEBUG
        Sig_p sig = proofstate->signature;
        fprintf(stdout, "# Derivation of pid (%ld)\n", (long) getpid());
        DerivationStackTSTPPrint(stdout, sig, success->derivation);
        fprintf(stdout, "\nDone.\n");
#endif
        assert(ClauseLiteralNumber(success) == 0);
        status = PROOF_FOUND;
    }
    fflush(stdout);
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
        if ((!ClauseTableauQueryProp(handle, TUPSaturationBlocked)) && ((open_branches->members == 1) || BranchIsLocal(handle)))
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

long ClauseTableauCollectBranchCopyLabels(TB_p terms,
                                          ClauseTableau_p branch,
                                          ClauseSet_p set,
                                          PStack_p branch_labels)
{
    assert(branch);
    assert(set);
    ClauseTableau_p branch_handle = branch;
    while (branch_handle)
    {
        assert(branch_handle);
        Clause_p label = ClauseCopyAndPrepareForSaturation(branch_handle->label,
                                                           terms,
                                                           branch->control->hcb);
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
            ClauseSetCopyInsertAndPrepareForSaturation(branch_handle->folding_labels,
                                                       set,
                                                       terms,
                                                       branch->control->hcb,
                                                       branch_labels);
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

long BacktrackProofState(ProofState_p proofstate,
                         ProofControl_p proofcontrol,
                         TableauControl_p tableaucontrol,
                         BackupProofState_p backup)
{
    //printf("start backtracking %ld\n", tableaucontrol->number_of_saturation_attempts);
    ClauseSet_p unprocessed = NULL;
    assert(proofstate);
    assert(proofcontrol);
    assert(backup);
    assert(tableaucontrol);
    Warning("Unsound");

    TermCellStoreDeleteRWLinks(&(proofstate->terms->term_store));

    EtableauProofStateResetClauseSets(proofstate);

    if (!(tableaucontrol->quicksat)) // We are doing full saturation on branches
    {
        if (ClauseSetCardinality(backup->unprocessed))
        {
            unprocessed = ClauseSetFlatCopy(backup->unprocessed);
        }
        else
        {
            unprocessed = ClauseSetFlatCopy(tableaucontrol->unprocessed);
        }
        ProofStateResetProcessedSet(proofstate, proofcontrol, unprocessed);
        ClauseSetFree(unprocessed);
    }
    else
    {
        proofstate->state_is_complete = false;
    }

    assert(ClauseSetEmpty(proofstate->processed_neg_units));
    assert(ClauseSetEmpty(proofstate->processed_non_units));
    assert(ClauseSetEmpty(proofstate->processed_pos_eqns));
    assert(ClauseSetEmpty(proofstate->processed_pos_rules));
    ClauseSetFree(proofstate->processed_neg_units);
    ClauseSetFree(proofstate->processed_non_units);
    ClauseSetFree(proofstate->processed_pos_eqns);
    ClauseSetFree(proofstate->processed_pos_rules);

    proofstate->processed_neg_units = ClauseSetAlloc();
    proofstate->processed_non_units = ClauseSetAlloc();
    proofstate->processed_pos_eqns  = ClauseSetAlloc();
    proofstate->processed_pos_rules = ClauseSetAlloc();

    proofstate->processed_pos_rules->demod_index = PDTreeAlloc(proofstate->terms);
    proofstate->processed_pos_eqns->demod_index  = PDTreeAlloc(proofstate->terms);
    proofstate->processed_neg_units->demod_index = PDTreeAlloc(proofstate->terms);

    ClauseSetInsertSetFlatCopyIndexed(proofstate->processed_neg_units, backup->processed_neg_units);
    ClauseSetInsertSetFlatCopyIndexed(proofstate->processed_non_units, backup->processed_non_units);
    ClauseSetInsertSetFlatCopyIndexed(proofstate->processed_pos_eqns,  backup->processed_pos_eqns);
    ClauseSetInsertSetFlatCopyIndexed(proofstate->processed_pos_rules, backup->processed_pos_rules);


    proofstate->demods[0]            = proofstate->processed_pos_rules;
    proofstate->demods[1]            = proofstate->processed_pos_eqns;
    proofstate->demods[2]            = NULL;

    return 0;
}

ProofState_p BacktrackProofStateNew(ProofControl_p proofcontrol,
                                    TableauControl_p tableaucontrol,
                                    BackupProofState_p backup)
{
    ProofState_p proofstate = ProofStateAlloc(FPIgnoreProps);
    ClauseSet_p unprocessed = NULL;
    assert(proofcontrol);
    assert(backup);
    assert(tableaucontrol);

    if (!(tableaucontrol->quicksat)) // We are doing full saturation on branches
    {
        if (ClauseSetCardinality(backup->unprocessed))
        {
            unprocessed = ClauseSetFlatCopy(backup->unprocessed);
        }
        else
        {
            unprocessed = ClauseSetFlatCopy(tableaucontrol->unprocessed);
        }
        ProofStateResetProcessedSet(proofstate, proofcontrol, unprocessed);
        ClauseSetFree(unprocessed);
    }
    else
    {
        proofstate->state_is_complete = false;
    }

    ClauseSetInsertSetCopyOptIndexed(proofstate->processed_neg_units, backup->processed_neg_units);
    ClauseSetInsertSetCopyOptIndexed(proofstate->processed_non_units, backup->processed_non_units);
    ClauseSetInsertSetCopyOptIndexed(proofstate->processed_pos_eqns,  backup->processed_pos_eqns);
    ClauseSetInsertSetCopyOptIndexed(proofstate->processed_pos_rules, backup->processed_pos_rules);

    return proofstate;
}

long BacktrackProofStateReset(ProofState_p proofstate,
                              ProofControl_p proofcontrol,
                              TableauControl_p tableaucontrol,
                              BackupProofState_p backup)
{
    assert(proofstate);
    assert(proofcontrol);
    assert(backup);
    assert(tableaucontrol);

    ////// This is the old way of resetting the saturation proofstate
    //ClauseSet_p unprocessed = ClauseSetFlatCopy(tableaucontrol->unprocessed);
    ClauseSet_p unprocessed = clauseset_flatcopy_deleterw(tableaucontrol->unprocessed);
    EtableauProofStateResetClauseSets(proofstate);
    ProofStateResetProcessedSet(proofstate, proofcontrol, unprocessed);

    return 0;
}

ProofState_p BacktrackProofStateNew2(ProofState_p proofstate,
                                     ProofControl_p proofcontrol,
                                     TableauControl_p tableaucontrol,
                                     BackupProofState_p backup)
{
    assert(proofstate);
    assert(proofcontrol);
    assert(backup);
    assert(tableaucontrol);
    //printf("allocating new proof state\n");

    ProofState_p new_state = etableau_proof_state_alloc(proofstate);
    //printf("copying unprocessed into the new proofstate's axioms\n");
    clauseset_insert_copy(new_state->terms, new_state->axioms, tableaucontrol->unprocessed);

    //printf("initializing global indices\n");
    //ProofControl_p new_proofconrol
    GlobalIndicesInit(&(new_state->wlindices),
                      new_state->signature,
                      proofcontrol->heuristic_parms.rw_bw_index_type,
                      "NoIndex",
                      "NoIndex");
    //printf("initializing proofstate\n");

    ProofStateInit(new_state, proofcontrol);
    //ClauseSet_p unprocessed = clauseset_flatcopy_deleterw(tableaucontrol->unprocessed);
    //EtableauProofStateResetClauseSets(proofstate);
    //ProofStateResetProcessedSet(proofstate, proofcontrol, unprocessed);

    //printf("returning new proof state\n");
    return new_state;
}

long clauseset_delete_rw_links(ClauseSet_p set)
{
    long res=0;
    Clause_p handle = set->anchor->succ;
    while (handle != set->anchor)
    {
        res += clause_delete_rw_links(handle);
        handle = handle->succ;
    }
    return res;
}

long clause_delete_rw_links(Clause_p clause)
{
    long res = 0;
    Eqn_p lit = clause->literals;
    while (lit)
    {
        res += eqn_delete_rw_links(lit);
        lit = lit->next;
    }
    return res;
}

long eqn_delete_rw_links(Eqn_p eqn)
{
    Term_p lterm = eqn->lterm;
    Term_p rterm = eqn->rterm;
    TermDeleteRWLink(lterm);
    for (int i=0; i<lterm->arity; i++)
    {
        TermDeleteRWLink(lterm->args[i]);
    }
    TermDeleteRWLink(rterm);
    for (int i=0; i<lterm->arity; i++)
    {
        TermDeleteRWLink(lterm->args[i]);
    }
    return 4;
}

ClauseSet_p clauseset_flatcopy_deleterw(ClauseSet_p set)
{
    Clause_p handle, temp;
    assert(set);
    ClauseSet_p new = ClauseSetAlloc();
    for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
    {
        assert(handle);
        temp = ClauseFlatCopy(handle);
        clause_delete_rw_links(temp);
        ClauseDelProp(temp, CPIsDIndexed);
        ClauseDelProp(temp, CPIsSIndexed);
        ClauseSetInsert(new, temp);
    }
    return new;
}

/*-----------------------------------------------------------------------
//
// Function: ProofStateAlloc()
//
//   Return an empty, initialized proof state. The argument is:
//   free_symb_prop: Which sub-properties of FPDistinctProp should be
//                   ignored (i.e. which classes with distinct object
//                   syntax  should be treated as plain free
//                   symbols). Use FPIgnoreProps for default
//                   behaviour, FPDistinctProp for fully free
//                   (conventional) semantics.
//
//   This differs from ProofStateAlloc by assuming we have FPIgnoreProps
//   and using the signature of an existing ProofState_p.
//
//   There is a corresponding etableau_proof_state_free function.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

ProofState_p etableau_proof_state_alloc(ProofState_p main_proof_state)
{
   ProofState_p handle = ProofStateCellAlloc();

   //handle->type_bank            = TypeBankAlloc();
   handle->type_bank = main_proof_state->type_bank;
   //handle->signature            = SigAlloc(handle->type_bank);
   handle->signature = main_proof_state->signature;
   //SigInsertInternalCodes(handle->signature);
   //handle->original_symbols     = 0;
   handle->original_symbols     = main_proof_state->original_symbols;
   handle->terms                = TBAlloc(handle->signature);
   handle->tmp_terms            = TBAlloc(handle->signature);
   //handle->freshvars            = VarBankAlloc(handle->type_bank);
   handle->freshvars = main_proof_state->freshvars;
   // The variable banks should already be shadowed!
   //VarBankPairShadow(handle->terms->vars, handle->freshvars);
   handle->f_axioms             = FormulaSetAlloc();
   handle->f_ax_archive         = FormulaSetAlloc();
   handle->ax_archive           = ClauseSetAlloc();
   handle->axioms               = ClauseSetAlloc();
   handle->processed_pos_rules  = ClauseSetAlloc();
   handle->processed_pos_eqns   = ClauseSetAlloc();
   handle->processed_neg_units  = ClauseSetAlloc();
   handle->processed_non_units  = ClauseSetAlloc();
   handle->unprocessed          = ClauseSetAlloc();
   handle->tmp_store            = ClauseSetAlloc();
   handle->eval_store           = ClauseSetAlloc();
   handle->archive              = ClauseSetAlloc();

   if (main_proof_state->watchlist)
   {
       handle->watchlist = ClauseSetCopy(handle->terms, main_proof_state->watchlist);
   }
   else
   {
       handle->watchlist = NULL;
   }
   //handle->watchlist            = ClauseSetAlloc();
   handle->f_archive            = FormulaSetAlloc();
   handle->extract_roots        = PStackAlloc();
   GlobalIndicesNull(&(handle->gindices));
   handle->fvi_initialized      = false;
   handle->fvi_cspec            = NULL;
   handle->processed_pos_rules->demod_index = PDTreeAlloc(handle->terms);
   handle->processed_pos_eqns->demod_index  = PDTreeAlloc(handle->terms);
   handle->processed_neg_units->demod_index = PDTreeAlloc(handle->terms);
   handle->demods[0]            = handle->processed_pos_rules;
   handle->demods[1]            = handle->processed_pos_eqns;
   handle->demods[2]            = NULL;
   GlobalIndicesNull(&(handle->wlindices));
   handle->state_is_complete       = true;
   //handle->has_interpreted_symbols = false;
   handle->has_interpreted_symbols = main_proof_state->has_interpreted_symbols;
   handle->definition_store     = DefStoreAlloc(handle->terms);
   handle->def_store_cspec      = NULL;

   handle->gc_terms             = GCAdminAlloc(handle->terms);
   GCRegisterFormulaSet(handle->gc_terms, handle->f_axioms);
   GCRegisterFormulaSet(handle->gc_terms, handle->f_ax_archive);
   GCRegisterClauseSet(handle->gc_terms, handle->axioms);
   GCRegisterClauseSet(handle->gc_terms, handle->ax_archive);
   GCRegisterClauseSet(handle->gc_terms, handle->processed_pos_rules);
   GCRegisterClauseSet(handle->gc_terms, handle->processed_pos_eqns);
   GCRegisterClauseSet(handle->gc_terms, handle->processed_neg_units);
   GCRegisterClauseSet(handle->gc_terms, handle->processed_non_units);
   GCRegisterClauseSet(handle->gc_terms, handle->unprocessed);
   GCRegisterClauseSet(handle->gc_terms, handle->tmp_store);
   GCRegisterClauseSet(handle->gc_terms, handle->eval_store);
   GCRegisterClauseSet(handle->gc_terms, handle->archive);
   //GCRegisterClauseSet(handle->gc_terms, handle->watchlist);
   if (handle->watchlist)
   {
       GCRegisterClauseSet(handle->gc_terms, handle->watchlist);
   }
   GCRegisterClauseSet(handle->gc_terms, handle->definition_store->def_clauses);
   GCRegisterFormulaSet(handle->gc_terms, handle->definition_store->def_archive);
   GCRegisterFormulaSet(handle->gc_terms, handle->f_archive);

   handle->status_reported              = false;
   handle->answer_count                 = 0;

   handle->processed_count              = 0;
   handle->proc_trivial_count           = 0;
   handle->proc_forward_subsumed_count  = 0;
   handle->proc_non_trivial_count       = 0;
   handle->other_redundant_count        = 0;
   handle->non_redundant_deleted        = 0;
   handle->backward_subsumed_count      = 0;
   handle->backward_rewritten_count     = 0;
   handle->backward_rewritten_lit_count = 0;
   handle->generated_count              = 0;
   handle->generated_lit_count          = 0;
   handle->non_trivial_generated_count  = 0;
   handle->context_sr_count     = 0;
   handle->paramod_count        = 0;
   handle->factor_count         = 0;
   handle->resolv_count         = 0;
   handle->satcheck_count       = 0;
   handle->satcheck_success     = 0;
   handle->satcheck_satisfiable = 0;
   handle->satcheck_full_size   = 0;
   handle->satcheck_actual_size = 0;
   handle->satcheck_core_size   = 0;
   handle->satcheck_preproc_time  = 0.0;
   handle->satcheck_encoding_time = 0.0;
   handle->satcheck_solver_time   = 0.0;
   handle->satcheck_preproc_stime  = 0.0;
   handle->satcheck_encoding_stime = 0.0;
   handle->satcheck_solver_stime   = 0.0;

   handle->filter_orphans_base   = 0;
   handle->forward_contract_base = 0;

   handle->gc_count             = 0;
   handle->gc_used_count        = 0;

#ifdef NEVER_DEFINED
   printf("# XXXf_axioms            = %p\n", handle->f_axioms);
   printf("# XXXf_ax_archive        = %p\n", handle->f_ax_archive);
   printf("# XXXax_archive          = %p\n", handle->ax_archive);
   printf("# XXXaxioms              = %p\n", handle->axioms);
   printf("# XXXprocessed_pos_rules = %p\n", handle->processed_pos_rules);
   printf("# XXXprocessed_pos_eqns  = %p\n", handle->processed_pos_eqns);
   printf("# XXXprocessed_neg_units = %p\n", handle->processed_neg_units);
   printf("# XXXprocessed_non_units = %p\n", handle->processed_non_units);
   printf("# XXXunprocessed         = %p\n", handle->unprocessed);
   printf("# XXXtmp_store           = %p\n", handle->tmp_store);
   printf("# XXXeval_store          = %p\n", handle->eval_store);
   printf("# XXXarchive             = %p\n", handle->archive);
   printf("# XXXwatchlist           = %p\n", handle->watchlist);
   printf("# XXXf_archive           = %p\n", handle->f_archive);
#endif
   return handle;
}

/*-----------------------------------------------------------------------
//
// Function: etableau_proof_state_free()
//
//   Free a ProofStateCell, but not the type bank and signature.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void etableau_proof_state_free(ProofState_p junk)
{
   assert(junk);
   ClauseSetFree(junk->axioms);
   FormulaSetFree(junk->f_axioms);
   FormulaSetFree(junk->f_ax_archive);
   ClauseSetFree(junk->processed_pos_rules);
   ClauseSetFree(junk->processed_pos_eqns);
   ClauseSetFree(junk->processed_neg_units);
   ClauseSetFree(junk->processed_non_units);
   ClauseSetFree(junk->unprocessed);
   ClauseSetFree(junk->tmp_store);
   ClauseSetFree(junk->eval_store);
   ClauseSetFree(junk->archive);
   ClauseSetFree(junk->ax_archive);
   FormulaSetFree(junk->f_archive);
   PStackFree(junk->extract_roots);
   GlobalIndicesFreeIndices(&(junk->gindices));
   GCAdminFree(junk->gc_terms);
   //GCAdminFree(junk->gc_original_terms);
   if(junk->watchlist)
   {
      ClauseSetFree(junk->watchlist);
   }
   GlobalIndicesFreeIndices(&(junk->wlindices));

   DefStoreFree(junk->definition_store);
   if(junk->fvi_cspec)
   {
      FVCollectFree(junk->fvi_cspec);
   }
   if(junk->def_store_cspec)
   {
      FVCollectFree(junk->def_store_cspec);
   }
   // junk->original_terms->sig = NULL;
   junk->terms->sig = NULL;
   junk->tmp_terms->sig = NULL;
   //SigFree(junk->signature);
   TBFree(junk->terms);
   TBFree(junk->tmp_terms);
   //VarBankFree(junk->freshvars);
   //TypeBankFree(junk->type_bank);

   ProofStateCellFree(junk);
}
// End of file

// Insert copies of clauses from "from" to "to".
// Uses ClauseCopy
// Removes all properties of the clause

long clauseset_insert_copy(TB_p bank, ClauseSet_p to, ClauseSet_p from)
{
    long res = 0;
    Clause_p handle, temp;
    assert(to);
    assert(from);
    for (handle = from->anchor->succ; handle != from->anchor; handle = handle->succ)
    {
        assert(handle);
        res++;
        temp   = ClauseCopy(handle, bank);
        temp->properties = CPIgnoreProps;
        temp->weight = ClauseStandardWeight(temp);
        //ClauseMarkMaximalTerms(bank->ocb, temp);
        ClauseSetInsert(to, temp);
    }
    return res;
}
