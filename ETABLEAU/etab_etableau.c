#include "etab_etableau.h"
#include "etab_backtrack.h"

// Forward declaration

extern bool inf_sys_complete;

void etableau_proofstate_free(ProofState_p junk);
ProofState_p etableau_proofstate_alloc(ProofState_p main_proof_state);
long clauseset_insert_copy(TB_p bank, ClauseSet_p to, ClauseSet_p from);
ProofState_p backtrack_proofstate(ProofState_p proofstate,
                                  ProofControl_p proofcontrol,
                                  TableauControl_p tableaucontrol,
                                  ClauseTableau_p leaf);
long collect_branch_labels_for_saturation(TB_p terms,
                                          ClauseTableau_p branch,
                                          ClauseSet_p set,
                                          PStack_p branch_labels,
                                          ProofControl_p proofcontrol);
long collect_set_for_saturation(ClauseSet_p from,
                                ClauseSet_p to,
                                TB_p bank,
                                ProofControl_p proofcontrol,
                                PStack_p branch_labels);
bool branch_saturation_allowed(ClauseTableau_p branch);
bool classify_branch_python(ClauseTableau_p branch);
long collect_ground_units(ProofState_p etableau_proofstate,
                          TB_p tableau_bank,
                          ClauseTableau_p where,
                          ErrorCodes status);

// Function definitions

ErrorCodes EproverCloseBranchWrapper(ProofState_p proofstate,
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

    // Hash the branch and make sure that we haven't already saturated an identical branch
    long branch_hash = ClauseTableauHashBranch(branch);
    //printf("# Hash of branch we are going to saturate with %ld clauses: %ld\n",
           //selected_number_of_clauses_to_process,
           //branch_hash);
    tableau_control->number_of_saturation_attempts++;

    // If we have already unsuccessfully saturated an identical branch, block the attempt
    if (PStackFindInt(tableau_control->failed_saturations, branch_hash))
    {
        tableau_control->number_saturations_blocked++;
        ClauseTableauSetProp(branch, TUPSaturationBlocked);
        return RESOURCE_OUT;
    }

    // If we have already successfully saturated an identical branch, we can mark this branch as closed for free
    else if (PStackFindInt(tableau_control->successful_saturations, branch_hash))
    {
        tableau_control->number_of_free_saturations++;
        //printf("# We got a free saturation!\n");
        return PROOF_FOUND;
    }
#ifdef XGBOOST_FLAG
    DStr_p branch_data_file = DStrAlloc();
    DStrAppendStr(branch_data_file, "/home/hesterj/Projects/branchdata/");
    DStrAppendInt(branch_data_file, getpid());
#endif
    // Create a backtracked proofstate for the branch saturation.
    ProofState_p new_proofstate = backtrack_proofstate(proofstate,
                                                       proofcontrol,
                                                       tableau_control,
                                                       branch);

    // Actually do the branch saturation
    ErrorCodes branch_status = EproverCloseBranch(new_proofstate,
                                                  proofcontrol,
                                                  branch,
                                                  selected_number_of_clauses_to_process);

    if (branch_status != PROOF_FOUND) PStackPushInt(tableau_control->failed_saturations, branch_hash);
    else if (branch_status == PROOF_FOUND) PStackPushInt(tableau_control->successful_saturations, branch_hash);

    branch->previously_saturated = selected_number_of_clauses_to_process;

#ifdef ETAB_SAVE_GROUND_UNITS
long
    __attribute__((unused)) long number_of_units_saved =
         collect_ground_units(new_proofstate, proofstate->terms, branch, branch_status);
#endif

    // Record the branch in the appropriate file with the saturation status
#ifdef XGBOOST_FLAG
    const char* postfix = ",0\n";
    int number_of_times_to_print = 1;
    if (branch_status == PROOF_FOUND)
    {
        number_of_times_to_print = 10;
        postfix = ",1\n";
    }
    ClauseTableauPrintBranchSimpleToFile(DStrView(branch_data_file),
                                         "a",
                                         number_of_times_to_print,
                                         NULL,
                                         postfix,
                                         ". ",
                                         branch);
    DStrFree(branch_data_file);
#endif

    /* etableau_proofstate_free(new_proofstate); */
    branch->saturation_state = new_proofstate;

    return branch_status;
}

/*
** Use the Etableau closure rule, i/e superposition calculus saturation procedure
** on the selected branch of the tableau.  If the branch is satisfiable, the problem
** specification is satisfiable.  Otherwise, if a contradiction is found, it
** reflects a partial refutation and the branch can be closed.
**
*/

ErrorCodes EproverCloseBranch(ProofState_p proofstate,
                              ProofControl_p proofcontrol,
                              ClauseTableau_p branch,
                              long max_proc)
{
    assert(branch->state != proofstate); // Do not saturate branches with the main proof search state!
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

    // Prepare the proofstate (which has just been allocated)
    // for Etableau saturation.

    long number_found __attribute__((unused)) =
        collect_branch_labels_for_saturation(terms,
                                             branch,
                                             proofstate->axioms,
                                             debug_branch_labels,
                                             proofcontrol);
    GlobalIndicesInit(&(proofstate->wlindices),
                      proofstate->signature,
                      proofcontrol->heuristic_parms.rw_bw_index_type,
                      "NoIndex",
                      "NoIndex");
    ProofStateInit(proofstate, proofcontrol);

    // This is the interreduction step!
    assert(!ClauseSetEmpty(proofstate->unprocessed));

    if (!success && interreduction)
    {
        LiteralSelectionFun sel_strat =
            proofcontrol->heuristic_parms.selection_strategy;
        proofcontrol->heuristic_parms.selection_strategy = SelectNoGeneration;
        success = Saturate(proofstate, proofcontrol, LONG_MAX, // This is the interreduction
                           LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
                           LLONG_MAX, LONG_MAX);
        proofcontrol->heuristic_parms.selection_strategy = sel_strat;
        if (success)
        {
            ClauseTableauSetProp(branch, TUPSaturationClosedInterreduction);
            (tableaucontrol->number_of_saturations_closed_in_interreduction)++;
        }
        else
        {
            ProofStateResetProcessedNoCopy(proofstate, proofcontrol, branch_labels);
            //  branch_labels now has the the clauses from the tableau's branch
        }
        assert(ProofStateCardinality(proofstate));
    }

    if(LIKELY(!success)) // First we will process the clauses of the branch, and then the full saturation
    {
        assert(!ClauseSetEmpty(proofstate->unprocessed));
        proofcontrol->heuristic_parms.sat_check_grounding = GMNoGrounding; // This disables calls to SAT solver
        if (process_branch_clauses_first)
        {
            status = ProcessSpecificClauseStack(proofstate,
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
#ifndef NDEBUG
    printf("# (%ld) Beginning full saturation\n", (long) getpid());
#endif
            success = Saturate(proofstate, proofcontrol, max_proc,
                               LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
                               LLONG_MAX, LONG_MAX);
#ifndef NDEBUG
    printf("# (%ld) Ended full saturation\n", (long) getpid());
#endif
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




int CloseBranchesWithEprover(TableauControl_p tableaucontrol,
                             ClauseTableau_p master,
                             long max_proc)
{
    ProofState_p proofstate = tableaucontrol->proofstate;
    ProofControl_p proofcontrol = tableaucontrol->proofcontrol;
    assert(tableaucontrol);
    assert(proofstate);
    assert(proofcontrol);
    assert(master->master == master);
    TableauSet_p open_branches = master->open_branches;
    assert(open_branches);

    if (tableaucontrol->only_saturate_max_depth_branches)
    {
        int deepest_depth = ClauseTableauGetDeepestBranch(master);
        if (deepest_depth < master->maximum_depth - 1)
        {
            //printf("Only saturate when we have a deep branch\n");
            return 0;
        }
        else
        {
            //printf("We have a deep branch\n");
        }
    }

    ClauseTableau_p handle = open_branches->anchor->succ;
    int num_local_branches = 0;
    int successful_count = 0;
    int branch_status = RESOURCE_OUT;
    while (handle != open_branches->anchor)
    {
        assert(handle);
        assert(handle != master->open_branches->anchor);
        assert(handle->info);
        if (branch_saturation_allowed(handle))
        {
            num_local_branches++;
            //ResetAllOccurrences(&tableau_control->feature_tree);
            branch_status = EproverCloseBranchWrapper(proofstate,
                                                      proofcontrol,
                                                      handle,
                                                      tableaucontrol,
                                                      max_proc);
            //EqnBranchRepresentationsList(handle, tableau_control->feature_list, branch_status);
            //XGBoostTest();
            if (branch_status == PROOF_FOUND)
            {
                // Close the branch
                fflush(stdout);
                TableauSetExtractEntry(handle);
                handle->open = false;
                handle->saturation_closed = true;
                handle->mark_int = 0;
                ClauseTableauRegisterStep(handle);
                DStrAppendStr(handle->info, " Saturation closed ");
                DStrAppendInt(handle->info, tableaucontrol->number_of_saturation_attempts);
                successful_count++;
                tableaucontrol->number_of_successful_saturation_attempts++;

                // Create the backtrack for the etableau closure rule...
                // No substitutions are applied to the tableau in Etableau closure rule applications
                Subst_p empty_subst = SubstAlloc();
                Backtrack_p backtrack = BacktrackAlloc(handle, empty_subst, 0, ETABLEAU_RULE);
                SubstDelete(empty_subst);
                backtrack->completed = true;
                assert(BacktrackIsEtableauStep(backtrack));
                assert(handle->arity == 0);
                PStackPushP(handle->backtracks, backtrack);
                PStack_p position_copy = PStackCopy(backtrack->position);
                PStackPushP(handle->master->master_backtracks, position_copy);
                assert(handle->set == NULL);

                // Branches may be made local by Etableau closure - we can check again
                handle = open_branches->anchor->succ;
                continue;
            }
            else if (branch_status == SATISFIABLE)
            {
                fprintf(GlobalOut, "# Satisfiable branch found.\n");
                fflush(GlobalOut);
                successful_count++;
                assert(tableaucontrol->satisfiable);
                DStrAppendStr(handle->info, " Satisfiable ");
                DStrAppendInt(handle->info, tableaucontrol->number_of_saturation_attempts);
                break;
            }
            else
            {
                ClauseTableauSetProp(handle, TUPSaturationBlocked);
                if (tableaucontrol->only_saturate_max_depth_branches) break;
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
        tableaucontrol->closed_tableau = master;
    }
    // Exit and return to tableaux proof search
    return successful_count;
}

ErrorCodes ProcessSpecificClauseWrapper(ProofState_p state, ProofControl_p control, Clause_p clause, Clause_p *success_ref)
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
        fprintf(stdout, "# Bizzare behavior: Satisfiable branch in ProcessSpecificClause?\n");
        fflush(stdout);
        return SATISFIABLE;
    }
    return RESOURCE_OUT;
}

ErrorCodes ProcessSpecificClauseStack(ProofState_p state, ProofControl_p control, ClauseStack_p stack, Clause_p *success_ref)
{
    Clause_p success = NULL;
    //printf("%ld branch clauses\n", PStackGetSP(stack));
    while (!PStackEmpty(stack))
    {
        Clause_p handle = PStackPopP(stack);
        //int status = ProcessSpecificClauseWrapperNoCopy(state, control, handle, success_ref);
        ErrorCodes status = ProcessSpecificClauseWrapper(state, control, handle, &success);
        if (status == PROOF_FOUND || status==SATISFIABLE)
        {
            assert(success || status==SATISFIABLE);
            *success_ref = success;
            return status;
        }
        handle = handle->succ;
    }
    return RESOURCE_OUT;
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
        CloseBranchesWithEprover(tableaucontrol,
                                 saturation_tableau,
                                 10000);
        if (tableaucontrol->closed_tableau)
        {
            assert(tableaucontrol->closed_tableau == saturation_tableau);
            EtableauStatusReport(tableaucontrol, active, tableaucontrol->closed_tableau);
            return true;
        }
    }
    return false;
}

/*
** Insert copies of the clauses on the branch in to "set"
*/

long collect_branch_labels_for_saturation(TB_p terms,
                                          ClauseTableau_p branch,
                                          ClauseSet_p set,
                                          PStack_p branch_labels,
                                          ProofControl_p proofcontrol)
{
    assert(branch);
    assert(set);
    ClauseTableau_p branch_handle = branch;
    while (branch_handle)
    {
        assert(branch_handle);
        Clause_p label = ClauseCopy(branch_handle->label, terms); // Copy the clause with the temporary termbank
        assert(label);
        assert(label->set == NULL);
        assert(ClauseLiteralNumber(label));
        ClauseSetProp(label, CPIsTableauClause);
        ClauseSetInsert(set, label);
        if (branch_labels)
        {
            PStackPushP(branch_labels, label);
        }
#ifdef SATURATION_USES_FOLDING_LABELS
        if (branch_handle->folding_labels)
        {
            collect_set_for_saturation(branch_handle->folding_labels,
                                       set,
                                       terms,
                                       proofcontrol,
                                       branch_labels);
        }
#endif
        branch_handle = branch_handle->parent;
    }
    return set->members;
}

long collect_set_for_saturation(ClauseSet_p from,
                                ClauseSet_p to,
                                TB_p bank,
                                ProofControl_p proofcontrol,
                                PStack_p branch_labels)
{
    assert(from);
    assert(to);
    assert(bank);
    Clause_p handle = from->anchor->succ;
    while (handle != from->anchor)
    {
        Clause_p copied = ClauseCopy(handle, bank);
        ClauseSetInsert(to, copied);
        handle = handle->succ;
    }

    return to->members;
}

ProofState_p backtrack_proofstate(ProofState_p proofstate,
                                  ProofControl_p proofcontrol,
                                  TableauControl_p tableaucontrol,
                                  ClauseTableau_p leaf)
{
    assert(proofstate);
    assert(proofcontrol);
    assert(tableaucontrol);

    bool created_new_proofstate = false;

    /* ProofState_p new_state = etableau_proofstate_alloc(proofstate); */
    // Get the most recent saturation state available, or allocate a new one
    ProofState_p new_state = EtableauUpdateSaturationState(leaf,
                                                           &created_new_proofstate);

#ifndef NDEBUG
    printf("# (%ld) Collecting axioms for branch saturation\n", (long) getpid());
#endif
    if (created_new_proofstate)
    {
        // If we created a new proofstate, we need to add all of the unprocessed to it.
        // Otherwise, we should be OK by just continuing where it left off, because
        // whenever the proof procedure backtracks, the saturation states are destroyed.
        clauseset_insert_copy(new_state->terms, new_state->axioms, tableaucontrol->unprocessed);
    }
#ifndef NDEBUG
    printf("# (%ld) Done collecting axioms\n", (long) getpid());
#endif

    return new_state;
}


/*-----------------------------------------------------------------------
//
// Function: etableau_proofstate_alloc()
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

ProofState_p etableau_proofstate_alloc(ProofState_p main_proof_state)
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
   //handle->state_is_complete       = true;
   handle->state_is_complete       = main_proof_state->state_is_complete;
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
// Function: EtableauProofstateFree()
//
//   Free a ProofStateCell, but not the type bank and signature.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void EtableauProofstateFree(ProofState_p junk)
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

long clauseset_insert_copy(TB_p bank,
                           ClauseSet_p to,
                           ClauseSet_p from)
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
        assert(!ClauseQueryProp(temp, CPIsDIndexed | CPIsSIndexed | CPIsGlobalIndexed));
        temp->properties = CPIgnoreProps;
        //temp->weight = ClauseStandardWeight(temp);
        //ClauseCanonize(temp);
        //ClauseMarkMaximalTerms(bank->ocb, temp);
        ClauseSetInsert(to, temp);
    }
    return res;
}

bool branch_saturation_allowed(ClauseTableau_p branch)
{
    if (!ClauseTableauQueryProp(branch, TUPSaturationBlocked))
    {
        if (branch->open_branches->members == 1 || BranchIsLocal(branch))
        {
#ifdef ZMQ_FLAG
            return classify_branch_python(branch);
#elif ETAB_RANDOM_SAT
            double rand = JKISSRandDouble(NULL);
            if (rand < 0.5) return false;
            return true;
#else
            return true;
#endif
        }
    }
    return false;
}

#ifdef ZMQ_FLAG
bool classify_branch_python(ClauseTableau_p branch)
{
    assert(branch);
    TableauControl_p tableaucontrol = branch->master->tableaucontrol;
    if (!(tableaucontrol->zmq_connection)) return true;
    assert(tableaucontrol);
    zmsg_t* branch_message = zmsg_new();
    DStr_p branch_str_dstr = ClauseTableauBranchToDStr(branch);
    zmsg_addstr(branch_message, DStrView(branch_str_dstr));
    assert(branch_message);
    zsock_t* socket = tableaucontrol->zmq_connection;
    assert(socket);
    zmsg_send(&branch_message, socket);
    char *str = zstr_recv (socket);
    int result = atoi(str);
    zstr_free (&str);
    DStrFree(branch_str_dstr);

    //printf ("# Received: %d\n", result);
    if (result != 0 && result != 1)
    {
        Error("Unknown result from classification server\n", 120);
    }
    if (result == 0)
    {
        tableaucontrol->number_of_saturation_attempts_deferred++;
        return false;
    }

    return true;
}
#endif

// Collect the ground units of the saturation proofstate and insert them as folding
// labels at the appropriate node.  If the saturation attempt was unsuccessful,
// insert them at the node where the attempt happened.

long collect_ground_units(ProofState_p saturation_proofstate,
                          TB_p tableau_bank,
                          ClauseTableau_p where,
                          ErrorCodes status)
{
    assert(saturation_proofstate);
    assert(tableau_bank);
    assert(where);
    Clause_p handle = NULL;
    Clause_p copied = NULL;
    long number_copied = 0;
    if (where->open_branches->members == 0) return 0;
    if (status != RESOURCE_OUT) return 0;

    ClauseSet_p to = where->folding_labels;
    assert(to);
    ClauseSet_p pos_eqns = saturation_proofstate->processed_pos_eqns;
    ClauseSet_p pos_rules = saturation_proofstate->processed_pos_rules;
    ClauseSet_p neg_units = saturation_proofstate->processed_neg_units;

    assert(pos_eqns);
    assert(pos_rules);
    assert(neg_units);

    handle = pos_eqns->anchor->succ;
    while (handle != pos_eqns->anchor)
    {
        if (ClauseIsGround(handle))
        {
            copied = ClauseCopy(handle, tableau_bank);
            ClauseSetInsert(to, copied);
            number_copied++;
        }
        handle = handle->succ;
    }
    handle = pos_rules->anchor->succ;
    while (handle != pos_rules->anchor)
    {
        if (ClauseIsGround(handle))
        {
            copied = ClauseCopy(handle, tableau_bank);
            ClauseSetInsert(to, copied);
            number_copied++;
        }
        handle = handle->succ;
    }
    handle = neg_units->anchor->succ;
    while (handle != neg_units->anchor)
    {
        if (ClauseIsGround(handle))
        {
            copied = ClauseCopy(handle, tableau_bank);
            ClauseSetInsert(to, copied);
            number_copied++;
        }
        handle = handle->succ;
    }
    ClauseSetDelProp(to, CPIsDIndexed | CPIsSIndexed | CPIsGlobalIndexed);
    //if (status == PROOF_FOUND)
    //{
        //printf("copied %ld clauses from the proofstate up\n", number_copied);
    //}
    //else
    //{
        //printf("copied %ld clauses from the proofstate in place\n", number_copied);
    //}
    return number_copied;
}

/*
** TODO
** Thoughts about how we can maintain multiple proofstates at once:
** Whenever we do a branch saturation, look for an available saturation proofstate above the saturation node
** If one is found, move the found proofstate to the saturation node
** This function always assigns a saturation proofstate to the leaf node it is called on.
*/

ProofState_p EtableauUpdateSaturationState(ClauseTableau_p leaf,
                                           bool* created_new_proofstate)
{
    assert(*created_new_proofstate == false);
    assert(leaf != leaf->master);
    int height = 0;
    ClauseTableau_p climber = leaf;
    while (climber)
    {
        if (climber->saturation_state)
        {
            Warning("Reusing existing saturation proofstate %d", height);
            ProofState_p discovered_proofstate = climber->saturation_state;
            assert(discovered_proofstate->unprocessed);
            climber->saturation_state = NULL;
            leaf->saturation_state = discovered_proofstate;
            return leaf->saturation_state;
        }
        height++;
        climber = climber->parent;
    }
    assert(!(leaf->saturation_state));
    Warning("Creating new saturation proofstate");
    leaf->saturation_state = etableau_proofstate_alloc(leaf->state);
    *created_new_proofstate = true;
    return leaf->saturation_state;
}


// End of file
