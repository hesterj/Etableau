#include<etab_newproc.h>

extern void c_smoketest();

int Etableau_n0(TableauControl_p tableaucontrol,
               ProofState_p proofstate,
               ProofControl_p proofcontrol,
               TB_p bank,
               ClauseSet_p active,
               int max_depth,
               int tableauequality)
{
    if(geteuid() == 0) Error("# Please do not run Etableau as root.", 1);
    ClauseSetFreeClauses(proofstate->archive);
    APRVerify();
    c_smoketest();

    bool proof_found = false;
    problemType = PROBLEM_FO;
    FunCode max_var = ClauseSetGetMaxVar(active);
    // Create a new copy of the unprocesed axioms...
    tableaucontrol->unprocessed = ClauseSetCopy(bank, proofstate->unprocessed);
    GCAdmin_p gc = proofstate->gc_terms;
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
    ClauseSet_p unit_axioms = ClauseSetAlloc();
    ClauseSetMoveUnits(extension_candidates, unit_axioms);
    ClauseSetCopyUnits(bank, start_rule_candidates, unit_axioms);

    GCRegisterClauseSet(gc, unit_axioms);
    GCRegisterClauseSet(gc, extension_candidates);
    GCRegisterClauseSet(gc, tableaucontrol->unprocessed);

    //  At this point, all that is left in extension_candidates are non-conjecture non-unit clauses.
    //  The conjecture non-unit clauses will be added to extension candidates later.

    TableauStack_p distinct_tableaux_stack = EtableauCreateStartRulesStack(proofstate,
                                                                           proofcontrol,
                                                                           bank,
                                                                           max_var,
                                                                           unit_axioms,
                                                                           start_rule_candidates,
                                                                           tableaucontrol);

    if (tableaucontrol->closed_tableau)
    {
        EtableauStatusReport(tableaucontrol, active, tableaucontrol->closed_tableau);
        proof_found = true;
    }
   if (PStackEmpty(distinct_tableaux_stack))
   {
       Error("There are no tableaux!", 10);
   }
   ClauseTableau_p initial_example = PStackElementP(distinct_tableaux_stack, 0);
   if (!initial_example)
   {
       Error("Unable to find a tableau!", 10);
   }
   else if (!initial_example->label)
   {
       Error("Initial tableau has no label!", 10);
   }

// Do a branch saturation on the original problem before diving in to the tableaux proofsearch
   if (!proof_found && tableaucontrol->branch_saturation_enabled)
   {
       // The maximum number of tableaux to attmept to saturate before moving on is the last paramater of the below function
       proof_found = EtableauSaturateAllTableauxInStack(tableaucontrol, distinct_tableaux_stack, active, 30);
   }
   else
   {
        fprintf(GlobalOut, "# NOT attempting initial tableau saturation\n");
   }

   ClauseSetFreeUnits(start_rule_candidates);
   ClauseSetInsertSet(extension_candidates, start_rule_candidates);  // Now that all of the start rule tableaux have been created, non-unit start_rules can be made extension candidates.
   ClauseSetFree(start_rule_candidates);
   fprintf(GlobalOut, "# %ld start rule tableaux created.\n", PStackGetSP(distinct_tableaux_stack));
   fprintf(GlobalOut, "# %ld extension rule candidate clauses\n", extension_candidates->members);
   printf("\n");

   // Now do proof search...

   if (!proof_found && tableaucontrol->multiprocessing_active != 0)
   {
       proof_found = EtableauMultiprocess_n(tableaucontrol,
                                            distinct_tableaux_stack,
                                            active,
                                            extension_candidates,
                                            max_depth);

   }
   else if (!proof_found)
   {
       proof_found = EtableauProofSearchAtDepthWrapper_n1(tableaucontrol,
                                                         distinct_tableaux_stack,
                                                         active,
                                                         extension_candidates,
                                                         max_depth,
                                                         NULL);
   }

   // Proof search is over
   fprintf(GlobalOut, "# Proof search is over...\n");

   GCDeregisterClauseSet(gc, extension_candidates);
   ClauseSetFree(extension_candidates);
   GCDeregisterClauseSet(gc, unit_axioms);
   ClauseSetFree(unit_axioms);
   GCDeregisterClauseSet(gc, tableaucontrol->unprocessed);
   ClauseSetFree(tableaucontrol->unprocessed);

   TableauStackFree(distinct_tableaux_stack);

   // Memory is cleaned up...

   if (proof_found) // success
   {
       return 1;
   }
   // failure
   if (proof_found == false)
   {
       TSTPOUT(GlobalOut, "ResourceOut");
   }
   return 0;
}

ClauseTableau_p EtableauProofSearch_n3(TableauControl_p tableaucontrol,
                                      ClauseTableau_p master,
                                      ClauseSet_p extension_candidates,
                                      int current_depth,
                                      int max_depth,
                                      BacktrackStatus_p backtrack_status,
                                      TableauStack_p new_tableaux)
{
    assert(tableaucontrol);
    assert(master);
    assert(master->master == master);
    assert(extension_candidates);
    assert(current_depth);
    assert(master->label);
    assert(master->open_branches);
    //fprintf(GlobalOut, "# Current depth %d\n", current_depth);

    ClauseTableau_p (*branch_selection_function)(TableauSet_p, int, int, int*) = &branch_select;

    if ((UNLIKELY(new_tableaux))) branch_selection_function = &branch_select2; // If we are still populating, we cannot extend on previously extended branches
    //fprintf(stdout, " %p %d %d ", master, tableaucontrol->number_of_extensions, current_depth);

    int extensions_done = 0; // This allows us to keep track of the number of extensions done since the last backtrack
    int depth_status = DEPTH_OK;
    ClauseTableau_p open_branch = NULL, result = NULL;
    TableauSet_p open_branches = master->open_branches;
    while (true)
    {
        open_branch = (*branch_selection_function)(open_branches, current_depth, max_depth, &depth_status);
        if (depth_status == ALL_DEPTHS_EXCEEDED) // All of the open branches exceed our maximum depth, so we must backtrack
        {
            assert(!open_branch);
            //fprintf(stdout, "# Backtracking due to all depths exceeded, %ld remaining\n", PStackGetSP(master->master_backtracks));
            //fflush(stdout);
            bool backtrack_successful = BacktrackWrapper(master, true);
            if (!backtrack_successful)
            {
                *backtrack_status = BACKTRACK_FAILURE; // Failed backtrack, this tableau is no good.
                break;
            }
            depth_status = DEPTH_OK;
            continue; // We backtracked, try again
        }
        if (UNLIKELY(new_tableaux && depth_status == ALL_PREVIOUSLY_SELECTED))
        {
            //fprintf(GlobalOut, "# Moving to next tableau for population because all the possible branches were already extended\n");
            *backtrack_status = NEXT_TABLEAU;
            break;
        }
        else if (!open_branch) // All of the open branches exceed our current depth, so we must break and return in order to increase it
        {
            break;
        }
        //fprintf(GlobalOut, "# Selected open branch %p, %d extensions done so far, current depth %d\n", open_branch, tableaucontrol->number_of_extensions, current_depth);
        int extended = 0;
        assert(open_branch);
        assert(open_branch->id == 0);
        assert(open_branch->backtracks);
        assert(open_branch->depth < current_depth);
        assert(open_branch->failures);
        assert(open_branch->parent);
        assert(open_branch->parent->backtracks);
        assert(depth_status == DEPTH_OK);

        result = ClauseTableauSearchForPossibleExtension(tableaucontrol,
                                                         open_branch,
                                                         extension_candidates,
                                                         current_depth,
                                                         &extended,
                                                         new_tableaux);
        extensions_done += extended;

        if (result || (open_branches->members == 0)) // We have found a closed tableau
        {
            assert(tableaucontrol->closed_tableau == result);
            break;
        }
        if (UNLIKELY(new_tableaux))
        {
            assert(tableaucontrol->multiprocessing_active);
            //fprintf(GlobalOut, "# There are %ld new tableaux.\n", PStackGetSP(new_tableaux));
            if (PStackGetSP(new_tableaux) >= (long) tableaucontrol->multiprocessing_active)
            {
                *backtrack_status = RETURN_NOW;
                break;
            }
        }
        if (!new_tableaux && open_branch->set) // If the open branch is still in a set after the extension rule attempt, it means it was not able to be extended and so should be backtracked
        {
            //fprintf(GlobalOut, "# Backtracking due to branch still open, %ld remaining\n", PStackGetSP(master->master_backtracks));
            //DStrView(open_branch->info);
            //fprintf(GlobalOut, "^ info\n" );
            bool backtrack_successful = BacktrackWrapper(master, true);
            if (!backtrack_successful)
            {
                *backtrack_status = BACKTRACK_FAILURE; // Failed backtrack, this tableau is no good.
                break;
            }
        }
        else if (UNLIKELY(extended && tableaucontrol->number_of_extensions % 100 == 0))
        {
            *backtrack_status = NEXT_TABLEAU;
            break;
        }
    }

    if (UNLIKELY(new_tableaux)) ClauseTableauDeselectBranches(open_branches);
    //fprintf(stdout," %d\n", extensions_done);
    fflush(stdout);

    return result;
}

ClauseTableau_p EtableauProofSearchAtDepth_n2(TableauControl_p tableaucontrol,
                                             ClauseTableau_p master,
                                             ClauseSet_p extension_candidates,
                                             int max_depth,
                                             BacktrackStatus_p status,
                                             TableauStack_p new_tableaux)
{
   // Root is depth 0, initial start rule is depth 1, so first depth should be 2
   BacktrackStatus backtrack_status = BACKTRACK_OK;
   int current_depth = ClauseTableauGetShallowestBranch(master);
   //for (int current_depth = 2; current_depth < max_depth; current_depth++)
   while (current_depth < max_depth)
   {
       //fprintf(GlobalOut, "# Current depth %d\n", current_depth);
       ClauseTableau_p result = EtableauProofSearch_n3(tableaucontrol,
                                                      master,
                                                      extension_candidates,
                                                      current_depth,
                                                      max_depth,
                                                      &backtrack_status,
                                                      new_tableaux);
       *status = backtrack_status;
       if (result || master->open_branches->members == 0)
       {
           assert(tableaucontrol->closed_tableau == result);
           return result;
       }
       if (backtrack_status == BACKTRACK_FAILURE || backtrack_status == NEXT_TABLEAU || backtrack_status == RETURN_NOW)
       {
           break;
       }
       current_depth++;
   }

   return NULL;
}

bool EtableauMultiprocess_n(TableauControl_p tableaucontrol,
                            TableauStack_p starting_tableaux,
                            ClauseSet_p active,
                            ClauseSet_p extension_candidates,
                            int max_depth)
{
    bool proof_found = false;
    int num_cores_available = TableauControlGetCores(tableaucontrol);
    tableaucontrol->multiprocessing_active = num_cores_available;
    ClauseTableau_p resulting_tab = NULL;
    TableauStack_p new_tableaux = PStackAlloc();
    if (PStackGetSP(starting_tableaux) < num_cores_available)
    {
        fprintf(GlobalOut, "# There are not enough tableaux to fork, creating more\n");
        proof_found = EtableauProofSearchAtDepthWrapper_n1(tableaucontrol,
                                                          starting_tableaux,
                                                          active,
                                                          extension_candidates,
                                                          max_depth,
                                                          new_tableaux);
        fprintf(GlobalOut, "# We now have %ld tableaux to operate on\n", PStackGetSP(new_tableaux));
        if (resulting_tab)
        {
            fprintf(GlobalOut, "# Found closed tableau during pool population.\n");
            EtableauStatusReport(tableaucontrol, tableaucontrol->unprocessed, resulting_tab);
            TableauStackFree(new_tableaux);
            return true;
        }
    }
    else
    {
        while (!PStackEmpty(starting_tableaux))
        {
            assert(starting_tableaux->current);
            ClauseTableau_p start = PStackPopP(starting_tableaux);
            PStackPushP(new_tableaux, start);
        }
    }
    ///////////


    if (PStackGetSP(new_tableaux) < num_cores_available)
    {
        fprintf(GlobalOut, "# %ld tableaux and %d cores\n", PStackGetSP(new_tableaux), num_cores_available);
        Error("# Trying to fork with too few tableaux...", 1);
    }

    EPCtrlSet_p process_set = EPCtrlSetAlloc();
    PStack_p buckets = PStackAlloc();
    for (int i=0; i < num_cores_available; i++)
    {
        PStackPushP(buckets, PStackAlloc());
    }
    int tableaux_distributor = 0;
    while (!PStackEmpty(new_tableaux))
    {
        tableaux_distributor = tableaux_distributor % num_cores_available;
        assert(new_tableaux->current);
        ClauseTableau_p tab = PStackPopP(new_tableaux);
        TableauStack_p process_bucket = PStackElementP(buckets, tableaux_distributor);
        PStackPushP(process_bucket, tab);
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
            TableauStack_p new_tableaux = PStackElementP(buckets, i);
            assert(!PStackEmpty(new_tableaux));
            //TableauSetMoveClauses(distinct_tableaux_set, process_starting_tableaux);

            // should be good to go...
            proc->pipe = fdopen(pipefd[1], "w");
            GlobalOut = proc->pipe;
            close(pipefd[0]);
            tableaucontrol->process_control = proc;
            proof_found = EtableauProofSearchAtDepthWrapper_n1(tableaucontrol,
                                                               new_tableaux,
                                                               active,
                                                               extension_candidates,
                                                               max_depth,
                                                               NULL);
            TableauStackFree(new_tableaux);
            if (proof_found) exit(PROOF_FOUND);
            else exit(RESOURCE_OUT);
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
        TableauStack_p trash = PStackPopP(buckets);
        TableauStackFree(trash);
    }
    PStackFree(buckets);
    TableauStackFree(new_tableaux);
    return proof_found;
}

bool EtableauProofSearchAtDepthWrapper_n1(TableauControl_p tableaucontrol,
                                         TableauStack_p distinct_tableaux_stack,
                                          ClauseSet_p active,
                                         ClauseSet_p extension_candidates,
                                         int max_depth,
                                         TableauStack_p new_tableaux)
{
    bool proof_found = false;
    PStackPointer current_tableau_index = 0;
    PStackPointer current_new_tableaux_index = 0;
    ClauseTableau_p current_tableau = PStackElementP(distinct_tableaux_stack, current_tableau_index);
    BacktrackStatus status = BACKTRACK_OK;
    while (!proof_found)
    {
        //ClauseTableau_p closed_tableau = EtableauProofSearch_n(tableaucontrol, initial_example, extension_candidates, max_depth);
        ClauseTableau_p closed_tableau = EtableauProofSearchAtDepth_n2(tableaucontrol,
                                                                      current_tableau,
                                                                      extension_candidates,
                                                                      max_depth,
                                                                      &status,
                                                                      new_tableaux);
        if (closed_tableau || current_tableau->open_branches->members == 0)
        {
            fprintf(GlobalOut, "# Report status... proof found\n");
            EtableauStatusReport(tableaucontrol, active, closed_tableau);
            proof_found = true;
        }
        else
        {
            assert(status == BACKTRACK_FAILURE || status == NEXT_TABLEAU || status == RETURN_NOW);
            if (status == BACKTRACK_FAILURE)
            {
                PStackDiscardElement(distinct_tableaux_stack, current_tableau_index);
                ClauseTableauFree(current_tableau);
                current_tableau = NULL;
                current_tableau_index = 0;
            }
            //else if (status == NEXT_TABLEAU)
            //{
                //fprintf(GlobalOut, "# Switching from a tableau with %ld open branches because of extension limit.\n", current_tableau->open_branches->members);
            //}
            if (status == RETURN_NOW)
            {
                break;
            }
            current_tableau = EtableauGetNextTableau(distinct_tableaux_stack, &current_tableau_index, new_tableaux, &current_new_tableaux_index);
            if (current_tableau == NULL) break; // In case we ran out of tableaux...
        }
    }

    return proof_found;
}

ClauseTableau_p EtableauGetNextTableau(TableauStack_p distinct_tableaux_stack,
                                       PStackPointer *current_index_p,
                                       TableauStack_p new_tableaux,
                                       PStackPointer *current_new_tableaux_index_p)
{
    ClauseTableau_p new_current_tableau = NULL;
    (*current_index_p)++;
    if (*current_index_p >= PStackGetSP(distinct_tableaux_stack))
    {
        if (new_tableaux)
        {
            fprintf(GlobalOut, "# Extending on a tableau from the new tableau stack while populating\n");
            //if (*current_new_tableaux_index_p == PStackGetSP(new_tableaux))
            if (PStackEmpty(new_tableaux))
            {
                //TSTPOUT(GlobalOut, "ResourceOut");
                //fprintf(GlobalOut, "# There are %ld new_tableaux and %ld in distinct_tableaux_stack\n", PStackGetSP(new_tableaux), PStackGetSP(distinct_tableaux_stack));
                //Error("Ran out of tableaux to extend on while populating", 10);
                *current_index_p = 0;
                new_current_tableau = PStackElementP(distinct_tableaux_stack, *current_index_p);
                return new_current_tableau;
            }
            assert(new_tableaux->current);
            new_current_tableau = PStackPopP(new_tableaux);
            PStackPushP(distinct_tableaux_stack, new_current_tableau);
            return new_current_tableau;
        }
        if ( PStackEmpty(distinct_tableaux_stack) )
        {
            fprintf(GlobalOut, "# Unable to get any tableaux...\n");
            return NULL;
        }
        *current_index_p = 0;
    }
    assert(*current_index_p < distinct_tableaux_stack->current);
    new_current_tableau = PStackElementP(distinct_tableaux_stack, *current_index_p);
    return new_current_tableau;
}
