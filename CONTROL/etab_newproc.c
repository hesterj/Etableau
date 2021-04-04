#include<etab_newproc.h>

extern void c_smoketest();
bool all_tableaux_in_stack_are_root(TableauStack_p stack);
ClauseTableau_p get_next_tableau_population(TableauStack_p distinct_tableaux_stack,
                                            PStackPointer *current_index_p,
                                            TableauStack_p new_tableaux);
ClauseTableau_p get_next_tableau(TableauStack_p distinct_tableaux_stack,
                                 PStackPointer *current_index_p);

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

#ifdef FOLD
    fprintf(GlobalOut, "# The folding up rule is enabled...\n");
#else
    fprintf(GlobalOut, "# The folding up rule is disabled...\n");
#endif
#ifdef LOCAL
    fprintf(GlobalOut, "# Local unification is enabled...\n");
#else
    fprintf(GlobalOut, "# Local unification is disabled...\n");
#endif
#ifdef SATURATION_USES_FOLDING_LABELS
    fprintf(GlobalOut, "# Any saturation attempts will use folding labels...\n");
#else
    fprintf(GlobalOut, "# Any saturation attempts will not use folding labels...\n");
#endif

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

    //long unbound = TermBankUnbindAll(bank);
    //fprintf(GlobalOut, "# Unound %ld terms before tableau proof search...\n", unbound);
    ClauseSet_p start_rule_candidates = EtableauGetStartRuleCandidates(proofstate, extension_candidates);
    fprintf(GlobalOut, "# There are %ld start rule candidates:\n", start_rule_candidates->members);
    ClauseSet_p unit_axioms = ClauseSetAlloc();

    ClauseSetMoveUnits(extension_candidates, unit_axioms);
    ClauseSetCopyUnits(bank, start_rule_candidates, unit_axioms);
    ClauseSetCopyUnits(bank, proofstate->processed_neg_units, unit_axioms);
    ClauseSetCopyUnits(bank, proofstate->processed_pos_eqns, unit_axioms);
    ClauseSetCopyUnits(bank, proofstate->processed_pos_rules, unit_axioms);

    printf("# Found %ld unit axioms.\n", ClauseSetCardinality(unit_axioms));

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

   bool saturate_start_rules = true;
// Do a branch saturation on the original problem before diving in to the tableaux proofsearch
   if (saturate_start_rules && !proof_found && tableaucontrol->branch_saturation_enabled)
   {
       // The maximum number of tableaux to attmept to saturate before moving on is the last paramater of the below function
       proof_found = EtableauSaturateAllTableauxInStack(tableaucontrol, distinct_tableaux_stack, active, 30);
   }
   else
   {
        fprintf(GlobalOut, "# NOT attempting initial tableau saturation\n");
   }

   //ClauseSetFreeUnits(start_rule_candidates);
   ClauseSetInsertSet(extension_candidates, start_rule_candidates);  // Now that all of the start rule tableaux have been created, non-unit start_rules can be made extension candidates.
   assert(ClauseSetEmpty(start_rule_candidates));
   ClauseSetFree(start_rule_candidates);
   fprintf(GlobalOut, "# %ld start rule tableaux created.\n", PStackGetSP(distinct_tableaux_stack));
   fprintf(GlobalOut, "# %ld extension rule candidate clauses\n", extension_candidates->members);
   printf("\n");

   assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
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
       proof_found = EtableauProofSearch_n1(tableaucontrol,
                                            distinct_tableaux_stack,
                                            active,
                                            extension_candidates,
                                            max_depth);
   }

   // Proof search is over
   fprintf(GlobalOut, "# Proof search is over...\n");

   ClauseSetDelProp(extension_candidates, CPIsDIndexed);
   ClauseSetDelProp(extension_candidates, CPIsSIndexed);
   GCDeregisterClauseSet(gc, extension_candidates);
   ClauseSetFree(extension_candidates);
   ClauseSetDelProp(unit_axioms, CPIsDIndexed);
   ClauseSetDelProp(unit_axioms, CPIsSIndexed);
   GCDeregisterClauseSet(gc, unit_axioms);
   ClauseSetFree(unit_axioms);
   ClauseSetDelProp(tableaucontrol->unprocessed, CPIsDIndexed);
   ClauseSetDelProp(tableaucontrol->unprocessed, CPIsSIndexed);
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
                                      BacktrackStatus_p backtrack_status)
{
    assert(tableaucontrol);
    assert(master);
    assert(master->master == master);
    assert(extension_candidates);
    assert(current_depth);
    assert(master->label);
    assert(master->open_branches);
    //fprintf(GlobalOut, "# Current depth %d\n", current_depth);


    int extensions_done = 0; // This allows us to keep track of the number of extensions done since the last backtrack
    int depth_status = DEPTH_OK;
    ClauseTableau_p open_branch = NULL, result = NULL;
    TableauSet_p open_branches = master->open_branches;
    while (true)
    {
        open_branch = branch_select(open_branches, current_depth, max_depth, &depth_status);
        if (depth_status == ALL_DEPTHS_EXCEEDED) // All of the open branches exceed our maximum depth, so we must backtrack
        {
            assert(!open_branch);
            //fprintf(stdout, "# Backtracking due to all depths exceeded, %ld remaining\n", PStackGetSP(master->master_backtracks));
            bool backtrack_successful = BacktrackWrapper(master);
            if (!backtrack_successful)
            {
                *backtrack_status = BACKTRACK_FAILURE; // Failed backtrack, this tableau is no good.
                break;
            }
            depth_status = DEPTH_OK;
            continue; // We backtracked, try again
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
        assert(open_branch->master == master);
        assert(depth_status == DEPTH_OK);

        result = ClauseTableauSearchForPossibleExtension(tableaucontrol,
                                                         open_branch,
                                                         extension_candidates,
                                                         current_depth,
                                                         &extended,
                                                         NULL);
        extensions_done += extended;
        assert(open_branch->master == master);

        if (result || (open_branches->members == 0)) // We have found a closed tableau
        {
            assert(tableaucontrol->closed_tableau == result);
            break;
        }
        if (open_branch->set) // If the open branch is still in a set after the extension rule attempt, it means it was not able to be extended and so should be backtracked
        {
            assert(!extended);
            //printf("backtracking due to extension failure\n");
            bool backtrack_successful = BacktrackWrapper(master);
            if (!backtrack_successful)
            {
                *backtrack_status = BACKTRACK_FAILURE; // Failed backtrack, this tableau is no good.
                break;
            }
        }
        else if (tableaucontrol->number_of_extensions % 100 == 0)
        {
            *backtrack_status = NEXT_TABLEAU;
            break;
        }
    }

    assert(open_branches);
    assert(master->open_branches == open_branches);

    assert(master->master == master);
    return result;
}

ClauseTableau_p EtableauPopulate_n3(TableauControl_p tableaucontrol,
                                    ClauseTableau_p master,
                                    ClauseSet_p extension_candidates,
                                    int current_depth,
                                    int max_depth,
                                    BacktrackStatus_p backtrack_status,
                                    TableauStack_p new_tableaux)
{
    assert(new_tableaux);
    assert(tableaucontrol);
    assert(master);
    assert(master->master == master);
    assert(extension_candidates);
    assert(current_depth);
    assert(master->label);
    assert(master->open_branches);

    int extensions_done = 0; // This allows us to keep track of the number of extensions done since the last backtrack
    int depth_status = DEPTH_OK;
    ClauseTableau_p open_branch = NULL, result = NULL;
    TableauSet_p open_branches = master->open_branches;
    while (true)
    {
        open_branch = branch_select2(open_branches, current_depth, max_depth, &depth_status);
        if (depth_status == ALL_PREVIOUSLY_SELECTED || depth_status == ALL_DEPTHS_EXCEEDED)
        {
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
        assert(open_branch->master == master);
        assert(depth_status == DEPTH_OK);
        assert(tableaucontrol->multiprocessing_active);

        result = ClauseTableauSearchForPossibleExtension(tableaucontrol,
                                                         open_branch,
                                                         extension_candidates,
                                                         current_depth,
                                                         &extended,
                                                         new_tableaux);
        extensions_done += extended;
        assert(open_branch->master == master);

        if (result || (open_branches->members == 0)) // We have found a closed tableau
        {
            assert(tableaucontrol->closed_tableau == result);
            break;
        }
        if (PStackGetSP(new_tableaux) >= GetDesiredNumberOfTableaux(tableaucontrol))
        {
            *backtrack_status = RETURN_NOW;
            break;
        }
    }

    assert(open_branches);
    assert(master->open_branches == open_branches);

    ClauseTableauDeselectBranches(open_branches);

    assert(master->master == master);
    assert(all_tableaux_in_stack_are_root(new_tableaux));
    return result;
}

ClauseTableau_p EtableauPopulate_n2(TableauControl_p tableaucontrol,
                                    ClauseTableau_p master,
                                    ClauseSet_p extension_candidates,
                                    int max_depth,
                                    BacktrackStatus_p status,
                                    TableauStack_p new_tableaux)
{
   // Root is depth 0, initial start rule is depth 1, so first depth should be 2
   BacktrackStatus backtrack_status = BACKTRACK_OK;
   ClauseTableau_p result = NULL;
   //int current_depth = ClauseTableauGetShallowestBranch(master);
   int current_depth = max_depth-1;
   assert(master->master == master);
   //while (current_depth < max_depth)
   while (true)
   {
       //fprintf(GlobalOut, "# Current depth %d\n", current_depth);
       assert(master->master == master);
       result = EtableauPopulate_n3(tableaucontrol,
                                       master,
                                       extension_candidates,
                                       current_depth,
                                       max_depth,
                                       &backtrack_status,
                                       new_tableaux);
       *status = backtrack_status;
       assert(master->master == master);
       if (result || master->open_branches->members == 0)
       {
           assert(tableaucontrol->closed_tableau == result);
           assert(master->master == master);
           break;
       }
       if (backtrack_status == BACKTRACK_FAILURE || backtrack_status == NEXT_TABLEAU || backtrack_status == RETURN_NOW)
       {
           break;
       }
       current_depth++;
   }
   assert(master->master == master);
   assert(all_tableaux_in_stack_are_root(new_tableaux));

   // If we have reached the maximum depth, we need to select the next tableau.

  // if (current_depth == max_depth) backtrack_status = NEXT_TABLEAU;

   return result;
}

ClauseTableau_p EtableauProofSearch_n2(TableauControl_p tableaucontrol,
                                       ClauseTableau_p master,
                                       ClauseSet_p extension_candidates,
                                       int max_depth,
                                       BacktrackStatus_p status)
{
   // Root is depth 0, initial start rule is depth 1, so first depth should be 2
   BacktrackStatus backtrack_status = BACKTRACK_OK;
   ClauseTableau_p result = NULL;
   int current_depth = ClauseTableauGetShallowestBranch(master);
   assert(master->master == master);
   while (current_depth < max_depth)
   {
       //fprintf(GlobalOut, "# Current depth %d\n", current_depth);
       assert(master->master == master);
       result = EtableauProofSearch_n3(tableaucontrol,
                                       master,
                                       extension_candidates,
                                       current_depth,
                                       max_depth,
                                       &backtrack_status);
       *status = backtrack_status;
       assert(master->master == master);
       if (result || master->open_branches->members == 0)
       {
           assert(tableaucontrol->closed_tableau == result);
           assert(master->master == master);
           break;
       }
       if (backtrack_status == BACKTRACK_FAILURE || backtrack_status == NEXT_TABLEAU || backtrack_status == RETURN_NOW)
       {
           break;
       }
       current_depth++;
   }
   assert(master->master == master);

   // If we have reached the maximum depth, we need to select the next tableau.

  // if (current_depth == max_depth) backtrack_status = NEXT_TABLEAU;

   return result;
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
    TableauStack_p new_tableaux = PStackAlloc();
    if (PStackGetSP(starting_tableaux) < num_cores_available)
    {
        fprintf(GlobalOut, "# There are not enough tableaux to fork, creating more from the initial %ld\n", PStackGetSP(starting_tableaux));
        proof_found = EtableauPopulate_n1(tableaucontrol,
                                          starting_tableaux,
                                          active,
                                          extension_candidates,
                                          max_depth,
                                          new_tableaux);
        fprintf(GlobalOut, "# We now have %ld tableaux to operate on\n", PStackGetSP(new_tableaux));
        if (proof_found)
        {
            fprintf(GlobalOut, "# Found closed tableau during pool population.\n");
            fflush(GlobalOut);
            assert(tableaucontrol->closed_tableau);
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
            assert(start->master == start);
            PStackPushP(new_tableaux, start);
        }
    }
    ///////////
    ///////////
    assert(false);

//#ifndef NDEBUG
    //printf("printing hashes of tableaux\n");
    //printf("there are %ld starting tableaux\n", PStackGetSP(starting_tableaux));
    //for (PStackPointer p=0; p<PStackGetSP(new_tableaux); p++)
    //{
        //ClauseTableau_p new_t = PStackElementP(new_tableaux, p);
        //assert(new_t->master == new_t);
        //printf("%ld %ld %f\n", ClauseTableauHash(new_t), PStackGetSP(new_t->master->master_backtracks), ClauseTableauGetAverageDepth(new_t));
    //}
    //printf("done printing hashes\n");
    //fflush(stdout);
//#endif

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
        assert(tab->master == tab);
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
            TableauStack_p new_tableaux = PStackElementP(buckets, i);
//#ifndef NDEBUG
            //printf("%ld tableaux in new process %d\n", PStackGetSP(new_tableaux), i);
            //fflush(stdout);
//#endif

            // should be good to go...
            proc->pipe = fdopen(pipefd[1], "w");
            GlobalOut = proc->pipe;
            close(pipefd[0]);
            tableaucontrol->process_control = proc;
            proof_found = EtableauProofSearch_n1(tableaucontrol,
                                                 new_tableaux,
                                                 active,
                                                 extension_candidates,
                                                 max_depth);
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
    fflush(stdout);
    fflush(GlobalOut);
    while (!PStackEmpty(buckets))
    {
        TableauStack_p trash = PStackPopP(buckets);
        TableauStackFree(trash);
    }
    PStackFree(buckets);
    TableauStackFree(new_tableaux);
#ifndef NDEBUG
    printf("# My mother is a fish\n");
#endif
    return proof_found;
}

bool EtableauProofSearch_n1(TableauControl_p tableaucontrol,
                            TableauStack_p distinct_tableaux_stack,
                            ClauseSet_p active,
                            ClauseSet_p extension_candidates,
                            int max_depth)
{
    if (PStackEmpty(distinct_tableaux_stack))
    {
        Warning("No tableaux for proof search...");
        return false;
    }
    assert(tableaucontrol);
    assert(distinct_tableaux_stack);
    assert(active);
    assert(extension_candidates);
    assert(!ClauseSetEmpty(extension_candidates));
    bool proof_found = false;
    PStackPointer current_tableau_index = -1;
    ClauseTableau_p current_tableau = NULL;
    while ((current_tableau = get_next_tableau(distinct_tableaux_stack,
                                               &current_tableau_index)))
    {
        assert(current_tableau && "We must have a tableau for proof search...");
        assert(current_tableau->master == current_tableau && "The current tableau must be the root node of the tableau");
        BacktrackStatus tableau_status = BACKTRACK_OK;
        ClauseTableau_p closed_tableau = EtableauProofSearch_n2(tableaucontrol,
                                                                current_tableau,
                                                                extension_candidates,
                                                                max_depth,
                                                                &tableau_status);
        assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
        if (closed_tableau || current_tableau->open_branches->members == 0)
        {
            assert(tableaucontrol->closed_tableau == closed_tableau);
            EtableauStatusReport(tableaucontrol, active, closed_tableau);
            proof_found = true;
            break;
        }
        else
        {
            assert(current_tableau->master == current_tableau);
            switch (tableau_status)
            {
                case BACKTRACK_OK: // This should only happen during population, when all possible extension up to a depth have been made on a tableau
                {
                    assert(false && "Backtrack OK should not happen during normal proof search");
                    break;
                }
                case BACKTRACK_FAILURE: // We never backtrack during population
                {
                    assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
                    assert(PStackElementP(distinct_tableaux_stack, current_tableau_index) == current_tableau);
                    PStackDiscardElement(distinct_tableaux_stack, current_tableau_index);
                    ClauseTableauFree(current_tableau);
                    current_tableau_index = 0;
                    assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
                    //printf("got signal btf in normal proof search\n");
                    break;
                }
                case NEXT_TABLEAU:
                {
                    assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
                    break;
                }
                case RETURN_NOW:
                {
                    //printf("About to give up...\n");
                    goto return_point;
                }
                default:
                {
                    Error("Unknown tableau status in n1", 100);
                }
            }
        }
    }

    return_point:
    return proof_found;
}

bool EtableauPopulate_n1(TableauControl_p tableaucontrol,
                         TableauStack_p distinct_tableaux_stack,
                         ClauseSet_p active,
                         ClauseSet_p extension_candidates,
                         int max_depth,
                         TableauStack_p new_tableaux)
{
    assert(new_tableaux);
    if (PStackEmpty(distinct_tableaux_stack))
    {
        Warning("No tableaux for proof search...");
        return false;
    }
    assert(tableaucontrol);
    assert(distinct_tableaux_stack);
    assert(active);
    assert(extension_candidates);
    assert(!ClauseSetEmpty(extension_candidates));
    bool proof_found = false;
    PStackPointer current_tableau_index = -1;
    ClauseTableau_p current_tableau = NULL;
    //while (!proof_found)
    while ((current_tableau = get_next_tableau_population(distinct_tableaux_stack,
                                                          &current_tableau_index,
                                                          new_tableaux)))
    {
        assert(current_tableau && "We must have a tableau for proof search...");
        assert(current_tableau->master == current_tableau && "The current tableau must be the root node of the tableau");
        //printf("iter %ld:%ld\n", current_tableau_index, PStackGetSP(distinct_tableaux_stack));
        assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
        BacktrackStatus tableau_status = BACKTRACK_OK;
        ClauseTableau_p closed_tableau = EtableauPopulate_n2(tableaucontrol,
                                                             current_tableau,
                                                             extension_candidates,
                                                             max_depth,
                                                             &tableau_status,
                                                             new_tableaux);
        assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
        if (UNLIKELY(current_tableau_index >= 10000)) tableau_status = RETURN_NOW;
        if (closed_tableau || current_tableau->open_branches->members == 0)
        {
            assert(tableaucontrol->closed_tableau == closed_tableau);
            //fprintf(GlobalOut, "# Reporting status (n1), a proof was found.\n");
            EtableauStatusReport(tableaucontrol, active, closed_tableau);
            proof_found = true;
            break;
        }
        else
        {
            assert(current_tableau->master == current_tableau);
            switch (tableau_status)
            {
                case BACKTRACK_OK: // This should only happen during population, when all possible extension up to a depth have been made on a tableau
                {
                    assert(false && "We should not get BACKTRACK_OK status in population");
                    break;
                }
                case BACKTRACK_FAILURE: // We never backtrack during population
                {
                    assert(false && "We should not get BACKTRACK_FAILURE status in population");
                    break;
                }
                case NEXT_TABLEAU:
                {
                    assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
                    break;
                }
                case RETURN_NOW:
                {
                    goto return_point;
                }
                default:
                {
                    Error("Unknown tableau status in n1", 100);
                }
            }
        }
    }

    printf("Returning from population with %ld new_tableaux and %ld remaining starting tableaux.\n",
            PStackGetSP(new_tableaux),
            PStackGetSP(distinct_tableaux_stack));
    assert(all_tableaux_in_stack_are_root(new_tableaux));
    while (!PStackEmpty(distinct_tableaux_stack))
    {
        ClauseTableau_p start = PStackPopP(distinct_tableaux_stack);
        assert(start->master == start);
        PStackPushP(new_tableaux, start);
    }
    return_point:
    return proof_found;
}

ClauseTableau_p get_next_tableau_population(TableauStack_p distinct_tableaux_stack,
                                            PStackPointer *current_index_p,
                                            TableauStack_p new_tableaux)
{
    ClauseTableau_p new_current_tableau = NULL;
    assert(new_tableaux);
    (*current_index_p)++;
    assert(*current_index_p >= 0);
    if (*current_index_p >= PStackGetSP(distinct_tableaux_stack))
    {
        if (!PStackEmpty(new_tableaux))
        {
            new_current_tableau = PStackPopP(new_tableaux);
            assert(new_current_tableau->master == new_current_tableau);
        }
    }
    else
    {
        new_current_tableau = PStackElementP(distinct_tableaux_stack, *current_index_p);
        assert(new_current_tableau->master == new_current_tableau);
    }

    if (!new_current_tableau)
    {
        printf("no new tableau...\n");
    }
    else
    {
        printf("found new tableau, %ld new remaining, %ld distinct\n", PStackGetSP(new_tableaux), PStackGetSP(distinct_tableaux_stack));
    }

    return new_current_tableau;
}

ClauseTableau_p get_next_tableau(TableauStack_p distinct_tableaux_stack,
                                 PStackPointer *current_index_p)
{
    ClauseTableau_p new_current_tableau = NULL;
    (*current_index_p)++;
    assert(*current_index_p >= 0);
    if (*current_index_p >= PStackGetSP(distinct_tableaux_stack))
    {
        if (!PStackEmpty(distinct_tableaux_stack) )
        {
            *current_index_p = 0;
            new_current_tableau = PStackElementP(distinct_tableaux_stack, *current_index_p);
            assert(new_current_tableau->master == new_current_tableau);
        }
    }
    else
    {
        new_current_tableau = PStackElementP(distinct_tableaux_stack, *current_index_p);
        assert(new_current_tableau->master == new_current_tableau);
    }

    return new_current_tableau;
}

bool all_tableaux_in_stack_are_root(TableauStack_p stack)
{
    if (!stack) return true;
    for (PStackPointer p=0; p< PStackGetSP(stack); p++)
    {
        ClauseTableau_p tab = PStackElementP(stack, p);
        if (tab->master != tab)
        {
            printf("failure at %ld\n", p);
            printf("%ld d:%d %ld\n", ClauseTableauHash(tab), tab->depth, ClauseTableauHash(tab->master));
            return false;
        }
    }
    return true;
}
