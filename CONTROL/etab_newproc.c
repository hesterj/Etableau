#include"etab_newproc.h"

/*
** Function declarations
*/

extern void c_smoketest();
bool all_tableaux_in_stack_are_root(TableauStack_p stack);
ClauseTableau_p get_next_tableau_population(TableauStack_p distinct_tableaux_stack,
                                            PStackPointer *current_index_p,
                                            TableauStack_p new_tableaux,
                                            TableauControl_p tableaucontrol,
                                            ClauseSet_p active,
                                            ClauseSet_p extension_candidates);
ClauseTableau_p get_next_tableau(TableauStack_p distinct_tableaux_stack,
                                 PStackPointer *current_index_p,
                                 TableauControl_p tableaucontrol,
                                 ClauseSet_p active,
                                 ClauseSet_p extension_candidates);
long create_all_start_rules(TableauControl_p tableaucontrol,
                        TableauStack_p stack,
                        ClauseSet_p active);
ClauseTableau_p branch_select_new(TableauSet_p open_branches, int max_depth);
ClauseTableau_p branch_select(TableauSet_p open_branches, int max_depth);
long add_equality_axioms_to_state(TableauControl_p tableaucontrol,
                                  ClauseSet_p active,
                                  ClauseSet_p extension_candidates);
static inline bool can_restart(TableauControl_p tableaucontrol,
                               TableauStack_p stack,
                               ClauseSet_p active);


/*
** Function Definitions
 */

/*
** This selection function returns the deepest branch found shallower than max depth.
*/

ClauseTableau_p branch_select(TableauSet_p open_branches, int max_depth)
{
    assert(open_branches);
    ClauseTableau_p selected = NULL;
    int selected_depth = 0;
    ClauseTableau_p branch = open_branches->anchor->succ;
    while (branch != open_branches->anchor)
    {
        assert(branch);
        assert(branch->label);
        assert(branch->arity == 0);
        assert(branch->children == NULL);
        assert(branch->label);
        if (branch->depth < max_depth && branch->depth > selected_depth)
        {
            selected_depth = branch->depth;
            selected = branch;
        }
        branch = branch->succ;
    }
    return selected;
}
/*
** This selection function returns the first branch found shallower than max depth that has not been previously selected.
*/

ClauseTableau_p branch_select_new(TableauSet_p open_branches, int max_depth)
{
    assert(open_branches);
    ClauseTableau_p selected = NULL;
    ClauseTableau_p branch = open_branches->anchor->succ;
    while (branch != open_branches->anchor)
    {
        assert(branch);
        assert(branch->label);
        assert(branch->arity == 0);
        assert(branch->children == NULL);
        assert(branch->label);
        if (branch->depth < max_depth && !ClauseTableauQueryProp(branch, TUPHasBeenPreviouslySelected))
        {
            ClauseTableauSetProp(branch, TUPHasBeenPreviouslySelected);
            return branch;
        }
        branch = branch->succ;
    }
    return selected;
}

int Etableau_n0(TableauControl_p tableaucontrol,
                ProofState_p proofstate,
                ProofControl_p proofcontrol,
                TB_p bank,
                ClauseSet_p active,
                unsigned long maximum_depth,
                int tableauequality)
{
    //max_depth = 2;
    if(geteuid() == 0) Error("# Please do not run Etableau as root.", 1);
    ClauseSetFreeClauses(proofstate->archive);
    APRVerify();
    c_smoketest();
#ifdef XGBOOST_FLAG
    XGBoostTest();
#endif

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
    // Create a new copy of the unprocesed axioms...

    //assert(tableauequality == 0 || tableauequality ==1);
    if (tableauequality == 1 || (tableauequality == 2 && ClauseSetIsEquational(active)))
    {
        //ClauseSet_p equality_axioms = EqualityAxioms(bank);
        //ClauseSet_p equality_axioms = apr_EqualityAxioms(bank, true);
        ClauseSet_p equality_axioms = EqualityAxiomsWithSubstitution(bank, active, true);
        fprintf(GlobalOut, "# Adding %ld equality axioms\n", equality_axioms->members);
        ClauseSetInsertSet(active, equality_axioms);
        ClauseSetFree(equality_axioms);
        tableaucontrol->equality_axioms_added = true;
    }
    tableaucontrol->unprocessed = ClauseSetCopy(bank, proofstate->unprocessed);
    GCAdmin_p gc = proofstate->gc_terms;
    fprintf(GlobalOut, "# %ld beginning clauses after preprocessing and clausification\n", active->members);
    ClauseSet_p extension_candidates = ClauseSetCopy(bank, active);

    //long unbound = TermBankUnbindAll(bank);
    //fprintf(GlobalOut, "# Unound %ld terms before tableau proof search...\n", unbound);
    ClauseSet_p start_rule_candidates = EtableauGetStartRuleCandidates(tableaucontrol,
                                                                       proofstate,
                                                                       extension_candidates);
    fprintf(GlobalOut, "# There are %ld start rule candidates:\n", start_rule_candidates->members);
    ClauseSet_p unit_axioms = ClauseSetAlloc();

    ClauseSetMoveUnits(extension_candidates, unit_axioms);
    ClauseSetCopyUnits(bank, start_rule_candidates, unit_axioms);
    ClauseSetCopyUnits(bank, proofstate->processed_neg_units, unit_axioms);
    ClauseSetCopyUnits(bank, proofstate->processed_pos_eqns, unit_axioms);
    ClauseSetCopyUnits(bank, proofstate->processed_pos_rules, unit_axioms);

    ClauseSet_p disjoint_unit_axioms = ClauseSetCopyDisjoint(bank, unit_axioms);
    ClauseSetFree(unit_axioms);
    unit_axioms = disjoint_unit_axioms;
    //ClauseSetPrint(stdout, unit_axioms, true);

    printf("# Found %ld unit axioms.\n", ClauseSetCardinality(unit_axioms));

    GCRegisterClauseSet(gc, unit_axioms);
    GCRegisterClauseSet(gc, extension_candidates);
    GCRegisterClauseSet(gc, tableaucontrol->unprocessed);

    //  At this point, all that is left in extension_candidates are non-unit clauses.
    //  The conjecture non-unit clauses will be added to extension candidates later.

    TableauStack_p distinct_tableaux_stack = EtableauCreateStartRulesStack(bank,
                                                                           unit_axioms,
                                                                           start_rule_candidates,
                                                                           tableaucontrol,
                                                                           maximum_depth);

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
   if (tableaucontrol->saturate_start_rules && !proof_found && tableaucontrol->branch_saturation_enabled)
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
   assert(ClauseSetEmpty(start_rule_candidates));
   ClauseSetFree(start_rule_candidates);
   fprintf(GlobalOut, "# %ld start rule tableaux created.\n", PStackGetSP(distinct_tableaux_stack));
   fprintf(GlobalOut, "# %ld extension rule candidate clauses\n", extension_candidates->members);
   fprintf(GlobalOut, "# %ld unit axiom clauses\n", unit_axioms->members);
   printf("\n");

   assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
   // Now do proof search...
   //TableauControlInitializeZMQ(tableaucontrol);

   if (!proof_found && tableaucontrol->multiprocessing_active != 0)
   {
       proof_found = EtableauMultiprocess(tableaucontrol,
                                          distinct_tableaux_stack,
                                          active,
                                          extension_candidates,
                                          maximum_depth);

   }
   else if (!proof_found)
   {
       proof_found = EtableauSelectTableau(tableaucontrol,
                                            distinct_tableaux_stack,
                                            active,
                                            extension_candidates);
   }
   //TableauControlDeleteZMQ(tableaucontrol);

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

ClauseTableau_p EtableauSelectBranchAndExtend(TableauControl_p tableaucontrol,
                                              ClauseTableau_p master,
                                              ClauseSet_p extension_candidates,
                                              BacktrackStatus_p backtrack_status)
{
    assert(tableaucontrol);
    assert(master);
    assert(master->master == master);
    assert(extension_candidates);
    assert(master->label);
    assert(master->open_branches);


    int extensions_done = 0; // This allows us to keep track of the number of extensions done since the last backtrack
    long big_backtracks = 0;
    //int depth_status = DEPTH_OK;
    ClauseTableau_p selected_branch = NULL, result = NULL;
    TableauSet_p open_branches = master->open_branches;
    while (true)
    {
        selected_branch = branch_select(open_branches, MaximumDepth(master));
        if (!selected_branch)
        {
#ifdef BIGJUMP
            long number_of_open_branches = master->open_branches->members;
            long previous_bigjump_open_branches = LONG_MAX;
            if (master->bigjump)
            {
                previous_bigjump_open_branches = master->bigjump->open_branches->members;
            }
            if (number_of_open_branches < ceil(previous_bigjump_open_branches/2))
            {
                if (master->bigjump)
                {
                    ClauseTableauFree(master->bigjump);
                }
                printf("# Copying a better bigjump, %ld < %ld\n", number_of_open_branches, previous_bigjump_open_branches);
                master->bigjump = ClauseTableauMasterCopy(master);
                master->bigjump->unit_axioms = ClauseSetCopy(master->terms, master->unit_axioms);
            }
#endif
            ClauseTableauSetProp(master, TUPBacktrackedDueToMaxDepth);
            bool backtrack_successful = true;
            if ((big_backtracks = tableaucontrol->tableaubigbacktrack))
            {
                backtrack_successful = BacktrackMultiple(master, BacktrackReasonMaxDepth, big_backtracks);
            }
            else
            {
                backtrack_successful = BacktrackWrapper(master, BacktrackReasonMaxDepth);
            }
            if (!backtrack_successful)
            {
                ETAB_VERBOSE(printf("# Backtrack failed because we couldn't select a branch (depth)\n");)
                *backtrack_status = BACKTRACK_FAILURE; // Failed backtrack, this tableau is no good.
                break;
            }
            ETAB_VERBOSE(printf("# Backtrack successful (depth)\n");)
            continue; // We backtracked, try again
        }
        ETAB_VERBOSE(printf("# Selected a new branch\n");)

        int extended = 0;
        assert(selected_branch);
        assert(selected_branch->id == 0);
        assert(selected_branch->backtracks);
        assert(selected_branch->failures);
        assert(selected_branch->parent);
        assert(selected_branch->parent->backtracks);
        assert(selected_branch->master == master);

        result = ClauseTableauSearchForPossibleExtension(tableaucontrol,
                                                         selected_branch,
                                                         extension_candidates,
                                                         &extended,
                                                         NULL);


        extensions_done += extended;
        assert(selected_branch->master == master);

        if (result || (open_branches->members == 0)) // We have found a closed tableau
        {
            assert(tableaucontrol->closed_tableau == result);
            break;
        }
        if (BranchIsOpen(selected_branch)) // If the open branch is still open after the extension rule attempt, it means it was not able to be extended and so we need to backtrack
        {
            assert(!extended);
            ClauseTableauSetProp(master, TUPBacktrackedDueToExtensionFailure);
            bool backtrack_successful = true;
            backtrack_successful = BacktrackWrapper(master, BacktrackReasonExtensionFailure);
            if (!backtrack_successful)
            {
                ETAB_VERBOSE(printf("# Backtrack failed (couldn't extend branch)\n");)
                *backtrack_status = BACKTRACK_FAILURE; // Failed backtrack, this tableau is no good.
                break;
            }
            ETAB_VERBOSE(printf("# Backtrack successful (couldn't extend branch)\n");)
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

ClauseTableau_p EtableauPopulationSelectBranchAndExtend(TableauControl_p tableaucontrol,
                                    ClauseTableau_p master,
                                    ClauseSet_p extension_candidates,
                                    BacktrackStatus_p backtrack_status,
                                    TableauStack_p new_tableaux)
{
    assert(new_tableaux);
    assert(tableaucontrol);
    assert(master);
    assert(master->master == master);
    assert(extension_candidates);
    assert(master->label);
    assert(master->open_branches);

    int extensions_done = 0; // This allows us to keep track of the number of extensions done since the last backtrack
    //int depth_status = DEPTH_OK;
    ClauseTableau_p open_branch = NULL, result = NULL;
    TableauSet_p open_branches = master->open_branches;
    while (true)
    {
        //open_branch = branch_select2(open_branches, current_depth, max_depth, &depth_status);
        open_branch = branch_select_new(open_branches, MaximumDepth(master));
        if (!open_branch)
        {
            *backtrack_status = NEXT_TABLEAU;
            break;
        }
        //fprintf(GlobalOut, "# Selected open branch %p, %d extensions done so far, current depth %d\n", open_branch, tableaucontrol->number_of_extensions, current_depth);
        int extended = 0;
        assert(open_branch);
        assert(open_branch->id == 0);
        assert(open_branch->backtracks);
        assert(open_branch->depth < MaximumDepth(open_branch));
        assert(open_branch->failures);
        assert(open_branch->parent);
        assert(open_branch->parent->backtracks);
        assert(open_branch->master == master);
        assert(tableaucontrol->multiprocessing_active);

        result = ClauseTableauSearchForPossibleExtension(tableaucontrol,
                                                         open_branch,
                                                         extension_candidates,
                                                         &extended,
                                                         new_tableaux);
        extensions_done += extended;
        assert(open_branch->master == master);
        ClauseTableauSetProp(master, TUPHasBeenExtendedOn);

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

bool EtableauMultiprocess(TableauControl_p tableaucontrol,
                          TableauStack_p starting_tableaux,
                          ClauseSet_p active,
                          ClauseSet_p extension_candidates,
                          unsigned long max_depth)
{
    bool proof_found = false;
    int num_cores_available = TableauControlGetCores(tableaucontrol);
    tableaucontrol->multiprocessing_active = num_cores_available;
    TableauStack_p new_tableaux = PStackAlloc();
    if (PStackGetSP(starting_tableaux) < num_cores_available)
    {
        fprintf(GlobalOut, "# There are not enough tableaux to fork, creating more from the initial %ld\n", PStackGetSP(starting_tableaux));
        proof_found = EtableauPopulation(tableaucontrol,
                                          starting_tableaux,
                                          active,
                                          extension_candidates,
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
        ClauseTableauDeleteAllProps(tab);
        DeleteAllBacktrackInformation(tab);
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
            TableauControlInitializeZMQ(tableaucontrol);
            TableauStack_p new_tableaux = PStackElementP(buckets, i);
            assert(problemType == PROBLEM_FO);

            // should be good to go...
            //proc->pipe = fdopen(pipefd[1], "w");
            //GlobalOut = proc->pipe;
            //close(pipefd[0]);
            GlobalOut = stdout;
            fflush(GlobalOut);
            tableaucontrol->process_control = proc;
            proof_found = EtableauSelectTableau(tableaucontrol,
                                                 new_tableaux,
                                                 active,
                                                 extension_candidates);
            TableauStackFree(new_tableaux);
            TableauControlDeleteZMQ(tableaucontrol);
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
    return proof_found;
}

bool EtableauSelectTableau(TableauControl_p tableaucontrol,
                            TableauStack_p distinct_tableaux_stack,
                            ClauseSet_p active,
                            ClauseSet_p extension_candidates)
{
    assert(tableaucontrol);
    assert(distinct_tableaux_stack);
    assert(active);
    assert(extension_candidates);
    assert(!ClauseSetEmpty(extension_candidates));
    bool proof_found = false;
    PStackPointer current_tableau_index = -1;
    ClauseTableau_p current_tableau = NULL;
    BacktrackStatus tableau_status = BACKTRACK_OK;
    while ((current_tableau = get_next_tableau(distinct_tableaux_stack,
                                               &current_tableau_index,
                                               tableaucontrol,
                                               active,
                                               extension_candidates)))
    {
        TB_p terms = current_tableau->terms;
        //if (Verbose)
        //{
            //fprintf(stderr, "# Selected tableau %ld\n", current_tableau_index);
        //}
        //fprintf(stderr, "# Selected tableau has maximum depth %d, average depth %f\n", ClauseTableauGetDeepestBranch(current_tableau),
                //ClauseTableauGetAverageDepth(current_tableau));
        if (tableaucontrol->closed_tableau)
        {
            EtableauStatusReport(tableaucontrol, active, tableaucontrol->closed_tableau);
        }
        assert(MaximumDepth(current_tableau) && "Maximum depth must be a positive integer");
        assert(current_tableau && "We must have a tableau for proof search...");
        assert(current_tableau->master == current_tableau && "The current tableau must be the root node of the tableau");
        tableau_status = BACKTRACK_OK;
        ClauseTableau_p closed_tableau = EtableauSelectBranchAndExtend(tableaucontrol,
                                                                       current_tableau,
                                                                       extension_candidates,
                                                                       &tableau_status);
        assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
        if (closed_tableau || current_tableau->open_branches->members == 0 || tableaucontrol->closed_tableau)
        {
            closed_tableau = tableaucontrol->closed_tableau;
            EtableauStatusReport(tableaucontrol, active, closed_tableau);
            proof_found = true;
            goto return_point;
        }
        else
        {
            assert(current_tableau->master == current_tableau);
            //GCCollect(terms->gc);
            switch (tableau_status)
            {
                case BACKTRACK_OK: // This should only happen during population, when all possible extension up to a depth have been made on a tableau
                {
                    assert(false && "Backtrack OK should not happen during normal proof search");
                    break;
                }
                case BACKTRACK_FAILURE:
                {
                    ETAB_VERBOSE(printf("# %p backtrack failed. maximum depth %lu\n", current_tableau, MaximumDepth(current_tableau));)
                    assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
                    assert(PStackElementP(distinct_tableaux_stack, current_tableau_index) == current_tableau);
                    assert(current_tableau->master == current_tableau);
                    assert(current_tableau->arity); // We need to ensure we still have the result of a start rule
                    assert(ClauseTableauQueryProp(current_tableau, TUPBacktrackedDueToExtensionFailure) || ClauseTableauQueryProp(current_tableau, TUPBacktrackedDueToMaxDepth));
                    assert(IsAnyPropSet(current_tableau, TUPBacktracked));

                    DeleteAllBacktrackInformation(current_tableau);
                    if (!ClauseTableauQueryProp(current_tableau, TUPBacktrackedDueToMaxDepth))
                    {
                        // If the backtrack failed and not due to maximum depth, this is a failure tableau
                        // and is discarded.
                        PStackDiscardElement(distinct_tableaux_stack, current_tableau_index);
                        ClauseTableauFree(current_tableau);
                        current_tableau_index = 0;
                        ETAB_VERBOSE(printf("# %p deleted at maximum depth %lu (backtrack failed for a reason other than depth)\n", current_tableau, MaximumDepth(current_tableau));)
                    }
                    else
                    {
                        // Otherwise, we need to increase the maximum depth.
                        // In this case, there will be a bigjump tableau and we can choose
                        // it to be the next tableau.
                        if (current_tableau->bigjump)
                        {
                            ClauseTableau_p new_tableau = current_tableau->bigjump;
                            PStackDiscardElement(distinct_tableaux_stack, current_tableau_index);
                            current_tableau->bigjump = NULL;
                            MaximumDepth(new_tableau) = MaximumDepth(current_tableau) << (unsigned long) 1;
                            ClauseTableauFree(current_tableau);
                            PStackPushP(distinct_tableaux_stack, new_tableau);
                            current_tableau_index = 0;
                            printf("Removed the current tableau and replaced it with its bigjump\n");
                            fflush(stdout);
                            assert(new_tableau->bigjump == NULL);
                        }
                        else
                        {
                            MaximumDepth(current_tableau) = MaximumDepth(current_tableau) << (unsigned long) 1;
                            assert(ClauseTableauQueryProp(current_tableau, TUPBacktrackedDueToMaxDepth));
                            ClauseTableauDelProp(current_tableau, TUPBacktracked);
                            assert(!ClauseTableauQueryProp(current_tableau, TUPBacktrackedDueToMaxDepth));
                            assert(!ClauseTableauQueryProp(current_tableau, TUPBacktrackedDueToExtensionFailure));
                            assert(!ClauseTableauQueryProp(current_tableau, TUPBacktracked));
                            ETAB_VERBOSE(printf("# %p increased maximum depth to %lu (backtrack failed because of depth)\n", current_tableau, MaximumDepth(current_tableau));)
                        }
                    }
                    break;
                }
                case NEXT_TABLEAU:
                {
                    assert(all_tableaux_in_stack_are_root(distinct_tableaux_stack));
                    break;
                }
                case RETURN_NOW: // Give up
                {
                    goto return_point;
                }
                default:
                {
                    Error("Unknown tableau status in n1", 100);
                }
            } // End of switch statement
        } // End of no proof found else statement
    } // End of tableau selection while loop

    return_point:
    return proof_found;
}

bool EtableauPopulation(TableauControl_p tableaucontrol,
                        TableauStack_p distinct_tableaux_stack,
                        ClauseSet_p active,
                        ClauseSet_p extension_candidates,
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
    //assert(!ClauseSetEmpty(extension_candidates));
    bool proof_found = false;
    PStackPointer current_tableau_index = -1;
    ClauseTableau_p current_tableau = NULL;
    //while (!proof_found)
    while ((current_tableau = get_next_tableau_population(distinct_tableaux_stack,
                                                          &current_tableau_index,
                                                          new_tableaux,
                                                          tableaucontrol,
                                                          active,
                                                          extension_candidates)))
    {
        if (tableaucontrol->closed_tableau)
        {
            EtableauStatusReport(tableaucontrol, active, tableaucontrol->closed_tableau);
        }
        assert(current_tableau && "We must have a tableau for proof search...");
        assert(current_tableau->master == current_tableau && "The current tableau must be the root node of the tableau");
        //printf("iter %ld:%ld\n", current_tableau_index, PStackGetSP(new_tableaux));
        BacktrackStatus tableau_status = BACKTRACK_OK;
        ClauseTableau_p closed_tableau = EtableauPopulationSelectBranchAndExtend(tableaucontrol,
                                                                                 current_tableau,
                                                                                 extension_candidates,
                                                                                 &tableau_status,
                                                                                 new_tableaux);
        // If we have not been able to find enough tableaux after 500 iterations, just return soon.
        if (UNLIKELY(current_tableau_index >= 250)) tableau_status = RETURN_NOW;
        if (closed_tableau || current_tableau->open_branches->members == 0 || tableaucontrol->closed_tableau)
        {
            closed_tableau = tableaucontrol->closed_tableau;
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
                    Error("We should not get BACKTRACK_OK status in population", 100);
                    break;
                }
                case BACKTRACK_FAILURE: // We never backtrack during population
                {
                    Error("We should not get BACKTRACK_FAILURE status in population", 100);
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

    return_point:
    assert(all_tableaux_in_stack_are_root(new_tableaux));
    while (!PStackEmpty(distinct_tableaux_stack))
    {
        ClauseTableau_p start = PStackPopP(distinct_tableaux_stack);
        assert(start->master == start);
        if (ClauseTableauQueryProp(start, TUPHasBeenExtendedOn))
        {
            ClauseTableauFree(start);
        }
        else
        {
            ClauseTableauDeleteAllProps(start);
            PStackPushP(new_tableaux, start);
        }
    }
    printf("# Returning from population with %ld new_tableaux and %ld remaining starting tableaux.\n",
            PStackGetSP(new_tableaux),
            PStackGetSP(distinct_tableaux_stack));
    return proof_found;
}

ClauseTableau_p get_next_tableau_population(TableauStack_p distinct_tableaux_stack,
                                            PStackPointer *current_index_p,
                                            TableauStack_p new_tableaux,
                                            TableauControl_p tableaucontrol,
                                            ClauseSet_p active,
                                            ClauseSet_p extension_candidates)
{
    ClauseTableau_p new_current_tableau = NULL;
    assert(new_tableaux);
    (*current_index_p)++;
    assert(*current_index_p >= 0);
    if (*current_index_p >= PStackGetSP(distinct_tableaux_stack))
    {
        // If we have not been able to produce tableaux
        if (PStackEmpty(new_tableaux) && can_restart(tableaucontrol, new_tableaux, active))
        {
            add_equality_axioms_to_state(tableaucontrol, active, extension_candidates);
            create_all_start_rules(tableaucontrol, new_tableaux, active);
        }
        // Get a new tableau from the newly produced stack
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

    return new_current_tableau;
}

ClauseTableau_p get_next_tableau(TableauStack_p distinct_tableaux_stack,
                                 PStackPointer *current_index_p,
                                 TableauControl_p tableaucontrol,
                                 ClauseSet_p active,
                                 ClauseSet_p extension_candidates)
{
    ClauseTableau_p new_current_tableau = NULL;
    (*current_index_p)++;
    assert(*current_index_p >= 0);
    //printf("selecting new tableau %ld remain, psp: %ld\n", PStackGetSP(distinct_tableaux_stack), *current_index_p);
    if (*current_index_p >= PStackGetSP(distinct_tableaux_stack))
    {
        // If we have not been able to produce tableaux
        if (PStackEmpty(distinct_tableaux_stack) && can_restart(tableaucontrol, distinct_tableaux_stack, active))
        {
            //printf("# Ran out of tableaux in process, attempting to make more from every clause.\n");
            add_equality_axioms_to_state(tableaucontrol, active, extension_candidates);
            create_all_start_rules(tableaucontrol, distinct_tableaux_stack, active);
        }
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
            printf("%ld d:%ld %ld\n", ClauseTableauHash(tab), tab->depth, ClauseTableauHash(tab->master));
            return false;
        }
    }
    return true;
}

// Create start rule applications for ALL clauses in active and put the resulting tableaux in to stack

long create_all_start_rules(TableauControl_p tableaucontrol,
                            TableauStack_p stack,
                            ClauseSet_p active)
{
    printf("# Ran out of tableaux, making start rules for all clauses\n");
    long res = 0;
    TB_p terms = tableaucontrol->proofstate->terms;
    tableaucontrol->all_start_rule_created = true;
    //printf("Ran out of tableaux in population...\n");
    ClauseSet_p emergency_units = ClauseSetAlloc();
    ClauseSetCopyUnits(terms, active, emergency_units);
    TableauStack_p emergency_tableaux = EtableauCreateStartRulesStack(terms,
                                                                      emergency_units,
                                                                      active,
                                                                      tableaucontrol,
                                                                      4);
    while (!PStackEmpty(emergency_tableaux))
    {
        PStackPushP(stack, PStackPopP(emergency_tableaux));
        res++;
    }
    ClauseSetFree(emergency_units);
    TableauStackFree(emergency_tableaux);
    //printf("# Made %ld start rules\n", res);
    return res;
}

long add_equality_axioms_to_state(TableauControl_p tableaucontrol,
                                  ClauseSet_p active,
                                  ClauseSet_p extension_candidates)
{
    // If we are not dynamically adding equality axioms during proof search, or have already done so, return
    if (!ClauseSetIsEquational(active)) return 0;
    if (tableaucontrol->tableauequality != 3 || tableaucontrol->equality_axioms_added) return 0;
    TB_p terms = tableaucontrol->proofstate->terms;
    ClauseSet_p equality_axioms = EqualityAxiomsWithSubstitution(terms, active, true);
    long res = equality_axioms->members;
    //ClauseSet_p equality_copy = ClauseSetCopy(terms, equality_axioms);
    ClauseSetMoveUnits(equality_axioms, active);
    long new_ext_candidates = ClauseSetInsertSet(extension_candidates, equality_axioms);
    tableaucontrol->equality_axioms_added = true;
    //printf("# Added %ld equality axioms and %ld new extension candidates\n", res, new_ext_candidates);
    return res;
}

static inline bool can_restart(TableauControl_p tableaucontrol, TableauStack_p stack, ClauseSet_p active)
{
    assert(PStackEmpty(stack));
    if (tableaucontrol->all_start_rule_created == false) return true;
    if (ClauseSetIsEquational(active) && tableaucontrol->equality_axioms_added == false) return true;
    return false;
}


// End of file
