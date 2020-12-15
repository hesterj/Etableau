#include<etab_newproc.h>

extern void c_smoketest();

int Etableau_n(TableauControl_p tableaucontrol,
               ProofState_p proofstate,
               ProofControl_p proofcontrol,
               TB_p bank,
               ClauseSet_p active,
               int max_depth,
               int tableauequality)
{
    if(geteuid() == 0) Error("# Please do not run Etableau as root.", 1);
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

   if (PStackEmpty(distinct_tableaux_stack))
   {
       Warning("There are no tableaux!");
   }
   ClauseTableau_p initial_example = PStackElementP(distinct_tableaux_stack, 0);
   if (!initial_example)
   {
       Warning("Unable to find a tableau!");
   }
   else if (!initial_example->label)
   {
       Warning("Initial tableau has no label!");
   }

// Do a branch saturation on the original problem before diving in to the tableaux proofsearch
   if (tableaucontrol->branch_saturation_enabled)
   {
       fprintf(GlobalOut, "# Attempting initial tableau saturation\n");
       BranchSaturation_p branch_sat = BranchSaturationAlloc(tableaucontrol->proofstate,
                                                             tableaucontrol->proofcontrol,
                                                             initial_example,
                                                             10000);
// Trying to keep one object in extensions and saturations
        AttemptToCloseBranchesWithSuperpositionSerial(tableaucontrol, branch_sat);
        BranchSaturationFree(branch_sat);
        if (tableaucontrol->closed_tableau)
        {
            proof_found = true;
            tableaucontrol->closed_tableau = initial_example;
            EtableauStatusReport(tableaucontrol, active, tableaucontrol->closed_tableau);
        }
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

   while (!proof_found)
   {
       ClauseTableau_p closed_tableau = EtableauProofSearch_n(tableaucontrol, initial_example, extension_candidates, max_depth);
       if (closed_tableau)
       {
           fprintf(GlobalOut, "# Report status...\n");
           proof_found = true;
       }
   }


   // Proof search is over

   GCDeregisterClauseSet(gc, extension_candidates);
   ClauseSetFree(extension_candidates);
   GCDeregisterClauseSet(gc, unit_axioms);
   ClauseSetFree(unit_axioms);
   GCDeregisterClauseSet(gc, tableaucontrol->unprocessed);
   ClauseSetFree(tableaucontrol->unprocessed);

   while (!PStackEmpty(distinct_tableaux_stack))
   {
       ClauseTableau_p trash = PStackPopP(distinct_tableaux_stack);
       ClauseTableauFree(trash);
   }
   PStackFree(distinct_tableaux_stack);
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

ClauseTableau_p EtableauProofSearch_n(TableauControl_p tableaucontrol, ClauseTableau_p start, ClauseSet_p extension_candidates, int max_depth)
{
    assert(tableaucontrol);
    assert(start);
    assert(start->master == start);
    assert(extension_candidates);
    assert(max_depth);
    assert(start->label);
    assert(start->open_branches);

    fprintf(GlobalOut, "# About to try to extend again...\n");

    ClauseTableau_p closed_tableau = NULL;
    ClauseTableau_p open_branch = branch_select(start->open_branches, max_depth);

    Clause_p selected = extension_candidates->anchor->succ;
    int number_of_extensions = 0;
    while (selected != extension_candidates->anchor) // iterate over the clauses we can split on the branch
    {
        number_of_extensions += ClauseTableauExtensionRuleAttemptOnBranch(tableaucontrol,
                                                                          open_branch,
                                                                          NULL,
                                                                          selected,
                                                                          NULL);
        if (tableaucontrol->closed_tableau)
        {
            closed_tableau = tableaucontrol->closed_tableau;
            fprintf(GlobalOut, "# Success\n");
            return closed_tableau;
        }
        else if (number_of_extensions > 0)
        {
            fprintf(GlobalOut, "# Selecting a new open branch...\n");
            return NULL;
        }
        selected = selected->succ;
    }

    assert(number_of_extensions == 0);
    assert(open_branch->parent->backtracks);

    ClauseTableau_p backtrack_location = open_branch->parent;
    BacktrackStack_p backtrack_stack = backtrack_location->backtracks;
    fprintf(GlobalOut, "# Unable to extend on a branch!  It should be backtracked... there are %ld backtracks at the open branch\n", PStackGetSP(backtrack_stack));

    // If there is nothing to backtrack at a node, we need to look farther up.
    // Here, nothing to backtrack means that every extension attempt at the open branch has failed.
    // That means that we must backtrack at a higher location...

    while (PStackGetSP(backtrack_stack) == 0)
    {
        backtrack_location = backtrack_location->parent;
        if (backtrack_location == NULL)
        {
            fprintf(GlobalOut, "# Went to the root in search of a backtrack...\n");
            return NULL;
        }
        backtrack_stack = backtrack_location->backtracks;
        assert(backtrack_stack);
    }
    Backtrack_p bt = (Backtrack_p) PStackPopP(backtrack_stack);
    PStackPushP(backtrack_location->failures, bt);
    assert(GetNodeFromPosition(open_branch->master, bt->position) == backtrack_location);

    assert(open_branch->master);
    Backtrack(bt);
    open_branch = NULL; // open_branch has been free'd in backtracking!

    fprintf(GlobalOut, "# Backtracking completed...\n");

#ifndef DNDEBUG
    fprintf(GlobalOut, "# Verifying that the open branches are not broken...\n");
    ClauseTableauAssertCheck(start->master);
    ClauseTableau_p temp_handle = start->open_branches->anchor->succ;
    while (temp_handle != start->open_branches->anchor)
    {
        assert(temp_handle->master == start);
        assert(temp_handle->label);
        temp_handle = temp_handle->succ;
    }
#endif

    return NULL;
}
