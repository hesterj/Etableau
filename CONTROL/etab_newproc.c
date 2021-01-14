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
   if (tableaucontrol->branch_saturation_enabled)
   {
       proof_found = EtableauSaturateAllTableauxInStack(tableaucontrol, distinct_tableaux_stack, active);
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

   if (!proof_found && tableaucontrol->multiprocessing_active)
   {
       proof_found = EtableauMultiprocess_n(tableaucontrol,
                                            distinct_tableaux_stack,
                                            extension_candidates,
                                            max_depth);

   }
   else if (!proof_found)
   {
       proof_found = EtableauProofSearchAtDepthWrapper_n(tableaucontrol,
                                                         distinct_tableaux_stack,
                                                         active,
                                                         extension_candidates,
                                                         max_depth);
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

ClauseTableau_p EtableauProofSearch_n(TableauControl_p tableaucontrol,
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
    fprintf(GlobalOut, "# Current depth %d\n", current_depth);

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
            fprintf(GlobalOut, "# Backtracking due to all depths exceeded, %ld remaining\n", PStackGetSP(master->master_backtracks));
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
        fprintf(GlobalOut, "# Selected open branch %p, %d extensions done so far, current depth %d\n", open_branch, tableaucontrol->number_of_extensions, current_depth);
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
                                                         &extended);
        extensions_done += extended;

        if (result || (open_branches->members == 0)) // We have found a closed tableau
        {
            assert(tableaucontrol->closed_tableau == result);
            return result;
        }
        if (open_branch->set) // If the open branch is still in a set after the extension rule attempt, it means it was not able to be extended and so should be backtracked
        {
            fprintf(GlobalOut, "# Backtracking, %ld remaining\n", PStackGetSP(master->master_backtracks));
            bool backtrack_successful = BacktrackWrapper(master);
            if (!backtrack_successful)
            {
                *backtrack_status = BACKTRACK_FAILURE; // Failed backtrack, this tableau is no good.
                break;
            }
        }
        else if (extended && tableaucontrol->number_of_extensions % 100 == 0)
        {
            *backtrack_status = NEXT_TABLEAU;
            break;
        }
    }

    fprintf(GlobalOut, "# Unable to extend at depth... Returning from EtableauProofSearch_n\n");

    return NULL;
}

ClauseTableau_p EtableauProofSearchAtDepth_n(TableauControl_p tableaucontrol,
                                             ClauseTableau_p master,
                                             ClauseSet_p extension_candidates,
                                             int max_depth,
                                             BacktrackStatus_p status)
{
   // Root is depth 0, initial start rule is depth 1, so first depth should be 2
   BacktrackStatus backtrack_status = BACKTRACK_OK;
   for (int current_depth = 2; current_depth < max_depth; current_depth++)
   {
       ClauseTableau_p result = EtableauProofSearch_n(tableaucontrol,
                                                      master,
                                                      extension_candidates,
                                                      current_depth,
                                                      max_depth,
                                                      &backtrack_status);
       *status = backtrack_status;
       if (result || master->open_branches->members == 0)
       {
           assert(tableaucontrol->closed_tableau == result);
           return result;
       }
       if (backtrack_status == BACKTRACK_FAILURE || backtrack_status == NEXT_TABLEAU)
       {
           break;
       }
   }

   return NULL;
}

bool EtableauMultiprocess_n(TableauControl_p tableaucontrol,
                            PStack_p starting_tableaux,
                            ClauseSet_p extension_candidates,
                            int max_depth)
{
    return false;
}

bool EtableauProofSearchAtDepthWrapper_n(TableauControl_p tableaucontrol,
                                         TableauStack_p distinct_tableaux_stack,
                                         ClauseSet_p active,
                                         ClauseSet_p extension_candidates,
                                         int max_depth)
{
    bool proof_found = false;
    PStackPointer current_tableau_index = 0;
    ClauseTableau_p current_tableau = PStackElementP(distinct_tableaux_stack, current_tableau_index);
    BacktrackStatus status = BACKTRACK_OK;
    while (!proof_found)
    {
        //ClauseTableau_p closed_tableau = EtableauProofSearch_n(tableaucontrol, initial_example, extension_candidates, max_depth);
        ClauseTableau_p closed_tableau = EtableauProofSearchAtDepth_n(tableaucontrol,
                                                                      current_tableau,
                                                                      extension_candidates,
                                                                      max_depth,
                                                                      &status);
        if (closed_tableau || current_tableau->open_branches->members == 0)
        {
            fprintf(GlobalOut, "# Report status... proof found\n");
            EtableauStatusReport(tableaucontrol, active, closed_tableau);
            proof_found = true;
        }
        else
        {
            assert(status == BACKTRACK_FAILURE || status == NEXT_TABLEAU);
            if (status == BACKTRACK_FAILURE)
            {
                fprintf(GlobalOut, "# Switching from a tableau with %ld open branches because of backtrack failure.\n", current_tableau->open_branches->members);
            }
            else if (status == NEXT_TABLEAU)
            {
                fprintf(GlobalOut, "# Switching from a tableau with %ld open branches because of extension limit.\n", current_tableau->open_branches->members);
            }
            current_tableau = EtableauGetNextTableau(distinct_tableaux_stack, &current_tableau_index);
        }
    }

    return proof_found;
}

ClauseTableau_p EtableauGetNextTableau(TableauStack_p distinct_tableaux_stack,
                                       PStackPointer *current_index_p)
{
    PStackPointer current_index = *current_index_p;
    current_index++;
    if (current_index == PStackGetSP(distinct_tableaux_stack))
    {
        current_index = 0;
    }
    ClauseTableau_p new_current_tableau = PStackElementP(distinct_tableaux_stack, current_index);
    return new_current_tableau;
}
