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
       //ClauseTableau_p closed_tableau = EtableauProofSearch_n(tableaucontrol, initial_example, extension_candidates, max_depth);
       ClauseTableau_p closed_tableau = EtableauProofSearchAtDepth_n(tableaucontrol,
                                                                     initial_example,
                                                                     extension_candidates,
                                                                     max_depth);
       if (closed_tableau || initial_example->open_branches->members == 0)
       {
           fprintf(GlobalOut, "# Report status... proof found\n");
           proof_found = true;
       }
       else
       {
           // Switch to a new tableau here?
           ClauseTableauPrint(initial_example->master);
           fprintf(GlobalOut, "# Tableau failure for some reason %ld open branches...\n", initial_example->open_branches->members);
           break;
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

ClauseTableau_p EtableauProofSearch_n(TableauControl_p tableaucontrol,
                                      ClauseTableau_p master,
                                      ClauseSet_p extension_candidates,
                                      int current_depth,
                                      BacktrackStatus_p backtrack_status)
{
    assert(tableaucontrol);
    assert(master);
    assert(master->master == master);
    assert(extension_candidates);
    assert(current_depth);
    assert(master->label);
    assert(master->open_branches);

    int extensions_done = 0; // This allows us to keep track of the number of extensions done since the last backtrack
    ClauseTableau_p open_branch = NULL, result = NULL;
    TableauSet_p open_branches = master->open_branches;
    while ((open_branch = branch_select(open_branches, current_depth)))
    {
        fprintf(GlobalOut, "# Selected open branch %p, %d extensions done so far, current depth %d\n", open_branch, tableaucontrol->number_of_extensions, current_depth);
        assert(open_branch);
        assert(open_branch->id == 0);
        assert(open_branch->backtracks);
        assert(open_branch->depth < current_depth);
        assert(open_branch->failures);
        assert(open_branch->parent);
        assert(open_branch->parent->backtracks);
        result = ClauseTableauSearchForPossibleExtension(tableaucontrol,
                                                         open_branch,
                                                         extension_candidates,
                                                         current_depth);
        if (result || (open_branches->members == 0)) // We have found a closed tableau
        {
            assert(tableaucontrol->closed_tableau == result);
            return result;
        }
        if (open_branch->set) // If the open branch is still in a set after the extension rule attempt, it means it was not able to be extended and so should be backtracked
        {
            bool backtrack_successful = BacktrackWrapper(master);
            if (!backtrack_successful)
            {
                *backtrack_status = BACKTRACK_FAILURE; // Failed backtrack, this tableau is no good.
                break;
            }
            continue;
        }
        extensions_done++;
    }

    fprintf(GlobalOut, "# Unable to extend (at depth), or could not backtrack...\n");

    return NULL;
}

ClauseTableau_p EtableauProofSearchAtDepth_n(TableauControl_p tableaucontrol,
                                             ClauseTableau_p master,
                                             ClauseSet_p extension_candidates,
                                             int max_depth)
{
   // Root is depth 0, initial start rule is depth 1, so first depth should be 2
   BacktrackStatus backtrack_status = BACKTRACK_OK;
   for (int current_depth = 2; current_depth < max_depth; current_depth++)
   {
       ClauseTableau_p result = EtableauProofSearch_n(tableaucontrol,
                                                      master,
                                                      extension_candidates,
                                                      current_depth,
                                                      &backtrack_status);
       if (result || master->open_branches->members == 0)
       {
           assert(tableaucontrol->closed_tableau == result);
           return result;
       }
       if (backtrack_status == BACKTRACK_FAILURE)
       {
           break;
       }
   }

   return NULL;
}
