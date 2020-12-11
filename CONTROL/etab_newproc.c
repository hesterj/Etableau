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

    TableauSet_p distinct_tableaux_set = EtableauCreateStartRules(proofstate,
                                                                  proofcontrol,
                                                                  bank,
                                                                  max_var,
                                                                  unit_axioms,
                                                                  start_rule_candidates,
                                                                  tableaucontrol);
   ClauseTableau_p initial_example = distinct_tableaux_set->anchor->succ->master;

   if (distinct_tableaux_set->members == 0)
   {
       Warning("There are no tableaux!");
   }
   else if (!initial_example)
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
   fprintf(GlobalOut, "# %ld start rule tableaux created.\n", distinct_tableaux_set->members);
   fprintf(GlobalOut, "# %ld extension rule candidate clauses\n", extension_candidates->members);
   printf("\n");

   // Now do proof search...

   // Proof search is over

   GCDeregisterClauseSet(gc, extension_candidates);
   ClauseSetFree(extension_candidates);
   GCDeregisterClauseSet(gc, unit_axioms);
   ClauseSetFree(unit_axioms);
   GCDeregisterClauseSet(gc, tableaucontrol->unprocessed);
   ClauseSetFree(tableaucontrol->unprocessed);

   while (!TableauSetEmpty(distinct_tableaux_set))
   {
       ClauseTableau_p trash = TableauSetExtractFirst(distinct_tableaux_set);
       ClauseTableauFree(trash);
   }
   TableauSetFree(distinct_tableaux_set);
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
