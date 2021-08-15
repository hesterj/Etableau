#include "etab_backtrack.h"

/*
** Some forward declarations
*/


/*
** Function definitions
*/
PStack_p SubstRecordBindings(Subst_p subst)
{
    assert(subst);
    PStack_p bindings = PStackAlloc();
    PStackPointer substpointer = PStackGetSP(subst);

    for (PStackPointer p=0; p< substpointer; p++)
    {
        Term_p element = PStackElementP(subst, p);
        Binding_p binding = BindingAlloc(element);
        PStackPushP(bindings, binding);
    }
    assert(PStackGetSP(subst) == PStackGetSP(bindings));
    return bindings;
}

Backtrack_p BacktrackAlloc(ClauseTableau_p position, Subst_p subst, long head_lit_position, TableauStepType type)
{
    Backtrack_p backtrack = BacktrackCellAlloc();
    backtrack->type = type;
    backtrack->reason = BacktrackReasonNotBacktracked;
    backtrack->master = position->master;
    backtrack->position = PStackAlloc();
    backtrack->id = position->id;
    backtrack->head_lit_position = head_lit_position;
    backtrack->completed = false;
    ClauseTableau_p handle = position;
    while (handle != handle->master)
    {
        PStackPushInt(backtrack->position, (long) handle->position);
        handle = handle->parent;
    }

    backtrack->bindings = SubstRecordBindings(subst);
    return backtrack;

}

void BacktrackFree(Backtrack_p trash)
{
    assert(trash);
    assert(trash->position);
    PStackFree(trash->position);
    BindingStackFree(trash->bindings);

    //TermFree(trash->bind); // variables are always shared, the bindings in a backtrack_p are unshared so have to be free'd
    BacktrackCellCellFree(trash);
}

Backtrack_p BacktrackCopy(Backtrack_p original, ClauseTableau_p new_master)
{
    Backtrack_p new = BacktrackCellAlloc();
    new->type = original->type;
    new->head_lit_position = original->head_lit_position;
    new->id = original->id;
    new->position = PStackCopy(original->position);
    new->bindings = BindingStackCopy(original->bindings);
    new->master = new_master;
    new->completed = true;
    return new;
}

ClauseTableau_p GetNodeFromPosition(ClauseTableau_p master, PStack_p position)
{
    assert(master);
    assert(position);

    ClauseTableau_p handle = master;
    for (PStackPointer p = PStackGetSP(position)-1; p >= 0; p--)
    {
        int current_position = PStackElementInt(position, p);
        handle = handle->children[current_position];
        assert(handle);
        assert(handle->label);
    }
    return handle;
}

bool VerifyBacktrackIsExtensionStep(Backtrack_p handle)
{
    assert(handle);
    ClauseTableau_p node = GetNodeFromPosition(handle->master, handle->position);
    if (node->arity > 0) return true;
    return false;
}

bool VerifyBacktrackIsClosureStep(Backtrack_p handle)
{
    assert(handle);
    ClauseTableau_p node = GetNodeFromPosition(handle->master, handle->position);
    if (node->arity == 0) return true;
    return false;
}

Binding_p BindingAlloc(Term_p var) // The variable is just that, the bind is what the variable is dereferenced to.
{
    assert(var);
    assert(TermIsVar(var));
    Binding_p handle = BindingCellAlloc();
    handle->variable = var;
    handle->bind = TermDerefAlways(var);
    return handle;
}

void BindingFree(Binding_p trash)
{
    BindingCellFree(trash);
}

Binding_p BindingCopy(Binding_p old_bind)
{
    Binding_p new = BindingCellAlloc();
    new->variable = old_bind->variable;
    new->bind = old_bind->bind;
    return new;
}

BacktrackStack_p BacktrackStackCopy(BacktrackStack_p stack, ClauseTableau_p new_master)
{
    assert(stack);
    BacktrackStack_p new_stack = PStackAlloc();
    PStackPointer max = PStackGetSP(stack);
    for (PStackPointer p = 0; p < max; p++)
    {
        Backtrack_p bt = PStackElementP(stack, p);
        Backtrack_p new_bt = BacktrackCopy(bt, new_master);
        PStackPushP(new_stack, new_bt);
    }
    assert(PStackGetSP(new_stack) == PStackGetSP(stack));
    return new_stack;
}

void Backtrack(Backtrack_p bt, BacktrackReason reason)
{
    assert(bt);
    ClauseTableau_p master = bt->master;
    assert(master);
    assert(master->label);
    assert(master == master->master);
    ClauseTableau_p position = GetNodeFromPosition(master, bt->position);

    DStrFree(position->info);
    position->info = DStrAlloc();

    assert(position);
    assert(position->label);
    assert(position->id == bt->id);
    if (bt->completed)
    {
        ClauseTableauDeregisterStep(position);
    }
    if (BacktrackIsExtensionStep(bt))
    {
        if (bt->completed)
        {
            // delete the children
            assert(position->arity > 1);
            for (int i=0; i<position->arity; i++)
            {
                assert(position->children[i]);
                if (position->children[i]->set)
                {
                    assert(position->children[i]->open == true);
                    TableauSetExtractEntry(position->children[i]);
                }
                assert(position->children[i]->set == NULL);
                ClauseTableauFree(position->children[i]);
            }
            ClauseTableauArgArrayFree(position->children, position->arity);
            position->children = NULL;
            position->arity = 0;
            position->folded_up = 0;
        }
    }
    else if (BacktrackIsClosureStep(bt))
    {
        assert(position->arity == 0);
        assert(position->open == false);
        assert(position->set == NULL);
        assert(position->children == NULL);
    }
    else if (BacktrackIsEtableauStep(bt))
    {
        assert(position->arity == 0);
        assert(position->set == NULL);
        assert(position->open == false);
        ClauseTableauDelProp(position, TUPSaturationClosed);
        ClauseTableauSetProp(position, TUPSaturationBlocked);
        position->saturation_closed = false;
    }
    else
    {
        assert(false && "Unknown backtrack");
    }

    bt->reason = reason;
    position->id = 0;
    position->open = true;
    position->mark_int = 0;
    TableauSetInsert(master->open_branches, position);

    // roll back every node of the tableau
    if (PStackGetSP(bt->bindings) > 0) //
    {
        RollBackEveryNode(master);
    }

    // Shouldn't need to update variables here because they are updated before any potential inference rule.
    //ClauseTableauUpdateVariablesArray(master);

    assert(position->label);
    return;
}

void RollBackEveryNode(ClauseTableau_p tab)
{
    PStackPointer p_labels = PStackGetSP(tab->old_labels);
    PStackPointer p_folding = PStackGetSP(tab->old_folding_labels);
    GCAdmin_p gc = tab->terms->gc;

    assert(p_labels);
    if (p_labels)
    {
        assert(tab->old_labels->current);
        Clause_p new_label = (Clause_p) PStackPopP(tab->old_labels);
        assert(new_label->set);
        tab->label = new_label;
        // The old tab->label now only has a reference to it in the label_storage.
        // The automatic garbage collection for label storage (will) work with a a mark & sweep
    }

    assert(p_folding);
    if (p_folding)
    {
        assert(tab->old_folding_labels->current);
        assert(PTreeFindBinary(gc->clause_sets, tab->folding_labels));
        ClauseSet_p new_folding_labels = (ClauseSet_p) PStackPopP(tab->old_folding_labels);
        GCDeregisterClauseSet(gc, tab->folding_labels);
        ClauseSetFree(tab->folding_labels);
        tab->folding_labels = new_folding_labels;
    }

    PTreeFree(tab->local_variables);
    tab->local_variables = NULL;

    assert(tab->label);
    if (tab->saturation_state)
    {
        EtableauProofstateFree(tab->saturation_state);
        tab->saturation_state = NULL;
    }
    for (int i=0; i<tab->arity; i++)
    {
        RollBackEveryNode(tab->children[i]);
    }

    return;
}

PStack_p BindingStackCopy(PStack_p binding_stack)
{
    PStack_p new_stack = PStackAlloc();
    for (PStackPointer p=0; p< PStackGetSP(binding_stack); p++)
    {
        Binding_p binding_p = (Binding_p) PStackElementP(binding_stack, p);
        Binding_p new = BindingCopy(binding_p);
        PStackPushP(new_stack, new);
    }
    assert(PStackGetSP(new_stack) == PStackGetSP(binding_stack));
    return new_stack;
}

void BindingStackFree(PStack_p trash)
{
    while (!PStackEmpty(trash))
    {
        Binding_p trash_bind = (Binding_p) PStackPopP(trash);
        BindingFree(trash_bind);
    }
    PStackFree(trash);
}

/*
** If a subst has been recorded as a failure substitution at a node, then return true!
** This is only used for checking if a closure rule application is a failure.
*/

bool SubstIsFailure(ClauseTableau_p tab, Subst_p subst)
{
    assert(tab);
    assert(subst);
    assert(tab->failures);
    BacktrackStack_p failures = tab->failures;
    PStackPointer failures_length = PStackGetSP(failures);
    for (int i=0; i<failures_length; i++)
    {
        Backtrack_p bt = PStackElementP(failures, i);
        //if (PStackGetSP(subst) && BacktrackContainsSubst(bt, subst)) // The empty substitution is not a failure substitution...
        //{
            //return true;
        //}
        if (tab->id == bt->id)
        {
            ETAB_VERBOSE(printf("# Failure substitution averted\n");)
            assert(BacktrackIsClosureStep(bt));
            return true;
        }
    }
    return false;
}

bool ExtensionIsFailure(ClauseTableau_p tab, Subst_p subst, long extension_id, long head_literal_position)
{
    assert(tab);
    assert(subst);
    assert(tab->failures);
    BacktrackStack_p failures = tab->failures;
    PStackPointer failures_length = PStackGetSP(failures);
    for (int i=0; i<failures_length; i++)
    {
        Backtrack_p bt = PStackElementP(failures, i);
        // The empty substitution is not a failure substitution...
        //if (PStackGetSP(subst) && (bt->id == extension_id) && (head_literal_position == bt->head_lit_position) && BacktrackContainsSubst(bt, subst))
        //{
            //return true;
        //}
        if (bt->id == extension_id && head_literal_position == bt->head_lit_position)
        {
            return true;
        }
    }
    return false;
}

/*
** Iterate over the subst, checking to see if the binding occurs
*/

bool BindingOccursInSubst(Binding_p binding, Subst_p subst)
{
    assert(binding);
    assert(subst);
    PStackPointer stack_pointer = PStackGetSP(subst);
    for (int i=0; i<stack_pointer; i++)
    {
        Term_p var = PStackElementP(subst, i);
        Term_p bound_var = TermDerefAlways(var);
        Term_p binding_var = binding->variable;
        Term_p binding_bound = binding->bind;
        //if ((var == binding_var) && (bound_var == binding_bound)) // Should probably not just do pointer comparisons...

        //if (true) // Terms are ALWAYS shared
        if (var == binding_var) // Terms are ALWAYS shared
        {
            Subst_p subst = SubstAlloc();
            if (SubstMguComplete(bound_var, binding_bound, subst))
            {
                if (SubstIsRenaming(subst))
                {
                    SubstDelete(subst);
                    return true;
                }
            }
            SubstDelete(subst);
        }

    }
    return false;
}

/*
** If any of the bindings in backtrack is more general than subst, return true.
*/

bool BacktrackContainsSubst(Backtrack_p backtrack, Subst_p subst)
{
    assert(backtrack);
    assert(subst);
    PStackPointer p = PStackGetSP(backtrack->bindings);
    for (int i=0; i<p; i++)
    {
        Binding_p bind = PStackElementP(backtrack->bindings, i);
        if (BindingOccursInSubst(bind, subst))
        {
            return true;
        }
    }
    return false;
}

/*
** The function collects the most recent backtrack information, and then backtracks that step.
** If a bactkrack is found and executed, then return true.
** Otherwise, return false.  This can happen if there are no more possible backtracks (failure tableau)
*/

bool BacktrackWrapper(ClauseTableau_p master, BacktrackReason reason)
{
    //TableauControl_p tableaucontrol = master->tableaucontrol;
    bool success = true;
    assert(master == master->master);
    PStack_p master_backtracks = master->master_backtracks;
    //fprintf(GlobalOut, "# We need to backtrack... There are %ld known previous steps we can backtrack\n", PStackGetSP(master_backtracks));
    if (PStackGetSP(master_backtracks) == 0)
    {
        success = false;
        goto return_point;
    }
    PStack_p bt_position = (PStack_p) PStackPopP(master_backtracks); // bt_position is a stack indicating a location in the tableau
    ClauseTableau_p backtrack_location = GetNodeFromPosition(master, bt_position);
    BacktrackStack_p backtrack_stack = backtrack_location->backtracks;
    Backtrack_p bt = (Backtrack_p) PStackPopP(backtrack_stack);
    PStackPushP(backtrack_location->failures, bt);
    assert(GetNodeFromPosition(master, bt->position) == backtrack_location);
    assert(bt->master);

    Backtrack(bt, reason);
    PStackFree(bt_position);

    // IF we just backtracked an Etableau closure rule, it was only possible because of an application of another
    // (bad) rule previously that made that step possible!
    // This means that we need to backtrack AGAIN.

    if (BacktrackIsEtableauStep(bt))
    {
        success = BacktrackWrapper(master, reason);
    }

    return_point:
    return success;
}

void DeleteAllBacktrackInformation(ClauseTableau_p tableau)
{
    assert(tableau);

    // We reset the old labels because the clause garbage collection should handle the old labels appropriately
    PStackReset(tableau->old_labels);
    //while (!PStackEmpty(tableau->old_labels))
    //{
        //Clause_p trash_label = PStackPopP(tableau->old_labels);
        //ClauseSetExtractEntry(trash_label);
        //ClauseFree(trash_label);
    //}
    while (!PStackEmpty(tableau->old_folding_labels))
    {
        ClauseSet_p trash_label_set = PStackPopP(tableau->old_folding_labels);
        GCDeregisterClauseSet(tableau->terms->gc, trash_label_set);
        ClauseSetFree(trash_label_set);
    }
    assert(PStackEmpty(tableau->old_labels));
    assert(PStackEmpty(tableau->old_folding_labels));
    PositionStackFreePositions(tableau->master_backtracks);
    BacktrackStackDeleteInformation(tableau->backtracks);
    BacktrackStackDeleteInformation(tableau->failures);
    for (int i=0; i<tableau->arity; i++)
    {
        DeleteAllBacktrackInformation(tableau->children[i]);
    }
}

void BacktrackStackDeleteInformation(BacktrackStack_p trash)
{
    if (!trash) return;
    while (!PStackEmpty(trash))
    {
        Backtrack_p trash_bt = (Backtrack_p) PStackPopP(trash);
        assert(trash_bt);
        BacktrackFree(trash_bt);
    }
}

/*
** If there are n backtracks available, backtrack n/fraction times.
** If we ran out of backtracks return false, else return true.
*/

bool BacktrackMultiple(ClauseTableau_p master, BacktrackReason reason, long denominator)
{
    assert(denominator);
    long number_of_backtracks = PStackGetSP(master->master_backtracks);
    double fraction = (double) number_of_backtracks / (double) denominator;
    assert(fraction >= 0);
    double ceiling = ceil(fraction);
    long counter = (long) ceiling;
    assert(counter);
    bool success = true;

    while (counter)
    {
        success = BacktrackWrapper(master, reason);
        if (!success) break;
        counter--;
    }

    return success;
}
