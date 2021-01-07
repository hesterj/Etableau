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
    return bindings;
}

Backtrack_p BacktrackAlloc(ClauseTableau_p position, Subst_p subst)
{
    Backtrack_p backtrack = BacktrackCellAlloc();
    if (position->arity == 0) backtrack->is_extension_step = false;
    else backtrack->is_extension_step = true;
    backtrack->master = position->master;
    backtrack->position = PStackAlloc();
    backtrack->id = 0;
    ClauseTableau_p handle = position;
    while (handle != handle->master)
    {
        PStackPushInt(backtrack->position, (long) handle->position);
        handle = handle->parent;
    }
#ifndef DNDEBUG
    assert(GetNodeFromPosition(position->master, backtrack->position) == position);
    if (PStackGetSP(backtrack->position) != position->depth)
    {
        Warning("Recorded a position of depth %d with %d steps to reach it...", position->depth, PStackGetSP(backtrack->position));
    }
#endif

    backtrack->bindings = SubstRecordBindings(subst);
    return backtrack;

}

void BacktrackFree(Backtrack_p trash)
{
    assert(trash);
    PStackFree(trash->position);
    BindingStackFree(trash->bindings);

    //TermFree(trash->bind); // variables are always shared, the bindings in a backtrack_p are unshared so have to be free'd
    BacktrackCellCellFree(trash);
}

Backtrack_p BacktrackCopy(Backtrack_p original)
{
    Backtrack_p new = BacktrackCellAlloc();
    new->is_extension_step = original->is_extension_step;
    new->position = PStackCopy(original->position);
    new->bindings = BindingStackCopy(original->bindings);
    return new;
}

ClauseTableau_p GetNodeFromPosition(ClauseTableau_p master, PStack_p position)
{
    assert(master);
    assert(position);

    #ifndef DNDEBUG
    fprintf(GlobalOut, "# Printing position stack: ");
    PStackPrintInt(GlobalOut, " %ld ", position);
    fprintf(GlobalOut, "\n");
    #endif

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

BacktrackStack_p BacktrackStackCopy(BacktrackStack_p stack)
{
    assert(stack);
    BacktrackStack_p new_stack = PStackAlloc();
    PStackPointer max = PStackGetSP(stack);
    for (PStackPointer p = 0; p < max; p++)
    {
        Backtrack_p bt = PStackElementP(stack, p);
        Backtrack_p new_bt = BacktrackCopy(bt);
        PStackPushP(new_stack, new_bt);
    }
    assert(PStackGetSP(new_stack) == PStackGetSP(stack));
    return new_stack;
}

void Backtrack(Backtrack_p bt)
{
    assert(bt);
    ClauseTableau_p master = bt->master;
    assert(master);
    assert(master->label);
    ClauseTableau_p position = GetNodeFromPosition(master, bt->position);
    assert(position);
    assert(position->label);
    if (BacktrackIsExtensionStep(bt))
    {
        // delete the children
        fprintf(GlobalOut, "# Backtracking extension %p (d%d) with %d children and whose parent is %p\n", position, position->depth, position->arity, position->parent);
        assert(position->arity > 1);
        for (int i=0; i<position->arity; i++)
        {
            if (position->children[i]->set)
            {
                assert(position->children[i]->open == true);
                TableauSetExtractEntry(position->children[i]);
            }
            #ifndef DNDEBUG
            if (position->children[i]->arity)
            {
                Warning("Attempting to backtrack an extension with a child %p extended on!", position->children[i]);
            }
            #endif
            assert(position->children[i]->set == NULL);
            ClauseTableauFree(position->children[i]);
            position->children[i]->label = NULL;
            position->children[i]->parent = NULL;
            position->children[i]->master = NULL;
            position->children[i] = NULL;
        }
        ClauseTableauArgArrayFree(position->children, position->arity);
        position->children = NULL;
        position->arity = 0;
    }
    else // this is a closure step, etableau closures are not registered or backtracked
    {
        assert(position->arity == 0);
        assert(position->open == false);
        assert(position->set == NULL);
        assert(position->children == NULL);
    }
    bt->id = position->id;
    position->id = 0;
    position->open = true;
    TableauSetInsert(master->open_branches, position);

#ifndef DNDEBUG
    ClauseTableauAssertCheck(master);
#endif
    // roll back every node of the tableau
    if (PStackGetSP(bt->bindings) > 0) //
    {
        RollBackEveryNode(master);
    }

#ifndef DNDEBUG
    ClauseTableauAssertCheck(master);
#endif

    assert(position->label);
    return;
}

void RollBackEveryNode(ClauseTableau_p tab)
{
    PStackPointer p_labels = PStackGetSP(tab->old_labels);
    PStackPointer p_folding = PStackGetSP(tab->old_folding_labels);
    GCAdmin_p gc = tab->terms->gc;
    if (p_labels)
    {
        Clause_p new_label = (Clause_p) PStackPopP(tab->old_labels);
        ClauseSetExtractEntry(tab->label);
        ClauseFree(tab->label);
        tab->label = new_label;
    }
    if (p_folding)
    {
        ClauseSet_p new_folding_labels = (ClauseSet_p) PStackPopP(tab->old_folding_labels);
        GCDeregisterClauseSet(gc, tab->folding_labels);
        ClauseSetFree(tab->folding_labels);
        tab->folding_labels = new_folding_labels;
    }
    assert(tab->label);
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
        if (BacktrackContainsSubst(bt, subst))
        {
            return true;
        }
    }
    return false;
}

bool ExtensionIsFailure(ClauseTableau_p tab, Subst_p subst, long extension_id)
{
    assert(tab);
    assert(subst);
    assert(tab->failures);
    BacktrackStack_p failures = tab->failures;
    PStackPointer failures_length = PStackGetSP(failures);
    for (int i=0; i<failures_length; i++)
    {
        Backtrack_p bt = PStackElementP(failures, i);
        if ((bt->id == extension_id) && BacktrackContainsSubst(bt, subst))
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

bool BacktrackWrapper(ClauseTableau_p master)
{
    assert(master == master->master);
    PStack_p master_backtracks = master->master_backtracks;
    fprintf(GlobalOut, "# Unable to extend on a branch!  We need to backtrack... There are %ld known previous steps we can backtrack\n", PStackGetSP(master_backtracks));
    if (PStackGetSP(master_backtracks) == 0)
    {
        Warning("The tableau failed to backtrack because there are no possible previous steps", 10);
        return false;
    }
    PStack_p bt_position = (PStack_p) PStackPopP(master_backtracks); // bt_position is a stack indicating a location in the tableau
    ClauseTableau_p backtrack_location = GetNodeFromPosition(master, bt_position);
    PStackFree(bt_position);
    fprintf(GlobalOut, "# There are %ld failures at this node.\n", PStackGetSP(backtrack_location->failures));
    BacktrackStack_p backtrack_stack = backtrack_location->backtracks;
    Backtrack_p bt = (Backtrack_p) PStackPopP(backtrack_stack);
    PStackPushP(backtrack_location->failures, bt);
    assert(GetNodeFromPosition(master, bt->position) == backtrack_location);

    Backtrack(bt);

    fprintf(GlobalOut, "# Backtracking completed...\n");
    return true;
}
