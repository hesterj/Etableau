#include "etab_backtrack.h"


//long SubstRecordBindings(Subst_p subst, BacktrackStack_p backtracks, VarBank_p varbank, ClauseTableau_p position)
//{
    //assert(subst);
    //assert(backtracks);
    //assert(varbank);
    //assert(position);
    //PStackPointer substpointer = PStackGetSP(subst);
    //for (PStackPointer p=0; p< substpointer; p++)
    //{
        //Term_p element = PStackElementP(subst, p);
        //Backtrack_p bt = BacktrackAlloc(element, element, varbank, position);
        //PStackPushP(backtracks, bt);
    //}
    //return substpointer;
//}

Backtrack_p BacktrackAlloc_UNUSED(Subst_p subst, VarBank_p varbank, ClauseTableau_p position)
{
    assert(variable);
    assert(bind);
    assert(varbank);
    assert(position);
    assert(TermIsVar(variable));
    Backtrack_p backtrack = BacktrackCellAlloc();
    //backtrack->variable = variable;
    //backtrack->bind = TermCopy(bind, varbank, DEREF_ALWAYS);
    backtrack->master = position->master;
    backtrack->position = PStackAlloc();
    ClauseTableau_p handle = position;
    while (handle != position->master)
    {
        PStackPushInt(backtrack->position, (long) handle->position);
        handle = handle->master;
    }
    return backtrack;
}

Backtrack_p BacktrackAlloc(ClauseTableau_p position)
{
    Backtrack_p backtrack = BacktrackCellAlloc();
    if (position->arity == 0) backtrack->is_extension_step = false;
    else backtrack->is_extension_step = true;
    backtrack->master = position->master;
    backtrack->position = PStackAlloc();
    ClauseTableau_p handle = position;
    while (handle != position->master)
    {
        PStackPushInt(backtrack->position, (long) handle->position);
        handle = handle->master;
    }
    return backtrack;

}

void BacktrackFree(Backtrack_p trash)
{
    assert(trash);
    assert(!TermQueryProp(TPIsUnshared));
    PStackFree(trash->position);
    //TermFree(trash->bind); // variables are always shared, the bindings in a backtrack_p are unshared so have to be free'd
    BacktrackCellCellFree(trash);
}

Backtrack_p BacktrackCopy(Backtrack_p original)
{
    Backtrack_p new = BacktrackCellAlloc();
    new->is_extension_step = original->is_extension_step;
    new->position = PStackCopy(original->position);
    return new;
}

ClauseTableau_p GetNodeFromPosition(ClauseTableau_p master, PStack_p position)
{
    assert(master);
    assert(position);
    ClauseTableau_p handle = master;
    for (PStackPointer p = PStackGetSP(position); p != 0; p--)
    {
        handle = master->children[(short) p];
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

Binding_p BindingAlloc(Term_p var, VarBank_p vars) // The variable is just that, the bind is what the variable is dereferenced to.
{
    assert(var);
    assert(TermIsVar(var));
    Binding_p handle = BindingCellAlloc();
    handle->variable = var;
    handle->bind = TermCopy(var, vars, DEREF_ALWAYS); // What if the binding is to another variable?  This is troublesome...
    return handle;
}

void BindingFree(Binding_p trash)
{
    TermFree(trash->bind);
}

BacktrackStack_p BacktrackStackCopy(BacktrackStack_p stack)
{
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
    ClauseTableau_p master = bt->master;
    ClauseTableau_p position = GetNodeFromPosition(master, bt->position);
    if (BacktrackIsExtensionStep(bt))
    {
        // delete the children
        position->open = true;
        for (int i=0; i<position->arity; i++)
        {
            ClauseTableauFree(position->children[i]);
        }
        ClauseTableauArgArrayFree(position->children, trash->arity);
        position->children = NULL;
        position->arity = 0;
        // roll back every node of the tableau
        RollBackEveryNode(master);

    }
    else
    {
        // mark the position as open
        position->open = true;
        // rock back every node of the tableau
        RollBackEveryNode(master);
    }
    return;
}

void RollBackEveryNode(ClauseTableau_p master)
{
    return;
}
