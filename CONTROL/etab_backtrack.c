#include "etab_backtrack.h"


long SubstRecordBindings(Subst_p subst, BacktrackStack_p backtracks, VarBank_p varbank)
{
    PStackPointer substpointer = PStackGetSP(subst);
    for (PStackPointer p=0; p< substpointer; p++)
    {
        Term_p element = PStackElementP(subst, p);
        Backtrack_p bt = BacktrackAlloc(element, element, varbank);
        PStackPushP(backtracks, bt);
    }
    return substpointer;
}

Backtrack_p BacktrackAlloc(Term_p variable, Term_p bind, VarBank_p varbank)
{
    Backtrack_p backtrack = BacktrackCellAlloc();
    backtrack->variable = variable;
    backtrack->bind = TermCopy(bind, varbank, DEREF_ALWAYS);
    backtrack->position = NULL;
    return backtrack;
}

void BacktrackFree(Backtrack_p trash)
{
    TermFree(trash->bind); // variables are always shared, the bindings in a backtrack_p are unshared so have to be free'd
    BacktrackCellCellFree(trash);
}
