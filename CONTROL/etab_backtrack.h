#ifndef ETAB_BACKTRACK
#define ETAB_BACKTRACK
#include<cco_proofproc.h>
//#include<etab_tableauproc.h>
#include <etab_etableau.h>

// To store the bindings, we will use Eqn_p to store the pair.  L
typedef struct backtrackcell
{
    Term_p variable;
    Term_p bind;
    ClauseTableau_p position; // If an extension step was done at this step, this is a pointer to the parent node of the step
    // If it was a closure rule done, position is the closed node.
}BackTrackCell, *Backtrack_p;


#define BacktrackCellAlloc() (BackTrackCell*)SizeMalloc(sizeof(BackTrackCell));
#define BacktrackCellCellFree(junk) SizeFree(junk, sizeof(BackTrackCell));
long SubstRecordBindings(Subst_p subst, BacktrackStack_p backtracks, VarBank_p varbank);
Backtrack_p BacktrackAlloc(Term_p variable, Term_p bind, VarBank_p varbank);
bool BackTrackIsExtensionStep(Backtrack_p handle);
bool BackTrackIsClosureStep(Backtrack_p handle);
void BacktrackFree(Backtrack_p trash);
#endif
