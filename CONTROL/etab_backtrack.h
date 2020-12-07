#ifndef ETAB_BACKTRACK
#define ETAB_BACKTRACK
#include<cco_proofproc.h>
//#include<etab_tableauproc.h>
#include <etab_etableau.h>

// These can be used to store the actions done on the tableau
// They also can be used to record failure substitutions-
// i/e if a particular step forced backtracking, new steps can be checked against this to
// prevent repeating the exact same step
// The master node of a tableaux has a stack of these that keep track of the steps made.
// There is also a stack of these at the master node that represent failure steps, things that have been backtracked and will not be repeated.
typedef struct backtrackcell
{
    ClauseTableau_p master;
    bool is_extension_step;
    //Term_p variable;
    //Term_p bind;
    //PStack_p bindings; // This is a stack of the variable bindings that were used in this step
    PStack_p position; // If an extension step was done at this step, this is a path to the parent node of the step from the master node.
    // If it was a closure rule done, position is the closed node.
    // Clearly, if a position has no children, then it was a closure step, extension otherwise.
    // There are no branch saturations stored, as they do not affect the tableaux and are purely good.
}BackTrackCell, *Backtrack_p;

//typedef struct bindingcell
//{
    //Term_p variable;
    //Term_p bind;
//}BindingCell, *Binding_p;


#define BacktrackCellAlloc() (BackTrackCell*)SizeMalloc(sizeof(BackTrackCell))
#define BacktrackCellCellFree(junk) SizeFree(junk, sizeof(BackTrackCell))
//long SubstRecordBindings(Subst_p subst, BacktrackStack_p backtracks, VarBank_p varbank, ClauseTableau_p position);
Backtrack_p BacktrackAlloc_UNUSED(Subst_p subst, VarBank_p varbank, ClauseTableau_p position);
Backtrack_p BacktrackAlloc(ClauseTableau_p position);
Backtrack_p BacktrackCopy(Backtrack_p original);
#define BacktrackIsExtensionStep(bt) (bt->is_extension_step)
#define BacktrackisClosureStep(bt) !BacktrackIsExtensionStep(bt)
bool VerifyBacktrackIsExtensionStep(Backtrack_p handle);
bool VerifyBacktrackIsClosureStep(Backtrack_p handle);
void BacktrackFree(Backtrack_p trash);
ClauseTableau_p GetNodeFromPosition(ClauseTableau_p master, PStack_p position);
BacktrackStack_p BacktrackStackCopy(BacktrackStack_p stack);
void Backtrack(Backtrack_p bt);
void RollBackEveryNode(ClauseTableau_p master);

// Binding stuff, currently unused... Much easier to just keep copies of old clauses.
//#define BindingCellAlloc() (BindingCell*)SizeMalloc(sizeof(BindingCell));
//#define BindingCellFree(junk) SizeFree(junk, sizeof(BindingCell));
//Binding_p BindingAlloc(Term_p var, VarBank_p vars); // The variable is just that, the bind is what the variable is dereferenced to.
//void BindingFree(Binding_p trash); // The bind is unshared so must be free'd, variables are always shared
#endif
