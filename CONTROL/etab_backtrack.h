#ifndef ETAB_BACKTRACK
#define ETAB_BACKTRACK
#include<cco_proofproc.h>
#include<etab_extension.h>
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
    TableauStepType type;
    long id; // This is the ident of the clause split in the extension step, or the clause used in the closure rule
    long head_lit_position; // This is the position in the literals array of the selected clause of the head literal.  0 if it was a closure rule step
    PStack_p bindings; // This is a stack of the Binding_p that were used in this step
    PStack_p position; // If an extension step was done at this step, this is a path to the parent node of the step from the master node.
    bool completed;
    // If it was a closure rule done, position is the closed node.
    // Clearly, if a position has no children, then it was a closure step, extension otherwise.
    // There are no branch saturations stored, as they do not affect the tableaux and are purely good.
}BackTrackCell, *Backtrack_p;

// This is a way to keep information about substitutions around
// Avoid using this directly
typedef struct bindingcell
{
    Term_p variable;
    Term_p bind;
}BindingCell, *Binding_p;


typedef int BacktrackStatus;
typedef int* BacktrackStatus_p;
#define BACKTRACK_FAILURE 0
#define BACKTRACK_OK 1
#define NEXT_TABLEAU 2
#define RETURN_NOW 3

#define BacktrackCellAlloc() (BackTrackCell*)SizeMalloc(sizeof(BackTrackCell))
#define BacktrackCellCellFree(junk) SizeFree(junk, sizeof(BackTrackCell))
PStack_p SubstRecordBindings(Subst_p subst);
Backtrack_p BacktrackAlloc(ClauseTableau_p position, Subst_p subst, long head_lit_position, TableauStepType type);
Backtrack_p BacktrackCopy(Backtrack_p original, ClauseTableau_p new_master);
BacktrackStack_p BacktrackStackCopy(BacktrackStack_p stack, ClauseTableau_p new_master);
#define BacktrackIsExtensionStep(bt) (bt->type == EXTENSION_RULE)
#define BacktrackIsClosureStep(bt) (bt->type == CLOSURE_RULE)
#define BacktrackIsEtableauStep(bt) (bt->type == ETABLEAU_RULE)
bool VerifyBacktrackIsExtensionStep(Backtrack_p handle);
bool VerifyBacktrackIsClosureStep(Backtrack_p handle);
void BacktrackFree(Backtrack_p trash);
ClauseTableau_p GetNodeFromPosition(ClauseTableau_p master, PStack_p position);
bool SubstIsFailure(ClauseTableau_p tab, Subst_p subst);
bool ExtensionIsFailure(ClauseTableau_p tab, Subst_p subst, long extension_id, long head_lit_position);
bool BindingOccursInSubst(Binding_p binding, Subst_p subst);
bool BacktrackContainsSubst(Backtrack_p backtrack, Subst_p subst);
bool BacktrackWrapper(ClauseTableau_p master);
bool BacktrackMultiple(ClauseTableau_p master, long denominator);
void Backtrack(Backtrack_p bt);
void RollBackEveryNode(ClauseTableau_p master);
void DeleteAllBacktrackInformation(ClauseTableau_p tableau);
void BacktrackStackDeleteInformation(BacktrackStack_p trash);


// Binding stuff, this is only used for failure substitutions!
#define BindingCellAlloc() (BindingCell*)SizeMalloc(sizeof(BindingCell));
#define BindingCellFree(junk) SizeFree(junk, sizeof(BindingCell));
Binding_p BindingAlloc(Term_p var); // The variable is just that, the bind is what the variable is dereferenced to.
void BindingFree(Binding_p trash); // The bind is unshared so must be free'd, variables are always shared
Binding_p BindingCopy(Binding_p old_bind);
PStack_p BindingStackCopy(PStack_p binding_stack);
void BindingStackFree(PStack_p trash);

#endif
