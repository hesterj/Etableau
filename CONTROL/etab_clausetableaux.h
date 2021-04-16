#ifndef CLAUSETABLEAUX
#define CLAUSETABLEAUX
#include <clb_os_wrapper.h>
#include <cio_signals.h>
#include <ccl_fcvindexing.h>
#include <che_heuristics.h>
#include <che_axiomscan.h>
#include <che_to_autoselect.h>
#include <cco_clausesplitting.h>
#include <cco_forward_contraction.h>
#include <cco_interpreted.h>
#include <ccl_satinterface.h>
#include <cco_proofproc.h>
#include <cco_scheduling.h>
#include <cco_proc_ctrl.h>
#include <etab_apr.h>
#include <time.h>
#include <arpa/inet.h>
#include <clb_plist.h>
#include <clb_quadtrees.h>
#include <clb_objtrees.h>

typedef PStack_p ClauseStack_p; // Stack of Clause_p
typedef PStack_p ClauseSetStack_p; // Stack of ClauseSet_p
typedef PStack_p TableauStack_p; // Stack of ClauseTableau_p
typedef PStack_p ClauseRep_p;
typedef PList_p TableauList_p;
typedef PStack_p BacktrackStack_p; // Stack of Backtrack_p
typedef PStack_p BindingStack_p; // Stack of Binding_p
typedef PStack_p PositionStack_p;
struct tableaucontrol_cell;
struct backup_proofstate_cell;

#define DEPTH_OK 0
#define ALL_DEPTHS_EXCEEDED 1
#define ALL_PREVIOUSLY_SELECTED 2

typedef enum
{
   TUPIgnoreProps = 0,
   TUPOpen = 1,
   TUPSaturationClosedInterreduction = 2*TUPOpen,
   TUPSaturationClosedOnBranch = 2*TUPSaturationClosedInterreduction,
   TUPSaturationClosedAfterBranch = 2*TUPSaturationClosedOnBranch,
   TUPSaturationClosed = TUPSaturationClosedOnBranch | TUPSaturationClosedAfterBranch | TUPSaturationClosedInterreduction,
   TUPFoldingBlocked = 2*TUPSaturationClosedAfterBranch,
   TUPSaturationBlocked = 2*TUPFoldingBlocked,
   TUPHeadLiteral = 2*TUPSaturationBlocked,
   TUPBacktrackedDueToMaxDepth = 2*TUPHeadLiteral,
   TUPBacktrackedDueToExtensionFailure = 2*TUPBacktrackedDueToMaxDepth,
   TUPHasBeenExtendedOn = 2*TUPBacktrackedDueToExtensionFailure,
   TUPBacktracked = TUPBacktrackedDueToMaxDepth | TUPBacktrackedDueToExtensionFailure,
   TUPHasBeenPreviouslySelected = 2*TUPHasBeenExtendedOn
} TableauProperties;

typedef struct clausetableau 
{
	ProofState_p state;
	ProofControl_p control;
	struct tableaucontrol_cell* tableaucontrol;
	TableauProperties properties;
	TB_p          terms;
	Sig_p         signature;
	bool open;
	bool saturation_closed;
	bool head_lit;    // If this node was made as a head literal in an extension step, it is true.  Otherwise false.
	long max_step;   // The number of expansion/closure steps done on the tableaux so far.  Nonzero at root node.
	long step;       // Nodes are marked in the order they were expanded/closed on.
	long depth;		// depth of the node in the tableau
	long position;   // If the node is a child, this is its position in the children array of the parent
	long arity;		// number of children
	long mark_int;   // The number of steps up a node node was closed by.  0 if not closed by extension/closure
	long folded_up;  // If the node has been folded up, this is the number of steps up it went
	long id;  		   // If a clause was split on a node, this is the id of the clause used to split.
	long previously_saturated;  // If  branch has already been saturated this amount or more, don't do it!
	long number_of_variables_on_branch;
	unsigned long maximum_depth; // The maximum depth that this tableau is allowed to search
	DStr_p info;    // Contains the substitution used to close this node

	// Only present at root.  Contains variables that are present in the tableau.
	PDArray_p tableau_variables_array;

	// The local variables of the branch.  Use UpdateLocalVariables on the branch to find them.
	PTree_p local_variables;

	// A stacks of previous steps.
	PositionStack_p master_backtracks; // This is present at the master only.  At the top is the most recent action taken anywhere in the tableau.  This is a PStack_p of PStack_p.
	BacktrackStack_p backtracks;  // This is present at every node.  This is a stack of Backtrack_p, most recent action is at the top.
	BacktrackStack_p failures; // This is present at every node.  If a node is unable to be extended on, the most recent substitution is added to this.
	// The failures can be interpreted as failure substitutions with an associated position in the tableau where the work was done.
	
	Clause_p label; // The clause at this node
	ClauseStack_p old_labels; // Keep the old labels around in case there needs to be backtracking.
	ClauseSet_p unit_axioms; // Only present at the master node
	ClauseSet_p folding_labels; // These are clauses that have been folded up to this node.
	ClauseSetStack_p old_folding_labels; // Keep the old folding labels around in case there needs to be backtracking.
	
	// Tableau set cell stuff...
	struct tableau_set_cell* set; // if this node is in a set, it is the set of open branches
	struct tableau_set_cell* open_branches; // the open branches that should be operated on
	
	// Pointers for navigating tableaux/sets of tableaux
	struct clausetableau* active_branch; // active branch for keeping track of what branch is being extended
	struct clausetableau* pred; // For navigating the set- used for open branches
	struct clausetableau* succ;
	struct clausetableau* parent; // parent node
	struct clausetableau* *children;  //array of children
	struct clausetableau* master; // root node of the tableau
}ClauseTableau, *ClauseTableau_p, **ClauseTableau_ref;

typedef int TableauStepType;
#define EXTENSION_RULE 0
#define CLOSURE_RULE 1
#define ETABLEAU_RULE 2

#define ClauseTableauCellAlloc() (ClauseTableau*)SizeMalloc(sizeof(ClauseTableau))
#define ClauseTableauCellFree(junk) SizeFree(junk, sizeof(ClauseTableau))
#define ClauseTableauArgArrayAlloc(arity) ((ClauseTableau_p*)SizeMalloc((arity)*sizeof(ClauseTableau_p)))
#define ClauseTableauArgArrayFree(junk, arity) SizeFree((junk),(arity)*sizeof(ClauseTableau_p))
#define ClauseTableauSetProp(clause, prop) SetProp((clause), (prop))
#define ClauseTableauDelProp(clause, prop) DelProp((clause), (prop))
#define ClauseTableauGiveProps(clause, prop) GiveProps((clause), (prop))
#define ClauseTableauQueryProp(clause, prop) QueryProp((clause), (prop))
void clauseprint(Clause_p clause);
void ClauseTableauDeleteAllProps(ClauseTableau_p tab);

ClauseTableau_p ClauseTableauAlloc(struct tableaucontrol_cell* tableaucontrol);
void ClauseTableauInitialize(ClauseTableau_p handle, ProofState_p state);
void ClauseTableauFree(ClauseTableau_p trash);
ClauseTableau_p ClauseTableauMasterCopy(ClauseTableau_p tab);
ClauseTableau_p ClauseTableauChildCopy(ClauseTableau_p tab, ClauseTableau_p parent);
ClauseTableau_p ClauseTableauChildLabelAlloc(ClauseTableau_p parent, Clause_p label, int position);
void ClauseTableauApplySubstitution(ClauseTableau_p tab, Subst_p subst);
void ClauseTableauApplySubstitutionToNode(ClauseTableau_p tab, Subst_p subst);
ClauseSet_p ClauseSetApplySubstitution(TB_p bank, ClauseSet_p set, Subst_p subst);
FunCode ClauseSetGetMaxVar(ClauseSet_p set);
Clause_p ClauseApplySubst(Clause_p clause,  TB_p bank, Subst_p subst);
int ClauseTableauDifference(ClauseTableau_p higher, ClauseTableau_p lower);
void ClauseTableauScoreActive(ClauseTableau_p tab);
void ClauseTableauPrint(ClauseTableau_p tab);
void ClauseTableauCollectSteps(ClauseTableau_p tab, PStack_p steps);
void ClauseTableauTPTPPrint(ClauseTableau_p tab);
void ClauseTableauPrint2(ClauseTableau_p tab);

void HCBClauseSetEvaluate(HCB_p hcb, ClauseSet_p clauses);

ClauseSet_p ClauseSetCopy(TB_p bank, ClauseSet_p set);
ClauseSet_p ClauseSetFlatCopy(ClauseSet_p set);
ClauseSet_p ClauseSetFlatCopyIndexed(ClauseSet_p set);
ClauseSet_p ClauseSetCopyOpt(ClauseSet_p set);
ClauseSet_p ClauseSetCopyIndexedOpt(ClauseSet_p set);
Clause_p ClauseFlatCopyFresh(Clause_p clause, ClauseTableau_p tableau);
long ClauseSetInsertSetFlatCopyIndexed(ClauseSet_p to, ClauseSet_p from);
long ClauseSetInsertSetCopyOptIndexed(ClauseSet_p to, ClauseSet_p from);
bool ClausesAreDisjoint(Clause_p a, Clause_p b);

Clause_p ClauseCopyFresh(Clause_p clause, ClauseTableau_p tableau);  // Major memory hog
void ClauseBindFresh(Clause_p clause, Subst_p subst, ClauseTableau_p tableau);

ClauseSet_p EqualityAxioms(TB_p bank);
PList_p ClauseSetToPList(ClauseSet_p set);

Subst_p ClauseContradictsClause(ClauseTableau_p tab, Clause_p a, Clause_p b);
Subst_p ClauseContradictsClauseSubst(Clause_p a, Clause_p b, Subst_p subst);
int ClauseTableauGetDeepestBranch(ClauseTableau_p tab);
int ClauseTableauGetShallowestBranch(ClauseTableau_p tab);


ClauseTableau_p TableauStartRule(ClauseTableau_p tab, Clause_p start);
int ClauseTableauAssertCheck(ClauseTableau_p tab);

bool ClauseTableauBranchContainsLiteral(ClauseTableau_p parent, Eqn_p literal);
bool ClauseTableauIsLeafRegular(ClauseTableau_p tab);

void ClauseTableauRegisterStep(ClauseTableau_p tab);
void ClauseTableauDeregisterStep(ClauseTableau_p tab);

void ClauseTableauPrintDOTGraphToFile(FILE* file, ClauseTableau_p tab);
void ClauseTableauPrintDOTGraph(ClauseTableau_p tab);
void ClauseTableauPrintDOTGraphChildren(ClauseTableau_p tab, FILE* dotgraph);
void ClauseTableauPrintDerivation(FILE* out, ClauseTableau_p final_tableau, TableauStack_p derivation);

void AssertClauseStackMembersAreInSet(ClauseStack_p stack);
void AssertAllOldLabelsAreInSet(ClauseTableau_p tab);
void PositionStackFreePositions(PositionStack_p positions);

#define NodeIsLeaf(tab) (tab->arity == 0)
#define NodeIsNonLeaf(tab) (tab->arity != 0)
#define NodeIsHeadLiteral(tab) (tab->head_lit)
#define BranchIsOpen(tab) (tab->set)
#define MaximumDepth(tab) (tab->master->maximum_depth)


/*  Now for tableau sets...
 * 
 * 
*/

typedef struct tableau_set_cell
{
	ClauseTableau_p anchor;
	long members;
}TableauSetCell, *TableauSet_p;


#define TableauSetCellAlloc()    (TableauSetCell*)SizeMalloc(sizeof(TableauSetCell))
#define TableauSetCellFree(junk) SizeFree(junk, sizeof(TableauSetCell))

#define      TableauSetEmpty(set)\
             ((set)->anchor->succ == (set)->anchor)

#define TableauSetCardinality(set) (set->members)
TableauSet_p TableauSetAlloc();
TableauSet_p TableauSetCopy(TableauSet_p set);
void TableauSetInsert(TableauSet_p set, ClauseTableau_p tab);
void ClauseTableauPrintBranch(ClauseTableau_p branch);
void ClauseTableauPrintBranch2(ClauseTableau_p branch);
ClauseTableau_p   TableauSetExtractFirst(TableauSet_p list);
ClauseTableau_p TableauSetExtractEntry(ClauseTableau_p set);
void TableauSetFree(TableauSet_p handle);
void TableauSetDrainToStack(PStack_p to, TableauSet_p from);
void TableauStackDrainToSet(TableauSet_p to, PStack_p from);
void TableauSetMoveClauses(TableauSet_p to, TableauSet_p from);
void ClauseTableauDeselectBranches(TableauSet_p open_branches);


void TableauStackFreeTableaux(PStack_p stack);
void TableauStackFree(TableauStack_p stack);
void ClauseTableauCollectLeaves(ClauseTableau_p tab, TableauSet_p leaves);
void ClauseTableauCollectLeavesStack(ClauseTableau_p tab, PStack_p leaves);

bool TableauDominatesNode(ClauseTableau_p tab, ClauseTableau_p node);

Term_p ClauseTableauGetFreshVar(ClauseTableau_p tab, Term_p old_var);
void ClauseTableauBindFreshVar(ClauseTableau_p master, Subst_p subst, Term_p old_var);
long ClauseGetIdent(Clause_p clause);
long          SubstDStrPrint(DStr_p str, Subst_p subst, Sig_p sig, DerefType deref);

/*  Tableau control struct
 * 
 * 
*/

typedef struct tableaucontrol_cell
{
	EPCtrl_p process_control;
	ProofState_p proofstate;
	//struct backup_proofstate_cell* backup;
	ProofControl_p proofcontrol;
	TB_p terms;
	bool branch_saturation_enabled; // Is branch saturation enabled?
	bool satisfiable;
	bool all_start_rule_created;
	bool only_saturate_max_depth_branches;
	long quicksat; // Maximum number of processed clauess in saturation attempts
	long number_of_extensions;
	long number_of_saturation_attempts;
	long number_of_successful_saturation_attempts;
	long number_of_saturations_closed_in_interreduction;
	long number_of_saturations_closed_on_branch;
	long number_of_saturations_closed_after_branch;
	long neg_conjectures;
	long number_of_nodes_freed;
	char *problem_name;
	char *dot_output;
	char *clausification_buffer;
	long multiprocessing_active;  // Have we reached enough tableaux to break the problem in to forks?
	PStack_p new_tableaux;
	ClauseTableau_p closed_tableau;
	ClauseSet_p unprocessed;
	ClauseSet_p label_storage; // This is to ensure that terms occurring in the tableau are not free'd by the gc
	TableauStack_p tableaux_trash;
	TableauStack_p max_depth_tableaux;
	PObjTree_p feature_tree;
	PList_p feature_list;
}TableauControlCell, *TableauControl_p;

#define TableauControlCellAlloc()    (TableauControlCell*)SizeMalloc(sizeof(TableauControlCell))
#define TableauControlCellFree(junk) SizeFree(junk, sizeof(TableauControlCell))


TableauControl_p TableauControlAlloc(long neg_conjectures, 
									 char *problem_name,
									 char *dot_output,
									 ProofState_p proofstate,
									 ProofControl_p proofcontrol,
									 bool branch_saturation_enabled,
									 bool only_saturate_max_depth_branches,
									 long num_cores_to_use,
									 long quicksat);
void TableauControlFree(TableauControl_p trash);
void EqnRepFree(void *eqn_p);

//  Stuff for representing branches of a tableau as a stack of integers
ClauseRep_p ClauseGetRepresentation(Clause_p clause);

void ClauseStackFree(ClauseStack_p trash);
void EtableauStatusReport(TableauControl_p tableaucontrol,
                          ClauseSet_p active,
                          ClauseTableau_p resulting_tab);
int ClauseCmpByIdent(const void* clause1, const void* clause2);
void ClauseStackPrint(FILE* out, PStack_p stack);

inline int GetDesiredNumberOfTableaux(TableauControl_p control);
inline int GetDesiredNumberOfTableaux(TableauControl_p control)
{
	return 2*(control->multiprocessing_active);
}

long ClauseTableauHash(ClauseTableau_p tableau);
void ClauseTableauCreateID(ClauseTableau_p tableau, DStr_p str);
long ClauseTableauAddDepths(ClauseTableau_p tab);
double ClauseTableauGetAverageDepth(ClauseTableau_p tableau);
void TermTreePrintCodes(FILE* out, PTree_p tree);

#endif
