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
struct tableaucontrol_cell;

#define DEPTH_OK 0
#define ALL_DEPTHS_EXCEEDED 1
#define ALL_PREVIOUSLY_SELECTED 2

typedef struct clausetableau 
{
	ProofState_p state;
	ProofControl_p control;
	struct tableaucontrol_cell* tableaucontrol;
	TB_p          terms;
	Sig_p         signature;
	bool open;
	bool saturation_closed;
	bool previously_selected;
	bool head_lit;    // If this node was made as a head literal in an extension step, it is true.  Otherwise false.
	bool saturation_blocked;
	bool folding_blocked;
	short max_step;   // The number of expansion/closure steps done on the tableaux so far.  Nonzero at root node.
	short step;       // Nodes are marked in the order they were expanded/closed on.
	short depth;		// depth of the node in the tableau
	short position;   // If the node is a child, this is its position in the children array of the parent
	short arity;		// number of children
	short mark_int;   // The number of steps up a node node was closed by.  0 if not closed by extension/closure
	short folded_up;  // If the node has been folded up, this is the number of steps up it went
	long id;  		   // If a clause was split on a node, this is the id of the clause used to split.
	long previously_saturated;  // If  branch has already been saturated this amount or more, don't do it!
	long max_var;     // f_code of the maximal variable in the tableau
	DStr_p info;    // Contains the substitution used to close this node
	PStack_p local_variables; // The variables of the tableau that are local to the branch.
	
	 // Only present at root.  Contains variables that are present in the tableau.
	PTree_p tableau_variables;

	// A stacks of previous steps.
	PStack_p master_backtracks; // This is present at the master only.  At the top is the most recent action taken anywhere in the tableau.  This is a PStack_p of PStack_p.
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
ClauseSet_p ClauseSetFlatCopy(TB_p bank, ClauseSet_p set);
Clause_p ClauseFlatCopyFresh(Clause_p clause, ClauseTableau_p tableau);

Clause_p ClauseCopyFresh(Clause_p clause, ClauseTableau_p tableau);  // Major memory hog

ClauseSet_p EqualityAxioms(TB_p bank);
PList_p ClauseSetToPList(ClauseSet_p set);

Subst_p ClauseContradictsClause(ClauseTableau_p tab, Clause_p a, Clause_p b);
Subst_p ClauseContradictsClauseSubst(Clause_p a, Clause_p b, Subst_p subst);
int ClauseTableauGetDeepestBranch(ClauseTableau_p tab);
int ClauseTableauGetShallowestBranch(ClauseTableau_p tab);


ClauseTableau_p TableauStartRule(ClauseTableau_p tab, Clause_p start);
int ClauseTableauAssertCheck(ClauseTableau_p tab);

bool ClauseTableauBranchContainsLiteral(ClauseTableau_p branch, Eqn_p literal);
bool ClauseTableauIsLeafRegular(ClauseTableau_p tab);

void ClauseTableauRegisterStep(ClauseTableau_p tab);

void ClauseTableauPrintDOTGraphToFile(FILE* file, ClauseTableau_p tab);
void ClauseTableauPrintDOTGraph(ClauseTableau_p tab);
void ClauseTableauPrintDOTGraphChildren(ClauseTableau_p tab, FILE* dotgraph);
void ClauseTableauPrintDerivation(FILE* out, ClauseTableau_p final_tableau, TableauStack_p derivation);

void AssertClauseStackMembersAreInSet(ClauseStack_p stack);
void AssertAllOldLabelsAreInSet(ClauseTableau_p tab);

#define NodeIsLeaf(tab) (tab->arity == 0)
#define NodeIsNonLeaf(tab) (tab->arity != 0)
#define NodeIsHeadLiteral(tab) (tab->head_lit)


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
long ClauseGetIdent(Clause_p clause);
long          SubstDStrPrint(DStr_p str, Subst_p subst, Sig_p sig, DerefType deref);

/*  Tableau control struct
 * 
 * 
*/

typedef struct tableaucontrol_cell
{
	ProofState_p proofstate;
	ProofControl_p proofcontrol;
	int number_of_extensions;
	long number_of_saturation_attempts;
	long number_of_successful_saturation_attempts;
	long neg_conjectures;
	long number_of_nodes_freed;
	char *problem_name;
	char *dot_output;
	PStack_p new_tableaux;
	ClauseTableau_p closed_tableau;
	ClauseSet_p unprocessed;
	ClauseSet_p label_storage; // This is to ensure that terms occurring in the tableau are not free'd by the gc
	TB_p terms;
	bool branch_saturation_enabled; // Is branch saturation enabled?
	int multiprocessing_active;  // Have we reached enough tableaux to break the problem in to forks?
	bool satisfiable;
	TableauStack_p tableaux_trash;
	TableauStack_p max_depth_tableaux;
	char *clausification_buffer;
	EPCtrl_p process_control;
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
									 int num_cores_to_use);
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

#endif
