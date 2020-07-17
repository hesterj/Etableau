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
#include <apr.h>
#include <time.h>
#include <arpa/inet.h>
#include <clb_plist.h>

typedef PStack_p ClauseStack_p;
typedef PStack_p TableauStack_p;

typedef struct clausetableau 
{
	ProofState_p state;
	ProofControl_p control;
	TB_p          terms;
	Sig_p         signature;
	bool open;
	bool saturation_closed;
	bool head_lit;    // If this node was made as a head literal in an extension step, it is true.  Otherwise false.
	short max_step;   // The number of expansion/closure steps done on the tableaux so far.  Nonzero at root node.
	short step;       // Nodes are marked in the order they were expanded/closed on.
	short depth;		// depth of the node in the tableau
	short position;   // If the node is a child, this is its position in the children array of the parent
	short arity;		// number of children
	short mark_int;   // The number of steps up a node node was closed by.  0 if not closed by extension/closure
	short folded_up;  // If the node has been folded up, this is the number of steps up it went
	long id;  		   // If a clause was split on a node, this is the id of the clause used to split.
	long max_var;     // f_code of the maximal variable in the tableau
	//DStr_p info;    // Contains the substitution used to close this node
	PStack_p local_variables; // The variables of the tableau that are local to the branch.
	
	TableauStack_p derivation;
	
	Clause_p label; // The clause at this node
	Clause_p tmp_label; // For creating temporary copies of clauses, i/e in closure
	ClauseSet_p unit_axioms; // Only present at the master node
	ClauseSet_p folding_labels; // These are clauses that have been folded up to this node.
	
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

#define ClauseTableauCellAlloc() (ClauseTableau*)SizeMalloc(sizeof(ClauseTableau))
#define ClauseTableauCellFree(junk) SizeFree(junk, sizeof(ClauseTableau))
#define ClauseTableauArgArrayAlloc(arity) ((ClauseTableau_p*)SizeMalloc((arity)*sizeof(ClauseTableau_p)))
#define ClauseTableauArgArrayFree(junk, arity) SizeFree((junk),(arity)*sizeof(ClauseTableau_p))
ClauseTableau_p ClauseTableauAlloc();
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
void ClauseTableauPrint2(ClauseTableau_p tab);

void HCBClauseSetEvaluate(HCB_p hcb, ClauseSet_p clauses);

ClauseSet_p ClauseSetCopy(TB_p bank, ClauseSet_p set);
ClauseSet_p ClauseSetFlatCopy(TB_p bank, ClauseSet_p set);
ClauseSet_p ClauseSetFlatCopy(TB_p bank, ClauseSet_p set);
Clause_p ClauseFlatCopyFresh(Clause_p clause, ClauseTableau_p tableau);

Clause_p ClauseCopyFresh(Clause_p clause, ClauseTableau_p tableau);  // Major memory hog

ClauseSet_p EqualityAxioms(TB_p bank);

long ClauseGetIdent(Clause_p clause);

Subst_p ClauseContradictsClause(ClauseTableau_p tab, Clause_p a, Clause_p b);
Subst_p ClauseContradictsClauseSubst(Clause_p a, Clause_p b, Subst_p subst);


ClauseTableau_p TableauStartRule(ClauseTableau_p tab, Clause_p start);
int ClauseTableauAssertCheck(ClauseTableau_p tab);

bool ClauseTableauBranchContainsLiteral(ClauseTableau_p branch, Eqn_p literal);
bool ClauseTableauIsLeafRegular(ClauseTableau_p tab);

void ClauseTableauPrintDOTGraphToFile(FILE* file, ClauseTableau_p tab);
void ClauseTableauPrintDOTGraph(ClauseTableau_p tab);
void ClauseTableauPrintDOTGraphChildren(ClauseTableau_p tab, FILE* dotgraph);


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

TableauSet_p TableauSetAlloc();
TableauSet_p TableauSetCopy(TableauSet_p set);
void TableauSetInsert(TableauSet_p list, ClauseTableau_p set);
void ClauseTableauPrintBranch(ClauseTableau_p branch);
void ClauseTableauPrintBranch2(ClauseTableau_p branch);
ClauseTableau_p   TableauSetExtractFirst(TableauSet_p list);
ClauseTableau_p TableauSetExtractEntry(ClauseTableau_p set);
void TableauSetFree(TableauSet_p handle);

void TableauStackFreeTableaux(PStack_p stack);
void ClauseTableauCollectLeaves(ClauseTableau_p tab, TableauSet_p leaves);
void ClauseTableauCollectLeavesStack(ClauseTableau_p tab, PStack_p leaves);

bool TableauDominatesNode(ClauseTableau_p tab, ClauseTableau_p node);

typedef struct tableaucontrol_cell
{
	ProofState_p proofstate;
	ProofControl_p proofcontrol;
	int number_of_extensions;
	long neg_conjectures;
	char *problem_name;
	PStack_p new_tableaux;
	ClauseTableau_p closed_tableau;
	ClauseSet_p unprocessed;
	TB_p terms;
	bool branch_saturation_enabled; // Is branch saturation enabled?
	bool satisfiable;
	PStack_p trash;  // Old tableaux for tracing bugs... should not be used normally
	char *clausification_buffer;
}TableauControlCell, *TableauControl_p;

#define TableauControlCellAlloc()    (TableauControlCell*)SizeMalloc(sizeof(TableauControlCell))
#define TableauControlCellFree(junk) SizeFree(junk, sizeof(TableauControlCell))


TableauControl_p TableauControlAlloc(long neg_conjectures, 
												 char *problem_name, 
												 ProofState_p proofstate, 
												 ProofControl_p proofcontrol,
												 bool branch_saturation_enabled);
void TableauControlFree(TableauControl_p trash);

#endif
