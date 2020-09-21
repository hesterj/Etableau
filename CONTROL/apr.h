#ifndef APR

#define APR

#include <ccl_relevance.h>
#include <clausetableaux.h>

/*  Alternating Path Relevance functions and struct
 *  These are functions for a directed graph for the purpose of 
 *  computing alternating path relevance.
 *  The literals and clauses are NOT copies, so are not free'd in 
 *  the graph cleanup methods.
 *  The entry point is APRProofStateProcess.  
 *  John Hester
*/

typedef struct aprcontrolcell
{
	long max_used_node_id; 
	long max_var; // Largest (negative) variable f_code used
	bool equality; // Create equality axioms?
	bool build_graph; // Actually create edges- used for printing the graph at end
	IntMap_p map; // Given an ident, return the stack of nodes for that clause
	IntMap_p original_clause_map; // Given an ident, return a pointer to the original clause
	PStack_p buckets; // Collection of all the buckets.  One clause corresponds with one bucket
	PStack_p graph_nodes; // Stack of all the nodes
	PStack_p type1_nodes; 
	PStack_p type2_nodes;
	PStack_p type1_equality_nodes;
	PStack_p type1_nonequality_nodes;
	ClauseSet_p equality_axioms;
	ClauseSet_p fresh_clauses; // Set of clauses with all fresh variables for multithreading
	FixedDArray_p substitution_axiom_characteristic; // 0 at index f_code if no equality axiom created, 1 otherwise
	Sig_p sig;
	TB_p terms;
}APRControlCell, *APRControl_p;

typedef struct aprcell
{
	long id;
	short int type;
	bool visited;
	bool equality_node;
	Eqn_p literal;
	Clause_p clause;
	PStack_p edges;
}APRCell, *APR_p;

#define APRCellAlloc() (APRCell*)SizeMalloc(sizeof(APRCell))
#define APRCellFree(junk) SizeFree(junk, sizeof(APRCell))
#define APRControlCellAlloc() (APRControlCell*)SizeMalloc(sizeof(APRControlCell))
#define APRControlCellFree(junk) SizeFree(junk, sizeof(APRControlCell))
APR_p APRAlloc(short int type, Eqn_p literal, Clause_p clause, bool equality);
void APRFree(APR_p trash);
APRControl_p APRControlAlloc(Sig_p sig, TB_p terms);
void APRControlFree(APRControl_p trash);
bool APRComplementarilyUnifiable(Eqn_p a, Eqn_p b);
PStack_p APRBuildGraphConjectures(APRControl_p control, ClauseSet_p clauses, PList_p conjectures, int distance);
int APRGraphAddClauses(APRControl_p control, ClauseSet_p clauses, bool equality);
int APRGraphAddClausesList(APRControl_p control, PList_p clauses);
bool APRGraphAddNodes(APRControl_p control, Clause_p clause, bool equality);
long APRGraphUpdateEdges(APRControl_p control);
long APRGraphUpdateEdgesDeleteOld(APRControl_p control);
long APRGraphUpdateEdgesFromListStack(APRControl_p control,
												  PTree_p *already_visited,
												  PStack_p start_nodes,
												  PStack_p relevant,
												  int distance);
long APRGraphCreateDOT(APRControl_p control);
long APRGraphCreateDOTClausesLabeled(APRControl_p control);
long APRGraphCreateDOTClauses(APRControl_p control);
Clause_p APRGetBucketClause(PStack_p bucket);
int APRBreadthFirstSearch(APRControl_p control, PStack_p nodes, PTree_p *clauses, int relevance);
PStack_p APRRelevance(APRControl_p control, ClauseSet_p set, int relevance);
PStack_p APRCollectNodesFromList(APRControl_p control, PList_p list);

PStack_p APRRelevanceList(APRControl_p control, PList_p list, int relevance);
PStack_p APRRelevanceNeighborhood(Sig_p sig, ClauseSet_p set, PList_p list, int relevance, bool equality, bool print_graph);

void APRProofStateProcess(ProofState_p proofstate, int relevance, bool equality, bool print_apr_graph);
void APRProofStateProcessTest(ProofState_p proofstate, int relevance, bool equality, bool print_apr_graph);
void APRLiveProofStateProcess(ProofState_p proofstate, int relevance);
ClauseSet_p apr_EqualityAxioms(TB_p bank, bool substitution);

int APRNodeStackAddSubstAxioms(APRControl_p control, PStack_p nodes);
int APRNodeAddSubstAxioms(APRControl_p control, APR_p node);
int EqnAddSubstAxioms(APRControl_p control, Eqn_p eqn);
int TermAddSubstAxioms(APRControl_p control, Term_p term);
Clause_p ClauseCreateSubstitutionAxiom(APRControl_p control, Sig_p sig, FunCode f_code);

int APRCreateInterClauseEdges(APRControl_p control,
										Eqn_p current_literal,
										PStack_p type1stack, 
										PStack_p new_start_nodes,
										PStack_p current_edges,
										PStack_p relevant, 
										PStackPointer t1_iter, 
										int distance);
										
static inline void APRVerify();

static inline void APRVerify()
{
	fprintf(GlobalOut, "# APR header successfully linked.\n");
}



#endif
