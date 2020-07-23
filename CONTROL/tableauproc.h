#ifndef TABLEAUSATURATE

#define TABLEAUSATURATE

//#include <etableau.h>
#include <extension.h>
#include <math.h>

WFormula_p ProofStateGetConjecture(ProofState_p state);

bool TFormulasShareVariables(Sig_p sig, TFormula_p a, TFormula_p b);
long ClauseSetMoveUnits(ClauseSet_p set, ClauseSet_p units);
long ClauseSetCopyUnits(TB_p bank, ClauseSet_p set, ClauseSet_p units);
long ClauseSetFreeUnits(ClauseSet_p set);

int ConnectionTableauBatch(TableauControl_p tableaucontrol, 
										  ProofState_p proofstate, 
										  ProofControl_p proofcontrol, 
										  TB_p bank, ClauseSet_p active, 
										  int max_depth, 
										  int tableauequality);
ClauseTableau_p ConnectionTableauProofSearch(TableauControl_p tableaucontrol,
											  ProofState_p proofstate, 
											  ProofControl_p proofcontrol, 
											  TableauStack_p distinct_tableaux_stack,
										     ClauseSet_p extension_candidates,
										     int max_depth,
										     TableauStack_p new_tableaux);
ClauseTableau_p ConnectionTableauProofSearch2(TableauControl_p tableaucontrol,
											  ProofState_p proofstate, 
											  ProofControl_p proofcontrol, 
											  TableauSet_p distinct_tableaux_set,
										     ClauseSet_p extension_candidates,
										     int max_depth,
										     TableauStack_p new_tableaux);
ClauseTableau_p ConnectionCalculusExtendOpenBranches(ClauseTableau_p active_tableau, TableauStack_p new_tableaux,
																							TableauControl_p control,
																							TableauSet_p distinct_tableaux,
																							ClauseSet_p extension_candidates,
																							int max_depth, TableauStack_p max_depth_tableaux);
    

#endif
