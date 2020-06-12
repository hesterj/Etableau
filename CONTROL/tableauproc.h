#ifndef TABLEAUSATURATE

#define TABLEAUSATURATE

//#include <etableau.h>
#include <extension.h>

WFormula_p ProofStateGetConjecture(ProofState_p state);

bool TFormulasShareVariables(Sig_p sig, TFormula_p a, TFormula_p b);
long ClauseSetMoveUnits(ClauseSet_p set, ClauseSet_p units);

Clause_p ConnectionTableauBatch(TableauControl_p tableaucontrol, 
										  ProofState_p proofstate, 
										  ProofControl_p proofcontrol, 
										  TB_p bank, ClauseSet_p active, 
										  int max_depth, 
										  int tableauequality);
ClauseTableau_p ConnectionTableauProofSearch(TableauControl_p tableaucontrol,
															ProofState_p proofstate, 
															ProofControl_p proofcontrol, 
															TableauSet_p distinct_tableaux,
															ClauseSet_p extension_candidates,
															int max_depth,
															PStack_p new_tableaux);
ClauseTableau_p ConnectionCalculusExtendOpenBranches(ClauseTableau_p active_tableau, PStack_p new_tableaux,
																							TableauControl_p control,
																							TableauSet_p distinct_tableaux,
																							ClauseSet_p extension_candidates,
																							int max_depth);
    

#endif
