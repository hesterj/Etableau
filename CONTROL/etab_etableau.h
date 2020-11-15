#include <etab_foldingup.h>
#include "etab_xgboost_interaction.h"

typedef struct branch_saturation
{
	ProofState_p proofstate;
	ProofControl_p proofcontrol;
	ClauseTableau_p master; // The tableau that is having its branches saturated
	int num_open_branches; 
	long max_proc; // Max number of clauses to process on a branch
}BranchSaturationCell, *BranchSaturation_p;

int process_branch_nofork(ProofState_p proofstate, 
						  ProofControl_p proofcontrol,
						  ClauseTableau_p branch,
						  TableauControl_p tableau_control,
						  long max_proc);

#define BranchSaturationCellAlloc()    (BranchSaturationCell*)SizeMalloc(sizeof(BranchSaturationCell))
#define BranchSaturationCellFree(junk) SizeFree(junk, sizeof(BranchSaturationCell))
void BranchSaturationFree(BranchSaturation_p branch_sat);
BranchSaturation_p BranchSaturationAlloc(ProofState_p proofstate, 
													  ProofControl_p proofcontrol, 
													  ClauseTableau_p master,
													  long max_proc);


int ECloseBranchProcessBranchFirst(ProofState_p proofstate, ProofControl_p proofcontrol, 
					  ClauseTableau_p branch);
int ECloseBranchProcessBranchFirstSerial(ProofState_p proofstate, 
													  ProofControl_p proofcontrol, 
													  ClauseTableau_p branch, 
													  long max_proc);
int ECloseBranch(ProofState_p proofstate, 
					  ProofControl_p proofcontrol,
					  TableauControl_p tableaucontrol, 
					  ClauseTableau_p branch);
int AttemptToCloseBranchesWithSuperposition(TableauControl_p tableau_control, BranchSaturation_p jobs);
int AttemptToCloseBranchesWithSuperpositionSerial(TableauControl_p tableau_control, BranchSaturation_p jobs);

void EtableauProofStateResetClauseSets(ProofState_p state);
int EtableauInsertBranchClausesIntoUnprocessed(ProofState_p state,
                                 ProofControl_p control,
                                 ClauseTableau_p branch);
void TermTreeDeleteRWLinks(Term_p root);
void TermCellStoreDeleteRWLinks(TermCellStore_p store);


int ProcessSpecificClauseWrapper(ProofState_p state, ProofControl_p control, Clause_p clause);


int ProcessSpecificClauseSetWrapper(ProofState_p state, ProofControl_p control, ClauseSet_p set);
