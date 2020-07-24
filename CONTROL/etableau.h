//include <extension.h>
#include <foldingup.h>

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

int ECloseBranch(ProofState_p proofstate, ProofControl_p proofcontrol, 
					  ClauseTableau_p branch);
int ECloseBranchProcessBranchFirst(ProofState_p proofstate, ProofControl_p proofcontrol, 
					  ClauseTableau_p branch);
int ECloseBranchProcessBranchFirstSerial(ProofState_p proofstate, 
													  ProofControl_p proofcontrol, 
													  ClauseTableau_p branch, 
													  long max_proc);
int AttemptToCloseBranchesWithSuperposition(TableauControl_p tableau_control, BranchSaturation_p jobs);
int AttemptToCloseBranchesWithSuperpositionSerial(TableauControl_p tableau_control, BranchSaturation_p jobs);

void EtableauProofStateResetClauseSets(ProofState_p state);
void EtableauInsertBranchClausesIntoUnprocessed(ProofState_p state,
                                 ProofControl_p control,
                                 ClauseTableau_p branch);
