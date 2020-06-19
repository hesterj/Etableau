//include <extension.h>
#include <foldingup.h>

typedef struct branch_saturation
{
	ProofState_p proofstate;
	ProofControl_p proofcontrol;
	ClauseTableau_p master;
	int num_open_branches;
}BranchSaturationCell, *BranchSaturation_p;

#define BranchSaturationCellAlloc()    (BranchSaturationCell*)SizeMalloc(sizeof(BranchSaturationCell))
#define BranchSaturationCellFree(junk) SizeFree(junk, sizeof(BranchSaturationCell))
void BranchSaturationFree(BranchSaturation_p branch_sat);
BranchSaturation_p BranchSaturationAlloc(ProofState_p proofstate, ProofControl_p proofcontrol, ClauseTableau_p master);

int ECloseBranch(ProofState_p proofstate, ProofControl_p proofcontrol, 
					  ClauseTableau_p branch);
int ECloseBranchProcessBranchFirst(ProofState_p proofstate, ProofControl_p proofcontrol, 
					  ClauseTableau_p branch);
int AttemptToCloseBranchesWithSuperposition(TableauControl_p tableau_control, BranchSaturation_p jobs);
