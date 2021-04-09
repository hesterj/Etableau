#ifndef ETABLEAU
#define ETABLEAU
#include "etab_foldingup.h"
#include "etab_xgboost_interaction.h"

typedef struct branch_saturation
{
	ProofState_p proofstate;
	ProofControl_p proofcontrol;
	ClauseTableau_p master; // The tableau that is having its branches saturated
	int num_open_branches; 
	long max_proc; // Max number of clauses to process on a branch
}BranchSaturationCell, *BranchSaturation_p;


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
ErrorCodes ECloseBranchWithInterreduction(ProofState_p proofstate,
										  ProofControl_p proofcontrol,
										  ClauseTableau_p branch,
										  long max_proc);
ErrorCodes ECloseBranchWrapper(ProofState_p proofstate,
							   ProofControl_p proofcontrol,
							   ClauseTableau_p branch,
							   TableauControl_p tableau_control,
							   long max_proc);
int AttemptToCloseBranchesWithSuperposition(TableauControl_p tableau_control, BranchSaturation_p jobs);
int AttemptToCloseBranchesWithSuperpositionSerial(TableauControl_p tableau_control, BranchSaturation_p jobs);

void EtableauProofStateResetClauseSets(ProofState_p state);
int EtableauInsertBranchClausesIntoUnprocessed(ProofState_p state,
                                 ProofControl_p control,
                                 ClauseTableau_p branch);
void TermTreeDeleteRWLinks(Term_p root);
void TermCellStoreDeleteRWLinks(TermCellStore_p store);

long ClauseTableauCollectBranchCopyLabels(ClauseTableau_p branch, ClauseSet_p set, PStack_p branch_labels);

int ProcessSpecificClauseWrapper(ProofState_p state, ProofControl_p control, Clause_p clause);
int ProcessSpecificClauseWrapperNoCopy(ProofState_p state, ProofControl_p control, Clause_p clause, Clause_p *success_ref);


ErrorCodes ProcessSpecificClauseSetWrapper(ProofState_p state, ProofControl_p control, ClauseSet_p set);
ErrorCodes ProcessSpecificClauseStackWrapper(ProofState_p state, ProofControl_p control, ClauseStack_p stack);
ErrorCodes ProcessSpecificClauseStackWrapperNoCopy(ProofState_p state, ProofControl_p control, ClauseStack_p stack, Clause_p *success_ref);

bool EtableauSaturateAllTableauxInStack(TableauControl_p tableaucontrol, TableauStack_p distinct_tableaux_stack, ClauseSet_p active, long maximum);
Clause_p ClauseCopyAndPrepareForSaturation(Clause_p clause, TB_p bank, HCB_p hcb);
long ClauseSetCopyInsertAndPrepareForSaturation(ClauseSet_p from, ClauseSet_p to, TB_p bank, HCB_p hcb, PStack_p branch_labels);

long TermTreeUnbind(Term_p root);
long TermCellStoreUnbindAll(TermCellStore_p store);
long TermBankUnbindAll(TB_p bank);

typedef struct backup_proofstate_cell
{
    long num_processed;
    ClauseSet_p   processed_pos_rules;
    ClauseSet_p   processed_pos_eqns;
    ClauseSet_p   processed_neg_units;
    ClauseSet_p   processed_non_units;
    ClauseSet_p   unprocessed;
}BackupProofStateCell, *BackupProofState_p;

#define BackupProofStateCellAlloc() (BackupProofStateCell*)SizeMalloc(sizeof(BackupProofStateCell))
#define BackupProofStateCellFree(junk) SizeFree(junk, sizeof(BackupProofStateCell))

BackupProofState_p BackupProofstateAlloc(ProofState_p original);
void BackupProofStateFree(BackupProofState_p junk);

long BacktrackProofState(ProofState_p proofstate,
                         ProofControl_p proofcontrol,
                         TableauControl_p tableaucontrol,
                         BackupProofState_p backup);


#endif
