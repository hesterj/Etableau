#include <etableau.h>
#include <cco_scheduling.h>
#include <omp.h>

// Forward declaration

int process_saturation_output(TableauControl_p tableau_control,
										pid_t *pool, 
										int *return_status, 
										ClauseTableau_p *branches, 
										int num_open_branches);
void process_branch(ProofState_p proofstate, 
						  ProofControl_p proofcontrol, 
						  pid_t *pool, 
						  int *return_status, 
						  ClauseTableau_p *branches, 
						  int i);

// Function definitions 

BranchSaturation_p BranchSaturationAlloc(ProofState_p proofstate, ProofControl_p proofcontrol, ClauseTableau_p master)
{
	BranchSaturation_p branch_sat = BranchSaturationCellAlloc();
	branch_sat->proofstate = proofstate;
	branch_sat->proofcontrol = proofcontrol;
	branch_sat->master = master;
	return branch_sat;
}

void BranchSaturationFree(BranchSaturation_p branch_sat)
{
	BranchSaturationCellFree(branch_sat);
}

void process_branch(ProofState_p proofstate, 
						  ProofControl_p proofcontrol, 
						  pid_t *pool, 
						  int *return_status, 
						  ClauseTableau_p *branches, 
						  int i)
{
	pid_t worker = fork();
	if (worker == 0) // We are in the child process 
	{
		ClauseTableau_p branch = branches[i];
		assert(branches[i]);
		SilentTimeOut = true;
		//int branch_status = ECloseBranch(proofstate, proofcontrol, branch);
		int branch_status = ECloseBranchProcessBranchFirst(proofstate, proofcontrol, branch);
		//~ #ifndef DNDEBUG
		//~ fprintf(GlobalOut, "# FORK FINAL REPORT %ld processed clauses, branch_status %d, branch %p\n", ProofStateProcCardinality(proofstate), branch_status, branch);
		//~ #endif
		exit(branch_status);
	}
	else if (worker > 0)  // parent process
	{
		pool[i] = worker;
		return_status[i] = RESOURCE_OUT;
	}
	else 
	{
		Error("Fork failure", 1);
	}
}

int ECloseBranchProcessBranchFirst(ProofState_p proofstate, ProofControl_p proofcontrol, 
					  ClauseTableau_p branch)
{
	Clause_p success = NULL;
	ClauseTableau_p node = branch;
	assert(proofstate);
	assert(proofcontrol);
	//long proc_limit = 500;
	
	// Collect the clauses of the branch
	
	while (node)
	{
		if (node != node->master)
		{
			Clause_p label = node->label;
			assert(!label->set);
			assert(!label->evaluations);
			ClauseSetProp(label, CPInitial);
			success = ProcessSpecificClause(proofstate, proofcontrol, label, LONG_MAX);
			if (success)
			{
				//fprintf(GlobalOut, "# Saturate returned empty clause on branch.\n");
				//ProofStateStatisticsPrint(GlobalOut, proofstate);
				return PROOF_FOUND;
			}
		}
		if (node->folding_labels) // Process the folding labels, if there are any
		{
			ClauseSetSetProp(node->folding_labels, CPInitial);
			//printf("# Folded up clauses:\n");
			//ClauseSetPrint(GlobalOut, node->folding_labels, true);printf("\n");
			while (!ClauseSetEmpty(node->folding_labels))
			{
				Clause_p fold_label = ClauseSetExtractFirst(node->folding_labels);
				success = ProcessSpecificClause(proofstate, 
														  proofcontrol, 
														  fold_label, 
														  LONG_MAX);
				if (success)
				{
					fprintf(GlobalOut, "# Saturate returned empty clause on folds.\n");
					//ProofStateStatisticsPrint(GlobalOut, proofstate);
					return PROOF_FOUND;
				}
			}
		}
		if (node->unit_axioms) // Process the units, if there are any
		{
			ClauseSetSetProp(node->unit_axioms, CPInitial);
			while (!ClauseSetEmpty(node->unit_axioms))
			{
				Clause_p unit = ClauseSetExtractFirst(node->unit_axioms);
				success = ProcessSpecificClause(proofstate, 
														  proofcontrol, 
														  unit, 
														  LONG_MAX);
				if (success)
				{
					fprintf(GlobalOut, "# Saturate returned empty clause on units.\n");
					//ProofStateStatisticsPrint(GlobalOut, proofstate);
					return PROOF_FOUND;
				}
			}
		}
		node = node->parent;
	}
	
	// Now do normal saturation
	success = Saturate(proofstate, proofcontrol, 1000,
							 LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
							 LLONG_MAX, LONG_MAX);
	if (success)
	{
		//fprintf(GlobalOut, "# Saturate returned empty clause %p.\n", success);
		//ProofStateStatisticsPrint(GlobalOut, proofstate);
		return PROOF_FOUND;
	}
	
	//~ fprintf(GlobalOut, "# Surrendering\n");
	return RESOURCE_OUT;
}

int AttemptToCloseBranchesWithSuperposition(TableauControl_p tableau_control, BranchSaturation_p jobs)
{
	ProofState_p proofstate = jobs->proofstate;
	ProofControl_p proofcontrol = jobs->proofcontrol;
	ClauseTableau_p master = jobs->master;
	TableauSet_p open_branches = master->open_branches;
	
	int num_open_branches = (int) open_branches->members;
	
	// Collect the local branches in an array
	pid_t pool[num_open_branches];  // Uninitialized array
	int return_status[num_open_branches]; // Uninitialized array
	ClauseTableau_p branches[num_open_branches]; // Uninitialized array
	// Initialize the arrays: We are only interested in local branches
	ClauseTableau_p handle = open_branches->anchor->succ;
	int num_local_branches = 0;
	for (int i=0; i<num_open_branches; i++)
	{
		assert(handle != master->open_branches->anchor);
		if (BranchIsLocal(handle))
		{
			num_local_branches++;
			branches[i] = handle;
			pool[i] = 0;
			return_status[i] = RESOURCE_OUT;
		}
		else 
		{
			branches[i] = NULL;
			pool[i] = -1;
			return_status[i] = RESOURCE_OUT;
		}
		handle = handle->succ;
	}
	
	#pragma omp task
	{
		for (int i=0; i<num_open_branches; i++)
		{
			if (branches[i]) // Branch is local, so we will try to close it
			{
				process_branch(proofstate, proofcontrol, pool, return_status, branches, i);
			}
		}
		process_saturation_output(tableau_control, pool, return_status, branches, num_open_branches);
	}
	fflush(GlobalOut);
	// Exit and return to tableaux proof search
	return 0;
}

int process_saturation_output(TableauControl_p tableau_control,
										pid_t *pool, 
										int *return_status, 
										ClauseTableau_p *branches, 
										int num_open_branches)
{
	int raw_status = 0, status = OTHER_ERROR;
	int successful_count = 0;
	ClauseTableau_p closed_branch = NULL;
	for (int i=0; i<num_open_branches; i++)
	{
		pid_t respid = -1;
		while(respid == -1)
		{
			pid_t worker = pool[i];
			//fprintf(GlobalOut, "#");
			if (worker == -1) break;
			assert(branches[i]);
			respid = waitpid(worker, &raw_status, 0);
			if (WIFEXITED(raw_status))
         {
				//fprintf(GlobalOut, "# Fork %d dead, respid %d, status %d.\n", worker, respid, raw_status);
            status = WEXITSTATUS(raw_status);
            if (status == SATISFIABLE)
            {
					return_status[i] = SATISFIABLE;
					ClauseTableau_p satisfiable_branch = branches[i];
					fprintf(GlobalOut, "# Satisfiable branch!\n");
					tableau_control->closed_tableau = satisfiable_branch;
					tableau_control->satisfiable = true;
					successful_count++;
					return successful_count;
				}
            if (status == PROOF_FOUND)
            {
					proof_found:
					//fprintf(GlobalOut, "# Branch %d of %d detected with exit status %d, raw status %d\n", i, num_open_branches, status, raw_status);
					assert(respid);
					closed_branch = branches[i];
					TableauSetExtractEntry(closed_branch);
					closed_branch->open = false;
					closed_branch->saturation_closed = true;
					DStrAppendStr(closed_branch->info, "Saturation closed");
					return_status[i] = PROOF_FOUND;
					successful_count++;
					break;
            }
         }
         else if (WIFSIGNALED(raw_status))
         {
				Error("#%d %d Signalled termination\n", raw_status, respid);
			}
         else
         {
            Error("#%d %d Abnormal termination\n", raw_status, respid);
         }
		}
	}
	if (successful_count == num_open_branches)
	{
		fprintf(GlobalOut, "# All %d remaining open branches were closed with E.\n", successful_count);
		tableau_control->closed_tableau = closed_branch->master;
	}
	return successful_count;
}
