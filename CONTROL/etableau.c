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
		int branch_status = ECloseBranch(proofstate, proofcontrol, branch);
		//printf("%ld processed clauses, status %d, branch %p\n", ProofStateProcCardinality(proofstate), branch_status, branch);
		exit(branch_status);
	}
	else if (worker > 0)
	{
		pool[i] = worker;
		return_status[i] = RESOURCE_OUT;
	}
	else 
	{
		Error("Fork failure", 1);
	}
}

int ECloseBranch(ProofState_p proofstate, 
					  ProofControl_p proofcontrol, 
					  ClauseTableau_p branch)
{
	ClauseSet_p branch_clauses = ClauseSetAlloc();
	ClauseTableau_p node = branch;
	assert(proofstate);
	assert(proofcontrol);
	long proc_limit = 500;
	
	// Collect the clauses of the branch
	
	while (node)
	{
		if (node != node->master)
		{
			Clause_p label = node->label;
			label->weight = ClauseStandardWeight(label);
			ClauseSetIndexedInsertClause(branch_clauses, label);
		}
		if (node->folding_labels)
		{
			ClauseSetIndexedInsertClauseSet(branch_clauses, node->folding_labels);
		}
		node = node->parent;
	}
	
	// Switch the unprocessed set with branch_clauses, so that the branches are processed first
	
	ClauseSetSetProp(branch_clauses, CPInitial);
	ClauseSetSetProp(branch_clauses, CPLimitedRW);
	
	ClauseSet_p axioms = proofstate->axioms;
	ClauseSet_p unproc = proofstate->unprocessed;
	proofstate->axioms = branch_clauses;
	proofstate->unprocessed = ClauseSetAlloc();
	ProofStateInit(proofstate, proofcontrol);
	Clause_p success = Saturate(proofstate, proofcontrol, LONG_MAX,
							 LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
							 LLONG_MAX, LONG_MAX);
	if (success)
	{
		//fprintf(GlobalOut, "Superposition contradiction purely within branch!\n");
		return PROOF_FOUND;
	}
	// Undo the switching so that we can proceed with normal saturation
	assert(proofstate->unprocessed->members == 0);
	ClauseSetFree(proofstate->unprocessed);
	proofstate->axioms = axioms;
	proofstate->unprocessed = unproc;
	assert(proofstate->unprocessed);
	ClauseSetFree(branch_clauses);
	
	// Now do normal saturation
	success = Saturate(proofstate, proofcontrol, 1000,
							 LONG_MAX, LONG_MAX, LONG_MAX, LONG_MAX,
							 LLONG_MAX, LONG_MAX);
	if (success)
	{
		//fprintf(GlobalOut, "Saturate returned empty clause.\n");
		//ProofStateStatisticsPrint(GlobalOut, proofstate);
		return PROOF_FOUND;
	}
	//printf("Returning RESOURCE_OUT\n");
	//ProofStateStatisticsPrint(GlobalOut, proofstate);
	return RESOURCE_OUT;
}

int AttemptToCloseBranchesWithSuperposition(TableauControl_p tableau_control, BranchSaturation_p jobs)
{
	int num_threads = omp_get_num_threads();
	ProofState_p proofstate = jobs->proofstate;
	ProofControl_p proofcontrol = jobs->proofcontrol;
	ClauseTableau_p master = jobs->master;
	BranchSaturationFree(jobs);
	
	TableauSet_p open_branches = master->open_branches;
	int num_open_branches = (int) open_branches->members;
	pid_t pool[num_open_branches];
	int return_status[num_open_branches];
	
	// Collect the local branches in an array
	ClauseTableau_p handle = open_branches->anchor->succ;
	ClauseTableau_p branches[num_open_branches];
	for (int i=0; i<num_open_branches; i++)
	{
		assert(handle != master->open_branches->anchor);
		if (BranchIsLocal(handle)) branches[i] = handle;
		else 
		{
			branches[i] = NULL;
			pool[i] = -1;
			return_status[i] = RESOURCE_OUT;
		}
		handle = handle->succ;
	}
	
	int raw_status = 0, status = OTHER_ERROR;
	pid_t worker = 0, respid;

	fflush(GlobalOut);
	
	#pragma omp task
	{
		for (int i=0; i<num_open_branches; i++)
		{
			if (branches[i]) // Branch is local, so we will try to close it
			{
				process_branch(proofstate, proofcontrol, pool, return_status, branches, i);
			}
		}
		// Process any results
		#pragma omp taskwait
		process_saturation_output(tableau_control, pool, return_status, branches, num_open_branches);
	}
	
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
			if (worker == -1) break;
			assert(branches[i]);
			respid = waitpid(worker, &raw_status, 0);
			//printf("Fork %d dead, respid %d, status %d.\n", worker, respid, raw_status);
			if (WIFEXITED(raw_status))
         {
            status = WEXITSTATUS(raw_status);
            if (status == SATISFIABLE)
            {
					return_status[i] = SATISFIABLE;
					ClauseTableau_p satisfiable_branch = branches[i];
					tableau_control->closed_tableau = satisfiable_branch;
					tableau_control->satisfiable = true;
					successful_count++;
					return successful_count;
				}
            if (status == PROOF_FOUND)
            {
					//printf("Branch %d detected with signal PROOF_FOUND, %d\n", i, status);
					assert(respid);
					closed_branch = branches[i];
					TableauSetExtractEntry(closed_branch);
					closed_branch->open = false;
					closed_branch->saturation_closed = true;
					return_status[i] = PROOF_FOUND;
					successful_count++;
					break;
            }
            else
            {
					//printf("#%d", status);
               //fprintf(GlobalOut, "# No success with fork\n");
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
