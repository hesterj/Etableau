#include "etab_clausetableaux.h"

int clausesetallocs_counter = 1;  

// Functions for clausetableaux.h

/*  The open branches for each distinct tableau MUST be initialized on creation,
 *  not by this method.
 * 
 * 
*/

ClauseTableau_p ClauseTableauAlloc(TableauControl_p tableaucontrol)
{
	ClauseTableau_p handle = ClauseTableauCellAlloc();
	handle->tableaucontrol = tableaucontrol;
	handle->tableau_variables = NULL;
	handle->depth = 0;
	handle->position = 0;
	handle->arity = 0;
	handle->unit_axioms = NULL;
	handle->previously_saturated = 0;
	//handle->mark = NULL;
	handle->mark_int = 0;
	handle->folded_up = 0;
	handle->step = 0;
	handle->max_step = 0;
	handle->folding_labels = NULL;
	handle->set = NULL;
	handle->head_lit = false;
	handle->saturation_closed = false;
	handle->id = 0;
	handle->max_var = 0;
	handle->info = DStrAlloc();
	handle->active_branch = NULL;
	handle->pred = NULL;
	handle->control = NULL;
	handle->state = NULL;
	handle->succ = NULL;
	handle->local_variables = NULL;
	handle->open_branches = NULL;
	handle->children = NULL;
	handle->label = NULL;
	handle->master = handle;
	handle->parent = NULL;
	handle->open = true;
	
	return handle;
}

/*  This copies the master node of a tableau and its children,
 *  set up for use with method of connection tableaux.
 * 
*/

ClauseTableau_p ClauseTableauMasterCopy(ClauseTableau_p tab)
{
	assert(tab->master == tab);  // Masters have themselves as master
	TB_p bank = tab->terms;
	ClauseTableau_p handle = ClauseTableauCellAlloc();

	GCAdmin_p gc = tab->state->gc_terms;
	ClauseSet_p label_storage = tab->tableaucontrol->label_storage;
	handle->tableaucontrol = tab->tableaucontrol;
	handle->tableau_variables = NULL;
	handle->arity = tab->arity;
	handle->previously_saturated = tab->previously_saturated;
	
	char *info = DStrCopy(tab->info);
	handle->info = DStrAlloc();
	DStrAppendStr(handle->info, info);
	FREE(info);
	
	handle->depth = tab->depth;
	handle->position = tab->position;
	assert(handle->depth == 0);
	
	// Do NOT copy the unit axioms because there may be a subst active!!
	handle->unit_axioms = NULL;
	handle->set = NULL;
	handle->pred = NULL;
	handle->id = tab->id;
	handle->mark_int = tab->mark_int;
	handle->step = tab->step;
	handle->max_step = tab->max_step;
	handle->folded_up = tab->folded_up;
	assert(handle->folded_up == 0); // the master node should not be folded up
	if (tab->folding_labels)
	{
		handle->folding_labels = ClauseSetCopy(bank, tab->folding_labels);
		GCRegisterClauseSet(gc, handle->folding_labels);
	}
	else
	{
		handle->folding_labels = NULL;
	}
	handle->head_lit = tab->head_lit;
	handle->succ = NULL;
	handle->active_branch = NULL;
	handle->saturation_closed = tab->saturation_closed;
	handle->max_var = tab->max_var;
	handle->open_branches = TableauSetAlloc();
	handle->terms = tab->terms;
	handle->control = tab->control;
	handle->state = tab->state;
	handle->local_variables = NULL;
	
	if (tab->label)
	{
		//handle->label = ClauseCopy(tab->label, bank);
		handle->label = ClauseCopy(tab->label, bank);
		assert(handle->label);
		ClauseSetInsert(label_storage, handle->label);
	}
	else 
	{
		handle->label = NULL;
	}
	handle->master = handle;
	handle->parent = NULL;
	
	if (tab->arity == 0) // tab does not have children
	{
		//assert(0);
		handle->open = true;
		//TableauSetInsert(handle->open_branches, handle);
	}
	else
	{
		handle->open = tab->open;
	}
	
	if (tab->arity)
	{
		handle->children = ClauseTableauArgArrayAlloc(tab->arity);
		for (int i=0; i<tab->arity; i++)
		{
			handle->children[i] = ClauseTableauChildCopy(tab->children[i], handle);
		}
	}
	else 
	{
		handle->children = NULL;
	}
	return handle;
}

ClauseTableau_p ClauseTableauChildCopy(ClauseTableau_p tab, ClauseTableau_p parent)
{
	assert(tab);
	assert(parent);
	TB_p bank = tab->terms; //Copy tableau tab
	ClauseTableau_p handle = ClauseTableauCellAlloc();
	handle->tableaucontrol = NULL;
	handle->tableau_variables = NULL;
	handle->unit_axioms = NULL;
	GCAdmin_p gc = tab->state->gc_terms;
	ClauseSet_p label_storage = parent->master->tableaucontrol->label_storage;
	
	char *info = DStrCopy(tab->info);
	handle->info = DStrAlloc();
	DStrAppendStr(handle->info, info);
	FREE(info);
	
	handle->open_branches = parent->open_branches;
	handle->control = parent->control;
	handle->set = NULL;
	handle->previously_saturated = tab->previously_saturated;
	handle->id = tab->id;
	handle->step = tab->step;
	handle->max_step = tab->max_step;
	handle->head_lit = tab->head_lit;
	handle->max_var = parent->max_var;
	handle->active_branch = NULL;
	handle->signature = parent->signature;
	handle->terms = parent->terms;
	handle->mark_int = tab->mark_int;
	handle->folded_up = tab->folded_up;
	handle->saturation_closed = tab->saturation_closed;
	handle->parent = parent;
	handle->master = parent->master;
	handle->depth = 1+parent->depth;
	handle->position = tab->position;
	assert(handle->depth > 0);
	assert((handle->depth == parent->depth + 1));
	handle->state = parent->state;
	handle->open = tab->open;
	handle->arity = tab->arity;
	handle->local_variables = NULL;
	if (tab->folding_labels)
	{
		handle->folding_labels = ClauseSetCopy(bank, tab->folding_labels);
		GCRegisterClauseSet(gc, handle->folding_labels);
	}
	else
	{
		handle->folding_labels = NULL;
	}
	if (tab->master->active_branch == tab)
	{
		handle->master->active_branch = handle;
		assert(handle->arity == 0);
	}
	
	if (tab->label)
	{
		//handle->label = ClauseCopy(tab->label, handle->terms);
		assert(tab->label);
		handle->label = ClauseCopy(tab->label, bank);
		assert(handle->label);
		ClauseSetInsert(label_storage, handle->label);
	}
	else
	{
		tab->label = NULL;
	}
	if ((handle->arity == 0) && (handle->open)) // If one of the open branches is found during copying, add it to the collection of open branches
	{
		TableauSetInsert(handle->open_branches, handle);
	}
	
	if (tab->arity)
	{
		handle->children = ClauseTableauArgArrayAlloc(tab->arity);
		
		for (int i=0; i<tab->arity; i++)
		{
			handle->children[i] = ClauseTableauChildCopy(tab->children[i], handle);
		}
	}
	else 
	{
		handle->children = NULL;
	}
	
	return handle;
}

void ClauseTableauInitialize(ClauseTableau_p handle, ProofState_p initial)
{
	handle->signature = initial->signature;
	handle->state = initial;
	handle->terms = initial->terms;
}


ClauseTableau_p ClauseTableauChildLabelAlloc(ClauseTableau_p parent, Clause_p label, int position)
{
	ClauseTableau_p handle = ClauseTableauCellAlloc();
	GCAdmin_p gc = parent->state->gc_terms;
	ClauseSet_p label_storage = parent->master->tableaucontrol->label_storage;
	ClauseSetInsert(label_storage, label); // For gc
	handle->tableaucontrol = NULL;
	handle->tableau_variables = NULL;
	assert(parent);
	assert(label);
	parent->arity += 1;
	handle->step = -1;
	handle->max_step = 0;
	handle->depth = parent->depth + 1;
	handle->position = position;
	handle->previously_saturated = 0;
	handle->unit_axioms = NULL;
	handle->open_branches = parent->open_branches;
	handle->label = label;
	handle->id = 0;
	handle->head_lit = false;
	handle->local_variables = NULL;
	handle->control = parent->control;
	handle->max_var = parent->max_var;
	handle->set = NULL;
	handle->mark_int = 0;
	handle->folded_up = 0;
	handle->folding_labels = NULL;
	handle->info = DStrAlloc();
	handle->active_branch = NULL;
	handle->pred = NULL;
	handle->succ = NULL;
	handle->signature = parent->signature;
	handle->children = NULL;
	handle->terms = parent->terms;
	handle->parent = parent;
	handle->master = parent->master;
	handle->state = parent->state;
	handle->open = true;
	handle->arity = 0;
	handle->saturation_closed = false;
	return handle;
}

/*  Sets the relevant fields to NULL after free'ing
*/

void ClauseTableauFree(ClauseTableau_p trash)
{
	GCAdmin_p gc = trash->state->gc_terms;
	if (trash->depth == 0 && trash->tableau_variables)
	{
		//PStackFree(trash->derivation);
		PTreeFree(trash->tableau_variables);
	}
	if (trash->label)
	{
		assert(trash->label->set);
		ClauseSetExtractEntry(trash->label);
		ClauseFree(trash->label);
		trash->label = NULL;
	}
	if (trash->depth == 0 && trash->unit_axioms) //unit axioms are only at the master node
	{
		ClauseSetFree(trash->unit_axioms);
	}
	if (trash->local_variables)
	{
		PStackFree(trash->local_variables);
	}
	if (trash->folding_labels)
	{
		GCDeregisterClauseSet(gc, trash->folding_labels);
		ClauseSetFree(trash->folding_labels);
	}
	if (trash->children)
	{
		for (int i=0; i<trash->arity; i++)
		{
			ClauseTableauFree(trash->children[i]);
		}
		ClauseTableauArgArrayFree(trash->children, trash->arity);
	}
	if (trash->depth == 0)
	{
		TableauSetFree(trash->open_branches);
	}
	DStrFree(trash->info);
	ClauseTableauCellFree(trash);
}

void TableauStackFreeTableaux(PStack_p stack)
{
	while (!PStackEmpty(stack))
	{
		//printf("f");
		//fflush(stdout);
		ClauseTableau_p tab = PStackPopP(stack);
		assert(tab == tab->master);
		ClauseTableauFree(tab);
	}
}

void HCBClauseSetEvaluate(HCB_p hcb, ClauseSet_p clauses)
{
	Clause_p handle = clauses->anchor->succ;
	while (handle != clauses-> anchor)
	{
		HCBClauseEvaluate(hcb, handle);
		handle = handle->succ;
	}
}

/*  Apply subst to the entire tableau
*/

void ClauseTableauApplySubstitution(ClauseTableau_p tab, Subst_p subst)
{
	if (PStackGetSP(subst) == 0)
	{
		return;
	}
	
	ClauseTableau_p master = tab->master;
	ClauseTableauApplySubstitutionToNode(master, subst);
}

FunCode ClauseSetGetMaxVar(ClauseSet_p set)
{
	FunCode max_funcode = 0;
	Clause_p start_label = set->anchor->succ;
   PStack_p start_subterms = PStackAlloc();
   PTree_p tree = NULL;
   while (start_label != set->anchor)
   {
		ClauseCollectVariables(start_label, &tree);
		//ClauseCollectSubterms(start_label, start_subterms);
		start_label = start_label->succ;
	}
	PTreeToPStack(start_subterms, tree);
	//printf("%ld subterms found", PStackGetSP(start_subterms));
	Term_p temp_term = NULL;
	for (PStackPointer p = 0; p<PStackGetSP(start_subterms); p++)
	{
		temp_term = PStackElementP(start_subterms, p);
		//printf("tmp term fcode %ld ", temp_term->f_code);
		if (TermIsVar(temp_term))
		{
			FunCode var_funcode = temp_term->f_code;
			//printf("%ld ", var_funcode);
			if (var_funcode <= max_funcode)
			{
				max_funcode = var_funcode;
			}
		}
	}
	//printf("\n");
	PTreeFree(tree);
	PStackFree(start_subterms);
	if (max_funcode == 0)
	{
		return -2;
	}
	//printf("max_funcode: %ld\n", max_funcode);
	return max_funcode;
}

/*  Recursively apply subst to the clauses in tab, and tab's children
*/

void ClauseTableauApplySubstitutionToNode(ClauseTableau_p tab, Subst_p subst)
{
	GCAdmin_p gc = tab->state->gc_terms;
	assert(tab->label);
	assert(subst);
	ClauseSet_p label_storage = tab->master->tableaucontrol->label_storage;
	Clause_p new_label = ClauseCopy(tab->label, tab->terms);
	ClauseSetExtractEntry(tab->label);
	ClauseSetInsert(label_storage, new_label);
	ClauseFree(tab->label);
	assert(new_label);
	tab->label = new_label;
	
	if (tab->folding_labels)  // The edge labels that have been folded up if the pointer is non-NULL
	{
		ClauseSet_p new_edge = ClauseSetCopy(tab->terms, tab->folding_labels);
		GCDeregisterClauseSet(gc, tab->folding_labels);
		ClauseSetFree(tab->folding_labels);
		GCRegisterClauseSet(gc, new_edge);
		assert(new_edge);
		tab->folding_labels = new_edge;
	}
	
	for (int i=0; i<tab->arity; i++)
	{
		ClauseTableauApplySubstitutionToNode(tab->children[i], subst);
	}
}

Subst_p ClauseContradictsClause(ClauseTableau_p tab, Clause_p a, Clause_p b)
{
	assert (tab && a && b);
	if (a==b) return NULL;  // Easy case...
	if (!ClauseIsUnit(a) || !ClauseIsUnit(b)) return NULL;
	Eqn_p a_eqn = a->literals;
	Eqn_p b_eqn = b->literals;
	
	if (EqnIsPositive(a_eqn) && EqnIsPositive(b_eqn)) return NULL;
	if (EqnIsNegative(a_eqn) && EqnIsNegative(b_eqn)) return NULL;
	
	Subst_p subst = SubstAlloc();
	
	if (EqnUnify(a_eqn, b_eqn, subst))
	{
		return subst;
	}
	
	SubstDelete(subst);
	
	return NULL;
}

Subst_p ClauseContradictsClauseSubst(Clause_p a, Clause_p b, Subst_p subst)
{
	assert (a && b);
	if (a==b) return NULL;  // Easy case...
	//if (!ClauseIsUnit(a) || !ClauseIsUnit(b)) return 0;  // Should not happen
	Eqn_p a_eqn = a->literals;
	Eqn_p b_eqn = b->literals;
	assert(a_eqn);
	assert(b_eqn);
	bool success = false;
	
	if (EqnIsPositive(a_eqn) && EqnIsPositive(b_eqn)) return NULL;
	if (EqnIsNegative(a_eqn) && EqnIsNegative(b_eqn)) return NULL;
	
	if ((success = EqnUnify(a_eqn, b_eqn, subst)))
	{
		//for (PStackPointer p = 0; p < PStackGetSP(subst); p++)
		//{
			//Term_p var = PStackElementP(subst, p); 
			//Type_p var_type = var->type;
			//Term_p binding = var->binding;
			//Type_p bind_type = binding->type;
			//assert(var_type == bind_type);
		//}
		return subst;
	}
	
	return NULL;
}

ClauseSet_p ClauseSetCopy(TB_p bank, ClauseSet_p set)
{
	Clause_p handle, temp;
	assert(set);
	ClauseSet_p new = ClauseSetAlloc();
	for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
	{
		assert(handle);
		//temp = ClauseCopy(handle,bank);
		temp = ClauseCopy(handle, bank);
		ClauseSetInsert(new, temp);
	}
	return new;
}

ClauseSet_p ClauseSetFlatCopy(TB_p bank, ClauseSet_p set)
{
	Clause_p handle, temp;
	assert(set);
	ClauseSet_p new = ClauseSetAlloc();
	for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
	{
		assert(handle);
		temp = ClauseFlatCopy(handle);
		ClauseSetInsert(new, temp);
	}
	return new;
}

/*
*/

ClauseSet_p ClauseSetApplySubstitution(TB_p bank, ClauseSet_p set, Subst_p subst)
{
	Clause_p handle, temp;
	ClauseSet_p new = ClauseSetAlloc();
	
	for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
	{
		temp = ClauseCopy(handle, bank);
		ClauseSetInsert(new, temp);
	}
	return new;
}

/* Should only be called on closed tableau, as in order to collect the leaves, open branches
 *  must be removed from their tableau set.
*/

void ClauseTableauPrint(ClauseTableau_p tab)
{
	assert(tab);
	if (tab == NULL) Error("# Error:  Attempting to print NULL tableau", 1);
	PStack_p leaves = PStackAlloc();
	ClauseTableauCollectLeavesStack(tab, leaves);
	for (PStackPointer p = 0; p<PStackGetSP(leaves); p++)
	{
		ClauseTableau_p handle = PStackElementP(leaves, p);
		ClauseTableauPrintBranch(handle);printf("\n");
	}
	PStackFree(leaves);
}

void ClauseTableauPrint2(ClauseTableau_p tab)
{
	PStack_p leaves = PStackAlloc();
	ClauseTableauCollectLeavesStack(tab, leaves);
	for (PStackPointer p = 0; p<PStackGetSP(leaves); p++)
	{
		ClauseTableau_p handle = PStackElementP(leaves, p);
		ClauseTableauPrintBranch2(handle);printf("\n");
	}
	PStackFree(leaves);
}

/*  Checks to see if the node dominates tab, properly.
 *  i/e if they are the same, return false;
 * 
*/

bool TableauDominatesNode(ClauseTableau_p tab, ClauseTableau_p node)
{
	if (tab == node) return false;
	ClauseTableau_p climber = node->parent;
	while (climber)
	{
		if (climber == tab) return true;
		climber = climber->parent;
	}
	return false;
}

/*  Only call on closed tableau.  Collects the leaves (no children nodes).
 * 
*/

void ClauseTableauCollectLeaves(ClauseTableau_p tab, TableauSet_p leaves)
{
	if (tab->arity == 0) // found a leaf
	{
		assert(!tab->set);
		TableauSetInsert(leaves, tab);
	}
	for (int i=0; i<tab->arity; i++)
	{
		ClauseTableauCollectLeaves(tab->children[i], leaves);
	}
}

/*  
 * Collects the leaves below a tableau node
*/

void ClauseTableauCollectLeavesStack(ClauseTableau_p tab, PStack_p leaves)
{
	if (tab->arity == 0) // found a leaf
	{
		PStackPushP(leaves, tab);
	}
	for (int i=0; i<tab->arity; i++)
	{
		ClauseTableauCollectLeavesStack(tab->children[i], leaves);
	}
}

void ClauseTableauPrintBranch(ClauseTableau_p branch)
{
	ClauseTableau_p depth_check = branch;
	assert(depth_check);
	//printf("\033[1;33m");
	while (depth_check->depth != 0)
	{
		assert(depth_check->label);
		assert(depth_check->id >= 0);
		fprintf(stdout, "# %d,%d,%ld,%d, step: %d ", depth_check->depth,depth_check->arity, depth_check->id,depth_check->mark_int, depth_check->step);
		fprintf(stdout, "%s", DStrView(depth_check->info));
		if (depth_check->head_lit)
		{
			fprintf(stdout, " x");
		}
		if (!depth_check->open)
		{
			fprintf(stdout, " c");
		}
		if (depth_check->saturation_closed)
		{
			fprintf(stdout, " s");
		}
		fprintf(stdout, "\n");
		ClausePrint(stdout, depth_check->label, true);
		
		fprintf(stdout, "\n");
		depth_check = depth_check->parent;
	}
	assert (depth_check->depth == 0);
	assert (depth_check->label);
	
	fprintf(stdout, "# %d,%d,%ld,%d \n", depth_check->depth,depth_check->arity, depth_check->id,depth_check->mark_int);
	ClausePrint(stdout, depth_check->label, true);
	fprintf(stdout, "\n");
	//printf("\033[0m");
}

void ClauseTableauPrintBranch2(ClauseTableau_p branch)
{
	ClauseTableau_p depth_check = branch;
	assert(depth_check);
	//printf("\033[1;33m");
	while (depth_check->depth != 0)
	{
		assert(depth_check->label);
		assert(depth_check->id >= 0);
		printf("# Depth: %d, Arity: %d, Id: %ld, Mark: %d\n", depth_check->depth,depth_check->arity, depth_check->id,depth_check->mark_int);
		printf("# Properties:");
		if (depth_check->head_lit)
		{
			printf(" Head literal.");
		}
		if (depth_check->saturation_closed)
		{
			printf(" Closed by saturation.");
		}
		else if (!depth_check->open)
		{
			printf(" Closed by extension or closure.");
		}
		printf("\n");
		ClausePrint(GlobalOut, depth_check->label, true);
		
		printf("\n");
		depth_check = depth_check->parent;
	}
	assert (depth_check->depth == 0);
	assert (depth_check->label);
	
	printf("# Depth: %d, Arity: %d, Id: %ld, Mark: %d\n", depth_check->depth,depth_check->arity, depth_check->id,depth_check->mark_int);
	printf("# Root.\n");
	ClausePrint(GlobalOut, depth_check->label, true);
	printf("\n");
	//printf("\033[0m");
}

Clause_p ClauseApplySubst(Clause_p clause,  TB_p bank, Subst_p subst)
{
   Clause_p new_clause;
   Term_p variable_in_clause __attribute__((unused));
   assert(clause);
   new_clause = ClauseCopy(clause, bank);
   return new_clause;
}

/*-----------------------------------------------------------------------
//
// Function: ClauseCopyFresh()
//
//   Create a variable-fresh copy of clause.  Every variable that is 
//   in the clause is replaced with a fresh one.  variable_subst is the address of the 
//   substitution replacing the old variables with new ones.  Must be free'd afterwards!
//
//	John Hester
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

Clause_p ClauseCopyFresh(Clause_p clause, ClauseTableau_p tableau)
{
	assert(tableau);
	assert(tableau->master);
	assert(tableau->master->terms);
	assert(tableau->master->terms->vars);
   PTree_p variable_tree = NULL;
   PStack_p variables;
   PStackPointer p;
   Subst_p subst;
   Term_p old_var, fresh_var;
   Clause_p handle;
   // VarBank_p variable_bank = tableau->master->terms->vars;
   
   assert(clause);
   
   variables = PStackAlloc();
   //VarBankSetVCountsToUsed(variable_bank);
   subst = SubstAlloc();
   
   ClauseCollectVariables(clause, &variable_tree);
   PTreeToPStack(variables, variable_tree);
   PTreeFree(variable_tree);
   
   //printf("Clause being copied: ");ClausePrint(GlobalOut, clause, true);printf("\n");
   
   for (p = 0; p < PStackGetSP(variables); p++)
   {
	   old_var = PStackElementP(variables, p);
	   fresh_var = ClauseTableauGetFreshVar(tableau->master, old_var); // new
	   assert(fresh_var != old_var);
	   assert(fresh_var->f_code != old_var->f_code);
	   if (fresh_var->f_code == old_var->f_code)
	   {
			printf("Clause copy fresh error\n");
			exit(0);
		}
	   SubstAddBinding(subst, old_var, fresh_var);
	   //printf("The subst: %ld %ld\n", fresh_var->f_code, old_var->f_code);
	   //SubstPrint(GlobalOut, subst, tableau->terms->sig, DEREF_NEVER);
	   //printf("\n");
   }
   
   handle = ClauseCopy(clause, tableau->terms);
   
   SubstDelete(subst);
   PStackFree(variables);

   return handle;
}

ClauseTableau_p TableauStartRule(ClauseTableau_p tab, Clause_p start)
{
	Eqn_p literals, lit;
	TB_p bank = tab->terms;
	int arity = 0;
	Clause_p new_clause;
	ClauseSet_p tableau_label_storage = tab->tableaucontrol->label_storage;
	assert(!(tab->label));
	assert(!(tab->arity));
	assert(start);
	assert(tab->state);
	assert(tab->control);
	
	arity = ClauseLiteralNumber(start);
	tab->open = true;
	//TableauSetExtractEntry(tab); // no longer open
	assert(!(tab->set));
	assert(tab->open_branches->members == 0);
	tab->label = ClauseCopy(start, tab->terms);
	ClauseSetInsert(tableau_label_storage, tab->label);
	assert(tab->label);
	
	tab->id = ClauseGetIdent(tab->label);
	DStrAppendStr(tab->info, " Start rule");
	
	assert(arity > 0);
	
	tab->children = ClauseTableauArgArrayAlloc(arity);
	literals = EqnListCopy(start->literals, bank);
	for (int i=0; i<arity; i++)
	{
		lit = EqnListExtractFirst(&literals);
		new_clause = ClauseAlloc(lit);
		ClauseRecomputeLitCounts(new_clause);
		tab->children[i] = ClauseTableauChildLabelAlloc(tab, new_clause, i);
		assert(tab->children[i]);
		assert(tab->children[i]->label);
		assert(tab->children[i]->label->set);
		TableauSetInsert(tab->children[i]->open_branches, tab->children[i]);
	}
	EqnListFree(literals);
	
	return tab;
}

// The number of steps up one must go to reach higher from lower, if they are in the same branch.

int ClauseTableauDifference(ClauseTableau_p higher, ClauseTableau_p lower)
{
	return (lower->depth - higher->depth);
}

/*  Creates the symmetry, reflexivity, and transitivity equality axioms.
 *  These are needed in clausal tableaux calculus for problems with equality.
 *  Clausified, they are 4 axioms.
 * 
*/

ClauseSet_p EqualityAxioms(TB_p bank)
{
	//Clause_p symmetry
	Type_p i_type = bank->sig->type_bank->i_type;
	//~ Term_p x = VarBankVarAssertAlloc(bank->vars, -2, i_type);
	//~ Term_p y = VarBankVarAssertAlloc(bank->vars, -4, i_type);
	//~ Term_p z = VarBankVarAssertAlloc(bank->vars, -6, i_type);
	Term_p x = VarBankGetFreshVar(bank->vars, i_type);
	Term_p y = VarBankGetFreshVar(bank->vars, i_type);
	Term_p z = VarBankGetFreshVar(bank->vars, i_type);
	//VarBankSetVCountsToUsed(bank->vars);
	
	ClauseSet_p equality_axioms = ClauseSetAlloc();
	
	Eqn_p x_equals_x = EqnAlloc(x, x, bank, true);
	Clause_p clause1 = ClauseAlloc(x_equals_x);
	ClauseRecomputeLitCounts(clause1);
	//printf("clause 1: %d\n", ClauseLiteralNumber(clause1));
	//ClausePrint(GlobalOut, clause1, true);
	ClauseSetInsert(equality_axioms, clause1);
	
	Eqn_p y_equals_x = EqnAlloc(y, x, bank, true);
	Eqn_p x_neq_y = EqnAlloc(x, y, bank, false);
	EqnListAppend(&y_equals_x, x_neq_y);
	Clause_p clause2 = ClauseAlloc(y_equals_x);
	ClauseRecomputeLitCounts(clause2);
	//printf("clause 2: %d\n", ClauseLiteralNumber(clause2));
	//ClausePrint(GlobalOut, clause2, true);
	ClauseSetInsert(equality_axioms, clause2);
	
	Eqn_p x_equals_y = EqnAlloc(x, y, bank, true);
	Eqn_p y_neq_x = EqnAlloc(y, x, bank, false);
	EqnListAppend(&x_equals_y, y_neq_x);
	Clause_p clause3 = ClauseAlloc(x_equals_y);
	ClauseRecomputeLitCounts(clause2);
	//printf("clause 3: %d\n", ClauseLiteralNumber(clause3));
	//ClausePrint(GlobalOut, clause3, true);
	ClauseSetInsert(equality_axioms, clause3);
	
	Eqn_p x_equals_z = EqnAlloc(x, z, bank, true);
	x_neq_y = EqnAlloc(x, y, bank, false);
	Eqn_p y_neq_z = EqnAlloc(y, z, bank, false);
	EqnListAppend(&x_equals_z, x_neq_y);
	EqnListAppend(&x_equals_z, y_neq_z);
	Clause_p clause4 = ClauseAlloc(x_equals_z);
	ClauseRecomputeLitCounts(clause4);
	//printf("clause 4: %d\n", ClauseLiteralNumber(clause4));
	//ClausePrint(GlobalOut, clause4, true);
	ClauseSetInsert(equality_axioms, clause4);
	
	return equality_axioms;
}

// Goes through the children to tableau to ensure that all of the nodes have labels
// returns number of nodes checked

int ClauseTableauAssertCheck(ClauseTableau_p tab)
{
	int num_nodes = 0;
	assert(tab->label);
	if (tab->parent)
	{
		assert(tab->depth > 0);
	}
	for (int i=0; i<tab->arity; i++)
	{
		assert(tab->children[i]);
		assert(tab->children[i]->depth == tab->depth + 1);
		num_nodes += ClauseTableauAssertCheck(tab->children[i]);
	}
	return num_nodes;
}

TableauSet_p TableauSetAlloc()
{
   TableauSet_p set = TableauSetCellAlloc();

   set->members = 0;
   //set->anchor  = ClauseTableauAlloc();
   set->anchor = ClauseTableauCellAlloc();
   set->anchor->label = NULL;
   set->anchor->succ = set->anchor;
   set->anchor->pred = set->anchor;

   return set;
}

TableauSet_p TableauSetCopy(TableauSet_p set)
{
	return NULL;
}

void TableauSetInsert(TableauSet_p set, ClauseTableau_p tab)
{
   assert(set);
   assert(tab);
   assert(!tab->set);

   tab->succ = set->anchor;
   tab->pred = set->anchor->pred;
   set->anchor->pred->succ = tab;
   set->anchor->pred = tab;
   tab->set = set;
   set->members++;
}

ClauseTableau_p TableauSetExtractEntry(ClauseTableau_p fset)
{
   assert(fset);
   assert(fset->set);

   fset->pred->succ = fset->succ;
   fset->succ->pred = fset->pred;
   fset->set->members--;
   fset->set = NULL;
   fset->succ = NULL;
   fset->pred = NULL;

   return fset;
}

ClauseTableau_p   TableauSetExtractFirst(TableauSet_p list)
{
   assert(list);

   if(TableauSetEmpty(list))
   {
      return NULL;
   }
   return TableauSetExtractEntry(list->anchor->succ);
}

/*  Don't actually free the members of set- this must have already been free'd
 * 
 * 
*/

void TableauSetFree(TableauSet_p set)
{
	ClauseTableauCellFree(set->anchor);
	TableauSetCellFree(set);
}

/*  Empty the set "from" and push all its members to "to"
*/

void TableauSetDrainToStack(PStack_p to, TableauSet_p from)
{
	while (!TableauSetEmpty(from))
	{
		PStackPushP(to, TableauSetExtractFirst(from));
	}
}

void TableauStackDrainToSet(TableauSet_p to, PStack_p from)
{
	while (!PStackEmpty(from))
	{
		ClauseTableau_p handle = PStackPopP(from);
		TableauSetInsert(to, handle);
	}
}

void TableauSetMoveClauses(TableauSet_p to, TableauSet_p from)
{
	while (!TableauSetEmpty(from))
	{
		ClauseTableau_p handle = TableauSetExtractFirst(from);
		TableauSetInsert(to, handle);
	}
}

void ClauseTableauPrintDOTGraph(ClauseTableau_p tab)
{
	FILE *dotgraph = fopen("/home/hesterj/Projects/APRTESTING/DOT/graph.dot", "w");
	ClauseTableauPrintDOTGraphToFile(dotgraph, tab);
	fclose(dotgraph);
}

void ClauseTableauPrintDOTGraphToFile(FILE* dotgraph, ClauseTableau_p tab)
{
	if (dotgraph == NULL)
	{
		printf("# Failed to print DOT graph, continuing\n");
		return;
	}
	else
	{
		printf("# Printing DOT graph to specified file\n");
	}
	
	Clause_p root_label = tab->label;
	assert(root_label);
	long root_id = ClauseGetIdent(root_label);
	// any folded up clauses here?
	int folds = 0;
	if (tab->folding_labels) folds = tab->folding_labels->members;
	
	fprintf(dotgraph, "digraph aprgraph {\n");
	
	fprintf(dotgraph,"   %ld [color=Green, label=\"", root_id);
	ClauseTSTPCorePrint(dotgraph, root_label, true);
	if (tab->folding_labels)
	{
		Clause_p handle = tab->folding_labels->anchor->succ;
		while (handle != tab->folding_labels->anchor) 
		{
			fprintf(dotgraph, "\n");
			ClauseTSTPCorePrint(dotgraph, handle, true);
			handle = handle->succ;
		}
	}
	fprintf(dotgraph, " %d\"]\n", folds);
	
	for (int i=0; i < tab->arity; i++)
	{	
		ClauseTableau_p child = tab->children[i];
		assert(child);
		ClauseTableauPrintDOTGraphChildren(child, dotgraph);
	}
	fprintf(dotgraph, "\n}");
}

void ClauseTableauPrintDOTGraphChildren(ClauseTableau_p tab, FILE* dotgraph)
{
	ClauseTableau_p parent = tab->parent;
	Clause_p parent_label = parent->label;
	long parent_ident = ClauseGetIdent(parent_label);
	Clause_p label = tab->label;
	long ident = ClauseGetIdent(label);
	// any folded up clauses here?
	int folds = 0;
	if (tab->folding_labels) folds = tab->folding_labels->members;
	
	if (!tab->open)
	{
		fprintf(dotgraph,"   %ld [color=Black, label=\"", ident);
	}
	else
	{
		if (tab->set == tab->open_branches)
		{
			fprintf(dotgraph,"   %ld [color=Blue, shape=box, label=\"", ident);
		}
		else
		{
			fprintf(dotgraph,"   %ld [color=Blue, label=\"", ident);
		}
	}
	ClauseTSTPCorePrint(dotgraph, label, true);
	int tab_depth = tab->depth;
	bool tab_saturation_closed = tab->saturation_closed;
	int tab_mark_int = tab->mark_int;
	int tab_folded_up = tab->folded_up;
	
	fprintf(dotgraph, " d:%d ", tab_depth);
	fprintf(dotgraph, "f:%d ", folds);
	fprintf(dotgraph, "s:%d ", tab_saturation_closed);
	fprintf(dotgraph, "m:%d ", tab_mark_int);
	fprintf(dotgraph, "id:%ld ", tab->id);
	fprintf(dotgraph, "fu:%d\"]\n ", tab_folded_up);
	fprintf(dotgraph,"   %ld -> %ld\n", parent_ident, ident);
	
	for (int i=0; i < tab->arity; i++)
	{	
		ClauseTableau_p child = tab->children[i];
		ClauseTableauPrintDOTGraphChildren(child, dotgraph);
	}
	fflush(dotgraph);
}

/*  Checks to see if labels on leaf nodes are duplicated higher up on their branch.
 *  If so, the branch and thus tableau is not leaf regular (or regular for that matter).
 *  Used to prevent closure rule applications from creating irregular tableaux. 
*/ 


bool ClauseTableauIsLeafRegular(ClauseTableau_p tab)
{
	ClauseTableau_p master = tab->master;
	TableauSet_p open_branches = master->open_branches;
	ClauseTableau_p open_branch = open_branches->anchor->succ;
	while (open_branch != open_branches->anchor)
	{
		if (ClauseTableauBranchContainsLiteral(open_branch->parent, open_branch->label->literals))
		{
			// irregular
			return false;
		}
		open_branch = open_branch->succ;
	}
	return true;
}

// Attempt to unify the literal with the nodes on the branch above.
// If one can be unified, the expansion would no longer be regular.

bool ClauseTableauBranchContainsLiteral(ClauseTableau_p branch, Eqn_p literal)
{
	Clause_p label = branch->label;
	Eqn_p node_literal = label->literals;
	ClauseTableau_p node = branch;
	Subst_p subst = SubstAlloc();
	while (node != branch->master) // climb the tableau until we hit the root.  do not check root for regularity
	{
		label = node->label;
		node_literal = label->literals;
		if (EqnIsPositive(literal) && EqnIsNegative(node_literal)) 
		{
			SubstBacktrack(subst);
			node = node->parent;
			continue;
		}
		else if (EqnIsNegative(literal) && EqnIsPositive(node_literal))
		{
			SubstBacktrack(subst);
			node = node->parent;
			continue;
		}
		else if (EqnUnify(literal, node_literal, subst))
		{
			//~ printf("Potentially irregular extension:\n");
			//~ EqnTSTPPrint(GlobalOut,node_literal , true);printf("\n");
			//~ EqnTSTPPrint(GlobalOut,literal , true);printf("\n");
			if (SubstIsRenaming(subst))
			{
				//printf("Node clause:\n");
				//ClausePrint(GlobalOut, label, true);printf("\n");
				SubstDelete(subst);
				//printf("# Branch contains literal... irregular\n");
				return true;
			}
		}
		SubstBacktrack(subst);
		node = node->parent;
	}
	SubstDelete(subst);
	return false;
}

TableauControl_p TableauControlAlloc(long neg_conjectures, 
												 char *problem_name, 
												 ProofState_p proofstate, 
												 ProofControl_p proofcontrol,
												 bool branch_saturation_enabled,
												 int num_cores_to_use)
{
	TableauControl_p handle = TableauControlCellAlloc();
	handle->terms = NULL; // The termbank for this tableau control..
	handle->number_of_extensions = 0;  // Total number of extensions done
	handle->closed_tableau = NULL;
	handle->branch_saturation_enabled = branch_saturation_enabled;
	handle->satisfiable = false;
	handle->multiprocessing_active = num_cores_to_use;
	handle->unprocessed = NULL;
	handle->label_storage = ClauseSetAlloc();
	handle->problem_name = problem_name;
	handle->neg_conjectures = neg_conjectures;
	handle->proofstate = proofstate;
	handle->proofcontrol = proofcontrol;
	handle->tableaux_trash = PStackAlloc();
	handle->clausification_buffer = NULL;
	handle->process_control = NULL;
	return handle;
}

void TableauControlFree(TableauControl_p trash)
{
	//assert(ClauseSetEmpty(trash->label_storage));
	ClauseSetFree(trash->label_storage);
	PStackFree(trash->tableaux_trash);
	TableauControlCellFree(trash);
}

void ClauseTableauPrintDerivation(FILE* out, ClauseTableau_p final_tableau, TableauStack_p derivation)
{
	for (PStackPointer p = 1; p < PStackGetSP(derivation); p++)
	{
		ClauseTableau_p previous_step = PStackElementP(derivation, p);
		assert(previous_step);
		ClauseTableauPrint(previous_step);
		DStr_p str = DStrAlloc();
		DStrAppendStr(str, "/home/hesterj/Projects/APRTESTING/DOT/unsattest/graph");
		DStrAppendInt(str, p);
		DStrAppendStr(str, ".dot");
		FILE *dotgraph = fopen(DStrView(str), "w");
		ClauseTableauPrintDOTGraphToFile(dotgraph, previous_step->master);
		fclose(dotgraph);
		printf("# %ld\n", p);
		if ((p + 1) == PStackGetSP(derivation))
		{
			sleep(1);
			DStr_p str2 = DStrAlloc();
			DStrAppendStr(str2, "/home/hesterj/Projects/APRTESTING/DOT/unsattest/graph");
			DStrAppendInt(str2, p+1);
			DStrAppendStr(str2, ".dot");
			FILE *dotgraph = fopen(DStrView(str2), "w");
			ClauseTableauPrintDOTGraphToFile(dotgraph, final_tableau);
			fclose(dotgraph);
			DStrFree(str2);
		}
		printf("#############################\n");
		DStrFree(str);
		sleep(1);
	}
}

void ClauseTableauRegisterStep(ClauseTableau_p tab)
{
	tab->master->max_step++;
	tab->step = tab->master->max_step;
}

int TableauStepCmp(const void* tab1_intorp, const void* tab2_intorp)
{
	const IntOrP* step1 = (const IntOrP*) tab1_intorp;
	const IntOrP* step2 = (const IntOrP*) tab2_intorp;
	
	ClauseTableau_p tab1 = step1->p_val;
	ClauseTableau_p tab2 = step2->p_val;
	if (tab1->step < tab2->step) return -1;
	else if (tab1->step > tab2->step) return 1;
	return 0;
}

void ClauseTableauCollectSteps(ClauseTableau_p tab, PStack_p steps)
{
	if (tab->step >= 0)
	{
		PStackPushP(steps, tab);
	}
	for (int i=0; i<tab->arity; i++)
	{
		ClauseTableauCollectSteps(tab->children[i], steps);
	}
}

void ClauseTableauTPTPPrint(ClauseTableau_p tab)
{
	PStack_p steps = PStackAlloc();
	ClauseTableauCollectSteps(tab, steps);
	fprintf(GlobalOut, "# Found %ld steps\n", PStackGetSP(steps));
	PStackSort(steps, TableauStepCmp);
	for (long i=0; i< PStackGetSP(steps); i++)
	{
		ClauseTableau_p node = PStackElementP(steps, i);
		fprintf(GlobalOut, "# %d ", (int) node->step);
		ClausePrint(GlobalOut, node->label, true);
		fprintf(GlobalOut, " %s\n", DStrView(node->info));
	}
	PStackFree(steps);
}

/*  Return the smallest variable that does not occur in the tableau,
 *  according to the tableau_variables tree.  Adds the variable to the
 *  tree when it is found.
*/

Term_p ClauseTableauGetFreshVar(ClauseTableau_p tab, Term_p old_var)
{
	assert(tab == tab->master);
	FunCode var_funcode = tab->max_var -2;
	assert(var_funcode%2 == 0);
	bool fresh_found = false;
	VarBank_p varbank = tab->terms->vars;
	//int v_count = PDArrayElementInt(varbank->v_counts, old_var->type->type_uid);
	while (!fresh_found)
	{
		//printf("# %ld\n", var_funcode);
		Term_p potential_fresh = VarBankFCodeFind(varbank, var_funcode);
		if (UNLIKELY(!potential_fresh)) //hasn't been created yet
		{
			potential_fresh = VarBankVarAssertAlloc(varbank, var_funcode, old_var->type);
		}
		PTree_p found = PTreeFind(&(tab->tableau_variables), potential_fresh);
		if (!found)
		{
			assert(TermIsVar(potential_fresh));
			PTreeStore(&(tab->tableau_variables), potential_fresh);
			assert(PTreeFind(&(tab->tableau_variables), potential_fresh));
			//v_count++;
			//PDArrayAssignInt(varbank->v_counts, old_var->type->type_uid, v_count);
			return potential_fresh;
		}
		var_funcode -= 2;
	}
	Error("# Could not find a fresh variable...", 1);
	return NULL;
}

PList_p ClauseSetToPList(ClauseSet_p set)
{
	PList_p list = PListAlloc();
	Clause_p handle = set->anchor->succ;
	while (handle != set->anchor)
	{
		PListStoreP(list, handle);
		handle = handle->succ;
	}
	return list;
}

long ClauseGetIdent(Clause_p clause)
{
	long ident = clause->ident;
	if (ident<0)
	{
		ident = ident - LONG_MIN;
	}
	return ident;
}

/*-----------------------------------------------------------------------
//
// Function: SubstPrint()
//
//   Print a substitution. Note: Due to the different interpretations
//   of terms (follow/ignore bindings) and share variable, printing
//   substitutions with deref=DEREF_ALWAYS may lead to
//   unpredictable behaviour (if e.g. the substitution was generated
//   by matching x onto f(x)). Returns number of variables in subst
//   (well, why not...).
//
// Global Variables: -
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

long SubstDStrPrint(DStr_p str, Subst_p subst, Sig_p sig, DerefType deref)
{
   PStackPointer i, limit;
	FILE *out;
	char *buf;
	size_t len;
	
	out = open_memstream(&buf, &len);
	if (out == NULL)
	{
		int error_number = errno;
		fprintf(stdout, "Error: Buffer error %d in SubstDStrPrint!\n", error_number);	
		return 0;	
	}
   limit = PStackGetSP(subst);
   fprintf(out, "{");
   if(limit)
   {
      SubstBindingPrint(out,  PStackElementP(subst,0), sig, deref);
      {
         for(i=1; i<limit;i++)
         {
            fprintf(out, ", ");
            SubstBindingPrint(out,  PStackElementP(subst,i), sig,
                              deref);
         }
      }
   }
   fprintf(out, "}");
   fclose(out);
	DStrAppendStr(str, buf);
	free(buf);
   return (long)limit;
}

// Now for stuff about representing clauses and branches as stack of integers 
ClauseRep_p ClauseGetRepresentation(Clause_p clause)
{
	Eqn_p literals = clause->literals;
	return NULL;
}
