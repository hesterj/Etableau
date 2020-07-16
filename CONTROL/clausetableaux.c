#include "clausetableaux.h"

int clausesetallocs_counter = 1;  

// Functions for clausetableaux.h

/*  The open branches for each distinct tableau MUST be initialized on creation,
 *  not by this method.
 * 
 * 
*/

ClauseTableau_p ClauseTableauAlloc()
{
	ClauseTableau_p handle = ClauseTableauCellAlloc();
	handle->depth = 0;
	handle->position = 0;
	handle->arity = 0;
	handle->unit_axioms = NULL;
	//handle->mark = NULL;
	handle->mark_int = 0;
	handle->folded_up = 0;
	handle->step = 0;
	handle->max_step = 0;
	handle->folding_labels = NULL;
	handle->set = NULL;
	handle->derivation = PStackAlloc();
	handle->head_lit = false;
	handle->saturation_closed = false;
	handle->id = 0;
	handle->max_var = 0;
	//handle->info = DStrAlloc();
	handle->active_branch = NULL;
	handle->pred = NULL;
	handle->control = NULL;
	handle->state = NULL;
	handle->succ = NULL;
	handle->local_variables = NULL;
	handle->open_branches = NULL;
	handle->children = NULL;
	handle->label = NULL;
	handle->tmp_label = NULL;
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
	handle->derivation = PStackCopy(tab->derivation);
	PStackPushP(handle->derivation, tab);
	handle->tmp_label = NULL;
	handle->arity = tab->arity;
	//~ char *info = DStrCopy(tab->info);
	//~ handle->info = DStrAlloc();
	//~ DStrAppendStr(handle->info, info);
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
		handle->label = ClauseCopyOpt(tab->label);
		assert(handle->label);
	}
	else 
	{
		handle->label = NULL;
	}
	handle->master = handle;
	handle->parent = NULL;
	
	if (tab->arity == 0) // tab does not have children
	{
		handle->open = true;
		TableauSetInsert(handle->open_branches, handle);
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
	handle->derivation = NULL;
	handle->unit_axioms = NULL;
	//~ char *info = DStrCopy(tab->info);
	//~ handle->info = DStrAlloc();
	//~ DStrAppendStr(handle->info, info);
	handle->open_branches = parent->open_branches;
	handle->control = parent->control;
	handle->set = NULL;
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
	handle->tmp_label = NULL;
	handle->local_variables = NULL;
	if (tab->folding_labels)
	{
		handle->folding_labels = ClauseSetCopy(bank, tab->folding_labels);
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
		handle->label = ClauseCopyOpt(tab->label);
		assert(handle->label);
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
	handle->derivation = NULL;
	assert(parent);
	assert(label);
	parent->arity += 1;
	handle->step = 0;
	handle->max_step = 0;
	handle->depth = parent->depth + 1;
	handle->position = position;
	handle->unit_axioms = NULL;
	handle->open_branches = parent->open_branches;
	handle->label = label;
	handle->tmp_label = NULL;
	handle->id = 0;
	handle->head_lit = false;
	handle->local_variables = NULL;
	handle->control = parent->control;
	handle->max_var = parent->max_var;
	handle->set = NULL;
	handle->mark_int = 0;
	handle->folded_up = 0;
	handle->folding_labels = NULL;
	//handle->info = DStrAlloc();
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
	if (trash->derivation)
	{
		PStackFree(trash->derivation);
	}
	if (trash->label)
	{
		ClauseFree(trash->label);
		trash->label = NULL;
	}
	if (trash->unit_axioms) //unit axioms are only at the master node
	{
		ClauseSetFree(trash->unit_axioms);
	}
	if (trash->local_variables)
	{
		PStackFree(trash->local_variables);
	}
	if (trash->folding_labels)
	{
		ClauseSetFree(trash->folding_labels);
	}
	if (trash->children)
	{
		for (int i=0; i<trash->arity; i++)
		{
			ClauseTableauFree(trash->children[i]);
			trash->children[i] = NULL;
		}
		ClauseTableauArgArrayFree(trash->children, trash->arity);
		trash->children = NULL;
	}
	if (trash->depth == 0 && trash->open_branches)
	{
		TableauSetFree(trash->open_branches);
		trash->open_branches = NULL;
	}
	//DStrFree(trash->info);
	ClauseTableauCellFree(trash);
}

void TableauStackFreeTableaux(PStack_p stack)
{
	while (!PStackEmpty(stack))
	{
		ClauseTableau_p tab = PStackPopP(stack);
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
	
	assert(tab->label);
	assert(subst);
	
	Clause_p new_label = ClauseCopyOpt(tab->label);
	ClauseFree(tab->label);
	assert(new_label);
	tab->label = new_label;
	
	if (tab->folding_labels)  // The edge labels that have been folded up if the pointer is non-NULL
	{
		ClauseSet_p new_edge = ClauseSetCopy(tab->terms, tab->folding_labels);
		ClauseSetFree(tab->folding_labels);
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
		temp = ClauseCopyOpt(handle);
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
		temp = ClauseCopyOpt(handle);
		ClauseSetInsert(new, temp);
	}
	return new;
}

/* Should only be called on closed tableau, as in order to collect the leaves, open branches
 *  must be removed from their tableau set.
*/

void ClauseTableauPrint(ClauseTableau_p tab)
{
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
		fprintf(GlobalOut, "# %d,%d,%ld,%d ", depth_check->depth,depth_check->arity, depth_check->id,depth_check->mark_int);
		if (depth_check->head_lit)
		{
			fprintf(GlobalOut, " x");
		}
		if (!depth_check->open)
		{
			fprintf(GlobalOut, " c");
		}
		if (depth_check->saturation_closed)
		{
			fprintf(GlobalOut, " s");
		}
		fprintf(GlobalOut, "\n");
		ClausePrint(GlobalOut, depth_check->label, true);
		
		fprintf(GlobalOut, "\n");
		depth_check = depth_check->parent;
	}
	assert (depth_check->depth == 0);
	assert (depth_check->label);
	
	fprintf(GlobalOut, "# %d,%d,%ld,%d \n", depth_check->depth,depth_check->arity, depth_check->id,depth_check->mark_int);
	ClausePrint(GlobalOut, depth_check->label, true);
	fprintf(GlobalOut, "\n");
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
   new_clause = ClauseCopyOpt(clause);
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
   PTree_p variable_tree = NULL;
   PStack_p variables;
   PStackPointer p;
   Subst_p subst;
   Term_p old_var, fresh_var;
   Clause_p handle;
   VarBank_p variable_bank;
   
   assert(clause);
   
   variable_bank = tableau->master->terms->vars;
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
	   //~ printf("tableau max var: %ld\n", tableau->master->max_var);
	   //~ printf("old var: %ld\n", old_var->f_code);
	   //printf("# Old_var->type in ClauseFlatCopyFresh: %ld\n", old_var->type->f_code);
	   tableau->master->max_var -= 2;
	   //fresh_var = VarBankVarAssertAlloc(variable_bank, tableau->master->max_var, old_var->type);
	   fresh_var = VarBankGetFreshVar(variable_bank, old_var->type);
	   //~ printf("old var: %ld\n", old_var->f_code);
	   //~ printf("fresh var: %ld\n", fresh_var->f_code);
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
   
	//printf("max_var %ld\n", tableau->master->max_var);
   
   handle = ClauseCopyOpt(clause);
   
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
	assert(!(tab->label));
	assert(!(tab->arity));
	assert(start);
	assert(tab->state);
	assert(tab->control);
	
	arity = ClauseLiteralNumber(start);
	tab->open = true;
	TableauSetExtractEntry(tab); // no longer open
	assert(tab->open_branches->members == 0);
	tab->label = ClauseCopyOpt(start);
	assert(tab->label);
	
	tab->id = ClauseGetIdent(tab->label);
	
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
   set->anchor  = ClauseTableauAlloc();
   set->anchor->succ = set->anchor;
   set->anchor->pred = set->anchor;

   return set;
}

TableauSet_p TableauSetCopy(TableauSet_p set)
{
	return NULL;
}

void TableauSetInsert(TableauSet_p list, ClauseTableau_p tab)
{
   assert(list);
   assert(tab);
   assert(!tab->set);

   tab->succ = list->anchor;
   tab->pred = list->anchor->pred;
   list->anchor->pred->succ = tab;
   list->anchor->pred = tab;
   tab->set = list;
   list->members++;
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

long ClauseGetIdent(Clause_p clause)
{
	long ident = clause->ident;
	if (ident<0)
	{
		ident = ident - LONG_MIN;
	}
	return ident;
}

TableauControl_p TableauControlAlloc(long neg_conjectures, 
												 char *problem_name, 
												 ProofState_p proofstate, 
												 ProofControl_p proofcontrol,
												 bool branch_saturation_enabled)
{
	TableauControl_p handle = TableauControlCellAlloc();
	handle->terms = NULL; // The termbank for this tableau control..
	handle->number_of_extensions = 0;  // Total number of extensions done
	handle->closed_tableau = NULL;
	handle->branch_saturation_enabled = branch_saturation_enabled;
	handle->satisfiable = false;
	handle->unprocessed = NULL;
	handle->problem_name = problem_name;
	handle->neg_conjectures = neg_conjectures;
	handle->proofstate = proofstate;
	handle->proofcontrol = proofcontrol;
	handle->trash = PStackAlloc();
	handle->clausification_buffer = NULL;
	return handle;
}

void TableauControlFree(TableauControl_p trash)
{
	TableauControlCellFree(trash);
}
