#include"etab_xgboost_interaction.h"

DTree_p DTreeAlloc(long key, int arity)
{
    DTree_p handle = DTreeCellAlloc();
    handle->key = key;
    handle->arity = arity;
    handle->children = DTreeArgArrayAlloc(arity);
    for (int i=0; i<arity; i++)
    {
        handle->children[i] = NULL;
    }
    return handle;
}

void DTreeFree(void *trash_tree)
{
    DTree_p trash = (DTree_p) trash_tree;
    DTree_p *children = trash->children;
    int arity = trash->arity;
    for (int i=0; i<arity; i++)
    {
        DTreeFree(children[i]);
    }
    DTreeCellFree(trash);
    DTreeArgArrayFree(children, arity);
}

DTree_p DTreeRepresentation(Term_p term)
{
    assert(term);
    int arity = term->arity;
    long code = TermIsVar(term) ? -1 : term->f_code;
    DTree_p handle = DTreeAlloc(code, term->arity);
    if (arity)
    {
        handle->children = DTreeArgArrayAlloc(arity);
        for (int i=0; i<arity; i++)
        {
            handle->children[i] = DTreeRepresentation(term->args[i]);
        }
    }

    return handle;
}

DTree_p DTreeEqnRepresentation(Eqn_p eqn)
{
    bool positive = EqnIsPositive(eqn);
    DTree_p handle = DTreeAlloc(positive, 2);
    handle->children = DTreeArgArrayAlloc(2);
    handle->children[0] = DTreeRepresentation(eqn->lterm);
    handle->children[1] = DTreeRepresentation(eqn->rterm);
    return handle;

}

// Return 0 if the two DTree_p are identical
// This is intended to be a ComparisonFunctionType!

int DTreesIdentical(const void *left_p, const void *right_p)
{
    DTree_p left = (DTree_p) left_p;
    DTree_p right = (DTree_p) right_p;
    if (left->key != right->key || left->arity != right->arity) return 1;
    int arity = left->arity;
    int children_identical = 0;
    for (int i=0; i<arity; i++)
    {
        children_identical = DTreesIdentical(left->children[i], right->children[i]);
        if (children_identical != 0) return 1;
    }
    return 0;
}


int EqnUnifyRenamingPCmp(const void *left_p, const void *right_p)
{
    Eqn_p left = (Eqn_p) left_p;
    Eqn_p right = (Eqn_p) right_p;
    bool unifiable = EqnUnifyRenamingP(left, right);
    if (unifiable) return 0;
    return 1;
}

void DTreeStupidPrintChildren(DTree_p root)
{
    for (int i=0; i<root->arity; i++)
    {
        DTree_p child = root->children[i];
        fprintf(GlobalOut, "%ld ", child->key);
    }
    fprintf(GlobalOut, "\n");
    for (int i=0; i<root->arity; i++)
    {
        DTreeStupidPrintChildren(root->children[i]);
    }

}

void DTreeStupidPrint(DTree_p root)
{
    fprintf(GlobalOut, "%ld\n", root->key);
    for (int i=0; i<root->arity; i++)
    {
        DTreeStupidPrintChildren(root->children[i]);
    }
}

/*
** This is the function that gets (an easy) feature representation of the branch.  Features are indexed by their address of the corresponding DTree_p.
** The number of occurrences of a feature is the value of the occurence_function applied to the memory addresses of the branch's DTree_p occurrences.
 */

long DTreeBranchRepresentations(ClauseTableau_p branch, PObjTree_p *tree_of_trees)
{
    //fprintf(GlobalOut, "# getting branch representations\n");
    //fprintf(GlobalOut, "# p: %p\n", *tree_of_trees);
    while (branch != branch->master)
    {
        assert(ClauseLiteralNumber(branch->label) == 1);
        PObjTree_p new_cell = PTreeCellAlloc();
        Eqn_p label_eqn = branch->label->literals;
        DTree_p dtree_representation = DTreeEqnRepresentation(label_eqn);
        new_cell->key = dtree_representation;
        //fprintf(GlobalOut, "# inserting... &%p %p\n", tree_of_trees, *tree_of_trees);
        PObjTree_p objtree_cell = PTreeObjInsert(tree_of_trees, new_cell, DTreesIdentical);
        //fprintf(GlobalOut, "# done inserting\n");
        if (objtree_cell) // We found a cell with an identical ptree, so we can discard the one we just made and increment the number of occurrences of the one we found.
        {
            PTreeCellFree(new_cell);
            DTreeFree(dtree_representation);
            DTree_p real_tree = (DTree_p) objtree_cell->key;
            real_tree->occurrences++;
            *tree_of_trees = objtree_cell;  // The tree was splayed and objtree_cell is the new root.
        }
        else // The dtree we just made has been inserted into the tree of dtrees, and since it clearly occurs we increment the occurrences.
        {
            *tree_of_trees = new_cell; // Since the new cell was inserted into the splay tree, we need to ensure we have a reference to the root.
            dtree_representation->occurrences++;
        }

        branch = branch->parent;
    }
    //fprintf(GlobalOut, "# blablabla %ld\n", PTreeNodes(*tree_of_trees));
    return 0;
}

long EqnBranchRepresentations(ClauseTableau_p branch, PObjTree_p *tree_of_eqns)
{
    TB_p bank = branch->terms;
    VarBank_p vars = bank->vars;
    TypeBank_p typebank = bank->sig->type_bank;
    Type_p individual_type = typebank->i_type;

    while (branch != branch->master)
    {
        assert(ClauseLiteralNumber(branch->label) == 1);
        PTree_p eqn_vars = NULL;
        Eqn_p label_eqn = branch->label->literals;

        __attribute__((unused)) long num_vars = EqnCollectVariables(label_eqn, &eqn_vars);

        Subst_p variable_subst = SubstAlloc();
        Term_p x1 = VarBankVarAssertAlloc(vars, -2, individual_type);
        PStack_p traverse = PTreeTraverseInit(eqn_vars);
        PTree_p variable_cell;
        Term_p variable;
        while ((variable_cell = PTreeTraverseNext(traverse)))
        {
            variable = variable_cell->key;
            SubstAddBinding(variable_subst, variable, x1);
        }
        PTreeTraverseExit(traverse);

        Term_p unshared_lterm = TermCopy(label_eqn->lterm, vars, DEREF_ALWAYS);
        assert(!TermCellQueryProp(unshared_lterm, TPIsShared));
        Term_p unshared_rterm;
        if (label_eqn->rterm->f_code == SIG_TRUE_CODE)
        {
            unshared_rterm = bank->true_term;
        }
        else
        {
            unshared_rterm = TermCopy(label_eqn->rterm, vars, DEREF_ALWAYS);
            assert(!TermCellQueryProp(unshared_rterm, TPIsShared));
        }
        Eqn_p dummy_eqn = EqnAlloc(unshared_lterm, unshared_rterm, bank, label_eqn->pos);
        SubstDelete(variable_subst);

        PObjTree_p new_cell = PTreeCellAlloc();
        new_cell->key = dummy_eqn;
        PObjTree_p objtree_cell = PTreeObjInsert(tree_of_eqns, new_cell, EqnUnifyRenamingPCmp);
        if (objtree_cell) // We found a cell with an identical eqn, so we can discard the one we just made and increment the number of occurrences of the one we found.
        {
            TermFree(unshared_lterm);
            if (unshared_rterm->f_code != SIG_TRUE_CODE)
            {
                TermFree(unshared_rterm);
            }
            EqnFree(dummy_eqn);
            PTreeCellFree(new_cell);
            Eqn_p real_eqn = (Eqn_p) objtree_cell->key;
            real_eqn->occurrences++;
        }
        else // The dtree we just made has been inserted into the tree of dtrees, and since it clearly occurs we increment the occurrences.
        {
            assert(new_cell->key == dummy_eqn);
            dummy_eqn->occurrences++;
        }
        PTreeFree(eqn_vars);
        branch = branch->parent;
    }
    return 0;
}

/*
** Return true if left and right are unifiable by a renaming of variables, false otherwise
**
**
*/

bool EqnUnifyRenamingP(Eqn_p left, Eqn_p right)
{
    Subst_p subst = SubstAlloc();
    bool success = true;
    bool unified = EqnUnify(left, right, subst);
    if (!unified || !SubstIsRenaming(subst))
    {
        success = false;
    }
    SubstDelete(subst);
    //if (left->lterm->f_code == right->lterm->f_code &&
        //left->rterm->f_code == right->rterm->f_code)
    //{
        //fprintf(GlobalOut, "Attempting to unify:\n");
        //EqnPrint(GlobalOut, left, EqnIsNegative(left), true); fprintf(GlobalOut, "\n");
        //EqnPrint(GlobalOut, right, EqnIsNegative(right), true); fprintf(GlobalOut, "\n");
        //fprintf(GlobalOut, "%d\n", success);
    //}
    return success;
}

void DTreeResetOccurrences(void *tree)
{
    DTree_p tree_casted = (DTree_p) tree;
    tree_casted->occurrences = 0;
}
void ResetAllOccurrences(PObjTree_p *tree_of_trees)
{
    PTreeVisitInOrder(*tree_of_trees, DTreeResetOccurrences);
}


void FeatureTreePrint(FILE* out, PObjTree_p *tree_of_trees)
{
    PStack_p iter = PTreeTraverseInit(*tree_of_trees);
    PObjTree_p handle = NULL;
    while ((handle = PTreeTraverseNext(iter)))
    {
        DTree_p tree = (DTree_p) handle->key;
        assert(tree);
        fprintf(out, "# %p: %d\n", tree, tree->occurrences);
        DTreeStupidPrint(tree);
    }
    PTreeTraverseExit(iter);
}

void EqnTreePrint(FILE* out, PObjTree_p *tree_of_eqns)
{
    PStack_p iter = PTreeTraverseInit(*tree_of_eqns);
    PObjTree_p handle = NULL;
    while ((handle = PTreeTraverseNext(iter)))
    {
        Eqn_p eqn = (Eqn_p) handle->key;
        assert(eqn);
        fprintf(GlobalOut, "# %p ", eqn);
        EqnPrint(GlobalOut, eqn, EqnIsNegative(eqn), true);
        fprintf(GlobalOut, " %d\n", eqn->occurrences);

    }
    PTreeTraverseExit(iter);
}

//  Another try...  Using PList instead of splay trees

long EqnBranchRepresentationsList(ClauseTableau_p branch, PList_p list_of_eqns, int branch_status)
{
    TB_p bank = branch->terms;
    VarBank_p vars = bank->vars;
    //TypeBank_p typebank = bank->sig->type_bank;
    //Type_p individual_type = typebank->i_type;

    while (branch != branch->master)
    {
        assert(ClauseLiteralNumber(branch->label) == 1);
        Eqn_p label_eqn = branch->label->literals;

        //PTree_p eqn_vars = NULL;
        //long num_vars = EqnCollectVariables(label_eqn, &eqn_vars);
        //Subst_p variable_subst = SubstAlloc();
        //Term_p x1 = VarBankVarAssertAlloc(vars, -2, individual_type);
        //PStack_p traverse = PTreeTraverseInit(eqn_vars);
        //PTree_p variable_cell;
        //Term_p variable;
        //while ((variable_cell = PTreeTraverseNext(traverse)))
        //{
            //variable = variable_cell->key;
            //SubstAddBinding(variable_subst, variable, x1);
        //}
        //PTreeTraverseExit(traverse);
        //PTreeFree(eqn_vars);

        Term_p unshared_lterm = TermCopyUnifyVars(vars, label_eqn->lterm);
        //Term_p unshared_lterm = TermCopy(label_eqn->lterm, vars, DEREF_ALWAYS);
        assert(!TermCellQueryProp(unshared_lterm, TPIsShared));
        Term_p unshared_rterm;
        if (label_eqn->rterm->f_code == SIG_TRUE_CODE)
        {
            unshared_rterm = bank->true_term;
        }
        else
        {
            //unshared_rterm = TermCopy(label_eqn->rterm, vars, DEREF_ALWAYS);
            unshared_rterm = TermCopyUnifyVars(vars, label_eqn->rterm);
            assert(!TermCellQueryProp(unshared_rterm, TPIsShared));
        }
        Eqn_p dummy_eqn = EqnAlloc(unshared_lterm, unshared_rterm, bank, label_eqn->pos);
        //SubstDelete(variable_subst);

        // Check to see if an equivalent equation is stored in the list
        Eqn_p found;
        if ((found = EquivalentEquationInList(dummy_eqn, list_of_eqns)))
        {
            found->occurrences++;
            TermFree(dummy_eqn->lterm);
            if (dummy_eqn->rterm->f_code != SIG_TRUE_CODE)
            {
                TermFree(dummy_eqn->rterm);
            }
            EqnFree(dummy_eqn);
            if (branch_status == PROOF_FOUND) // If the proof attempt on this branch was successful, increment the counter of successful proof searches
            {
                found->positive_occurrences++;
            }
        }
        else
        {
            PListStoreP(list_of_eqns, dummy_eqn);
            dummy_eqn->occurrences++;
            if (branch_status == PROOF_FOUND) // If the proof attempt on this branch was successful, increment the counter of successful proof searches
            {
                dummy_eqn->positive_occurrences++;
            }
        }

        branch = branch->parent;
    }
    return 0;
}

Eqn_p EquivalentEquationInList(Eqn_p eqn, PList_p anchor)
{
    PList_p handle = anchor->succ;
    while (handle != anchor)
    {
        Eqn_p handle_eqn = (Eqn_p) handle->key.p_val;
        if (EqnUnifyRenamingP(handle_eqn, eqn))
        {
            return handle_eqn;
        }
        handle = handle->succ;
    }
    return NULL;
}

void EqnPListPrint(FILE* out, PList_p list_of_eqns)
{
    fprintf(GlobalOut, "# Printing feature list vector\n");
    PList_p handle = list_of_eqns->succ;
    while (handle != list_of_eqns)
    {
        Eqn_p eqn = (Eqn_p) handle->key.p_val;
        assert(eqn);
        fprintf(GlobalOut, "# %p ", eqn);
        EqnPrint(GlobalOut, eqn, EqnIsNegative(eqn), true);
        fprintf(GlobalOut, " %d / %d\n", eqn->positive_occurrences, eqn->occurrences);
        handle = handle->succ;
    }
}

#ifdef XGBOOST_FLAG
void XGBoostTest()
{
    BoosterHandle booster;
    XGBoosterCreate(NULL, 0, &booster);
    XGBoosterSetParam(booster, "seed", "0");
    XGBoosterFree(booster);
    printf("# XGBoost linked\n");
}
#endif
