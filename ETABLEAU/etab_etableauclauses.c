#include"etab_etableauclauses.h"

Clause_p etab_clause_copy(Clause_p clause, PDArray_p branch_variables, PDArray_p tableau_variables);
Eqn_p etab_eqnlist_copy(Eqn_p list, PDArray_p branch_variables, PDArray_p tableau_variables);
Eqn_p etab_eqn_copy(Eqn_p eq, PDArray_p branch_variables, PDArray_p tableau_variables);

Clause_p EtableauClauseCopyReal(Clause_p clause, PDArray_p branch_variables, PDArray_p tableau_variables)
{
    assert(clause);
    assert(node);
    assert(node->master);
    assert(node->master->tableau_variables_array);
    assert(node->node_variables_array);

    Clause_p res;

    if (branch_variables && tableau_variables)
    {
        res = etab_clause_copy(clause, branch_variables, tableau_variables);
    }
    else
    {
        res = ClauseCopyOpt(clause);
    }

    assert(res);

    return res;
}

ClauseSet_p EtableauClauseSetCopyReal(ClauseSet_p set, PDArray_p branch_variables, PDArray_p tableau_variables)
{
    ClauseSet_p new;
    if (branch_variables && tableau_variables)
    {
        Clause_p handle, temp;
        assert(set);
        new = ClauseSetAlloc();
        for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
        {
            assert(handle);
            temp = EtableauClauseCopyReal(handle, branch_variables, tableau_variables);
            ClauseDelProp(temp, CPIsDIndexed);
            ClauseDelProp(temp, CPIsSIndexed);
            ClauseSetInsert(new, temp);
        }
    }
    else
    {
        new = ClauseSetCopyOpt(set);
    }
    return new;
}

Clause_p etab_clause_copy(Clause_p clause, PDArray_p branch_variables, PDArray_p tableau_variables)
{
   assert(bank);
   assert(clause);
   assert(clause->literals->lterm->f_code <= bank->sig->f_count);
   assert(clause->literals->rterm->f_code <= bank->sig->f_count);
   Clause_p handle = clause_copy_meta(clause);

   handle->literals = etab_eqnlist_copy(clause->literals, branch_variables, tableau_variables);

   return handle;
}

Eqn_p etab_eqnlist_copy(Eqn_p list, PDArray_p branch_variables, PDArray_p tableau_variables)
{
   Eqn_p  newlist = NULL;
   EqnRef insert = &newlist;

   while(list)
   {
      *insert = etab_eqn_copy(list, branch_variables, tableau_variables);
      insert = &((*insert)->next);
      list = list->next;
   }
   *insert = NULL;

   return newlist;
}

Eqn_p etab_eqn_copy(Eqn_p eq, PDArray_p branch_variables, PDArray_p tableau_variables)
{
   Eqn_p  handle;
   Term_p lterm, rterm;

   lterm = TBInsertOptArray(eq->bank, eq->lterm, DEREF_ALWAYS, branch_variables, tableau_variables);
   rterm = TBInsertOptArray(eq->bank, eq->rterm, DEREF_ALWAYS, branch_variables, tableau_variables);

   handle = EqnAlloc(lterm, rterm, eq->bank, false); /* Properties will be
                                                        taken care of
                                                        later! */
   handle->properties = eq->properties;
   EqnDelProp(handle, EPMaxIsUpToDate);
   EqnDelProp(handle, EPIsOriented);

   return handle;
}

ClauseSet_p ClauseSetCopy(TB_p bank, ClauseSet_p set)
{
    Clause_p handle, temp;
    assert(set);
    ClauseSet_p new = ClauseSetAlloc();
    for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
    {
        assert(handle);
        temp = ClauseCopy(handle, bank);
#ifdef DEBUG
        ClauseRecomputeLitCounts(temp);
        assert(ClauseLiteralNumber(temp));
#endif
        ClauseDelProp(temp, CPIsDIndexed);
        ClauseDelProp(temp, CPIsSIndexed);
        ClauseSetInsert(new, temp);
    }
    return new;
}

ClauseSet_p ClauseSetCopyDisjoint(TB_p bank, ClauseSet_p set)
{
    Clause_p handle, temp;
    assert(set);
    ClauseSet_p new = ClauseSetAlloc();
    for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
    {
        assert(handle);
        temp = ClauseCopyDisjoint(handle);
#ifdef DEBUG
        ClauseRecomputeLitCounts(temp);
        assert(ClauseLiteralNumber(temp));
#endif
        ClauseDelProp(temp, CPIsDIndexed);
        ClauseDelProp(temp, CPIsSIndexed);
        ClauseSetInsert(new, temp);
    }
    return new;
}

// Copy a clause set, ignore bindings

ClauseSet_p ClauseSetFlatCopy(ClauseSet_p set)
{
    Clause_p handle, temp;
    assert(set);
    ClauseSet_p new = ClauseSetAlloc();
    for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
    {
        assert(handle);
        temp = ClauseFlatCopy(handle);
        ClauseDelProp(temp, CPIsDIndexed);
        ClauseDelProp(temp, CPIsSIndexed);
        ClauseSetInsert(new, temp);
    }
    return new;
}

ClauseSet_p ClauseSetCopyOpt(ClauseSet_p set)
{
    Clause_p handle, temp;
    assert(set);
    ClauseSet_p new = ClauseSetAlloc();
    for (handle = set->anchor->succ; handle != set->anchor; handle = handle->succ)
    {
        assert(handle);
        temp = ClauseCopyOpt(handle);
#ifdef DEBUG
        ClauseRecomputeLitCounts(temp);
        assert(ClauseLiteralNumber(temp));
#endif
        ClauseDelProp(temp, CPIsDIndexed);
        ClauseDelProp(temp, CPIsSIndexed);
        ClauseSetInsert(new, temp);
    }
    return new;
}

//EtableauClause_p EtableauClauseAlloc(Clause_p clause)
//{
    //EtableauClause_p wrapped_clause = EtableauClauseCellAlloc();
    //wrapped_clause->properties = ETCIgnoreProps;
    //wrapped_clause->clause = clause;
    //return wrapped_clause;
//}
//
//void EtableauClauseFree(EtableauClause_p junk)
//{
    //EtableauClauseCellFree(junk);
//}
