#ifndef EXTENSION
#define EXTENSION

//#include <foldingup.h>
#include <etab_etableau.h>
/*  Storage type for potential extension steps to be done at a single node
 *  This is needed because there can be several extension steps to be done
*/

typedef struct tableau_extension_cell
{
	Clause_p selected; // the clause being split
	Subst_p subst; // the substitution that must be applied to the tableau to do the step
	Clause_p head_clause; // the head literal of the extension step...
	ClauseSet_p other_clauses; // the clauses that will be in the new branches
	ClauseTableau_p parent; // the parent tableau.
	
	struct tableau_extension_cell* succ;  // for singly linked lists of the extension steps
}TableauExtension, *TableauExtension_p;

void ClauseSetFreeAnchor(ClauseSet_p junk);
ClauseSet_p ClauseStackToClauseSet(ClauseStack_p stack);

bool ClauseTableauExtensionIsRegular(ClauseTableau_p branch, Clause_p clause);


#define TableauExtensionCellAlloc() (TableauExtension*)SizeMalloc(sizeof(TableauExtension))
#define TableauExtensionCellFree(junk) SizeFree(junk, sizeof(TableauExtension))

int ClauseTableauExtensionRuleAttemptOnBranch(TableauControl_p control,
															 ClauseTableau_p open_branch, 
															 TableauSet_p distinct_tableaux,
															 Clause_p selected,
															 TableauStack_p new_tableaux);
ClauseSet_p SplitClauseFresh(TB_p bank, ClauseTableau_p tableau, Clause_p clause); // Major memory eating offender
TableauExtension_p ClauseTableauCreateExtensionJobs(ClauseTableau_p open_branch, Clause_p selected);
ClauseTableau_p ClauseTableauExtensionRule(TableauControl_p tableau_control,
														 TableauSet_p distinct_tableaux, 
														 TableauExtension_p extension, 
														 TableauStack_p new_tableaux);
										   
TableauExtension_p TableauExtensionAlloc(Clause_p selected,
										 Subst_p subst, 
										 Clause_p head_clause, 
										 ClauseSet_p other_clauses, 
										 ClauseTableau_p parent);
void TableauExtensionFree(TableauExtension_p ext);

#endif
