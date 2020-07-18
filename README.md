Etableau is theorem prover designed to combine the superposition and tableaux calculus in a new way.  It is a fork of the Eprover project that intends to maintain compatibility with the source.  By leveraging the power of multiple formal systems, the deductive power is increased on many problems.

In a first order tableaux, branches that don't share variables with other branches are considered local.  Etableau implements part of the first order tableaux calculus specified in the Handbook of Automated Reasoning.  Etableau's search uses Eprover's superposition calculus to close branches that are local.  Often, in superposition theorem proving, contradictions are found quickly or not at all.  By engaging in a short search on many branches, and closing those that can be easily removed using the tableaux calculus, the search space of the tableaux calculus is restrained.  

This enables an automated generation of lemmas by the prover- substitutions that were used to close branches of a tableau are applied to it, and the clauses resulting from this are used in superposition proof search.  Clauses generated in the tableaux proof search that end up labelling nodes in local branches are processed first to leverage this automated lemma generation.

Etableau is a work in progress.  If you clone this repository and it crashes or is unsound, please let me know.

Install instructions:

```
./configure
make rebuild
cd PROVER
./eprover -h | 
```

Etableau is installed and licensed in the same way as Eprover.  Usage is also the same, except with some options added.  Try Etableau proof seach with:

```
./eprover --auto -s --tableau=1 --tableau-depth=10 --tableau-saturation=1 SET996+1.p
```

If a successful proof (closed tableau) is not found up to --tableau-depth, search will abort.  If the option --tableau is not set to 1, Eprover will operate normally.
