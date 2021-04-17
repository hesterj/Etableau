
Etableau
========

Etableau is a first order theorem prover for first order logic based 
on [Eprover](https://www.eprover.org), using it as a library.  Etableau combines the superposition
calculus and the clausal tableaux connection calculus in a novel way, using the
tableaux calculus to generate lemmas and new assumptions that can be 
used to find contradictions in certain situations.

This means that branches of a tableau that are difficult to close using
the clausal tableau calculus can be closed with Eprover's saturation.
The saturation procedure benefits from the extra assumptions that are 
present on the branch of the tableau.  It seems that saturation procedures
often find a proof quickly or not at all, so by doing many short proof
searches with differing assumptions it is possible for proofs to be found
that may not have been otherwise.

Etableau is licensed and installed in the same way as Eprover.

To install Etableau, clone this repository, execute the following commands,
or follow the instructions for Eprover.

``` 
    ./configure
    make rebuild
```
    
The executable "eprover" is generated in the PROVER directory.  To check that it worked,
try running ./eprover --tableau=1 --tableau-saturation=1 --auto $1, where $1 is some [TPTP](https://www.tptp.org) problem file.

tableau
---------
--tableau=1 enables clausal tableaux proof search.  If this option is not passed, normal
Eprover will happen.

tableau-saturation
--------------------

--tableau-saturation=1 enables the combination of the superposition calculus and tableaux
calculus.  The default is 0, meaning that without this option, Etableau will function
purely as a clausal tableaux connection calculus prover.

tableau-dot-print
-------------------
--tableau-dot-print=dir prints DOT graphs of the closed tableau found in a successful proof 
search to the directory dir.

tableau-dot-print-steps
-----------------------
--tableau-dot-print-steps prints DOT graphs of every step made by the prover to the directory
specified in tableau-dot-print.  When a closed tableau is found, the final step will be the 
closed tableau.  Otherwise, the steps present will be the most recent made by the prover.
The PID is used to distinguish steps made by different processes.

tsmdo
-----
--tsmdo restricts branch saturation attmepts on a tableau to the case where there is a branch
at the current maximum tableau search depth.  It stands for "Tableau saturate max depth only".
If this is not passed, Etableau will attempt to saturate every local branch found.  
Passing this option potentially increases the amount of branching during proof search, 
but also prevents time being wasted on attempts to saturate
shallow branches that may not have an easily found contradiction.  The default is false.

tnssr
-----
--tnssr prevents star rule tableaux from being saturated by Eprover.  It stands for 
"Tableau no saturate start rules".  This is useful if you
want to force Etableau to do a little more work, rather than just relying on Eprover to find
contradictions on simple problems immediately.  By default this is disabled in order to prove
as many problems as possible.

apr
-----
--apr=3 filters the axiom specification to only include clauses within an alternating
path relevance distance of 3 from the conjectures of the specification.  This number can 
be changed.  This option is not recommended except on the largest problems.

quicksat
----------
--quicksat=100 ensures that no more than 100 clauses are processed during saturation of
tableau branches.  This number can be changed.  The default value is 100 if the option
--quicksat is passed without an integer option.  If quicksat is passed, then there will
be a loss of completeness for branch saturations, but not the entire proof search.  This
is becuase of the fact that if only a small number of clauses are going to be processed
on a branch saturation, there is no need to copy the entire unprocessed clause set and
only a small number or none are copied.  If this option is not passed, the number of
clauses passed during branch saturations will vary, with more clauses being processed
when there are fewer open local branches.

tableau-equality
------------------
--tableau-equality=1 introduces equality axioms for the symbols found in the specification
as well as axioms of symmetry, reflection, and transitivity.  This is helpful on some
problems.  This is not normally necessary because if equality is detected in the signature
of a problem, equality axioms are automatically added.

Eprover options
---------------
Options controlling the saturation procedure of Eprover also work, allowing the user 
to use different strategies.  It is recommended to at least use the --auto
option of Eprover.

Help
----

If you have any problems with this software or a bug report, please feel free to contact
me at <hesterj@etableau.com>.  The project's webpage is [here](https://www.etableau.com).
[Github](https://github.com/hesterj/Etableau).



