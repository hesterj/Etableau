This is an automated theorem prover that combines the clausal tableaux and superposition calculus.  It uses Eprover's superposition proof search on tableau branches that satisfy certain conditions and has its own implementation of the tableaux calculus, found in the CONTROL directory with etab_* prefixes.  Etableau is licenced in the same way as Eprover.  The installation instructions are the same as Eprover.

In order to use the Etableau proof search, invoke Eprover as usual, but with additional options.  "--tableau=1" enables tableaux proof search. "--tableau-depth=10" sets the maximum tableau depth to 10.  "--tableau-saturation=1" enables saturating certain branches of tableaux with Eprover's superposition proof search.  A tableau with all of its branches closed by Eprover or the classical tableau rules constitutes a proof.  

The master branch is intended to be a more stable version that works, while I am actively working on the devel branch and it may not work.

If you have any problems or suggestions, please email me at hesterj@ufl.edu.
