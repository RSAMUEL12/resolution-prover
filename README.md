# Resolution Proof Solver using Prolog

This project is interlinked with my Logic and Verification module and focusing on the sub-topic of Proof systems such as the Semantic Tableau and Resolution Proof.
A resolution proof is a proof mechanic that takes in a propositional formula and determines whether it is a tautology.
The proof occurs by taking the negation of the formula and checking if it is a contradiction, and if so, will produce an empty clause in the CNF format.

In order to run the program, use SWI-Prolog or the online IDE Swish.
Call the main function test(X) where X is the user input of a formula in the form: (neg) a and/or/imp/reimp/equiv (neg) b.
The output will be either YES, if a proof exists, or NO.
