# Partitions mod p

The primary goal of this project was to formalize the first section of [this paper](https://people.math.sc.edu/boylan/reprints/nomoreramafinal.pdf) by Ahlgren and Boylan on the congurences of the partition function modulo a prime. This goal has been completed, and we are now trying to formalize some of the theorems prior to this paper, as well as information about Modular Forms Mod ℓ more generally.

You can find an overview of the definitions and theorems [here](https://dozenalist.github.io/Partitions-mod-p/)

[Graph of Delarations](https://dozenalist.github.io/Partitions-mod-p/dep_graph_document.html)

Formalized : 

- Everything is done. The main theorem is proved with a sorry-free connection down to the axioms.

- The Definitions of Modular Forms, Integer Modular Forms, and Modular Forms Mod ℓ
  - Modular Forms are functions on the complex plane that satisfy a number of conditions. They have a natural number weight k. 
  - Integer Modular Forms are sequences to the Integers whose infinite q-series is a Modular Form. They have a natural number weight k.
  - Modular Forms Mod ℓ are sequences to ZMod ℓ such that there exists an Integer Modular Form that reduces to this sequence (mod ℓ). They have a weight that is of type ZMod (ℓ - 1). This is because we can only add and subtract Modular Forms Mod ℓ whose weights are congruent (mod ℓ - 1).

- The Definitions of addition and multiplication between Modular Forms and exponentiation of Modular Forms
  - For regular Modular Forms, these are the standard definitions, but Integer Modular Forms and Modular Forms Mod ℓ are trickier, because we have to think of the sequence that results from multiplication of the overall q-series (which is hidden from the definition). We can multiply two Modular Forms of any weight, and their weights add, but we can only add Modular Forms of the same weight. 

- The definitions of the Theta and U operators, both of which act on Modular Forms Mod ℓ

- The definition of the Filtration of a Modular Form Mod ℓ (call it b) as the least natural number such that b has that weight. Unlike in the paper, the Filtration of the zero function is zero.

- The definitions of δℓ as a natural number and of Δ and fℓ as Modular Forms of their respective weights, as well as the Eisenstein series.

- Information about a basis for the space of Modular Forms. Specifically, the normalized, upper triangular basis consisting of powers of E4, E6, and Delta.

- All of the main results of the paper.



TODO : 

· Prove the Kimming and Olson result?

· Generalize to more subrings of C and more subgroups of GL(2,R)


