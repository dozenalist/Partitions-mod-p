# Partitions mod p

The primary goal of this project was to formalize the first section of [this paper](https://people.math.sc.edu/boylan/reprints/nomoreramafinal.pdf) by Ahlgren and Boylan on the congurences of the partition function modulo a prime. This goal has been completed, and we are now trying to formalize some of the theorems prior to this paper, as well as information about Modular Forms Mod ℓ more generally.

You can find an overview of the definitions and theorems [here](https://dozenalist.github.io/Partitions-mod-p/)

Formalized : 

- The Definitions of Modular Forms, Integer Modular Forms, and Modular Forms Mod ℓ
  - Modular Forms are functions on the complex plane that satisfy a number of conditions. They have a natural number weight k. 
  - Integer Modular Forms are sequences to the Integers whose infinite q-series is a Modular Form. They have a natural number weight k.
  - Modular Forms Mod ℓ are sequences to ZMod ℓ such that there exists an Integer Modular Form that reduces to this sequence (mod ℓ). They have a weight that is of type ZMod (ℓ - 1). This is because we can only       add and subtract Modular Forms Mod ℓ whose weights are congruent (mod ℓ - 1).

- The Definitions of addition and multiplication between Modular Forms and exponentiation of Modular Forms
  - For regular Modular Forms, these are the standard definitions, but Integer Modular Forms and Modular Forms Mod ℓ are trickier, because we have to think of the sequence that results from multiplication of the      overall q-series (which is hidden from the definition). We can multiply two Modular Forms of any weight, and their weights add, but we can only add Modular Forms of the same weight. 

- The definitions of the Theta and U operators, both of which act on Modular Forms Mod ℓ

- The definition of the Filtration of a Modular Form Mod ℓ (call it b) as the least natural number such that b has that weight. Unlike in the paper, the Filtration of the zero function is zero.

- The definitions of δℓ as a natural number and of Δ and fℓ as Modular Forms of their respective weights, as well as the Eisenstein series.

- Information about a basis for the space of Modular Forms. Specifically, the normalized, upper triangular basis consisting of powers of E4, E6, and Delta.

- All of the main results of the paper. Everything from the beginning to the end of the proof of Theorem 1 is fully formalized, assuming some preliminaries.



TODO : 

- Prove that Integer Modular Forms and Modular Forms Mod ℓ form a graded ring. (i.e. fill in the sorries on the definitions of add, mul, and pow of these structures).

- Prove that the Theta and U operators preserve modularity.

- Prove lemma 2.1

- Prove that if two Modular Forms Mod ℓ are equal, then their weights are congruent (mod ℓ - 1)

- Prove that Δ and the Eisenstein series are Modular Forms.

- Prove that the basis used actually forms a basis for the space of Modular Forms

- Prove the Filtration Log property.


Note : 

Much of this project is written in the language of == and Mcongr. 

Often it’s necessary to prove something of the form a = b, where a : ModularFormMod ℓ k, and b : ModularFormMod ℓ (k + 0).
In lean, trying to assert a = b throws an error, because a and b dont have the same type, and equality only works between elements of the same type. 

To get around this, we can assert that a == b, meaning that for all n, a n = b n, or in other words that a and b are the same underlying sequence. I’ve proved that, for most of the things we’d like to use it for, == acts like = .

We can also assert that a = Mcongr b (h : k + 0 = k), where Mcongr casts the type of b to match the type of a, given a proof that these two types are equal. 

When adding or subtracting two Modular Forms whose types are technically different but provably equal, we can use, for example, a +r b (h : (the weight of a) = (the weight of b) ) in which the sum here inherits the type of b, given a proof that the two types are equal. 

