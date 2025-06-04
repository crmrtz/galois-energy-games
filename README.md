# Galois energy games

This repository contains an Isabelle/HOL proof of decidability of Galois energy games and as well as a formal proof of decidability of monotonic energy games.
The Isabelle theories are an enhancement of the theories developed as part of the master's thesis "A Formal Proof of Decidability of Multi-weighted Declining Energy Games" written by Caroline Lemke at the Technical University of Berlin. 

## Structure of the Repository

- **`/isabelle-theories`**: This folder contains the current Isabelle theories and the documents built from these. The latter presents the Isabelle/HOL proofs.
  
- **`/master-thesis`**: This folder contains the master's thesis as well as the originally submitted isabelle theories and the corresponding documents built. These files correspond to the version of the formalisation the master's thesis references.

## Overview

Building on Benjamin Bisping's research, we study (multi-weighted) energy games with reachability winning conditions. These are zero-sum two-player games with perfect information played on directed graphs labelled by (multi-weighted) energy functions. Bisping introduced a generalisation of the bisimulation game to decide all common notions of behavioural equivalence at once. While he claims decidability and provides an algorithm to compute minimal attacker winning budgets (i.e. Pareto fronts), the claim lacks a formal proof. Using Isabelle/HOL, we provide a machine-checked proof to substantiate Bisping’s claim of decidability.

We abstract the necessary properties used in the proof and introduce new classes of energy games: Galois energy games.
In such games updates can be undone through Galois connections, yielding a weakened form of inversion sufficient for an algorihm similar to standard shortest path algorithms. 
Simplifying and generalising Bisping's algorithm we prove the decidability for Galois energy games over well-founded bounded join-semilattices with a finite set of positions.
In particular Galois energy games over vectors of (extended) naturals with the component-wise order are decidable. We show that Bisping's declining energy games as well as energy games with vector addition are such Galois energy games and are thus decidable.

Generalising the algorithm and the accompanying proofs even further, we obtain decidability results for an even larger class of energy games: monotonic energy games. These results are presented in the master's thesis only.


### Important Note: Theories have evolved

Since the submission of the thesis, the Isabelle formalisation has undergone further development. The master's thesis provides an overview of the originally formalised results. This means that the Isabelle theories in this repository have evolved and expanded beyond what was presented in the thesis.

