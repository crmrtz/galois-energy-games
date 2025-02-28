# Galois energy games

This is my master's thesis, written at the Technical University of Berlin.

Building on Benjamin Bisping's research, we study (multi-weighted) energy games with reachability winning conditions. These are zero-sum two-player games with perfect information played on directed graphs labelled by (multi-weighted) energy functions. Bisping introduced a generalisation of the bisimulation game to decide all common notions of behavioural equivalence at once. While he claims decidability and provides an algorithm to compute minimal attacker winning budgets (i.e. Pareto fronts), the claim lacks a formal proof. Using Isabelle/HOL, we provide a machine-checked proof to substantiate Bisping’s claim of decidability.

The Isabelle theories are in the accordingly named folder and were further developed since submission. The accompanying PDFs are built from the theories originally submitted and present the formal proofs. This master's thesis provides an overview of the results and contextualises them within the research. Furthermore, we abstract the necessary properties used in the proof and introduce new classes of energy games, named (generalised) Galois energy games. Simplifying and generalising Bisping's algorithm we prove the decidability of these classes, assuming that the set of positions is finite and the energies form a well-founded bounded join-semilattice.

Despite the original title of the master's thesis ("A Formal Proof of Decidability of Multi-weighted Declining Energy Games") we study energy games with reachability winning conditions extensively. In particular, we are able to show decidability for energy games that are not declining, concluding that monotonicity plays the key role. However, declining energy games result in significantly better running times, which in some fixed-dimension cases are polynomial. By providing new decidability results, this work strengthens the theoretical foundations of multi-weighted energy games.

