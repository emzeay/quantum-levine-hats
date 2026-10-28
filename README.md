# Quantum strategies for Levine's hat game

This repository accompanies a paper on quantum strategies for Levine's hat game using one Bell pair. It includes Lean 4 proofs, a Cirq demo, and files for reproducing a classical five-hat optimization.

## Main result

Alice and Bob each wear a stack of hats, independently colored black or white by fair coin flips. Alice sees Bob's stack and Bob sees Alice's. They agree on a strategy before the hats are chosen, then each selects a position in their own stack without communicating. They win if both selected hats are black.

For four hats per player, Alice and Bob share one Bell pair and succeed with probability

$$
\frac{1517}{4352} = 0.348575368\ldots > \frac{89}{256} = 0.34765625,
$$

where $89/256$ is the unrestricted classical optimum. The gap is $1/1088$.

For five hats per player, the quantum strategy succeeds with probability $1463/4160$. [SCIP](https://www.scipopt.org/) reports a classical optimum of $358/1024$, providing computational evidence for a quantum advantage without an independent exact certificate. The paper also constructs strategies for larger finite stacks and infinite stacks that exceed the conjectured classical ceiling of $7/20$.

## Read, check, or run

- Read the mathematical account in [paper.pdf](paper.pdf).
- Build the Lean 4 development in [LevineHats.lean](LevineHats.lean).
- Run the Bell-pair simulation in the [demo](demo/README.md).
- Inspect the five-hat computational evidence in [verification](verification/README.md).

## Lean verification

The project pins Lean 4 and mathlib through `lean-toolchain` and `lake-manifest.json`. With Lean and `elan` installed, run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The Lean development formalizes the four-hat strategy and its extensions using four-hat blocks, including padding to arbitrary finite sizes and an infinite-stack construction. The paper's five-hat strategy, five-hat recurrence, and measurement refinements are not included in the formalization.

The four-hat classical upper bound is computed through Lean's `bv_decide` mechanism in [LevineHats/ClassicalCertificate.lean](LevineHats/ClassicalCertificate.lean). Its trust boundary includes Lean's compiled runtime, so it is not a kernel-only certificate. `Audit.lean` prints the axioms of the principal declarations.

## Acknowledgments

Levine’s hat game originates with Lionel Levine. The strategies build on earlier classical work and biased CHSH correlations. References and detailed attribution appear in the paper.

This project used OpenAI’s Codex for exploration, Lean formalization, and initial drafting. The paper was curated and revised by the author.

## License

Source and documentation are licensed under the [Apache License, Version 2.0](LICENSE).
