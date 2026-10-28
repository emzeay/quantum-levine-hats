# Computational verification

This directory contains the model, solver output, and classical strategy from the five-hat computation.

## Four hats

The unrestricted classical four-hat upper bound is formalized in [LevineHats/ClassicalCertificate.lean](../LevineHats/ClassicalCertificate.lean). It is therefore kept with the Lean source rather than duplicated here.

## Five hats

The [five-hats](five-hats/README.md) directory contains an optimization model allowing different deterministic strategies for Alice and Bob. [SCIP](https://www.scipopt.org/) 10.0.2 reports matching lower and upper bounds of 358 winning deals out of 1,024.

Exhaustive enumeration verifies that the included strategy wins exactly 358 deals. The claim that no strategy wins more relies on SCIP's floating-point computation. An independently checkable exact certificate is not included at this time; let's see if I can get one to generate on my machine in a reasonable time...

See the [subdirectory's README](five-hats/README.md) for file descriptions and the recorded run details, and Appendix C of the [paper](../paper.pdf) for the mathematical formulation.
