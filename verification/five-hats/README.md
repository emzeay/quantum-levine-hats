# Five-hat classical optimization

These files record the classical five-hat optimization described in Appendix C of the [paper](../../paper.pdf). Alice and Bob may use different deterministic response functions, each mapping the observed hats to a position in their own stack.

[SCIP](https://www.scipopt.org/) 10.0.2, invoked through PySCIPOpt, terminated with status `optimal`, reporting matching lower and upper bounds of 358 winning deals out of 1,024. The run took about 2 hours 28 minutes for me and processed 445,277 nodes.

## Files

- [check_witness.py](check_witness.py): enumerates all deals to check the saved strategy's score.
- [build_model.py](build_model.py): builds the optimization model in SCIP's CIP format and compares it with the saved export.
- [model.cip](model.cip) and [model.mps](model.mps): exported SCIP optimization models.
- [solver-settings.set](solver-settings.set): nondefault settings used in the recorded run.
- [best-solution.sol](best-solution.sol): SCIP's saved solution.
- [best-strategy.json](best-strategy.json): the corresponding response functions.
- [result.json](result.json) and [run-metadata.json](run-metadata.json): final outcome, version, scope, and resource information.
- [solver.log](solver.log): the recorded SCIP solver log.

In [best-strategy.json](best-strategy.json), array entries correspond to observed strings from `00000` through `11111` in binary order. Positions are zero-based, with position 0 referring to the leftmost hat. The paper uses one-based positions.

The model has 300 binary assignment variables and 900 continuous win variables. Its symmetry reduction removes only equivalent relabelings of Alice's physical hat positions. It does not impose equality between Alice's and Bob's response functions.

The model also includes a valid upper bound of 369 wins, derived from the published infinite-stack classical bound of $81/224$. Appendix C explains this deduction and the symmetry reduction.

## Check the witness and model

Both scripts require Python 3.10 or later and use only the standard library. From the repository root:

```sh
cd verification/five-hats
python3 check_witness.py
python3 build_model.py --check model.cip
```

The witness checker reads [best-strategy.json](best-strategy.json) and verifies exactly 358 wins out of 1,024 deals. It does not check the classical upper bound.

The model check compares the generated objective, variable types and bounds, and every constraint with the saved CIP export. It ignores whitespace, declaration order, and the statistics header. It does not run SCIP.

To write a fresh model in a temporary directory and check it against the recorded export:

```sh
model_dir=$(mktemp -d)
python3 build_model.py --output "$model_dir/model.cip" --check model.cip
```

The builder refuses to overwrite existing files. It is a standalone reconstruction of the formulation, not the original PySCIPOpt runner identified by the hash in [run-metadata.json](run-metadata.json).

## Reproduce the optimization

With the SCIP command-line executable installed, start its interactive shell from this directory. From the repository root:

```sh
cd verification/five-hats
scip
```

Enter these commands in the SCIP shell to load the saved settings, model, and solution, then run the optimization:

```text
set load solver-settings.set
read model.cip
read best-solution.sol
optimize
display statistics
quit
```

These commands use SCIP directly, so PySCIPOpt is not required. See SCIP's [interactive-shell documentation](https://www.scipopt.org/doc/html/SHELL.php) for details. The recorded run used SCIP 10.0.2. Runtime and search details can vary between versions, builds, and machines, even with the saved settings and solution.

## Status

Exact enumeration verifies that the saved strategy wins 358 of the 1,024 deals. The upper bound relies on SCIP's floating-point computation. An independently checkable exact certificate is not included, and the five-hat optimum has not been formalized in Lean.
