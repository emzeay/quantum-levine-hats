# Levine's hat game: a Cirq demonstration

This program demonstrates the paper's rational strategies using one Bell pair. It verifies their success probabilities for four and five hats and simulates games with randomly chosen hats.

For each game, Alice and Bob see the other player's hats, choose a local measurement when one is needed, measure their half of a Bell pair, and use the result to select one of two positions in their own stack.

Verification uses exact rational arithmetic over every possible hat deal to calculate the quantum strategy's success probability and the selected classical strategy's score. It does not establish the classical optimum. In the simulation, Cirq samples the quantum measurement outcomes.

## Install and run

Requires Python 3.11 or later.

From the repository root:

```bash
cd demo
python -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python hats_demo.py
```

With no flags, the program demonstrates four hats, starting with verification and then a simulation comparing the quantum and classical strategies on the same randomly generated hat deals.

The three flags are:

```text
--hats H       Hats per player. Defaults to 4.
--rounds [N]   Simulation rounds. Defaults for 4 or 5 hats, and is required for 6+ hats.
--seed S       Reproduce a simulation. If unspecified, a random seed is generated.
```

For one, two, or three hats, the program prints the banner reporting that no quantum advantage is possible, then stops. It does not use the round count or seed.

For four and five hats, verification runs before the simulation. Omitting `--rounds` or supplying it without a number uses the default count. The defaults are 393,320 rounds for four hats and 220,196 for five hats, chosen using a normal approximation to give roughly a 95% probability of strictly more quantum wins than classical wins. The classical opponents are an optimal $89/256$ strategy for four hats and the $358/1024$ witness for five hats. Note that a particular simulation can still favor the classical strategy.

For six or more hats, `--rounds N` is required. The program simulates the one-Bell-pair five-hat block strategy with the smaller-stack fallback and reports its observed score beside the analytic recurrence value. It does not make a classical comparison at those sizes.

When `--seed` is omitted, the program generates a seed from operating-system randomness. The simulation uses seeded pseudorandom generators and prints the seed so the run can be reproduced in the same software environment.

Examples:

```bash
.venv/bin/python hats_demo.py --hats 5
.venv/bin/python hats_demo.py --hats 7 --rounds 100000
.venv/bin/python hats_demo.py --hats 4 --rounds 100000 --seed 20261025
```
