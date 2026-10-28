#!/usr/bin/env python3
"""Build or compare the classical five-hat SCIP model without running a solver."""

from __future__ import annotations

import argparse
from pathlib import Path


HATS = 5
INPUTS = range(1, (1 << HATS) - 1)
POSITIONS = range(HATS)
MONOCHROMATIC_WINS = 31
CLASSICAL_CEILING = 369


def hat_bit(word: int, position: int) -> int:
    """Positions are zero-based from the leftmost bit."""
    return (word >> (HATS - position - 1)) & 1


def constraint(
    name: str,
    positive: list[str],
    negative: list[str],
    relation: str,
    bound: int,
) -> str:
    terms = []
    for sign, variables in (("+", positive), ("-", negative)):
        for variable in variables:
            kind = "C" if variable.startswith("w_") else "B"
            terms.append(f"{sign}<{variable}>[{kind}]")
    expression = " ".join(terms).removeprefix("+")
    return f"  [linear] <{name}>: {expression} {relation} {bound};"


def build_model() -> str:
    lines = [
        "STATISTICS",
        "  Problem name     : levine_five_hats_unrestricted_classical",
        "  Variables        : 1200 (300 binary, 0 integer, 0 implicit integer, 900 continuous)",
        "  Constraints      : 0 initial, 2881 maximal",
        "OBJECTIVE",
        "  Sense            : maximize",
        f"  Offset           : +{MONOCHROMATIC_WINS}",
        "VARIABLES",
    ]
    for prefix in ("f", "g"):
        for observed in INPUTS:
            for position in POSITIONS:
                lines.append(
                    f"  [binary] <{prefix}_{observed}_{position}>: "
                    "obj=0, original bounds=[0,1]"
                )
    for x in INPUTS:
        for y in INPUTS:
            lines.append(f"  [continuous] <w_{x}_{y}>: obj=1, original bounds=[0,1]")

    lines.append("CONSTRAINTS")
    for party, prefix in (("alice", "f"), ("bob", "g")):
        for observed in INPUTS:
            choices = [f"{prefix}_{observed}_{position}" for position in POSITIONS]
            lines.append(constraint(f"{party}_one_hot_{observed}", choices, [], "==", 1))

    for x in INPUTS:
        for y in INPUTS:
            win = [f"w_{x}_{y}"]
            alice_black = [f"f_{y}_{a}" for a in POSITIONS if hat_bit(x, a)]
            bob_black = [f"g_{x}_{b}" for b in POSITIONS if hat_bit(y, b)]
            # The three inequalities force w to equal the AND of the selected colors.
            lines.append(constraint(f"win_le_alice_{x}_{y}", win, alice_black, "<=", 0))
            lines.append(constraint(f"win_le_bob_{x}_{y}", win, bob_black, "<=", 0))
            lines.append(
                constraint(f"win_ge_and_{x}_{y}", win, alice_black + bob_black, ">=", -1)
            )

    # Normalize Alice's output labels by first occurrence, without requiring
    # Alice and Bob to use the same response function. Appendix C justifies this symmetry.
    for y in INPUTS:
        for a in range(1, HATS):
            earlier = [f"f_{z}_{a - 1}" for z in range(1, y)]
            lines.append(
                constraint(f"alice_restricted_growth_{y}_{a}", [f"f_{y}_{a}"], earlier, "<=", 0)
            )

    # The published infinite-stack bound gives C <= floor(1 + 1020*81/224) = 369.
    wins = [f"w_{x}_{y}" for x in INPUTS for y in INPUTS]
    lines.append(
        constraint(
            "published_classical_ceiling_369_minus_31", wins, [], "<=",
            CLASSICAL_CEILING - MONOCHROMATIC_WINS,
        )
    )
    lines.append("END")
    return "\n".join(lines) + "\n"


def model_records(text: str) -> dict[str, tuple[str, ...]]:
    """Compare model records exactly, ignoring whitespace, declaration order, and statistics."""
    records: dict[str, list[str]] = {"OBJECTIVE": [], "VARIABLES": [], "CONSTRAINTS": []}
    section = "STATISTICS"
    ended = False
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if ended:
            raise ValueError("Unexpected content after END in the CIP model.")
        if stripped == "END":
            ended = True
        elif stripped in ("STATISTICS", *records):
            section = stripped
        elif section != "STATISTICS":
            records[section].append("".join(stripped.split()))
    if not ended or any(not values for values in records.values()):
        raise ValueError("The CIP model is incomplete.")
    return {name: tuple(sorted(values)) for name, values in records.items()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write a new CIP file; existing files are never overwritten")
    parser.add_argument("--check", type=Path, help="compare the generated model with a saved CIP file")
    args = parser.parse_args()
    if args.output is None and args.check is None:
        parser.error("specify --output PATH, --check PATH, or both")

    generated = build_model()
    try:
        if args.check is not None:
            saved = args.check.read_text(encoding="utf-8")
            actual, expected = model_records(generated), model_records(saved)
            differences = [name.lower() for name in actual if actual[name] != expected[name]]
            if differences:
                raise ValueError("Model mismatch in " + ", ".join(differences) + ".")
            print("Model matches: 1,200 variables and 2,881 constraints, with the same objective.")
        if args.output is not None:
            with args.output.open("x", encoding="utf-8") as stream:
                stream.write(generated)
            print(f"Wrote {args.output}")
    except (OSError, ValueError) as error:
        parser.exit(1, f"Model build/check failed: {error}\n")


if __name__ == "__main__":
    main()
