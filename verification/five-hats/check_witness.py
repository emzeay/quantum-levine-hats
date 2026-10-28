#!/usr/bin/env python3
"""Check the saved classical five-hat strategy by enumerating all 1,024 deals."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


HATS = 5
WORDS = tuple(f"{value:05b}" for value in range(1 << HATS))
EXPECTED_WINS = 358
DEFAULT_WITNESS = Path(__file__).with_name("best-strategy.json")


def check_witness(path: Path) -> int:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("The witness must be a JSON object.")

    for party in ("alice", "bob"):
        positions = data.get(party)
        if not isinstance(positions, list) or len(positions) != len(WORDS):
            raise ValueError(f"{party}: expected one position for each of the 32 inputs.")
        if any(type(position) is not int or not 0 <= position < HATS for position in positions):
            raise ValueError(f"{party}: positions must be integers from 0 through 4.")

    # Alice's response is indexed by Bob's hats, and Bob's by Alice's hats.
    wins = sum(
        alice_word[data["alice"][y]] == "1" and bob_word[data["bob"][x]] == "1"
        for x, alice_word in enumerate(WORDS)
        for y, bob_word in enumerate(WORDS)
    )
    deals = len(WORDS) ** 2
    if type(data.get("deals")) is not int or data["deals"] != deals:
        raise ValueError(f"The recorded deal count must be {deals}.")
    if type(data.get("wins")) is not int or data["wins"] != wins:
        raise ValueError(f"The recorded win count does not match the enumeration ({wins}).")
    if wins != EXPECTED_WINS:
        raise ValueError(f"Expected the {EXPECTED_WINS}-win witness, but counted {wins} wins.")
    return wins


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "witness", type=Path, nargs="?", default=DEFAULT_WITNESS,
        help="strategy JSON file; defaults to best-strategy.json beside this script",
    )
    args = parser.parse_args()
    try:
        wins = check_witness(args.witness)
    except (OSError, ValueError) as error:
        parser.exit(1, f"Witness check failed: {error}\n")
    print(f"Verified: {wins} wins out of {len(WORDS) ** 2:,} deals.")
    print("This checks an attaining strategy, not the classical upper bound.")


if __name__ == "__main__":
    main()
