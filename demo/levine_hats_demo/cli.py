from __future__ import annotations

import argparse
import secrets
import time

import numpy as np

from . import four_hat, five_hat
from .block_family import BlockFamilyStrategy
from .cirq_simulator import BellPairSimulator
from .hat_game import ClassicalStrategy, QuantumStrategy
from .terminal_output import (
    banner,
    print_comparison,
    print_elapsed,
    print_quantum_simulation,
    print_verification,
)
from .verification import verify_four_hat, verify_five_hat


def random_hat_word(hats: int, rng: np.random.Generator) -> int:
    return int.from_bytes(rng.bytes((hats + 7) // 8), "big") & ((1 << hats) - 1)


def run_comparison(
    strategy: QuantumStrategy,
    classical_play: ClassicalStrategy,
    rounds: int,
    seed: int | None,
) -> None:
    seed = secrets.randbits(64) if seed is None else seed
    rng = np.random.default_rng(seed)
    limit = 1 << strategy.hats
    deals = [(int(rng.integers(limit)), int(rng.integers(limit))) for _ in range(rounds)]
    quantum = BellPairSimulator(rng).play(strategy, deals)
    classical_wins = sum(classical_play(*deal)[2] for deal in deals)
    print_comparison(rounds, seed, sum(result.won for result in quantum), classical_wins)


def run_family(hats: int, rounds: int, seed: int | None) -> None:
    seed = secrets.randbits(64) if seed is None else seed
    rng = np.random.default_rng(seed)
    strategy = BlockFamilyStrategy(hats)
    deals = [(random_hat_word(hats, rng), random_hat_word(hats, rng)) for _ in range(rounds)]
    results = BellPairSimulator(rng).play(strategy, deals)
    print_quantum_simulation(
        rounds, seed, sum(result.won for result in results), strategy.expected_probability()
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="A Cirq demonstration of one-Bell-pair strategies in Levine's hat game."
    )
    parser.add_argument(
        "--hats", type=int, default=4, metavar="H",
        help="number of hats per player; defaults to 4",
    )
    parser.add_argument(
        "--rounds", type=int, nargs="?", const=-1, metavar="N",
        help="simulate N random deals; without N, uses the 95%% default for 4 or 5 hats",
    )
    parser.add_argument(
        "--seed", type=int,
        help="reproducible seed; omit it to seed from operating-system randomness",
    )
    args = parser.parse_args()
    if args.hats <= 0:
        parser.error("--hats must be positive")
    if args.rounds is not None and args.rounds != -1 and args.rounds <= 0:
        parser.error("--rounds must be positive")

    print(banner(args.hats))
    if args.hats <= 3:
        return
    if args.rounds is None or args.rounds == -1:
        if args.hats >= 6:
            parser.error("--rounds N is required for 6 or more hats")
        rounds = four_hat.DEFAULT_ROUNDS if args.hats == 4 else five_hat.DEFAULT_ROUNDS
    else:
        rounds = args.rounds

    if args.hats in (4, 5):
        if args.hats == 4:
            strategy = four_hat.FourHatStrategy()
            classical_play = four_hat.classical_play
            verify = verify_four_hat
        else:
            strategy = five_hat.FiveHatStrategy()
            classical_play = five_hat.classical_play
            verify = verify_five_hat

        print()
        start = time.perf_counter()
        print_verification(verify())
        print_elapsed(time.perf_counter() - start)
        print()
        start = time.perf_counter()
        run_comparison(strategy, classical_play, rounds, args.seed)
        print_elapsed(time.perf_counter() - start, rounds)
    else:
        start = time.perf_counter()
        run_family(args.hats, rounds, args.seed)
        print_elapsed(time.perf_counter() - start, rounds)
