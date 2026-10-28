from __future__ import annotations

from .verification import VerificationResult


def banner(hats: int) -> str:
    suffix = "s" if hats != 1 else ""
    if hats <= 3:
        note = "there is no quantum advantage!"
    elif hats == 4:
        note = "one Bell pair beats the *proven* classical optimum."
    elif hats == 5:
        note = "one Bell pair beats the *computed* classical optimum."
    else:
        note = "one Bell pair beats the *conjectured* classical optimum."
    return f"""
    __
  _|__|_
   LEVINE'S HAT GAME
   Quantum advantage demonstration for 2 players
   github.com/emzeay/quantum-levine-hats

For {hats} hat{suffix} per player, {note}"""


def print_verification(result: VerificationResult) -> None:
    print(f"Verification over all {result.deals:,} hat deals")
    print(
        f"  {'Quantum Bell-pair strategy:':<31}  "
        f"{str(result.quantum_score):>9} = {float(result.quantum_score):.9f}"
    )
    print(
        f"  {'Classical strategy:':<31}  "
        f"{str(result.classical_score):>9} = {float(result.classical_score):.9f}"
    )
    print(
        f"  {'Difference:':<31}  "
        f"{str(result.difference):>9} = {float(result.difference):.9f}"
    )


def print_comparison(
    rounds: int, seed: int, quantum_wins: int, classical_wins: int
) -> None:
    print(f"Simulation ({rounds:,} rounds | seed={seed})")
    print(
        f"  {'Quantum Bell-pair strategy:':<31}  "
        f"{quantum_wins:>9,} wins = {quantum_wins / rounds: .6f}"
    )
    print(
        f"  {'Classical strategy:':<31}  "
        f"{classical_wins:>9,} wins = {classical_wins / rounds: .6f}"
    )
    print(
        f"  {'Difference:':<31}  {quantum_wins - classical_wins:>+9,} wins = "
        f"{(quantum_wins - classical_wins) / rounds:+.6f}"
    )


def print_quantum_simulation(
    rounds: int, seed: int, wins: int, expected: float
) -> None:
    observed = wins / rounds
    print(f"Simulation ({rounds:,} rounds | seed={seed})")
    print(
        f"  {'Quantum Bell-pair strategy:':<31}  "
        f"{wins:>9,} wins = {observed: .6f}"
    )
    print(f"  {'Predicted success probability:':<31}  {expected:>26.6f}")
    print(f"  {'Observed minus predicted:':<31}  {observed - expected:>+26.6f}")


def print_elapsed(elapsed: float, rounds: int | None = None) -> None:
    suffix = f" | Rounds/sec: {rounds / elapsed:,.0f}" if rounds is not None else ""
    print(f"  Elapsed: {elapsed:.2f} s{suffix}")
