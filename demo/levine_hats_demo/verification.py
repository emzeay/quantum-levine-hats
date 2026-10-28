from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product

from . import four_hat, five_hat
from .hat_game import ClassicalStrategy, QuantumStrategy, bell_outcome_probability, hat_bit


@dataclass(frozen=True)
class VerificationResult:
    deals: int
    quantum_score: Fraction
    classical_score: Fraction

    @property
    def difference(self) -> Fraction:
        return self.quantum_score - self.classical_score


def exact_score(strategy: QuantumStrategy) -> Fraction:
    """Average the exact Bell-pair winning probability over every hat deal."""
    total = Fraction()
    for alice_hats, bob_hats in product(range(1 << strategy.hats), repeat=2):
        alice = strategy.action_for_observed(bob_hats, "alice")
        bob = strategy.action_for_observed(alice_hats, "bob")
        for alice_outcome, bob_outcome in product(range(2), repeat=2):
            alice_black = hat_bit(
                alice_hats, alice.position_for(alice_outcome), strategy.hats
            )
            bob_black = hat_bit(bob_hats, bob.position_for(bob_outcome), strategy.hats)
            if alice_black and bob_black:
                total += bell_outcome_probability(
                    alice.measurement, bob.measurement, alice_outcome, bob_outcome
                )
    return total / (1 << (2 * strategy.hats))


def _verify_strategy(
    strategy: QuantumStrategy,
    classical_play: ClassicalStrategy,
    expected_quantum: Fraction,
    expected_classical: Fraction,
) -> VerificationResult:
    deals = 1 << (2 * strategy.hats)
    quantum = exact_score(strategy)
    classical_wins = sum(
        classical_play(x, y)[2]
        for x, y in product(range(1 << strategy.hats), repeat=2)
    )
    classical = Fraction(classical_wins, deals)
    if quantum != expected_quantum or classical != expected_classical:
        raise ValueError(
            f"Verification failed for {strategy.hats} hats: "
            f"quantum={quantum} (expected {expected_quantum}), "
            f"classical={classical} (expected {expected_classical})"
        )
    return VerificationResult(deals, quantum, classical)


def verify_four_hat() -> VerificationResult:
    return _verify_strategy(
        four_hat.FourHatStrategy(),
        four_hat.classical_play,
        four_hat.RATIONAL_SCORE,
        four_hat.CLASSICAL_SCORE,
    )


def verify_five_hat() -> VerificationResult:
    return _verify_strategy(
        five_hat.FiveHatStrategy(),
        five_hat.classical_play,
        five_hat.RATIONAL_SCORE,
        five_hat.CLASSICAL_SCORE,
    )
