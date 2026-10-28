from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction
from typing import Literal, Protocol


Party = Literal["alice", "bob"]
ClassicalStrategy = Callable[[int, int], tuple[int, int, bool]]


@dataclass(frozen=True)
class Measurement:
    """A real qubit observable zZ + xX, with exact rational coefficients."""

    name: str
    z: Fraction
    x: Fraction


@dataclass(frozen=True)
class LocalAction:
    """A measurement and zero-based hat positions for its +1 and -1 outcomes."""

    measurement: Measurement
    plus_position: int
    minus_position: int

    def position_for(self, outcome: int) -> int:
        """Cirq's bits 0 and 1 represent eigenvalues +1 and -1, respectively."""
        return (self.plus_position, self.minus_position)[outcome]


@dataclass(frozen=True)
class RoundResult:
    alice_position: int
    bob_position: int
    won: bool


class QuantumStrategy(Protocol):
    hats: int

    def action_for_observed(self, observed: int, party: Party) -> LocalAction: ...

    def expected_probability(self) -> float: ...


def hat_bit(word: int, position: int, hats: int) -> int:
    """Read a zero-based position from the leftmost (most significant) bit."""
    return (word >> (hats - position - 1)) & 1


def bell_outcome_probability(
    alice: Measurement,
    bob: Measurement,
    alice_outcome: int,
    bob_outcome: int,
) -> Fraction:
    """Exact outcome probability on Phi+, whose X/Z correlation is a dot product."""
    sign = (1, -1)
    correlation = alice.z * bob.z + alice.x * bob.x
    return (1 + sign[alice_outcome] * sign[bob_outcome] * correlation) / 4
