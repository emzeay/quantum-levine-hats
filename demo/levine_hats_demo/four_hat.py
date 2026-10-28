from __future__ import annotations

from fractions import Fraction
from .hat_game import LocalAction, Measurement, Party, hat_bit


RATIONAL_SCORE = Fraction(1517, 4352)
CLASSICAL_SCORE = Fraction(89, 256)
DEFAULT_ROUNDS = 393_320

ALICE_MEASUREMENTS = (
    Measurement("A0", Fraction(15, 17), Fraction(-8, 17)),
    Measurement("A1", Fraction(-1), Fraction(0)),
    Measurement("A2", Fraction(15, 17), Fraction(8, 17)),
)
BOB_MEASUREMENTS = (
    Measurement("B0", Fraction(1), Fraction(0)),
    Measurement("B1", Fraction(0), Fraction(1)),
)
# Tables are indexed by observed words in binary order. Pairs list zero-based
# positions for the +1 and -1 outcomes; equal positions ignore the measurement.
ALICE_SETTINGS = (
    0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0,
)
ALICE_PAIRS = (
    (0, 0), (3, 3), (2, 2), (2, 2),
    (0, 1), (1, 3), (0, 2), (3, 2),
    (1, 0), (1, 3), (0, 2), (2, 3),
    (0, 0), (1, 1), (0, 0), (0, 0),
)
BOB_SETTINGS = (
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
)
BOB_PAIRS = (
    (0, 0), (3, 3), (2, 2), (2, 3),
    (1, 0), (3, 3), (1, 0), (3, 3),
    (0, 1), (0, 1), (2, 2), (2, 2),
    (1, 0), (0, 1), (1, 0), (0, 0),
)


class FourHatStrategy:
    hats = 4

    def action_for_observed(self, observed: int, party: Party) -> LocalAction:
        if party == "alice":
            settings, pairs, measurements = ALICE_SETTINGS, ALICE_PAIRS, ALICE_MEASUREMENTS
        else:
            settings, pairs, measurements = BOB_SETTINGS, BOB_PAIRS, BOB_MEASUREMENTS
        plus_position, minus_position = pairs[observed]
        return LocalAction(measurements[settings[observed]], plus_position, minus_position)

    def expected_probability(self) -> float:
        return float(RATIONAL_SCORE)


def classical_play(alice_hats: int, bob_hats: int) -> tuple[int, int, bool]:
    """The optimal classical assignment fixes A1 to -1 and all other settings to +1."""
    alice = FourHatStrategy().action_for_observed(bob_hats, "alice")
    bob = FourHatStrategy().action_for_observed(alice_hats, "bob")
    alice_outcome = int(alice.measurement.name == "A1")
    bob_outcome = 0
    a_position = alice.position_for(alice_outcome)
    b_position = bob.position_for(bob_outcome)
    won = bool(hat_bit(alice_hats, a_position, 4) and hat_bit(bob_hats, b_position, 4))
    return a_position, b_position, won
