from __future__ import annotations

from fractions import Fraction
from .hat_game import LocalAction, Measurement, Party, hat_bit


RATIONAL_SCORE = Fraction(1463, 4160)
CLASSICAL_SCORE = Fraction(358, 1024)
DEFAULT_ROUNDS = 220_196

ALICE_MEASUREMENTS = (
    Measurement("A0", Fraction(0), Fraction(1)),
    Measurement("A1", Fraction(1), Fraction(0)),
    Measurement("A2", Fraction(3, 5), Fraction(4, 5)),
    Measurement("A3", Fraction(4, 5), Fraction(-3, 5)),
    Measurement("A4", Fraction(4, 5), Fraction(3, 5)),
    Measurement("A5", Fraction(5, 13), Fraction(-12, 13)),
    Measurement("A6", Fraction(5, 13), Fraction(12, 13)),
)
BOB_MEASUREMENTS = (
    Measurement("B0", Fraction(0), Fraction(1)),
    Measurement("B1", Fraction(1), Fraction(0)),
    Measurement("B2", Fraction(3, 5), Fraction(-4, 5)),
    Measurement("B3", Fraction(4, 5), Fraction(-3, 5)),
    Measurement("B4", Fraction(4, 5), Fraction(3, 5)),
    Measurement("B5", Fraction(5, 13), Fraction(-12, 13)),
    Measurement("B6", Fraction(5, 13), Fraction(12, 13)),
)
# Tables use binary input order and zero-based positions, as in the four-hat table.
ALICE_SETTINGS = (
    1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 3, 4, 1,
    1, 2, 3, 0, 1, 1, 1, 1, 1, 6, 5, 0, 1, 0, 0, 1,
)
ALICE_PAIRS = (
    (0, 0), (0, 0), (3, 3), (3, 0),
    (2, 2), (2, 2), (2, 2), (2, 2),
    (1, 1), (1, 0), (3, 1), (3, 0),
    (2, 1), (2, 1), (2, 1), (2, 0),
    (4, 4), (4, 0), (4, 3), (3, 0),
    (4, 2), (4, 2), (4, 2), (4, 2),
    (1, 1), (1, 0), (1, 3), (3, 0),
    (1, 1), (1, 4), (3, 1), (0, 0),
)
BOB_SETTINGS = (
    1, 1, 1, 2, 1, 1, 0, 5, 1, 1, 1, 1, 1, 1, 4, 0,
    1, 4, 0, 0, 0, 6, 0, 0, 1, 1, 1, 1, 3, 0, 1, 1,
)
BOB_PAIRS = (
    (0, 0), (0, 0), (3, 3), (0, 3),
    (2, 2), (2, 2), (3, 2), (2, 3),
    (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 2), (2, 2), (1, 2), (0, 2),
    (4, 4), (0, 4), (3, 4), (3, 4),
    (2, 4), (2, 4), (3, 4), (3, 4),
    (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 2), (2, 4), (1, 3), (0, 0),
)
CLASSICAL_ALICE = (
    0, 0, 1, 0, 2, 0, 2, 0, 3, 0, 3, 0, 3, 0, 3, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 0, 3, 4, 3, 0,
)
CLASSICAL_BOB = (
    0, 0, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    4, 4, 1, 1, 4, 4, 1, 1, 4, 4, 3, 0, 4, 4, 3, 0,
)


class FiveHatStrategy:
    hats = 5

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
    a_position = CLASSICAL_ALICE[bob_hats]
    b_position = CLASSICAL_BOB[alice_hats]
    won = bool(hat_bit(alice_hats, a_position, 5) and hat_bit(bob_hats, b_position, 5))
    return a_position, b_position, won
