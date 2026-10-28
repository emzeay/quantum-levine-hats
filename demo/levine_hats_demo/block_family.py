from __future__ import annotations

from fractions import Fraction

from .four_hat import FourHatStrategy
from .five_hat import FiveHatStrategy, RATIONAL_SCORE as FIVE_SCORE
from .hat_game import LocalAction, Measurement, Party


SMALL_SCORES = {1: Fraction(1, 4), 2: Fraction(5, 16), 3: Fraction(11, 32)}
TWO_HAT_POSITIONS = (0, 1, 0, 0)
THREE_HAT_POSITIONS = (0, 0, 1, 0, 2, 2, 1, 0)
FALLBACK_MEASUREMENT = Measurement("fallback", Fraction(1), Fraction(0))


class BlockFamilyStrategy:
    """The rational five-hat block construction with smaller-stack fallbacks."""

    def __init__(self, hats: int):
        if hats < 1:
            raise ValueError("hats must be positive")
        self.hats = hats
        self._four = FourHatStrategy()
        self._five = FiveHatStrategy()

    def action_for_observed(self, observed: int, party: Party) -> LocalAction:
        hats = self.hats
        offset = 0
        while hats > 5:
            first_block = observed >> (hats - 5)
            if first_block not in (0, 31):
                action = self._five.action_for_observed(first_block, party)
                break
            # Skipping a block only changes the hat offset; the Bell pair is untouched.
            hats -= 5
            observed &= (1 << hats) - 1
            offset += 5
        else:
            action = self._base_action(hats, observed, party)
        return LocalAction(
            action.measurement,
            action.plus_position + offset,
            action.minus_position + offset,
        )

    def _base_action(self, hats: int, observed: int, party: Party) -> LocalAction:
        if hats == 1:
            return LocalAction(FALLBACK_MEASUREMENT, 0, 0)
        if hats == 2:
            position = TWO_HAT_POSITIONS[observed]
            return LocalAction(FALLBACK_MEASUREMENT, position, position)
        if hats == 3:
            position = THREE_HAT_POSITIONS[observed]
            return LocalAction(FALLBACK_MEASUREMENT, position, position)
        if hats == 4:
            return self._four.action_for_observed(observed, party)
        return self._five.action_for_observed(observed, party)

    def expected_probability(self) -> float:
        blocks, remaining = divmod(self.hats - 1, 5)
        base_hats = remaining + 1
        if base_hats <= 3:
            score = float(SMALL_SCORES[base_hats])
        elif base_hats == 4:
            score = self._four.expected_probability()
        else:
            score = float(FIVE_SCORE)
        for _ in range(blocks):
            score = float(FIVE_SCORE) - 1 / 1024 + score / 256
        return score
