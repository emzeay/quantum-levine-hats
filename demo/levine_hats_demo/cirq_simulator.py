from __future__ import annotations

from collections import defaultdict

import cirq
import numpy as np

from .hat_game import LocalAction, Measurement, QuantumStrategy, RoundResult, hat_bit


class BellPairSimulator:
    """Samples a fresh Bell pair per deal, batching deals with the same measurements."""

    def __init__(self, rng: np.random.Generator):
        self._simulator = cirq.Simulator(seed=int(rng.integers(2**32)))
        self._circuits: dict[tuple[Measurement, Measurement], cirq.Circuit] = {}

    def play(
        self, strategy: QuantumStrategy, deals: list[tuple[int, int]]
    ) -> list[RoundResult]:
        grouped: dict[tuple[Measurement, Measurement], list[int]] = defaultdict(list)
        actions: list[tuple[LocalAction, LocalAction]] = []
        for index, (alice_hats, bob_hats) in enumerate(deals):
            alice = strategy.action_for_observed(bob_hats, "alice")
            bob = strategy.action_for_observed(alice_hats, "bob")
            actions.append((alice, bob))
            grouped[alice.measurement, bob.measurement].append(index)

        outcomes: list[tuple[int, int] | None] = [None] * len(deals)
        # Batch circuit repetitions, then restore the original deal order.
        for measurements, indices in grouped.items():
            result = self._simulator.run(
                self._circuit(*measurements), repetitions=len(indices)
            )
            alice_bits = result.measurements["alice"].reshape(-1)
            bob_bits = result.measurements["bob"].reshape(-1)
            for index, alice_outcome, bob_outcome in zip(
                indices, alice_bits, bob_bits
            ):
                outcomes[index] = (int(alice_outcome), int(bob_outcome))

        results: list[RoundResult] = []
        for (alice_hats, bob_hats), (alice, bob), outcome in zip(deals, actions, outcomes):
            assert outcome is not None
            a_position = alice.position_for(outcome[0])
            b_position = bob.position_for(outcome[1])
            won = bool(
                hat_bit(alice_hats, a_position, strategy.hats)
                and hat_bit(bob_hats, b_position, strategy.hats)
            )
            results.append(RoundResult(a_position, b_position, won))
        return results

    def _circuit(self, alice: Measurement, bob: Measurement) -> cirq.Circuit:
        key = (alice, bob)
        if key not in self._circuits:
            a, b = cirq.LineQubit.range(2)
            self._circuits[key] = cirq.Circuit(
                cirq.H(a),
                cirq.CNOT(a, b),
                self._basis_change(alice).on(a),
                self._basis_change(bob).on(b),
                cirq.measure(a, key="alice"),
                cirq.measure(b, key="bob"),
            )
        return self._circuits[key]

    @staticmethod
    def _basis_change(measurement: Measurement) -> cirq.MatrixGate:
        """Rotate the observable's +1/-1 eigenvectors to computational bits 0/1."""
        angle = np.arctan2(float(measurement.x), float(measurement.z))
        plus = np.array((np.cos(angle / 2), np.sin(angle / 2)), dtype=complex)
        minus = np.array((-plus[1].conjugate(), plus[0].conjugate()))
        return cirq.MatrixGate(np.column_stack((plus, minus)).conj().T)
