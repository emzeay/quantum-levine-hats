import LevineHats.Attainment
import LevineHats.ComplexPhysical
import LevineHats.Marginals
import LevineHats.Encoding
import LevineHats.BellReduction
import LevineHats.Padding
import LevineHats.Scanning
import LevineHats.Infinite

/-!
# Entanglement in Levine's hat game

The four-hat separation is unconditional within the stated no-communication model.
The larger family exceeds the *conjectured* classical 7/20 benchmark.
See README.md for exact scope and the native LRAT-check trust boundary of the classical bound.
-/
namespace LevineHats

/-- Four hats: a full classical optimum and an explicit complex quantum realization
with strictly larger payoff. State and measurement validity are certified in ComplexPhysical. -/
theorem four_hat_quantum_advantage :
    (∀ a b, classicalValue a b ≤ 89/256) ∧
    (∃ a b, classicalValue a b = 89/256) ∧
    complexGame bit basePolicy = (1517/4352 : ℂ) ∧
    (89/256 : ℚ) < 1517/4352 := by
  refine ⟨classicalValue_le, classical_optimum.2, ?_, by norm_num⟩
  rw [complexGame_eq_game, base_game, score_exact]
  norm_num

/-- One Bell-pair strategy for every positive multiple of four hats.
The recursive input model is equivalent to all fair bitstrings (Encoding.lean). -/
theorem finite_family_quantum_payoff (n : Nat) :
    Fintype.card (HatIndex n) = 4*(n+1) ∧
    complexGame (stackHat n) (stackPolicy n) =
      (125/357 + (1517/4352 - 125/357)*(1/64)^n : ℂ) :=
  ⟨index_card n, complex_family_closed n⟩

end LevineHats
