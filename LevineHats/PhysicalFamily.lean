import LevineHats.Physical
import LevineHats.Family
import LevineHats.Classical

set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
namespace LevineHats
open scoped BigOperators Topology
open Filter

/-- Born-rule payoff for a finite hat system, with independent uniform inputs.
The same two-qubit density operator and local measurement banks are used at every size. -/
def physicalGame {T I : Type*} [Fintype T] (h : T → I → ℚ) (p : Policy T I) : ℝ :=
  (∑ x : T, ∑ y : T, ∑ a : Outcome, ∑ b : Outcome,
    born (realMatrix (aliceProjector (p.aSetting y) a))
      (realMatrix (bobProjector (p.bSetting x) b)) *
        (h x (p.aLabel y a) : ℝ) * (h y (p.bLabel x b) : ℝ)) /
      (Fintype.card T : ℝ)^2

theorem physicalGame_eq_game {T I : Type*} [Fintype T]
    (h : T → I → ℚ) (p : Policy T I) :
    physicalGame h p = (game h p : ℝ) := by
  simp only [physicalGame, physical_probability, game, average, payoff,
    Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, ← Finset.sum_div]
  ring

def physicalFamilyScore (n : Nat) : ℝ := physicalGame (stackHat n) (stackPolicy n)

theorem physicalFamilyScore_eq (n : Nat) : physicalFamilyScore n = (familyScore n : ℝ) :=
  physicalGame_eq_game _ _

theorem physical_family_closed (n : Nat) : physicalFamilyScore n =
    125/357 + (1517/4352 - 125/357)*(1/64)^n := by
  rw [physicalFamilyScore_eq, family_closed]
  push_cast
  rfl

theorem physical_family_limit :
    Tendsto physicalFamilyScore atTop (𝓝 (125/357)) := by
  change Tendsto (fun n => physicalFamilyScore n) atTop (𝓝 (125/357))
  simp only [physicalFamilyScore_eq]
  exact family_limit

theorem physical_family_above_benchmark {n : Nat} (hn : 1 ≤ n) :
    (7/20 : ℝ) < physicalFamilyScore n := by
  rw [physicalFamilyScore_eq]
  have h : ((7/20 : ℚ) : ℝ) < (familyScore n : ℝ) :=
    Rat.cast_lt.mpr (family_above_benchmark hn)
  norm_num at h ⊢
  exact h

/-- Arbitrary real mixing weights, rather than only rational shared randomness. -/
theorem classical_real_mixture_le {R : Type*} [Fintype R]
    (p : R → ℝ) (hp : ∀ r, 0 ≤ p r) (hn : ∑ r, p r = 1)
    (alice bob : R → Word → Position) :
    (∑ r, p r * (classicalValue (alice r) (bob r) : ℝ)) ≤ 89/256 := by
  calc
    _ ≤ ∑ r, p r * (89/256) := by
      apply Finset.sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_left _ (hp r)
      have h : (classicalValue (alice r) (bob r) : ℝ) ≤ ((89/256 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (classicalValue_le (alice r) (bob r))
      norm_num at h ⊢
      exact h
    _ = 89/256 := by rw [← Finset.sum_mul, hn, one_mul]

theorem physical_beats_real_mixture {R : Type*} [Fintype R]
    (p : R → ℝ) (hp : ∀ r, 0 ≤ p r) (hn : ∑ r, p r = 1)
    (alice bob : R → Word → Position) :
    (∑ r, p r * (classicalValue (alice r) (bob r) : ℝ)) < physicalScore := by
  have h := classical_real_mixture_le p hp hn alice bob
  rw [physicalScore_exact]
  linarith

end LevineHats
