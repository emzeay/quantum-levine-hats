import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LevineHats
open scoped BigOperators Matrix
abbrev Word := Fin 16
abbrev Position := Fin 4
abbrev Outcome := Fin 2
abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℚ

/-- Displayed stack bits run from most significant to least significant. -/
def hat (x : Word) (a : Position) : Bool := x.val / 2^(3-a.val) % 2 == 1

def win (x y : Word) (a b : Position) : Bool := hat x a && hat y b

def aliceSetting : Word → Fin 3 := ![0,0,0,0,1,2,1,1,1,1,0,1,0,0,0,0]
def aliceLabel : Word → Outcome → Position := ![![0,0],![3,3],![2,2],![2,2],![0,1],![1,3],![0,2],![3,2],![1,0],![1,3],![0,2],![2,3],![0,0],![1,1],![0,0],![0,0]]
def bobSetting : Word → Fin 2 := ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0]
def bobLabel : Word → Outcome → Position := ![![0,0],![3,3],![2,2],![2,3],![1,0],![3,3],![1,0],![3,3],![0,1],![0,1],![2,2],![2,2],![1,0],![0,1],![1,0],![0,0]]

/-- Rank-one projectors onto (4,-1), (0,1), (4,1); no floating-point data. -/
def alicePlus : Fin 3 → QubitMatrix := ![
  !![16/17, -4/17; -4/17, 1/17],
  !![0, 0; 0, 1],
  !![16/17, 4/17; 4/17, 1/17]]
def bobPlus : Fin 2 → QubitMatrix := ![!![1,0;0,0], !![1/2,1/2;1/2,1/2]]
def aliceProjector (i : Fin 3) (o : Outcome) : QubitMatrix :=
  if o = 0 then alicePlus i else 1 - alicePlus i
def bobProjector (j : Fin 2) (o : Outcome) : QubitMatrix :=
  if o = 0 then bobPlus j else 1 - bobPlus j

/-- Bell-state Born rule: (1/2) sum_ij P_ij Q_ij for real projectors. -/
def bellQ (P Q : QubitMatrix) : ℚ :=
  (∑ i, ∑ j, P i j * Q i j) / 2

def probability (i : Fin 3) (j : Fin 2) (a b : Outcome) : ℚ :=
  bellQ (aliceProjector i a) (bobProjector j b)

def deal (x y : Word) : ℚ := ∑ a, ∑ b,
  if win x y (aliceLabel y a) (bobLabel x b) then
    probability (aliceSetting y) (bobSetting x) a b else 0

def score : ℚ := (∑ x, ∑ y, deal x y) / 256


theorem alice_symmetric (i : Fin 3) (a : Outcome) :
    (aliceProjector i a).transpose = aliceProjector i a := by
  fin_cases i <;> fin_cases a <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [aliceProjector, alicePlus, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply]
theorem alice_idempotent (i : Fin 3) (a : Outcome) :
    aliceProjector i a * aliceProjector i a = aliceProjector i a := by
  fin_cases i <;> fin_cases a <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [aliceProjector, alicePlus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.one_apply]
theorem bob_symmetric (i : Fin 2) (a : Outcome) :
    (bobProjector i a).transpose = bobProjector i a := by
  fin_cases i <;> fin_cases a <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [bobProjector, bobPlus, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply]
theorem bob_idempotent (i : Fin 2) (a : Outcome) :
    bobProjector i a * bobProjector i a = bobProjector i a := by
  fin_cases i <;> fin_cases a <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [bobProjector, bobPlus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.one_apply]
theorem alice_complete (i : Fin 3) : aliceProjector i 0 + aliceProjector i 1 = 1 := by
  simp [aliceProjector]
theorem bob_complete (i : Fin 2) : bobProjector i 0 + bobProjector i 1 = 1 := by
  simp [bobProjector]

/-- Integer outcome weights, denominator 68. This is derived from the projectors. -/
def weight (i : Fin 3) (j : Fin 2) (a b : Outcome) : Nat :=
  if a = b then ![![32,9], ![0,17], ![32,25]] i j
  else ![![2,25], ![34,17], ![2,9]] i j

theorem probability_eq_weight (i : Fin 3) (j : Fin 2) (a b : Outcome) :
    probability i j a b = (weight i j a b : ℚ) / 68 := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [probability, bellQ, aliceProjector, bobProjector, alicePlus, bobPlus,
      weight, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]

theorem probability_nonneg (i : Fin 3) (j : Fin 2) (a b : Outcome) :
    0 ≤ probability i j a b := by
  rw [probability_eq_weight]
  positivity

theorem alice_uniform (i : Fin 3) (j : Fin 2) (a : Outcome) :
    ∑ b, probability i j a b = 1/2 := by
  simp only [probability_eq_weight, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> norm_num [weight]
theorem bob_uniform (i : Fin 3) (j : Fin 2) (b : Outcome) :
    ∑ a, probability i j a b = 1/2 := by
  simp only [probability_eq_weight, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases b <;> norm_num [weight]
theorem probability_normalized (i : Fin 3) (j : Fin 2) :
    ∑ a, ∑ b, probability i j a b = 1 := by
  simp only [alice_uniform]
  norm_num [Fin.sum_univ_two]

def dealWeight (x y : Word) : Nat := ∑ a : Outcome, ∑ b : Outcome,
  if win x y (aliceLabel y a) (bobLabel x b) then
    weight (aliceSetting y) (bobSetting x) a b else 0

theorem deal_eq_weight (x y : Word) : deal x y = (dealWeight x y : ℚ) / 68 := by
  simp only [deal, dealWeight, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    Finset.sum_div, ite_div, zero_div, probability_eq_weight]

theorem total_weight : (∑ x : Word, ∑ y : Word, dealWeight x y) = 6068 := by
  decide +kernel

theorem score_exact : score = 1517/4352 := by
  simp only [score, deal_eq_weight, ← Finset.sum_div, ← Nat.cast_sum]
  rw [total_weight]
  norm_num

theorem score_exceeds_classical_benchmark : score - 89/256 = 1/1088 := by
  rw [score_exact]
  norm_num

end LevineHats
