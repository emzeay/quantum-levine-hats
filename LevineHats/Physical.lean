import LevineHats.Model
import Mathlib.Basic.Real.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
namespace LevineHats
open scoped BigOperators Matrix
abbrev RealQubitMatrix := Matrix (Fin 2) (Fin 2) ℝ
abbrev PairIndex := Fin 2 × Fin 2

def realMatrix (M : QubitMatrix) : RealQubitMatrix := M.map (Rat.castHom ℝ)

theorem realMatrix_mul (M N : QubitMatrix) :
    realMatrix (M * N) = realMatrix M * realMatrix N := Matrix.map_mul

theorem realMatrix_add (M N : QubitMatrix) :
    realMatrix (M + N) = realMatrix M + realMatrix N := by
  ext i j
  simp [realMatrix]

theorem realMatrix_one : realMatrix 1 = 1 := by
  exact Matrix.map_one _ (by simp) (by simp)

theorem realMatrix_hermitian (M : QubitMatrix) (h : M.transpose = M) :
    (realMatrix M).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  change (realMatrix M).transpose = realMatrix M
  exact congrArg (fun N : QubitMatrix => realMatrix N) h

theorem projector_positive (M : QubitMatrix) (hs : M.transpose = M) (hi : M*M=M) :
    (realMatrix M).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (realMatrix M)
  rw [realMatrix_hermitian M hs, ← realMatrix_mul, hi] at h
  exact h

/-- The density operator of (|00>+|11>)/sqrt(2). -/
def bellDensity : Matrix PairIndex PairIndex ℝ := fun i j =>
  if i.1 = i.2 ∧ j.1 = j.2 then 1/2 else 0

theorem bellDensity_hermitian : bellDensity.IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  rcases i with ⟨i,k⟩
  rcases j with ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [bellDensity, Matrix.transpose_apply]

theorem bellDensity_positive : bellDensity.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨bellDensity_hermitian, ?_⟩
  intro v
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [bellDensity, star_trivial]
  nlinarith [sq_nonneg (v (0,0) + v (1,1))]

theorem bellDensity_trace : Matrix.trace bellDensity = 1 := by
  norm_num [Matrix.trace, bellDensity, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The usual tensor-product Born rule, evaluated on our density operator. -/
def born (P Q : RealQubitMatrix) : ℝ :=
  Matrix.trace (bellDensity * Matrix.kronecker P Q)

theorem born_eq_rational (P Q : QubitMatrix) :
    born (realMatrix P) (realMatrix Q) = (bellQ P Q : ℝ) := by
  simp [born, bellQ, bellDensity, realMatrix, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem physical_probability (i : Fin 3) (j : Fin 2) (a b : Outcome) :
    born (realMatrix (aliceProjector i a)) (realMatrix (bobProjector j b)) =
      (probability i j a b : ℝ) := born_eq_rational _ _

theorem alice_physical (i : Fin 3) :
    (∀ a, (realMatrix (aliceProjector i a)).PosSemidef) ∧
    (∀ a, realMatrix (aliceProjector i a) * realMatrix (aliceProjector i a) =
      realMatrix (aliceProjector i a)) ∧
    realMatrix (aliceProjector i 0) + realMatrix (aliceProjector i 1) = 1 := by
  refine ⟨fun a => projector_positive _ (alice_symmetric i a) (alice_idempotent i a), ?_, ?_⟩
  · intro a
    rw [← realMatrix_mul, alice_idempotent]
  · rw [← realMatrix_add, alice_complete, realMatrix_one]

theorem bob_physical (i : Fin 2) :
    (∀ a, (realMatrix (bobProjector i a)).PosSemidef) ∧
    (∀ a, realMatrix (bobProjector i a) * realMatrix (bobProjector i a) =
      realMatrix (bobProjector i a)) ∧
    realMatrix (bobProjector i 0) + realMatrix (bobProjector i 1) = 1 := by
  refine ⟨fun a => projector_positive _ (bob_symmetric i a) (bob_idempotent i a), ?_, ?_⟩
  · intro a
    rw [← realMatrix_mul, bob_idempotent]
  · rw [← realMatrix_add, bob_complete, realMatrix_one]

def physicalScore : ℝ := (∑ x : Word, ∑ y : Word, ∑ a : Outcome, ∑ b : Outcome,
  if win x y (aliceLabel y a) (bobLabel x b) then
    born (realMatrix (aliceProjector (aliceSetting y) a))
      (realMatrix (bobProjector (bobSetting x) b)) else 0) / 256

theorem physicalScore_exact : physicalScore = 1517/4352 := by
  have hs := congrArg (fun q : ℚ => (q : ℝ)) score_exact
  simpa only [score, deal, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, Rat.cast_ofNat,
    apply_ite, Rat.cast_zero, physicalScore, physical_probability] using hs

end LevineHats
