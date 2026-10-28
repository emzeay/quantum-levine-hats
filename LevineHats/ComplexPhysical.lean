import LevineHats.PhysicalFamily
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.Rat

set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
namespace LevineHats
open scoped BigOperators ComplexOrder
abbrev ComplexQubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

def complexMatrix (M : QubitMatrix) : ComplexQubitMatrix := M.map (Rat.castHom ℂ)

theorem complexMatrix_mul (M N : QubitMatrix) :
    complexMatrix (M*N) = complexMatrix M * complexMatrix N := Matrix.map_mul

theorem complexMatrix_add (M N : QubitMatrix) :
    complexMatrix (M+N) = complexMatrix M + complexMatrix N := by
  ext i j
  simp [complexMatrix]

theorem complexMatrix_one : complexMatrix 1 = 1 :=
  Matrix.map_one _ (by simp) (by simp)

theorem complexMatrix_hermitian (M : QubitMatrix) (h : M.transpose = M) :
    (complexMatrix M).IsHermitian := by
  change (complexMatrix M).conjTranspose = complexMatrix M
  ext i j
  have hij := congrFun (congrFun h i) j
  simpa [complexMatrix, Matrix.conjTranspose_apply, Matrix.transpose_apply] using
    congrArg (fun q : ℚ => (q : ℂ)) hij

theorem complex_projector_positive (M : QubitMatrix)
    (hs : M.transpose = M) (hi : M*M=M) : (complexMatrix M).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (complexMatrix M)
  rw [complexMatrix_hermitian M hs, ← complexMatrix_mul, hi] at h
  exact h

/-- The Bell state density matrix in the standard complex Hilbert space. -/
def complexBellDensity : Matrix PairIndex PairIndex ℂ := fun i j =>
  if i.1 = i.2 ∧ j.1 = j.2 then 1/2 else 0

theorem complexBellDensity_hermitian : complexBellDensity.IsHermitian := by
  change complexBellDensity.conjTranspose = complexBellDensity
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [complexBellDensity, Matrix.conjTranspose_apply]

theorem complexBellDensity_idempotent : complexBellDensity * complexBellDensity =
    complexBellDensity := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [complexBellDensity, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem complexBellDensity_positive : complexBellDensity.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self complexBellDensity
  rw [complexBellDensity_hermitian, complexBellDensity_idempotent] at h
  exact h

theorem complexBellDensity_trace : Matrix.trace complexBellDensity = 1 := by
  norm_num [Matrix.trace, complexBellDensity, Fintype.sum_prod_type, Fin.sum_univ_two]

def complexBorn (P Q : ComplexQubitMatrix) : ℂ :=
  Matrix.trace (complexBellDensity * Matrix.kronecker P Q)

theorem complexBorn_eq_rational (P Q : QubitMatrix) :
    complexBorn (complexMatrix P) (complexMatrix Q) = (bellQ P Q : ℂ) := by
  simp [complexBorn, bellQ, complexBellDensity, complexMatrix, Matrix.trace,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem complex_physical_probability (i : Fin 3) (j : Fin 2) (a b : Outcome) :
    complexBorn (complexMatrix (aliceProjector i a)) (complexMatrix (bobProjector j b)) =
      (probability i j a b : ℂ) := complexBorn_eq_rational _ _

theorem alice_complex_physical (i : Fin 3) :
    (∀ a, (complexMatrix (aliceProjector i a)).PosSemidef) ∧
    (∀ a, complexMatrix (aliceProjector i a) * complexMatrix (aliceProjector i a) =
      complexMatrix (aliceProjector i a)) ∧
    complexMatrix (aliceProjector i 0) + complexMatrix (aliceProjector i 1) = 1 := by
  refine ⟨fun a => complex_projector_positive _ (alice_symmetric i a) (alice_idempotent i a), ?_, ?_⟩
  · intro a
    rw [← complexMatrix_mul, alice_idempotent]
  · rw [← complexMatrix_add, alice_complete, complexMatrix_one]

theorem bob_complex_physical (i : Fin 2) :
    (∀ a, (complexMatrix (bobProjector i a)).PosSemidef) ∧
    (∀ a, complexMatrix (bobProjector i a) * complexMatrix (bobProjector i a) =
      complexMatrix (bobProjector i a)) ∧
    complexMatrix (bobProjector i 0) + complexMatrix (bobProjector i 1) = 1 := by
  refine ⟨fun a => complex_projector_positive _ (bob_symmetric i a) (bob_idempotent i a), ?_, ?_⟩
  · intro a
    rw [← complexMatrix_mul, bob_idempotent]
  · rw [← complexMatrix_add, bob_complete, complexMatrix_one]

/-- The complex Born expectation is real and agrees with the rational game model. -/
def complexGame {T I : Type*} [Fintype T] (h : T → I → ℚ) (p : Policy T I) : ℂ :=
  (∑ x : T, ∑ y : T, ∑ a : Outcome, ∑ b : Outcome,
    complexBorn (complexMatrix (aliceProjector (p.aSetting y) a))
      (complexMatrix (bobProjector (p.bSetting x) b)) *
        (h x (p.aLabel y a) : ℂ) * (h y (p.bLabel x b) : ℂ)) /
      (Fintype.card T : ℂ)^2

theorem complexGame_eq_game {T I : Type*} [Fintype T]
    (h : T → I → ℚ) (p : Policy T I) : complexGame h p = (game h p : ℂ) := by
  simp only [complexGame, complex_physical_probability, game, average, payoff,
    Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, ← Finset.sum_div]
  ring

theorem complex_family_closed (n : Nat) :
    complexGame (stackHat n) (stackPolicy n) =
      (125/357 + (1517/4352 - 125/357)*(1/64)^n : ℂ) := by
  rw [complexGame_eq_game]
  change (familyScore n : ℂ) = _
  rw [family_closed]
  push_cast
  rfl

end LevineHats
