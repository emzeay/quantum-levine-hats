import LevineHats.Model
import LevineHats.ClassicalCertificate

set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 100000
namespace LevineHats
open scoped BigOperators

/-- Every deterministic local strategy is allowed, without constraints on outputs. -/
def classicalCount (alice bob : Word → Position) : Nat :=
  ∑ x, ∑ y, if win x y (alice y) (bob x) then 1 else 0

def classicalValue (alice bob : Word → Position) : ℚ := classicalCount alice bob / 256

theorem hat_bitvec (x : Word) (a : Position) :
    hat x a = ClassicalCertificate.hatBV (BitVec.ofNat 4 x.val) (BitVec.ofNat 2 a.val) := by
  revert x a
  decide +kernel

theorem classicalCount_le_256 (alice bob : Word → Position) : classicalCount alice bob ≤ 256 := by
  calc
    classicalCount alice bob ≤ ∑ _x : Word, ∑ _y : Word, (1 : Nat) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      split <;> omega
    _ = 256 := by decide

theorem cast_indicator (c : Bool) : BitVec.ofNat 9 (if c then 1 else 0) =
    (if c then 1#9 else 0#9) := by cases c <;> rfl

theorem classicalCount_encoding (alice bob : Word → Position) :
    BitVec.ofNat 9 (classicalCount alice bob) = ClassicalCertificate.count (BitVec.ofNat 2 (alice 0).val) (BitVec.ofNat 2 (alice 1).val) (BitVec.ofNat 2 (alice 2).val) (BitVec.ofNat 2 (alice 3).val) (BitVec.ofNat 2 (alice 4).val) (BitVec.ofNat 2 (alice 5).val) (BitVec.ofNat 2 (alice 6).val) (BitVec.ofNat 2 (alice 7).val) (BitVec.ofNat 2 (alice 8).val) (BitVec.ofNat 2 (alice 9).val) (BitVec.ofNat 2 (alice 10).val) (BitVec.ofNat 2 (alice 11).val) (BitVec.ofNat 2 (alice 12).val) (BitVec.ofNat 2 (alice 13).val) (BitVec.ofNat 2 (alice 14).val) (BitVec.ofNat 2 (alice 15).val) (BitVec.ofNat 2 (bob 0).val) (BitVec.ofNat 2 (bob 1).val) (BitVec.ofNat 2 (bob 2).val) (BitVec.ofNat 2 (bob 3).val) (BitVec.ofNat 2 (bob 4).val) (BitVec.ofNat 2 (bob 5).val) (BitVec.ofNat 2 (bob 6).val) (BitVec.ofNat 2 (bob 7).val) (BitVec.ofNat 2 (bob 8).val) (BitVec.ofNat 2 (bob 9).val) (BitVec.ofNat 2 (bob 10).val) (BitVec.ofNat 2 (bob 11).val) (BitVec.ofNat 2 (bob 12).val) (BitVec.ofNat 2 (bob 13).val) (BitVec.ofNat 2 (bob 14).val) (BitVec.ofNat 2 (bob 15).val) := by
  simp only [classicalCount, Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero,
    BitVec.ofNat_add, ClassicalCertificate.count]
  simp only [win, hat_bitvec, cast_indicator]
  simp (config := { maxSteps := 2000000 }) only [BitVec.add_assoc]
  rfl

theorem classicalCount_le (alice bob : Word → Position) : classicalCount alice bob ≤ 89 := by
  have hb := ClassicalCertificate.bound (BitVec.ofNat 2 (alice 0).val) (BitVec.ofNat 2 (alice 1).val) (BitVec.ofNat 2 (alice 2).val) (BitVec.ofNat 2 (alice 3).val) (BitVec.ofNat 2 (alice 4).val) (BitVec.ofNat 2 (alice 5).val) (BitVec.ofNat 2 (alice 6).val) (BitVec.ofNat 2 (alice 7).val) (BitVec.ofNat 2 (alice 8).val) (BitVec.ofNat 2 (alice 9).val) (BitVec.ofNat 2 (alice 10).val) (BitVec.ofNat 2 (alice 11).val) (BitVec.ofNat 2 (alice 12).val) (BitVec.ofNat 2 (alice 13).val) (BitVec.ofNat 2 (alice 14).val) (BitVec.ofNat 2 (alice 15).val) (BitVec.ofNat 2 (bob 0).val) (BitVec.ofNat 2 (bob 1).val) (BitVec.ofNat 2 (bob 2).val) (BitVec.ofNat 2 (bob 3).val) (BitVec.ofNat 2 (bob 4).val) (BitVec.ofNat 2 (bob 5).val) (BitVec.ofNat 2 (bob 6).val) (BitVec.ofNat 2 (bob 7).val) (BitVec.ofNat 2 (bob 8).val) (BitVec.ofNat 2 (bob 9).val) (BitVec.ofNat 2 (bob 10).val) (BitVec.ofNat 2 (bob 11).val) (BitVec.ofNat 2 (bob 12).val) (BitVec.ofNat 2 (bob 13).val) (BitVec.ofNat 2 (bob 14).val) (BitVec.ofNat 2 (bob 15).val)
  rw [← classicalCount_encoding] at hb
  have hm : classicalCount alice bob < 2^9 := by
    have := classicalCount_le_256 alice bob
    omega
  simpa only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] using hb

theorem classicalValue_le (alice bob : Word → Position) : classicalValue alice bob ≤ 89/256 := by
  have := classicalCount_le alice bob
  unfold classicalValue
  exact div_le_div_of_nonneg_right (by exact_mod_cast this) (by norm_num)

theorem quantum_beats_every_deterministic (alice bob : Word → Position) :
    classicalValue alice bob < score := by
  have h := classicalValue_le alice bob
  rw [score_exact]
  linarith

/-- Shared randomness independent of the hats is a convex mixture of local strategies. -/
theorem quantum_beats_finite_shared_randomness {R : Type*} [Fintype R]
    (p : R → ℚ) (hp : ∀ r, 0 ≤ p r) (hn : ∑ r, p r = 1)
    (alice bob : R → Word → Position) :
    (∑ r, p r * classicalValue (alice r) (bob r)) < score := by
  have h : (∑ r, p r * classicalValue (alice r) (bob r)) ≤ 89/256 := by
    calc
      _ ≤ ∑ r, p r * (89/256) := Finset.sum_le_sum (fun r _ =>
        mul_le_mul_of_nonneg_left (classicalValue_le (alice r) (bob r)) (hp r))
      _ = 89/256 := by rw [← Finset.sum_mul, hn, one_mul]
  rw [score_exact]
  linarith

end LevineHats
