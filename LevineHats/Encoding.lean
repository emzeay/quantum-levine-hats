import LevineHats.Family
import Mathlib.Data.Fintype.EquivFin

set_option maxHeartbeats 0
noncomputable section
namespace LevineHats
open scoped BigOperators

local instance (n : Nat) : DecidableEq (HatIndex n) := Classical.decEq _

/-- The actual black/white assignment represented by a recursive stack. -/
def stackBits : (n : Nat) → Stack n → HatIndex n → Bool
  | 0 => hat
  | n+1 => fun x i => match i with
    | .inl j => hat x.1 j
    | .inr j => stackBits n x.2 j

theorem wordBits_injective : Function.Injective hat := by decide +kernel

theorem stackBits_injective (n : Nat) : Function.Injective (stackBits n) := by
  induction n with
  | zero => exact wordBits_injective
  | succ n ih =>
    intro x y h
    apply Prod.ext
    · apply wordBits_injective
      funext i
      exact congrFun h (.inl i)
    · apply ih
      funext i
      exact congrFun h (.inr i)

theorem stackBits_bijective (n : Nat) : Function.Bijective (stackBits n) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨stackBits_injective n, ?_⟩
  simp [stack_card, index_card, pow_mul]

noncomputable def stackBitEquiv (n : Nat) : Stack n ≃ (HatIndex n → Bool) :=
  Equiv.ofBijective _ (stackBits_bijective n)

theorem stackHat_eq_bit (n : Nat) (x : Stack n) (i : HatIndex n) :
    stackHat n x i = if stackBits n x i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i => rfl
    | inr i => exact ih x.2 i

/-- Uniform recursive stacks give exactly uniform independent fair-bit strings:
every assignment appears once, and averages of every observable agree. -/
theorem average_stackBits (n : Nat) (f : (HatIndex n → Bool) → ℚ) :
    average (fun x : Stack n => f (stackBits n x)) = average f := by
  classical
  unfold average
  have hs := (stackBitEquiv n).sum_comp f
  have hc := Fintype.card_congr (stackBitEquiv n)
  change (∑ x, f (stackBitEquiv n x)) / (Fintype.card (Stack n) : ℚ) = _
  rw [hs, hc]

end LevineHats
