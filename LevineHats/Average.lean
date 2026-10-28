import LevineHats.Model
import Mathlib.Tactic.FieldSimp

set_option maxHeartbeats 0
namespace LevineHats
open scoped BigOperators

def average {α : Type*} [Fintype α] (f : α → ℚ) : ℚ := (∑ x, f x) / Fintype.card α

theorem card_ne_zero (α : Type*) [Fintype α] [Nonempty α] : (Fintype.card α : ℚ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

@[simp] theorem average_const {α : Type*} [Fintype α] [Nonempty α] (q : ℚ) :
    average (fun _ : α => q) = q := by
  simp [average, nsmul_eq_mul]

theorem average_add {α : Type*} [Fintype α] (f g : α → ℚ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_mul_const {α : Type*} [Fintype α] (f : α → ℚ) (q : ℚ) :
    average (fun x => f x * q) = average f * q := by
  simp [average, ← Finset.sum_mul]
  ring

theorem average_const_mul {α : Type*} [Fintype α] (q : ℚ) (f : α → ℚ) :
    average (fun x => q * f x) = q * average f := by
  simp [average, ← Finset.mul_sum]
  ring

theorem average_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℚ) :
    average (fun x => ∑ y, f x y) = ∑ y, average (fun x => f x y) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem average_swap {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℚ) :
    average (fun x => average (fun y => f x y)) =
    average (fun y => average (fun x => f x y)) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem average_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℚ) :
    average f = average (fun x => average (fun y => f (x,y))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

def bit (x : Word) (a : Position) : ℚ := if hat x a then 1 else 0

@[simp] theorem bit_zero (a : Position) : bit 0 a = 0 := by
  fin_cases a <;> norm_num [bit, hat]
@[simp] theorem bit_full (a : Position) : bit 15 a = 1 := by
  fin_cases a <;> norm_num [bit, hat]

theorem bit_sum : ∀ a : Position, (∑ x : Word, bit x a) = 8 := by
  intro a
  fin_cases a <;> norm_num only [bit, hat, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ] <;> norm_num

@[simp] theorem average_bit (a : Position) : average (fun x => bit x a) = 1/2 := by
  simp only [average, bit_sum]
  norm_num

end LevineHats
