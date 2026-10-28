import LevineHats.Average
import LevineHats.TwoBlocks

set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace LevineHats
open scoped BigOperators

/-- All policies use the same fixed Bell pair and measurement banks. -/
structure Policy (T I : Type*) where
  aSetting : T → Fin 3
  bSetting : T → Fin 2
  aLabel : T → Outcome → I
  bLabel : T → Outcome → I

def basePolicy : Policy Word Position :=
  ⟨aliceSetting, bobSetting, aliceLabel, bobLabel⟩

def payoff {T I : Type*} (h : T → I → ℚ) (p : Policy T I) (x y : T) : ℚ :=
  ∑ a : Outcome, ∑ b : Outcome,
    probability (p.aSetting y) (p.bSetting x) a b * h x (p.aLabel y a) * h y (p.bLabel x b)

def game {T I : Type*} [Fintype T] (h : T → I → ℚ) (p : Policy T I) : ℚ :=
  average (fun x => average (fun y => payoff h p x y))

theorem base_payoff (x y : Word) : payoff bit basePolicy x y = deal x y := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  change probability _ _ a b * bit x (aliceLabel y a) * bit y (bobLabel x b) = _
  by_cases hx : hat x (aliceLabel y a) = true <;>
    by_cases hy : hat y (bobLabel x b) = true <;> simp [bit, win, hx, hy, basePolicy]

theorem base_game : game bit basePolicy = score := by
  simp only [game, average, base_payoff, ← Finset.sum_div, score]
  norm_num
  ring

@[simp] theorem monochrome_zero : monochrome 0 = true := by decide
@[simp] theorem monochrome_full : monochrome 15 = true := by decide

/-- Prepend one four-hat block, and skip it iff the observed block is monochromatic. -/
def liftPolicy {T I : Type*} (p : Policy T I) : Policy (Word × T) (Position ⊕ I) where
  aSetting y := if monochrome y.1 then p.aSetting y.2 else aliceSetting y.1
  bSetting x := if monochrome x.1 then p.bSetting x.2 else bobSetting x.1
  aLabel y a := if monochrome y.1 then .inr (p.aLabel y.2 a) else .inl (aliceLabel y.1 a)
  bLabel x b := if monochrome x.1 then .inr (p.bLabel x.2 b) else .inl (bobLabel x.1 b)

def liftHat {T I : Type*} (h : T → I → ℚ) (x : Word × T) : Position ⊕ I → ℚ
  | .inl i => bit x.1 i
  | .inr i => h x.2 i

theorem liftHat_balanced {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2) :
    ∀ i, average (fun x => liftHat h x i) = 1/2 := by
  intro i
  cases i with
  | inl i => simp only [average_prod, liftHat, average_const, average_bit]
  | inr i => simp only [average_prod, liftHat, hh, average_const]

theorem mixed_alice_average {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2)
    (i : Fin 3) (j : Fin 2) (label : Outcome → I) :
    average (fun x => ∑ a : Outcome, ∑ b : Outcome,
      probability i j a b * h x (label a)) = 1/2 := by
  simp only [average_sum, average_const_mul, hh]
  simp only [← Finset.sum_mul, probability_normalized]
  norm_num

theorem mixed_bob_average {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2)
    (i : Fin 3) (j : Fin 2) (label : Outcome → I) :
    average (fun x => ∑ a : Outcome, ∑ b : Outcome,
      probability i j a b * h x (label b)) = 1/2 := by
  simp only [average_sum, average_const_mul, hh]
  simp only [← Finset.sum_mul, probability_normalized]
  norm_num

def sliceGame {T I : Type*} [Fintype T] (h : T → I → ℚ) (p : Policy T I)
    (x y : Word) : ℚ :=
  average (fun u => average (fun v => payoff (liftHat h) (liftPolicy p) (x,u) (y,v)))

theorem slice_active {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (p : Policy T I) (x y : Word)
    (hx : monochrome x = false) (hy : monochrome y = false) :
    sliceGame h p x y = deal x y := by
  simp [sliceGame, payoff, liftHat, liftPolicy, hx, hy, ← base_payoff, basePolicy]

theorem slice_both_skip {T I : Type*} [Fintype T]
    (h : T → I → ℚ) (p : Policy T I) (x y : Word)
    (hx : monochrome x = true) (hy : monochrome y = true) :
    sliceGame h p x y = game h p := by
  simp [sliceGame, game, payoff, liftHat, liftPolicy, hx, hy]

theorem slice_zero_left {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (p : Policy T I) (y : Word) (hy : monochrome y = false) :
    sliceGame h p 0 y = 0 := by
  simp [sliceGame, payoff, liftHat, liftPolicy, monochrome_zero, hy]

theorem slice_zero_right {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (p : Policy T I) (x : Word) (hx : monochrome x = false) :
    sliceGame h p x 0 = 0 := by
  simp [sliceGame, payoff, liftHat, liftPolicy, monochrome_zero, hx]

theorem slice_full_left {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2)
    (p : Policy T I) (y : Word) (hy : monochrome y = false) :
    sliceGame h p 15 y = 1/2 := by
  simp only [sliceGame, payoff, liftPolicy, hy, monochrome_full, Bool.false_eq_true,
    ↓reduceIte, liftHat, bit_full, mul_one]
  simp only [mixed_bob_average h hh, average_const]

theorem slice_full_right {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2)
    (p : Policy T I) (x : Word) (hx : monochrome x = false) :
    sliceGame h p x 15 = 1/2 := by
  unfold sliceGame
  rw [average_swap]
  simp only [payoff, liftPolicy, hx, monochrome_full, Bool.false_eq_true,
    ↓reduceIte, liftHat, bit_full, mul_one]
  simp only [mixed_alice_average h hh, average_const]


/-- Unconditional contributions of all front-block cases except simultaneous skipping,
scaled by the common denominator 68. -/
def frontWeight (x y : Word) : Nat :=
  if monochrome x then
    if monochrome y then 0 else if x = 15 then 34 else 0
  else if monochrome y then (if y = 15 then 34 else 0)
  else dealWeight x y

theorem frontWeight_total : (∑ x : Word, ∑ y : Word, frontWeight x y) = 6000 := by
  decide +kernel

theorem monochrome_cases (x : Word) (hx : monochrome x = true) : x = 0 ∨ x = 15 := by
  simpa [monochrome] using hx

theorem slice_formula {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2)
    (p : Policy T I) (x y : Word) :
    sliceGame h p x y = (frontWeight x y : ℚ) / 68 +
      if monochrome x && monochrome y then game h p else 0 := by
  cases hx : monochrome x <;> cases hy : monochrome y
  · rw [slice_active h p x y hx hy]
    simp [frontWeight, hx, hy, deal_eq_weight]
  · rcases monochrome_cases y hy with rfl | rfl
    · rw [slice_zero_right h p x hx]
      simp [frontWeight, hx]
    · rw [slice_full_right h hh p x hx]
      norm_num [frontWeight, hx]
  · rcases monochrome_cases x hx with rfl | rfl
    · rw [slice_zero_left h p y hy]
      simp [frontWeight, hy]
    · rw [slice_full_left h hh p y hy]
      norm_num [frontWeight, hy]
  · rw [slice_both_skip h p x y hx hy]
    simp [frontWeight, hx, hy]

theorem game_lift_slices {T I : Type*} [Fintype T]
    (h : T → I → ℚ) (p : Policy T I) :
    game (liftHat h) (liftPolicy p) = average (fun x : Word => average (fun y : Word =>
      sliceGame h p x y)) := by
  simp only [game, average_prod, sliceGame]
  congr 1
  funext x
  exact average_swap (fun u y => average (fun v => payoff (liftHat h) (liftPolicy p) (x,u) (y,v)))

theorem monochrome_sum (q : ℚ) :
    (∑ x : Word, ∑ y : Word, if monochrome x && monochrome y then q else 0) = 4*q := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [monochrome]
  ring

/-- Adding four hats to an arbitrary balanced tail strategy needs no extra entanglement. -/
theorem lift_game {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2)
    (p : Policy T I) :
    game (liftHat h) (liftPolicy p) = 375/1088 + game h p / 64 := by
  rw [game_lift_slices]
  simp only [slice_formula h hh p, average, Finset.sum_add_distrib, ← Finset.sum_div]
  simp only [← Nat.cast_sum, frontWeight_total, monochrome_sum]
  norm_num
  ring

end LevineHats
