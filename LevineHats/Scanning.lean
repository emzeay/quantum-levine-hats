import LevineHats.Family

set_option maxHeartbeats 0
namespace LevineHats
open scoped BigOperators Topology
open Filter

/-- Number of four-hat blocks inspected before choosing the one local measurement. -/
def scanCount : (n : Nat) → Stack n → Nat
  | 0 => fun _ => 1
  | n+1 => fun x => if monochrome x.1 then 1 + scanCount n x.2 else 1

theorem scanCount_bounds (n : Nat) (x : Stack n) : 1 ≤ scanCount n x ∧ scanCount n x ≤ n+1 := by
  induction n with
  | zero => simp [scanCount]
  | succ n ih =>
    have ht := ih x.2
    dsimp [scanCount]
    split <;> omega

def expectedBlocks (n : Nat) : ℚ := average (fun x : Stack n => (scanCount n x : ℚ))

theorem average_monochrome_ite (a b : ℚ) :
    average (fun x : Word => if monochrome x then a else b) = a/8 + 7*b/8 := by
  norm_num [average, monochrome, Fin.sum_univ_succ]
  ring

theorem expectedBlocks_zero : expectedBlocks 0 = 1 := by
  simp [expectedBlocks, scanCount]

theorem expectedBlocks_succ (n : Nat) : expectedBlocks (n+1) = 1 + expectedBlocks n / 8 := by
  change average (fun x : Word × Stack n =>
    ((if monochrome x.1 then 1 + scanCount n x.2 else 1 : Nat) : ℚ)) = _
  rw [average_prod]
  have he (x : Word) : average (fun y : Stack n =>
      ((if monochrome x then 1 + scanCount n y else 1 : Nat) : ℚ)) =
      if monochrome x then 1 + expectedBlocks n else 1 := by
    cases hx : monochrome x <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one,
        average_add, average_const, expectedBlocks]
  simp only [he, average_monochrome_ite]
  ring

theorem expectedBlocks_closed (n : Nat) :
    expectedBlocks n = 8/7 - (1/7)*(1/8)^n := by
  induction n with
  | zero => rw [expectedBlocks_zero]; norm_num
  | succ n ih => rw [expectedBlocks_succ, ih, pow_succ]; ring

theorem expectedBlocks_lt (n : Nat) : expectedBlocks n < 8/7 := by
  rw [expectedBlocks_closed]
  have hp : (0 : ℚ) < (1/8)^n := pow_pos (by norm_num) _
  linarith

/-- Inspecting all four hats in each examined block costs fewer than 32/7 hats on average. -/
theorem expectedHats_lt (n : Nat) : (4 : ℚ) * expectedBlocks n < 32/7 := by
  have := expectedBlocks_lt n
  linarith

theorem expectedBlocks_limit :
    Tendsto (fun n => (expectedBlocks n : ℝ)) atTop (𝓝 (8/7)) := by
  have hp : Tendsto (fun n : Nat => (1/8 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc : Tendsto (fun _ : Nat => (8/7 : ℝ)) atTop (𝓝 (8/7)) := tendsto_const_nhds
  have h := hc.sub (hp.const_mul (1/7))
  simpa only [expectedBlocks_closed, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_pow, mul_zero, sub_zero] using h

/-- Event that all blocks in a finite observed prefix are monochromatic. -/
def allMonochrome : (n : Nat) → Stack n → Bool
  | 0 => monochrome
  | n+1 => fun x => monochrome x.1 && allMonochrome n x.2

def noActiveProbability (n : Nat) : ℚ :=
  average (fun x : Stack n => if allMonochrome n x then 1 else 0)

theorem noActive_zero : noActiveProbability 0 = 1/8 := by
  change average (fun x : Word => if monochrome x then (1 : ℚ) else 0) = _
  rw [average_monochrome_ite]
  norm_num

theorem noActive_succ (n : Nat) : noActiveProbability (n+1) = noActiveProbability n / 8 := by
  change average (fun x : Word × Stack n =>
    if monochrome x.1 && allMonochrome n x.2 then (1 : ℚ) else 0) = _
  rw [average_prod]
  have he (x : Word) : average (fun y : Stack n =>
      if monochrome x && allMonochrome n y then (1 : ℚ) else 0) =
      if monochrome x then noActiveProbability n else 0 := by
    cases hx : monochrome x <;> simp [noActiveProbability]
  simp only [he, average_monochrome_ite]
  ring

theorem noActive_closed (n : Nat) : noActiveProbability n = (1/8)^(n+1) := by
  induction n with
  | zero => rw [noActive_zero]; ring
  | succ n ih => rw [noActive_succ, ih, pow_succ]; ring

end LevineHats
