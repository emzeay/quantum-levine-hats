import LevineHats.Composition
import Mathlib.Analysis.SpecificLimits.Basic

set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace LevineHats
open scoped BigOperators Topology
open Filter

/-- Index n means n+1 blocks, i.e. 4(n+1) hats per player. -/
def Stack : Nat → Type
  | 0 => Word
  | n+1 => Word × Stack n

def HatIndex : Nat → Type
  | 0 => Position
  | n+1 => Position ⊕ HatIndex n

instance stackFintype : (n : Nat) → Fintype (Stack n)
  | 0 => inferInstanceAs (Fintype Word)
  | n+1 => letI := stackFintype n; inferInstanceAs (Fintype (Word × Stack n))
instance stackNonempty : (n : Nat) → Nonempty (Stack n)
  | 0 => inferInstanceAs (Nonempty Word)
  | n+1 => letI := stackNonempty n; inferInstanceAs (Nonempty (Word × Stack n))
instance indexFintype : (n : Nat) → Fintype (HatIndex n)
  | 0 => inferInstanceAs (Fintype Position)
  | n+1 => letI := indexFintype n; inferInstanceAs (Fintype (Position ⊕ HatIndex n))

def stackHat : (n : Nat) → Stack n → HatIndex n → ℚ
  | 0 => bit
  | n+1 => liftHat (stackHat n)

def stackPolicy : (n : Nat) → Policy (Stack n) (HatIndex n)
  | 0 => basePolicy
  | n+1 => liftPolicy (stackPolicy n)

theorem stackHat_balanced (n : Nat) :
    ∀ i, average (fun x => stackHat n x i) = 1/2 := by
  induction n with
  | zero => exact average_bit
  | succ n ih => exact liftHat_balanced (stackHat n) ih

theorem stackHat_binary (n : Nat) : ∀ x i, stackHat n x i = 0 ∨ stackHat n x i = 1 := by
  induction n with
  | zero =>
    intro x i
    dsimp [stackHat, bit]
    split <;> simp
  | succ n ih =>
    intro x i
    cases i with
    | inl i =>
      dsimp [stackHat, liftHat, bit]
      split <;> simp
    | inr i => exact ih x.2 i

theorem stack_card (n : Nat) : Fintype.card (Stack n) = 16^(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Word × Stack n) = _
    rw [Fintype.card_prod, ih]
    simp [pow_succ, Nat.mul_comm]

theorem index_card (n : Nat) : Fintype.card (HatIndex n) = 4*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Position ⊕ HatIndex n) = _
    rw [Fintype.card_sum, ih]
    simp only [Fintype.card_fin]
    omega

def familyScore (n : Nat) : ℚ := game (stackHat n) (stackPolicy n)

theorem family_zero : familyScore 0 = 1517/4352 := by
  change game bit basePolicy = _
  rw [base_game, score_exact]

theorem family_succ (n : Nat) : familyScore (n+1) = 375/1088 + familyScore n / 64 :=
  lift_game (stackHat n) (stackHat_balanced n) (stackPolicy n)

theorem family_closed (n : Nat) :
    familyScore n = 125/357 + (1517/4352 - 125/357)*(1/64)^n := by
  induction n with
  | zero => rw [family_zero]; norm_num
  | succ n ih => rw [family_succ, ih, pow_succ]; ring

theorem family_one : familyScore 1 = 97517/278528 := by
  rw [family_closed]
  norm_num

theorem family_step_lt (n : Nat) : familyScore n < familyScore (n+1) := by
  induction n with
  | zero => rw [family_zero, family_one]; norm_num
  | succ n ih =>
    rw [family_succ (n+1), family_succ n]
    rw [family_succ n] at ih
    linarith

theorem family_strictMono : StrictMono familyScore := strictMono_nat_of_lt_succ family_step_lt

theorem family_above_benchmark {n : Nat} (hn : 1 ≤ n) : 7/20 < familyScore n := by
  have h := family_strictMono.monotone hn
  rw [family_one] at h
  linarith

theorem limit_excess : (125/357 : ℚ) - 7/20 = 1/7140 := by norm_num

theorem family_limit : Tendsto (fun n => (familyScore n : ℝ)) atTop (𝓝 (125/357)) := by
  have hp : Tendsto (fun n : Nat => ((1/64 : ℝ)^n)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (hp.const_mul (1517/4352 - 125/357)).const_add (125/357)
  simpa only [family_closed, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, mul_zero, add_zero] using h

end LevineHats
