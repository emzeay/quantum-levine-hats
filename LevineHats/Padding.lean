import LevineHats.ComplexPhysical
import LevineHats.Encoding

set_option maxHeartbeats 0
noncomputable section
namespace LevineHats
open scoped BigOperators

/-- Add independent extra hats; the policy keeps using the original positions. -/
def padPolicy {T I U J : Type*} (p : Policy T I) : Policy (T × U) (I ⊕ J) where
  aSetting y := p.aSetting y.1
  bSetting x := p.bSetting x.1
  aLabel y a := .inl (p.aLabel y.1 a)
  bLabel x b := .inl (p.bLabel x.1 b)

def padHat {T I U J : Type*} (h : T → I → ℚ) (g : U → J → ℚ)
    (x : T × U) : I ⊕ J → ℚ
  | .inl i => h x.1 i
  | .inr j => g x.2 j

theorem pad_game {T I U J : Type*} [Fintype T] [Fintype U] [Nonempty U]
    (h : T → I → ℚ) (g : U → J → ℚ) (p : Policy T I) :
    game (padHat h g) (padPolicy p) = game h p := by
  simp only [game, average_prod, payoff, padHat, padPolicy, average_const]

def extraHat (r : Nat) (x : Fin r → Bool) (i : Fin r) : ℚ := if x i then 1 else 0

abbrev PaddedStack (n r : Nat) := Stack n × (Fin r → Bool)
abbrev PaddedIndex (n r : Nat) := HatIndex n ⊕ Fin r

def paddedHat (n r : Nat) : PaddedStack n r → PaddedIndex n r → ℚ :=
  padHat (stackHat n) (extraHat r)
def paddedPolicy (n r : Nat) : Policy (PaddedStack n r) (PaddedIndex n r) :=
  padPolicy (stackPolicy n)

theorem padded_index_card (n r : Nat) : Fintype.card (PaddedIndex n r) = 4*(n+1)+r := by
  simp [PaddedIndex, index_card]

/-- Every padded stack corresponds to one complete assignment of independent fair hats. -/
def paddedBitEquiv (n r : Nat) : PaddedStack n r ≃ (PaddedIndex n r → Bool) :=
  (Equiv.prodCongr (stackBitEquiv n) (Equiv.refl (Fin r → Bool))).trans
    (Equiv.sumArrowEquivProdArrow (HatIndex n) (Fin r) Bool).symm

theorem paddedHat_eq_bit (n r : Nat) (x : PaddedStack n r) (i : PaddedIndex n r) :
    paddedHat n r x i = if paddedBitEquiv n r x i then 1 else 0 := by
  cases i with
  | inl i => exact stackHat_eq_bit n x.1 i
  | inr i => rfl

theorem padded_game (n r : Nat) :
    game (paddedHat n r) (paddedPolicy n r) = familyScore n :=
  pad_game _ _ _

theorem padded_complex_score (n r : Nat) :
    complexGame (paddedHat n r) (paddedPolicy n r) =
      (125/357 + (1517/4352 - 125/357)*(1/64)^n : ℂ) := by
  rw [complexGame_eq_game, padded_game, family_closed]
  push_cast
  rfl

theorem padded_real_score (n r : Nat) :
    physicalGame (paddedHat n r) (paddedPolicy n r) = (familyScore n : ℝ) := by
  rw [physicalGame_eq_game, padded_game]

/-- Every number of hats at least four is covered by full blocks and at most three ignored hats. -/
theorem all_sizes_from_four (h : Nat) (hh : 4 ≤ h) :
    Fintype.card (PaddedIndex (h/4-1) (h%4)) = h ∧
    complexGame (paddedHat (h/4-1) (h%4)) (paddedPolicy (h/4-1) (h%4)) =
      (125/357 + (1517/4352 - 125/357)*(1/64)^(h/4-1) : ℂ) := by
  refine ⟨?_, padded_complex_score _ _⟩
  rw [padded_index_card]
  omega

/-- For every h≥8, an explicit h-hat quantum strategy beats the conjectured 35% benchmark.
This theorem does not assert a classical upper bound for those sizes. -/
theorem all_sizes_from_eight (h : Nat) (hh : 8 ≤ h) :
    Fintype.card (PaddedIndex (h/4-1) (h%4)) = h ∧
    (7/20 : ℝ) < physicalGame (paddedHat (h/4-1) (h%4))
      (paddedPolicy (h/4-1) (h%4)) := by
  refine ⟨(all_sizes_from_four h (by omega)).1, ?_⟩
  rw [padded_real_score]
  have hq := family_above_benchmark (n := h/4-1) (by omega)
  have hr := Rat.cast_lt (K := ℝ) |>.mpr hq
  norm_num at hr ⊢
  exact hr

end LevineHats
