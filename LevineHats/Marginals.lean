import LevineHats.Family

set_option maxHeartbeats 0
namespace LevineHats
open scoped BigOperators

def aliceMarginal {T I : Type*} [Fintype T] (h : T → I → ℚ) (p : Policy T I) : ℚ :=
  average (fun x => average (fun y => ∑ a : Outcome, ∑ b : Outcome,
    probability (p.aSetting y) (p.bSetting x) a b * h x (p.aLabel y a)))

def bobMarginal {T I : Type*} [Fintype T] (h : T → I → ℚ) (p : Policy T I) : ℚ :=
  average (fun x => average (fun y => ∑ a : Outcome, ∑ b : Outcome,
    probability (p.aSetting y) (p.bSetting x) a b * h y (p.bLabel x b)))

theorem aliceMarginal_half {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2)
    (p : Policy T I) : aliceMarginal h p = 1/2 := by
  unfold aliceMarginal
  simp only [← Finset.sum_mul, alice_uniform]
  rw [average_swap]
  simp only [average_sum, average_const_mul, hh]
  norm_num [Fin.sum_univ_two]

theorem bobMarginal_half {T I : Type*} [Fintype T] [Nonempty T]
    (h : T → I → ℚ) (hh : ∀ i, average (fun x => h x i) = 1/2)
    (p : Policy T I) : bobMarginal h p = 1/2 := by
  unfold bobMarginal
  have hs (x y : T) : (∑ a : Outcome, ∑ b : Outcome,
      probability (p.aSetting y) (p.bSetting x) a b * h y (p.bLabel x b)) =
      ∑ b : Outcome, (1/2 : ℚ) * h y (p.bLabel x b) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, bob_uniform]
  simp only [hs]
  simp only [average_sum, average_const_mul, hh]
  norm_num [Fin.sum_univ_two]

/-- The improvement is in joint success: neither player's own success rate increases. -/
theorem family_marginals (n : Nat) :
    aliceMarginal (stackHat n) (stackPolicy n) = 1/2 ∧
    bobMarginal (stackHat n) (stackPolicy n) = 1/2 :=
  ⟨aliceMarginal_half _ (stackHat_balanced n) _,
   bobMarginal_half _ (stackHat_balanced n) _⟩

end LevineHats
