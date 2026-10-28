import LevineHats.Model

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace LevineHats
open scoped BigOperators

/-- Sign of a binary measurement outcome (outcome zero denotes +1). -/
def outcomeSign (a : Outcome) : ℚ := if a = 0 then 1 else -1

/-- Binary no-signalling probabilities expressed using local means and correlations.
This algebraic definition does not assert positivity for arbitrary arguments. -/
def momentsProbability (A : Fin 3 → ℚ) (B : Fin 2 → ℚ)
    (C : Fin 3 → Fin 2 → ℚ) (i : Fin 3) (j : Fin 2) (a b : Outcome) : ℚ :=
  (1 + outcomeSign a * A i + outcomeSign b * B j +
    outcomeSign a * outcomeSign b * C i j) / 4

def momentsScore (A : Fin 3 → ℚ) (B : Fin 2 → ℚ) (C : Fin 3 → Fin 2 → ℚ) : ℚ :=
  (∑ x : Word, ∑ y : Word, ∑ a : Outcome, ∑ b : Outcome,
    if win x y (aliceLabel y a) (bobLabel x b) then
      momentsProbability A B C (aliceSetting y) (bobSetting x) a b else 0) / 256

/-- Exact reduction of the fixed hat-response table to biased CHSH and one aligned term.
All local-mean coefficients cancel, so the identity does not assume unbiased measurements. -/
theorem momentsScore_formula (A : Fin 3 → ℚ) (B : Fin 2 → ℚ)
    (C : Fin 3 → Fin 2 → ℚ) :
    momentsScore A B C =
      (324 + 4*C 0 0 - 2*C 0 1 - 24*C 1 0 + 4*C 2 0 + 2*C 2 1) / 1024 := by
  norm_num [momentsScore, momentsProbability, outcomeSign, win, hat,
    aliceLabel, bobLabel, aliceSetting, bobSetting, Fin.sum_univ_succ]
  ring

/-- Correlations of the rational Bell-pair measurements used in this project. -/
def rationalCorrelations : Fin 3 → Fin 2 → ℚ :=
  ![![15/17, -8/17], ![-1,0], ![15/17,8/17]]

theorem rational_probability_moments (i : Fin 3) (j : Fin 2) (a b : Outcome) :
    probability i j a b = momentsProbability (fun _ => 0) (fun _ => 0)
      rationalCorrelations i j a b := by
  rw [probability_eq_weight]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [momentsProbability, outcomeSign, rationalCorrelations, weight]

theorem score_eq_moments : score =
    momentsScore (fun _ => 0) (fun _ => 0) rationalCorrelations := by
  simp only [score, deal, momentsScore, rational_probability_moments]

/-- A second derivation of the exact value, using the correlation identity. -/
theorem score_exact_from_correlations : score = 1517/4352 := by
  rw [score_eq_moments, momentsScore_formula]
  norm_num [rationalCorrelations]

/-- Depolarizing visibility scales all correlations, leaving local means zero.
This is an algebraic score formula; no density-matrix noise model is asserted here. -/
theorem visibility_score (v : ℚ) :
    momentsScore (fun _ => 0) (fun _ => 0) (fun i j => v * rationalCorrelations i j) =
      81/256 + (35/1088)*v := by
  rw [momentsScore_formula]
  norm_num [rationalCorrelations]
  ring

theorem visibility_beats_classical_iff (v : ℚ) :
    89/256 < momentsScore (fun _ => 0) (fun _ => 0)
      (fun i j => v * rationalCorrelations i j) ↔ 34/35 < v := by
  rw [visibility_score]
  constructor <;> intro h <;> linarith

end LevineHats
