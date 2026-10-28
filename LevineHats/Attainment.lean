import LevineHats.Classical

set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace LevineHats

/-- A deterministic response profile attaining the classical optimum. -/
def classicalAlice (y : Word) : Position :=
  aliceLabel y (if aliceSetting y = 1 then 1 else 0)
def classicalBob (x : Word) : Position := bobLabel x 0

theorem classical_attainment_count : classicalCount classicalAlice classicalBob = 89 := by
  decide +kernel

theorem classical_attainment : classicalValue classicalAlice classicalBob = 89/256 := by
  simp only [classicalValue, classical_attainment_count]
  norm_num

theorem classical_optimum :
    (∀ a b, classicalValue a b ≤ 89/256) ∧
    (∃ a b, classicalValue a b = 89/256) :=
  ⟨classicalValue_le, ⟨classicalAlice, classicalBob, classical_attainment⟩⟩

end LevineHats
