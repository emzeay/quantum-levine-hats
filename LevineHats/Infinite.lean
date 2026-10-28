import LevineHats.Scanning
import LevineHats.Physical
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Countably infinite fair hats

The block streams are independent products of uniform four-bit words. This file
proves almost-sure stopping, measurability, exact finite-prefix laws, and the
infinite expected payoff using dominated convergence. No classical upper bound
is asserted here; 7/20 remains a conjectured classical benchmark.
-/
set_option maxHeartbeats 200000
set_option Elab.async false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace LevineHats.Infinite

abbrev Stream := Nat → Word

def blockMeasure : Measure Word := (PMF.uniformOfFintype Word).toMeasure
instance : IsProbabilityMeasure blockMeasure := by unfold blockMeasure; infer_instance

def streamMeasure : Measure Stream := Measure.infinitePi (fun _ : Nat => blockMeasure)
instance : IsProbabilityMeasure streamMeasure := by unfold streamMeasure; infer_instance

def monoSet : Set Word := {x | monochrome x = true}

theorem mono_measure : blockMeasure monoSet = 1/8 := by
  rw [blockMeasure, PMF.toMeasure_apply_fintype]
  norm_num [monoSet, Set.indicator, monochrome, PMF.uniformOfFintype_apply, Fin.sum_univ_succ]
  have h : (16 : ℝ≥0)⁻¹ + 16⁻¹ = 8⁻¹ := by norm_num
  have hh := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h
  simpa using hh

def badPrefix (k : Nat) : Set Stream := Set.pi (Finset.range k) (fun _ => monoSet)

theorem badPrefix_measure (k : Nat) : streamMeasure (badPrefix k) = (1/8)^k := by
  unfold streamMeasure badPrefix
  rw [Measure.infinitePi_pi _ (by intro i hi; exact Set.Finite.measurableSet (Set.toFinite _))]
  simp [mono_measure]

theorem eventually_active_ae : ∀ᵐ x ∂streamMeasure, ∃ k, monochrome (x k) = false := by
  rw [ae_iff]
  have hle (k : Nat) : streamMeasure {x | ¬ ∃ j, monochrome (x j) = false} ≤ (1/8)^k := by
    rw [← badPrefix_measure]
    apply measure_mono
    intro x hx i hi
    have hx' : ∀ j, monochrome (x j) = true := by
      intro j
      cases hh : monochrome (x j) <;> simp_all
    exact hx' i
  have hp : Tendsto (fun k : Nat => (1/8 : ℝ≥0∞)^k) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  exact le_antisymm (ge_of_tendsto hp (Eventually.of_forall hle)) (by positivity)

def HasActive (x : Stream) : Prop := ∃ k, monochrome (x k) = false

theorem measurableSet_active (k : Nat) :
    MeasurableSet {x : Stream | monochrome (x k) = false} := by
  have hm : Measurable (fun x : Stream => monochrome (x k)) :=
    (measurable_of_countable monochrome).comp (measurable_pi_apply k)
  exact hm (measurableSet_singleton false)

theorem measurableSet_hasActive : MeasurableSet {x : Stream | HasActive x} := by
  simp only [HasActive, Set.ofPred_exists]
  exact MeasurableSet.iUnion measurableSet_active

/-- A total least-index definition; zero is used on the null event of no active block. -/
theorem activeWitness (x : Stream) : ∃ k, HasActive x → monochrome (x k) = false := by
  by_cases h : HasActive x
  · obtain ⟨k,hk⟩ := h
    exact ⟨k, fun _ => hk⟩
  · exact ⟨0, fun hx => False.elim (h hx)⟩

def firstActive (x : Stream) : Nat := by
  classical
  exact Nat.find (activeWitness x)

theorem firstActive_spec (x : Stream) (hx : HasActive x) :
    monochrome (x (firstActive x)) = false := by
  classical
  exact Nat.find_spec (activeWitness x) hx

theorem before_firstActive (x : Stream) {j : Nat} (hj : j < firstActive x) :
    monochrome (x j) = true := by
  classical
  cases hm : monochrome (x j) with
  | true => rfl
  | false =>
    have hl : firstActive x ≤ j := Nat.find_min' (activeWitness x) (fun _ => hm)
    omega

theorem measurableSet_findPredicate (k : Nat) :
    MeasurableSet {x : Stream | HasActive x → monochrome (x k) = false} := by
  convert measurableSet_hasActive.compl.union (measurableSet_active k) using 1
  ext x
  simp [imp_iff_not_or]

theorem firstActive_measurable : Measurable firstActive := by
  classical
  exact measurable_find activeWitness measurableSet_findPredicate

theorem activeWord_measurable : Measurable (fun x : Stream => x (firstActive x)) := by
  classical
  exact Measurable.find (fun k => measurable_pi_apply k) measurableSet_findPredicate activeWitness

def infinitePolicy : Policy Stream (Nat × Position) where
  aSetting y := aliceSetting (y (firstActive y))
  bSetting x := bobSetting (x (firstActive x))
  aLabel y a := (firstActive y, aliceLabel (y (firstActive y)) a)
  bLabel x b := (firstActive x, bobLabel (x (firstActive x)) b)

def infiniteHat (x : Stream) (i : Nat × Position) : ℚ := bit (x i.1) i.2

theorem infinitePolicy_measurable :
    Measurable infinitePolicy.aSetting ∧ Measurable infinitePolicy.bSetting ∧
    (∀ a, Measurable (fun x => infinitePolicy.aLabel x a)) ∧
    (∀ b, Measurable (fun x => infinitePolicy.bLabel x b)) := by
  refine ⟨(measurable_of_countable aliceSetting).comp activeWord_measurable,
    (measurable_of_countable bobSetting).comp activeWord_measurable, ?_, ?_⟩
  · intro a
    exact firstActive_measurable.prodMk
      ((measurable_of_countable (fun w => aliceLabel w a)).comp activeWord_measurable)
  · intro b
    exact firstActive_measurable.prodMk
      ((measurable_of_countable (fun w => bobLabel w b)).comp activeWord_measurable)

def takeStack : (n : Nat) → Stream → Stack n
  | 0 => fun x => x 0
  | n+1 => fun x => (x 0, takeStack n (fun k => x (k+1)))

def flattenIndex : (n : Nat) → HatIndex n → Nat × Position
  | 0 => fun i => (0,i)
  | n+1 => fun i => match i with
    | .inl j => (0,j)
    | .inr j => ((flattenIndex n j).1+1, (flattenIndex n j).2)

theorem takeStack_hat (n : Nat) (x : Stream) (i : HatIndex n) :
    stackHat n (takeStack n x) i = infiniteHat x (flattenIndex n i) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i => rfl
    | inr i => exact ih (fun k => x (k+1)) i

/-- The finite policy agrees with the first active block whenever that block is in range. -/
theorem policy_at_active (k : Nat) : ∀ (n : Nat) (x : Stream), k ≤ n →
    monochrome (x k) = false → (∀ j, j < k → monochrome (x j) = true) →
    (stackPolicy n).aSetting (takeStack n x) = aliceSetting (x k) ∧
    (stackPolicy n).bSetting (takeStack n x) = bobSetting (x k) ∧
    (∀ a, flattenIndex n ((stackPolicy n).aLabel (takeStack n x) a) = (k,aliceLabel (x k) a)) ∧
    (∀ b, flattenIndex n ((stackPolicy n).bLabel (takeStack n x) b) = (k,bobLabel (x k) b)) := by
  induction k with
  | zero =>
    intro n x hn ha hp
    cases n with
    | zero => simp [stackPolicy, takeStack, basePolicy, flattenIndex]
    | succ n => simp [stackPolicy, takeStack, liftPolicy, ha, flattenIndex]
  | succ k ih =>
    intro n x hn ha hp
    cases n with
    | zero => omega
    | succ n =>
      have h0 : monochrome (x 0) = true := hp 0 (by omega)
      have ht := ih n (fun j => x (j+1)) (by omega) ha (fun j hj => hp (j+1) (by omega))
      rcases ht with ⟨haS,hbS,haL,hbL⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [stackPolicy, takeStack, liftPolicy, h0] using haS
      · simpa [stackPolicy, takeStack, liftPolicy, h0] using hbS
      · intro a
        simp only [stackPolicy, takeStack, liftPolicy, h0, ↓reduceIte, flattenIndex]
        rw [haL]
      · intro b
        simp only [stackPolicy, takeStack, liftPolicy, h0, ↓reduceIte, flattenIndex]
        rw [hbL]

/-- The conditional Born payoff is exactly stable once both first active blocks are in range. -/
theorem truncation_payoff (x y : Stream) (hx : HasActive x) (hy : HasActive y)
    (n : Nat) (hnx : firstActive x ≤ n) (hny : firstActive y ≤ n) :
    payoff (stackHat n) (stackPolicy n) (takeStack n x) (takeStack n y) =
      payoff infiniteHat infinitePolicy x y := by
  obtain ⟨haX,hbX,haLX,hbLX⟩ := policy_at_active (firstActive x) n x hnx
    (firstActive_spec x hx) (fun j hj => before_firstActive x hj)
  obtain ⟨haY,hbY,haLY,hbLY⟩ := policy_at_active (firstActive y) n y hny
    (firstActive_spec y hy) (fun j hj => before_firstActive y hj)
  simp only [payoff, takeStack_hat, haY, hbX, haLY, hbLX, infinitePolicy]

theorem pair_active_ae : ∀ᵐ xy ∂streamMeasure.prod streamMeasure,
    HasActive xy.1 ∧ HasActive xy.2 := by
  have hx : ∀ᵐ xy ∂streamMeasure.prod streamMeasure, HasActive xy.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    simpa [HasActive] using eventually_active_ae
  have hy : ∀ᵐ xy ∂streamMeasure.prod streamMeasure, HasActive xy.2 := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    simpa [HasActive] using eventually_active_ae
  exact hx.and hy

/-- Almost surely, finite-prefix conditional payoffs eventually equal the infinite-policy payoff. -/
theorem truncation_eventually_equal_ae : ∀ᵐ xy ∂streamMeasure.prod streamMeasure,
    ∀ᶠ n in atTop,
      payoff (stackHat n) (stackPolicy n) (takeStack n xy.1) (takeStack n xy.2) =
        payoff infiniteHat infinitePolicy xy.1 xy.2 := by
  filter_upwards [pair_active_ae] with xy hxy
  filter_upwards [eventually_ge_atTop (max (firstActive xy.1) (firstActive xy.2))] with n hn
  exact truncation_payoff xy.1 xy.2 hxy.1 hxy.2 n
    ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)

def stackWords : (n : Nat) → Stack n → Fin (n+1) → Word
  | 0 => fun x _ => x
  | n+1 => fun x => Fin.cases x.1 (stackWords n x.2)

theorem stackWords_injective (n : Nat) : Function.Injective (stackWords n) := by
  induction n with
  | zero => intro x y h; exact congrFun h 0
  | succ n ih =>
    intro x y h
    apply Prod.ext
    · exact congrFun h 0
    · apply ih
      funext i
      exact congrFun h i.succ

theorem stackWords_take (n : Nat) (x : Stream) (i : Fin (n+1)) :
    stackWords n (takeStack n x) i = x i.val := by
  induction n generalizing x with
  | zero => fin_cases i; rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (fun k => x (k+1)) j

attribute [local irreducible] Stack

local instance stackMeasurable (n : Nat) : MeasurableSpace (Stack n) := ⊤
local instance stackMeasurableSingleton (n : Nat) : MeasurableSingletonClass (Stack n) := ⟨fun _ => trivial⟩

def prefixSet (n : Nat) (s : Stack n) : Set Stream :=
  Set.pi (Finset.range (n+1)) (fun k => if h : k < n+1 then {stackWords n s ⟨k,h⟩} else Set.univ)

theorem takeStack_fiber (n : Nat) (s : Stack n) :
    takeStack n ⁻¹' {s} = prefixSet n s := by
  ext x
  constructor
  · intro hx k hk
    have hx' : takeStack n x = s := hx
    have hk' : k < n+1 := Finset.mem_range.mp hk
    simp only [dite_eq_left hk', Set.mem_singleton_iff]
    rw [← hx', stackWords_take]
  · intro hx
    apply stackWords_injective n
    funext i
    rw [stackWords_take]
    have hi := hx i (Finset.mem_range.mpr i.isLt)
    simpa only [dite_eq_left i.isLt, Set.mem_singleton_iff] using hi

theorem takeStack_measurable (n : Nat) : Measurable (takeStack n) := by
  classical
  intro s hs
  have he : takeStack n ⁻¹' s = ⋃ a ∈ s, takeStack n ⁻¹' {a} := by ext x; simp
  rw [he]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro ha
  rw [takeStack_fiber]
  exact MeasurableSet.pi (Finset.countable_toSet _) (by intro k hk; split <;> measurability)

theorem block_singleton (w : Word) : blockMeasure {w} = 16⁻¹ := by
  simp [blockMeasure, PMF.uniformOfFintype_apply]

theorem prefixSet_measure (n : Nat) (s : Stack n) : streamMeasure (prefixSet n s) =
    (16⁻¹ : ℝ≥0∞)^(n+1) := by
  unfold streamMeasure prefixSet
  rw [Measure.infinitePi_pi _ (by intro k hk; split <;> measurability)]
  have he (k : Nat) (hk : k ∈ Finset.range (n+1)) :
      blockMeasure (if h : k < n+1 then {stackWords n s ⟨k,h⟩} else Set.univ) = 16⁻¹ := by
    rw [dite_eq_left (Finset.mem_range.mp hk), block_singleton]
  simp only [Finset.prod_congr rfl he, Finset.prod_const, Finset.card_range]

theorem takeStack_law (n : Nat) : streamMeasure.map (takeStack n) =
    (PMF.uniformOfFintype (Stack n)).toMeasure := by
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.map_apply (takeStack_measurable n) (measurableSet_singleton s),
    takeStack_fiber, prefixSet_measure]
  rw [PMF.toMeasure_apply_singleton (PMF.uniformOfFintype (Stack n)) s (measurableSet_singleton s)]
  simp [PMF.uniformOfFintype_apply, stack_card, ENNReal.inv_pow]


theorem pair_takeStack_law (n : Nat) :
    (streamMeasure.prod streamMeasure).map (Prod.map (takeStack n) (takeStack n)) =
      ((PMF.uniformOfFintype (Stack n)).toMeasure).prod
        (PMF.uniformOfFintype (Stack n)).toMeasure := by
  rw [← Measure.map_prod_map _ _ (takeStack_measurable n) (takeStack_measurable n),
    takeStack_law]

theorem uniform_singleton {T : Type*} [Fintype T] [Nonempty T]
    [MeasurableSpace T] [MeasurableSingletonClass T] (x : T) :
    (PMF.uniformOfFintype T).toMeasure {x} = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  rw [PMF.toMeasure_apply_singleton (PMF.uniformOfFintype T) x (measurableSet_singleton x), PMF.uniformOfFintype_apply]

def finitePayoff (n : Nat) (xy : Stream × Stream) : ℝ :=
  (payoff (stackHat n) (stackPolicy n) (takeStack n xy.1) (takeStack n xy.2) : ℝ)

def infinitePayoff (xy : Stream × Stream) : ℝ :=
  (payoff infiniteHat infinitePolicy xy.1 xy.2 : ℝ)

def infiniteScore : ℝ := ∫ xy, infinitePayoff xy ∂streamMeasure.prod streamMeasure

theorem finitePayoff_integral (n : Nat) :
    (∫ xy, finitePayoff n xy ∂streamMeasure.prod streamMeasure) = (familyScore n : ℝ) := by
  classical
  let f : Stack n × Stack n → ℝ := fun xy => (payoff (stackHat n) (stackPolicy n) xy.1 xy.2 : ℝ)
  have he : (∫ xy, finitePayoff n xy ∂streamMeasure.prod streamMeasure) =
      ∫ xy, f xy ∂((PMF.uniformOfFintype (Stack n)).toMeasure).prod
        (PMF.uniformOfFintype (Stack n)).toMeasure := by
    rw [← pair_takeStack_law]
    exact (integral_map_of_stronglyMeasurable
      ((takeStack_measurable n).prodMap (takeStack_measurable n))
      (measurable_of_countable f).stronglyMeasurable).symm
  rw [he, integral_fintype Integrable.of_finite]
  have hs (xy : Stack n × Stack n) :
      (((PMF.uniformOfFintype (Stack n)).toMeasure).prod
        (PMF.uniformOfFintype (Stack n)).toMeasure).real {xy} =
        ((Fintype.card (Stack n) : ℝ)^2)⁻¹ := by
    rcases xy with ⟨x,y⟩
    simp only [measureReal_def, ← Set.singleton_prod_singleton, Measure.prod_prod,
      uniform_singleton, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring
  simp only [hs, smul_eq_mul, Fintype.sum_prod_type, f, familyScore, game, average,
    Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, ← Finset.mul_sum, ← Finset.sum_div]
  ring

attribute [-instance] stackMeasurable stackMeasurableSingleton


theorem binary_payoff_bounds {T I : Type*} (h : T → I → ℚ)
    (hb : ∀ x i, h x i = 0 ∨ h x i = 1) (p : Policy T I) (x y : T) :
    0 ≤ payoff h p x y ∧ payoff h p x y ≤ 1 := by
  have ht (a b : Outcome) :
      0 ≤ probability (p.aSetting y) (p.bSetting x) a b * h x (p.aLabel y a) * h y (p.bLabel x b) ∧
      probability (p.aSetting y) (p.bSetting x) a b * h x (p.aLabel y a) * h y (p.bLabel x b) ≤
        probability (p.aSetting y) (p.bSetting x) a b := by
    have hp := probability_nonneg (p.aSetting y) (p.bSetting x) a b
    rcases hb x (p.aLabel y a) with hx | hx <;>
      rcases hb y (p.bLabel x b) with hy | hy <;> simp [hx, hy, hp]
  constructor
  · exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => (ht a b).1))
  · calc
      payoff h p x y ≤ ∑ a : Outcome, ∑ b : Outcome,
          probability (p.aSetting y) (p.bSetting x) a b :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => (ht a b).2))
      _ = 1 := probability_normalized _ _


theorem finitePrefix_measurable (n : Nat) (f : Stack n × Stack n → ℝ) :
    Measurable (fun xy : Stream × Stream => f (takeStack n xy.1, takeStack n xy.2)) := by
  let : MeasurableSpace (Stack n) := ⊤
  let : MeasurableSingletonClass (Stack n) := ⟨fun _ => trivial⟩
  have hf : Measurable f := measurable_of_countable f
  have hg : Measurable (Prod.map (takeStack n) (takeStack n)) :=
    (takeStack_measurable n).prodMap (takeStack_measurable n)
  exact hf.comp hg

theorem finitePayoff_measurable (n : Nat) : Measurable (finitePayoff n) :=
  finitePrefix_measurable n (fun xy =>
    (payoff (stackHat n) (stackPolicy n) xy.1 xy.2 : ℝ))


theorem finitePayoff_norm_le (n : Nat) (xy : Stream × Stream) : ‖finitePayoff n xy‖ ≤ 1 := by
  have h := binary_payoff_bounds (stackHat n) (stackHat_binary n) (stackPolicy n)
    (takeStack n xy.1) (takeStack n xy.2)
  have hl : (0 : ℝ) ≤ finitePayoff n xy := by
    unfold finitePayoff
    exact_mod_cast h.1
  have hu : finitePayoff n xy ≤ (1 : ℝ) := by
    unfold finitePayoff
    exact_mod_cast h.2
  simpa [Real.norm_eq_abs, abs_of_nonneg hl] using hu


/-- Actual infinite fair-stack expected payoff, rather than just a limit of finite values. -/
theorem infiniteScore_exact : infiniteScore = 125/357 := by
  have hd := tendsto_integral_of_dominated_convergence (μ := streamMeasure.prod streamMeasure)
    (F := finitePayoff) (f := infinitePayoff) (fun _ => 1)
    (fun n => (finitePayoff_measurable n).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (finitePayoff_norm_le n))
    (by
      filter_upwards [truncation_eventually_equal_ae] with xy hxy
      have he : (fun n => finitePayoff n xy) =ᶠ[atTop] (fun _ => infinitePayoff xy) :=
        hxy.mono (fun n hn => congrArg (fun q : ℚ => (q : ℝ)) hn)
      exact tendsto_const_nhds.congr' he.symm)
  simp only [finitePayoff_integral] at hd
  exact tendsto_nhds_unique hd family_limit

/-- The integrand is the usual Born-rule success probability for the fixed Bell pair. -/
theorem infinitePayoff_born (xy : Stream × Stream) : infinitePayoff xy =
    ∑ a : Outcome, ∑ b : Outcome,
      born (realMatrix (aliceProjector (infinitePolicy.aSetting xy.2) a))
        (realMatrix (bobProjector (infinitePolicy.bSetting xy.1) b)) *
      (infiniteHat xy.1 (infinitePolicy.aLabel xy.2 a) : ℝ) *
      (infiniteHat xy.2 (infinitePolicy.bLabel xy.1 b) : ℝ) := by
  simp only [infinitePayoff, payoff, Rat.cast_sum, Rat.cast_mul, physical_probability]

theorem infiniteScore_excess : infiniteScore - 7/20 = 1/7140 := by
  rw [infiniteScore_exact]
  norm_num

end LevineHats.Infinite
