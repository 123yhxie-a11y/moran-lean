import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Homogeneous Moran sets and measures

This file defines homogeneous Moran sets, their associated probability measures,
and digit mask functions. It proves their Fourier product formula and constructs
spectral Moran measures with prescribed Fourier and Hausdorff dimensions.
The construction uses linear block lengths, finite-field power digits, and the
least odd primes satisfying the scale and logarithmic cost bounds.
A sharp degree-dependent bound for additive character sums supplies the mask estimates.
The Fourier decay, Salem property, and explicit spectrum are established for
this same construction.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace Moran

/-- Bases and nonempty digit sets for a homogeneous Moran construction, indexed from zero. -/
structure Data where
  /-- The integer base at each level. -/
  base : ℕ → ℕ
  /-- The base at each level is at least two. -/
  two_le_base : ∀ n, 2 ≤ base n
  /-- The finite digit set at each level. -/
  digits : ℕ → Finset ℕ
  /-- Every digit set is nonempty. -/
  digits_nonempty : ∀ n, (digits n).Nonempty
  /-- Every digit is strictly smaller than its base. -/
  digit_lt_base : ∀ n d, d ∈ digits n → d < base n

namespace Data

variable (A : Data)

/-- The product of the bases through level `n`, including level zero. -/
def scale (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (n + 1), A.base k

/-- The real number encoded by a sequence of digits. -/
def coding (d : ℕ → ℕ) : ℝ :=
  ∑' n, (d n : ℝ) / (A.scale n : ℝ)

/-- The homogeneous Moran set consisting of all admissible digit expansions. -/
def carrier : Set ℝ :=
  {x | ∃ d : ℕ → ℕ, (∀ n, d n ∈ A.digits n) ∧ A.coding d = x}

private lemma two_pow_mul_base_le_scale (n : ℕ) :
    2 ^ n * A.base n ≤ A.scale n := by
  simpa [scale, Finset.prod_range_succ] using
    Nat.mul_le_mul_right (A.base n)
      (Finset.prod_le_prod (s := Finset.range n) (f := fun _ ↦ 2) (g := A.base)
        (fun _ _ ↦ Nat.zero_le 2) (fun k _ ↦ A.two_le_base k))

private lemma coding_term_le (n d : ℕ) (hd : d ∈ A.digits n) :
    (d : ℝ) / (A.scale n : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
  have hb : (0 : ℝ) < A.base n := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide)
    (A.two_le_base n))
  have hs : (2 : ℝ) ^ n * A.base n ≤ A.scale n := by
    exact_mod_cast A.two_pow_mul_base_le_scale n
  have hd' : (d : ℝ) ≤ A.base n := Nat.cast_le.mpr (A.digit_lt_base n d hd).le
  calc
    (d : ℝ) / (A.scale n : ℝ) ≤ (A.base n : ℝ) / (2 ^ n * A.base n) :=
      div_le_div₀ hb.le hd' (mul_pos (pow_pos (by norm_num) n) hb) hs
    _ = (1 / 2 : ℝ) ^ n := by
      field_simp
      simp

private lemma base_div_scale_le (n : ℕ) :
    (A.base n : ℝ) / (A.scale n : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
  have hb : (0 : ℝ) < A.base n := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide)
    (A.two_le_base n))
  have hs : (2 : ℝ) ^ n * A.base n ≤ A.scale n := by
    exact_mod_cast A.two_pow_mul_base_le_scale n
  calc
    (A.base n : ℝ) / (A.scale n : ℝ) ≤
        (A.base n : ℝ) / (2 ^ n * A.base n) := by
      exact div_le_div_of_nonneg_left hb.le (mul_pos (pow_pos (by norm_num) n) hb) hs
    _ = (1 / 2 : ℝ) ^ n := by
      field_simp
      simp

/-- Every admissible digit expansion is summable. -/
theorem summable_coding (d : ℕ → ℕ) (hd : ∀ n, d n ∈ A.digits n) :
    Summable (fun n ↦ (d n : ℝ) / (A.scale n : ℝ)) := by
  exact Summable.of_nonneg_of_le (fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n ↦ A.coding_term_le n (d n) (hd n))
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))

private lemma prefix_product_pos (n : ℕ) : 0 < ∏ j ∈ Finset.range n, A.base j := by
  exact Finset.prod_pos (fun j _ ↦ lt_of_lt_of_le Nat.zero_lt_two (A.two_le_base j))

private lemma sum_coding_prefix_le (d : ℕ → ℕ) (hd : ∀ n, d n ∈ A.digits n) (n : ℕ) :
    ∑ j ∈ Finset.range n, (d j : ℝ) / A.scale j ≤
      1 - ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hP : (0 : ℝ) < ∏ j ∈ Finset.range n, (A.base j : ℝ) := by
      exact_mod_cast A.prefix_product_pos n
    have hN : (0 : ℝ) < A.base n := by
      exact_mod_cast Nat.zero_lt_two.trans_le (A.two_le_base n)
    have hd' : (d n : ℝ) + 1 ≤ A.base n := by
      exact_mod_cast Nat.succ_le_of_lt (A.digit_lt_base n (d n) (hd n))
    rw [Finset.sum_range_succ]
    refine (add_le_add_left ih _).trans ?_
    simp only [scale, Finset.prod_range_succ, Nat.cast_mul, Nat.cast_prod]
    field_simp
    nlinarith

private lemma coding_mem_Icc (d : ℕ → ℕ) (hd : ∀ n, d n ∈ A.digits n) :
    A.coding d ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨tsum_nonneg (fun _ ↦ by positivity),
    le_of_tendsto (A.summable_coding d hd).hasSum.tendsto_sum_nat
      (Eventually.of_forall (fun n ↦ (A.sum_coding_prefix_le d hd n).trans ?_))⟩
  exact sub_le_self _ (by positivity)

private lemma continuousOn_coding :
    ContinuousOn A.coding {d | ∀ n, d n ∈ A.digits n} := by
  refine continuousOn_tsum (fun n ↦ ?_)
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)) ?_
  · exact ((continuous_of_discreteTopology : Continuous (fun k : ℕ ↦ (k : ℝ))).comp
      (continuous_apply n)).div_const _ |>.continuousOn
  · intro n x hx
    simpa only [norm_div, Real.norm_natCast] using A.coding_term_le n (x n) (hx n)

/-- The homogeneous Moran set is nonempty and compact. -/
theorem nonempty_isCompact_carrier :
    A.carrier.Nonempty ∧ IsCompact A.carrier := by
  change (A.coding '' {d | ∀ n, d n ∈ A.digits n}).Nonempty ∧
    IsCompact (A.coding '' {d | ∀ n, d n ∈ A.digits n})
  constructor
  · exact Set.Nonempty.image A.coding
      ⟨fun n ↦ (A.digits_nonempty n).choose, fun n ↦ (A.digits_nonempty n).choose_spec⟩
  · exact (isCompact_pi_infinite
      (fun n ↦ (A.digits n).finite_toSet.isCompact)).image_of_continuousOn A.continuousOn_coding

/-- The uniform probability distribution on the digits at level `n`. -/
def digitLaw (n : ℕ) : Measure ℕ :=
  ((A.digits n).card : ℝ≥0∞)⁻¹ •
    ∑ d ∈ A.digits n, Measure.dirac d

/-- The atomic distribution of the scaled digit at level `n`. -/
def factor (n : ℕ) : Measure ℝ :=
  ((A.digits n).card : ℝ≥0∞)⁻¹ •
    ∑ d ∈ A.digits n, Measure.dirac ((d : ℝ) / (A.scale n : ℝ))

/-- The convolution of the first `n` scaled digit distributions. -/
def partialConvolution (A : Data) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (partialConvolution A n).conv (A.factor n)

/-- The Cantor–Moran measure is the distribution of the independent digit series. -/
def measure : Measure ℝ :=
  Measure.map A.coding (Measure.infinitePi A.digitLaw)

private lemma isProbabilityMeasure_digitLaw (n : ℕ) :
    IsProbabilityMeasure (A.digitLaw n) := by
  refine ⟨?_⟩
  simp [digitLaw, ENNReal.inv_mul_cancel,
    Nat.ne_of_gt (A.digits_nonempty n).card_pos]

private lemma ae_mem_digits (n : ℕ) : ∀ᵐ d ∂A.digitLaw n, d ∈ A.digits n := by
  simp [ae_iff, digitLaw]

private lemma ae_all_mem_digits :
    ∀ᵐ d ∂Measure.infinitePi A.digitLaw, ∀ n, d n ∈ A.digits n := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  refine ae_all_iff.mpr (fun n ↦ ?_)
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable
    ((Measure.infinitePi_map_eval A.digitLaw n).symm ▸ A.ae_mem_digits n)

private lemma measurable_coding : Measurable A.coding := by
  exact Measurable.tsum (fun n ↦
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_pi_apply n)).div_const (A.scale n : ℝ))

/-- The Cantor–Moran measure is a probability measure. -/
instance instIsProbabilityMeasure : IsProbabilityMeasure A.measure := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  exact Measure.isProbabilityMeasure_map A.measurable_coding.aemeasurable

/-- The Cantor–Moran measure is concentrated on its homogeneous Moran set. -/
theorem measure_compl_carrier :
    A.measure A.carrierᶜ = 0 := by
  rw [measure, Measure.map_apply A.measurable_coding
    A.nonempty_isCompact_carrier.2.measurableSet.compl]
  exact ae_iff.mp (A.ae_all_mem_digits.mono (fun d hd ↦ ⟨d, hd, rfl⟩))

private lemma measurable_coding_term (n : ℕ) :
    Measurable (fun d : ℕ → ℕ ↦ (d n : ℝ) / (A.scale n : ℝ)) := by
  exact ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    (measurable_pi_apply n)).div_const _

private lemma map_digitLaw (n : ℕ) :
    (A.digitLaw n).map (fun d : ℕ ↦ (d : ℝ) / (A.scale n : ℝ)) = A.factor n := by
  simp [digitLaw, factor, Measure.map_smul,
    Measure.map_finset_sum (measurable_of_countable _).aemeasurable]

private lemma map_coding_term (n : ℕ) :
    (Measure.infinitePi A.digitLaw).map
      (fun d : ℕ → ℕ ↦ (d n : ℝ) / (A.scale n : ℝ)) = A.factor n := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  change (Measure.infinitePi A.digitLaw).map
    ((fun d : ℕ ↦ (d : ℝ) / (A.scale n : ℝ)) ∘ (fun d : ℕ → ℕ ↦ d n)) = _
  rw [← Measure.map_map (μ := Measure.infinitePi A.digitLaw)
    (f := fun d : ℕ → ℕ ↦ d n) (g := fun d : ℕ ↦ (d : ℝ) / (A.scale n : ℝ))
    (measurable_of_countable _) (measurable_pi_apply n),
    Measure.infinitePi_map_eval, A.map_digitLaw]

private lemma indep_coding_terms :
    ProbabilityTheory.iIndepFun
      (fun n (d : ℕ → ℕ) ↦ (d n : ℝ) / (A.scale n : ℝ))
      (Measure.infinitePi A.digitLaw) := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  exact ProbabilityTheory.iIndepFun_infinitePi (fun n ↦
    measurable_of_countable (fun d : ℕ ↦ (d : ℝ) / (A.scale n : ℝ)))

private lemma measurable_partial_coding (n : ℕ) :
    Measurable
      (fun d : ℕ → ℕ ↦ ∑ k ∈ Finset.range n, (d k : ℝ) / (A.scale k : ℝ)) := by
  exact Finset.measurable_sum _ (fun k _ ↦ A.measurable_coding_term k)

private lemma map_partial_coding (n : ℕ) :
    (Measure.infinitePi A.digitLaw).map
      (fun d : ℕ → ℕ ↦ ∑ k ∈ Finset.range n, (d k : ℝ) / (A.scale k : ℝ)) =
      A.partialConvolution n := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  induction n with
  | zero => simp [partialConvolution, Measure.map_const]
  | succ n ih =>
    have hi := A.indep_coding_terms.indepFun_finsetSum_of_notMem
      A.measurable_coding_term (Finset.notMem_range_self (n := n))
    simp only [Finset.sum_fn] at hi
    simpa only [Finset.sum_range_succ, partialConvolution, Pi.add_def, ih, A.map_coding_term]
      using hi.map_add_eq_map_conv_map
        (A.measurable_partial_coding n) (A.measurable_coding_term n)

private lemma tendsto_integral_finset_coding {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ →ᵇ E) :
    Tendsto (fun s : Finset ℕ ↦ ∫ d, f (∑ k ∈ s, (d k : ℝ) / (A.scale k : ℝ))
      ∂Measure.infinitePi A.digitLaw)
      atTop (𝓝 (∫ d, f (A.coding d) ∂Measure.infinitePi A.digitLaw)) := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall (fun s ↦ (f.continuous.stronglyMeasurable.comp_measurable
      (Finset.measurable_sum s (fun k _ ↦ A.measurable_coding_term k))).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun _ ↦
      Filter.Eventually.of_forall (fun _ ↦ f.norm_coe_le_norm _))
  · exact A.ae_all_mem_digits.mono (fun d hd ↦
      f.continuous.continuousAt.tendsto.comp (A.summable_coding d hd).hasSum)

private lemma tendsto_integral_partial_coding {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ →ᵇ E) :
    Tendsto (fun n ↦ ∫ d, f (∑ k ∈ Finset.range n, (d k : ℝ) / (A.scale k : ℝ))
      ∂Measure.infinitePi A.digitLaw)
      atTop (𝓝 (∫ d, f (A.coding d) ∂Measure.infinitePi A.digitLaw)) := by
  exact (A.tendsto_integral_finset_coding f).comp tendsto_finset_range

private lemma tendsto_integral_partialConvolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ →ᵇ E) :
    Tendsto (fun n ↦ ∫ x, f x ∂A.partialConvolution n)
      atTop (𝓝 (∫ x, f x ∂A.measure)) := by
  simpa only [← A.map_partial_coding, measure,
    integral_map_of_stronglyMeasurable (A.measurable_partial_coding _)
      f.continuous.stronglyMeasurable,
    integral_map_of_stronglyMeasurable A.measurable_coding f.continuous.stronglyMeasurable]
    using A.tendsto_integral_partial_coding f

/-- Finite digit convolutions converge weakly to the Cantor–Moran measure. -/
theorem tendsto_partialConvolution (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(A.partialConvolution n))
      atTop (𝓝 (∫ x, f x ∂A.measure)) := by
  exact A.tendsto_integral_partialConvolution f

end Data

private lemma pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero {F : Type*} [Field F]
    (P : Polynomial F) (x : F) (M : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ M ∣ P ↔
      ∀ n < M, (Polynomial.hasseDeriv n P).eval x = 0 := by
  rw [← map_dvd_iff (Polynomial.taylorEquiv x)]
  change Polynomial.taylor x ((Polynomial.X - Polynomial.C x) ^ M) ∣
    Polynomial.taylor x P ↔ _
  simp [Polynomial.X_pow_dvd_iff, Polynomial.taylor_coeff]

private lemma hasseDeriv_eval_mul_pow_expChar {F : Type*} [Field F] {p r n : ℕ}
    [ExpChar F p] (P Q : Polynomial F) (x : F) (hn : n < p ^ r) :
    (Polynomial.hasseDeriv n (P * Q ^ (p ^ r))).eval x =
      (Polynomial.hasseDeriv n P).eval x * Q.eval x ^ (p ^ r) := by
  have hd : (Polynomial.X - Polynomial.C x) ^ (p ^ r) ∣
      P * Q ^ (p ^ r) - P * Polynomial.C (Q.eval x) ^ (p ^ r) := by
    rw [← mul_sub, ← sub_pow_expChar_pow]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd
      (Polynomial.X_sub_C_dvd_sub_C_eval (p := Q) (a := x)) _) _
  have hz := (pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero _ _ _).mp hd n hn
  have hC : P * Polynomial.C (Q.eval x) ^ (p ^ r) = Q.eval x ^ (p ^ r) • P := by
    rw [← Polynomial.C_pow, Polynomial.smul_eq_C_mul, mul_comm]
  simpa only [hC, map_sub, map_smul, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul, sub_eq_zero, mul_comm] using hz

private lemma coprime_block_index_injective {m q : ℕ} (hmq : m.Coprime q) :
    Function.Injective (fun a : Fin q × ℕ ↦ a.1.val * m + a.2 * q) := by
  intro a b hab
  have hmod : a.1.val * m ≡ b.1.val * m [MOD q] := by
    simpa [Nat.ModEq, Nat.add_mod] using congrArg (· % q) hab
  have hi : a.1 = b.1 := Fin.ext <|
    (hmod.cancel_right_of_coprime hmq.symm).eq_of_lt_of_lt a.1.isLt b.1.isLt
  exact Prod.ext hi (Nat.eq_of_mul_eq_mul_right (Nat.zero_le _ |>.trans_lt a.1.isLt)
    (by simpa only [hi, Nat.add_right_inj] using hab))

private lemma natDegree_degree_block {F : Type*} [Field F] {m q L i j : ℕ}
    (e g : Polynomial F) (he : e ≠ 0) (hg₀ : g ≠ 0) (hg : g.natDegree = m * L) :
    (e * g ^ i * Polynomial.X ^ (j * (q * L))).natDegree =
      e.natDegree + L * (i * m + j * q) := by
  rw [Polynomial.natDegree_mul_X_pow _ (mul_ne_zero he (pow_ne_zero _ hg₀)),
    Polynomial.natDegree_mul he (pow_ne_zero _ hg₀), Polynomial.natDegree_pow, hg]
  ring

private lemma sum_ne_zero_of_natDegree_injective {F ι : Type*} [Field F] [Fintype ι]
    (v : ι → Polynomial F)
    (hinj : ∀ {a b}, v a ≠ 0 → v b ≠ 0 → (v a).natDegree = (v b).natDegree → a = b)
    (hne : ∃ a, v a ≠ 0) : ∑ a, v a ≠ 0 := by
  have hsum := Polynomial.degree_sum_eq_of_disjoint v Finset.univ
    (fun a ha b hb hab hd ↦ hab (hinj ha.2 hb.2
      (Polynomial.natDegree_eq_of_degree_eq hd)))
  obtain ⟨a, ha⟩ := hne
  intro hz
  have hle := Finset.le_sup (f := fun a ↦ (v a).degree) (Finset.mem_univ a)
  rw [← hsum, hz, Polynomial.degree_zero] at hle
  exact ha (Polynomial.degree_eq_bot.mp (le_bot_iff.mp hle))

private lemma sum_degree_blocks_ne_zero {F : Type*} [Field F] {m q L u : ℕ}
    (hmq : m.Coprime q) (hL : 0 < L) (g : Polynomial F) (hg₀ : g ≠ 0)
    (hg : g.natDegree = m * L) (e : Fin q × Fin (u + 1) → Polynomial F)
    (he : ∀ a, (e a).natDegree < L) (hne : ∃ a, e a ≠ 0) :
    ∑ a, e a * g ^ a.1.val * Polynomial.X ^ (a.2.val * (q * L)) ≠ 0 := by
  classical
  let v (a : Fin q × Fin (u + 1)) := e a * g ^ a.1.val *
    Polynomial.X ^ (a.2.val * (q * L))
  have hv (a) : v a ≠ 0 ↔ e a ≠ 0 := by simp [v, hg₀]
  have hd (a) (ha : v a ≠ 0) :
      (v a).natDegree = (e a).natDegree + L * (a.1.val * m + a.2.val * q) := by
    exact natDegree_degree_block (e a) g ((hv a).mp ha) hg₀ hg
  have hinj {a b} (ha : v a ≠ 0) (hb : v b ≠ 0)
      (hab : (v a).natDegree = (v b).natDegree) : a = b := by
    have hdiv := congrArg (· / L) hab
    simp only [hd a ha, hd b hb, Nat.add_mul_div_left _ _ hL,
      Nat.div_eq_of_lt (he a), Nat.div_eq_of_lt (he b), zero_add] at hdiv
    simpa only [Prod.mk.injEq, Fin.val_inj, ← Prod.ext_iff] using
      coprime_block_index_injective hmq (a₁ := (a.1, a.2.val))
      (a₂ := (b.1, b.2.val)) hdiv
  exact sum_ne_zero_of_natDegree_injective v hinj (hne.imp (fun a ha ↦ (hv a).mpr ha))

private lemma natDegree_jet_relation_lt {F : Type*} [Field F] {q u L D : ℕ}
    (hL : 0 < L) (G : Polynomial F) (hG : G.natDegree ≤ D)
    (e : Fin q × Fin (u + 1) → Polynomial F) (he : ∀ a, (e a).natDegree < L)
    (n : ℕ) :
    (∑ a, Polynomial.hasseDeriv n (e a) * G ^ a.1.val *
      Polynomial.X ^ a.2.val).natDegree < L + (q - 1) * D + u := by
  have hterm (a : Fin q × Fin (u + 1)) :
      (Polynomial.hasseDeriv n (e a) * G ^ a.1.val *
        Polynomial.X ^ a.2.val).natDegree ≤ (L - 1) + (q - 1) * D + u := by
    refine Polynomial.natDegree_mul_le.trans ?_
    refine add_le_add (Polynomial.natDegree_mul_le.trans ?_) (by simpa using a.2.isLt)
    exact add_le_add ((Polynomial.natDegree_hasseDeriv_le _ _).trans
      ((Nat.sub_le _ _).trans (Nat.le_pred_of_lt (he a))))
      (by simpa only [Polynomial.natDegree_pow, Nat.pred_eq_sub_one] using
        Nat.mul_le_mul (Nat.le_pred_of_lt a.1.isLt) hG)
  exact (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun a _ ↦ hterm a)).trans_lt
    (by omega)

private lemma exists_jet_coefficient_relation {F : Type*} [Field F] {q u L D M : ℕ}
    (G : Polynomial F)
    (hdim : M * (L + (q - 1) * D + u) < q * (u + 1) * L) :
    ∃ e : Fin q × Fin (u + 1) → Polynomial.degreeLT F L, e ≠ 0 ∧
      ∀ (n : Fin M) (k : Fin (L + (q - 1) * D + u)),
        (∑ a, Polynomial.hasseDeriv n.val (e a : Polynomial F) * G ^ a.1.val *
          Polynomial.X ^ a.2.val).coeff k.val = 0 := by
  classical
  let T := L + (q - 1) * D + u
  let A : (Fin q × Fin (u + 1) → Polynomial.degreeLT F L) →ₗ[F]
      (Fin M × Fin T → F) := {
    toFun := fun e nj ↦ (∑ a, Polynomial.hasseDeriv nj.1.val (e a : Polynomial F) *
      G ^ a.1.val * Polynomial.X ^ a.2.val).coeff nj.2.val
    map_add' := fun x y ↦ funext fun nj ↦ by simp [add_mul, Finset.sum_add_distrib]
    map_smul' := fun c x ↦ funext fun nj ↦ by simp [← Finset.smul_sum] }
  have hker : A.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simpa [Module.finrank_pi_fintype,
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F L), T] using hdim)
  obtain ⟨e, heker, he₀⟩ := (Submodule.ne_bot_iff A.ker).mp hker
  exact ⟨e, he₀, fun n k ↦ congrFun (LinearMap.mem_ker.mp heker) (n, k)⟩

private lemma exists_jet_relation {F : Type*} [Field F] {q u L D M : ℕ}
    (hL : 0 < L) (G : Polynomial F) (hG : G.natDegree ≤ D)
    (hdim : M * (L + (q - 1) * D + u) < q * (u + 1) * L) :
    ∃ e : Fin q × Fin (u + 1) → Polynomial F,
      (∀ a, (e a).natDegree < L) ∧ (∃ a, e a ≠ 0) ∧
      ∀ n < M, ∑ a, Polynomial.hasseDeriv n (e a) * G ^ a.1.val *
        Polynomial.X ^ a.2.val = 0 := by
  classical
  let T := L + (q - 1) * D + u
  obtain ⟨e, he₀, hecoeff⟩ := exists_jet_coefficient_relation G hdim
  have he (a) : (e a : Polynomial F).natDegree < L := by
    by_cases hz : (e a : Polynomial F) = 0
    case neg =>
      exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (Polynomial.mem_degreeLT.mp (e a).property)
    case pos => simp [hz, hL]
  have hne : ∃ a, (e a : Polynomial F) ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall, Submodule.coe_eq_zero] using he₀
  refine ⟨fun a ↦ e a, he, hne, fun n hn ↦ ?_⟩
  ext k
  by_cases hk : k < T
  · exact hecoeff ⟨n, hn⟩ ⟨k, hk⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((natDegree_jet_relation_lt hL G hG (fun a ↦ e a) he n).trans_le (Nat.le_of_not_gt hk))

private lemma hasseDeriv_eval_degree_block {F : Type*} [Field F] {p r V n : ℕ}
    [ExpChar F p] (P H : Polynomial F) (i j : ℕ) (x : F)
    (hn : n < p ^ r) (hx : x ^ (p ^ r * V) = x) :
    (Polynomial.hasseDeriv n (P * (H ^ (p ^ r)) ^ i *
      Polynomial.X ^ (j * (p ^ r * V)))).eval x =
      (Polynomial.hasseDeriv n P).eval x * (H.eval x ^ (p ^ r)) ^ i * x ^ j := by
  have heq : P * (H ^ (p ^ r)) ^ i * Polynomial.X ^ (j * (p ^ r * V)) =
      P * (H ^ i * Polynomial.X ^ (j * V)) ^ (p ^ r) := by
    simp only [mul_pow, ← pow_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [heq, hasseDeriv_eval_mul_pow_expChar P _ x hn]
  have hxj : x ^ (j * (V * p ^ r)) = x ^ j := by
    simpa only [← pow_mul, mul_assoc, mul_left_comm, mul_comm] using congrArg (· ^ j) hx
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    mul_pow, ← pow_mul, hxj, mul_assoc, mul_comm i]

private lemma natDegree_sum_degree_blocks_lt {F : Type*} [Field F] {m q u L : ℕ}
    (hL : 0 < L) (g : Polynomial F) (hg : g.natDegree = m * L)
    (e : Fin q × Fin (u + 1) → Polynomial F) (he : ∀ a, (e a).natDegree < L) :
    (∑ a, e a * g ^ a.1.val * Polynomial.X ^ (a.2.val * (q * L))).natDegree <
      L + (q - 1) * (m * L) + u * (q * L) := by
  have hterm (a : Fin q × Fin (u + 1)) :
      (e a * g ^ a.1.val * Polynomial.X ^ (a.2.val * (q * L))).natDegree ≤
        (L - 1) + (q - 1) * (m * L) + u * (q * L) := by
    refine Polynomial.natDegree_mul_le.trans (add_le_add
      (Polynomial.natDegree_mul_le.trans ?_) ?_)
    · refine add_le_add (Nat.le_pred_of_lt (he a)) ?_
      rw [Polynomial.natDegree_pow, hg]
      exact Nat.mul_le_mul_right _ (Nat.le_pred_of_lt a.1.isLt)
    · simpa using Nat.mul_le_mul_right (q * L) (Nat.le_of_lt_succ a.2.isLt)
  exact (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun a _ ↦ hterm a)).trans_lt
    (by omega)

private lemma exists_auxiliary_polynomial {F : Type*} [Field F]
    {p r V m q u L D M : ℕ} [ExpChar F p]
    (hL : 0 < L) (hmq : m.Coprime q) (H G : Polynomial F) (hH : H ≠ 0)
    (hdeg : (H ^ (p ^ r)).natDegree = m * L) (hG : G.natDegree ≤ D)
    (hdim : M * (L + (q - 1) * D + u) < q * (u + 1) * L)
    (hM : M ≤ p ^ r) (hT : q * L = p ^ r * V) (S : Finset F)
    (hS : ∀ x ∈ S, x ^ (q * L) = x ∧ H.eval x ^ (p ^ r) = G.eval x) :
    ∃ P : Polynomial F, P ≠ 0 ∧
      P.natDegree < L + (q - 1) * (m * L) + u * (q * L) ∧
      ∀ x ∈ S, (Polynomial.X - Polynomial.C x) ^ M ∣ P := by
  classical
  obtain ⟨e, he, hne, hjet⟩ := exists_jet_relation hL G hG hdim
  let P := ∑ a, e a * (H ^ (p ^ r)) ^ a.1.val * Polynomial.X ^ (a.2.val * (q * L))
  have hroots : ∀ x ∈ S, (Polynomial.X - Polynomial.C x) ^ M ∣ P := by
    intro x hx
    refine (pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero P x M).mpr (fun n hn ↦ ?_)
    simpa only [P, map_sum, Polynomial.eval_finsetSum, hT,
      hasseDeriv_eval_degree_block (x := x) (V := V) (hn := hn.trans_le hM)
        (hx := by simpa only [← hT] using (hS x hx).1), (hS x hx).2,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      using congrArg (Polynomial.eval x) (hjet n hn)
  exact ⟨P, sum_degree_blocks_ne_zero hmq hL _ (pow_ne_zero _ hH) hdeg e he hne,
    natDegree_sum_degree_blocks_lt hL _ hdeg e he, hroots⟩

private lemma card_mul_le_natDegree_of_pow_dvd {F : Type*} [Field F]
    (S : Finset F) (P : Polynomial F) (hP : P ≠ 0) (M : ℕ)
    (hS : ∀ x ∈ S, (Polynomial.X - Polynomial.C x) ^ M ∣ P) :
    S.card * M ≤ P.natDegree := by
  have hd := Finset.prod_dvd_of_coprime
    (fun a _ b _ hab ↦ (Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab).pow) hS
  simpa [Polynomial.natDegree_prod S (fun x ↦ (Polynomial.X - Polynomial.C x) ^ M)
    (fun x _ ↦ pow_ne_zero M (Polynomial.X_sub_C_ne_zero x))]
    using Polynomial.natDegree_le_of_dvd hd hP

private lemma natDegree_sum_frobenius_powers {F : Type*} [Field F] {q : ℕ}
    (hq : 1 < q) (f : Polynomial F) (hf : 0 < f.natDegree) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), f ^ (q ^ j)).natDegree = f.natDegree * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine (Polynomial.natDegree_add_eq_right_of_natDegree_lt ?_).trans
      (by simp [Polynomial.natDegree_pow, Nat.mul_comm])
    simpa only [ih, Polynomial.natDegree_pow, Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hq (Nat.lt_succ_self n)) hf

private lemma sum_frobenius_powers_add {F : Type*} [CommRing F] {p q a : ℕ}
    [ExpChar F p] (hq : q = p ^ a) (x : F) (k t : ℕ) :
    ∑ j ∈ Finset.range (k + t), x ^ (q ^ j) =
      (∑ j ∈ Finset.range k, x ^ (q ^ j)) +
        (∑ j ∈ Finset.range t, x ^ (q ^ j)) ^ (q ^ k) := by
  rw [Finset.sum_range_add]
  congr 1
  have hk : q ^ k = p ^ (a * k) := by rw [hq, pow_mul]
  rw [hk, sum_pow_char_pow, ← hk]
  simp only [← pow_mul, ← pow_add, Nat.add_comm]

private lemma natDegree_C_sub_sum_frobenius_powers_le {F : Type*} [Field F] {q k : ℕ}
    (hq : 1 < q) (f : Polynomial F) (hf : 0 < f.natDegree) (hk : 0 < k) (b : F) :
    (Polynomial.C b - ∑ j ∈ Finset.range k, f ^ (q ^ j)).natDegree ≤
      f.natDegree * q ^ (k - 1) := by
  have hlow := natDegree_sum_frobenius_powers hq f hf (k - 1)
  rw [Nat.sub_add_cancel hk] at hlow
  simpa only [Polynomial.natDegree_C, zero_max, hlow] using
    Polynomial.natDegree_sub_le (Polynomial.C b) (∑ j ∈ Finset.range k, f ^ (q ^ j))

private lemma eval_sum_frobenius_powers_high {F : Type*} [Field F] {p q a k t : ℕ}
    [ExpChar F p] (hqa : q = p ^ a) (f : Polynomial F) (x b : F)
    (hx : ∑ j ∈ Finset.range (k + t + 1), f.eval x ^ (q ^ j) = b) :
    (∑ j ∈ Finset.range (t + 1), f ^ (q ^ j)).eval x ^ (p ^ (a * k)) =
      (Polynomial.C b - ∑ j ∈ Finset.range k, f ^ (q ^ j)).eval x := by
  have hqk : q ^ k = p ^ (a * k) := by rw [hqa, pow_mul]
  have hsplit := sum_frobenius_powers_add hqa (f.eval x) k (t + 1)
  rw [← Nat.add_assoc, hx] at hsplit
  simpa only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, ← hqk] using eq_sub_of_add_eq' hsplit.symm

private lemma auxiliary_trace_parameters {q m k t u : ℕ} (hq : 1 < q)
    (hm : 0 < m) (hk : 0 < k) (ht : t ≤ k) (hu : q * u * m ≤ q ^ t) :
    q * u ≤ q ^ k ∧
      q * u * (q ^ (k + t) + (q - 1) * (m * q ^ (k - 1)) + u) <
        q * (u + 1) * q ^ (k + t) := by
  have hq₀ : 0 < q := by omega
  have hM : q * u ≤ q ^ k := ((Nat.le_mul_of_pos_right _ hm).trans hu).trans
    (Nat.pow_le_pow_right hq₀ ht)
  have hpow : q ^ k = q * q ^ (k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ']
  have hu' : u ≤ m * q ^ (k - 1) :=
    (Nat.le_of_mul_le_mul_left (hpow ▸ hM) hq₀).trans
      (by simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right (q ^ (k - 1)) hm)
  have hbracket : (q - 1) * (m * q ^ (k - 1)) + u ≤ m * q ^ k := by
    rw [hpow]
    nlinarith [Nat.sub_add_cancel hq₀]
  have hsmall : q * u * ((q - 1) * (m * q ^ (k - 1)) + u) ≤ q ^ (k + t) := by
    refine (Nat.mul_le_mul_left (q * u) hbracket).trans ?_
    simpa only [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (q ^ k) hu
  exact ⟨hM, by nlinarith [pow_pos hq₀ (k + t)]⟩

private lemma exists_trace_auxiliary_polynomial {F : Type*} [Field F]
    {p q a k t u : ℕ} [ExpChar F p] (hq : 1 < q) (hqa : q = p ^ a)
    (f : Polynomial F) (hf : 0 < f.natDegree) (hmq : f.natDegree.Coprime q)
    (hk : 0 < k) (ht : t ≤ k) (hu : q * u * f.natDegree ≤ q ^ t)
    (b : F) (S : Finset F)
    (hS : ∀ x ∈ S, x ^ (q ^ (k + t + 1)) = x ∧
      ∑ j ∈ Finset.range (k + t + 1), f.eval x ^ (q ^ j) = b) :
    ∃ P : Polynomial F, P ≠ 0 ∧
      P.natDegree < f.natDegree * q ^ (k + t + 1) + q * u * q ^ (k + t) ∧
      ∀ x ∈ S, (Polynomial.X - Polynomial.C x) ^ (q * u) ∣ P := by
  let H := ∑ j ∈ Finset.range (t + 1), f ^ (q ^ j)
  let G := Polynomial.C b - ∑ j ∈ Finset.range k, f ^ (q ^ j)
  have hq₀ : 0 < q := by omega
  have hHdeg : H.natDegree = f.natDegree * q ^ t :=
    natDegree_sum_frobenius_powers hq f hf t
  have hH : H ≠ 0 := by
    intro hz
    simpa [hz] using
      (mul_pos hf (pow_pos hq₀ t)).trans_eq hHdeg.symm
  have hqk : q ^ k = p ^ (a * k) := by rw [hqa, pow_mul]
  have hdeg : (H ^ (p ^ (a * k))).natDegree = f.natDegree * q ^ (k + t) := by
    simp only [← hqk, Polynomial.natDegree_pow, hHdeg, pow_add,
      Nat.mul_left_comm]
  have hG : G.natDegree ≤ f.natDegree * q ^ (k - 1) :=
    natDegree_C_sub_sum_frobenius_powers_le hq f hf hk b
  have hT : q * q ^ (k + t) = p ^ (a * k) * q ^ (t + 1) := by
    rw [← hqk]
    simp only [pow_add, pow_succ', Nat.mul_left_comm]
  have hroots (x : F) (hx : x ∈ S) :
      x ^ (q * q ^ (k + t)) = x ∧ H.eval x ^ (p ^ (a * k)) = G.eval x := by
    exact ⟨by simpa only [← pow_succ'] using (hS x hx).1,
      eval_sum_frobenius_powers_high hqa f x b (hS x hx).2⟩
  obtain ⟨hM, hdim⟩ := auxiliary_trace_parameters hq hf hk ht hu
  obtain ⟨P, hP, hPdeg, hPS⟩ := exists_auxiliary_polynomial (pow_pos hq₀ (k + t))
    hmq H G hH hdeg hG hdim (hqk ▸ hM) hT S hroots
  refine ⟨P, hP, hPdeg.trans_le ?_, hPS⟩
  rw [pow_succ']
  nlinarith [Nat.sub_add_cancel hq₀, Nat.le_mul_of_pos_right (q ^ (k + t)) hf]

private lemma card_trace_fiber_mul_lt {F E : Type*} [Field F] [Field E]
    [Fintype F] [Finite E] [Algebra F E] {p a k t u : ℕ} [ExpChar E p]
    (hqa : Fintype.card F = p ^ a) (hdegree : Module.finrank F E = k + t + 1)
    (f : Polynomial E) (hf : 0 < f.natDegree) (hmq : f.natDegree.Coprime (Fintype.card F))
    (hk : 0 < k) (ht : t ≤ k) (hu : Fintype.card F * u * f.natDegree ≤ Fintype.card F ^ t)
    (b : F) :
    Nat.card {x : E // Algebra.trace F E (f.eval x) = b} * (Fintype.card F * u) <
      f.natDegree * Fintype.card F ^ (k + t + 1) +
        Fintype.card F * u * Fintype.card F ^ (k + t) := by
  classical
  letI := Fintype.ofFinite E
  let S := Finset.univ.filter (fun x : E ↦ Algebra.trace F E (f.eval x) = b)
  have hS (x : E) (hx : x ∈ S) :
      x ^ (Fintype.card F ^ (k + t + 1)) = x ∧
        ∑ j ∈ Finset.range (k + t + 1), f.eval x ^ (Fintype.card F ^ j) =
          algebraMap F E b := by
    refine ⟨?_, ?_⟩
    · rw [← hdegree, ← Module.card_eq_pow_finrank]
      exact FiniteField.pow_card x
    · simpa only [hdegree, Nat.card_eq_fintype_card, (Finset.mem_filter.mp hx).2] using
        (FiniteField.algebraMap_trace_eq_sum_pow F E (f.eval x)).symm
  obtain ⟨P, hP, hdeg, hPS⟩ := exists_trace_auxiliary_polynomial Fintype.one_lt_card hqa
    f hf hmq hk ht hu (algebraMap F E b) S hS
  simpa only [S, Nat.card_eq_fintype_card, Fintype.card_subtype] using
    (card_mul_le_natDegree_of_pow_dvd S P hP _ hPS).trans_lt hdeg

private lemma trace_multiplicity_bounds {q m t : ℕ} (hm : 0 < m)
    (ht : 0 < t) (hmt : m ≤ q ^ (t - 1)) :
    q * (q ^ (t - 1) / m) * m ≤ q ^ t ∧
      q ^ t ≤ 2 * (q * (q ^ (t - 1) / m)) * m := by
  have hpow : q ^ t = q * q ^ (t - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ']
  have hhalf : q ^ (t - 1) ≤ 2 * ((q ^ (t - 1) / m) * m) := by
    nlinarith [Nat.lt_div_mul_add (a := q ^ (t - 1)) hm,
      Nat.le_mul_of_pos_right m (Nat.div_pos hmt hm)]
  simpa only [hpow, Nat.mul_assoc, Nat.mul_left_comm] using
    And.intro (Nat.mul_le_mul_left q (Nat.div_mul_le_self (q ^ (t - 1)) m))
      (Nat.mul_le_mul_left q hhalf)

private lemma card_trace_fiber_lt_of_degree_le {F E : Type*} [Field F] [Field E]
    [Fintype F] [Finite E] [Algebra F E] {p a k t : ℕ} [ExpChar E p]
    (hqa : Fintype.card F = p ^ a) (hdegree : Module.finrank F E = k + t + 1)
    (f : Polynomial E) (hf : 0 < f.natDegree) (hmq : f.natDegree.Coprime (Fintype.card F))
    (hk : 0 < k) (ht : t ≤ k) (ht₀ : 0 < t)
    (hmt : f.natDegree ≤ Fintype.card F ^ (t - 1)) (b : F) :
    Nat.card {x : E // Algebra.trace F E (f.eval x) = b} <
      Fintype.card F ^ (k + t) + 2 * f.natDegree ^ 2 * Fintype.card F ^ (k + 1) := by
  obtain ⟨hu, hM⟩ := trace_multiplicity_bounds hf ht₀ hmt
  have hcount := card_trace_fiber_mul_lt hqa hdegree f hf hmq hk ht hu b
  have herror : f.natDegree * Fintype.card F ^ (k + t + 1) ≤
      (2 * f.natDegree ^ 2 * Fintype.card F ^ (k + 1)) *
        (Fintype.card F * (Fintype.card F ^ (t - 1) / f.natDegree)) := by
    simpa only [pow_add, pow_one, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using Nat.mul_le_mul_left (f.natDegree * Fintype.card F ^ (k + 1)) hM
  exact Nat.lt_of_mul_lt_mul_right (hcount.trans_le
    (by nlinarith : f.natDegree * Fintype.card F ^ (k + t + 1) +
      Fintype.card F * (Fintype.card F ^ (t - 1) / f.natDegree) * Fintype.card F ^ (k + t) ≤
        (Fintype.card F ^ (k + t) + 2 * f.natDegree ^ 2 * Fintype.card F ^ (k + 1)) *
          (Fintype.card F * (Fintype.card F ^ (t - 1) / f.natDegree))))

private lemma card_trace_fiber_lt_of_pow_le {F E : Type*} [Field F] [Field E]
    [Fintype F] [Finite E] [Algebra F E] {k t : ℕ}
    (hdegree : Module.finrank F E = k + t + 1) (f : Polynomial E) (hf : 0 < f.natDegree)
    (hsmall : Fintype.card F ^ t ≤ f.natDegree * Fintype.card F) (b : F) :
    Nat.card {x : E // Algebra.trace F E (f.eval x) = b} <
      Fintype.card F ^ (k + t) + 2 * f.natDegree ^ 2 * Fintype.card F ^ (k + 2) := by
  letI := Fintype.ofFinite E
  have hcard : Nat.card {x : E // Algebra.trace F E (f.eval x) = b} ≤
      Fintype.card F ^ (k + t + 1) := by
    simpa only [Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := F) (V := E), hdegree] using
      Nat.card_le_card_of_injective (fun x : {x : E // Algebra.trace F E (f.eval x) = b} ↦
        (x : E)) Subtype.val_injective
  have hbound : Fintype.card F ^ (k + t + 1) ≤ f.natDegree * Fintype.card F ^ (k + 2) := by
    simpa only [pow_add, pow_one, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using Nat.mul_le_mul_left (Fintype.card F ^ (k + 1)) hsmall
  exact (hcard.trans hbound).trans_lt (by
    nlinarith [pow_pos (Fintype.card_pos (α := F)) (k + t),
      Nat.le_mul_of_pos_right (f.natDegree * Fintype.card F ^ (k + 2)) hf])

private lemma card_trace_fiber_lt {F E : Type*} [Field F] [Field E]
    [Fintype F] [Finite E] [Algebra F E] {p a k t : ℕ} [ExpChar E p]
    (hqa : Fintype.card F = p ^ a) (hdegree : Module.finrank F E = k + t + 1)
    (f : Polynomial E) (hf : 0 < f.natDegree) (hmq : f.natDegree.Coprime (Fintype.card F))
    (hk : 0 < k) (ht : t ≤ k) (b : F) :
    Nat.card {x : E // Algebra.trace F E (f.eval x) = b} <
      Fintype.card F ^ (k + t) + 2 * f.natDegree ^ 2 * Fintype.card F ^ (k + 2) := by
  by_cases hsmall : Fintype.card F ^ t ≤ f.natDegree * Fintype.card F
  · exact card_trace_fiber_lt_of_pow_le hdegree f hf hsmall b
  · have ht₀ : 0 < t := by
      by_contra! hz
      simp only [Nat.eq_zero_of_le_zero hz, pow_zero, not_le] at hsmall
      exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt (Nat.mul_pos hf Fintype.card_pos))) hsmall
    have hpow : Fintype.card F ^ t = Fintype.card F * Fintype.card F ^ (t - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel ht₀, pow_succ']
    have hmt : f.natDegree ≤ Fintype.card F ^ (t - 1) := Nat.le_of_mul_le_mul_left
      (by simpa only [hpow, Nat.mul_comm] using (Nat.lt_of_not_ge hsmall).le) Fintype.card_pos
    exact (card_trace_fiber_lt_of_degree_le hqa hdegree f hf hmq hk ht ht₀ hmt b).trans_le
      (Nat.add_le_add_left (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right Fintype.card_pos (by omega))) _)

private lemma abs_le_card_mul_of_sum_eq_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {D : ℝ} (hD : 0 ≤ D) (hsum : ∑ i, w i = 0)
    (hw : ∀ i, w i ≤ D) (i : ι) : |w i| ≤ Fintype.card ι * D := by
  classical
  have hrest := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ ↦ hw j)
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ i), hsum, zero_sub,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hrest
  have hc : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨i⟩)
  exact abs_le.mpr ⟨by linarith, by nlinarith [hw i]⟩

private lemma abs_card_trace_fiber_sub_le {F E : Type*} [Field F] [Field E]
    [Fintype F] [Finite E] [Algebra F E] {p a k t : ℕ} [ExpChar E p]
    (hqa : Fintype.card F = p ^ a) (hdegree : Module.finrank F E = k + t + 1)
    (f : Polynomial E) (hf : 0 < f.natDegree) (hmq : f.natDegree.Coprime (Fintype.card F))
    (hk : 0 < k) (ht : t ≤ k) (b : F) :
    |(Nat.card {x : E // Algebra.trace F E (f.eval x) = b} : ℝ) -
      (Fintype.card F : ℝ) ^ (k + t)| ≤
        2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (k + 3) := by
  classical
  letI := Fintype.ofFinite E
  let w (b : F) : ℝ := Nat.card {x : E // Algebra.trace F E (f.eval x) = b} -
    (Fintype.card F : ℝ) ^ (k + t)
  have hcard : (∑ b : F, Nat.card {x : E // Algebra.trace F E (f.eval x) = b}) =
      Fintype.card F ^ (k + t + 1) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma,
      Module.card_eq_pow_finrank (K := F) (V := E), hdegree] using
        Fintype.card_congr (Equiv.sigmaFiberEquiv (fun x : E ↦ Algebra.trace F E (f.eval x)))
  have hsum : ∑ b, w b = 0 := by
    simp only [w, Finset.sum_sub_distrib, ← Nat.cast_sum, hcard, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Nat.cast_pow, Nat.cast_mul, pow_succ', sub_self]
  have hw (b : F) : w b ≤ 2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (k + 2) := by
    exact sub_le_iff_le_add.mpr (by
      exact_mod_cast (card_trace_fiber_lt hqa hdegree f hf hmq hk ht b).le.trans_eq
        (Nat.add_comm _ _))
  simpa only [w, show k + 3 = (k + 2) + 1 by omega, pow_succ', mul_left_comm] using
    abs_le_card_mul_of_sum_eq_zero w (by positivity) hsum hw b

private lemma norm_sum_addChar_comp_le_of_fiber_bound {F E : Type*} [CommRing F]
    [Fintype F] [Fintype E] (g : E → F) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    {A D : ℝ} (hbound : ∀ b : F, |(Nat.card {x : E // g x = b} : ℝ) - A| ≤ D) :
    ‖∑ x : E, ψ (g x)‖ ≤ Fintype.card F * D := by
  classical
  have hgroup := (Equiv.sigmaFiberEquiv g).sum_comp (fun x ↦ ψ (g x))
  have heq : ∑ x : E, ψ (g x) = ∑ b : F, (Nat.card {x : E // g x = b} : ℂ) * ψ b := by
    have hx (b : F) (x : {x : E // g x = b}) : g x = b := x.property
    simpa [Equiv.sigmaFiberEquiv, Fintype.sum_sigma, hx] using hgroup.symm
  have hcenter : ∑ x : E, ψ (g x) =
      ∑ b : F, ((Nat.card {x : E // g x = b} : ℂ) - A) * ψ b := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
      AddChar.sum_eq_zero_of_ne_one hψ, mul_zero, sub_zero, heq]
  have hterm (b : F) : ‖((Nat.card {x : E // g x = b} : ℂ) - A) * ψ b‖ ≤ D := by
    simpa only [norm_mul, AddChar.norm_apply, mul_one, ← Complex.ofReal_natCast,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hbound b
  simpa only [← hcenter, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun b _ ↦ hterm b))

private lemma norm_sum_addChar_trace_le {F E : Type*} [Field F] [Field E]
    [Fintype F] [Fintype E] [Algebra F E] {p a k t : ℕ} [ExpChar E p]
    (hqa : Fintype.card F = p ^ a) (hdegree : Module.finrank F E = k + t + 1)
    (f : Polynomial E) (hf : 0 < f.natDegree) (hmq : f.natDegree.Coprime (Fintype.card F))
    (hk : 0 < k) (ht : t ≤ k) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖∑ x : E, ψ (Algebra.trace F E (f.eval x))‖ ≤
      2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (k + 4) := by
  simpa only [show k + 4 = (k + 3) + 1 by omega, pow_succ', mul_left_comm] using
    norm_sum_addChar_comp_le_of_fiber_bound (fun x : E ↦ Algebra.trace F E (f.eval x)) ψ hψ
      (abs_card_trace_fiber_sub_le hqa hdegree f hf hmq hk ht)

private lemma norm_sum_addChar_trace_le_sqrt_card_of_two_le {F E : Type*} [Field F] [Field E]
    [Fintype F] [Fintype E] [Algebra F E] (hdegree : 2 ≤ Module.finrank F E)
    (f : Polynomial E) (hf : 0 < f.natDegree) (hmq : f.natDegree.Coprime (Fintype.card F))
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖∑ x : E, ψ (Algebra.trace F E (f.eval x))‖ ≤
      (2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 4) *
        Real.sqrt (Fintype.card E) := by
  obtain ⟨a, hp, hqa⟩ := FiniteField.card F (ringChar F)
  letI : Fact (ringChar F).Prime := ⟨hp⟩
  letI : CharP E (ringChar F) := (Algebra.charP_iff F E _).mp inferInstance
  have hroot : (Fintype.card F : ℝ) ^ (Module.finrank F E / 2) ≤
      Real.sqrt (Fintype.card E) := by
    apply Real.le_sqrt_of_sq_le
    rw [← pow_mul, Module.card_eq_pow_finrank (K := F) (V := E), Nat.cast_pow]
    exact_mod_cast Nat.pow_le_pow_right (Fintype.card_pos (α := F))
      (Nat.div_mul_le_self (Module.finrank F E) 2)
  have hsum := norm_sum_addChar_trace_le hqa (k := Module.finrank F E / 2)
    (t := Module.finrank F E - Module.finrank F E / 2 - 1) (by omega)
    f hf hmq (by omega) (by omega) ψ hψ
  exact hsum.trans (by
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hroot
        (by positivity : 0 ≤ 2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 4))

private lemma norm_sum_addChar_trace_le_sqrt_card {F E : Type*} [Field F] [Field E]
    [Fintype F] [Fintype E] [Algebra F E]
    (f : Polynomial E) (hf : 0 < f.natDegree) (hmq : f.natDegree.Coprime (Fintype.card F))
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖∑ x : E, ψ (Algebra.trace F E (f.eval x))‖ ≤
      (2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 4) *
        Real.sqrt (Fintype.card E) := by
  by_cases hdegree : 2 ≤ Module.finrank F E
  · exact norm_sum_addChar_trace_le_sqrt_card_of_two_le hdegree f hf hmq ψ hψ
  · have hN : Module.finrank F E = 1 := by
      have := Module.finrank_pos (R := F) (M := E)
      omega
    have hcard : Fintype.card E = Fintype.card F := by
      rw [Module.card_eq_pow_finrank (K := F) (V := E), hN, pow_one]
    have hsum : ‖∑ x : E, ψ (Algebra.trace F E (f.eval x))‖ ≤ (Fintype.card F : ℝ) := by
      simpa only [AddChar.norm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one, hcard] using norm_sum_le Finset.univ (fun x : E ↦
          ψ (Algebra.trace F E (f.eval x)))
    have hroot : 1 ≤ Real.sqrt (Fintype.card E) := Real.le_sqrt_of_sq_le (by
      exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := E)))
    have hcoeff : (Fintype.card F : ℝ) ≤
        2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 4 := by
      exact_mod_cast ((Nat.le_self_pow (by decide : 4 ≠ 0) (Fintype.card F)).trans
        (Nat.le_mul_of_pos_right _ (by positivity : 0 < 2 * f.natDegree ^ 2))).trans_eq
          (Nat.mul_comm _ _)
    exact (hsum.trans hcoeff).trans (le_mul_of_one_le_right (by positivity) hroot)

private lemma finite_fourier_orthogonality {F : Type*} [CommRing F] [Fintype F]
    [DecidableEq F] (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (k l : F) :
    ∑ x : F, ψ (x * (k - l)) = if k = l then Fintype.card F else 0 := by
  rw [AddChar.sum_mulShift (k - l) hψ]
  simp only [sub_eq_zero]

private lemma finite_fourier_parseval_complex {F : Type*} [CommRing F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (w : F → ℂ) :
    ∑ k : F, (∑ x : F, w x * ψ (x * k)) * starRingEnd ℂ (∑ x : F, w x * ψ (x * k)) =
      (Fintype.card F : ℂ) * ∑ x : F, w x * starRingEnd ℂ (w x) := by
  classical
  simp only [map_sum, map_mul, ← AddChar.map_neg_eq_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, y]; rw [Finset.sum_comm]
  simp_rw [mul_mul_mul_comm (w _) (ψ _) ((starRingEnd ℂ) (w _)) (ψ _),
    ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, mul_comm (_ - _),
    ← Finset.mul_sum, finite_fourier_orthogonality ψ hψ]
  simp [Finset.mul_sum, mul_comm, mul_left_comm]

private lemma finite_fourier_parseval {F : Type*} [CommRing F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (w : F → ℂ) :
    ∑ k : F, ‖∑ x : F, w x * ψ (x * k)‖ ^ 2 =
      Fintype.card F * ∑ x : F, ‖w x‖ ^ 2 := by
  have h := finite_fourier_parseval_complex ψ hψ w
  simpa only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re] using congrArg Complex.re h

private def fieldResidueEquiv {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F) :
    F ≃ Fin (p ^ r) :=
  b.equivFun.toEquiv.trans
    ((Equiv.piCongrRight fun _ ↦ (ZMod.finEquiv p).toEquiv.symm).trans
      finFunctionFinEquiv)

private def powerCoordinateBlock {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) : Fin (p ^ m) :=
  finFunctionFinEquiv fun j : Fin m ↦
    (ZMod.finEquiv p).symm
      (b.equivFun (x ^ (j.val / r + 2)) ⟨j.val % r, Nat.mod_lt _ hr⟩)

private def powerDigit {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) : ℕ :=
  (fieldResidueEquiv b x).val + p ^ r * (powerCoordinateBlock b hr m x).val

private lemma powerDigit_lt {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) : powerDigit b hr m x < p ^ (r + m) := by
  simpa only [powerDigit, pow_add] using
    (Nat.add_lt_add_right (fieldResidueEquiv b x).isLt
      (p ^ r * (powerCoordinateBlock b hr m x).val)).trans_le
      (by simpa only [Nat.mul_succ, add_comm] using
        Nat.mul_le_mul_left (p ^ r) (powerCoordinateBlock b hr m x).isLt)

private lemma powerDigit_mod {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) :
    powerDigit b hr m x % p ^ r = (fieldResidueEquiv b x).val := by
  simp [powerDigit, Nat.mod_eq_of_lt (fieldResidueEquiv b x).isLt]

private lemma powerDigit_injective {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) : Function.Injective (powerDigit b hr m) := by
  exact fun x y h ↦ (fieldResidueEquiv b).injective (Fin.ext
    (by simpa only [powerDigit_mod] using congrArg (· % p ^ r) h))

private def powerDigitSet {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ) : Finset ℕ :=
  Finset.univ.image (powerDigit b hr m)

private lemma card_powerDigitSet {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ) :
    (powerDigitSet b hr m).card = p ^ r := by
  simpa only [powerDigitSet, Finset.card_image_of_injective _
    (powerDigit_injective b hr m), Finset.card_univ, Fintype.card_fin] using
      Fintype.card_congr (fieldResidueEquiv b)

private lemma powerDigitSet_nonempty {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ) :
    (powerDigitSet b hr m).Nonempty :=
  Finset.univ_nonempty.image (powerDigit b hr m)

private lemma mem_powerDigitSet_lt {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ)
    {d : ℕ} (hd : d ∈ powerDigitSet b hr m) : d < p ^ (r + m) := by
  exact (Finset.mem_image.mp hd).elim fun x hx ↦ hx.2 ▸ powerDigit_lt b hr m x

private lemma natCast_finEquiv {n : ℕ} [NeZero n] (i : Fin n) :
    (i.val : ZMod n) = ZMod.finEquiv n i := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact ZMod.natCast_zmod_val (n := n + 1) i

private def fieldCyclicEquiv {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F) :
    F ≃ ZMod (p ^ r) :=
  (fieldResidueEquiv b).trans (ZMod.finEquiv (p ^ r)).toEquiv

private lemma powerDigit_cast {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) :
    (powerDigit b hr m x : ZMod (p ^ r)) = fieldCyclicEquiv b x := by
  simpa only [ZMod.natCast_mod, natCast_finEquiv, fieldCyclicEquiv,
    Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe] using
      congrArg (fun n : ℕ ↦ (n : ZMod (p ^ r))) (powerDigit_mod b hr m x)

private lemma powerDigit_orthogonality {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ)
    (k l : ZMod (p ^ r)) :
    ∑ x : F, ZMod.stdAddChar ((powerDigit b hr m x : ZMod (p ^ r)) * (k - l)) =
      if k = l then (p ^ r : ℕ) else 0 := by
  simpa only [powerDigit_cast] using
    ((fieldCyclicEquiv b).sum_comp (fun x ↦ ZMod.stdAddChar (x * (k - l)))).trans
      (by
        simpa only [ZMod.card] using finite_fourier_orthogonality
          ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar (p ^ r)) k l)

private def powerFrequency (p r m : ℕ) (k : ZMod (p ^ r)) : ℤ :=
  (p ^ m : ℕ) * k.valMinAbs

private lemma powerFrequency_bound {p r m : ℕ} [NeZero p] (hp : Odd p)
    (k : ZMod (p ^ r)) : 2 * |powerFrequency p r m k| ≤ (p ^ (r + m) : ℕ) - (1 : ℤ) := by
  have hsmall : 2 * k.valMinAbs.natAbs + 1 ≤ p ^ r := by
    have hmod := Nat.odd_iff.mp (hp.pow (n := r))
    have hbound := k.natAbs_valMinAbs_le
    omega
  have hcast : 2 * |k.valMinAbs| + 1 ≤ (p ^ r : ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Int.natCast_natAbs]
      using Int.ofNat_le.mpr hsmall
  have hmul := mul_le_mul_of_nonneg_left hcast (show 0 ≤ (p ^ m : ℤ) by positivity)
  have hpos : 0 < (p : ℤ) ^ m := pow_pos (Nat.cast_pos.mpr (NeZero.pos p)) m
  simp only [powerFrequency, abs_mul, Nat.cast_pow, pow_add, Nat.cast_mul, abs_of_pos hpos]
  push_cast at hmul
  nlinarith

private lemma powerDigit_eq_sum {p r m : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (x : F) :
    powerDigit b hr m x = ∑ j : Fin (r + m),
      ((ZMod.finEquiv p).symm
        (b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩)).val * p ^ j.val := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Nat.div_eq_of_lt, Nat.mod_eq_of_lt,
    Fin.isLt, Nat.add_div_left _ hr, Nat.add_mod_left, zero_add, pow_one]
  simp only [powerDigit, fieldResidueEquiv, powerCoordinateBlock, Equiv.trans_apply,
    LinearEquiv.coe_toEquiv, Equiv.piCongrRight_apply, finFunctionFinEquiv_apply]
  simp [Pi.map, pow_add, Finset.mul_sum, mul_left_comm, Nat.add_assoc]

private def powerPhasePolynomial {p r q : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (a : Fin q → ZMod p) :
    Polynomial F :=
  ∑ j, Polynomial.monomial (j.val / r + 1)
    (a j • b.traceDual ⟨j.val % r, Nat.mod_lt _ hr⟩)

private lemma powerPhasePolynomial_coeff_repr {p r q : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (a : Fin q → ZMod p) (j : Fin q) :
    b.traceDual.repr ((powerPhasePolynomial b hr a).coeff (j.val / r + 1))
      ⟨j.val % r, Nat.mod_lt _ hr⟩ = a j := by
  simp only [powerPhasePolynomial, Polynomial.finsetSum_coeff, map_sum, Finsupp.finsetSum_apply,
    Polynomial.coeff_monomial, apply_ite, DFunLike.ite_apply, map_zero, map_smul,
    Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, Fin.mk.injEq, smul_eq_mul,
    Finsupp.zero_apply, mul_one, mul_zero, Nat.add_left_inj,
    ← ite_and, ← Nat.ext_div_mod_iff, Fin.val_inj]
  simp

private lemma powerPhasePolynomial_natDegree_pos {p r q : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) {a : Fin q → ZMod p} (ha : a ≠ 0) :
    0 < (powerPhasePolynomial b hr a).natDegree := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  have hc : (powerPhasePolynomial b hr a).coeff (j.val / r + 1) ≠ 0 := by
    intro hc
    exact hj (by simpa only [hc, map_zero, Finsupp.zero_apply, Pi.zero_apply] using
      (powerPhasePolynomial_coeff_repr b hr a j).symm)
  exact (Nat.zero_lt_succ _).trans_le (Polynomial.le_natDegree_of_ne_zero hc)

private lemma powerPhasePolynomial_natDegree_le_of_le_mul {p r q d : ℕ}
    [Fact p.Prime] {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (a : Fin q → ZMod p)
    (hqd : q ≤ r * d) : (powerPhasePolynomial b hr a).natDegree ≤ d := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ ↦
    (Polynomial.natDegree_monomial_le _).trans ?_)
  exact Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hr).mpr
    (j.isLt.trans_le (hqd.trans_eq (Nat.mul_comm r d))))

private lemma trace_powerPhasePolynomial_eval {p r q : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (a : Fin q → ZMod p) (x : F) :
    Algebra.trace (ZMod p) F ((powerPhasePolynomial b hr a).eval x) =
      ∑ j, a j * b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩ := by
  simp only [powerPhasePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl (fun j _ ↦ congrArg (a j * ·) ?_)
  simpa only [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply,
    Module.Basis.equivFun_apply, mul_comm] using
    (b.traceDual.traceDual_repr_apply (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩).symm

private def logarithmicSeries {F : Type*} [Field F] (g : PowerSeries F) :
    PowerSeries F :=
  PowerSeries.derivative F g * g⁻¹

private lemma logarithmicSeries_mul {F : Type*} [Field F] (g h : PowerSeries F)
    (hg : PowerSeries.constantCoeff g ≠ 0) (hh : PowerSeries.constantCoeff h ≠ 0) :
    logarithmicSeries (g * h) = logarithmicSeries g + logarithmicSeries h := by
  simp only [logarithmicSeries, Derivation.leibniz, smul_eq_mul,
    PowerSeries.mul_inv_rev, add_mul]
  linear_combination (PowerSeries.derivative F h * h⁻¹) * PowerSeries.mul_inv_cancel g hg +
    (PowerSeries.derivative F g * g⁻¹) * PowerSeries.mul_inv_cancel h hh

private lemma coeff_inv_eq_of_coeff_eq {F : Type*} [Field F]
    (g h : PowerSeries F) {n : ℕ}
    (heq : ∀ k ≤ n, PowerSeries.coeff k g = PowerSeries.coeff k h) :
    PowerSeries.coeff n g⁻¹ = PowerSeries.coeff n h⁻¹ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [PowerSeries.coeff_inv, PowerSeries.coeff_inv]
    have hc : PowerSeries.constantCoeff g = PowerSeries.constantCoeff h := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using heq 0 (Nat.zero_le n)
    rw [hc]
    congr 2
    refine Finset.sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
    have hij' := Finset.mem_antidiagonal.mp hij
    split_ifs with hj
    · rw [heq i (by omega), ih j hj (fun k hk ↦ heq k (by omega))]
    · rfl

private lemma coeff_logarithmicSeries_sub {F : Type*} [Field F]
    (g h : PowerSeries F) {n : ℕ} (hg : PowerSeries.constantCoeff g = 1)
    (heq : ∀ k ≤ n, PowerSeries.coeff k g = PowerSeries.coeff k h) :
    PowerSeries.coeff n (logarithmicSeries g) -
      PowerSeries.coeff n (logarithmicSeries h) =
        (n + 1 : F) * (PowerSeries.coeff (n + 1) g - PowerSeries.coeff (n + 1) h) := by
  simp only [logarithmicSeries, PowerSeries.coeff_mul, ← Finset.sum_sub_distrib,
    PowerSeries.coeff_derivative]
  have hh : PowerSeries.constantCoeff h = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff, hg] using (heq 0 (Nat.zero_le n)).symm
  rw [Finset.sum_eq_single (n, 0)]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff, hg, hh, mul_sub, mul_comm]
  · rintro ⟨i, j⟩ hij hne
    have hij' := Finset.mem_antidiagonal.mp hij
    have hi : i + 1 ≤ n := by
      by_contra! hi
      exact hne (Prod.ext (by omega) (by omega))
    rw [heq (i + 1) hi, coeff_inv_eq_of_coeff_eq g h (fun k hk ↦ heq k (by omega)),
      sub_self]
  · simp

private def rootPowerSum {F : Type*} [Field F] (g : Polynomial F) : ℕ → F
  | 0 => g.natDegree
  | n + 1 => -PowerSeries.coeff n (logarithmicSeries (g.reverse : PowerSeries F))

private lemma rootPowerSum_mul {F : Type*} [Field F] (g h : Polynomial F)
    (hg : g.Monic) (hh : h.Monic) (n : ℕ) :
    rootPowerSum (g * h) n = rootPowerSum g n + rootPowerSum h n := by
  cases n with
  | zero => simp only [rootPowerSum, Polynomial.natDegree_mul hg.ne_zero hh.ne_zero, Nat.cast_add]
  | succ n =>
    simp only [rootPowerSum, Polynomial.reverse_mul_of_domain, Polynomial.coe_mul]
    rw [logarithmicSeries_mul _ _ (by simpa using hg.ne_zero) (by simpa using hh.ne_zero)]
    simp only [map_add, neg_add_rev, add_comm]

private def polynomialRootPhase {F : Type*} [Field F] (f g : Polynomial F) : F :=
  ∑ n ∈ Finset.range (f.natDegree + 1), f.coeff n * rootPowerSum g n

private lemma polynomialRootPhase_mul {F : Type*} [Field F] (f g h : Polynomial F)
    (hg : g.Monic) (hh : h.Monic) :
    polynomialRootPhase f (g * h) = polynomialRootPhase f g + polynomialRootPhase f h := by
  simp only [polynomialRootPhase, rootPowerSum_mul g h hg hh, mul_add,
    Finset.sum_add_distrib]

private lemma rootPowerSum_eq_of_reverse_coeff_eq {F : Type*} [Field F]
    (g h : Polynomial F) (hg : g.Monic) (hdeg : g.natDegree = h.natDegree) {n : ℕ}
    (heq : ∀ k ≤ n, g.reverse.coeff k = h.reverse.coeff k) :
    rootPowerSum g n = rootPowerSum h n := by
  cases n with
  | zero => simpa only [rootPowerSum] using congrArg (fun n : ℕ ↦ (n : F)) hdeg
  | succ n =>
    have hlog := coeff_logarithmicSeries_sub (g.reverse : PowerSeries F)
      (h.reverse : PowerSeries F) (n := n)
      (by simpa only [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse]
        using hg.leadingCoeff)
      (fun k hk ↦ by simpa only [Polynomial.coeff_coe] using heq k (by omega))
    simp only [Polynomial.coeff_coe, heq (n + 1) le_rfl, sub_self, mul_zero,
      sub_eq_zero] at hlog
    exact congrArg Neg.neg hlog

private lemma rootPowerSum_sub_of_reverse_coeff_eq {F : Type*} [Field F]
    (g h : Polynomial F) (hg : g.Monic) {n : ℕ} (hn : 0 < n)
    (heq : ∀ k < n, g.reverse.coeff k = h.reverse.coeff k) :
    rootPowerSum g n - rootPowerSum h n =
      -(n : F) * (g.reverse.coeff n - h.reverse.coeff n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa only [rootPowerSum, Polynomial.coeff_coe, Nat.cast_succ, neg_sub, neg_mul,
    neg_sub_neg]
    using congrArg Neg.neg (coeff_logarithmicSeries_sub
      (g.reverse : PowerSeries F) (h.reverse : PowerSeries F)
      (by simpa only [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse]
        using hg.leadingCoeff)
      (fun k hk ↦ by simpa only [Polynomial.coeff_coe] using heq k (Nat.lt_succ_of_le hk)))

private lemma monic_add_monomial_of_lt {F : Type*} [Field F]
    (g : Polynomial F) (hg : g.Monic) {j : ℕ} (hj : j < g.natDegree) (t : F) :
    (g + Polynomial.monomial j t).Monic ∧
      (g + Polynomial.monomial j t).natDegree = g.natDegree := by
  have hlt := (Polynomial.natDegree_monomial_le t).trans_lt hj
  exact ⟨hg.add_of_left (Polynomial.degree_lt_degree hlt),
    Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt⟩

private lemma reverse_coeff_add_monomial {F : Type*} [Field F]
    (g : Polynomial F) (hg : g.Monic) {j k : ℕ} (hj : j < g.natDegree)
    (hk : k ≤ g.natDegree) (t : F) :
    (g + Polynomial.monomial j t).reverse.coeff k =
      g.reverse.coeff k + if k = g.natDegree - j then t else 0 := by
  simp only [Polynomial.coeff_reverse, (monic_add_monomial_of_lt g hg hj t).2,
    Polynomial.revAt_le hk, Polynomial.coeff_add, Polynomial.coeff_monomial,
    show j = g.natDegree - k ↔ k = g.natDegree - j by omega]

private lemma rootPowerSum_add_monomial_of_lt {F : Type*} [Field F]
    (g : Polynomial F) (hg : g.Monic) {j k : ℕ} (hj : j < g.natDegree)
    (hk : k < g.natDegree - j) (t : F) :
    rootPowerSum (g + Polynomial.monomial j t) k = rootPowerSum g k := by
  refine rootPowerSum_eq_of_reverse_coeff_eq _ _ (monic_add_monomial_of_lt g hg hj t).1
    (monic_add_monomial_of_lt g hg hj t).2 (fun i hi ↦ ?_)
  simp only [reverse_coeff_add_monomial g hg hj (by omega : i ≤ g.natDegree) t,
    if_neg (by omega : i ≠ g.natDegree - j), add_zero]

private lemma rootPowerSum_add_monomial_top {F : Type*} [Field F]
    (g : Polynomial F) (hg : g.Monic) {j : ℕ} (hj : j < g.natDegree) (t : F) :
    rootPowerSum (g + Polynomial.monomial j t) (g.natDegree - j) -
      rootPowerSum g (g.natDegree - j) = -(g.natDegree - j : ℕ) * t := by
  have h := rootPowerSum_sub_of_reverse_coeff_eq _ g
    (monic_add_monomial_of_lt g hg hj t).1 (Nat.sub_pos_of_lt hj)
    (fun k hk ↦ by simp only [reverse_coeff_add_monomial g hg hj
      (by omega : k ≤ g.natDegree) t, if_neg hk.ne, add_zero])
  simpa only [reverse_coeff_add_monomial g hg hj (Nat.sub_le _ _) t, if_true,
    add_sub_cancel_left] using h

private lemma polynomialRootPhase_add_monomial {F : Type*} [Field F]
    (f g : Polynomial F) (hg : g.Monic) (hf : 0 < f.natDegree)
    (hfg : f.natDegree ≤ g.natDegree) (t : F) :
    polynomialRootPhase f (g + Polynomial.monomial (g.natDegree - f.natDegree) t) -
      polynomialRootPhase f g = -(f.natDegree : F) * f.leadingCoeff * t := by
  have hj : g.natDegree - f.natDegree < g.natDegree := by omega
  have htop := rootPowerSum_add_monomial_top g hg hj t
  simp only [Nat.sub_sub_self hfg] at htop
  simp only [polynomialRootPhase]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [Finset.sum_range_succ, htop, Polynomial.coeff_natDegree,
    Finset.sum_eq_zero (fun k hk ↦ by
      rw [rootPowerSum_add_monomial_of_lt g hg hj (by
        simpa only [Nat.sub_sub_self hfg] using Finset.mem_range.mp hk), sub_self, mul_zero])]
  ring

private def monicCoefficientShift {F : Type*} [Field F] {n j : ℕ}
    (hj : j < n) (t : F) :
    {g : Polynomial F // g.Monic ∧ g.natDegree = n} ≃
      {g : Polynomial F // g.Monic ∧ g.natDegree = n} where
  toFun g := ⟨(g : Polynomial F) + Polynomial.monomial j t, by
    have h := monic_add_monomial_of_lt (g : Polynomial F) g.property.1
      (hj.trans_eq g.property.2.symm) t
    exact ⟨h.1, h.2.trans g.property.2⟩⟩
  invFun g := ⟨(g : Polynomial F) + Polynomial.monomial j (-t), by
    have h := monic_add_monomial_of_lt (g : Polynomial F) g.property.1
      (hj.trans_eq g.property.2.symm) (-t)
    exact ⟨h.1, h.2.trans g.property.2⟩⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp

private instance monicFixedDegreeFintype (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Fintype {g : Polynomial F // g.Monic ∧ g.natDegree = n} :=
  Fintype.ofEquiv (Fin n → F)
    ((Polynomial.monicEquivDegreeLT (R := F) n).trans
      (Polynomial.degreeLTEquiv F n).toEquiv).symm

private lemma sum_monic_rootPhase_eq_zero {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0)
    {n : ℕ} (hn : f.natDegree ≤ n) :
    ∑ g : {g : Polynomial F // g.Monic ∧ g.natDegree = n},
      ψ (polynomialRootPhase f g) = 0 := by
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  have hc : -(f.natDegree : F) * f.leadingCoeff ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hchar)
      (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hf))
  let e := monicCoefficientShift (by omega : n - f.natDegree < n)
    (x / (-(f.natDegree : F) * f.leadingCoeff))
  have hphase (g : {g : Polynomial F // g.Monic ∧ g.natDegree = n}) :
      polynomialRootPhase f (e g) = polynomialRootPhase f g + x := by
    have h := polynomialRootPhase_add_monomial f g g.property.1 hf
      (hn.trans_eq g.property.2.symm) (x / (-(f.natDegree : F) * f.leadingCoeff))
    simpa only [e, monicCoefficientShift, Equiv.coe_fn_mk, g.property.2,
      mul_div_cancel₀ _ hc, sub_eq_iff_eq_add, add_comm] using h
  have hsum := e.sum_comp (fun g ↦ ψ (polynomialRootPhase f g))
  simp only [hphase, AddChar.map_add_eq_mul, ← Finset.sum_mul] at hsum
  by_contra hne
  exact hx ((mul_eq_left₀ hne).mp hsum)

private lemma reverse_X_sub_C {F : Type*} [Field F] (x : F) :
    (Polynomial.X - Polynomial.C x).reverse = 1 - Polynomial.C x * Polynomial.X := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.reverse_add_C]
  simp [Polynomial.reverse, sub_eq_add_neg]

private lemma one_sub_C_mul_X_mul_geometric {F : Type*} [Field F] (x : F) :
    (1 - PowerSeries.C x * PowerSeries.X) * PowerSeries.mk (fun n ↦ x ^ n) = 1 := by
  ext (_ | n) <;> simp [sub_mul, mul_assoc, pow_succ']

private lemma inv_one_sub_C_mul_X {F : Type*} [Field F] (x : F) :
    (1 - PowerSeries.C x * PowerSeries.X)⁻¹ = PowerSeries.mk (fun n ↦ x ^ n) := by
  calc
    _ = (1 - PowerSeries.C x * PowerSeries.X)⁻¹ *
        ((1 - PowerSeries.C x * PowerSeries.X) * PowerSeries.mk (fun n ↦ x ^ n)) := by
      rw [one_sub_C_mul_X_mul_geometric, mul_one]
    _ = _ := by
      rw [← mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), one_mul]

private lemma coeff_logarithmicSeries_one_sub_C_mul_X {F : Type*} [Field F]
    (x : F) (n : ℕ) :
    PowerSeries.coeff n (logarithmicSeries (1 - PowerSeries.C x * PowerSeries.X)) =
      -x ^ (n + 1) := by
  simp [logarithmicSeries, inv_one_sub_C_mul_X, Derivation.leibniz,
    smul_eq_mul, pow_succ', neg_mul]

private lemma rootPowerSum_X_sub_C {F : Type*} [Field F] (x : F) (n : ℕ) :
    rootPowerSum (Polynomial.X - Polynomial.C x) n = x ^ n := by
  cases n with
  | zero => simp [rootPowerSum]
  | succ n => simp [rootPowerSum, reverse_X_sub_C,
      coeff_logarithmicSeries_one_sub_C_mul_X]

private lemma polynomialRootPhase_X_sub_C {F : Type*} [Field F]
    (f : Polynomial F) (x : F) :
    polynomialRootPhase f (Polynomial.X - Polynomial.C x) = f.eval x := by
  simp only [polynomialRootPhase, rootPowerSum_X_sub_C, Polynomial.eval_eq_sum_range]

private def additiveLPolynomial {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (f : Polynomial F) : Polynomial ℂ :=
  ∑ n ∈ Finset.range f.natDegree, Polynomial.monomial n
    (∑ g : {g : Polynomial F // g.Monic ∧ g.natDegree = n},
      ψ (polynomialRootPhase f g))

private lemma coeff_additiveLPolynomial {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0) (n : ℕ) :
    (additiveLPolynomial ψ f).coeff n =
      ∑ g : {g : Polynomial F // g.Monic ∧ g.natDegree = n},
        ψ (polynomialRootPhase f g) := by
  classical
  by_cases hn : n < f.natDegree
  · simp [additiveLPolynomial, Polynomial.coeff_monomial, hn]
  · simp [additiveLPolynomial, Polynomial.coeff_monomial, hn,
      sum_monic_rootPhase_eq_zero ψ hψ f hf hchar (Nat.le_of_not_gt hn)]

private lemma natDegree_additiveLPolynomial_le {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (f : Polynomial F) :
    (additiveLPolynomial ψ f).natDegree ≤ f.natDegree - 1 := by
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun n hn ↦
    (Polynomial.natDegree_monomial_le _).trans
      (Nat.le_pred_of_lt (Finset.mem_range.mp hn)))

private lemma sum_monic_rootPhase_degree_zero {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (f : Polynomial F) :
    ∑ g : {g : Polynomial F // g.Monic ∧ g.natDegree = 0},
      ψ (polynomialRootPhase f g) = 1 := by
  classical
  have hg (g : {g : Polynomial F // g.Monic ∧ g.natDegree = 0}) : (g : Polynomial F) = 1 :=
    g.property.1.natDegree_eq_zero.mp g.property.2
  letI : Unique {g : Polynomial F // g.Monic ∧ g.natDegree = 0} :=
    ⟨⟨⟨1, by simp⟩⟩, fun g ↦ Subtype.ext (hg g)⟩
  have hroot (n : ℕ) : rootPowerSum (1 : Polynomial F) n = 0 := by
    cases n <;> simp [rootPowerSum, logarithmicSeries, Polynomial.reverse]
  simp [hg, polynomialRootPhase, hroot]

private lemma constantCoeff_additiveLPolynomial {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (f : Polynomial F) (hf : 0 < f.natDegree) :
    (additiveLPolynomial ψ f).coeff 0 = 1 := by
  classical
  simp [additiveLPolynomial, Polynomial.coeff_monomial, hf, sum_monic_rootPhase_degree_zero]

private def fieldEquivMonicLinear (F : Type*) [Field F] :
    F ≃ {g : Polynomial F // g.Monic ∧ g.natDegree = 1} where
  toFun x := ⟨Polynomial.X - Polynomial.C x, Polynomial.monic_X_sub_C x, by simp⟩
  invFun g := -(g : Polynomial F).coeff 0
  left_inv x := by simp
  right_inv g := by
    apply Subtype.ext
    simpa only [Polynomial.C_neg, sub_neg_eq_add] using
      (g.property.1.eq_X_add_C g.property.2).symm

private lemma coeff_one_additiveLPolynomial {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0) :
    (additiveLPolynomial ψ f).coeff 1 = ∑ x : F, ψ (f.eval x) := by
  rw [coeff_additiveLPolynomial ψ hψ f hf hchar]
  exact (Fintype.sum_equiv (fieldEquivMonicLinear F) _ _ (fun x ↦
    congrArg ψ (polynomialRootPhase_X_sub_C f x).symm)).symm

private lemma natDegree_reverse_of_coeff_zero_ne_zero {F : Type*} [Field F]
    (g : Polynomial F) (hg : g.coeff 0 ≠ 0) :
    g.reverse.natDegree = g.natDegree := by
  rw [Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hg), Nat.sub_zero]

private lemma reverse_reverse_of_coeff_zero_ne_zero {F : Type*} [Field F]
    (g : Polynomial F) (hg : g.coeff 0 ≠ 0) : g.reverse.reverse = g := by
  rw [Polynomial.reverse, natDegree_reverse_of_coeff_zero_ne_zero g hg,
    Polynomial.reverse, Polynomial.reflect_reflect]

private lemma reverse_prod_X_sub_C {F ι : Type*} [Field F]
    (s : Finset ι) (w : ι → F) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (w i))).reverse =
      ∏ i ∈ s, (1 - Polynomial.C (w i) * Polynomial.X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reverse]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Polynomial.reverse_mul_of_domain, reverse_X_sub_C, ih]

private lemma exists_prod_one_sub_C_mul_X (g : Polynomial ℂ) (hg : g.coeff 0 = 1) :
    ∃ (N : ℕ) (w : Fin N → ℂ), N = g.natDegree ∧
      g = ∏ i, (1 - Polynomial.C (w i) * Polynomial.X) := by
  have hg₀ : g.coeff 0 ≠ 0 := hg.trans_ne one_ne_zero
  have hmonic : g.reverse.Monic := by
    simpa only [Polynomial.Monic, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero hg₀] using hg
  let roots := g.reverse.roots.toList
  refine ⟨roots.length, fun i ↦ roots[i.val], ?_, ?_⟩
  · simpa only [roots, Multiset.length_toList,
      natDegree_reverse_of_coeff_zero_ne_zero g hg₀] using
      (IsAlgClosed.splits g.reverse).natDegree_eq_card_roots.symm
  · rw [← reverse_prod_X_sub_C]
    refine (reverse_reverse_of_coeff_zero_ne_zero g hg₀).symm.trans
      (congrArg Polynomial.reverse ?_)
    rw [Fin.prod_univ_fun_getElem roots (fun x ↦ Polynomial.X - Polynomial.C x)]
    simpa only [← Multiset.prod_coe, ← Multiset.map_coe, roots, Multiset.coe_toList] using
      (IsAlgClosed.splits g.reverse).eq_prod_roots_of_monic hmonic

private lemma coeff_logarithmicSeries_prod_linear {F ι : Type*} [Field F]
    (s : Finset ι) (w : ι → F) (n : ℕ) :
    PowerSeries.coeff n (logarithmicSeries
      (∏ i ∈ s, (1 - PowerSeries.C (w i) * PowerSeries.X))) =
        -∑ i ∈ s, w i ^ (n + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logarithmicSeries]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, logarithmicSeries_mul _ _ (by simp) (by simp)]
    simp only [map_add, coeff_logarithmicSeries_one_sub_C_mul_X, ih, Finset.sum_insert hi,
      neg_add_rev, add_comm]

private lemma coeff_zero_logarithmicSeries {F : Type*} [Field F]
    (g : PowerSeries F) (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.coeff 0 (logarithmicSeries g) = PowerSeries.coeff 1 g := by
  simp [logarithmicSeries, PowerSeries.coeff_mul, PowerSeries.coeff_derivative,
    PowerSeries.coeff_zero_eq_constantCoeff, hg]

private lemma coeff_logarithmicSeries_of_factorization {N : ℕ}
    (g : Polynomial ℂ) (w : Fin N → ℂ)
    (hw : g = ∏ i, (1 - Polynomial.C (w i) * Polynomial.X)) (n : ℕ) :
    PowerSeries.coeff n (logarithmicSeries (g : PowerSeries ℂ)) =
      -∑ i, w i ^ (n + 1) := by
  rw [hw, show ((∏ i, (1 - Polynomial.C (w i) * Polynomial.X) : Polynomial ℂ) :
      PowerSeries ℂ) =
    ∏ i, ((1 - Polynomial.C (w i) * Polynomial.X : Polynomial ℂ) : PowerSeries ℂ) from
      map_prod Polynomial.coeToPowerSeries.ringHom
        (fun i : Fin N ↦ 1 - Polynomial.C (w i) * Polynomial.X) Finset.univ]
  simpa only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X] using
    coeff_logarithmicSeries_prod_linear Finset.univ w n

private lemma exists_additiveLPolynomial_power_sums {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0) :
    ∃ (N : ℕ) (w : Fin N → ℂ), N ≤ f.natDegree - 1 ∧
      (∑ x : F, ψ (f.eval x)) = -∑ i, w i ∧
      ∀ n : ℕ, PowerSeries.coeff n
        (logarithmicSeries (additiveLPolynomial ψ f : PowerSeries ℂ)) =
          -∑ i, w i ^ (n + 1) := by
  obtain ⟨N, w, hN, hw⟩ := exists_prod_one_sub_C_mul_X (additiveLPolynomial ψ f)
    (constantCoeff_additiveLPolynomial ψ f hf)
  have hlog := coeff_logarithmicSeries_of_factorization (additiveLPolynomial ψ f) w hw
  refine ⟨N, w, hN.trans_le (natDegree_additiveLPolynomial_le ψ f), ?_, hlog⟩
  simpa only [coeff_zero_logarithmicSeries (additiveLPolynomial ψ f : PowerSeries ℂ)
    (by simpa only [Polynomial.constantCoeff_coe] using
      constantCoeff_additiveLPolynomial ψ f hf),
    Polynomial.coeff_coe, coeff_one_additiveLPolynomial ψ hψ f hf hchar,
    zero_add, pow_one] using hlog 0

private lemma powerSeries_map_inv {F E : Type*} [Field F] [Field E]
    (φ : F →+* E) (g : PowerSeries F) (hg : PowerSeries.constantCoeff g ≠ 0) :
    PowerSeries.map φ g⁻¹ = (PowerSeries.map φ g)⁻¹ := by
  have h := congrArg (PowerSeries.map φ) (PowerSeries.mul_inv_cancel g hg)
  exact inv_unique (by simpa only [map_mul, map_one] using h)
    (PowerSeries.mul_inv_cancel _ (by
      simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
        map_zero] using φ.injective.ne hg))

private lemma powerSeries_map_derivative {F E : Type*} [Field F] [Field E]
    (φ : F →+* E) (g : PowerSeries F) :
    PowerSeries.map φ (PowerSeries.derivative F g) =
      PowerSeries.derivative E (PowerSeries.map φ g) := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_derivative]

private lemma powerSeries_map_logarithmicSeries {F E : Type*} [Field F] [Field E]
    (φ : F →+* E) (g : PowerSeries F) (hg : PowerSeries.constantCoeff g ≠ 0) :
    PowerSeries.map φ (logarithmicSeries g) =
      logarithmicSeries (PowerSeries.map φ g) := by
  simp only [logarithmicSeries, map_mul, powerSeries_map_derivative,
    powerSeries_map_inv φ g hg]

private lemma polynomial_map_reverse {F E : Type*} [Field F] [Field E]
    (φ : F →+* E) (g : Polynomial F) :
    g.reverse.map φ = (g.map φ).reverse := by
  ext n
  simp only [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.natDegree_map]

private lemma rootPowerSum_map {F E : Type*} [Field F] [Field E]
    (φ : F →+* E) (g : Polynomial F) (hg : g.Monic) (n : ℕ) :
    rootPowerSum (g.map φ) n = φ (rootPowerSum g n) := by
  cases n with
  | zero => simp [rootPowerSum]
  | succ n =>
    simp only [rootPowerSum, ← polynomial_map_reverse, Polynomial.polynomial_map_coe,
      ← powerSeries_map_logarithmicSeries φ (g.reverse : PowerSeries F)
        (by simpa using hg.ne_zero),
      PowerSeries.coeff_map, map_neg]

private lemma polynomialRootPhase_map {F E : Type*} [Field F] [Field E]
    (φ : F →+* E) (f g : Polynomial F) (hg : g.Monic) :
    polynomialRootPhase (f.map φ) (g.map φ) = φ (polynomialRootPhase f g) := by
  simp only [polynomialRootPhase, Polynomial.natDegree_map, Polynomial.coeff_map,
    rootPowerSum_map φ g hg, map_sum, map_mul]

private lemma polynomialRootPhase_one {F : Type*} [Field F] (f : Polynomial F) :
    polynomialRootPhase f 1 = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  cases n <;> simp [rootPowerSum, logarithmicSeries, Polynomial.reverse]

private lemma polynomialRootPhase_prod_X_sub_C {F : Type*} [Field F]
    (f : Polynomial F) (s : Multiset F) :
    polynomialRootPhase f (s.map (fun x ↦ Polynomial.X - Polynomial.C x)).prod =
      (s.map f.eval).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [polynomialRootPhase_one]
  | @cons x s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons,
      polynomialRootPhase_mul _ _ _ (Polynomial.monic_X_sub_C x)
        (Polynomial.monic_multisetProd_X_sub_C s)]
    simp only [polynomialRootPhase_X_sub_C, ih, Multiset.map_cons, Multiset.sum_cons]

private lemma polynomialRootPhase_eq_sum_roots {F : Type*} [Field F]
    (f g : Polynomial F) (hg : g.Monic) (hsplit : g.Splits) :
    polynomialRootPhase f g = (g.roots.map f.eval).sum := by
  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hg]
  exact polynomialRootPhase_prod_X_sub_C f g.roots

private lemma polynomialRootPhase_minpoly_powerBasis {F E : Type*} [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (pb : PowerBasis F E) (f : Polynomial F) :
    polynomialRootPhase f (minpoly F pb.gen) =
      Algebra.trace F E (Polynomial.aeval pb.gen f) := by
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [← polynomialRootPhase_map _ _ _ (minpoly.monic pb.isIntegral_gen),
    polynomialRootPhase_eq_sum_roots _ _ ((minpoly.monic pb.isIntegral_gen).map _)
      (IsAlgClosed.splits _), trace_eq_sum_embeddings (AlgebraicClosure F)]
  classical
  rw [Fintype.sum_equiv pb.liftEquiv' _ (fun x ↦ Polynomial.aeval (x : AlgebraicClosure F) f)
    (fun σ ↦ by simp only [PowerBasis.liftEquiv'_apply_coe, Polynomial.aeval_algHom_apply])]
  rw [Finset.sum_mem_multiset _ _ (fun x ↦ Polynomial.aeval x f) (fun _ ↦ rfl),
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots
      ((Polynomial.separable_map _).mpr (Algebra.IsSeparable.isSeparable F pb.gen)))]
  simp only [Polynomial.eval_map, Polynomial.aeval_def]

private lemma trace_aeval_eq_nsmul_rootPhase {F E : Type*} [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (x : E) (f : Polynomial F) :
    Algebra.trace F E (Polynomial.aeval x f) =
      Module.finrank (IntermediateField.adjoin F {x}) E •
        polynomialRootPhase f (minpoly F x) := by
  let K := IntermediateField.adjoin F {x}
  letI : FiniteDimensional K E := FiniteDimensional.right F K E
  letI : Algebra.IsSeparable F K := Algebra.isSeparable_tower_bot_of_isSeparable F K E
  have hphase := polynomialRootPhase_minpoly_powerBasis
    (IntermediateField.adjoin.powerBasis (Algebra.IsSeparable.isIntegral F x)) f
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at hphase
  rw [← Algebra.trace_trace (R := F) (S := K), show x =
    algebraMap K E (IntermediateField.AdjoinSimple.gen F x) from rfl,
    Polynomial.aeval_algebraMap_apply, Algebra.trace_algebraMap, map_nsmul, ← hphase]
  rfl

private lemma addChar_trace_aeval_eq_rootPhase_pow {F E : Type*} [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (ψ : AddChar F ℂ) (x : E) (f : Polynomial F) :
    ψ (Algebra.trace F E (Polynomial.aeval x f)) =
      ψ (polynomialRootPhase f (minpoly F x)) ^
        (Module.finrank F E / (minpoly F x).natDegree) := by
  rw [trace_aeval_eq_nsmul_rootPhase, AddChar.map_nsmul_eq_pow,
    ← IntermediateField.adjoin.finrank (IsIntegral.of_finite F x),
    ← Module.finrank_mul_finrank F (IntermediateField.adjoin F {x}) E,
    Nat.mul_div_cancel_left _ (Module.finrank_pos (R := F)
      (M := IntermediateField.adjoin F {x}))]

private lemma minpoly_eq_iff_aeval_eq_zero {F E : Type*} [Field F] [Field E]
    [Algebra F E] (g : Polynomial F) (hg : g.Monic) (hi : Irreducible g) (x : E) :
    minpoly F x = g ↔ Polynomial.aeval x g = 0 := by
  exact ⟨fun h ↦ h ▸ minpoly.aeval F x,
    fun h ↦ (minpoly.eq_of_irreducible_of_monic hi h hg).symm⟩

private lemma card_minpoly_fiber {F E : Type*} [Field F] [Field E] [Algebra F E]
    (g : Polynomial F) (hg : g.Monic) (hi : Irreducible g) (hsep : g.Separable)
    (hsplit : (g.map (algebraMap F E)).Splits) :
    Nat.card {x : E // minpoly F x = g} = g.natDegree := by
  have heq (x : E) : minpoly F x = g ↔ x ∈ g.rootSet E :=
    (minpoly_eq_iff_aeval_eq_zero g hg hi x).trans
      (Polynomial.mem_rootSet_of_ne hg.ne_zero).symm
  exact (Nat.card_congr (Equiv.subtypeEquivRight heq)).trans
    (by simpa only [Nat.card_eq_fintype_card] using
      Polynomial.card_rootSet_eq_natDegree hsep hsplit)

open scoped Classical in
private lemma sum_addChar_trace_eq_sum_minpoly {F E : Type*} [Field F] [Field E]
    [Fintype E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (ψ : AddChar F ℂ) (f : Polynomial F) :
    (∑ x : E, ψ (Algebra.trace F E (Polynomial.aeval x f))) =
      ∑ g ∈ Finset.univ.image (minpoly F : E → Polynomial F),
        (g.natDegree : ℂ) * ψ (polynomialRootPhase f g) ^
          (Module.finrank F E / g.natDegree) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := (minpoly F : E → Polynomial F))
    (fun x (_ : x ∈ Finset.univ) ↦ Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
      (fun x : E ↦ ψ (Algebra.trace F E (Polynomial.aeval x f)))]
  refine Finset.sum_congr rfl fun g hg ↦ ?_
  rw [Finset.sum_congr rfl (fun x hx ↦ by
    rw [addChar_trace_aeval_eq_rootPhase_pow, (Finset.mem_filter.mp hx).2])]
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hg
  have hcard := card_minpoly_fiber (minpoly F x) (minpoly.monic (IsIntegral.of_finite F x))
    (minpoly.irreducible (IsIntegral.of_finite F x)) (Algebra.IsSeparable.isSeparable F x)
    (Normal.splits (inferInstance : Normal F E) x)
  simp only [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card, hcard]

private lemma exists_minpoly_eq_of_natDegree_dvd {F E : Type*} [Field F] [Field E]
    [Finite E] [Algebra F E] (g : Polynomial F) (hg : g.Monic) (hi : Irreducible g)
    (hd : g.natDegree ∣ Module.finrank F E) :
    ∃ x : E, minpoly F x = g := by
  letI : Fact (Irreducible g) := ⟨hi⟩
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := F) (K := AdjoinRoot g) (L := E) (by
      rwa [(AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim])
  exact ⟨φ (AdjoinRoot.root g), by
    simp only [minpoly.algHom_eq φ φ.injective, AdjoinRoot.minpoly_root hg.ne_zero,
      hg.leadingCoeff, inv_one, Polynomial.C_1, mul_one]⟩

open scoped Classical in
private lemma mem_image_minpoly_iff {F E : Type*} [Field F] [Field E]
    [Fintype E] [Algebra F E] (g : Polynomial F) :
    g ∈ Finset.univ.image (minpoly F : E → Polynomial F) ↔
      g.Monic ∧ Irreducible g ∧ g.natDegree ∣ Module.finrank F E := by
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨minpoly.monic (IsIntegral.of_finite F x),
      minpoly.irreducible (IsIntegral.of_finite F x),
      minpoly.degree_dvd (IsIntegral.of_finite F x)⟩
  · rintro ⟨hg, hi, hd⟩
    obtain ⟨x, hx⟩ := exists_minpoly_eq_of_natDegree_dvd (E := E) g hg hi hd
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩

private def monicIrreduciblesUpTo (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Finset (Polynomial F) := by
  classical
  exact ((Finset.range (n + 1)).biUnion fun k ↦
    (Finset.univ : Finset {g : Polynomial F // g.Monic ∧ g.natDegree = k}).image
      Subtype.val).filter Irreducible

private lemma mem_monicIrreduciblesUpTo {F : Type*} [Field F] [Fintype F]
    (n : ℕ) (g : Polynomial F) :
    g ∈ monicIrreduciblesUpTo F n ↔ g.Monic ∧ Irreducible g ∧ g.natDegree ≤ n := by
  classical
  simp only [monicIrreduciblesUpTo, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, exists_prop]
  aesop

open scoped Classical in
private lemma image_minpoly_eq_monicIrreducibles {F E : Type*} [Field F] [Field E]
    [Fintype F] [Fintype E] [Algebra F E] :
    Finset.univ.image (minpoly F : E → Polynomial F) =
      (monicIrreduciblesUpTo F (Module.finrank F E)).filter
        (fun g ↦ g.natDegree ∣ Module.finrank F E) := by
  ext g
  simp only [mem_image_minpoly_iff, Finset.mem_filter, mem_monicIrreduciblesUpTo]
  exact ⟨fun h ↦ ⟨⟨h.1, h.2.1, Nat.le_of_dvd Module.finrank_pos h.2.2⟩, h.2.2⟩,
    fun h ↦ ⟨h.1.1, h.1.2.1, h.2⟩⟩

open scoped Classical in
private lemma sum_addChar_trace_eq_sum_irreducibles {F E : Type*} [Field F] [Field E]
    [Fintype F] [Fintype E] [Algebra F E] (ψ : AddChar F ℂ) (f : Polynomial F) :
    (∑ x : E, ψ (Algebra.trace F E (Polynomial.aeval x f))) =
      ∑ g ∈ monicIrreduciblesUpTo F (Module.finrank F E) with
        g.natDegree ∣ Module.finrank F E,
        (g.natDegree : ℂ) * ψ (polynomialRootPhase f g) ^
          (Module.finrank F E / g.natDegree) := by
  rw [sum_addChar_trace_eq_sum_minpoly, image_minpoly_eq_monicIrreducibles]

private def monicMulEmbedding {F : Type*} [Field F] (p : Polynomial F) (hp : p.Monic)
    (n : ℕ) :
    {g : Polynomial F // g.Monic ∧ g.natDegree = n} ↪
      {g : Polynomial F // g.Monic ∧ g.natDegree = p.natDegree + n} where
  toFun g := ⟨p * g, hp.mul g.property.1, by
    rw [Polynomial.natDegree_mul hp.ne_zero g.property.1.ne_zero, g.property.2]⟩
  inj' := by
    intro g h heq
    exact Subtype.ext (mul_left_cancel₀ hp.ne_zero (congrArg Subtype.val heq))

open scoped Classical in
private lemma image_monicMulEmbedding {F : Type*} [Field F] [Fintype F]
    (p : Polynomial F) (hp : p.Monic) (n : ℕ) :
    Finset.univ.image (monicMulEmbedding p hp n) =
      (Finset.univ : Finset {g : Polynomial F //
        g.Monic ∧ g.natDegree = p.natDegree + n}).filter (fun g ↦ p ∣ g.val) := by
  ext g
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact dvd_mul_right p a.val
  · rintro ⟨h, hh⟩
    have hmonic : h.Monic := hp.of_mul_monic_left (hh ▸ g.property.1)
    have hdeg : h.natDegree = n := Nat.add_left_cancel (show p.natDegree + h.natDegree =
        p.natDegree + n by
      rw [← Polynomial.natDegree_mul hp.ne_zero hmonic.ne_zero, ← hh, g.property.2])
    exact ⟨⟨h, hmonic, hdeg⟩, Subtype.ext hh.symm⟩

open scoped Classical in
private lemma sum_monic_multiples {F : Type*} [Field F] [Fintype F]
    (p : Polynomial F) (hp : p.Monic) (n : ℕ) (w : Polynomial F → ℂ) :
    (∑ g : {g : Polynomial F // g.Monic ∧ g.natDegree = p.natDegree + n},
      if p ∣ g.val then w g.val else 0) =
        ∑ h : {h : Polynomial F // h.Monic ∧ h.natDegree = n}, w (p * h.val) := by
  rw [← Finset.sum_filter, ← image_monicMulEmbedding p hp n, Finset.sum_image
    (fun _ _ _ _ h ↦ (monicMulEmbedding p hp n).injective h)]
  rfl

private def sievedMonicWeight {F : Type*} [Field F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) (g : Polynomial F) : ℂ := by
  classical
  exact if ∀ p ∈ s, ¬p ∣ g then w g else 0

private def sievedMonicSeries {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦
    ∑ g : {g : Polynomial F // g.Monic ∧ g.natDegree = n}, sievedMonicWeight w s g

private lemma sievedMonicWeight_mul {F : Type*} [Field F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) (p g : Polynomial F)
    (hw : w (p * g) = w p * w g) (hs : ∀ q ∈ s, Prime q ∧ ¬q ∣ p) :
    sievedMonicWeight w s (p * g) = w p * sievedMonicWeight w s g := by
  have heq : (∀ q ∈ s, ¬q ∣ p * g) ↔ ∀ q ∈ s, ¬q ∣ g :=
    forall_congr' fun q ↦ forall_congr' fun hq ↦ by
      rw [(hs q hq).1.dvd_mul, or_iff_right (hs q hq).2]
  by_cases h : ∀ q ∈ s, ¬q ∣ g
  · simp only [sievedMonicWeight, if_pos h, if_pos (heq.mpr h), hw]
  · simp only [sievedMonicWeight, if_neg h, if_neg (mt heq.mp h), mul_zero]

open scoped Classical in
private lemma sievedMonicWeight_insert {F : Type*} [Field F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) (p g : Polynomial F) :
    sievedMonicWeight w (insert p s) g =
      sievedMonicWeight w s g - if p ∣ g then sievedMonicWeight w s g else 0 := by
  by_cases h : p ∣ g <;> simp [sievedMonicWeight, h]

open scoped Classical in
private lemma coeff_sievedMonicSeries_insert_add {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) (p : Polynomial F) (hp : p.Monic)
    (hw : ∀ g : Polynomial F, g.Monic → w (p * g) = w p * w g)
    (hs : ∀ q ∈ s, Prime q ∧ ¬q ∣ p) (n : ℕ) :
    PowerSeries.coeff (p.natDegree + n) (sievedMonicSeries w (insert p s)) =
      PowerSeries.coeff (p.natDegree + n) (sievedMonicSeries w s) -
        w p * PowerSeries.coeff n (sievedMonicSeries w s) := by
  simp only [sievedMonicSeries, PowerSeries.coeff_mk, sievedMonicWeight_insert,
    Finset.sum_sub_distrib, sum_monic_multiples p hp n]
  exact congrArg (_ - ·) (by
    simpa only [Finset.mul_sum] using Finset.sum_congr rfl
      (fun (g : {g : Polynomial F // g.Monic ∧ g.natDegree = n}) _ ↦
        sievedMonicWeight_mul w s p g.val (hw g.val g.property.1) hs))

open scoped Classical in
private lemma coeff_sievedMonicSeries_insert_of_lt {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) (p : Polynomial F)
    {n : ℕ} (hn : n < p.natDegree) :
    PowerSeries.coeff n (sievedMonicSeries w (insert p s)) =
      PowerSeries.coeff n (sievedMonicSeries w s) := by
  have hdiv (g : {g : Polynomial F // g.Monic ∧ g.natDegree = n}) : ¬p ∣ g.val :=
    fun h ↦ (not_le_of_gt hn) (g.property.2 ▸
      Polynomial.natDegree_le_of_dvd h g.property.1.ne_zero)
  simp only [sievedMonicSeries, PowerSeries.coeff_mk, sievedMonicWeight_insert,
    if_neg (hdiv _), sub_zero]

open scoped Classical in
private lemma sievedMonicSeries_insert {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) (p : Polynomial F) (hp : p.Monic)
    (hw : ∀ g : Polynomial F, g.Monic → w (p * g) = w p * w g)
    (hs : ∀ q ∈ s, Prime q ∧ ¬q ∣ p) :
    sievedMonicSeries w (insert p s) = sievedMonicSeries w s *
      (1 - PowerSeries.C (w p) * PowerSeries.X ^ p.natDegree) := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, PowerSeries.coeff_mul_X_pow']
  by_cases hn : p.natDegree ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa only [if_pos hn, Nat.add_sub_cancel_left, PowerSeries.coeff_mul_C, mul_comm]
      using coeff_sievedMonicSeries_insert_add w s p hp hw hs k
  · rw [if_neg hn, sub_zero, coeff_sievedMonicSeries_insert_of_lt w s p (lt_of_not_ge hn)]

private lemma sievedMonicSeries_eq_mul_prod {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ)
    (hw : ∀ p g : Polynomial F, p.Monic → g.Monic → w (p * g) = w p * w g)
    (s : Finset (Polynomial F)) (hs : ∀ p ∈ s, p.Monic ∧ Irreducible p) :
    sievedMonicSeries w s = sievedMonicSeries w ∅ *
      ∏ p ∈ s, (1 - PowerSeries.C (w p) * PowerSeries.X ^ p.natDegree) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hp' := hs p (Finset.mem_insert_self p s)
    have hs' (q : Polynomial F) (hq : q ∈ s) := hs q (Finset.mem_insert_of_mem hq)
    have hsp (q : Polynomial F) (hq : q ∈ s) : Prime q ∧ ¬q ∣ p :=
      ⟨irreducible_iff_prime.mp (hs' q hq).2, fun hd ↦ hp
        ((Polynomial.eq_of_monic_of_associated (hs' q hq).1 hp'.1
          (((hs' q hq).2.dvd_irreducible_iff_associated hp'.2).mp hd)) ▸ hq)⟩
    rw [sievedMonicSeries_insert w s p hp'.1 (fun g hg ↦ hw p g hp'.1 hg) hsp,
      ih hs', Finset.prod_insert hp, mul_assoc, mul_comm (1 - _)]

private lemma sievedMonicWeight_eq_zero_of_degree_le {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ) (n : ℕ) (g : Polynomial F) (hg : g.Monic)
    (hpos : 0 < g.natDegree) (hdeg : g.natDegree ≤ n) :
    sievedMonicWeight w (monicIrreduciblesUpTo F n) g = 0 := by
  obtain ⟨p, hp, hi, hd⟩ := Polynomial.exists_monic_irreducible_factor g
    (fun h ↦ hpos.ne' (Polynomial.natDegree_eq_zero_of_isUnit h))
  exact if_neg (fun h ↦ h p ((mem_monicIrreduciblesUpTo n p).mpr
    ⟨hp, hi, (Polynomial.natDegree_le_of_dvd hd hg.ne_zero).trans hdeg⟩) hd)

private lemma coeff_sievedMonicSeries_eq_zero_of_le {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ) {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    PowerSeries.coeff k (sievedMonicSeries w (monicIrreduciblesUpTo F n)) = 0 := by
  simp only [sievedMonicSeries, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun g _ ↦ sievedMonicWeight_eq_zero_of_degree_le w n g
    g.property.1 (g.property.2.symm ▸ hk) (g.property.2.symm ▸ hkn)

private lemma coeff_logarithmicSeries_sieved_eq_zero {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ) {n k : ℕ} (hkn : k < n) :
    PowerSeries.coeff k
      (logarithmicSeries (sievedMonicSeries w (monicIrreduciblesUpTo F n))) = 0 := by
  rw [logarithmicSeries, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  have hij' := Finset.mem_antidiagonal.mp hij
  simp only [PowerSeries.coeff_derivative,
    coeff_sievedMonicSeries_eq_zero_of_le w (Nat.succ_pos i) (by omega : i + 1 ≤ n),
    zero_mul]

private lemma logarithmicSeries_prod {F ι : Type*} [Field F] (s : Finset ι)
    (g : ι → PowerSeries F) (hg : ∀ i ∈ s, PowerSeries.constantCoeff (g i) ≠ 0) :
    logarithmicSeries (∏ i ∈ s, g i) = ∑ i ∈ s, logarithmicSeries (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logarithmicSeries]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, logarithmicSeries_mul _ _ (hg a (Finset.mem_insert_self a s))
      (by
        simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr
          (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

private lemma sievedMonicSeries_empty_eq_additiveLPolynomial {F : Type*}
    [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0) :
    sievedMonicSeries (fun g ↦ ψ (polynomialRootPhase f g)) ∅ =
      (additiveLPolynomial ψ f : PowerSeries ℂ) := by
  ext n
  simp [sievedMonicSeries, sievedMonicWeight, coeff_additiveLPolynomial ψ hψ f hf hchar]

private lemma coeff_additiveLPolynomial_logarithmicSeries_eq_sum_factors {F : Type*}
    [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (logarithmicSeries (additiveLPolynomial ψ f : PowerSeries ℂ)) =
      -∑ p ∈ monicIrreduciblesUpTo F (n + 1), PowerSeries.coeff n
        (logarithmicSeries (1 - PowerSeries.C (ψ (polynomialRootPhase f p)) *
          PowerSeries.X ^ p.natDegree)) := by
  let w := fun p ↦ ψ (polynomialRootPhase f p)
  have hs (p : Polynomial F) (hp : p ∈ monicIrreduciblesUpTo F (n + 1)) :
      p.Monic ∧ Irreducible p :=
    ⟨((mem_monicIrreduciblesUpTo _ p).mp hp).1,
      ((mem_monicIrreduciblesUpTo _ p).mp hp).2.1⟩
  have hc (p : Polynomial F) (hp : p ∈ monicIrreduciblesUpTo F (n + 1)) :
      PowerSeries.constantCoeff (1 - PowerSeries.C (w p) * PowerSeries.X ^ p.natDegree) ≠ 0 := by
    simp [ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible (hs p hp).2))]
  have hmul := sievedMonicSeries_eq_mul_prod w
    (fun p g hp hg ↦ by
      simp only [w, polynomialRootPhase_mul f p g hp hg, AddChar.map_add_eq_mul])
    (monicIrreduciblesUpTo F (n + 1)) hs
  rw [sievedMonicSeries_empty_eq_additiveLPolynomial ψ hψ f hf hchar] at hmul
  have hlog := congrArg logarithmicSeries hmul
  rw [logarithmicSeries_mul _ _ (by
    simpa only [Polynomial.constantCoeff_coe, constantCoeff_additiveLPolynomial ψ f hf]
      using (one_ne_zero : (1 : ℂ) ≠ 0))
    (by simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr hc),
    logarithmicSeries_prod _ _ hc] at hlog
  exact eq_neg_of_add_eq_zero_left (by
    simpa only [map_add, map_sum, coeff_logarithmicSeries_sieved_eq_zero w (Nat.lt_succ_self n)]
      using congrArg (PowerSeries.coeff n) hlog.symm)

private lemma expand_inv {F : Type*} [Field F] (d : ℕ) (hd : d ≠ 0)
    (g : PowerSeries F) (hg : PowerSeries.constantCoeff g ≠ 0) :
    PowerSeries.expand d hd g⁻¹ = (PowerSeries.expand d hd g)⁻¹ := by
  have h := congrArg (PowerSeries.expand d hd) (PowerSeries.mul_inv_cancel g hg)
  exact inv_unique (by simpa only [map_mul, map_one] using h)
    (PowerSeries.mul_inv_cancel _ (by simpa only [PowerSeries.constantCoeff_expand] using hg))

private lemma X_mul_logarithmicSeries_one_sub_C_mul_X_pow {F : Type*} [Field F]
    (c : F) (d : ℕ) (hd : d ≠ 0) :
    PowerSeries.X * logarithmicSeries (1 - PowerSeries.C c * PowerSeries.X ^ d) =
      PowerSeries.C (d : F) * PowerSeries.expand d hd
        (PowerSeries.X * logarithmicSeries (1 - PowerSeries.C c * PowerSeries.X)) := by
  simp only [logarithmicSeries, map_mul,
    expand_inv d hd _ (by simp : PowerSeries.constantCoeff
      (1 - PowerSeries.C c * PowerSeries.X) ≠ 0),
    map_sub, map_one, PowerSeries.expand_C, PowerSeries.expand_X]
  simp only [Derivation.map_one_eq_zero, Derivation.leibniz, PowerSeries.derivative_C,
    PowerSeries.derivative_X, PowerSeries.derivative_pow, smul_eq_mul, mul_zero, add_zero,
    mul_one, zero_sub, map_zero, PowerSeries.expand_C, map_natCast]
  have hx : (PowerSeries.X : PowerSeries F) ^ (d - 1) * PowerSeries.X = PowerSeries.X ^ d := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hd)]
  linear_combination
    -(PowerSeries.C c * d) * (1 - PowerSeries.C c * PowerSeries.X ^ d)⁻¹ * hx

private lemma coeff_X_mul_logarithmicSeries_one_sub_C_mul_X {F : Type*} [Field F]
    (c : F) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.X * logarithmicSeries (1 - PowerSeries.C c * PowerSeries.X)) =
        if n = 0 then 0 else -c ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    simpa only [PowerSeries.coeff_succ_X_mul, Nat.succ_ne_zero, if_false] using
      coeff_logarithmicSeries_one_sub_C_mul_X c n

private lemma coeff_logarithmicSeries_one_sub_C_mul_X_pow {F : Type*} [Field F]
    (c : F) (d : ℕ) (hd : d ≠ 0) (n : ℕ) :
    PowerSeries.coeff n
      (logarithmicSeries (1 - PowerSeries.C c * PowerSeries.X ^ d)) =
        if d ∣ n + 1 then -(d : F) * c ^ ((n + 1) / d) else 0 := by
  have h := congrArg (PowerSeries.coeff (n + 1))
    (X_mul_logarithmicSeries_one_sub_C_mul_X_pow c d hd)
  simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_expand,
    coeff_X_mul_logarithmicSeries_one_sub_C_mul_X] at h
  by_cases hdiv : d ∣ n + 1
  · have hq : (n + 1) / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.succ_pos n) hdiv) (Nat.pos_of_ne_zero hd))
    simpa only [if_pos hdiv, if_neg hq, mul_neg, neg_mul] using h
  · simpa only [if_neg hdiv, mul_zero] using h

open scoped Classical in
private lemma coeff_additiveLPolynomial_logarithmicSeries_eq_sum_irreducibles {F : Type*}
    [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (logarithmicSeries (additiveLPolynomial ψ f : PowerSeries ℂ)) =
      ∑ p ∈ monicIrreduciblesUpTo F (n + 1) with p.natDegree ∣ n + 1,
        (p.natDegree : ℂ) * ψ (polynomialRootPhase f p) ^ ((n + 1) / p.natDegree) := by
  rw [coeff_additiveLPolynomial_logarithmicSeries_eq_sum_factors ψ hψ f hf hchar,
    ← Finset.sum_neg_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hd : p.natDegree ≠ 0 := (Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_irreducible
      ((mem_monicIrreduciblesUpTo _ p).mp hp).2.1)).ne'
  by_cases hdiv : p.natDegree ∣ n + 1 <;>
    simp [coeff_logarithmicSeries_one_sub_C_mul_X_pow _ _ hd, hdiv]

private lemma coeff_additiveLPolynomial_logarithmicSeries_eq_trace_sum {F E : Type*}
    [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0) (n : ℕ)
    (hE : Module.finrank F E = n + 1) :
    PowerSeries.coeff n (logarithmicSeries (additiveLPolynomial ψ f : PowerSeries ℂ)) =
      ∑ x : E, ψ (Algebra.trace F E (Polynomial.aeval x f)) := by
  rw [sum_addChar_trace_eq_sum_irreducibles, hE,
    coeff_additiveLPolynomial_logarithmicSeries_eq_sum_irreducibles ψ hψ f hf hchar]

private lemma norm_coeff_additiveLPolynomial_logarithmicSeries_le {F : Type*}
    [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0)
    (hcop : f.natDegree.Coprime (Fintype.card F)) (n : ℕ) :
    ‖PowerSeries.coeff n (logarithmicSeries (additiveLPolynomial ψ f : PowerSeries ℂ))‖ ≤
      (2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 4) *
        (Real.sqrt (Fintype.card F)) ^ (n + 1) := by
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  let E := FiniteField.Extension F (ringChar F) (n + 1)
  letI : Fintype E := Fintype.ofFinite E
  rw [coeff_additiveLPolynomial_logarithmicSeries_eq_trace_sum (E := E) ψ hψ f hf hchar n
    (FiniteField.finrank_extension F (ringChar F) (n + 1))]
  have h := norm_sum_addChar_trace_le_sqrt_card (f.map (algebraMap F E))
    (by simpa only [Polynomial.natDegree_map] using hf)
    (by simpa only [Polynomial.natDegree_map] using hcop) ψ hψ
  simpa only [Polynomial.natDegree_map, Polynomial.eval_map, ← Polynomial.aeval_def,
    Module.card_eq_pow_finrank (K := F) (V := E),
    show Module.finrank F E = n + 1 from FiniteField.finrank_extension F (ringChar F) (n + 1),
    Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _),
    ← Real.rpow_mul_natCast (Nat.cast_nonneg _), mul_comm] using h

private lemma norm_sum_eval_mul_pow_le {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (P : Polynomial ℂ) {B C : ℝ}
    (h : ∀ n : ℕ, 0 < n → ‖∑ j, w j ^ n‖ ≤ C * B ^ n) {n : ℕ} (hn : 0 < n) :
    ‖∑ j, P.eval (w j) * w j ^ n‖ ≤
      (∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ * C * B ^ k) * B ^ n := by
  have heq : ∑ j, P.eval (w j) * w j ^ n =
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * ∑ j, w j ^ (k + n) := by
    simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, mul_assoc, ← pow_add]
    simpa only [Finset.mul_sum] using Finset.sum_comm
      (s := Finset.univ) (t := Finset.range (P.natDegree + 1))
      (f := fun j k ↦ P.coeff k * w j ^ (k + n))
  rw [heq, Finset.sum_mul]
  refine norm_sum_le_of_le _ (fun k _ ↦ ?_)
  simpa only [norm_mul, pow_add, mul_assoc] using
    mul_le_mul_of_nonneg_left (h (k + n) (by omega)) (norm_nonneg (P.coeff k))

private lemma norm_le_of_power_sum_bound {ι : Type*} [Fintype ι] (w : ι → ℂ)
    {B C : ℝ} (hB : 0 < B)
    (h : ∀ n : ℕ, 0 < n → ‖∑ j, w j ^ n‖ ≤ C * B ^ n) (i : ι) :
    ‖w i‖ ≤ B := by
  classical
  obtain ⟨P, hP⟩ := (Polynomial.exists_eval_eq_iff w
    (fun j ↦ if w j = w i then (1 : ℂ) else 0)).2 (fun j k hjk ↦ by rw [hjk])
  let s := Finset.univ.filter (fun j ↦ w j = w i)
  have hs : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (show s.Nonempty from ⟨i, by simp [s]⟩)
  have hsum (n : ℕ) : ∑ j, P.eval (w j) * w j ^ n = (s.card : ℂ) * w i ^ n := by
    simp [hP, s, ite_mul, ← Finset.sum_filter, Finset.sum_congr rfl
      (fun j (hj : j ∈ s) ↦ congrArg (· ^ n) (Finset.mem_filter.mp hj).2)]
  let D := ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ * C * B ^ k
  by_contra! hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max (D / s.card) 1)
    ((one_lt_div hB).mpr hlt)
  have hn₀ : 0 < n := Nat.pos_of_ne_zero (fun hn₀ ↦ by simp [hn₀] at hn)
  have hb' : (s.card : ℝ) * ‖w i‖ ^ n ≤ D * B ^ n := by
    simpa only [hsum, norm_mul, Complex.norm_natCast, norm_pow] using
      norm_sum_eval_mul_pow_le w P h hn₀
  have hr : ‖w i‖ ^ n / B ^ n ≤ D / s.card :=
    (div_le_div_iff₀ (pow_pos hB n) hs).mpr (by simpa only [mul_comm] using hb')
  exact (not_lt_of_ge hr)
    (by simpa only [div_pow] using (le_max_left (D / s.card) 1).trans_lt hn)

private lemma norm_sum_addChar_le_degree_sub_one_mul_sqrt {F : Type*}
    [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : Polynomial F)
    (hf : 0 < f.natDegree) (hchar : (f.natDegree : F) ≠ 0)
    (hcop : f.natDegree.Coprime (Fintype.card F)) :
    ‖∑ x : F, ψ (f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
  obtain ⟨N, w, hN, hsum, hlog⟩ := exists_additiveLPolynomial_power_sums ψ hψ f hf hchar
  have hw (i : Fin N) : ‖w i‖ ≤ Real.sqrt (Fintype.card F) := by
    refine norm_le_of_power_sum_bound w (by positivity) (C :=
      2 * (f.natDegree : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 4) ?_ i
    intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    simpa only [hlog, norm_neg] using
      norm_coeff_additiveLPolynomial_logarithmicSeries_le ψ hψ f hf hchar hcop n
  rw [hsum, norm_neg]
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ ↦ hw i))).trans (by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hN) (Real.sqrt_nonneg (Fintype.card F)))

private lemma addChar_comp_trace_ne_one {F E : Type*} [Field F] [Field E]
    [Finite F] [Finite E] [Algebra F E] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom ≠ 1 := by
  apply fun h ↦ hψ (AddChar.compAddMonoidHom_injective_left
    (Algebra.trace F E).toAddMonoidHom (Algebra.trace_surjective F E) ?_)
  exact h.trans (by ext x; rfl)

private lemma natCast_ne_zero_of_coprime_card {F : Type*} [Field F] [Fintype F]
    {n : ℕ} (h : n.Coprime (Fintype.card F)) : (n : F) ≠ 0 := by
  exact (isCoprime_zero_right.mp
    (by simpa only [FiniteField.cast_card_eq_zero] using (h.cast : IsCoprime (n : F) _))).ne_zero

private lemma norm_sum_addChar_trace_le_degree_sub_one_mul_sqrt {F E : Type*}
    [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E]
    (f : Polynomial E) (hf : 0 < f.natDegree)
    (hcop : f.natDegree.Coprime (Fintype.card F)) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖∑ x : E, ψ (Algebra.trace F E (f.eval x))‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card E) := by
  have hcopE : f.natDegree.Coprime (Fintype.card E) := by
    exact (Module.card_eq_pow_finrank (K := F) (V := E)).symm ▸
      hcop.pow_right (Module.finrank F E)
  exact norm_sum_addChar_le_degree_sub_one_mul_sqrt
    (ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom)
    (addChar_comp_trace_ne_one ψ hψ) f hf (natCast_ne_zero_of_coprime_card hcopE) hcopE

private def linearPhaseIndices (p r q : ℕ) : Set (Fin q → ZMod p) :=
  {a | ∀ j, r ≤ j.val → a j = 0}

private lemma powerPhasePolynomial_natDegree_le_one {p r q : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r)
    {a : Fin q → ZMod p} (ha : a ∈ linearPhaseIndices p r q) :
    (powerPhasePolynomial b hr a).natDegree ≤ 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
  by_cases hj : j.val < r
  · simpa only [Nat.div_eq_of_lt hj, zero_add] using
      Polynomial.natDegree_monomial_le (a j • b.traceDual ⟨j.val % r, Nat.mod_lt _ hr⟩)
  · simp [ha j (Nat.le_of_not_gt hj)]

private lemma two_le_powerPhasePolynomial_natDegree {p r q : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r)
    {a : Fin q → ZMod p} (ha : a ∉ linearPhaseIndices p r q) :
    2 ≤ (powerPhasePolynomial b hr a).natDegree := by
  obtain ⟨j, hj, haj⟩ : ∃ j : Fin q, r ≤ j.val ∧ a j ≠ 0 := by
    simpa only [linearPhaseIndices, Set.mem_setOf_eq, not_forall, exists_prop] using ha
  have hc : (powerPhasePolynomial b hr a).coeff (j.val / r + 1) ≠ 0 := fun hc ↦
    haj (by simpa only [hc, map_zero, Finsupp.zero_apply] using
      (powerPhasePolynomial_coeff_repr b hr a j).symm)
  exact (Nat.succ_le_succ (Nat.div_pos hj hr)).trans (Polynomial.le_natDegree_of_ne_zero hc)

private lemma sum_addChar_eval_eq_zero_of_natDegree_eq_one {F : Type*}
    [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (f : Polynomial F) (hf : f.natDegree = 1) : ∑ x, ψ (f.eval x) = 0 := by
  have hc : f.coeff 1 ≠ 0 := by
    simpa only [← hf, Polynomial.coeff_natDegree, ne_eq, Polynomial.leadingCoeff_eq_zero]
      using (show f ≠ 0 from fun hz ↦ by simp [hz] at hf)
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf.le]
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    AddChar.map_add_eq_mul, AddChar.mulShift_apply, ← Finset.sum_mul, zero_mul] using
    congrArg (· * ψ (f.coeff 0))
      (AddChar.sum_eq_zero_of_ne_one ((AddChar.IsPrimitive.of_ne_one hψ) hc))

private lemma sum_power_coordinates_eq_zero_of_linear {p r q : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r)
    {a : Fin q → ZMod p} (ha : a ∈ linearPhaseIndices p r q) (ha₀ : a ≠ 0) :
    (∑ x : F, ZMod.stdAddChar
      (∑ j, a j * b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩)) = 0 := by
  have hψ : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
    simpa only [AddChar.mulShift_one] using ZMod.isPrimitive_stdAddChar p (a := 1) one_ne_zero
  simpa only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
    trace_powerPhasePolynomial_eval] using
    sum_addChar_eval_eq_zero_of_natDegree_eq_one
      (ZMod.stdAddChar.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom)
      (addChar_comp_trace_ne_one (F := ZMod p) (E := F) ZMod.stdAddChar hψ)
      (powerPhasePolynomial b hr a)
      (le_antisymm (powerPhasePolynomial_natDegree_le_one b hr ha)
        (powerPhasePolynomial_natDegree_pos b hr ha₀))

private lemma norm_sum_power_coordinates_le_of_le_mul {p r q d : ℕ}
    [Fact p.Prime] {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (hqd : q ≤ r * d)
    (hdp : d < p) {a : Fin q → ZMod p} (ha : a ≠ 0) :
    ‖∑ x : F, ZMod.stdAddChar
      (∑ j, a j * b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩)‖ ≤
        ((d - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
  by_cases hlin : a ∈ linearPhaseIndices p r q
  · simpa only [sum_power_coordinates_eq_zero_of_linear b hr hlin ha, norm_zero] using
      (mul_nonneg (Nat.cast_nonneg (d - 1)) (Real.sqrt_nonneg (Fintype.card F)))
  · have hdeg := powerPhasePolynomial_natDegree_le_of_le_mul b hr a hqd
    have hpos : 0 < (powerPhasePolynomial b hr a).natDegree :=
      (by decide : 0 < 2).trans_le (two_le_powerPhasePolynomial_natDegree b hr hlin)
    have hcop : (powerPhasePolynomial b hr a).natDegree.Coprime (Fintype.card (ZMod p)) := by
      simpa only [ZMod.card] using ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt hpos (hdeg.trans_lt hdp))).symm
    have hψ : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
      simpa only [AddChar.mulShift_one] using ZMod.isPrimitive_stdAddChar p (a := 1) one_ne_zero
    have h := norm_sum_addChar_trace_le_degree_sub_one_mul_sqrt
      (powerPhasePolynomial b hr a) hpos hcop ZMod.stdAddChar hψ
    simpa only [trace_powerPhasePolynomial_eval] using h.trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le_sub_right hdeg 1))
        (Real.sqrt_nonneg _))

private def finiteFrequency (A : Data) (L : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (∏ j ∈ Finset.range k, A.base j : ℕ) * L k

private lemma finiteFrequency_bound (A : Data) (L : ℕ → ℤ)
    (hL : ∀ n, 2 * |L n| ≤ (A.base n : ℤ) - 1) (n : ℕ) :
    2 * |finiteFrequency A L n| ≤ (∏ j ∈ Finset.range n, A.base j : ℕ) - (1 : ℤ) := by
  induction n with
  | zero => simp [finiteFrequency]
  | succ n ih =>
    have hprod : (0 : ℤ) ≤ (∏ j ∈ Finset.range n, A.base j : ℕ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left (hL n) hprod
    have hadd := abs_add_le (finiteFrequency A L n)
      ((∏ j ∈ Finset.range n, A.base j : ℕ) * L n)
    rw [abs_mul, abs_of_nonneg hprod] at hadd
    simp only [finiteFrequency, Finset.sum_range_succ, Finset.prod_range_succ,
      Nat.cast_mul] at ih hadd ⊢
    nlinarith

private lemma abs_finiteFrequency_div_scale_lt (A : Data) (L : ℕ → ℤ)
    (hL : ∀ n, 2 * |L n| ≤ (A.base n : ℤ) - 1) (n : ℕ) :
    |(finiteFrequency A L (n + 1) : ℝ) / A.scale n| < 1 / 2 := by
  have hbound : 2 * |(finiteFrequency A L (n + 1) : ℝ)| ≤ (A.scale n : ℝ) - 1 := by
    exact_mod_cast finiteFrequency_bound A L hL (n + 1)
  have hscale : 0 < (A.scale n : ℝ) := by
    linarith [abs_nonneg (finiteFrequency A L (n + 1) : ℝ)]
  rw [abs_div, abs_of_pos hscale, div_lt_iff₀ hscale]
  linarith

private def powerMoranData (p r m : ℕ → ℕ) [∀ n, NeZero (p n)] (F : ℕ → Type*)
    [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, Algebra (ZMod (p n)) (F n)]
    (b : ∀ n, Module.Basis (Fin (r n)) (ZMod (p n)) (F n))
    (hp : ∀ n, 2 ≤ p n) (hr : ∀ n, 0 < r n) : Data where
  base n := p n ^ (r n + m n)
  two_le_base n := (hp n).trans (Nat.le_pow (Nat.add_pos_left (hr n) _))
  digits n := powerDigitSet (b n) (hr n) (m n)
  digits_nonempty n := powerDigitSet_nonempty (b n) (hr n) (m n)
  digit_lt_base n _ hd := mem_powerDigitSet_lt (b n) (hr n) (m n) hd

private def galoisPowerBasis (p r : ℕ) [Fact p.Prime] (hr : 0 < r) :
    Module.Basis (Fin r) (ZMod p) (GaloisField p r) :=
  let b := Field.powerBasisOfFiniteOfSeparable (ZMod p) (GaloisField p r)
  b.basis.reindex (finCongr (b.finrank.symm.trans (GaloisField.finrank p hr.ne')))

private lemma galoisPowerBasis_apply (p r : ℕ) [Fact p.Prime] (hr : 0 < r) (j : Fin r) :
    galoisPowerBasis p r hr j =
      (Field.powerBasisOfFiniteOfSeparable (ZMod p) (GaloisField p r)).gen ^ j.val := by
  simp [galoisPowerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

private def galoisPowerMoranData (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) : Data :=
  letI : ∀ n, Fintype (GaloisField (p n) (r n)) := fun _ ↦ Fintype.ofFinite _
  powerMoranData p r m (fun n ↦ GaloisField (p n) (r n))
    (fun n ↦ galoisPowerBasis (p n) (r n) (hr n))
    (fun n ↦ (Fact.out : (p n).Prime).two_le) hr

private lemma galoisPowerMoranData_card_digits (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) (n : ℕ) :
    ((galoisPowerMoranData p r m hr).digits n).card = p n ^ r n := by
  simp only [galoisPowerMoranData, powerMoranData, card_powerDigitSet]

/-- The normalized trigonometric mask of a finite digit set. -/
def mask (B : Finset ℕ) (ξ : ℝ) : ℂ :=
  (B.card : ℂ)⁻¹ *
    ∑ d ∈ B, Complex.exp
      ((-2 * Real.pi * (d : ℝ) * ξ : ℝ) * Complex.I)

private def multisetMask (B : Multiset ℕ) (ξ : ℝ) : ℂ :=
  (B.card : ℂ)⁻¹ * (B.map fun d : ℕ ↦
    Complex.exp ((-2 * Real.pi * (d : ℝ) * ξ : ℝ) * Complex.I)).sum

private lemma multisetMask_map_univ {α : Type*} [Fintype α] (b : α → ℕ) (ξ : ℝ) :
    multisetMask (Finset.univ.val.map b) ξ = (Fintype.card α : ℂ)⁻¹ *
      ∑ x, Complex.exp ((-2 * Real.pi * (b x : ℝ) * ξ : ℝ) * Complex.I) := by
  simp [multisetMask, Multiset.map_map]

private lemma mask_image_eq_multisetMask {α : Type*} [Fintype α] (b : α → ℕ)
    (hb : Function.Injective b) (ξ : ℝ) :
    mask (Finset.univ.image b) ξ = multisetMask (Finset.univ.val.map b) ξ := by
  simp [mask, multisetMask_map_univ, Finset.card_image_of_injective _ hb,
    Finset.sum_image (fun _ _ _ _ h ↦ hb h)]

private def digitPhase {p : ℕ} [NeZero p] (θ : ℝ) (z : ZMod p) : ℂ :=
  Complex.exp ((-2 * Real.pi * θ * ((ZMod.finEquiv p).symm z).val : ℝ) * Complex.I)

private lemma prod_digitPhase {p q : ℕ} [NeZero p] (ξ : ℝ) (z : Fin q → ZMod p) :
    (∏ j, digitPhase ((p : ℝ) ^ j.val * ξ) (z j)) =
      Complex.exp ((-2 * Real.pi *
        (∑ j, ((ZMod.finEquiv p).symm (z j)).val * p ^ j.val : ℕ) * ξ : ℝ) * Complex.I) := by
  simp only [digitPhase, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private lemma finite_fourier_product_expansion {p q : ℕ} [NeZero p] {α : Type*} [Fintype α]
    (f : Fin q → ZMod p → ℂ) (g : Fin q → α → ZMod p) :
    (∑ x : α, ∏ j, f j (g j x)) =
      ∑ a : Fin q → ZMod p, (∏ j, (p : ℂ)⁻¹ * ZMod.dft (f j) (a j)) *
        ∑ x : α, ZMod.stdAddChar (∑ j, a j * g j x) := by
  have hinv (j : Fin q) (y : ZMod p) : f j y =
      ∑ k : ZMod p, ((p : ℂ)⁻¹ * ZMod.dft (f j) k) * ZMod.stdAddChar (k * y) := by
    have h := congrFun (ZMod.dft.symm_apply_apply (f j)) y
    simpa only [ZMod.invDFT_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
      mul_comm (ZMod.stdAddChar (_ * y))] using h.symm
  simp_rw [hinv, Fintype.prod_sum]
  rw [Finset.sum_comm]
  have hchar (a : Fin q → ZMod p) (x : α) :
      (∏ j, ZMod.stdAddChar (a j * g j x)) = ZMod.stdAddChar (∑ j, a j * g j x) := by
    simpa only [AddChar.toMonoidHom_apply, toAdd_prod, toAdd_ofAdd] using
      (map_prod ZMod.stdAddChar.toMonoidHom
        (fun j ↦ Multiplicative.ofAdd (a j * g j x)) Finset.univ).symm
  simp only [Finset.prod_mul_distrib, hchar, Finset.mul_sum]

private lemma multisetMask_expansion {p q : ℕ} [NeZero p] {α : Type*} [Fintype α]
    (b : α → ℕ) (g : Fin q → α → ZMod p)
    (hb : ∀ x, b x = ∑ j, ((ZMod.finEquiv p).symm (g j x)).val * p ^ j.val)
    (ξ : ℝ) :
    multisetMask (Finset.univ.val.map b) ξ =
      ∑ a : Fin q → ZMod p,
        (∏ j, (p : ℂ)⁻¹ * ZMod.dft (digitPhase ((p : ℝ) ^ j.val * ξ)) (a j)) *
          ((Fintype.card α : ℂ)⁻¹ * ∑ x, ZMod.stdAddChar (∑ j, a j * g j x)) := by
  simpa only [multisetMask_map_univ, hb, prod_digitPhase, Finset.mul_sum, mul_left_comm]
    using congrArg ((Fintype.card α : ℂ)⁻¹ * ·)
      (finite_fourier_product_expansion
        (fun j ↦ digitPhase ((p : ℝ) ^ j.val * ξ)) g)

private lemma mask_powerDigitSet_eq_prod_sum {p r m : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (ξ : ℝ) :
    mask (powerDigitSet b hr m) ξ = ((p ^ r : ℕ) : ℂ)⁻¹ *
      ∑ x : F, ∏ j : Fin (r + m), digitPhase ((p : ℝ) ^ j.val * ξ)
        (b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩) := by
  rw [mask, card_powerDigitSet]
  simp only [prod_digitPhase, ← powerDigit_eq_sum (m := m) b hr]
  simp only [powerDigitSet, Finset.sum_image
    (fun _ _ _ _ h ↦ powerDigit_injective b hr m h)]

private lemma sum_prod_digitPhase {p q : ℕ} [NeZero p] (ξ : ℝ) :
    (∑ z : Fin q → ZMod p, ∏ j, digitPhase ((p : ℝ) ^ j.val * ξ) (z j)) =
      ∑ d ∈ Finset.range (p ^ q),
        Complex.exp ((-2 * Real.pi * (d : ℝ) * ξ : ℝ) * Complex.I) := by
  let e : (Fin q → ZMod p) ≃ Fin (p ^ q) :=
    (Equiv.piCongrRight fun _ ↦ (ZMod.finEquiv p).toEquiv.symm).trans finFunctionFinEquiv
  have h := e.sum_comp (fun d ↦
    Complex.exp ((-2 * Real.pi * (d.val : ℝ) * ξ : ℝ) * Complex.I))
  simpa only [prod_digitPhase, e, Equiv.trans_apply, finFunctionFinEquiv_apply,
    Equiv.piCongrRight_apply, Pi.map_apply,
    Fin.sum_univ_eq_sum_range (fun d ↦
      Complex.exp ((-2 * Real.pi * (d : ℝ) * ξ : ℝ) * Complex.I)) (p ^ q)] using! h

private lemma mask_range_pow_eq_prod_dft_zero {p q : ℕ} [NeZero p] (ξ : ℝ) :
    mask (Finset.range (p ^ q)) ξ =
      ∏ j : Fin q, (p : ℂ)⁻¹ * ZMod.dft (digitPhase (p := p) ((p : ℝ) ^ j.val * ξ)) 0 := by
  simp only [ZMod.dft_apply_zero, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, inv_pow, Fintype.prod_sum, sum_prod_digitPhase]
  simp only [mask, Finset.card_range, Nat.cast_pow]

open scoped Classical in
private lemma sum_linear_mask_terms_eq_range {p r m : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (ξ : ℝ) :
    (∑ a ∈ Finset.univ.filter (fun a : Fin (r + m) → ZMod p ↦
      a ∈ linearPhaseIndices p r (r + m)),
      (∏ j, (p : ℂ)⁻¹ * ZMod.dft (digitPhase ((p : ℝ) ^ j.val * ξ)) (a j)) *
        (((p ^ r : ℕ) : ℂ)⁻¹ * ∑ x : F, ZMod.stdAddChar
          (∑ j, a j * b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩))) =
      mask (Finset.range (p ^ (r + m))) ξ := by
  rw [Finset.sum_eq_single (0 : Fin (r + m) → ZMod p)]
  · have hcard : Fintype.card F = p ^ r := by
      simpa only [Fintype.card_fin] using Fintype.card_congr (fieldResidueEquiv b)
    simp [hcard, NeZero.ne p, mask_range_pow_eq_prod_dft_zero]
  · intro a ha ha₀
    simp only [sum_power_coordinates_eq_zero_of_linear b hr (Finset.mem_filter.mp ha).2 ha₀,
      mul_zero]
  · simp [linearPhaseIndices]

private lemma mask_powerDigitSet_expansion {p r m : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (ξ : ℝ) :
    mask (powerDigitSet b hr m) ξ = ∑ a : Fin (r + m) → ZMod p,
      (∏ j, (p : ℂ)⁻¹ * ZMod.dft (digitPhase ((p : ℝ) ^ j.val * ξ)) (a j)) *
        (((p ^ r : ℕ) : ℂ)⁻¹ * ∑ x : F, ZMod.stdAddChar
          (∑ j, a j * b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩)) := by
  simpa only [← mask_image_eq_multisetMask _ (powerDigit_injective b hr m),
    powerDigitSet, show Fintype.card F = p ^ r from
      (Fintype.card_congr (fieldResidueEquiv b)).trans (Fintype.card_fin _)] using
    multisetMask_expansion (powerDigit b hr m)
      (fun j x ↦ b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩)
      (powerDigit_eq_sum b hr) ξ

open scoped Classical in
private lemma mask_sub_range_eq_sum_nonlinear {p r m : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (ξ : ℝ) :
    mask (powerDigitSet b hr m) ξ - mask (Finset.range (p ^ (r + m))) ξ =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (r + m) → ZMod p ↦
        a ∉ linearPhaseIndices p r (r + m)),
        (∏ j, (p : ℂ)⁻¹ * ZMod.dft (digitPhase ((p : ℝ) ^ j.val * ξ)) (a j)) *
          (((p ^ r : ℕ) : ℂ)⁻¹ * ∑ x : F, ZMod.stdAddChar
            (∑ j, a j * b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩)) := by
  rw [mask_powerDigitSet_expansion, ← sum_linear_mask_terms_eq_range b hr ξ,
    sub_eq_iff_eq_add, Finset.sum_filter_not_add_sum_filter]

private lemma digitPhase_mul_stdAddChar {p : ℕ} [NeZero p] (θ : ℝ) (z a : Fin p) :
    digitPhase θ (ZMod.finEquiv p z) *
      ZMod.stdAddChar (-(ZMod.finEquiv p z * ZMod.finEquiv p a)) =
        digitPhase (θ + (a.val : ℝ) / p) (ZMod.finEquiv p z) := by
  have hc : ((-(z.val : ℤ) * a.val : ℤ) : ZMod p) =
      -(ZMod.finEquiv p z * ZMod.finEquiv p a) := by
    simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast, natCast_finEquiv, neg_mul]
  rw [← hc, ZMod.stdAddChar_coe]
  simp only [digitPhase, RingEquiv.symm_apply_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma dft_digitPhase_eq_mask {p : ℕ} [NeZero p] (θ : ℝ) (a : Fin p) :
    (p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) (ZMod.finEquiv p a) =
      mask (Finset.range p) (θ + (a.val : ℝ) / p) := by
  rw [ZMod.dft_apply, mask, Finset.card_range]
  congr 1
  have h := (ZMod.finEquiv p).toEquiv.sum_comp (fun z ↦
    ZMod.stdAddChar (-(z * ZMod.finEquiv p a)) * digitPhase θ z)
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    mul_comm (ZMod.stdAddChar _), digitPhase_mul_stdAddChar] at h
  simp only [digitPhase, RingEquiv.symm_apply_apply,
    Fin.sum_univ_eq_sum_range (fun d ↦
      Complex.exp ((-2 * Real.pi * (θ + (a.val : ℝ) / p) * (d : ℝ) : ℝ) * Complex.I)) p] at h
  simpa only [digitPhase, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h.symm

private lemma exp_mask_phase_eq_pow (d : ℕ) (ξ : ℝ) :
    Complex.exp ((-2 * Real.pi * (d : ℝ) * ξ : ℝ) * Complex.I) =
      Complex.exp (Complex.I * (-2 * Real.pi * ξ : ℝ)) ^ d := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma mask_range_mul_exp_sub_one {N : ℕ} (hN : N ≠ 0) (ξ : ℝ) :
    (N : ℂ) * mask (Finset.range N) ξ *
      (Complex.exp (Complex.I * (-2 * Real.pi * ξ : ℝ)) - 1) =
        Complex.exp (Complex.I * (-2 * Real.pi * ξ : ℝ)) ^ N - 1 := by
  simp only [mask, Finset.card_range, exp_mask_phase_eq_pow]
  simpa [hN, mul_assoc] using
    geom_sum_mul (Complex.exp (Complex.I * (-2 * Real.pi * ξ : ℝ))) N

private lemma norm_exp_mask_phase_sub_one (ξ : ℝ) :
    ‖Complex.exp (Complex.I * (-2 * Real.pi * ξ : ℝ)) - 1‖ = 2 * |Real.sin (Real.pi * ξ)| := by
  simpa only [show -2 * Real.pi * ξ / 2 = -(Real.pi * ξ) by ring, Real.norm_eq_abs,
    abs_mul, Real.sin_neg, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      Complex.norm_exp_I_mul_ofReal_sub_one (-2 * Real.pi * ξ)

private lemma norm_mask_range_mul_sin {N : ℕ} (hN : N ≠ 0) (ξ : ℝ) :
    N * ‖mask (Finset.range N) ξ‖ * |Real.sin (Real.pi * ξ)| =
      |Real.sin (Real.pi * (N * ξ))| := by
  have hpow : Complex.exp (Complex.I * (-2 * Real.pi * ξ : ℝ)) ^ N =
      Complex.exp (Complex.I * (-2 * Real.pi * (N : ℝ) * ξ : ℝ)) :=
    (exp_mask_phase_eq_pow N ξ).symm.trans (congrArg Complex.exp (mul_comm _ _))
  have h := congrArg norm (mask_range_mul_exp_sub_one hN ξ)
  simp only [hpow, show -2 * Real.pi * (N : ℝ) * ξ = -2 * Real.pi * (N * ξ) by ring,
    norm_mul, Complex.norm_natCast, norm_exp_mask_phase_sub_one] at h
  linarith

private lemma two_mul_abs_sub_round_le_abs_sin (x : ℝ) :
    2 * |x - round x| ≤ |Real.sin (Real.pi * x)| := by
  have harg : |Real.pi * (x - round x)| ≤ Real.pi / 2 := by
    simpa only [abs_mul, abs_of_pos Real.pi_pos, mul_one_div] using
      mul_le_mul_of_nonneg_left (abs_sub_round x) Real.pi_pos.le
  have h : 2 * |x - round x| ≤ |Real.sin (Real.pi * (x - round x))| := by
    simpa [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc] using Real.mul_abs_le_abs_sin harg
  simpa [mul_sub, mul_comm Real.pi (round x : ℝ), Real.sin_sub_int_mul_pi,
    abs_mul, abs_zpow] using h

private lemma norm_mask_range_mul_round_dist_le {N : ℕ} (hN : N ≠ 0) (x : ℝ) :
    ‖mask (Finset.range N) x‖ * (2 * N * |x - round x|) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (two_mul_abs_sub_round_le_abs_sin x)
    (show 0 ≤ ‖mask (Finset.range N) x‖ * N by positivity)
  nlinarith [norm_mask_range_mul_sin hN x, Real.abs_sin_le_one (Real.pi * (N * x))]

private lemma two_div_pi_le_norm_mask_range {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : |x| ≤ 1 / 2) : 2 / Real.pi ≤ ‖mask (Finset.range N) (x / N)‖ := by
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    simpa only [abs_mul, abs_of_pos Real.pi_pos, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hx Real.pi_pos.le
  have hsin : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
    simpa [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc] using Real.mul_abs_le_abs_sin harg
  have hden : (N : ℝ) * |Real.sin (Real.pi * (x / N))| ≤ Real.pi * |x| := by
    have h := mul_le_mul_of_nonneg_left
      (Real.abs_sin_le_abs (x := Real.pi * (x / N))) hN'.le
    simpa [abs_mul, abs_div, abs_of_pos Real.pi_pos, abs_of_pos hN', div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc, hN'.ne'] using h
  have hid := norm_mask_range_mul_sin hN.ne' (x / N)
  simp only [mul_div_cancel₀ _ hN'.ne'] at hid
  have hmul := mul_le_mul_of_nonneg_left hden (norm_nonneg (mask (Finset.range N) (x / N)))
  have hmain : 2 * |x| ≤ (‖mask (Finset.range N) (x / N)‖ * Real.pi) * |x| := by
    nlinarith
  by_cases hx0 : x ≠ 0
  · exact (div_le_iff₀ Real.pi_pos).mpr
      ((mul_le_mul_iff_of_pos_right (abs_pos.mpr hx0)).mp hmain)
  · simpa [not_not.mp hx0, mask, hN.ne'] using (div_le_one Real.pi_pos).mpr Real.two_le_pi

private lemma two_div_pi_sub_le_norm_mask (B : Finset ℕ) {N : ℕ} (hN : 0 < N)
    {x ε : ℝ} (hx : |x| ≤ 1 / 2)
    (herror : ‖mask B (x / N) - mask (Finset.range N) (x / N)‖ ≤ ε) :
    2 / Real.pi - ε ≤ ‖mask B (x / N)‖ := by
  linarith [two_div_pi_le_norm_mask_range hN hx,
    norm_le_norm_add_norm_sub (mask B (x / N)) (mask (Finset.range N) (x / N))]

private lemma norm_mask_le_one (B : Finset ℕ) (hB : B.Nonempty) (ξ : ℝ) :
    ‖mask B ξ‖ ≤ 1 := by
  rw [mask, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (B.card : ℝ)⁻¹ * ‖∑ d ∈ B, Complex.exp
        (((-2 * Real.pi * d * ξ : ℝ) : ℂ) * Complex.I)‖ ≤
        (B.card : ℝ)⁻¹ * ∑ d ∈ B, ‖Complex.exp
          (((-2 * Real.pi * d * ξ : ℝ) : ℂ) * Complex.I)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = 1 := by
      simp [Complex.norm_exp, Nat.ne_of_gt hB.card_pos]

private def centeredGridIndex (p : ℕ) (θ : ℝ) (a : Fin p) : ℤ :=
  a.val - p * round (θ + (a.val : ℝ) / p) + round (p * θ)

private lemma centeredGridIndex_injective {p : ℕ} [NeZero p] (θ : ℝ) :
    Function.Injective (centeredGridIndex p θ) := by
  intro a b h
  have hz := congrArg (fun z : ℤ ↦ (z : ZMod p)) h
  simp only [centeredGridIndex, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero, add_left_inj] at hz
  exact (ZMod.finEquiv p).injective (by simpa only [natCast_finEquiv] using hz)

private lemma centeredGridIndex_eq {p : ℕ} (hp : 0 < p) (θ : ℝ) (a : Fin p) :
    (centeredGridIndex p θ a : ℝ) =
      p * (θ + (a.val : ℝ) / p - round (θ + (a.val : ℝ) / p)) -
        (p * θ - round (p * θ)) := by
  simp only [centeredGridIndex, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  field_simp
  ring

private lemma abs_centeredGridIndex_le {p : ℕ} (hp : 0 < p) (θ : ℝ) (a : Fin p) :
    |(centeredGridIndex p θ a : ℝ)| ≤
      p * |θ + (a.val : ℝ) / p - round (θ + (a.val : ℝ) / p)| + 1 / 2 := by
  rw [centeredGridIndex_eq hp]
  exact (abs_sub _ _).trans (by
    simpa only [abs_mul, abs_of_nonneg (show 0 ≤ (p : ℝ) by positivity)] using
      add_le_add_right (abs_sub_round ((p : ℝ) * θ)) _)

private lemma centeredGridIndex_mem_Icc {p : ℕ} (hp : 0 < p) (θ : ℝ) (a : Fin p) :
    centeredGridIndex p θ a ∈ Finset.Icc (-(p : ℤ)) p := by
  have h := abs_centeredGridIndex_le hp θ a
  have habs := abs_sub_round (θ + (a.val : ℝ) / p)
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hk : |(centeredGridIndex p θ a : ℝ)| ≤ p := by nlinarith
  rw [abs_le] at hk
  simpa only [Finset.mem_Icc, ← Int.cast_le (R := ℝ), Int.cast_neg, Int.cast_natCast] using hk

private def gridWeight (k : ℤ) : ℝ :=
  if k.natAbs ≤ 1 then 1 else (2 * (k.natAbs - 1 : ℕ) : ℝ)⁻¹

private lemma norm_mask_range_le_gridWeight {p : ℕ} (hp : 0 < p) (θ : ℝ) (a : Fin p) :
    ‖mask (Finset.range p) (θ + (a.val : ℝ) / p)‖ ≤
      gridWeight (centeredGridIndex p θ a) := by
  let k := centeredGridIndex p θ a
  change _ ≤ gridWeight k
  by_cases hk : k.natAbs ≤ 1
  · simpa only [gridWeight, if_pos hk] using
      norm_mask_le_one (Finset.range p) (Finset.nonempty_range_iff.mpr hp.ne') _
  · have hk' : 1 ≤ k.natAbs := by omega
    rw [gridWeight, if_neg hk, Nat.cast_sub hk', Nat.cast_one, ← one_div,
      le_div_iff₀ (by exact_mod_cast (show 0 < 2 * (k.natAbs - 1 : ℤ) by omega))]
    have h := mul_le_mul_of_nonneg_left (abs_centeredGridIndex_le hp θ a)
      (norm_nonneg (mask (Finset.range p) (θ + (a.val : ℝ) / p)))
    rw [show (k.natAbs : ℝ) = |(k : ℝ)| by
      simpa only [Int.cast_natCast, Int.cast_abs] using
        congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.natCast_natAbs k)]
    dsimp only [k]
    nlinarith [norm_mask_range_mul_round_dist_le hp.ne' (θ + (a.val : ℝ) / p),
      norm_nonneg (mask (Finset.range p) (θ + (a.val : ℝ) / p))]

private lemma sum_gridWeight_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), gridWeight k) = 2 + (harmonic n : ℝ) / 2 := by
  rw [show n + 2 = 2 + n by omega, Finset.sum_range_add]
  simp only [gridWeight, Int.natAbs_natCast]
  simp only [show ∀ x : ℕ, ¬2 + x ≤ 1 by omega, if_false,
    show ∀ x : ℕ, 2 + x - 1 = x + 1 by omega]
  norm_num [Finset.sum_range_succ, harmonic, Rat.cast_sum, ← Finset.sum_div,
    mul_inv_rev, div_eq_mul_inv]
  exact (Finset.sum_mul _ _ _).symm

private lemma sum_gridWeight_Icc {p : ℕ} (hp : 0 < p) :
    (∑ k ∈ Finset.Icc (-(p : ℤ)) p, gridWeight k) = 3 + (harmonic (p - 1) : ℝ) := by
  rw [Finset.sum_Icc_of_even_eq_range (by intro k; simp only [gridWeight, Int.natAbs_neg]),
    show p + 1 = (p - 1) + 2 by omega, sum_gridWeight_range]
  norm_num [gridWeight, nsmul_eq_mul]
  ring

private lemma sum_norm_mask_grid_le {p : ℕ} [NeZero p] (θ : ℝ) :
    (∑ a : Fin p, ‖mask (Finset.range p) (θ + (a.val : ℝ) / p)‖) ≤
      3 + (harmonic (p - 1) : ℝ) := by
  classical
  have hp := Nat.pos_of_ne_zero (NeZero.ne p)
  calc
    _ ≤ ∑ a : Fin p, gridWeight (centeredGridIndex p θ a) :=
      Finset.sum_le_sum (fun a _ ↦ norm_mask_range_le_gridWeight hp θ a)
    _ = ∑ k ∈ Finset.univ.image (centeredGridIndex p θ), gridWeight k :=
      (Finset.sum_image (fun _ _ _ _ h ↦ centeredGridIndex_injective θ h)).symm
    _ ≤ ∑ k ∈ Finset.Icc (-(p : ℤ)) p, gridWeight k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ ↦ ?_)
      · exact Finset.image_subset_iff.mpr (fun a _ ↦ centeredGridIndex_mem_Icc hp θ a)
      · unfold gridWeight
        split_ifs <;> positivity
    _ = _ := sum_gridWeight_Icc hp

private lemma three_add_harmonic_le_mask_log {p : ℕ} (hp : 16 ≤ p) :
    3 + (harmonic (p - 1) : ℝ) ≤ 2 * Real.log (2 * p) := by
  have hp' : (16 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog := Real.log_le_log (by norm_num : 0 < (16 : ℝ)) hp'
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hmono : Real.log (p - 1 : ℕ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < p - 1 by omega))
      (by exact_mod_cast Nat.sub_le p 1)
  rw [Real.log_mul (by norm_num) (by exact_mod_cast (show p ≠ 0 by omega))]
  linarith [harmonic_le_one_add_log (p - 1), Real.log_two_gt_d9]

private lemma sum_sq_norm_dft_digitPhase {p : ℕ} [NeZero p] (θ : ℝ) :
    ∑ a : ZMod p, ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖ ^ 2 = 1 := by
  have h := finite_fourier_parseval ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar p)
    (digitPhase (p := p) θ)
  rw [← Equiv.sum_comp (Equiv.neg (ZMod p))
    (fun a ↦ ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖ ^ 2)]
  simp only [Equiv.neg_apply, ZMod.dft_apply, mul_neg, neg_neg, smul_eq_mul,
    mul_comm (ZMod.stdAddChar _) (digitPhase θ _), norm_mul, norm_inv,
    Complex.norm_natCast, mul_pow, ← Finset.mul_sum, h]
  simp [digitPhase, Complex.norm_exp, ← pow_two, NeZero.ne p]

private lemma sq_sum_norm_dft_digitPhase_le {p : ℕ} [NeZero p] (θ : ℝ) :
    (∑ a : ZMod p, ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖) ^ 2 ≤ p := by
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, sum_sq_norm_dft_digitPhase, one_mul] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun a : ZMod p ↦ ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖) (fun _ ↦ (1 : ℝ))

private lemma sum_norm_dft_digitPhase_le_of_sixteen_le {p : ℕ} [NeZero p]
    (hp : 16 ≤ p) (θ : ℝ) :
    (∑ a : ZMod p, ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖) ≤
      2 * Real.log (2 * p) := by
  have heq := (ZMod.finEquiv p).toEquiv.sum_comp
    (fun a ↦ ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖)
  rw [← heq]
  simpa only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, dft_digitPhase_eq_mask] using
    (sum_norm_mask_grid_le (p := p) θ).trans (three_add_harmonic_le_mask_log hp)

private lemma sum_norm_dft_digitPhase_le {p : ℕ} [NeZero p] (hp : 2 ≤ p) (θ : ℝ) :
    (∑ a : ZMod p, ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖) ≤
      2 * Real.log (2 * p) := by
  by_cases hlarge : 16 ≤ p
  · exact sum_norm_dft_digitPhase_le_of_sixteen_le hlarge θ
  · have hsq := sq_sum_norm_dft_digitPhase_le (p := p) θ
    have hp16 : (p : ℝ) < 16 := Nat.cast_lt.mpr (Nat.lt_of_not_ge hlarge)
    by_cases hfour : 4 ≤ p
    · have hlog := Real.log_le_log (by norm_num : 0 < (2 : ℝ) ^ 3)
        (show (2 : ℝ) ^ 3 ≤ 2 * p by
          nlinarith [show (4 : ℝ) ≤ p from Nat.cast_le.mpr hfour])
      simp only [Real.log_pow, Nat.cast_ofNat] at hlog
      nlinarith [Real.log_two_gt_d9,
        sq_nonneg ((∑ a : ZMod p, ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖) - 4)]
    · have hlog := Real.log_le_log (by norm_num : 0 < (2 : ℝ) ^ 2)
        (show (2 : ℝ) ^ 2 ≤ 2 * p by
          nlinarith [show (2 : ℝ) ≤ p from Nat.cast_le.mpr hp])
      simp only [Real.log_pow, Nat.cast_ofNat] at hlog
      nlinarith [Real.log_two_gt_d9,
        show (p : ℝ) < 4 from Nat.cast_lt.mpr (Nat.lt_of_not_ge hfour),
        sq_nonneg ((∑ a : ZMod p, ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase θ) a‖) - 2)]

private lemma norm_mask_sub_one_le (B : Finset ℕ) (hB : B.Nonempty) {N : ℕ}
    (hBN : ∀ d ∈ B, d < N) (ξ : ℝ) :
    ‖mask B ξ - 1‖ ≤ 2 * Real.pi * N * |ξ| := by
  have hcard : (B.card : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hB.card_pos
  have hterm (d : ℕ) (hd : d ∈ B) :
      ‖Complex.exp (((-2 * Real.pi * d * ξ : ℝ) : ℂ) * Complex.I) - 1‖ ≤
        2 * Real.pi * N * |ξ| := by
    calc
      _ ≤ ‖-2 * Real.pi * d * ξ‖ := by
        simpa only [mul_comm] using
          (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * Real.pi * d * ξ))
      _ = 2 * Real.pi * d * |ξ| := by
        rw [Real.norm_eq_abs]
        simp [abs_mul, Real.pi_pos.le]
      _ ≤ 2 * Real.pi * N * |ξ| := by
        gcongr
        exact_mod_cast (hBN d hd).le
  calc
    ‖mask B ξ - 1‖ = ‖(B.card : ℂ)⁻¹ *
        ∑ d ∈ B, (Complex.exp
          (((-2 * Real.pi * d * ξ : ℝ) : ℂ) * Complex.I) - 1)‖ := by
      congr 1
      rw [mask, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_sub]
      simp [hcard]
    _ ≤ ‖(B.card : ℂ)⁻¹‖ *
        ∑ d ∈ B, ‖Complex.exp
          (((-2 * Real.pi * d * ξ : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [norm_mul]
      gcongr
      exact norm_sum_le _ _
    _ ≤ ‖(B.card : ℂ)⁻¹‖ * ∑ _d ∈ B, (2 * Real.pi * N * |ξ|) := by
      gcongr with d hd
      exact hterm d hd
    _ = 2 * Real.pi * N * |ξ| := by
      rw [norm_inv, Complex.norm_natCast]
      simp [Nat.ne_of_gt hB.card_pos]

private lemma norm_mask_sub_one_le_geometric (A : Data) (ξ : ℝ) (n : ℕ) :
    ‖mask (A.digits n) (ξ / (A.scale n : ℝ)) - 1‖ ≤
      (2 * Real.pi * |ξ|) * (1 / 2 : ℝ) ^ n := by
  calc
    ‖mask (A.digits n) (ξ / (A.scale n : ℝ)) - 1‖ ≤
        2 * Real.pi * A.base n * |ξ / (A.scale n : ℝ)| :=
      norm_mask_sub_one_le (A.digits n) (A.digits_nonempty n)
        (A.digit_lt_base n) _
    _ = (2 * Real.pi * |ξ|) * ((A.base n : ℝ) / (A.scale n : ℝ)) := by
      rw [abs_div]
      have hscale : 0 < (A.scale n : ℝ) := by
        exact_mod_cast Finset.prod_pos fun k _ ↦
          lt_of_lt_of_le Nat.zero_lt_two (A.two_le_base k)
      rw [abs_of_pos hscale]
      ring
    _ ≤ (2 * Real.pi * |ξ|) * (1 / 2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_left (A.base_div_scale_le n)
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (abs_nonneg ξ))

private lemma summable_norm_mask_sub_one (A : Data) (ξ : ℝ) :
    Summable fun n ↦ ‖mask (A.digits n) (ξ / (A.scale n : ℝ)) - 1‖ := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_mask_sub_one_le_geometric A ξ)
    ((summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left
      (2 * Real.pi * |ξ|))

private lemma tsum_norm_mask_sub_one_le (A : Data) (ξ : ℝ) :
    ∑' n, ‖mask (A.digits n) (ξ / (A.scale n : ℝ)) - 1‖ ≤
      4 * Real.pi * |ξ| := by
  have hgeom : Summable fun n : ℕ ↦
      (2 * Real.pi * |ξ|) * (1 / 2 : ℝ) ^ n :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left _
  calc
    _ ≤ ∑' n : ℕ, (2 * Real.pi * |ξ|) * (1 / 2 : ℝ) ^ n :=
      Summable.tsum_le_tsum (norm_mask_sub_one_le_geometric A ξ)
        (summable_norm_mask_sub_one A ξ) hgeom
    _ = 4 * Real.pi * |ξ| := by
      rw [tsum_mul_left, tsum_geometric_two]
      ring

private lemma norm_prod_sub_one_le_sum_norm_sub_one {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) :
    ‖∏ i ∈ s, z i - 1‖ ≤ ∑ i ∈ s, ‖z i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      calc
        ‖z a * ∏ i ∈ s, z i - 1‖ =
            ‖z a * (∏ i ∈ s, z i - 1) + (z a - 1)‖ := by
          congr 1
          ring
        _ ≤ ‖z a‖ * ‖∏ i ∈ s, z i - 1‖ + ‖z a - 1‖ := by
          exact (norm_add_le _ _).trans_eq (congrArg₂ (· + ·) (norm_mul _ _) rfl)
        _ ≤ 1 * (∑ i ∈ s, ‖z i - 1‖) + ‖z a - 1‖ := by
          gcongr
          · exact hz a (Finset.mem_insert_self a s)
          · exact ih fun i hi ↦ hz i (Finset.mem_insert_of_mem hi)
        _ = ‖z a - 1‖ + ∑ i ∈ s, ‖z i - 1‖ := by ring

private lemma norm_hasProd_sub_one_le_tsum_norm_sub_one (z : ℕ → ℂ) (Z : ℂ)
    (hprod : HasProd z Z) (hz : ∀ n, ‖z n‖ ≤ 1)
    (hsum : Summable fun n ↦ ‖z n - 1‖) :
    ‖Z - 1‖ ≤ ∑' n, ‖z n - 1‖ := by
  apply le_of_tendsto_of_tendsto
    ((continuous_norm.comp (continuous_id.sub continuous_const)).tendsto Z |>.comp
      hprod.tendsto_prod_nat)
    hsum.hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall fun n ↦
    norm_prod_sub_one_le_sum_norm_sub_one (Finset.range n) z
      (fun i _ ↦ hz i)

private lemma one_sub_tsum_norm_sub_one_le_norm_hasProd (z : ℕ → ℂ) (Z : ℂ)
    (hprod : HasProd z Z) (hz : ∀ n, ‖z n‖ ≤ 1)
    (hsum : Summable fun n ↦ ‖z n - 1‖) :
    1 - ∑' n, ‖z n - 1‖ ≤ ‖Z‖ := by
  have hreverse : 1 - ‖Z‖ ≤ ‖Z - 1‖ := by
    calc
      1 - ‖Z‖ ≤ ‖(1 : ℂ) - Z‖ := by simpa using norm_sub_norm_le (1 : ℂ) Z
      _ = ‖Z - 1‖ := norm_sub_rev _ _
  linarith [norm_hasProd_sub_one_le_tsum_norm_sub_one z Z hprod hz hsum]

/-- The Fourier integral of the constant one function is the measure Fourier transform. -/
theorem fourierIntegral_one_eq (μ : Measure ℝ) (ξ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ =
      ∫ x : ℝ, Complex.exp
        ((-2 * Real.pi * ξ * x : ℝ) * Complex.I) ∂μ := by
  simp only [Fourier.fourierIntegral, Real.vector_fourierIntegral_eq_integral_exp_smul,
    LinearMap.mul_apply', smul_eq_mul, one_mul, mul_comm, mul_left_comm, mul_assoc]

private lemma charFun_factor (A : Data) (n : ℕ) (ξ : ℝ) :
    charFun (A.factor n) (-2 * Real.pi * ξ) =
      mask (A.digits n) (ξ / (A.scale n : ℝ)) := by
  simp [charFun_apply_real, Data.factor, mask, integral_smul_measure,
    integral_finsetSum_measure, integrable_dirac, ← Complex.exp_conj,
    div_eq_mul_inv, map_ofNat, mul_comm, mul_left_comm, mul_assoc]

private lemma integral_char_finset_coding (A : Data) (s : Finset ℕ) (t : ℝ) :
    (∫ d, BoundedContinuousFunction.innerProbChar t
      (∑ k ∈ s, (d k : ℝ) / (A.scale k : ℝ)) ∂Measure.infinitePi A.digitLaw) =
      ∏ k ∈ s, charFun (A.factor k) t := by
  have h := congrFun ((A.indep_coding_terms.restrict s).charFun_map_fun_finsetSum_eq_prod
    (fun k _ ↦ (A.measurable_coding_term k).aemeasurable)) t
  simpa only [A.map_coding_term, Finset.prod_apply, charFun_eq_integral_innerProbChar,
    integral_map_of_stronglyMeasurable
      (Finset.measurable_sum s (fun k _ ↦ A.measurable_coding_term k))
      (BoundedContinuousFunction.innerProbChar t).continuous.stronglyMeasurable] using h

private lemma hasProd_charFun_factor (A : Data) (t : ℝ) :
    HasProd (fun n ↦ charFun (A.factor n) t) (charFun A.measure t) := by
  have h := A.tendsto_integral_finset_coding (BoundedContinuousFunction.innerProbChar t)
  simpa only [HasProd, SummationFilter.unconditional_filter,
    integral_char_finset_coding, charFun_eq_integral_innerProbChar,
    Data.measure, integral_map_of_stronglyMeasurable A.measurable_coding
      (BoundedContinuousFunction.innerProbChar t).continuous.stronglyMeasurable] using h

/-- The Fourier transform of a Cantor–Moran measure is the convergent product of its masks. -/
theorem Data.hasProd_mask (A : Data) (ξ : ℝ) :
    HasProd (fun n ↦ mask (A.digits n) (ξ / (A.scale n : ℝ)))
      (Fourier.fourierIntegral Real.fourierChar A.measure
        (fun _ ↦ (1 : ℂ)) ξ) := by
  have h := hasProd_charFun_factor A (-2 * Real.pi * ξ)
  simp only [charFun_factor] at h
  simpa only [fourierIntegral_one_eq, charFun_apply_real, Complex.ofReal_mul] using h

private lemma one_sub_tsum_mask_error_le_norm_fourier (A : Data) (ξ : ℝ) :
    1 - ∑' n, ‖mask (A.digits n) (ξ / (A.scale n : ℝ)) - 1‖ ≤
      ‖Fourier.fourierIntegral Real.fourierChar A.measure
        (fun _ ↦ (1 : ℂ)) ξ‖ := by
  exact one_sub_tsum_norm_sub_one_le_norm_hasProd _ _ (A.hasProd_mask ξ)
    (fun n ↦ norm_mask_le_one (A.digits n) (A.digits_nonempty n) _)
    (summable_norm_mask_sub_one A ξ)

private lemma one_sub_four_pi_mul_abs_le_norm_fourier (A : Data) (ξ : ℝ) :
    1 - 4 * Real.pi * |ξ| ≤
      ‖Fourier.fourierIntegral Real.fourierChar A.measure
        (fun _ ↦ (1 : ℂ)) ξ‖ := by
  exact (sub_le_sub_left (tsum_norm_mask_sub_one_le A ξ) 1).trans
    (one_sub_tsum_mask_error_le_norm_fourier A ξ)

private lemma abs_div_scale_succ_le (A : Data) (n : ℕ) (hbase : 16 ≤ A.base (n + 1))
    {ξ : ℝ} (hξ : |ξ / A.scale n| < 1 / 2) : |ξ / A.scale (n + 1)| ≤ 1 / 32 := by
  have hbase' : (16 : ℝ) ≤ A.base (n + 1) := by exact_mod_cast hbase
  have heq : |ξ / A.scale (n + 1)| = |ξ / A.scale n| / A.base (n + 1) := by
    simp [Data.scale, Finset.prod_range_succ, abs_div, div_mul_eq_div_div]
  simpa only [heq, show (1 / 2 : ℝ) / 16 = 1 / 32 by norm_num] using
    div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hξ.le (by norm_num) hbase'

private def tailData (A : Data) (n : ℕ) : Data where
  base k := A.base (n + k)
  two_le_base k := A.two_le_base (n + k)
  digits k := A.digits (n + k)
  digits_nonempty k := A.digits_nonempty (n + k)
  digit_lt_base k := A.digit_lt_base (n + k)

private lemma tailData_tail (A : Data) (n m : ℕ) :
    tailData (tailData A n) m = tailData A (n + m) := by
  simp only [tailData, Nat.add_assoc]

private lemma prefix_mul_scale_tail (A : Data) (n k : ℕ) :
    (∏ j ∈ Finset.range n, A.base j) * (tailData A n).scale k = A.scale (n + k) := by
  simpa only [Data.scale, tailData, Nat.add_assoc] using
    (Finset.prod_range_add A.base n (k + 1)).symm

private lemma coding_eq_sum_add_tail (A : Data) (d : ℕ → ℕ)
    (hd : ∀ n, d n ∈ A.digits n) (n : ℕ) :
    A.coding d = (∑ j ∈ Finset.range n, (d j : ℝ) / A.scale j) +
      (tailData A n).coding (fun k ↦ d (n + k)) /
        ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) := by
  have htail : (tailData A n).coding (fun k ↦ d (n + k)) /
      ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) =
        ∑' k, (d (k + n) : ℝ) / A.scale (k + n) := by
    simp only [Data.coding, ← tsum_div_const, div_div, ← Nat.cast_mul]
    exact tsum_congr (fun k ↦ by rw [Nat.mul_comm, prefix_mul_scale_tail, Nat.add_comm n])
  rw [htail, Data.coding]
  exact ((A.summable_coding d hd).sum_add_tsum_nat_add n).symm

private def prefixInterval (A : Data) (n : ℕ) (d : ∀ j : Fin n, A.digits j) : Set ℝ :=
  let a := ∑ j : Fin n, ((d j : ℕ) : ℝ) / A.scale j
  Set.Icc a (a + ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)⁻¹)

private lemma carrier_subset_iUnion_prefixInterval (A : Data) (n : ℕ) :
    A.carrier ⊆ ⋃ d : (∀ j : Fin n, A.digits j), prefixInterval A n d := by
  rintro x ⟨d, hd, rfl⟩
  refine Set.mem_iUnion.mpr ⟨fun j ↦ ⟨d j, hd j⟩, ?_⟩
  have htail := (tailData A n).coding_mem_Icc (fun k ↦ d (n + k)) (fun k ↦ hd (n + k))
  simp only [prefixInterval, Fin.sum_univ_eq_sum_range (fun j ↦ (d j : ℝ) / A.scale j) n,
    coding_eq_sum_add_tail A d hd n,
    Set.mem_Icc, le_add_iff_nonneg_right, add_le_add_iff_left]
  exact ⟨div_nonneg htail.1 (Nat.cast_nonneg _),
    by simpa only [one_div] using div_le_div_of_nonneg_right htail.2 (Nat.cast_nonneg _)⟩

private lemma ediam_prefixInterval (A : Data) (n : ℕ) (d : ∀ j : Fin n, A.digits j) :
    Metric.ediam (prefixInterval A n d) =
      ENNReal.ofReal (((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)⁻¹) := by
  simp [prefixInterval, Real.ediam_Icc]

private lemma tendsto_prefix_product_atTop (A : Data) :
    Tendsto (fun n ↦ ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)) atTop atTop := by
  have hbound (n : ℕ) : (2 : ℝ) ^ n ≤ ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ^ n ≤ ∏ j ∈ Finset.range n, A.base j from by
      simpa using Finset.prod_le_prod (s := Finset.range n) (f := fun _ ↦ 2)
        (g := A.base) (fun _ _ ↦ Nat.zero_le _) (fun j _ ↦ A.two_le_base j))
  exact tendsto_atTop_mono hbound (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

private lemma sum_ediam_prefixInterval_rpow (A : Data) (n : ℕ) (d : ℝ) :
    (∑ v : (∀ j : Fin n, A.digits j), Metric.ediam (prefixInterval A n v) ^ d) =
      ENNReal.ofReal (((∏ j ∈ Finset.range n, (A.digits j).card : ℕ) : ℝ) *
        ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) ^ (-d)) := by
  classical
  simp only [ediam_prefixInterval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_pi, Fintype.card_coe]
  rw [Fin.prod_univ_eq_prod_range (fun j ↦ (A.digits j).card) n,
    ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (Nat.cast_pos.mpr (A.prefix_product_pos n)))]
  rw [Real.inv_rpow (Nat.cast_nonneg _) d, Real.rpow_neg (Nat.cast_nonneg _) d,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

private lemma hausdorffMeasure_carrier_eq_zero_of_tendsto (A : Data) (d : ℝ)
    (hcost : Tendsto (fun n ↦ ((∏ j ∈ Finset.range n, (A.digits j).card : ℕ) : ℝ) *
      ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) ^ (-d)) atTop (𝓝 0)) :
    Measure.hausdorffMeasure d A.carrier = 0 := by
  classical
  let r (n : ℕ) := ENNReal.ofReal (((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)⁻¹)
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa only [r, Pi.inv_apply, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_prefix_product_atTop A).inv_tendsto_atTop
  have hcover := Measure.hausdorffMeasure_le_liminf_sum d A.carrier r hr (prefixInterval A)
    (Eventually.of_forall (fun n v ↦ (ediam_prefixInterval A n v).le))
    (Eventually.of_forall (carrier_subset_iUnion_prefixInterval A))
  simpa only [sum_ediam_prefixInterval_rpow, (ENNReal.tendsto_ofReal hcost).liminf_eq,
    ENNReal.ofReal_zero, nonpos_iff_eq_zero] using hcover

private lemma prod_card_digits_le_rpow (A : Data) {s : ℝ}
    (hcard : ∀ j, ((A.digits j).card : ℝ) ≤ (A.base j : ℝ) ^ s) (n : ℕ) :
    ((∏ j ∈ Finset.range n, (A.digits j).card : ℕ) : ℝ) ≤
      ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) ^ s := by
  simp only [Nat.cast_prod]
  rw [← Real.finsetProd_rpow _ _ (fun j _ ↦ Nat.cast_nonneg (A.base j))]
  exact Finset.prod_le_prod (fun j _ ↦ Nat.cast_nonneg (A.digits j).card) (fun j _ ↦ hcard j)

private lemma dimH_carrier_le_of_cover_cost (A : Data) {s : ℝ} (hs : 0 ≤ s)
    (hcost : ∀ d : ℝ, s < d → Tendsto (fun n ↦
      ((∏ j ∈ Finset.range n, (A.digits j).card : ℕ) : ℝ) *
        ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) ^ (-d)) atTop (𝓝 0)) :
    dimH A.carrier ≤ ENNReal.ofReal s := by
  refine dimH_le (fun d hd ↦ ?_)
  by_contra! hds
  exact ENNReal.zero_ne_top
    ((hausdorffMeasure_carrier_eq_zero_of_tendsto A d
      (hcost d ((ENNReal.ofReal_lt_coe_iff hs).mp hds))).symm.trans hd)

private lemma tendsto_cover_cost_of_card_le (A : Data) {s d : ℝ} (hsd : s < d)
    (hcard : ∀ j, ((A.digits j).card : ℝ) ≤ (A.base j : ℝ) ^ s) :
    Tendsto (fun n ↦ ((∏ j ∈ Finset.range n, (A.digits j).card : ℕ) : ℝ) *
      ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) ^ (-d)) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ ↦ by positivity) (g := fun n ↦
    ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) ^ (-(d - s))) ?_ ?_
  · intro n
    simpa only [← Real.rpow_add (Nat.cast_pos.mpr (A.prefix_product_pos n)),
      show s + -d = -(d - s) by ring] using
      mul_le_mul_of_nonneg_right (prod_card_digits_le_rpow A hcard n)
        (Real.rpow_nonneg (Nat.cast_nonneg (∏ j ∈ Finset.range n, A.base j)) (-d))
  · exact (tendsto_rpow_neg_atTop (sub_pos.mpr hsd)).comp (tendsto_prefix_product_atTop A)

private lemma dimH_carrier_le_of_card_le (A : Data) {s : ℝ} (hs : 0 ≤ s)
    (hcard : ∀ j, ((A.digits j).card : ℝ) ≤ (A.base j : ℝ) ^ s) :
    dimH A.carrier ≤ ENNReal.ofReal s :=
  dimH_carrier_le_of_cover_cost A hs (fun _ hsd ↦ tendsto_cover_cost_of_card_le A hsd hcard)

private lemma galoisPowerMoranData_dimH_le (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) {s : ℝ} (hs : 0 ≤ s)
    (hdim : ∀ n, (r n : ℝ) ≤ (r n + m n : ℕ) * s) :
    dimH (galoisPowerMoranData p r m hr).carrier ≤ ENNReal.ofReal s := by
  refine dimH_carrier_le_of_card_le _ hs (fun n ↦ ?_)
  rw [galoisPowerMoranData_card_digits]
  change ((p n ^ r n : ℕ) : ℝ) ≤ ((p n ^ (r n + m n) : ℕ) : ℝ) ^ s
  simp only [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Fact.out : (p n).Prime).one_lt.le) (hdim n)

private lemma eventually_mul_log_pow_le_rpow (C : ℝ) (q : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ q ≤ x ^ δ := by
  filter_upwards [((isLittleO_log_rpow_rpow_atTop (q : ℝ) hδ).const_mul_left C).bound
    zero_lt_one, eventually_ge_atTop (0 : ℝ)] with x hx hx₀
  simp only [Real.rpow_natCast, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx₀ δ)] at hx
  exact (le_abs_self _).trans hx

private lemma eventually_mul_mask_log_pow_le_rpow {C : ℝ} (hC : 0 ≤ C) (q : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, C * (2 * Real.log (2 * x)) ^ q ≤ x ^ δ := by
  filter_upwards [eventually_mul_log_pow_le_rpow (C * 4 ^ q) q hδ,
    eventually_ge_atTop (2 : ℝ)] with x hx hx₂
  have hlog : 2 * Real.log (2 * x) ≤ 4 * Real.log x := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_log (by norm_num) hx₂]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) hlog q) hC).trans
    (by simpa only [mul_pow, mul_assoc] using hx)

private lemma fourier_eq_prod_mul_tail (A : Data) (n : ℕ) (ξ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ =
      (∏ k ∈ Finset.range n, mask (A.digits k) (ξ / A.scale k)) *
        Fourier.fourierIntegral Real.fourierChar (tailData A n).measure
          (fun _ ↦ (1 : ℂ)) (ξ / (∏ j ∈ Finset.range n, A.base j : ℕ)) := by
  have htail : HasProd (fun k ↦ mask (A.digits (k + n)) (ξ / A.scale (k + n)))
      (Fourier.fourierIntegral Real.fourierChar (tailData A n).measure
        (fun _ ↦ (1 : ℂ)) (ξ / (∏ j ∈ Finset.range n, A.base j : ℕ))) := by
    have h := (tailData A n).hasProd_mask (ξ / (∏ j ∈ Finset.range n, A.base j : ℕ))
    simp only [div_div, ← Nat.cast_mul, prefix_mul_scale_tail] at h
    simpa only [tailData, Nat.add_comm n] using h
  exact (A.hasProd_mask ξ).unique
    (htail.prod_range_mul (f := fun k ↦ mask (A.digits k) (ξ / A.scale k)) (k := n))

private lemma fourier_tail_eq_mask_mul (A : Data) (n : ℕ) (ξ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar (tailData A (n + 1)).measure
      (fun _ ↦ (1 : ℂ)) (ξ / A.scale n) =
        mask (A.digits (n + 1)) (ξ / A.scale (n + 1)) *
          Fourier.fourierIntegral Real.fourierChar (tailData A (n + 2)).measure
            (fun _ ↦ (1 : ℂ)) (ξ / A.scale (n + 1)) := by
  have h := fourier_eq_prod_mul_tail (tailData A (n + 1)) 1 (ξ / A.scale n)
  rw [tailData_tail] at h
  simpa [tailData, Data.scale, Finset.prod_range_succ, div_mul_eq_div_div] using h

private lemma half_le_norm_fourier_tail (A : Data) (L : ℕ → ℤ)
    (hL : ∀ n, 2 * |L n| ≤ (A.base n : ℤ) - 1) (n : ℕ)
    (hbase : 16 ≤ A.base (n + 1)) :
    (1 / 2 : ℝ) ≤ ‖Fourier.fourierIntegral Real.fourierChar (tailData A (n + 2)).measure
      (fun _ ↦ (1 : ℂ)) ((finiteFrequency A L (n + 1) : ℝ) / A.scale (n + 1))‖ := by
  have habs := abs_div_scale_succ_le A n hbase (abs_finiteFrequency_div_scale_lt A L hL n)
  have hfourier := one_sub_four_pi_mul_abs_le_norm_fourier (tailData A (n + 2))
    ((finiteFrequency A L (n + 1) : ℝ) / A.scale (n + 1))
  nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four
    (abs_nonneg ((finiteFrequency A L (n + 1) : ℝ) / A.scale (n + 1)))]

private lemma le_norm_fourier_tail_of_mask (A : Data) (L : ℕ → ℤ)
    (hL : ∀ n, 2 * |L n| ≤ (A.base n : ℤ) - 1) (n : ℕ)
    (hbase : 16 ≤ A.base (n + 1)) {η : ℝ}
    (hmask : η ≤ ‖mask (A.digits (n + 1))
      ((finiteFrequency A L (n + 1) : ℝ) / A.scale (n + 1))‖) :
    η / 2 ≤ ‖Fourier.fourierIntegral Real.fourierChar (tailData A (n + 1)).measure
      (fun _ ↦ (1 : ℂ)) ((finiteFrequency A L (n + 1) : ℝ) / A.scale n)‖ := by
  rw [fourier_tail_eq_mask_mul, norm_mul]
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul hmask
    (half_le_norm_fourier_tail A L hL n hbase) (by norm_num) (norm_nonneg _)

private lemma one_div_two_pi_le_norm_fourier_tail (A : Data) (L : ℕ → ℤ)
    (hL : ∀ n, 2 * |L n| ≤ (A.base n : ℤ) - 1) (n : ℕ)
    (hbase : 16 ≤ A.base (n + 1))
    (herror : ∀ ξ : ℝ, ‖mask (A.digits (n + 1)) ξ -
      mask (Finset.range (A.base (n + 1))) ξ‖ ≤ 1 / Real.pi) :
    1 / (2 * Real.pi) ≤
      ‖Fourier.fourierIntegral Real.fourierChar (tailData A (n + 1)).measure
        (fun _ ↦ (1 : ℂ)) ((finiteFrequency A L (n + 1) : ℝ) / A.scale n)‖ := by
  have hmask := two_div_pi_sub_le_norm_mask (A.digits (n + 1))
    (lt_of_lt_of_le Nat.zero_lt_two (A.two_le_base (n + 1)))
    (abs_finiteFrequency_div_scale_lt A L hL n).le (herror _)
  have hmask' : 1 / Real.pi ≤ ‖mask (A.digits (n + 1))
      ((finiteFrequency A L (n + 1) : ℝ) / A.scale (n + 1))‖ := by
    rw [← sub_div, show (2 : ℝ) - 1 = 1 by norm_num] at hmask
    simpa [Data.scale, Finset.prod_range_succ, div_mul_eq_div_div] using hmask
  simpa only [div_div, mul_comm Real.pi] using
    le_norm_fourier_tail_of_mask A L hL n hbase hmask'

private lemma mask_add_int (B : Finset ℕ) (ξ : ℝ) (z : ℤ) :
    mask B (ξ + z) = mask B ξ := by
  refine congrArg ((B.card : ℂ)⁻¹ * ·) (Finset.sum_congr rfl (fun d _ ↦ ?_))
  have heq : ((-2 * Real.pi * d * (ξ + z) : ℝ) : ℂ) * Complex.I =
      ((-2 * Real.pi * d * ξ : ℝ) : ℂ) * Complex.I +
        ((-(d : ℤ) * z : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma exp_powerFrequency_sub_eq_char {p r m : ℕ} [NeZero p]
    (d : ℕ) (k l : ZMod (p ^ r)) :
    Complex.exp ((-2 * Real.pi * d *
      ((powerFrequency p r m k - powerFrequency p r m l : ℤ) : ℝ) /
        (p ^ (r + m) : ℕ) : ℝ) * Complex.I) =
      ZMod.stdAddChar ((d : ZMod (p ^ r)) * (l - k)) := by
  have h := ZMod.stdAddChar_coe (N := p ^ r) ((d : ℤ) * (l.valMinAbs - k.valMinAbs))
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, ZMod.coe_valMinAbs] at h
  rw [h]
  congr 1
  simp only [powerFrequency]
  push_cast
  field_simp [pow_add, NeZero.ne p]
  simp only [pow_add]
  ring

private lemma mask_powerFrequency_sub_eq_zero {p r m : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r)
    {k l : ZMod (p ^ r)} (hkl : k ≠ l) :
    mask (powerDigitSet b hr m)
      ((powerFrequency p r m k - powerFrequency p r m l : ℤ) / (p ^ (r + m) : ℕ)) = 0 := by
  simp only [mask, powerDigitSet, Finset.sum_image
    (fun _ _ _ _ h ↦ powerDigit_injective b hr m h), ← mul_div_assoc,
    exp_powerFrequency_sub_eq_char, powerDigit_orthogonality, if_neg hkl.symm,
    Nat.cast_zero, mul_zero]

private lemma finiteFrequency_sub_eq_sum_erase (A : Data) (L M : ℕ → ℤ)
    {j n : ℕ} (hj : j < n) :
    finiteFrequency A L n - finiteFrequency A M n -
      (∏ i ∈ Finset.range j, A.base i : ℕ) * (L j - M j) =
        ∑ i ∈ (Finset.range n).erase j,
          (∏ k ∈ Finset.range i, A.base k : ℕ) * (L i - M i) := by
  simp only [finiteFrequency, ← Finset.sum_sub_distrib, ← mul_sub]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hj), add_sub_cancel_right]

private lemma scale_dvd_finiteFrequency_sub (A : Data) (L M : ℕ → ℤ)
    {j n : ℕ} (hj : j < n) (hLM : ∀ i, i < j → L i = M i) :
    (A.scale j : ℤ) ∣ finiteFrequency A L n - finiteFrequency A M n -
      (∏ i ∈ Finset.range j, A.base i : ℕ) * (L j - M j) := by
  rw [finiteFrequency_sub_eq_sum_erase A L M hj]
  refine Finset.dvd_sum (fun i hi ↦ ?_)
  rcases lt_or_gt_of_ne (Finset.mem_erase.mp hi).1 with hij | hji
  · simp [hLM i hij]
  · apply dvd_mul_of_dvd_left
    exact_mod_cast Finset.prod_dvd_prod_of_subset _ _ A.base (Finset.range_mono hji)

private lemma mask_finiteFrequency_sub_eq (A : Data) (L M : ℕ → ℤ)
    {j n : ℕ} (hj : j < n) (hLM : ∀ i, i < j → L i = M i) :
    mask (A.digits j)
      (((finiteFrequency A L n - finiteFrequency A M n : ℤ) : ℝ) / A.scale j) =
        mask (A.digits j) (((L j - M j : ℤ) : ℝ) / A.base j) := by
  obtain ⟨z, hz⟩ := scale_dvd_finiteFrequency_sub A L M hj hLM
  rw [← mask_add_int _ (((L j - M j : ℤ) : ℝ) / A.base j) z]
  congr 1
  have hz' := congrArg (fun t : ℤ ↦ (t : ℝ)) hz
  simp only [Data.scale, Finset.prod_range_succ, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Nat.cast_mul] at hz' ⊢
  field_simp [(A.prefix_product_pos j).ne',
    (lt_of_lt_of_le Nat.zero_lt_two (A.two_le_base j)).ne']
  apply (div_eq_iff (by exact_mod_cast (A.prefix_product_pos j).ne')).mpr
  linarith

private lemma fourier_finiteFrequency_sub_eq_zero (A : Data) (L M : ℕ → ℤ)
    {j n : ℕ} (hj : j < n) (hLM : ∀ i, i < j → L i = M i)
    (hz : mask (A.digits j) (((L j - M j : ℤ) : ℝ) / A.base j) = 0) :
    Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ))
      (finiteFrequency A L n - finiteFrequency A M n : ℤ) = 0 := by
  exact (A.hasProd_mask _).unique (hasProd_zero_of_exists_eq_zero
    ⟨j, (mask_finiteFrequency_sub_eq A L M hj hLM).trans hz⟩)

private lemma fourier_sub_eq_zero_of_digit_masks (A : Data) (L M : ℕ → ℤ) (n : ℕ)
    (hfreq : finiteFrequency A L n ≠ finiteFrequency A M n)
    (hzero : ∀ j, j < n → L j ≠ M j →
      mask (A.digits j) (((L j - M j : ℤ) : ℝ) / A.base j) = 0) :
    Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ))
      (finiteFrequency A L n - finiteFrequency A M n : ℤ) = 0 := by
  have hex : ∃ j, j < n ∧ L j ≠ M j := by
    by_contra! h
    exact hfreq (Finset.sum_congr rfl (fun j hj ↦
      congrArg (_ * ·) (h j (Finset.mem_range.mp hj))))
  have hj := Nat.find_spec hex
  refine fourier_finiteFrequency_sub_eq_zero A L M hj.1 (fun i hi ↦ ?_)
    (hzero _ hj.1 hj.2)
  exact not_ne_iff.mp (fun h ↦ Nat.find_min hex hi ⟨hi.trans hj.1, h⟩)

private lemma galoisPowerMoranData_mask_zero (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) (n : ℕ) {k l : ZMod (p n ^ r n)} (hkl : k ≠ l) :
    let A := galoisPowerMoranData p r m hr
    mask (A.digits n)
      (((powerFrequency (p n) (r n) (m n) k - powerFrequency (p n) (r n) (m n) l : ℤ) : ℝ) /
        A.base n) = 0 := by
  letI : Fintype (GaloisField (p n) (r n)) := Fintype.ofFinite _
  exact mask_powerFrequency_sub_eq_zero
    (galoisPowerBasis (p n) (r n) (hr n)) (hr n) hkl

private lemma finiteFrequency_eq_of_zero_tail (A : Data) (L : ℕ → ℤ) {n N : ℕ}
    (hnN : n ≤ N) (hL : ∀ i, n ≤ i → L i = 0) :
    finiteFrequency A L N = finiteFrequency A L n := by
  exact (Finset.sum_subset (Finset.range_mono hnN) (fun i _ hi ↦ by
    simp [hL i (by simpa only [Finset.mem_range, not_lt] using hi)])).symm

private def galoisPowerSpectrum (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) : Set ℝ :=
  {ξ | ∃ L : ℕ → ℤ, (∀ j, ∃ k : ZMod (p j ^ r j), L j = powerFrequency (p j) (r j) (m j) k) ∧
    ∃ n, (∀ j, n ≤ j → L j = 0) ∧ ξ = finiteFrequency (galoisPowerMoranData p r m hr) L n}

private lemma finiteFrequency_mem_galoisPowerSpectrum (p r m : ℕ → ℕ)
    [∀ n, Fact (p n).Prime] (hr : ∀ n, 0 < r n)
    (k : ∀ j, ZMod (p j ^ r j)) (n : ℕ) :
    (finiteFrequency (galoisPowerMoranData p r m hr)
      (fun j ↦ powerFrequency (p j) (r j) (m j) (k j)) n : ℝ) ∈
        galoisPowerSpectrum p r m hr := by
  refine ⟨fun j ↦ if j < n then powerFrequency (p j) (r j) (m j) (k j) else 0, ?_, n, ?_, ?_⟩
  · intro j
    by_cases hj : j < n
    · exact ⟨k j, if_pos hj⟩
    · exact ⟨0, by simp [hj, powerFrequency]⟩
  · exact fun j hj ↦ if_neg (not_lt.mpr hj)
  · exact congrArg (fun z : ℤ ↦ (z : ℝ)) (Finset.sum_congr rfl (fun j hj ↦ by
      simp only [if_pos (Finset.mem_range.mp hj)]))

private lemma galoisPowerMoranData_fourier_sub_eq_zero (p r m : ℕ → ℕ)
    [∀ n, Fact (p n).Prime] (hr : ∀ n, 0 < r n) {ξ η : ℝ}
    (hξ : ξ ∈ galoisPowerSpectrum p r m hr) (hη : η ∈ galoisPowerSpectrum p r m hr)
    (hξη : ξ ≠ η) :
    Fourier.fourierIntegral Real.fourierChar (galoisPowerMoranData p r m hr).measure
      (fun _ ↦ (1 : ℂ)) (ξ - η) = 0 := by
  rcases hξ with ⟨L, hL, n, hn, rfl⟩
  rcases hη with ⟨M, hM, N, hN, rfl⟩
  rw [← finiteFrequency_eq_of_zero_tail _ L (le_max_left n N) hn,
    ← finiteFrequency_eq_of_zero_tail _ M (le_max_right n N) hN] at hξη ⊢
  rw [← Int.cast_sub]
  refine fourier_sub_eq_zero_of_digit_masks _ L M (max n N)
    (fun h ↦ hξη (congrArg (fun z : ℤ ↦ (z : ℝ)) h)) (fun j _ hj ↦ ?_)
  obtain ⟨k, hk⟩ := hL j
  obtain ⟨l, hl⟩ := hM j
  rw [hk, hl] at hj ⊢
  exact galoisPowerMoranData_mask_zero p r m hr j (fun h ↦ hj (congrArg _ h))

private def spectralVector (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) : Lp ℂ 2 μ :=
  BoundedContinuousFunction.toLp 2 μ ℂ
    (BoundedContinuousFunction.innerProbChar (2 * Real.pi * ξ))

private lemma spectralVector_ae_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    ∀ᵐ x ∂μ, spectralVector μ ξ x =
      Complex.exp ((2 * Real.pi * ξ * x : ℝ) * Complex.I) := by
  filter_upwards [(BoundedContinuousFunction.innerProbChar (2 * Real.pi * ξ)).coeFn_toLp
    2 μ ℂ] with x hx
  simpa [spectralVector, BoundedContinuousFunction.innerProbChar_apply,
    mul_comm, mul_left_comm, mul_assoc] using hx

private lemma spectralVector_inner (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ η : ℝ) :
    inner ℂ (spectralVector μ ξ) (spectralVector μ η) =
      Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) (ξ - η) := by
  rw [spectralVector, spectralVector, BoundedContinuousFunction.inner_toLp,
    fourierIntegral_one_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ ?_))
  simp only [BoundedContinuousFunction.innerProbChar_apply,
    RCLike.inner_apply, conj_trivial, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma galoisPowerSpectrum_orthonormal (p r m : ℕ → ℕ)
    [∀ n, Fact (p n).Prime] (hr : ∀ n, 0 < r n) :
    Orthonormal ℂ (fun ξ : galoisPowerSpectrum p r m hr ↦
      spectralVector (galoisPowerMoranData p r m hr).measure ξ) := by
  refine orthonormal_iff_ite.mpr (fun ξ η ↦ ?_)
  rw [spectralVector_inner]
  split_ifs with h
  · simp [h, fourierIntegral_one_eq]
  · exact galoisPowerMoranData_fourier_sub_eq_zero p r m hr ξ.property η.property
      (fun hξη ↦ h (Subtype.ext hξη))

private lemma prod_masks_eq_finite_sum (A : Data) (n : ℕ) (ξ : ℝ) :
    (∏ j : Fin n, mask (A.digits j) (ξ / A.scale j)) =
      (Fintype.card (∀ j : Fin n, A.digits j) : ℂ)⁻¹ *
        ∑ d : (∀ j : Fin n, A.digits j), Complex.exp
          ((-2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) *
            Complex.I) := by
  simp only [mask, Finset.prod_mul_distrib, ← Finset.prod_inv_distrib,
    Fintype.card_pi, Nat.cast_prod, Fintype.card_coe]
  congr 1
  conv_lhs => enter [2, j]; rw [← Finset.sum_coe_sort (A.digits j)]
  simp only [Fintype.prod_sum, ← Complex.exp_sum]
  refine Finset.sum_congr rfl fun d _ ↦ congrArg Complex.exp ?_
  simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ by congr 2; ring

private lemma normalized_exp_inner (c x y : ℝ) :
    inner ℂ ((c : ℂ)⁻¹ * Complex.exp (x * Complex.I))
      ((c : ℂ)⁻¹ * Complex.exp (y * Complex.I)) =
        ((c : ℂ)⁻¹) ^ 2 * Complex.exp ((y - x : ℝ) * Complex.I) := by
  simp only [RCLike.inner_apply, map_mul, map_inv₀, Complex.conj_ofReal,
    ← Complex.exp_conj, Complex.conj_I, Complex.ofReal_sub]
  rw [sub_mul, Complex.exp_sub, mul_neg, Complex.exp_neg]
  ring

private def finiteFourierVector (A : Data) (n : ℕ) (ξ : ℝ) :
    EuclideanSpace ℂ (∀ j : Fin n, A.digits j) :=
  WithLp.toLp 2 fun d ↦ (Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
    Complex.exp ((2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) *
      Complex.I)

private lemma finiteFourierVector_inner (A : Data) (n : ℕ) (ξ η : ℝ) :
    inner ℂ (finiteFourierVector A n ξ) (finiteFourierVector A n η) =
      ∏ j : Fin n, mask (A.digits j) ((ξ - η) / A.scale j) := by
  simp only [PiLp.inner_apply, finiteFourierVector, normalized_exp_inner,
    ← Finset.mul_sum, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    prod_masks_eq_finite_sum, Complex.ofReal_natCast]
  exact congrArg (_ * ·) (Finset.sum_congr rfl fun _ _ ↦ by congr 3; ring)

private lemma prod_masks_finiteFrequency_sub_eq_zero (A : Data) (L M : ℕ → ℤ) (n : ℕ)
    (hex : ∃ j, j < n ∧ L j ≠ M j)
    (hzero : ∀ j, j < n → L j ≠ M j →
      mask (A.digits j) (((L j - M j : ℤ) : ℝ) / A.base j) = 0) :
    (∏ j : Fin n, mask (A.digits j)
      (((finiteFrequency A L n - finiteFrequency A M n : ℤ) : ℝ) / A.scale j)) = 0 := by
  have hj := Nat.find_spec hex
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨Nat.find hex, hj.1⟩ : Fin n))
  exact (mask_finiteFrequency_sub_eq A L M hj.1 (fun i hi ↦
    not_ne_iff.mp (fun h ↦ Nat.find_min hex hi ⟨hi.trans hj.1, h⟩))).trans
      (hzero _ hj.1 hj.2)

private lemma powerFrequency_injective {p r m : ℕ} [NeZero p] :
    Function.Injective (powerFrequency p r m) := by
  intro k l hkl
  exact ZMod.injective_valMinAbs ((mul_left_cancel₀
    (by exact_mod_cast pow_ne_zero m (NeZero.ne p))) hkl)

private def finitePowerChoice (p r m : ℕ → ℕ) {n : ℕ}
    (k : ∀ j : Fin n, ZMod (p j ^ r j)) (j : ℕ) : ℤ :=
  powerFrequency (p j) (r j) (m j) (if hj : j < n then k ⟨j, hj⟩ else 0)

private lemma finitePowerChoice_different (p r m : ℕ → ℕ) [∀ j, NeZero (p j)] {n : ℕ}
    {k l : ∀ j : Fin n, ZMod (p j ^ r j)} (hkl : k ≠ l) :
    ∃ j, j < n ∧ finitePowerChoice p r m k j ≠ finitePowerChoice p r m l j := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hkl
  exact ⟨j, j.isLt, by simpa only [finitePowerChoice, dif_pos j.isLt] using
    (powerFrequency_injective (p := p j) (r := r j) (m := m j)).ne hj⟩

private lemma finitePowerFourier_orthonormal (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) :
    let A := galoisPowerMoranData p r m hr
    Orthonormal ℂ (fun k : (∀ j : Fin n, ZMod (p j ^ r j)) ↦
      finiteFourierVector A n (finiteFrequency A (finitePowerChoice p r m k) n)) := by
  classical
  refine orthonormal_iff_ite.mpr fun k l ↦ ?_
  rw [finiteFourierVector_inner, ← Int.cast_sub]
  split_ifs with hkl
  · simp [hkl, mask, galoisPowerMoranData_card_digits, NeZero.ne (p _)]
  · refine prod_masks_finiteFrequency_sub_eq_zero _ _ _ n
      (finitePowerChoice_different p r m hkl) fun j hj hdiff ↦ ?_
    simp only [finitePowerChoice, dif_pos hj] at hdiff ⊢
    exact galoisPowerMoranData_mask_zero p r m hr j (fun h ↦ hdiff (congrArg _ h))

private def finitePowerFourierBasis (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) :
    OrthonormalBasis (∀ j : Fin n, ZMod (p j ^ r j)) ℂ
      (EuclideanSpace ℂ (∀ j : Fin n, (galoisPowerMoranData p r m hr).digits j)) :=
  (basisOfOrthonormalOfCardEqFinrank (finitePowerFourier_orthonormal p r m hr n)
    (by simp only [finrank_euclideanSpace, Fintype.card_pi, Fintype.card_coe,
      galoisPowerMoranData_card_digits, ZMod.card])).toOrthonormalBasis
    (by simpa only [coe_basisOfOrthonormalOfCardEqFinrank] using
      finitePowerFourier_orthonormal p r m hr n)

private lemma finiteFourierVector_coefficient (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    inner ℂ (finiteFourierVector A n ξ) (WithLp.toLp 2 w) =
      (Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
        ∑ d, w d * Complex.exp
          ((-2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) *
            Complex.I) := by
  simp only [PiLp.inner_apply, finiteFourierVector, RCLike.inner_apply, map_mul,
    map_inv₀, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, mul_neg, neg_mul]
  conv_rhs => rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

private lemma finitePowerFourier_parseval (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ)
    (w : (∀ j : Fin n, (galoisPowerMoranData p r m hr).digits j) → ℂ) :
    let A := galoisPowerMoranData p r m hr
    (∑ k : (∀ j : Fin n, ZMod (p j ^ r j)),
      ‖(Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
        ∑ d, w d * Complex.exp
          ((-2 * Real.pi * finiteFrequency A (finitePowerChoice p r m k) n *
            (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) * Complex.I)‖ ^ 2) =
      ∑ d, ‖w d‖ ^ 2 := by
  have h := (finitePowerFourierBasis p r m hr n).sum_sq_norm_inner_right (WithLp.toLp 2 w)
  simpa only [finitePowerFourierBasis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank, finiteFourierVector_coefficient,
    PiLp.norm_sq_eq_of_L2] using h

private lemma finitePowerFrequency_injective (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) :
    Function.Injective (fun k : (∀ j : Fin n, ZMod (p j ^ r j)) ↦
      finiteFrequency (galoisPowerMoranData p r m hr) (finitePowerChoice p r m k) n) := by
  intro k l hkl
  exact (finitePowerFourier_orthonormal p r m hr n).linearIndependent.injective
    (congrArg (fun ξ : ℤ ↦ finiteFourierVector (galoisPowerMoranData p r m hr) n ξ) hkl)

private def finitePowerSpectrumEmbedding (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) :
    (∀ j : Fin n, ZMod (p j ^ r j)) ↪ galoisPowerSpectrum p r m hr where
  toFun k := ⟨finiteFrequency (galoisPowerMoranData p r m hr) (finitePowerChoice p r m k) n,
    finiteFrequency_mem_galoisPowerSpectrum p r m hr
      (fun j ↦ if hj : j < n then k ⟨j, hj⟩ else 0) n⟩
  inj' := by
    intro k l hkl
    exact finitePowerFrequency_injective p r m hr n
      (Int.cast_injective (α := ℝ) (congrArg Subtype.val hkl))

private lemma two_mul_abs_le_abs_sin_pi {x : ℝ} (hx : |x| ≤ 1 / 2) :
    2 * |x| ≤ |Real.sin (Real.pi * x)| := by
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    simpa only [abs_mul, abs_of_pos Real.pi_pos, mul_one_div] using
      mul_le_mul_of_nonneg_left hx Real.pi_pos.le
  simpa [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc] using Real.mul_abs_le_abs_sin harg

private lemma scaled_sine_lower {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : 0 ≤ t) (htN : t ≤ N / 2) :
    2 * t ≤ N * |Real.sin (Real.pi * (t / N))| := by
  have harg : |t / N| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    linarith
  simpa only [abs_of_nonneg (show 0 ≤ t / N by positivity), mul_assoc,
    div_mul_cancel₀ _ (show (N : ℝ) ≠ 0 by positivity), mul_comm (N : ℝ)] using
    mul_le_mul_of_nonneg_right (two_mul_abs_le_abs_sin_pi harg) (Nat.cast_nonneg N)

private lemma norm_mask_range_scaled_mul_le_sin {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : 0 ≤ t) (htN : t ≤ N / 2) :
    ‖mask (Finset.range N) (t / N)‖ * (2 * t) ≤ |Real.sin (Real.pi * t)| := by
  have h := mul_le_mul_of_nonneg_left (scaled_sine_lower hN ht htN)
    (norm_nonneg (mask (Finset.range N) (t / N)))
  have heq := norm_mask_range_mul_sin hN.ne' (t / N)
  simp only [mul_div_cancel₀ _ (show (N : ℝ) ≠ 0 by positivity)] at heq
  nlinarith

private lemma norm_adjacent_mask_range_le {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) (htN : t ≤ N / 2) :
    ‖mask (Finset.range M) t * mask (Finset.range N) (t / N)‖ ≤ (2 * M * t)⁻¹ := by
  rw [norm_mul, ← one_div, le_div_iff₀ (by positivity)]
  have h := mul_le_mul_of_nonneg_left (norm_mask_range_scaled_mul_le_sin hN ht.le htN)
    (show 0 ≤ M * ‖mask (Finset.range M) t‖ by positivity)
  nlinarith [norm_mask_range_mul_sin hM.ne' t, Real.abs_sin_le_one (Real.pi * (M * t))]

private lemma norm_mask_range_scaled_le {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) (htN : t ≤ N / 2) :
    ‖mask (Finset.range N) (t / N)‖ ≤ (2 * t)⁻¹ := by
  simpa [mask] using norm_adjacent_mask_range_le (M := 1) zero_lt_one hN ht htN

private lemma norm_mul_le_of_approximations {u v a b : ℂ} {ε δ : ℝ}
    (hu : ‖u‖ ≤ 1) (hua : ‖u - a‖ ≤ ε) (hvb : ‖v - b‖ ≤ δ) :
    ‖u * v‖ ≤ ‖a * b‖ + ε * ‖b‖ + δ := by
  have h := norm_add₃_le (a := a * b) (b := (u - a) * b) (c := u * (v - b))
  rw [show a * b + (u - a) * b + u * (v - b) = u * v by ring,
    norm_mul (u - a) b, norm_mul u (v - b)] at h
  nlinarith [mul_le_mul_of_nonneg_right hua (norm_nonneg b),
    mul_le_mul_of_nonneg_right hu (norm_nonneg (v - b))]

private lemma norm_adjacent_masks_le (B C : Finset ℕ) (hB : B.Nonempty)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) {ε δ t : ℝ}
    (ht : 0 < t) (htN : t ≤ N / 2)
    (hε : ‖mask B t - mask (Finset.range M) t‖ ≤ ε)
    (hδ : ‖mask C (t / N) - mask (Finset.range N) (t / N)‖ ≤ δ) :
    ‖mask B t * mask C (t / N)‖ ≤ ((M : ℝ)⁻¹ + ε) / (2 * t) + δ := by
  refine (norm_mul_le_of_approximations (norm_mask_le_one B hB t) hε hδ).trans ?_
  have hbound := add_le_add_right (add_le_add (norm_adjacent_mask_range_le hM hN ht htN)
    (mul_le_mul_of_nonneg_left (norm_mask_range_scaled_le hN ht htN)
      ((norm_nonneg _).trans hε))) δ
  simpa only [mul_inv_rev, div_eq_mul_inv, add_mul, mul_add, mul_comm, mul_assoc,
    mul_left_comm, add_comm] using hbound

private lemma norm_fourier_le_prod_masks (A : Data) (ξ : ℝ) (s : Finset ℕ) :
    ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
      ∏ j ∈ s, ‖mask (A.digits j) (ξ / A.scale j)‖ := by
  apply le_of_tendsto (A.hasProd_mask ξ).norm
  filter_upwards [eventually_ge_atTop s] with t ht
  simpa only [norm_prod] using Finset.prod_le_prod_of_subset_of_le_one ht
    (fun j _ ↦ norm_nonneg _) (fun j _ _ ↦ norm_mask_le_one _ (A.digits_nonempty j) _)

private lemma norm_fourier_le_adjacent_masks (A : Data) (ξ : ℝ) (n : ℕ) :
    ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
      ‖mask (A.digits n) (ξ / A.scale n) *
        mask (A.digits (n + 1)) ((ξ / A.scale n) / A.base (n + 1))‖ := by
  simpa [norm_mul, Data.scale, Finset.prod_range_succ, div_mul_eq_div_div] using
    norm_fourier_le_prod_masks A ξ {n, n + 1}

private lemma mul_rpow_le_rpow_of_separation {P N a b : ℝ} {k : ℕ}
    (hP : 1 ≤ P) (hN : 0 < N) (hsep : P ^ k ≤ N)
    (hab : 0 ≤ b - a) (hmargin : a ≤ k * (b - a)) :
    (P * N) ^ a ≤ N ^ b := by
  have h : P ^ a ≤ N ^ (b - a) :=
    (Real.rpow_le_rpow_of_exponent_le hP hmargin).trans
      (by simpa only [Real.rpow_natCast_mul (by linarith : 0 ≤ P)] using
        Real.rpow_le_rpow (by positivity : 0 ≤ P ^ k) hsep hab)
  simpa only [Real.mul_rpow (by linarith : 0 ≤ P) hN.le, ← Real.rpow_add hN,
    sub_add_cancel] using mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hN.le a)

private lemma scale_rpow_div_le {P x a : ℝ} (hP : 0 < P) (hx : 0 < x)
    (hPx : P ≤ 2 * x) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    P ^ (-a) / (x / P) ≤ 2 * x ^ (-a) := by
  rw [div_div_eq_mul_div, div_le_iff₀ hx, mul_assoc, ← Real.rpow_add_one hP.ne',
    ← Real.rpow_add_one hx.ne']
  refine (Real.rpow_le_rpow hP.le hPx (by linarith : 0 ≤ -a + 1)).trans ?_
  rw [Real.mul_rpow (by norm_num) hx.le]
  exact mul_le_mul_of_nonneg_right
    (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (by linarith : -a + 1 ≤ 1))
    (Real.rpow_nonneg hx.le _)

private lemma block_bound_le_rpow {P Q x a u v w : ℝ} (hP : 0 < P) (hx : 0 < x)
    (hPx : P ≤ 2 * x) (hxQ : x ≤ Q) (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (huv : u ≤ v) (hv : v ≤ P ^ (-a)) (hw : w ≤ Q ^ (-a)) :
    (u + v) / (2 * (x / P)) + w ≤ 3 * x ^ (-a) := by
  have hnum : u + v ≤ 2 * P ^ (-a) := by linarith
  have hfirst := div_le_div_of_nonneg_right hnum (show 0 ≤ 2 * (x / P) by positivity)
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] at hfirst
  linarith [scale_rpow_div_le hP hx hPx ha ha₁,
    Real.rpow_le_rpow_of_nonpos hx hxQ (neg_nonpos.mpr ha)]

private lemma exists_scale_block (A : Data) (N : ℕ) {ξ : ℝ} (hNξ : A.scale N ≤ ξ) :
    ∃ n : ℕ, N ≤ n ∧ A.scale n ≤ ξ ∧ ξ ≤ A.scale (n + 1) := by
  have hlim : Tendsto (fun j : ℕ ↦ (A.scale (N + j + 1) : ℝ)) atTop atTop := by
    simpa [Data.scale, Function.comp_def, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      (tendsto_prefix_product_atTop A).comp (tendsto_add_atTop_nat (N + 2))
  have hex : ∃ j : ℕ, ξ ≤ A.scale (N + j + 1) := (hlim.eventually_ge_atTop ξ).exists
  refine ⟨N + Nat.find hex, Nat.le_add_right _ _, ?_, Nat.find_spec hex⟩
  cases hj : Nat.find hex with
  | zero => simpa only [hj, Nat.add_zero] using hNξ
  | succ j =>
    simpa only [Nat.add_assoc] using
      (lt_of_not_ge (Nat.find_min hex (by omega : j < Nat.find hex))).le

private lemma norm_fourier_neg (μ : Measure ℝ) (ξ : ℝ) :
    ‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) (-ξ)‖ =
      ‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ‖ := by
  have h := congrArg norm (charFun_neg (μ := μ) (-2 * Real.pi * ξ))
  simpa only [fourierIntegral_one_eq, charFun_apply_real, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.norm_conj, mul_neg, neg_mul, neg_neg] using h

private lemma decay_weight_le {x a : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    3 * x ^ (-a) * (1 + x) ^ a ≤ 6 := by
  have hpow : (1 + x) ^ a ≤ (2 * x) ^ a :=
    Real.rpow_le_rpow (by linarith) (by linarith) ha
  have htwo : (2 : ℝ) ^ a ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha₁
  have heq : 3 * x ^ (-a) * (2 * x) ^ a = 3 * 2 ^ a := by
    rw [Real.mul_rpow (by norm_num) (by linarith), Real.rpow_neg (by linarith)]
    field_simp [(Real.rpow_pos_of_pos (by linarith : 0 < x) a).ne']
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans
    (heq.le.trans (by linarith))

private lemma exists_weighted_bound_of_eventual_decay {f : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) (hf : ∀ x, f x ≤ 1)
    (hdecay : ∀ᶠ x in atTop, f x ≤ 3 * x ^ (-a)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, 0 ≤ x → f x * (1 + x) ^ a ≤ C := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp hdecay
  refine ⟨7 + max R 1, by have := le_max_right R 1; linarith, fun x hx ↦ ?_⟩
  by_cases hlarge : max R 1 ≤ x
  · exact (mul_le_mul_of_nonneg_right (hR x ((le_max_left R 1).trans hlarge))
      (by positivity)).trans ((decay_weight_le ((le_max_right R 1).trans hlarge)
        ha ha₁).trans (by have := le_max_right R 1; linarith))
  · calc
      f x * (1 + x) ^ a ≤ 1 * (1 + x) ^ a :=
        mul_le_mul_of_nonneg_right (hf x) (by positivity)
      _ ≤ 1 + x := by simpa using Real.rpow_le_self_of_one_le (by linarith) ha₁
      _ ≤ 7 + max R 1 := by linarith

/-- The Fourier dimension of a finite Borel measure on the real line. -/
def fourierDim (μ : Measure ℝ) [IsFiniteMeasure μ] : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc 0 1 ∧
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        C * Real.rpow (1 + |ξ|) (-t / 2)}

private lemma fourier_decay_bddAbove (μ : Measure ℝ) [IsFiniteMeasure μ] :
    BddAbove {t : ℝ | t ∈ Set.Icc 0 1 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
        ‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ‖ ≤
          C * Real.rpow (1 + |ξ|) (-t / 2)} := by
  exact ⟨1, fun _ ht ↦ ht.1.2⟩

private lemma zero_mem_fourier_decay (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (0 : ℝ) ∈ {t : ℝ | t ∈ Set.Icc 0 1 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
        ‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ‖ ≤
          C * Real.rpow (1 + |ξ|) (-t / 2)} := by
  refine ⟨⟨le_rfl, zero_le_one⟩, 1, zero_lt_one, ?_⟩
  intro ξ
  simpa using Fourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ

private lemma fourierDim_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ fourierDim μ := by
  exact le_csSup (fourier_decay_bddAbove μ) (zero_mem_fourier_decay μ)

private lemma fourierDim_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    fourierDim μ ≤ 1 := by
  exact csSup_le ⟨0, zero_mem_fourier_decay μ⟩ (fun _ ht ↦ ht.1.2)

private lemma le_fourierDim_of_decay (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : s ≤ 1)
    (hdecay : ∀ t : ℝ, 0 < t → t < s → ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        C * Real.rpow (1 + |ξ|) (-t / 2)) : s ≤ fourierDim μ := by
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  by_cases hpos : 0 < t
  · exact le_csSup (fourier_decay_bddAbove μ)
      ⟨⟨hpos.le, ht.le.trans hs⟩, hdecay t hpos ht⟩
  · exact (le_of_not_gt hpos).trans (fourierDim_nonneg μ)

private lemma exists_fourier_decay_of_lt_fourierDim
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht : t < fourierDim μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        C * Real.rpow (1 + |ξ|) (-t / 2) := by
  obtain ⟨u, hu, htu⟩ := (lt_csSup_iff (fourier_decay_bddAbove μ)
    ⟨0, zero_mem_fourier_decay μ⟩).mp ht
  obtain ⟨C, hC, hdecay⟩ := hu.2
  refine ⟨C, hC, fun ξ ↦ (hdecay ξ).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg ξ]) (by linarith)) hC.le

/-- A spectral measure is a probability measure whose real-frequency exponentials
form a Hilbert basis of its `L²`. -/
def is_spectral (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ Λ : Set ℝ, ∃ b : HilbertBasis Λ ℂ (Lp ℂ 2 μ),
    ∀ ξ : Λ, ∀ᵐ x ∂μ,
      (b ξ : ℝ → ℂ) x =
        Complex.exp ((2 * Real.pi * (ξ : ℝ) * x : ℝ) * Complex.I)

private lemma eq_zero_of_dense_frame_bound {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {v : ι → E} (hv : Orthonormal ℂ v)
    {D : Set E} (hD : Dense D) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ f ∈ D, C * ‖f‖ ^ 2 ≤ ∑' i, ‖inner ℂ (v i) f‖ ^ 2)
    (f : E) (hf : ∀ i, inner ℂ (v i) f = 0) : f = 0 := by
  have htest : ∀ g ∈ D, C * ‖g‖ ^ 2 ≤ ‖g - f‖ ^ 2 := by
    intro g hg
    refine (hbound g hg).trans ?_
    simpa only [inner_sub_right, hf, sub_zero] using hv.tsum_inner_products_le (g - f)
  have hlim : C * ‖f‖ ^ 2 ≤ ‖f - f‖ ^ 2 :=
    hD.induction (P := fun g ↦ C * ‖g‖ ^ 2 ≤ ‖g - f‖ ^ 2) htest
      (isClosed_le (continuous_const.mul (continuous_norm.pow 2))
        ((continuous_id.sub continuous_const).norm.pow 2)) f
  have hzero : C * ‖f‖ ^ 2 = 0 :=
    le_antisymm (by simpa using hlim) (mul_nonneg hC.le (sq_nonneg _))
  simpa [hC.ne'] using hzero

private lemma orthogonal_eq_bot_of_dense_frame_bound {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {v : ι → E}
    (hv : Orthonormal ℂ v) {D : Set E} (hD : Dense D) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ f ∈ D, C * ‖f‖ ^ 2 ≤ ∑' i, ‖inner ℂ (v i) f‖ ^ 2) :
    (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ ?_
  refine eq_zero_of_dense_frame_bound hv hD hC hbound f fun i ↦ ?_
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self (f := v) i)) hf

private lemma frame_bound_of_finite_coefficients {E ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype κ]
    {v : ι → E} (hv : Orthonormal ℂ v) (e : κ ↪ ι) (f : E) (w z : κ → ℂ)
    (hw : ∑ k, ‖w k‖ ^ 2 = ‖f‖ ^ 2)
    (hcoeff : ∀ k, inner ℂ (v (e k)) f = z k * w k)
    {C : ℝ} (hz : ∀ k, C ≤ ‖z k‖ ^ 2) :
    C * ‖f‖ ^ 2 ≤ ∑' i, ‖inner ℂ (v i) f‖ ^ 2 := by
  have hfinite : C * ‖f‖ ^ 2 ≤ ∑ k, ‖inner ℂ (v (e k)) f‖ ^ 2 := by
    rw [← hw, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ ↦ by
      simpa only [hcoeff, norm_mul, mul_pow] using
        mul_le_mul_of_nonneg_right (hz k) (sq_nonneg ‖w k‖)
  refine hfinite.trans ?_
  simpa only [tsum_fintype, Function.comp_apply] using
    Summable.tsum_le_tsum_of_inj (f := fun k ↦ ‖inner ℂ (v (e k)) f‖ ^ 2)
      (g := fun i ↦ ‖inner ℂ (v i) f‖ ^ 2) e e.injective
      (fun _ _ ↦ sq_nonneg _) (fun _ ↦ le_rfl)
      ((hv.comp e e.injective).inner_products_summable f) (hv.inner_products_summable f)

private def admissiblePrefix (A : Data) (n : ℕ) (d : ℕ → ℕ) :
    ∀ j : Fin n, A.digits j := fun j ↦
  if h : d j ∈ A.digits j then ⟨d j, h⟩ else ⟨(A.digits_nonempty j).choose,
    (A.digits_nonempty j).choose_spec⟩

private lemma measurable_admissiblePrefix (A : Data) (n : ℕ) :
    Measurable (admissiblePrefix A n) := by
  apply measurable_pi_lambda
  intro j
  convert (measurable_of_countable (fun x : ℕ ↦ if h : x ∈ A.digits j then
      (⟨x, h⟩ : A.digits j) else ⟨(A.digits_nonempty j).choose,
        (A.digits_nonempty j).choose_spec⟩)).comp
      (@measurable_pi_apply ℕ (fun _ ↦ ℕ) _ (j : ℕ)) using 1
  rfl

private def productCylinderFunction (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) (d : ℕ → ℕ) : ℂ :=
  w (admissiblePrefix A n d)

private lemma measurable_productCylinderFunction (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    Measurable (productCylinderFunction A n w) := by
  exact (measurable_of_countable w).comp (measurable_admissiblePrefix A n)

private lemma memLp_productCylinderFunction (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    MemLp (productCylinderFunction A n w) 2 (Measure.infinitePi A.digitLaw) := by
  letI (j : ℕ) : IsProbabilityMeasure (A.digitLaw j) := A.isProbabilityMeasure_digitLaw j
  apply MemLp.of_bound (measurable_productCylinderFunction A n w).aestronglyMeasurable
    (∑ d, ‖w d‖)
  exact Filter.Eventually.of_forall fun d ↦ Finset.single_le_sum (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_univ (admissiblePrefix A n d))

private def productCylinderVector (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    Lp ℂ 2 (Measure.infinitePi A.digitLaw) :=
  (memLp_productCylinderFunction A n w).toLp (productCylinderFunction A n w)

private lemma digitLaw_singleton (A : Data) (n : ℕ) (d : A.digits n) :
    A.digitLaw n {(d : ℕ)} = ((A.digits n).card : ℝ≥0∞)⁻¹ := by
  simp [Data.digitLaw, d.property]

private def rangeEquivFin (n : ℕ) : (Finset.range n : Set ℕ) ≃ Fin n where
  toFun j := ⟨j, Finset.mem_range.mp j.property⟩
  invFun j := ⟨j, Finset.mem_range.mpr j.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma map_admissiblePrefix (A : Data) (n : ℕ) :
    (Measure.infinitePi A.digitLaw).map (admissiblePrefix A n) =
      (Fintype.card (∀ j : Fin n, A.digits j) : ℝ≥0∞)⁻¹ • Measure.count := by
  letI (j : ℕ) : IsProbabilityMeasure (A.digitLaw j) := A.isProbabilityMeasure_digitLaw j
  apply Measure.ext_of_singleton
  intro d
  rw [Measure.map_apply (measurable_admissiblePrefix A n) (MeasurableSet.singleton d)]
  let d' : (j : (Finset.range n : Set ℕ)) → ℕ := fun j ↦
    d ⟨j, Finset.mem_range.mp j.property⟩
  have heq : (Measure.infinitePi A.digitLaw) (admissiblePrefix A n ⁻¹' {d}) =
      (Measure.infinitePi A.digitLaw)
        (MeasureTheory.cylinder (Finset.range n) {d'}) := by
    apply measure_congr
    filter_upwards [A.ae_all_mem_digits] with x hx
    apply propext
    change admissiblePrefix A n x = d ↔ (Finset.range n).restrict x = d'
    constructor
    · intro h
      funext j
      simpa only [Finset.restrict_def, d', admissiblePrefix, dif_pos (hx j)] using
        congrArg Subtype.val (congrFun h ⟨j, Finset.mem_range.mp j.property⟩)
    · intro h
      funext j
      apply Subtype.ext
      simpa only [Finset.restrict_def, d', admissiblePrefix, dif_pos (hx j)] using
        congrFun h ⟨j, Finset.mem_range.mpr j.isLt⟩
  rw [heq, Measure.infinitePi_cylinder (μ := A.digitLaw) (s := Finset.range n)
    (S := {d'}) (MeasurableSet.singleton d')]
  rw [show ({d'} : Set ((j : (Finset.range n : Set ℕ)) → ℕ)) =
    Set.pi Set.univ (fun j ↦ {d' j}) by ext; simp only [Set.mem_singleton_iff,
      Set.mem_pi, Set.mem_univ, forall_const, funext_iff], Measure.pi_pi]
  simp only [d', digitLaw_singleton, Measure.smul_apply, Measure.count_singleton,
    smul_eq_mul, mul_one]
  have hinv : (∏ j : (Finset.range n : Set ℕ), ((A.digits j).card : ℝ≥0∞))⁻¹ =
      ∏ j : (Finset.range n : Set ℕ), ((A.digits j).card : ℝ≥0∞)⁻¹ := by
    apply ENNReal.prod_inv_distrib
    exact fun i _ j _ _ ↦ Or.inl (by
      exact_mod_cast Nat.ne_of_gt (A.digits_nonempty i).card_pos)
  calc
    _ = (∏ j : (Finset.range n : Set ℕ), ((A.digits j).card : ℝ≥0∞))⁻¹ := hinv.symm
    _ = _ := by
      congr 1
      rw [Fintype.card_pi]
      calc
        _ = ∏ j : Fin n, ((A.digits j).card : ℝ≥0∞) := by
          apply Fintype.prod_equiv (rangeEquivFin n)
          intro j
          rfl
        _ = _ := by
          simp only [Fintype.card_coe]
          exact_mod_cast rfl

private lemma integral_productCylinderFunction (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    ∫ d, productCylinderFunction A n w d ∂Measure.infinitePi A.digitLaw =
      (Fintype.card (∀ j : Fin n, A.digits j) : ℝ)⁻¹ * ∑ d, w d := by
  simp only [productCylinderFunction]
  rw [← integral_map (μ := Measure.infinitePi A.digitLaw)
    (measurable_admissiblePrefix A n).aemeasurable]
  · rw [map_admissiblePrefix]
    rw [integral_smul_measure]
    simp only [integral_count, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast]
  · exact (measurable_of_countable w).aestronglyMeasurable

private lemma norm_productCylinderVector_sq (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    ‖productCylinderVector A n w‖ ^ 2 =
      (Fintype.card (∀ j : Fin n, A.digits j) : ℝ)⁻¹ * ∑ d, ‖w d‖ ^ 2 := by
  apply Complex.ofReal_injective
  have hinner : inner ℂ (productCylinderVector A n w) (productCylinderVector A n w) =
      (‖productCylinderVector A n w‖ : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (productCylinderVector A n w)
  push_cast
  calc
    _ = inner ℂ (productCylinderVector A n w) (productCylinderVector A n w) := hinner.symm
    _ = ∫ a, inner ℂ ((productCylinderVector A n w : (ℕ → ℕ) → ℂ) a)
        ((productCylinderVector A n w : (ℕ → ℕ) → ℂ) a)
        ∂Measure.infinitePi A.digitLaw := MeasureTheory.L2.inner_def _ _
    _ = _ := by
      rw [integral_congr_ae ((memLp_productCylinderFunction A n w).coeFn_toLp.mono
        (fun d hd ↦ by rw [show (productCylinderVector A n w : (ℕ → ℕ) → ℂ) d =
          productCylinderFunction A n w d from hd]))]
      simp only [RCLike.inner_apply, Complex.mul_conj', productCylinderFunction]
      simpa only [productCylinderFunction, Complex.ofReal_pow, Complex.ofReal_inv,
        Complex.ofReal_natCast, Complex.ofReal_sum] using integral_productCylinderFunction A n
          (fun d ↦ (‖w d‖ ^ 2 : ℂ))

private lemma coding_measurePreserving (A : Data) :
    MeasurePreserving A.coding (Measure.infinitePi A.digitLaw) A.measure := by
  exact ⟨A.measurable_coding, rfl⟩

private def codingPullback (A : Data) :
    Lp ℂ 2 A.measure →ₗᵢ[ℂ] Lp ℂ 2 (Measure.infinitePi A.digitLaw) :=
  Lp.compMeasurePreservingₗᵢ ℂ A.coding (coding_measurePreserving A)

private def productSpectralVector (A : Data) (ξ : ℝ) :
    Lp ℂ 2 (Measure.infinitePi A.digitLaw) :=
  codingPullback A (spectralVector A.measure ξ)

private lemma productSpectralVector_ae_eq (A : Data) (ξ : ℝ) :
    ∀ᵐ d ∂Measure.infinitePi A.digitLaw, productSpectralVector A ξ d =
      Complex.exp ((2 * Real.pi * ξ * A.coding d : ℝ) * Complex.I) := by
  have hexp : ∀ᵐ x ∂A.measure, spectralVector A.measure ξ x =
      Complex.exp ((2 * Real.pi * ξ * x : ℝ) * Complex.I) := spectralVector_ae_eq A.measure ξ
  have hexp' : ∀ᵐ d ∂Measure.infinitePi A.digitLaw,
      spectralVector A.measure ξ (A.coding d) =
        Complex.exp ((2 * Real.pi * ξ * A.coding d : ℝ) * Complex.I) :=
    (coding_measurePreserving A).quasiMeasurePreserving.ae hexp
  filter_upwards [Lp.coeFn_compMeasurePreserving (spectralVector A.measure ξ)
    (coding_measurePreserving A), hexp'] with d hpull hexp
  exact hpull.trans hexp

private lemma productSpectralVector_orthonormal (p r m : ℕ → ℕ)
    [∀ n, Fact (p n).Prime] (hr : ∀ n, 0 < r n) :
    let A := galoisPowerMoranData p r m hr
    Orthonormal ℂ (fun ξ : galoisPowerSpectrum p r m hr ↦ productSpectralVector A ξ) := by
  intro A
  refine orthonormal_iff_ite.mpr fun ξ η ↦ ?_
  rw [productSpectralVector, productSpectralVector,
    (codingPullback A).inner_map_map]
  exact orthonormal_iff_ite.mp (galoisPowerSpectrum_orthonormal p r m hr) ξ η

private lemma indep_digits (A : Data) :
    ProbabilityTheory.iIndepFun (fun n (d : ℕ → ℕ) ↦ d n)
      (Measure.infinitePi A.digitLaw) := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  exact ProbabilityTheory.iIndepFun_infinitePi (fun _ ↦ measurable_id)

private def prefixFourierCylinder (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) : (ℕ → ℕ) → ℂ :=
  productCylinderFunction A n fun d ↦ w d * Complex.exp
    ((-2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) * Complex.I)

private def finiteTailFourierFunction (A : Data) (n N : ℕ) (ξ : ℝ)
    (d : ℕ → ℕ) : ℂ :=
  Complex.exp ((-2 * Real.pi * ξ *
    (∑ j ∈ Finset.Ico n (n + N), (d j : ℝ) / (A.scale j : ℝ)) : ℝ) * Complex.I)

private lemma measurable_prefixFourierCylinder (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    Measurable (prefixFourierCylinder A n ξ w) := by
  exact measurable_productCylinderFunction A n _

private lemma measurable_finiteTailFourierFunction (A : Data) (n N : ℕ) (ξ : ℝ) :
    Measurable (finiteTailFourierFunction A n N ξ) := by
  unfold finiteTailFourierFunction
  fun_prop

private lemma indep_prefixFourierCylinder_finiteTail (A : Data) (n N : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    ProbabilityTheory.IndepFun (prefixFourierCylinder A n ξ w)
      (finiteTailFourierFunction A n N ξ) (Measure.infinitePi A.digitLaw) := by
  let S := Finset.range n
  let T := Finset.Ico n (n + N)
  have hST : Disjoint S T := by
    simp [S, T, Finset.disjoint_left]
    omega
  have h := (indep_digits A).indepFun_finset S T hST fun j ↦ measurable_pi_apply j
  let f : (S → ℕ) → ℂ := fun q ↦
    w (fun j ↦ if hd : q ⟨j, Finset.mem_range.mpr j.isLt⟩ ∈ A.digits j then
      ⟨q ⟨j, Finset.mem_range.mpr j.isLt⟩, hd⟩ else
      ⟨(A.digits_nonempty j).choose, (A.digits_nonempty j).choose_spec⟩) *
        Complex.exp ((-2 * Real.pi * ξ * (∑ j : Fin n,
          (((if hd : q ⟨j, Finset.mem_range.mpr j.isLt⟩ ∈ A.digits j then
            ⟨q ⟨j, Finset.mem_range.mpr j.isLt⟩, hd⟩ else
            ⟨(A.digits_nonempty j).choose,
              (A.digits_nonempty j).choose_spec⟩) : A.digits j) : ℕ) /
                (A.scale j : ℝ)) : ℝ) * Complex.I)
  let g : (T → ℕ) → ℂ := fun q ↦ Complex.exp ((-2 * Real.pi * ξ *
    (∑ j : T, (q j : ℝ) / (A.scale j : ℝ)) : ℝ) * Complex.I)
  have hfg := h.comp (measurable_of_countable f) (measurable_of_countable g)
  convert hfg using 1
  · funext d
    simp only [Function.comp_apply, f, S, prefixFourierCylinder,
      productCylinderFunction, admissiblePrefix]
    rfl
  · funext d
    simp only [Function.comp_apply, g, T, finiteTailFourierFunction]
    congr 2
    exact congrArg (fun x : ℝ ↦ (x : ℂ)) (congrArg (fun x : ℝ ↦ -2 * Real.pi * ξ * x)
      (Finset.sum_subtype (Finset.Ico n (n + N)) (fun _ ↦ Iff.rfl)
        (fun j ↦ (d j : ℝ) / (A.scale j : ℝ))))

private lemma integral_prefix_mul_finiteTail (A : Data) (n N : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    (∫ d, prefixFourierCylinder A n ξ w d * finiteTailFourierFunction A n N ξ d
        ∂Measure.infinitePi A.digitLaw) =
      (∫ d, prefixFourierCylinder A n ξ w d ∂Measure.infinitePi A.digitLaw) *
        ∫ d, finiteTailFourierFunction A n N ξ d ∂Measure.infinitePi A.digitLaw := by
  exact (indep_prefixFourierCylinder_finiteTail A n N ξ w).integral_mul_eq_mul_integral
    (measurable_prefixFourierCylinder A n ξ w).aestronglyMeasurable
    (measurable_finiteTailFourierFunction A n N ξ).aestronglyMeasurable

private lemma integral_prefixFourierCylinder (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    (∫ d, prefixFourierCylinder A n ξ w d ∂Measure.infinitePi A.digitLaw) =
      (Fintype.card (∀ j : Fin n, A.digits j) : ℝ)⁻¹ *
        ∑ d, w d * Complex.exp
          ((-2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) *
            Complex.I) := by
  exact integral_productCylinderFunction A n _

private lemma finiteTailFourierFunction_eq (A : Data) (n N : ℕ) (ξ : ℝ)
    (d : ℕ → ℕ) :
    finiteTailFourierFunction A n N ξ d =
      BoundedContinuousFunction.innerProbChar
        (-2 * Real.pi * ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ))
        (∑ k ∈ Finset.range N, (d (n + k) : ℝ) / (tailData A n).scale k) := by
  simp only [finiteTailFourierFunction, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left, BoundedContinuousFunction.innerProbChar_apply,
    RCLike.inner_apply, conj_trivial]
  congr 1
  have hsum :
      (∑ x ∈ Finset.range N, (d (n + x) : ℝ) / (A.scale (n + x) : ℝ)) =
        (∑ x ∈ Finset.range N, (d (n + x) : ℝ) / (tailData A n).scale x) /
          ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [div_div, ← Nat.cast_mul, Nat.mul_comm, prefix_mul_scale_tail]
  have hreal :
      -2 * Real.pi * ξ *
          (∑ x ∈ Finset.range N, (d (n + x) : ℝ) / (A.scale (n + x) : ℝ)) =
        (-2 * Real.pi * ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)) *
          ∑ x ∈ Finset.range N, (d (n + x) : ℝ) / (tailData A n).scale x := by
    rw [hsum]
    ring
  exact congrArg (fun x : ℝ ↦ (x : ℂ) * Complex.I) hreal

private lemma shift_measurePreserving (A : Data) (n : ℕ) :
    MeasurePreserving (fun d : ℕ → ℕ ↦ fun k ↦ d (n + k))
      (Measure.infinitePi A.digitLaw)
      (Measure.infinitePi (tailData A n).digitLaw) := by
  letI (j : ℕ) : IsProbabilityMeasure (A.digitLaw j) := A.isProbabilityMeasure_digitLaw j
  refine ⟨by fun_prop, ?_⟩
  change (Measure.infinitePi A.digitLaw).map (fun d k ↦ d (n + k)) =
    Measure.infinitePi (fun k ↦ A.digitLaw (n + k))
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := A.digitLaw) (f := fun k ↦ n + k) (fun _ _ h ↦ Nat.add_left_cancel h)

private lemma integral_finiteTailFourierFunction (A : Data) (n N : ℕ) (ξ : ℝ) :
    (∫ d, finiteTailFourierFunction A n N ξ d ∂Measure.infinitePi A.digitLaw) =
      ∫ d, BoundedContinuousFunction.innerProbChar
          (-2 * Real.pi * ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ))
          (∑ k ∈ Finset.range N, (d k : ℝ) / (tailData A n).scale k)
        ∂Measure.infinitePi (tailData A n).digitLaw := by
  let f : (ℕ → ℕ) → ℂ := fun d ↦ BoundedContinuousFunction.innerProbChar
    (-2 * Real.pi * ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ))
    (∑ k ∈ Finset.range N, (d k : ℝ) / (tailData A n).scale k)
  calc
    _ = ∫ d, f (fun k ↦ d (n + k)) ∂Measure.infinitePi A.digitLaw :=
      integral_congr_ae (Filter.Eventually.of_forall fun d ↦
        finiteTailFourierFunction_eq A n N ξ d)
    _ = ∫ d, f d ∂Measure.infinitePi (tailData A n).digitLaw := by
      rw [← integral_map (μ := Measure.infinitePi A.digitLaw)
        (shift_measurePreserving A n).measurable.aemeasurable,
        (shift_measurePreserving A n).map_eq]
      fun_prop

private lemma tendsto_integral_finiteTailFourierFunction (A : Data) (n : ℕ) (ξ : ℝ) :
    Tendsto (fun N ↦ ∫ d, finiteTailFourierFunction A n N ξ d
      ∂Measure.infinitePi A.digitLaw) atTop
      (𝓝 (Fourier.fourierIntegral Real.fourierChar (tailData A n).measure
        (fun _ ↦ (1 : ℂ))
        (ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)))) := by
  let t := -2 * Real.pi * ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)
  have h := (tailData A n).tendsto_integral_partial_coding
    (BoundedContinuousFunction.innerProbChar t)
  convert h using 1
  · funext N
    exact integral_finiteTailFourierFunction A n N ξ
  · congr 1
    rw [fourierIntegral_one_eq, Data.measure]
    rw [integral_map (μ := Measure.infinitePi (tailData A n).digitLaw)
      (tailData A n).measurable_coding.aemeasurable]
    · apply integral_congr_ae
      filter_upwards with d
      simp only [BoundedContinuousFunction.innerProbChar_apply, RCLike.inner_apply,
        conj_trivial, t]
      congr 1
      push_cast
      ring
    · fun_prop

private lemma tendsto_prefix_mul_finiteTail (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) (d : ℕ → ℕ)
    (hd : ∀ j, d j ∈ A.digits j) :
    Tendsto (fun N ↦ prefixFourierCylinder A n ξ w d *
      finiteTailFourierFunction A n N ξ d) atTop
      (𝓝 (productCylinderFunction A n w d *
        Complex.exp ((-2 * Real.pi * ξ * A.coding d : ℝ) * Complex.I))) := by
  have hsum : Tendsto (fun N ↦
      ∑ j ∈ Finset.Ico n (n + N), (d j : ℝ) / (A.scale j : ℝ)) atTop
      (𝓝 (∑' k, (d (n + k) : ℝ) / (A.scale (n + k) : ℝ))) := by
    have htail : Summable (fun k ↦ (d (n + k) : ℝ) / (A.scale (n + k) : ℝ)) := by
      simpa only [Nat.add_comm] using
        (summable_nat_add_iff n).mpr (A.summable_coding d hd)
    simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] using
      htail.hasSum.tendsto_sum_nat
  have hexp : Tendsto (fun N ↦ finiteTailFourierFunction A n N ξ d) atTop
      (𝓝 (Complex.exp ((-2 * Real.pi * ξ *
        (∑' k, (d (n + k) : ℝ) / (A.scale (n + k) : ℝ)) : ℝ) * Complex.I))) := by
    unfold finiteTailFourierFunction
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    apply Filter.Tendsto.mul_const
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hsum.const_mul (-2 * Real.pi * ξ))
  have hcoding : A.coding d =
      (∑ j : Fin n, (d j : ℝ) / (A.scale j : ℝ)) +
        ∑' k, (d (n + k) : ℝ) / (A.scale (n + k) : ℝ) := by
    rw [Data.coding]
    simpa only [Fin.sum_univ_eq_sum_range
      (fun j ↦ (d j : ℝ) / (A.scale j : ℝ)) n, Nat.add_comm] using
      ((A.summable_coding d hd).sum_add_tsum_nat_add n).symm
  have hlimit : prefixFourierCylinder A n ξ w d *
        Complex.exp ((-2 * Real.pi * ξ *
          (∑' k, (d (n + k) : ℝ) / (A.scale (n + k) : ℝ)) : ℝ) * Complex.I) =
      productCylinderFunction A n w d *
        Complex.exp ((-2 * Real.pi * ξ * A.coding d : ℝ) * Complex.I) := by
    simp only [prefixFourierCylinder, productCylinderFunction, admissiblePrefix,
      dif_pos (hd _)]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    have harg :
        -2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℝ) / (A.scale j : ℝ)) +
            -2 * Real.pi * ξ *
              (∑' k, (d (n + k) : ℝ) / (A.scale (n + k) : ℝ)) =
          -2 * Real.pi * ξ * A.coding d := by
      rw [hcoding]
      ring
    rw [← add_mul]
    simpa only [Complex.ofReal_add] using
      congrArg (fun x : ℝ ↦ (x : ℂ) * Complex.I) harg
  rw [← hlimit]
  exact tendsto_const_nhds.mul hexp

private lemma integral_productCylinder_mul_codingChar (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    (∫ d, productCylinderFunction A n w d *
      Complex.exp ((-2 * Real.pi * ξ * A.coding d : ℝ) * Complex.I)
        ∂Measure.infinitePi A.digitLaw) =
      ((Fintype.card (∀ j : Fin n, A.digits j) : ℝ)⁻¹ *
        ∑ d, w d * Complex.exp
          ((-2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) *
            Complex.I)) *
        Fourier.fourierIntegral Real.fourierChar (tailData A n).measure
          (fun _ ↦ (1 : ℂ))
          (ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)) := by
  letI (j : ℕ) : IsProbabilityMeasure (A.digitLaw j) := A.isProbabilityMeasure_digitLaw j
  let C := ∑ d, ‖w d‖
  have hdom : Tendsto (fun N ↦ ∫ d, prefixFourierCylinder A n ξ w d *
      finiteTailFourierFunction A n N ξ d ∂Measure.infinitePi A.digitLaw) atTop
      (𝓝 (∫ d, productCylinderFunction A n w d *
        Complex.exp ((-2 * Real.pi * ξ * A.coding d : ℝ) * Complex.I)
          ∂Measure.infinitePi A.digitLaw)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C) ?_ ?_
      (integrable_const C) ?_
    · exact Filter.Eventually.of_forall fun N ↦
        ((measurable_prefixFourierCylinder A n ξ w).mul
          (measurable_finiteTailFourierFunction A n N ξ)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun N ↦ Filter.Eventually.of_forall fun d ↦ by
        simp only [prefixFourierCylinder, productCylinderFunction,
          finiteTailFourierFunction, norm_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one, C]
        exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _)
          (Finset.mem_univ (admissiblePrefix A n d))
    · exact A.ae_all_mem_digits.mono fun d hd ↦
        tendsto_prefix_mul_finiteTail A n ξ w d hd
  have hfactor : Tendsto (fun N ↦ ∫ d, prefixFourierCylinder A n ξ w d *
      finiteTailFourierFunction A n N ξ d ∂Measure.infinitePi A.digitLaw) atTop
      (𝓝 ((∫ d, prefixFourierCylinder A n ξ w d ∂Measure.infinitePi A.digitLaw) *
        Fourier.fourierIntegral Real.fourierChar (tailData A n).measure
          (fun _ ↦ (1 : ℂ))
          (ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)))) := by
    convert tendsto_const_nhds.mul (tendsto_integral_finiteTailFourierFunction A n ξ) using 1
    funext N
    exact integral_prefix_mul_finiteTail A n N ξ w
  rw [← integral_prefixFourierCylinder A n ξ w]
  exact tendsto_nhds_unique hdom hfactor

private lemma productSpectralVector_inner_productCylinder (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    inner ℂ (productSpectralVector A ξ) (productCylinderVector A n w) =
      ((Fintype.card (∀ j : Fin n, A.digits j) : ℝ)⁻¹ *
        ∑ d, w d * Complex.exp
          ((-2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) *
            Complex.I)) *
        Fourier.fourierIntegral Real.fourierChar (tailData A n).measure
          (fun _ ↦ (1 : ℂ))
          (ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)) := by
  rw [MeasureTheory.L2.inner_def]
  rw [integral_congr_ae]
  · exact integral_productCylinder_mul_codingChar A n ξ w
  · filter_upwards [productSpectralVector_ae_eq A ξ,
      (memLp_productCylinderFunction A n w).coeFn_toLp] with d hv hw
    have hw' : (productCylinderVector A n w : (ℕ → ℕ) → ℂ) d =
        productCylinderFunction A n w d := by
      simpa only [productCylinderVector] using hw
    rw [hv, hw']
    simp only [RCLike.inner_apply, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, Complex.exp_neg]
    rw [← Complex.exp_neg]
    congr 3
    push_cast
    ring_nf

private lemma productCylinder_inner_finiteFourier (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    inner ℂ (productSpectralVector A ξ) (productCylinderVector A n w) =
      Fourier.fourierIntegral Real.fourierChar (tailData A n).measure (fun _ ↦ (1 : ℂ))
        (ξ / ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)) *
          ((Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
            inner ℂ (finiteFourierVector A n ξ) (WithLp.toLp 2 w)) := by
  rw [productSpectralVector_inner_productCylinder, finiteFourierVector_coefficient]
  have hc : (Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
      (Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ =
        ((Fintype.card (∀ j : Fin n, A.digits j) : ℝ) : ℂ)⁻¹ := by
    rw [← pow_two, inv_pow]
    congr 1
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  rw [← mul_assoc _ _ (∑ d, _), hc, Complex.ofReal_inv]
  ring

private def finiteCylinderCoefficient (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ)
    (w : (∀ j : Fin n, (galoisPowerMoranData p r m hr).digits j) → ℂ)
    (k : ∀ j : Fin n, ZMod (p j ^ r j)) : ℂ :=
  let A := galoisPowerMoranData p r m hr
  (Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
    ((Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
      ∑ d, w d * Complex.exp
        ((-2 * Real.pi * finiteFrequency A (finitePowerChoice p r m k) n *
          (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) * Complex.I))

private lemma sum_norm_finiteCylinderCoefficient_sq (p r m : ℕ → ℕ)
    [∀ j, Fact (p j).Prime] (hr : ∀ j, 0 < r j) (n : ℕ)
    (w : (∀ j : Fin n, (galoisPowerMoranData p r m hr).digits j) → ℂ) :
    (∑ k, ‖finiteCylinderCoefficient p r m hr n w k‖ ^ 2) =
      ‖productCylinderVector (galoisPowerMoranData p r m hr) n w‖ ^ 2 := by
  let A := galoisPowerMoranData p r m hr
  let c : ℂ := (Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹
  have hc : ‖c‖ ^ 2 = (Fintype.card (∀ j : Fin n, A.digits j) : ℝ)⁻¹ := by
    simp only [c, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hparse := finitePowerFourier_parseval p r m hr n w
  change (∑ k, ‖c * ∑ d, w d * Complex.exp
    ((-2 * Real.pi * finiteFrequency A (finitePowerChoice p r m k) n *
      (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) * Complex.I)‖ ^ 2) =
        ∑ d, ‖w d‖ ^ 2 at hparse
  rw [norm_productCylinderVector_sq]
  change (∑ k, ‖c * (c * ∑ d, w d * Complex.exp
    ((-2 * Real.pi * finiteFrequency A (finitePowerChoice p r m k) n *
      (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) * Complex.I))‖ ^ 2) = _
  calc
    _ = ‖c‖ ^ 2 * (∑ k, ‖c * ∑ d, w d * Complex.exp
        ((-2 * Real.pi * finiteFrequency A (finitePowerChoice p r m k) n *
          (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) * Complex.I)‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [norm_mul, mul_pow]
    _ = ‖c‖ ^ 2 * ∑ d, ‖w d‖ ^ 2 := by rw [hparse]
    _ = _ := by rw [hc]

private def finiteTailFactor (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) (k : ∀ j : Fin n, ZMod (p j ^ r j)) : ℂ :=
  let A := galoisPowerMoranData p r m hr
  Fourier.fourierIntegral Real.fourierChar (tailData A n).measure
    (fun _ ↦ (1 : ℂ))
    ((finiteFrequency A (finitePowerChoice p r m k) n : ℝ) /
      ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ))

private lemma productSpectralVector_inner_eq_finiteTailFactor_mul_coefficient
    (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime] (hr : ∀ j, 0 < r j) (n : ℕ)
    (w : (∀ j : Fin n, (galoisPowerMoranData p r m hr).digits j) → ℂ)
    (k : ∀ j : Fin n, ZMod (p j ^ r j)) :
    let A := galoisPowerMoranData p r m hr
    inner ℂ (productSpectralVector A (finitePowerSpectrumEmbedding p r m hr n k))
      (productCylinderVector A n w) =
        finiteTailFactor p r m hr n k * finiteCylinderCoefficient p r m hr n w k := by
  intro A
  change inner ℂ (productSpectralVector A
    (finiteFrequency A (finitePowerChoice p r m k) n : ℝ)) (productCylinderVector A n w) = _
  simpa only [finiteTailFactor, finiteCylinderCoefficient, finiteFourierVector_coefficient] using
    productCylinder_inner_finiteFourier A n
      (finiteFrequency A (finitePowerChoice p r m k) n) w

private def promoteCylinderWeight (A : Data) {m n : ℕ} (hmn : m ≤ n)
    (w : (∀ j : Fin m, A.digits j) → ℂ) :
    (∀ j : Fin n, A.digits j) → ℂ := fun d ↦
  w fun j ↦ d ⟨j, j.isLt.trans_le hmn⟩

private lemma productCylinderVector_promote (A : Data) {m n : ℕ} (hmn : m ≤ n)
    (w : (∀ j : Fin m, A.digits j) → ℂ) :
    productCylinderVector A n (promoteCylinderWeight A hmn w) =
      productCylinderVector A m w := by
  apply Lp.ext
  filter_upwards [(memLp_productCylinderFunction A n
      (promoteCylinderWeight A hmn w)).coeFn_toLp,
    (memLp_productCylinderFunction A m w).coeFn_toLp] with d hn hm
  rw [show (productCylinderVector A n (promoteCylinderWeight A hmn w) :
      (ℕ → ℕ) → ℂ) d = productCylinderFunction A n
        (promoteCylinderWeight A hmn w) d by
      simpa only [productCylinderVector] using hn,
    show (productCylinderVector A m w : (ℕ → ℕ) → ℂ) d =
      productCylinderFunction A m w d by
      simpa only [productCylinderVector] using hm]
  unfold productCylinderFunction promoteCylinderWeight
  congr 1

private lemma productCylinderVector_add (A : Data) (n : ℕ)
    (w u : (∀ j : Fin n, A.digits j) → ℂ) :
    productCylinderVector A n (w + u) =
      productCylinderVector A n w + productCylinderVector A n u := by
  unfold productCylinderVector
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun _ ↦ rfl

private lemma productCylinderVector_smul (A : Data) (n : ℕ) (c : ℂ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    productCylinderVector A n (c • w) = c • productCylinderVector A n w := by
  unfold productCylinderVector
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun _ ↦ rfl

private lemma productCylinderVector_zero (A : Data) (n : ℕ) :
    productCylinderVector A n 0 = 0 := by
  simpa only [zero_smul] using productCylinderVector_smul A n 0 (0 :
    (∀ j : Fin n, A.digits j) → ℂ)

private def positiveCylinderSubmodule (A : Data) :
    Submodule ℂ (Lp ℂ 2 (Measure.infinitePi A.digitLaw)) where
  carrier := {f | ∃ n, ∃ w : (∀ j : Fin (n + 1), A.digits j) → ℂ,
    f = productCylinderVector A (n + 1) w}
  zero_mem' := ⟨0, 0, (productCylinderVector_zero A 1).symm⟩
  add_mem' := by
    rintro f g ⟨n, w, rfl⟩ ⟨m, u, rfl⟩
    let N := max n m
    let w' := promoteCylinderWeight A (Nat.succ_le_succ (le_max_left n m)) w
    let u' := promoteCylinderWeight A (Nat.succ_le_succ (le_max_right n m)) u
    refine ⟨N, w' + u', ?_⟩
    rw [productCylinderVector_add,
      productCylinderVector_promote A (Nat.succ_le_succ (le_max_left n m)),
      productCylinderVector_promote A (Nat.succ_le_succ (le_max_right n m))]
  smul_mem' := by
    rintro c f ⟨n, w, rfl⟩
    exact ⟨n, c • w, (productCylinderVector_smul A (n + 1) c w).symm⟩

private def cylinderWeight (A : Data) (I : Finset ℕ) (S : Set (I → ℕ)) (c : ℂ) :
    (∀ j : Fin (I.sup id + 1), A.digits j) → ℂ := by
  classical
  exact fun d ↦
    if (fun i : I ↦
      (d ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩ : ℕ)) ∈ S
      then c else 0

private lemma indicatorConstLp_cylinder_mem (A : Data) (I : Finset ℕ)
    (S : Set (I → ℕ)) (hS : MeasurableSet S) (hμ :
      (Measure.infinitePi A.digitLaw) (MeasureTheory.cylinder I S) ≠ ∞) (c : ℂ) :
    indicatorConstLp 2 (hS.cylinder I) hμ c ∈ positiveCylinderSubmodule A := by
  refine ⟨I.sup id, cylinderWeight A I S c, ?_⟩
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := Measure.infinitePi A.digitLaw)
      (s := MeasureTheory.cylinder I S) (hs := hS.cylinder I) (hμs := hμ) (c := c),
    (memLp_productCylinderFunction A (I.sup id + 1) (cylinderWeight A I S c)).coeFn_toLp,
    A.ae_all_mem_digits] with d hind hcyl hd
  have hcyl' : (productCylinderVector A (I.sup id + 1) (cylinderWeight A I S c) :
      (ℕ → ℕ) → ℂ) d = productCylinderFunction A (I.sup id + 1)
        (cylinderWeight A I S c) d := by
    simpa only [productCylinderVector] using hcyl
  rw [hind, hcyl']
  simp only [Set.indicator, MeasureTheory.mem_cylinder, productCylinderFunction, cylinderWeight]
  have htuple : (fun i : I ↦
      ((admissiblePrefix A (I.sup id + 1) d
        ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩ :
          A.digits i) : ℕ)) = I.restrict d := by
    funext i
    simp only [admissiblePrefix, dif_pos (hd i), Finset.restrict_def]
  rw [htuple]
  by_cases hmem : I.restrict d ∈ S
  · simp only [if_pos hmem, if_pos ((MeasureTheory.mem_cylinder I S d).mpr hmem)]
  · simp only [if_neg hmem, if_neg (fun h ↦ hmem ((MeasureTheory.mem_cylinder I S d).mp h))]

private lemma dense_positiveCylinderSubmodule (A : Data) :
    Dense (positiveCylinderSubmodule A :
      Set (Lp ℂ 2 (Measure.infinitePi A.digitLaw))) := by
  letI (j : ℕ) : IsProbabilityMeasure (A.digitLaw j) := A.isProbabilityMeasure_digitLaw j
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let ν := Measure.infinitePi A.digitLaw
  let D := positiveCylinderSubmodule A
  have hMD : ν.MeasureDense (MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ)) :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite ν
      MeasureTheory.isSetAlgebra_measurableCylinders
      MeasureTheory.generateFrom_measurableCylinders.symm
  have hcyl (c : ℂ) :
      {indicatorConstLp 2 (hMD.measurable t ht) hμt c |
        (t : Set (ℕ → ℕ)) (ht : t ∈ MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ))
          (hμt : ν t ≠ ∞)} ⊆ (D : Set (Lp ℂ 2 ν)) := by
    rintro _ ⟨t, ht, hμt, rfl⟩
    obtain ⟨I, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders t).mp ht
    exact indicatorConstLp_cylinder_mem A I S hS hμt c
  have hindicator (c : ℂ) (t : Set (ℕ → ℕ)) (ht : MeasurableSet t) (hμt : ν t ≠ ∞) :
      indicatorConstLp 2 ht hμt c ∈ D.topologicalClosure := by
    apply (closure_mono (hcyl c))
    exact hMD.indicatorConstLp_subset_closure 2 c ⟨t, ht, hμt, rfl⟩
  have htop : D.topologicalClosure = ⊤ := by
    apply eq_top_iff.mpr
    rintro f -
    refine Lp.induction (p := 2) (by simp) (motive := fun g ↦ g ∈ D.topologicalClosure)
      ?_ ?_ D.isClosed_topologicalClosure f
    · intro c t ht hμt
      rw [Lp.simpleFunc.coe_indicatorConst]
      exact hindicator c t ht (ne_of_lt hμt)
    · rintro f g hf hg - hfm hgm
      exact D.topologicalClosure.add_mem hfm hgm
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, htop]
  rfl

private lemma orthogonal_eq_bot_of_linearIsometry {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : E →ₗᵢ[ℂ] F) (v : ι → E)
    (hcomplete : (Submodule.span ℂ (Set.range fun i ↦ T (v i)))ᗮ = ⊥) :
    (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  have hTf : T f ∈ (Submodule.span ℂ (Set.range fun i ↦ T (v i)))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro g hg
    refine Submodule.span_induction (p := fun g hg ↦ inner ℂ g (T f) = 0) ?_ (by simp)
      (by simp +contextual [inner_add_left]) (by simp +contextual [inner_smul_left]) hg
    rintro _ ⟨i, rfl⟩
    rw [T.inner_map_map]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self (f := v) i)) hf
  rw [hcomplete] at hTf
  exact T.injective (by simpa using hTf)

/-- The Fourier dimension of a set, using probability measures concentrated on it. -/
def setFourierDim (K : Set ℝ) : ℝ :=
  sSup {t : ℝ | ∃ μ : Measure ℝ, ∃ hμ : IsProbabilityMeasure μ,
    letI := hμ
    μ Kᶜ = 0 ∧ fourierDim μ = t}

private lemma set_fourier_dims_bddAbove (K : Set ℝ) :
    BddAbove {t : ℝ | ∃ μ : Measure ℝ, ∃ hμ : IsProbabilityMeasure μ,
      letI := hμ
      μ Kᶜ = 0 ∧ fourierDim μ = t} := by
  refine ⟨1, ?_⟩
  rintro t ⟨μ, hμ, _, rfl⟩
  exact fourierDim_le_one μ

private lemma fourierDim_le_setFourierDim (μ : Measure ℝ) [hμ : IsProbabilityMeasure μ]
    {K : Set ℝ} (hK : μ Kᶜ = 0) : fourierDim μ ≤ setFourierDim K := by
  exact le_csSup (set_fourier_dims_bddAbove K) ⟨μ, hμ, hK, rfl⟩

/-- A Salem set has equal Fourier and Hausdorff dimensions. -/
def is_salem (K : Set ℝ) : Prop :=
  ENNReal.ofReal (setFourierDim K) = dimH K

private lemma fourier_autocorrelation (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar (μ.conv (μ.map (fun x ↦ -x)))
      (fun _ ↦ (1 : ℂ)) ξ =
      (‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ‖ : ℂ) ^ 2 := by
  have hneg (t : ℝ) : charFun (μ.map (fun x ↦ -x)) t = starRingEnd ℂ (charFun μ t) := by
    simpa only [neg_one_mul, charFun_neg] using charFun_map_mul (μ := μ) (-1) t
  have h := charFun_conv (μ := μ) (ν := μ.map (fun x ↦ -x)) (-2 * Real.pi * ξ)
  simp only [hneg, Complex.mul_conj'] at h
  simpa only [fourierIntegral_one_eq, charFun_apply_real, Complex.ofReal_mul] using h

private lemma integral_fourier_mul_gaussian (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b : ℂ} (hb : 0 < b.re) :
    (∫ ξ : ℝ, Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ *
      Complex.exp (-Real.pi * b * (ξ : ℂ) ^ 2)) =
      ∫ x : ℝ, 1 / b ^ (1 / 2 : ℂ) *
        Complex.exp (-Real.pi / b * (x : ℂ) ^ 2) ∂μ := by
  have hg : Integrable (fun ξ : ℝ ↦ Complex.exp (-Real.pi * b * (ξ : ℂ) ^ 2)) := by
    simpa only [neg_mul] using integrable_cexp_neg_mul_sq
      (b := (Real.pi : ℂ) * b) (by simpa using mul_pos Real.pi_pos hb)
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := LinearMap.mul ℝ ℝ) Real.continuous_fourierChar
    (continuous_fst.mul continuous_snd) (integrable_const (1 : ℂ) (μ := μ)) hg
  simpa only [Fourier.fourierIntegral, LinearMap.flip_mul, one_smul,
    VectorFourier.fourierIntegral, LinearMap.mul_apply', ← Real.fourier_real_eq,
    fourier_gaussian_pi hb, smul_eq_mul, one_mul] using h

private lemma integral_fourier_sq_mul_gaussian (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    (∫ ξ : ℝ, (‖Fourier.fourierIntegral Real.fourierChar μ
      (fun _ ↦ (1 : ℂ)) ξ‖ : ℂ) ^ 2 * Complex.exp (-Real.pi * b * (ξ : ℂ) ^ 2)) =
      ∫ x : ℝ, ∫ y : ℝ, 1 / (b : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-Real.pi / b * ((x - y : ℝ) : ℂ) ^ 2) ∂μ ∂μ := by
  have hg : Integrable (fun x : ℝ ↦ Complex.exp (-Real.pi / b * (x : ℂ) ^ 2))
      (μ.conv (μ.map (fun x ↦ -x))) := by
    refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
    filter_upwards with x
    rw [neg_div, ← Complex.ofReal_div, norm_cexp_neg_mul_sq, Complex.ofReal_re, norm_one]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_pos Real.pi_pos hb).le) (sq_nonneg x))
  have h := integral_fourier_mul_gaussian (μ.conv (μ.map (fun x ↦ -x)))
    (b := (b : ℂ)) hb
  rw [integral_conv (hg.const_mul (1 / (b : ℂ) ^ (1 / 2 : ℂ)))] at h
  simp only [fourier_autocorrelation] at h
  refine h.trans (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))
  dsimp only
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [sub_eq_add_neg]

private lemma integral_norm_fourier_sq_mul_gaussian (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    (∫ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
      (fun _ ↦ (1 : ℂ)) ξ‖ ^ 2 * Real.exp (-Real.pi * b * ξ ^ 2)) =
      ∫ x : ℝ, ∫ y : ℝ, 1 / Real.sqrt b *
        Real.exp (-Real.pi / b * (x - y) ^ 2) ∂μ ∂μ := by
  have hpow : (b : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt b : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      ← Real.sqrt_eq_rpow] using (Complex.ofReal_cpow hb.le (1 / 2)).symm
  apply Complex.ofReal_injective
  have h := integral_fourier_sq_mul_gaussian μ hb
  rw [hpow] at h
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_exp,
    integral_complex_ofReal] using h

private lemma integrable_norm_fourier_sq_mul_gaussian (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : ℝ ↦ ‖Fourier.fourierIntegral Real.fourierChar μ
      (fun _ ↦ (1 : ℂ)) ξ‖ ^ 2 * Real.exp (-Real.pi * b * ξ ^ 2)) := by
  have hg : Integrable (fun ξ : ℝ ↦ Real.exp (-(Real.pi * b) * ξ ^ 2)) :=
    integrable_exp_neg_mul_sq (mul_pos Real.pi_pos hb)
  have hg' : Integrable (fun ξ : ℝ ↦ Real.exp (-Real.pi * b * ξ ^ 2)) := by
    convert hg using 1
    ring_nf
  refine hg'.bdd_mul (c := (μ.real Set.univ) ^ 2) ?_ ?_
  · exact ((VectorFourier.fourierIntegral_continuous (L := LinearMap.mul ℝ ℝ)
      Real.continuous_fourierChar (continuous_fst.mul continuous_snd)
      (integrable_const (1 : ℂ) (μ := μ))).norm.pow 2).aestronglyMeasurable
  · filter_upwards with ξ
    have hft : ‖Fourier.fourierIntegral Real.fourierChar μ
        (fun _ ↦ (1 : ℂ)) ξ‖ ≤ μ.real Set.univ := by
      simpa using Fourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using
      pow_le_pow_left₀ (norm_nonneg _) hft 2

private lemma integrable_abs_rpow_mul_exp_neg_mul_sq {b q : ℝ}
    (hb : 0 < b) (hq : -1 < q) :
    Integrable (fun x : ℝ ↦ |x| ^ q * Real.exp (-b * x ^ 2)) := by
  have hpos := integrable_rpow_mul_exp_neg_mul_sq hb hq
  have hneg := hpos.comp_neg
  have hpw : Integrable ((Set.Iio (0 : ℝ)).piecewise
      (fun x ↦ (-x) ^ q * Real.exp (-b * (-x) ^ 2))
      (fun x ↦ x ^ q * Real.exp (-b * x ^ 2))) :=
    Integrable.piecewise (s := Set.Iio (0 : ℝ)) measurableSet_Iio
      hneg.integrableOn hpos.integrableOn
  convert hpw using 1
  ext x
  by_cases hx : x < 0
  · simp [Set.piecewise, hx, abs_of_neg hx]
  · simp [Set.piecewise, hx, abs_of_nonneg (le_of_not_gt hx)]

private lemma integrableOn_abs_rpow_near_zero {q : ℝ} (hq : -1 < q) :
    IntegrableOn (fun x : ℝ ↦ |x| ^ q) (Set.Icc (-1) 1) := by
  have hg := integrable_abs_rpow_mul_exp_neg_mul_sq (b := 1) (q := q) zero_lt_one hq
  have hg' : Integrable (fun x : ℝ ↦
      Real.exp 1 * (|x| ^ q * Real.exp (-1 * x ^ 2))) := hg.const_mul _
  refine Integrable.mono' (μ := volume.restrict (Set.Icc (-1) 1))
    hg'.integrableOn ?_ ?_
  · exact ((continuous_abs.comp continuous_id).measurable.pow_const q).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) q)]
    have hx_abs : |x| ≤ 1 := abs_le.mpr hx
    have hx_sq : x ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg x) hx_abs
    have hone : 1 ≤ Real.exp 1 * Real.exp (-1 * x ^ 2) := by
      rw [← Real.exp_add]
      simpa only [one_mul] using Real.one_le_exp (by linarith)
    nlinarith [Real.rpow_nonneg (abs_nonneg x) q]

private lemma integral_abs_rpow_mul_exp_neg_mul_sq {b q : ℝ}
    (hb : 0 < b) (hq : -1 < q) :
    (∫ x : ℝ, |x| ^ q * Real.exp (-b * x ^ 2)) =
      2 * (b ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2)) := by
  calc
    _ = ∫ x : ℝ, (fun u : ℝ ↦ u ^ q * Real.exp (-b * u ^ 2)) |x| := by
      congr 1
      funext x
      dsimp only
      rw [sq_abs]
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x ^ q * Real.exp (-b * x ^ 2) :=
      integral_comp_abs (f := fun u : ℝ ↦ u ^ q * Real.exp (-b * u ^ 2))
    _ = _ := by
      rw [show (fun x : ℝ ↦ x ^ q * Real.exp (-b * x ^ 2)) =
          (fun x : ℝ ↦ x ^ q * Real.exp (-b * x ^ (2 : ℝ))) by
            funext x
            rw [Real.rpow_two]]
      rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2) hq hb]

private lemma sq_le_const_mul_abs_rpow_of_decay {a C t x : ℝ}
    (ht : 0 < t) (hx : x ≠ 0) (ha : 0 ≤ a)
    (h : a ≤ C * (1 + |x|) ^ (-t / 2)) :
    a ^ 2 ≤ C ^ 2 * |x| ^ (-t) := by
  have hrpow : (1 + |x|) ^ (-t) ≤ |x| ^ (-t) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (abs_nonneg x)]
    have hbase : |x| ≤ 1 + |x| := by linarith
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) t)
      (Real.rpow_pos_of_pos (abs_pos.mpr hx) t)).2
        (Real.rpow_le_rpow (abs_nonneg x) hbase ht.le)
  calc
    a ^ 2 ≤ (C * (1 + |x|) ^ (-t / 2)) ^ 2 := pow_le_pow_left₀ ha h 2
    _ = C ^ 2 * (1 + |x|) ^ (-t) := by
      rw [mul_pow]
      congr 1
      calc
        ((1 + |x|) ^ (-t / 2)) ^ (2 : ℕ) =
            ((1 + |x|) ^ (-t / 2)) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (1 + |x|) ^ ((-t / 2) * 2) :=
          (Real.rpow_mul (by positivity) _ _).symm
        _ = (1 + |x|) ^ (-t) := by ring_nf
    _ ≤ C ^ 2 * |x| ^ (-t) :=
      mul_le_mul_of_nonneg_left hrpow (sq_nonneg C)

private lemma integral_norm_fourier_sq_mul_gaussian_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] {C t b : ℝ}
    (ht : 0 < t) (ht₁ : t < 1) (hb : 0 < b)
    (hdecay : ∀ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
      (fun _ ↦ (1 : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-t / 2)) :
    (∫ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
      (fun _ ↦ (1 : ℂ)) ξ‖ ^ 2 * Real.exp (-Real.pi * b * ξ ^ 2)) ≤
      C ^ 2 * (2 * ((Real.pi * b) ^ (-(-t + 1) / 2) *
        (1 / 2) * Real.Gamma ((-t + 1) / 2))) := by
  have hleft := integrable_norm_fourier_sq_mul_gaussian μ hb
  have hweight := integrable_abs_rpow_mul_exp_neg_mul_sq
    (mul_pos Real.pi_pos hb) (by linarith : -1 < -t)
  have hright : Integrable (fun ξ : ℝ ↦
      C ^ 2 * (|ξ| ^ (-t) * Real.exp (-Real.pi * b * ξ ^ 2))) := by
    simpa only [neg_mul] using hweight.const_mul (C ^ 2)
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    rw [ae_iff]
    simp
  calc
    _ ≤ ∫ ξ : ℝ, C ^ 2 *
        (|ξ| ^ (-t) * Real.exp (-Real.pi * b * ξ ^ 2)) := by
      refine integral_mono_ae hleft hright ?_
      filter_upwards [hne] with ξ hξ
      have hsquare := sq_le_const_mul_abs_rpow_of_decay ht hξ
        (norm_nonneg _) (hdecay ξ)
      exact mul_le_mul_of_nonneg_right hsquare (Real.exp_pos _).le |>.trans_eq (by ring)
    _ = C ^ 2 * ∫ ξ : ℝ,
        |ξ| ^ (-t) * Real.exp (-(Real.pi * b) * ξ ^ 2) := by
      rw [integral_const_mul]
      congr 2
      funext ξ
      ring_nf
    _ = _ := by
      rw [integral_abs_rpow_mul_exp_neg_mul_sq
        (mul_pos Real.pi_pos hb) (by linarith : -1 < -t)]

private lemma integral_laplace_riesz_kernel {d z : ℝ} (hd : 0 < d) (hz : z ≠ 0) :
    (∫ a in Set.Ioi (0 : ℝ),
      a ^ (d / 2 - 1) * Real.exp (-(z ^ 2) * a)) =
      (z ^ 2) ^ (-d / 2) * Real.Gamma (d / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := d / 2 - 1) (b := z ^ 2)
    zero_lt_one (by linarith : -1 < d / 2 - 1) (sq_pos_of_ne_zero hz)
  simp only [Real.rpow_one, div_one, mul_one, sub_add_cancel, neg_mul] at h
  convert h using 1 <;> ring_nf

private lemma lintegral_laplace_riesz_kernel {d z : ℝ} (hd : 0 < d) (hz : z ≠ 0) :
    (∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal
      (a ^ (d / 2 - 1) * Real.exp (-(z ^ 2) * a))) =
      ENNReal.ofReal ((z ^ 2) ^ (-d / 2) * Real.Gamma (d / 2)) := by
  have hint : IntegrableOn (fun a : ℝ ↦
      a ^ (d / 2 - 1) * Real.exp (-(z ^ 2) * a)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := d / 2 - 1) (b := z ^ 2)
      (by linarith : -1 < d / 2 - 1) le_rfl (sq_pos_of_ne_zero hz)
    simpa only [Real.rpow_one, neg_mul] using h
  have hnonneg : ∀ᵐ a ∂volume.restrict (Set.Ioi (0 : ℝ)),
      0 ≤ a ^ (d / 2 - 1) * Real.exp (-(z ^ 2) * a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [integral_laplace_riesz_kernel hd hz]

private lemma sq_rpow_neg_half {d z : ℝ} :
    (z ^ 2) ^ (-d / 2) = |z| ^ (-d) := by
  rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg z)]
  congr 2
  ring

private lemma ofReal_laplace_riesz_value {d z : ℝ} (hz : z ≠ 0) :
    ENNReal.ofReal ((z ^ 2) ^ (-d / 2) * Real.Gamma (d / 2)) =
      ENNReal.ofReal (Real.Gamma (d / 2)) * edist 0 z ^ (-d) := by
  rw [sq_rpow_neg_half]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg z) _)]
  rw [mul_comm, edist_dist]
  simp only [Real.dist_eq, zero_sub, abs_neg]
  rw [ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hz)]

private lemma lintegral_rpow_Ioi_eq_top (q : ℝ) :
    (∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal (a ^ q)) = ∞ := by
  by_contra hfinite
  have hmeas : AEStronglyMeasurable (fun a : ℝ ↦ a ^ q)
      (volume.restrict (Set.Ioi 0)) :=
    (measurable_id'.pow_const q).aestronglyMeasurable
  have hnonneg : ∀ᵐ a ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ a ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact Real.rpow_nonneg ha.le q
  have hint : IntegrableOn (fun a : ℝ ↦ a ^ q) (Set.Ioi 0) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp hfinite
  exact not_integrableOn_Ioi_rpow q hint

private lemma riesz_kernel_eq_lintegral {d : ℝ} (hd : 0 < d) (x y : ℝ) :
    edist x y ^ (-d) = (ENNReal.ofReal (Real.Gamma (d / 2)))⁻¹ *
      ∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (a ^ (d / 2 - 1) * Real.exp (-(x - y) ^ 2 * a)) := by
  have hgamma : 0 < Real.Gamma (d / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hgamma_zero : ENNReal.ofReal (Real.Gamma (d / 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hgamma).ne'
  by_cases hxy : x = y
  · subst y
    rw [edist_self, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hd)]
    have heq : (fun a : ℝ ↦ ENNReal.ofReal
        (a ^ (d / 2 - 1) * Real.exp (-(x - x) ^ 2 * a))) =
        fun a : ℝ ↦ ENNReal.ofReal (a ^ (d / 2 - 1)) := by
      funext a
      simp
    rw [heq, lintegral_rpow_Ioi_eq_top]
    simp
  · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    rw [lintegral_laplace_riesz_kernel hd hz]
    rw [ofReal_laplace_riesz_value hz]
    have hcancel : (ENNReal.ofReal (Real.Gamma (d / 2)))⁻¹ *
        ENNReal.ofReal (Real.Gamma (d / 2)) = 1 :=
      ENNReal.inv_mul_cancel hgamma_zero ENNReal.ofReal_ne_top
    rw [← mul_assoc, hcancel, one_mul]
    simp only [edist_dist, Real.dist_eq, zero_sub, abs_neg]

private def gaussianEnergy (μ : Measure ℝ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (-a * (x - y) ^ 2)) ∂μ ∂μ

private lemma gaussianEnergy_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 ≤ a) : gaussianEnergy μ a ≤ 1 := by
  calc
    gaussianEnergy μ a ≤ ∫⁻ _x : ℝ, ∫⁻ _y : ℝ, (1 : ℝ≥0∞) ∂μ ∂μ := by
      refine lintegral_mono fun x ↦ lintegral_mono fun y ↦ ?_
      rw [ENNReal.ofReal_le_one]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg (x - y)))
    _ = 1 := by simp

private lemma integrable_gaussian_kernel_prod (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 ≤ a) : Integrable (fun z : ℝ × ℝ ↦
      Real.exp (-a * (z.1 - z.2) ^ 2)) (μ.prod μ) := by
  refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa using Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
      (sq_nonneg (z.1 - z.2)))

private lemma gaussianEnergy_eq_ofReal_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 ≤ a) : gaussianEnergy μ a = ENNReal.ofReal
      (∫ x : ℝ, ∫ y : ℝ, Real.exp (-a * (x - y) ^ 2) ∂μ ∂μ) := by
  have hint := integrable_gaussian_kernel_prod μ ha
  have hmeas : AEMeasurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal
      (Real.exp (-a * (z.1 - z.2) ^ 2))) (μ.prod μ) := by
    fun_prop
  rw [gaussianEnergy, lintegral_lintegral hmeas]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)]
  rw [integral_prod _ hint]

private lemma gaussianEnergy_eq_ofReal_fourier_gaussian
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a : ℝ} (ha : 0 < a) :
    gaussianEnergy μ a = ENNReal.ofReal
      (Real.sqrt (Real.pi / a) *
        ∫ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
          (fun _ ↦ (1 : ℂ)) ξ‖ ^ 2 *
            Real.exp (-Real.pi * (Real.pi / a) * ξ ^ 2)) := by
  rw [gaussianEnergy_eq_ofReal_integral μ ha.le]
  congr 1
  let b := Real.pi / a
  have hb : 0 < b := div_pos Real.pi_pos ha
  have hsqrt : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
  have h := integral_norm_fourier_sq_mul_gaussian μ hb
  have hcoef : -Real.pi / b = -a := by
    dsimp [b]
    field_simp
  rw [hcoef] at h
  have h' : 1 / Real.sqrt b *
      (∫ x : ℝ, ∫ y : ℝ, Real.exp (-a * (x - y) ^ 2) ∂μ ∂μ) =
      ∫ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
        (fun _ ↦ (1 : ℂ)) ξ‖ ^ 2 * Real.exp (-Real.pi * b * ξ ^ 2) := by
    simpa only [integral_const_mul] using h.symm
  calc
    (∫ x : ℝ, ∫ y : ℝ, Real.exp (-a * (x - y) ^ 2) ∂μ ∂μ) =
        Real.sqrt b * (1 / Real.sqrt b *
          ∫ x : ℝ, ∫ y : ℝ, Real.exp (-a * (x - y) ^ 2) ∂μ ∂μ) := by
      field_simp
    _ = Real.sqrt b * ∫ ξ : ℝ,
        ‖Fourier.fourierIntegral Real.fourierChar μ
          (fun _ ↦ (1 : ℂ)) ξ‖ ^ 2 * Real.exp (-Real.pi * b * ξ ^ 2) := by
      rw [h']
    _ = _ := rfl

private lemma gaussian_scale_rpow {a t : ℝ} (ha : 0 < a) :
    Real.sqrt (Real.pi / a) *
        (Real.pi * (Real.pi / a)) ^ (-(-t + 1) / 2) =
      (Real.sqrt Real.pi * (Real.pi ^ 2) ^ (-(-t + 1) / 2)) *
        a ^ (-t / 2) := by
  have hsqrtdiv : Real.sqrt (Real.pi / a) =
      Real.sqrt Real.pi * a ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow Real.pi_pos.le ha.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg ha.le]
    rw [Real.sqrt_eq_rpow]
  have hpowdiv : (Real.pi * (Real.pi / a)) ^ (-(-t + 1) / 2) =
      (Real.pi ^ 2) ^ (-(-t + 1) / 2) *
        a ^ (-(-(-t + 1) / 2)) := by
    rw [show Real.pi * (Real.pi / a) = Real.pi ^ 2 / a by ring]
    rw [Real.div_rpow (sq_nonneg Real.pi) ha.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg ha.le]
  rw [hsqrtdiv, hpowdiv]
  rw [mul_assoc, mul_left_comm (a ^ (-(1 / 2 : ℝ))), ← mul_assoc]
  rw [← Real.rpow_add ha]
  congr 2
  ring

private lemma exists_gaussianEnergy_decay_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] {C t : ℝ}
    (hC : 0 < C) (ht : 0 < t) (ht₁ : t < 1)
    (hdecay : ∀ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
      (fun _ ↦ (1 : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-t / 2)) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 1 ≤ a →
      gaussianEnergy μ a ≤ ENNReal.ofReal (D * a ^ (-t / 2)) := by
  let D := Real.sqrt Real.pi * (Real.pi ^ 2) ^ (-(-t + 1) / 2) *
    C ^ 2 * Real.Gamma ((-t + 1) / 2)
  have hD : 0 < D := mul_pos
    (mul_pos (mul_pos (Real.sqrt_pos.2 Real.pi_pos)
      (Real.rpow_pos_of_pos (sq_pos_of_pos Real.pi_pos) _)) (sq_pos_of_pos hC))
    (Real.Gamma_pos_of_pos (by linarith))
  refine ⟨D, hD, fun a ha ↦ ?_⟩
  have ha_pos : 0 < a := zero_lt_one.trans_le ha
  rw [gaussianEnergy_eq_ofReal_fourier_gaussian μ ha_pos]
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.sqrt (Real.pi / a) *
        (∫ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
          (fun _ ↦ (1 : ℂ)) ξ‖ ^ 2 *
            Real.exp (-Real.pi * (Real.pi / a) * ξ ^ 2)) ≤
        Real.sqrt (Real.pi / a) *
          (C ^ 2 * (2 * ((Real.pi * (Real.pi / a)) ^ (-(-t + 1) / 2) *
            (1 / 2) * Real.Gamma ((-t + 1) / 2)))) := by
      gcongr
      exact integral_norm_fourier_sq_mul_gaussian_le μ ht ht₁
        (div_pos Real.pi_pos ha_pos) hdecay
    _ = D * a ^ (-t / 2) := by
      rw [show Real.sqrt (Real.pi / a) *
          (C ^ 2 * (2 * ((Real.pi * (Real.pi / a)) ^ (-(-t + 1) / 2) *
            (1 / 2) * Real.Gamma ((-t + 1) / 2)))) =
          (Real.sqrt (Real.pi / a) *
            (Real.pi * (Real.pi / a)) ^ (-(-t + 1) / 2)) *
              C ^ 2 * Real.Gamma ((-t + 1) / 2) by ring]
      rw [gaussian_scale_rpow ha_pos]
      dsimp [D]
      ring

private lemma lintegral_prod_laplace_kernel_eq (μ : Measure ℝ) [SFinite μ]
    {a d : ℝ} (ha : 0 < a) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal
      (a ^ (d / 2 - 1) * Real.exp (-(z.1 - z.2) ^ 2 * a)) ∂μ.prod μ) =
      ENNReal.ofReal (a ^ (d / 2 - 1)) * gaussianEnergy μ a := by
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
  rw [lintegral_const_mul]
  · rw [lintegral_prod]
    · congr 1
      unfold gaussianEnergy
      refine lintegral_congr fun x ↦ lintegral_congr fun y ↦ ?_
      congr 2
      ring
    · fun_prop
  · fun_prop

private def rieszPotential (μ : Measure ℝ) (d x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, edist x y ^ (-d) ∂μ

private lemma measurable_rieszPotential (μ : Measure ℝ) [SFinite μ] (d : ℝ) :
    Measurable (rieszPotential μ d) := by
  exact (measurable_edist.pow_const (-d)).lintegral_prod_right

private def rieszEnergy (μ : Measure ℝ) (d : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, rieszPotential μ d x ∂μ

private lemma rieszEnergy_eq_lintegral_gaussianEnergy
    (μ : Measure ℝ) [IsFiniteMeasure μ] {d : ℝ} (hd : 0 < d) :
    rieszEnergy μ d = (ENNReal.ofReal (Real.Gamma (d / 2)))⁻¹ *
      ∫⁻ a in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (a ^ (d / 2 - 1)) * gaussianEnergy μ a := by
  have hkernel : AEMeasurable (fun z : ℝ × ℝ ↦ edist z.1 z.2 ^ (-d)) (μ.prod μ) := by
    fun_prop
  simp only [rieszEnergy, rieszPotential]
  rw [lintegral_lintegral hkernel]
  simp_rw [riesz_kernel_eq_lintegral hd]
  rw [lintegral_const_mul]
  · congr 1
    rw [lintegral_lintegral_swap]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun a ha ↦ ?_
      exact lintegral_prod_laplace_kernel_eq μ ha
    · fun_prop
  · fun_prop

private lemma lintegral_riesz_scale_ne_top_of_decay
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {C t d : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hdt : d < t) (ht₁ : t < 1)
    (hdecay : ∀ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
      (fun _ ↦ (1 : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-t / 2)) :
    (∫⁻ a in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a ^ (d / 2 - 1)) * gaussianEnergy μ a) ≠ ∞ := by
  obtain ⟨D, hD, hfarBound⟩ :=
    exists_gaussianEnergy_decay_bound μ hC (lt_trans hd hdt) ht₁ hdecay
  have hnearInt : IntegrableOn (fun a : ℝ ↦ a ^ (d / 2 - 1))
      (Set.Ioc 0 1) := by
    have h := (integrableOn_abs_rpow_near_zero
      (by linarith : -1 < d / 2 - 1)).mono_set
        (show Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc (-1) 1 by
          intro a ha
          exact ⟨(show -1 ≤ a by linarith [ha.1]), ha.2⟩)
    refine h.congr_fun (fun a ha ↦ ?_) measurableSet_Ioc
    change |a| ^ (d / 2 - 1) = a ^ (d / 2 - 1)
    rw [abs_of_pos ha.1]
  have hfarInt : IntegrableOn (fun a : ℝ ↦ D * a ^ ((d - t) / 2 - 1))
      (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : (d - t) / 2 - 1 < -1)
      zero_lt_one).const_mul D
  have hnearTop : (∫⁻ a in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (a ^ (d / 2 - 1))) ≠ ∞ := by
    exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
          exact Real.rpow_nonneg ha.1.le _)).mpr hnearInt
  have hfarTop : (∫⁻ a in Set.Ioi (1 : ℝ),
      ENNReal.ofReal (D * a ^ ((d - t) / 2 - 1))) ≠ ∞ := by
    exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
          exact mul_nonneg hD.le (Real.rpow_nonneg (zero_lt_one.trans ha).le _))).mpr hfarInt
  have hnear : (∫⁻ a in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (a ^ (d / 2 - 1)) * gaussianEnergy μ a) ≤
      ∫⁻ a in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (a ^ (d / 2 - 1)) := by
    refine setLIntegral_mono (by fun_prop) fun a ha ↦ ?_
    simpa using mul_le_mul_right (gaussianEnergy_le_one μ ha.1.le)
      (ENNReal.ofReal (a ^ (d / 2 - 1)))
  have hfar : (∫⁻ a in Set.Ioi (1 : ℝ),
      ENNReal.ofReal (a ^ (d / 2 - 1)) * gaussianEnergy μ a) ≤
      ∫⁻ a in Set.Ioi (1 : ℝ),
        ENNReal.ofReal (D * a ^ ((d - t) / 2 - 1)) := by
    refine setLIntegral_mono (by fun_prop) fun a ha ↦ ?_
    have ha_pos : 0 < a := zero_lt_one.trans ha
    calc
      ENNReal.ofReal (a ^ (d / 2 - 1)) * gaussianEnergy μ a ≤
          ENNReal.ofReal (a ^ (d / 2 - 1)) *
            ENNReal.ofReal (D * a ^ (-t / 2)) :=
        mul_le_mul_right (hfarBound a ha.le) _
      _ = ENNReal.ofReal (D * a ^ ((d - t) / 2 - 1)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha_pos.le _)]
        congr 1
        rw [mul_left_comm, ← Real.rpow_add ha_pos]
        congr 1
        ring_nf
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext a
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ha
      rcases le_total a 1 with ha1 | ha1
      · exact Or.inl ⟨ha, ha1⟩
      · rcases eq_or_lt_of_le ha1 with rfl | ha1
        · exact Or.inl ⟨ha, le_rfl⟩
        · exact Or.inr ha1
    · rintro (ha | ha) <;> linarith
  rw [hsplit]
  refine ne_of_lt ((lintegral_union_le _ _ _).trans_lt ?_)
  exact (add_le_add hnear hfar).trans_lt
    ((ENNReal.add_lt_top).2
      ⟨lt_top_iff_ne_top.mpr hnearTop, lt_top_iff_ne_top.mpr hfarTop⟩)

private lemma measure_le_rieszPotential_mul_ediam (μ : Measure ℝ) [SFinite μ]
    {d : ℝ} (hd : 0 < d) {x : ℝ} {S : Set ℝ} (hx : x ∈ S)
    (hdiam : Metric.ediam S ≤ 1) (hpotential : rieszPotential μ d x ≠ ∞) :
    μ S ≤ rieszPotential μ d x * Metric.ediam S ^ d := by
  let r := Metric.ediam S
  have hr_top : r ≠ ∞ := ne_of_lt (hdiam.trans_lt (by simp))
  have hkernel : Measurable (fun y : ℝ ↦ edist x y ^ (-d)) :=
    measurable_edist_right.pow_const (-d)
  by_cases hr_zero : r = 0
  · have hS : S = {x} := by
      have hsub := Metric.ediam_eq_zero_iff.mp hr_zero
      ext y
      exact ⟨fun hy ↦ hsub hy hx, fun hy ↦ hy ▸ hx⟩
    have hnull : μ {y | edist x y ^ (-d) = ∞} = 0 :=
      measure_eq_top_of_lintegral_ne_top hkernel.aemeasurable hpotential
    have hxnull : μ {x} = 0 := by
      refine measure_mono_null ?_ hnull
      intro y hy
      subst y
      simpa using ENNReal.zero_rpow_of_neg (neg_neg_of_pos hd)
    simp [hS, hxnull, ENNReal.zero_rpow_of_pos hd]
  · have hr_pos : 0 < r := bot_lt_iff_ne_bot.mpr hr_zero
    have hpoint : ∀ y ∈ S, 1 ≤ r ^ d * edist x y ^ (-d) := by
      intro y hy
      have he : edist x y ≤ r := Metric.edist_le_ediam_of_mem hx hy
      have hrpow_pos : 0 < r ^ d := ENNReal.rpow_pos hr_pos hr_top
      have hrpow_top : r ^ d ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hd.le hr_top
      calc
        1 = r ^ d * (r ^ d)⁻¹ := (ENNReal.mul_inv_cancel hrpow_pos.ne' hrpow_top).symm
        _ ≤ r ^ d * (edist x y ^ d)⁻¹ :=
          mul_le_mul_right ((ENNReal.inv_le_inv).mpr (ENNReal.rpow_le_rpow he hd.le)) _
        _ = r ^ d * edist x y ^ (-d) := by rw [ENNReal.rpow_neg]
    have hmeas : Measurable (fun y : ℝ ↦ r ^ d * edist x y ^ (-d)) :=
      measurable_const.mul hkernel
    have hmeasure := meas_le_lintegral₀ (hmeas.aemeasurable (μ := μ)) hpoint
    rw [lintegral_const_mul _ hkernel] at hmeasure
    simpa only [rieszPotential, mul_comm] using hmeasure

private lemma exists_pos_measure_inter_le_of_lintegral_ne_top
    (μ : Measure ℝ) {K : Set ℝ} (hK : μ K ≠ 0) (P : ℝ → ℝ≥0∞)
    (hP : Measurable P) (hfinite : (∫⁻ x, P x ∂μ) ≠ ∞) :
    ∃ n : ℕ, 0 < μ (K ∩ {x | P x ≤ n}) := by
  have htop : μ {x | P x = ∞} = 0 :=
    measure_eq_top_of_lintegral_ne_top hP.aemeasurable hfinite
  have hUnion : μ (⋃ n : ℕ, K ∩ {x | P x ≤ n}) ≠ 0 := by
    intro hzero
    apply hK
    refine measure_mono_null ?_ (measure_union_null hzero htop)
    intro x hx
    by_cases hPx : P x = ∞
    · exact Set.mem_union_right _ hPx
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hPx
      exact Set.mem_union_left _ (Set.mem_iUnion.2 ⟨n, hx, hn.le⟩)
  exact exists_measure_pos_of_not_measure_iUnion_null hUnion

private lemma le_dimH_of_mass_bound (μ : Measure ℝ) {K : Set ℝ} (hK : μ K ≠ 0)
    {d : NNReal} {C ε : ℝ≥0∞} (hC : C ≠ 0) (hCtop : C ≠ ∞) (hε : 0 < ε)
    (hbound : ∀ S : Set ℝ, Metric.ediam S ≤ ε →
      μ S ≤ C * Metric.ediam S ^ (d : ℝ)) : (d : ℝ≥0∞) ≤ dimH K := by
  have hdom : C⁻¹ • μ ≤ Measure.hausdorffMeasure d := by
    refine Measure.le_hausdorffMeasure d (C⁻¹ • μ) ε hε ?_
    intro S hS
    simpa [Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hC hCtop] using mul_le_mul_right (hbound S hS) C⁻¹
  refine le_dimH_of_hausdorffMeasure_ne_zero ?_
  exact ne_of_gt ((ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hCtop) hK).trans_le (hdom K))

private lemma le_dimH_of_finite_potential (μ : Measure ℝ) {K : Set ℝ}
    (hK : μ K ≠ 0) (hKm : MeasurableSet K) {d : NNReal}
    (P : ℝ → ℝ≥0∞) (hP : Measurable P) (hfinite : (∫⁻ x, P x ∂μ) ≠ ∞)
    (hlocal : ∀ x ∈ K, P x ≠ ∞ → ∀ S : Set ℝ, x ∈ S →
      Metric.ediam S ≤ 1 → μ S ≤ P x * Metric.ediam S ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimH K := by
  obtain ⟨n, hn⟩ :=
    exists_pos_measure_inter_le_of_lintegral_ne_top μ hK P hP hfinite
  let E : Set ℝ := K ∩ {x | P x ≤ n}
  have hEm : MeasurableSet E := hKm.inter (hP measurableSet_Iic)
  have hrestrict : (μ.restrict E) E ≠ 0 := by
    rw [Measure.restrict_apply' hEm, Set.inter_self]
    exact hn.ne'
  have hmass : ∀ S : Set ℝ, Metric.ediam S ≤ (1 : ℝ≥0∞) →
      (μ.restrict E) S ≤ (n + 1 : ℕ) * Metric.ediam S ^ (d : ℝ) := by
    intro S hS
    rw [Measure.restrict_apply' hEm]
    by_cases hSE : (S ∩ E).Nonempty
    · obtain ⟨x, hxS, hxE⟩ := hSE
      have hxP : P x ≠ ∞ := ne_of_lt (hxE.2.trans_lt (by simp))
      calc
        μ (S ∩ E) ≤ P x * Metric.ediam (S ∩ E) ^ (d : ℝ) :=
          hlocal x hxE.1 hxP (S ∩ E) ⟨hxS, hxE⟩
            ((Metric.ediam_mono Set.inter_subset_left).trans hS)
        _ ≤ (n + 1 : ℕ) * Metric.ediam S ^ (d : ℝ) := by
          gcongr
          · exact hxE.2.trans (by exact_mod_cast Nat.le_succ n)
          · exact Set.inter_subset_left
    · rw [Set.not_nonempty_iff_eq_empty.mp hSE, measure_empty]
      exact bot_le
  exact (le_dimH_of_mass_bound (μ.restrict E) hrestrict (d := d)
    (C := (n + 1 : ℕ)) (ε := 1) (by simp) (by simp) zero_lt_one hmass).trans
      (dimH_mono Set.inter_subset_left)

private lemma le_dimH_of_finite_rieszEnergy (μ : Measure ℝ) [IsFiniteMeasure μ]
    {K : Set ℝ} (hK : μ K ≠ 0) (hKm : MeasurableSet K) {d : NNReal}
    (hd : 0 < d) (henergy : rieszEnergy μ d ≠ ∞) :
    (d : ℝ≥0∞) ≤ dimH K := by
  refine le_dimH_of_finite_potential μ hK hKm (rieszPotential μ d)
    (measurable_rieszPotential μ d) henergy ?_
  intro x _ hxfinite S hxS hdiam
  exact measure_le_rieszPotential_mul_ediam μ (by exact_mod_cast hd) hxS hdiam hxfinite

private lemma finite_rieszEnergy_of_decay
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {C t d : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hdt : d < t) (ht₁ : t < 1)
    (hdecay : ∀ ξ : ℝ, ‖Fourier.fourierIntegral Real.fourierChar μ
      (fun _ ↦ (1 : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-t / 2)) :
    rieszEnergy μ d ≠ ∞ := by
  rw [rieszEnergy_eq_lintegral_gaussianEnergy μ hd]
  apply ENNReal.mul_ne_top
  · rw [ENNReal.inv_ne_top]
    exact (ENNReal.ofReal_pos.mpr
      (Real.Gamma_pos_of_pos (by positivity : 0 < d / 2))).ne'
  · exact lintegral_riesz_scale_ne_top_of_decay μ hC hd hdt ht₁ hdecay

private lemma ofReal_fourierDim_le_dimH
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {K : Set ℝ}
    (hKm : MeasurableSet K) (hK : μ Kᶜ = 0) :
    ENNReal.ofReal (fourierDim μ) ≤ dimH K := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro d hd hdF
  have hdF' : (d : ℝ) < fourierDim μ := ENNReal.coe_lt_ofReal.mp hdF
  let t := ((d : ℝ) + fourierDim μ) / 2
  have hdt : (d : ℝ) < t := by dsimp [t]; linarith
  have htF : t < fourierDim μ := by dsimp [t]; linarith
  have ht₁ : t < 1 := htF.trans_le (fourierDim_le_one μ)
  obtain ⟨C, hC, hdecay⟩ := exists_fourier_decay_of_lt_fourierDim μ htF
  have henergy : rieszEnergy μ (d : ℝ) ≠ ∞ :=
    finite_rieszEnergy_of_decay μ hC (by exact_mod_cast hd) hdt ht₁ hdecay
  have hKpos : μ K ≠ 0 := by
    rw [(prob_compl_eq_zero_iff hKm).mp hK]
    exact one_ne_zero
  exact le_dimH_of_finite_rieszEnergy μ hKpos hKm hd henergy

private lemma setFourierDim_le_dimH_toReal
    (μ : Measure ℝ) [hμ : IsProbabilityMeasure μ] {K : Set ℝ}
    (hKm : MeasurableSet K) (hK : μ Kᶜ = 0) :
    setFourierDim K ≤ (dimH K).toReal := by
  have hdim_le : dimH K ≤ 1 :=
    (dimH_mono (Set.subset_univ K)).trans_eq Real.dimH_univ
  have hdimtop : dimH K ≠ ∞ := ne_of_lt (hdim_le.trans_lt (by simp))
  apply csSup_le
  · exact ⟨fourierDim μ, μ, hμ, hK, rfl⟩
  · rintro _t ⟨ν, hν, hνK, rfl⟩
    letI := hν
    exact (ENNReal.ofReal_le_iff_le_toReal hdimtop).mp
      (ofReal_fourierDim_le_dimH ν hKm hνK)

private lemma ofReal_setFourierDim_le_dimH
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {K : Set ℝ}
    (hKm : MeasurableSet K) (hK : μ Kᶜ = 0) :
    ENNReal.ofReal (setFourierDim K) ≤ dimH K := by
  have hdim_le : dimH K ≤ 1 :=
    (dimH_mono (Set.subset_univ K)).trans_eq Real.dimH_univ
  have hdimtop : dimH K ≠ ∞ := ne_of_lt (hdim_le.trans_lt (by simp))
  exact (ENNReal.ofReal_le_iff_le_toReal hdimtop).mpr
    (setFourierDim_le_dimH_toReal μ hKm hK)

private lemma is_salem_of_measure
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {K : Set ℝ} {s : ℝ}
    (hKm : MeasurableSet K) (hK : μ Kᶜ = 0)
    (hfourier : fourierDim μ = s) (hhausdorff : dimH K = ENNReal.ofReal s) :
    is_salem K := by
  rw [is_salem]
  apply le_antisymm (ofReal_setFourierDim_le_dimH μ hKm hK)
  rw [hhausdorff, ← hfourier]
  exact ENNReal.ofReal_le_ofReal (fourierDim_le_setFourierDim μ hK)

private def constructionLength (s : ℝ) (n : ℕ) : ℕ :=
  n + 1 + ⌈2 / s⌉₊

private def constructionRank (s : ℝ) (n : ℕ) : ℕ :=
  if s = 1 then n + 2 else ⌊s * constructionLength s n⌋₊

private lemma constructionLength_pos (s : ℝ) (n : ℕ) :
    0 < constructionLength s n := by
  exact Nat.add_pos_left (Nat.succ_pos n) _

private lemma constructionLength_mul_lower {s : ℝ} (hs : 0 < s) (n : ℕ) :
    2 ≤ s * constructionLength s n := by
  have hceil : 2 ≤ s * (⌈2 / s⌉₊ : ℝ) := by
    simpa only [mul_comm s] using (div_le_iff₀ hs).mp (Nat.le_ceil (2 / s))
  exact hceil.trans (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Nat.le_add_left ⌈2 / s⌉₊ (n + 1))) hs.le)

private lemma constructionRank_two_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    2 ≤ constructionRank s n := by
  exact if h : s = 1 then by simp [constructionRank, h] else by
    simpa only [constructionRank, if_neg h] using Nat.le_floor (constructionLength_mul_lower hs n)

private lemma constructionRank_pos {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 < constructionRank s n := by
  exact Nat.zero_lt_two.trans_le (constructionRank_two_le hs n)

private lemma constructionRank_lt {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    constructionRank s n < constructionLength s n := by
  by_cases h : s = 1
  · simp [h, constructionRank, constructionLength]
  · simpa only [constructionRank, if_neg h] using
      (Nat.floor_lt (mul_nonneg hs.le (Nat.cast_nonneg _))).mpr
        (mul_lt_of_lt_one_left (Nat.cast_pos.mpr (constructionLength_pos s n))
          (lt_of_le_of_ne hs₁ h))

private lemma constructionRank_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (constructionRank s n : ℝ) ≤ s * constructionLength s n := by
  by_cases h : s = 1
  · simp [h, constructionRank, constructionLength]
  · simpa only [constructionRank, if_neg h] using
      Nat.floor_le (mul_nonneg hs.le (Nat.cast_nonneg (constructionLength s n)))

private lemma constructionRank_lower (s : ℝ) (n : ℕ) :
    s * constructionLength s n - 1 ≤ (constructionRank s n : ℝ) := by
  by_cases h : s = 1
  · simp [h, constructionRank, constructionLength, add_sub_assoc]
  · simpa only [constructionRank, if_neg h] using
      (Nat.sub_one_lt_floor (s * constructionLength s n)).le

private def constructionRatio (s : ℝ) (n : ℕ) : ℝ :=
  (constructionRank s n : ℝ) / constructionLength s n

private def constructionExponent (s : ℝ) (n : ℕ) : ℝ :=
  ((constructionRank s n : ℝ) - 1) / constructionLength s n

private def constructionDegree (s : ℝ) (n : ℕ) : ℕ :=
  1 + ⌈((constructionLength s n - constructionRank s n : ℕ) : ℝ) /
    constructionRank s n⌉₊

private lemma tendsto_constructionLength (s : ℝ) :
    Tendsto (fun n ↦ (constructionLength s n : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp
    ((tendsto_add_atTop_nat ⌈2 / s⌉₊).comp (tendsto_add_atTop_nat 1))

private lemma constructionRatio_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    constructionRatio s n ≤ s := by
  exact (div_le_iff₀ (Nat.cast_pos.mpr (constructionLength_pos s n))).mpr
    (constructionRank_le hs n)

private lemma constructionRatio_error (s : ℝ) (n : ℕ) :
    s - constructionRatio s n ≤ 1 / (constructionLength s n : ℝ) := by
  change s - (constructionRank s n : ℝ) / constructionLength s n ≤ _
  exact (le_div_iff₀ (Nat.cast_pos.mpr (constructionLength_pos s n))).mpr (by
    nlinarith [constructionRank_lower s n, div_mul_cancel₀
      (constructionRank s n : ℝ)
      (Nat.cast_ne_zero.mpr (constructionLength_pos s n).ne')])

private lemma constructionExponent_pos {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 < constructionExponent s n := by
  exact div_pos (sub_pos.mpr (by
    exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 1 < 2) (constructionRank_two_le hs n))))
    (Nat.cast_pos.mpr (constructionLength_pos s n))

private lemma tendsto_constructionRatio {s : ℝ} (hs : 0 < s) :
    Tendsto (constructionRatio s) atTop (𝓝 s) := by
  have hgap : Tendsto (fun n ↦ s - constructionRatio s n) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ sub_nonneg.mpr (constructionRatio_le hs n))
      (constructionRatio_error s)
      (by simpa only [one_div, Pi.inv_apply, one_mul] using
        (tendsto_constructionLength s).inv_tendsto_atTop.const_mul (1 : ℝ))
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := s)).sub hgap

private lemma tendsto_constructionExponent {s : ℝ} (hs : 0 < s) :
    Tendsto (constructionExponent s) atTop (𝓝 s) := by
  change Tendsto (fun n ↦ ((constructionRank s n : ℝ) - 1) / constructionLength s n)
    atTop (𝓝 s)
  simpa only [constructionRatio, sub_div, one_div, Pi.inv_apply, sub_zero] using
    (tendsto_constructionRatio hs).sub (tendsto_constructionLength s).inv_tendsto_atTop

private lemma constructionDegree_two_le {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    2 ≤ constructionDegree s n := by
  simpa only [constructionDegree, Nat.add_comm 1, Nat.succ_eq_add_one] using
    Nat.succ_le_succ (Nat.ceil_pos.mpr (div_pos (G₀ := ℝ)
    (Nat.cast_pos.mpr (Nat.sub_pos_of_lt (constructionRank_lt hs hs₁ n)))
    (Nat.cast_pos.mpr (constructionRank_pos hs n))))

private lemma constructionLength_le_rank_mul_degree {s : ℝ} (hs : 0 < s)
    (hs₁ : s ≤ 1) (n : ℕ) :
    constructionLength s n ≤ constructionRank s n * constructionDegree s n := by
  have hceil := (div_le_iff₀ (Nat.cast_pos.mpr (constructionRank_pos hs n))).mp
    (Nat.le_ceil (((constructionLength s n - constructionRank s n : ℕ) : ℝ) /
      constructionRank s n))
  have hnat : constructionLength s n - constructionRank s n ≤
      ⌈((constructionLength s n - constructionRank s n : ℕ) : ℝ) /
        constructionRank s n⌉₊ * constructionRank s n := by exact_mod_cast hceil
  simpa only [constructionDegree, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.add_comm,
    Nat.mul_comm, Nat.sub_add_cancel (constructionRank_lt hs hs₁ n).le] using
      Nat.add_le_add_right hnat (constructionRank s n)

private lemma constructionExponent_gap (s : ℝ) (n : ℕ) :
    (constructionRank s n : ℝ) / 2 -
      constructionLength s n * constructionExponent s n / 2 =
        1 / 2 := by
  dsimp only [constructionExponent]
  field_simp [(constructionLength_pos s n).ne']
  ring

private def constructionPrimeCondition (s : ℝ) (n P p : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ constructionDegree s n < p ∧
    P ^ (n + 1) < p ^ constructionLength s n ∧
    (constructionDegree s n - 1 : ℝ) * (2 * Real.log (2 * p)) ^ constructionLength s n ≤
      (p : ℝ) ^ (1 / 2 : ℝ)

private lemma eventually_constructionPrime_cost {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (n : ℕ) :
    ∀ᶠ p : ℕ in atTop,
      (constructionDegree s n - 1 : ℝ) * (2 * Real.log (2 * p)) ^ constructionLength s n ≤
        (p : ℝ) ^ (1 / 2 : ℝ) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_mul_mask_log_pow_le_rpow (sub_nonneg.mpr
      (by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2)
        (constructionDegree_two_le hs hs₁ n)))) (constructionLength s n) (by norm_num))

private lemma exists_constructionPrime {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (n P : ℕ) :
    ∃ p, constructionPrimeCondition s n P p := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_constructionPrime_cost hs hs₁ n)
  obtain ⟨p, hp, hpprime⟩ := Nat.exists_infinite_primes
    (max M (P ^ (n + 1) + constructionDegree s n + 3))
  exact ⟨p, hpprime, hpprime.odd_of_ne_two (by omega), by omega,
    (show P ^ (n + 1) < p by omega).trans_le (Nat.le_pow (constructionLength_pos s n)),
    hM p (by omega)⟩

private def constructionPrime (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_constructionPrime hs hs₁ n
    (∏ j : Fin n, constructionPrime s hs hs₁ j ^ constructionLength s j))
termination_by n

private lemma constructionPrime_spec (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    constructionPrimeCondition s n
      (∏ j : Fin n, constructionPrime s hs hs₁ j ^ constructionLength s j)
      (constructionPrime s hs hs₁ n) := by
  classical
  rw [constructionPrime.eq_def]
  exact Nat.find_spec (exists_constructionPrime hs hs₁ n
    (∏ j : Fin n, constructionPrime s hs hs₁ j ^ constructionLength s j))

private instance constructionPrime_isPrime (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    Fact (constructionPrime s hs hs₁ n).Prime :=
  ⟨(constructionPrime_spec s hs hs₁ n).1⟩

private lemma constructionPrime_log_cost (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    let p := constructionPrime s hs hs₁ n
    (constructionDegree s n - 1 : ℝ) * (2 * Real.log (2 * p)) ^ constructionLength s n ≤
      (p : ℝ) ^ (1 / 2 : ℝ) := by
  exact (constructionPrime_spec s hs hs₁ n).2.2.2.2

private lemma norm_average_power_coordinates_le_of_le_mul {p r q d : ℕ}
    [Fact p.Prime] {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (hqd : q ≤ r * d)
    (hdp : d < p) {a : Fin q → ZMod p} (ha : a ≠ 0) :
    ‖((p ^ r : ℕ) : ℂ)⁻¹ * ∑ x : F, ZMod.stdAddChar
      (∑ j, a j * b.equivFun (x ^ (j.val / r + 1)) ⟨j.val % r, Nat.mod_lt _ hr⟩)‖ ≤
        ((d - 1 : ℕ) : ℝ) / Real.sqrt (p ^ r : ℕ) := by
  have hcard : Fintype.card F = p ^ r := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (fieldResidueEquiv b)
  have h := div_le_div_of_nonneg_right (norm_sum_power_coordinates_le_of_le_mul b hr hqd hdp ha)
    (Nat.cast_nonneg (p ^ r) : (0 : ℝ) ≤ _)
  rw [hcard, mul_div_assoc, Real.sqrt_div_self] at h
  simpa only [norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv, mul_comm] using h

private lemma norm_mask_powerDigitSet_sub_range_le_of_le_mul {p r m d : ℕ}
    [Fact p.Prime] {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (hqd : r + m ≤ r * d)
    (hdp : d < p) (ξ : ℝ) :
    ‖mask (powerDigitSet b hr m) ξ - mask (Finset.range (p ^ (r + m))) ξ‖ ≤
      (((d - 1 : ℕ) : ℝ) / Real.sqrt (p ^ r : ℕ)) *
        ∏ j : Fin (r + m), ∑ a : ZMod p,
          ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase ((p : ℝ) ^ j.val * ξ)) a‖ := by
  classical
  let w (a : Fin (r + m) → ZMod p) :=
    ∏ j, (p : ℂ)⁻¹ * ZMod.dft (digitPhase ((p : ℝ) ^ j.val * ξ)) (a j)
  let C : ℝ := ((d - 1 : ℕ) : ℝ) / Real.sqrt (p ^ r : ℕ)
  rw [mask_sub_range_eq_sum_nonlinear b hr ξ]
  calc
    _ ≤ ∑ a ∈ Finset.univ.filter (fun a ↦ a ∉ linearPhaseIndices p r (r + m)),
        ‖w a‖ * C := norm_sum_le_of_le _ fun a ha ↦ by
      have ha₀ : a ≠ 0 := fun hz ↦ (Finset.mem_filter.mp ha).2 (by simp [hz, linearPhaseIndices])
      exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left
        (norm_average_power_coordinates_le_of_le_mul b hr hqd hdp ha₀) (norm_nonneg _))
    _ ≤ ∑ a, ‖w a‖ * C := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun a _ _ ↦ mul_nonneg (norm_nonneg _) (by positivity))
    _ = _ := by
      rw [← Finset.sum_mul, mul_comm]
      simp only [w, norm_prod, Fintype.prod_sum, C]

private lemma prod_sum_norm_dft_digitPhase_le {p q : ℕ} [NeZero p]
    (hp : 2 ≤ p) (ξ : ℝ) :
    (∏ j : Fin q, ∑ a : ZMod p,
      ‖(p : ℂ)⁻¹ * ZMod.dft (digitPhase ((p : ℝ) ^ j.val * ξ)) a‖) ≤
        (2 * Real.log (2 * p)) ^ q := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod (s := Finset.univ) (fun j _ ↦ Finset.sum_nonneg
      (fun a _ ↦ norm_nonneg ((p : ℂ)⁻¹ * ZMod.dft (digitPhase ((p : ℝ) ^ j.val * ξ)) a)))
        (fun (j : Fin q) _ ↦ sum_norm_dft_digitPhase_le hp ((p : ℝ) ^ j.val * ξ))

private lemma norm_mask_powerDigitSet_sub_range_le_log_of_le_mul {p r m d : ℕ}
    [Fact p.Prime] {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r)
    (hqd : r + m ≤ r * d) (hdp : d < p) (ξ : ℝ) :
    ‖mask (powerDigitSet b hr m) ξ - mask (Finset.range (p ^ (r + m))) ξ‖ ≤
      (((d - 1 : ℕ) : ℝ) / Real.sqrt (p ^ r : ℕ)) *
        (2 * Real.log (2 * p)) ^ (r + m) := by
  exact (norm_mask_powerDigitSet_sub_range_le_of_le_mul b hr hqd hdp ξ).trans
    (mul_le_mul_of_nonneg_left
      (prod_sum_norm_dft_digitPhase_le (Fact.out : p.Prime).two_le ξ) (by positivity))

/-- A Moran construction with prescribed dimension, using least admissible odd primes. -/
def spectralMoranData (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) : Data :=
  galoisPowerMoranData (constructionPrime s hs hs₁) (constructionRank s)
    (fun n ↦ constructionLength s n - constructionRank s n) (constructionRank_pos hs)

private lemma spectralMoranData_base (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    (spectralMoranData s hs hs₁).base n =
      constructionPrime s hs hs₁ n ^ constructionLength s n := by
  change constructionPrime s hs hs₁ n ^
    (constructionRank s n + (constructionLength s n - constructionRank s n)) = _
  rw [Nat.add_sub_of_le (constructionRank_lt hs hs₁ n).le]

private lemma spectralMoranData_mask_error_raw (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (n : ℕ) (ξ : ℝ) :
    let p := constructionPrime s hs hs₁ n
    ‖mask ((spectralMoranData s hs hs₁).digits n) ξ -
      mask (Finset.range ((spectralMoranData s hs hs₁).base n)) ξ‖ ≤
        (constructionDegree s n - 1 : ℝ) *
          (2 * Real.log (2 * p)) ^ constructionLength s n *
            (p : ℝ) ^ (-(constructionRank s n : ℝ) / 2) := by
  letI : Fintype (GaloisField (constructionPrime s hs hs₁ n) (constructionRank s n)) :=
    Fintype.ofFinite _
  have h := norm_mask_powerDigitSet_sub_range_le_log_of_le_mul
    (galoisPowerBasis (constructionPrime s hs hs₁ n) (constructionRank s n)
      (constructionRank_pos hs n))
    (m := constructionLength s n - constructionRank s n) (constructionRank_pos hs n)
    (by simpa only [Nat.add_sub_of_le (constructionRank_lt hs hs₁ n).le] using
      constructionLength_le_rank_mul_degree hs hs₁ n)
    (constructionPrime_spec s hs hs₁ n).2.2.1 ξ
  simpa only [spectralMoranData, galoisPowerMoranData, powerMoranData,
    Nat.add_sub_of_le (constructionRank_lt hs hs₁ n).le,
    Nat.cast_sub (show 1 ≤ constructionDegree s n from
      (by norm_num : 1 ≤ 2).trans (constructionDegree_two_le hs hs₁ n)), Nat.cast_one,
    Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _),
    div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _), mul_right_comm,
    one_mul, neg_mul] using h

private lemma spectralMoranData_mask_error (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (n : ℕ) (ξ : ℝ) :
    let A := spectralMoranData s hs hs₁
    ‖mask (A.digits n) ξ - mask (Finset.range (A.base n)) ξ‖ ≤
      (A.base n : ℝ) ^ (-constructionExponent s n / 2) := by
  refine ((spectralMoranData_mask_error_raw s hs hs₁ n ξ).trans
    (mul_le_mul_of_nonneg_right (constructionPrime_log_cost s hs hs₁ n)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans_eq ?_
  rw [← Real.rpow_add (Nat.cast_pos.mpr (constructionPrime_spec s hs hs₁ n).1.pos),
    spectralMoranData_base, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
  exact congrArg ((constructionPrime s hs hs₁ n : ℝ) ^ ·)
    (by linarith [constructionExponent_gap s n])

private lemma construction_mask_cost_uniform (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {γ : ℝ} (hγs : γ < s / 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n,
      ((spectralMoranData s hs hs₁).base n : ℝ) ^ (-constructionExponent s n / 2) ≤
        C * ((spectralMoranData s hs hs₁).base n : ℝ) ^ (-γ) := by
  have hevent : ∀ᶠ n : ℕ in atTop,
      ((spectralMoranData s hs hs₁).base n : ℝ) ^ (γ - constructionExponent s n / 2) ≤ 1 := by
    filter_upwards [((tendsto_constructionExponent hs).div_const (2 : ℝ)).eventually
      (le_mem_nhds hγs)] with n hn using
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (Nat.one_le_of_lt ((spectralMoranData s hs hs₁).two_le_base n)))
        (sub_nonpos.mpr hn)
  obtain ⟨C, hC⟩ := (Filter.isBoundedUnder_of_eventually_le hevent).bddAbove_range
  refine ⟨max 1 C, le_max_left _ _, fun n ↦ ?_⟩
  simpa only [← Real.rpow_add (Nat.cast_pos.mpr (Nat.zero_lt_two.trans_le
      ((spectralMoranData s hs hs₁).two_le_base n))),
    show γ - constructionExponent s n / 2 + -γ = -constructionExponent s n / 2 by ring] using
    mul_le_mul_of_nonneg_right ((hC (Set.mem_range_self n)).trans (le_max_right 1 C))
      (Real.rpow_nonneg (Nat.cast_nonneg ((spectralMoranData s hs hs₁).base n)) (-γ))

private lemma spectralMoranData_mask_error_uniform (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {γ : ℝ} (hγs : γ < s / 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n ξ,
      ‖mask ((spectralMoranData s hs hs₁).digits n) ξ -
        mask (Finset.range ((spectralMoranData s hs hs₁).base n)) ξ‖ ≤
          C * ((spectralMoranData s hs hs₁).base n : ℝ) ^ (-γ) := by
  exact (construction_mask_cost_uniform s hs hs₁ hγs).imp fun C hC ↦
    ⟨hC.1, fun n ξ ↦ (spectralMoranData_mask_error s hs hs₁ n ξ).trans (hC.2 n)⟩

private lemma constructionExponent_le_one {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    constructionExponent s n ≤ 1 := by
  exact (div_le_one (Nat.cast_pos.mpr (constructionLength_pos s n))).mpr
    ((sub_le_self _ zero_le_one).trans (Nat.cast_le.mpr (constructionRank_lt hs hs₁ n).le))

private lemma spectralMoranData_scale_separation (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (n : ℕ) :
    let A := spectralMoranData s hs hs₁
    (∏ j ∈ Finset.range n, A.base j) ^ (n + 1) < A.base n := by
  simpa only [spectralMoranData_base, Fin.prod_univ_eq_prod_range
    (fun j ↦ constructionPrime s hs hs₁ j ^ constructionLength s j) n] using
    (constructionPrime_spec s hs hs₁ n).2.2.2.1

private lemma spectralMoranData_base_lt_succ (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    (spectralMoranData s hs hs₁).base n < (spectralMoranData s hs hs₁).base (n + 1) := by
  calc
    _ ≤ 2 ^ n * (spectralMoranData s hs hs₁).base n :=
      Nat.le_mul_of_pos_left _ (pow_pos (by decide) n)
    _ ≤ (spectralMoranData s hs hs₁).scale n :=
      (spectralMoranData s hs hs₁).two_pow_mul_base_le_scale n
    _ ≤ ((spectralMoranData s hs hs₁).scale n) ^ (n + 2) := Nat.le_pow (by omega)
    _ < _ := spectralMoranData_scale_separation s hs hs₁ (n + 1)

private lemma spectralMoranData_base_rpow_le_scale (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {γ : ℝ} (hγ : 0 ≤ γ) (n : ℕ) :
    let A := spectralMoranData s hs hs₁
    (A.base n : ℝ) ^ (-γ) ≤ (A.scale n : ℝ) ^ (-(γ * (n + 1) / (n + 2))) := by
  have hpower : ((spectralMoranData s hs hs₁).scale n : ℝ) ^
      (γ * (n + 1) / (n + 2)) ≤ ((spectralMoranData s hs hs₁).base n : ℝ) ^ γ := by
    simpa only [Data.scale, Finset.prod_range_succ, Nat.cast_mul] using
      mul_rpow_le_rpow_of_separation
        (by exact_mod_cast (spectralMoranData s hs hs₁).prefix_product_pos n)
        (Nat.cast_pos.mpr (Nat.zero_lt_two.trans_le
          ((spectralMoranData s hs hs₁).two_le_base n)))
        (by exact_mod_cast (spectralMoranData_scale_separation s hs hs₁ n).le)
        (show 0 ≤ γ - γ * (n + 1) / (n + 2) from sub_nonneg.mpr
          ((div_le_iff₀ (by positivity)).mpr (by nlinarith)))
        (show γ * (n + 1) / (n + 2) ≤
            (n + 1 : ℕ) * (γ - γ * (n + 1) / (n + 2)) from by
          have h := div_mul_cancel₀ (γ * (n + 1)) (by positivity : (n : ℝ) + 2 ≠ 0)
          push_cast
          nlinarith)
  simpa only [Data.scale, Real.rpow_neg (Nat.cast_nonneg _), one_div] using
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos
      (Nat.cast_pos.mpr ((spectralMoranData s hs hs₁).prefix_product_pos (n + 1))) _) hpower

private lemma eventually_constructionExponent_margin (s : ℝ) (hs : 0 < s)
    {a : ℝ} (ha : a < s / 2) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ constructionExponent s n / 2 - a ∧
      a ≤ (n + 1 : ℕ) * (constructionExponent s n / 2 - a) := by
  have hlim := ((tendsto_constructionExponent hs).div_const (2 : ℝ)).sub_const a
  exact (hlim.eventually (le_mem_nhds (sub_pos.mpr ha))).and
    ((Filter.Tendsto.atTop_mul_pos (sub_pos.mpr ha)
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)) hlim).eventually_ge_atTop a)

private lemma eventually_construction_mask_cost_le_scale (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {a : ℝ} (ha : a < s / 2) :
    let A := spectralMoranData s hs hs₁
    ∀ᶠ n : ℕ in atTop, (A.base n : ℝ) ^ (-constructionExponent s n / 2) ≤
      (A.scale n : ℝ) ^ (-a) := by
  intro A
  filter_upwards [eventually_constructionExponent_margin s hs ha] with n hn
  have hsep : ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) ^ (n + 1) ≤ A.base n := by
    exact_mod_cast (spectralMoranData_scale_separation s hs hs₁ n).le
  have hbase : 0 < (A.base n : ℝ) :=
    Nat.cast_pos.mpr (Nat.zero_lt_two.trans_le (A.two_le_base n))
  have hscale : 0 < (A.scale n : ℝ) := Nat.cast_pos.mpr (A.prefix_product_pos (n + 1))
  rw [neg_div, Real.rpow_neg hbase.le, Real.rpow_neg hscale.le,
    inv_le_inv₀ (Real.rpow_pos_of_pos hbase _) (Real.rpow_pos_of_pos hscale _)]
  simpa only [Data.scale, Finset.prod_range_succ, Nat.cast_mul] using
    mul_rpow_le_rpow_of_separation (by exact_mod_cast A.prefix_product_pos n)
      hbase hsep hn.1 hn.2

private lemma spectralMoranData_fourier_block_bound (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (ξ : ℝ) (n : ℕ) :
    let A := spectralMoranData s hs hs₁
    0 < ξ / A.scale n → ξ / A.scale n ≤ A.base (n + 1) / 2 →
      ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        ((A.base n : ℝ)⁻¹ + (A.base n : ℝ) ^ (-constructionExponent s n / 2)) /
          (2 * (ξ / A.scale n)) + (A.base (n + 1) : ℝ) ^ (-constructionExponent s (n + 1) / 2) := by
  intro A ht htN
  exact (norm_fourier_le_adjacent_masks A ξ n).trans
    (norm_adjacent_masks_le _ _ (A.digits_nonempty n)
      (Nat.zero_lt_two.trans_le (A.two_le_base n))
      (Nat.zero_lt_two.trans_le (A.two_le_base (n + 1))) ht htN
      (spectralMoranData_mask_error s hs hs₁ n _)
      (spectralMoranData_mask_error s hs hs₁ (n + 1) _))

private lemma inv_base_le_construction_mask_cost (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    let A := spectralMoranData s hs hs₁
    (A.base n : ℝ)⁻¹ ≤ (A.base n : ℝ) ^ (-constructionExponent s n / 2) := by
  simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ (spectralMoranData s hs hs₁).base n by
      exact_mod_cast (by norm_num : 1 ≤ 2).trans ((spectralMoranData s hs hs₁).two_le_base n))
    (by linarith [constructionExponent_le_one hs hs₁ n] : (-1 : ℝ) ≤ -constructionExponent s n / 2)

private lemma norm_mask_neg (B : Finset ℕ) (x : ℝ) :
    ‖mask B (-x)‖ = ‖mask B x‖ := by
  have h : mask B (-x) = starRingEnd ℂ (mask B x) := by
    simp only [mask, map_mul, map_inv₀, map_natCast, map_sum, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.ofReal_neg, neg_mul,
      map_neg, neg_neg]
  simpa only [h] using Complex.norm_conj (mask B x)

private lemma norm_mask_int_sub (B : Finset ℕ) (N : ℤ) (x : ℝ) :
    ‖mask B (N - x)‖ = ‖mask B x‖ := by
  simpa only [sub_eq_neg_add, mask_add_int] using norm_mask_neg B x

private lemma norm_adjacent_masks_reflect (B C : Finset ℕ) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    ‖mask B t * mask C (t / N)‖ =
      ‖mask B (N - t) * mask C ((N - t) / N)‖ := by
  simp only [norm_mul, show ((N : ℝ) - t) / N = 1 - t / N by
    rw [sub_div, div_self (Nat.cast_ne_zero.mpr hN.ne')],
    show ‖mask B (N - t)‖ = ‖mask B t‖ by simpa using norm_mask_int_sub B (N : ℤ) t,
    show ‖mask C (1 - t / N)‖ = ‖mask C (t / N)‖ by
      simpa using norm_mask_int_sub C 1 (t / N)]

private lemma norm_mask_range_near_one_le {Q : ℕ} (hQ : 2 ≤ Q) {a : ℝ}
    (ha : 1 / 2 ≤ a) (ha₁ : a ≤ 1) :
    ‖mask (Finset.range Q) (a / Q)‖ ≤ Real.pi * (1 - a) := by
  have hsin : |Real.sin (Real.pi * a)| ≤ Real.pi * (1 - a) := by
    simpa only [mul_sub, mul_one, Real.sin_pi_sub, abs_of_nonneg
      (show 0 ≤ Real.pi - Real.pi * a from sub_nonneg.mpr
        (mul_le_of_le_one_right Real.pi_pos.le ha₁))] using
        Real.abs_sin_le_abs (x := Real.pi * (1 - a))
  have h := norm_mask_range_scaled_mul_le_sin (by omega : 0 < Q)
    (by linarith : 0 ≤ a) (by
      have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith)
  nlinarith [norm_nonneg (mask (Finset.range Q) (a / Q))]

private lemma norm_adjacent_masks_mul_gap_le (B C : Finset ℕ) (hB : B.Nonempty)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) {ε δ u : ℝ}
    (hu : 0 ≤ u) (huN : u ≤ N / 2) (hε₁ : ε ≤ 1)
    (hε : ‖mask B u - mask (Finset.range M) u‖ ≤ ε)
    (hδ : ‖mask C (u / N) - mask (Finset.range N) (u / N)‖ ≤ δ) :
    ‖mask B u * mask C (u / N)‖ * u ≤ 1 + δ * u := by
  by_cases hu₀ : u = 0
  · simp [hu₀]
  · have h := norm_adjacent_masks_le B C hB hM hN (lt_of_le_of_ne hu (Ne.symm hu₀)) huN hε hδ
    have hmul := mul_le_mul_of_nonneg_right h hu
    have hM₁ : (M : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hM)
    have heq : (((M : ℝ)⁻¹ + ε) / (2 * u) + δ) * u =
        ((M : ℝ)⁻¹ + ε) / 2 + δ * u := by field_simp
    rw [heq] at hmul
    linarith

private lemma mul_le_of_gap_bounds {v w u N δ η : ℝ} (hv : 0 ≤ v) (hv₁ : v ≤ 1)
    (hN : 0 < N) (huN : u ≤ N) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hvu : v * u ≤ 1 + δ * u) (hw : w ≤ Real.pi * u / N + η) :
    v * w ≤ Real.pi / N + Real.pi * δ + η := by
  have hscaled := mul_le_mul_of_nonneg_left hvu Real.pi_pos.le
  have hδu := mul_le_mul_of_nonneg_left huN (mul_nonneg Real.pi_pos.le hδ)
  have hηv := mul_le_mul_of_nonneg_right hv₁ hη
  have hwv := mul_le_mul_of_nonneg_left hw hv
  have hN₀ := hN.ne'
  field_simp at hwv ⊢
  nlinarith [mul_le_mul_of_nonneg_right hηv hN.le]

private lemma norm_three_masks_upper_half_le (B C D : Finset ℕ)
    (hB : B.Nonempty) (hC : C.Nonempty) {M N Q : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hQ : 2 ≤ Q) {ε δ η t : ℝ}
    (ht : N / 2 ≤ t) (htN : t ≤ N) (hε₁ : ε ≤ 1)
    (hε : ‖mask B (N - t) - mask (Finset.range M) (N - t)‖ ≤ ε)
    (hδ : ‖mask C ((N - t) / N) - mask (Finset.range N) ((N - t) / N)‖ ≤ δ)
    (hη : ‖mask D ((t / N) / Q) - mask (Finset.range Q) ((t / N) / Q)‖ ≤ η) :
    ‖mask B t * mask C (t / N) * mask D ((t / N) / Q)‖ ≤
      Real.pi / N + Real.pi * δ + η := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hthird : ‖mask D ((t / N) / Q)‖ ≤ Real.pi * (N - t) / N + η := by
    have h := norm_mask_range_near_one_le hQ
      ((le_div_iff₀ hN').mpr (by linarith)) ((div_le_one hN').mpr htN)
    have heq : 1 - t / N = (N - t) / N := by field_simp
    rw [heq] at h
    simpa only [mul_div_assoc] using
      (norm_le_norm_add_norm_sub (mask (Finset.range Q) ((t / N) / Q))
        (mask D ((t / N) / Q))).trans (add_le_add h (by simpa only [norm_sub_rev] using hη))
  simpa only [norm_mul (mask B t * mask C (t / N))] using
    mul_le_of_gap_bounds (norm_nonneg _)
      (by
        simpa only [norm_mul, one_mul] using mul_le_mul
          (norm_mask_le_one B hB t) (norm_mask_le_one C hC (t / N)) (norm_nonneg _) zero_le_one)
      hN' (by linarith : (N : ℝ) - t ≤ N) ((norm_nonneg _).trans hδ)
      ((norm_nonneg _).trans hη)
      (by
        simpa only [norm_adjacent_masks_reflect B C hN t] using
          norm_adjacent_masks_mul_gap_le B C hB hM hN (sub_nonneg.mpr htN)
            (by linarith) hε₁ hε hδ) hthird

private lemma norm_fourier_le_three_masks (A : Data) (ξ : ℝ) (n : ℕ) :
    ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
      ‖mask (A.digits n) (ξ / A.scale n) *
        mask (A.digits (n + 1)) ((ξ / A.scale n) / A.base (n + 1)) *
        mask (A.digits (n + 2))
          (((ξ / A.scale n) / A.base (n + 1)) / A.base (n + 2))‖ := by
  simpa [norm_mul, Data.scale, Finset.prod_range_succ, div_mul_eq_div_div, mul_assoc] using
    norm_fourier_le_prod_masks A ξ {n, n + 1, n + 2}

private lemma spectralMoranData_fourier_upper_half_bound (s : ℝ) (hs : 0 < s)
    (hs₁ : s ≤ 1) (ξ : ℝ) (n : ℕ) :
    let A := spectralMoranData s hs hs₁
    A.base (n + 1) / 2 ≤ ξ / A.scale n → ξ / A.scale n ≤ A.base (n + 1) →
      ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        Real.pi / A.base (n + 1) +
          Real.pi * (A.base (n + 1) : ℝ) ^ (-constructionExponent s (n + 1) / 2) +
            (A.base (n + 2) : ℝ) ^ (-constructionExponent s (n + 2) / 2) := by
  intro A ht htN
  exact (norm_fourier_le_three_masks A ξ n).trans
    (norm_three_masks_upper_half_le _ _ _ (A.digits_nonempty n) (A.digits_nonempty (n + 1))
      (Nat.zero_lt_two.trans_le (A.two_le_base n))
      (Nat.zero_lt_two.trans_le (A.two_le_base (n + 1))) (A.two_le_base (n + 2)) ht htN
      (Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (Nat.one_le_of_lt (A.two_le_base n)))
        (by linarith [constructionExponent_pos hs n]))
      (spectralMoranData_mask_error s hs hs₁ n _)
      (spectralMoranData_mask_error s hs hs₁ (n + 1) _)
      (spectralMoranData_mask_error s hs hs₁ (n + 2) _))

private lemma spectralMoranData_fourier_lower_half_uniform (s : ℝ) (hs : 0 < s)
    (hs₁ : s ≤ 1) {γ C : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ C)
    (hcost : ∀ n, ((spectralMoranData s hs hs₁).base n : ℝ) ^
      (-constructionExponent s n / 2) ≤ C *
        ((spectralMoranData s hs hs₁).base n : ℝ) ^ (-γ)) (n : ℕ) (ξ : ℝ) :
    let A := spectralMoranData s hs hs₁
    0 < ξ / A.scale n → ξ / A.scale n ≤ A.base (n + 1) / 2 →
      ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        C * ((A.scale n : ℝ) ^ (-(γ * (n + 1) / (n + 2))) / (ξ / A.scale n) +
          (A.base (n + 1) : ℝ) ^ (-γ)) := by
  intro A ht htN
  have hprev := (hcost n).trans (mul_le_mul_of_nonneg_left
    (spectralMoranData_base_rpow_le_scale s hs hs₁ hγ n) hC)
  have hnum : (A.base n : ℝ)⁻¹ + (A.base n : ℝ) ^ (-constructionExponent s n / 2) ≤
      2 * (C * (A.scale n : ℝ) ^ (-(γ * (n + 1) / (n + 2)))) := by
    linarith [inv_base_le_construction_mask_cost s hs hs₁ n]
  simpa only [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0), mul_add,
    mul_div_assoc] using
    (spectralMoranData_fourier_block_bound s hs hs₁ ξ n ht htN).trans
      (add_le_add (div_le_div_of_nonneg_right hnum (by positivity)) (hcost (n + 1)))

private lemma spectralMoranData_fourier_upper_half_uniform (s : ℝ) (hs : 0 < s)
    (hs₁ : s ≤ 1) {γ C : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ C)
    (hcost : ∀ n, ((spectralMoranData s hs hs₁).base n : ℝ) ^
      (-constructionExponent s n / 2) ≤ C *
        ((spectralMoranData s hs hs₁).base n : ℝ) ^ (-γ)) (n : ℕ) (ξ : ℝ) :
    let A := spectralMoranData s hs hs₁
    A.base (n + 1) / 2 ≤ ξ / A.scale n → ξ / A.scale n ≤ A.base (n + 1) →
      ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        (9 * C) * (A.base (n + 1) : ℝ) ^ (-γ) := by
  intro A ht htN
  have hnext := (hcost (n + 2)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos
      (Nat.cast_pos.mpr (Nat.zero_lt_two.trans_le (A.two_le_base (n + 1))))
      (Nat.cast_le.mpr (spectralMoranData_base_lt_succ s hs hs₁ (n + 1)).le)
      (neg_nonpos.mpr hγ)) hC)
  have h := spectralMoranData_fourier_upper_half_bound s hs hs₁ ξ n ht htN
  rw [div_eq_mul_inv] at h
  nlinarith [mul_le_mul_of_nonneg_left (hcost (n + 1)) Real.pi_pos.le,
    mul_le_mul_of_nonneg_left
      ((inv_base_le_construction_mask_cost s hs hs₁ (n + 1)).trans (hcost (n + 1)))
      Real.pi_pos.le,
    mul_le_mul_of_nonneg_right Real.pi_le_four
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg (A.base (n + 1))) (-γ)))]

private lemma spectralMoranData_fourier_blockwise (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {γ : ℝ} (hγ : 0 < γ) (hγs : γ < s / 2) :
    let A := spectralMoranData s hs hs₁
    ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → ∀ ξ : ℝ,
      A.scale n ≤ ξ → ξ < A.scale (n + 1) →
        ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
          C * if ξ / A.scale n ≤ A.base (n + 1) / 2 then
            (A.scale n : ℝ) ^ (-(γ * (n + 1) / (n + 2))) / (ξ / A.scale n) +
              (A.base (n + 1) : ℝ) ^ (-γ)
          else (A.base (n + 1) : ℝ) ^ (-γ) := by
  intro A
  obtain ⟨C, hC, hcost⟩ := construction_mask_cost_uniform s hs hs₁ hγs
  refine ⟨9 * C, by positivity, fun n _ ξ hξ hξ' ↦ ?_⟩
  have hP : (0 : ℝ) < A.scale n := Nat.cast_pos.mpr (A.prefix_product_pos (n + 1))
  split_ifs with ht
  case neg =>
    exact spectralMoranData_fourier_upper_half_uniform s hs hs₁ hγ.le (by linarith)
      hcost n ξ (le_of_not_ge ht) ((div_le_iff₀ hP).mpr (by
        simpa only [Data.scale, Finset.prod_range_succ, Nat.cast_mul, mul_comm] using hξ'.le))
  case pos =>
    exact (spectralMoranData_fourier_lower_half_uniform s hs hs₁ hγ.le (by linarith)
      hcost n ξ (div_pos (hP.trans_le hξ) hP) ht).trans
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ 9 * C)
          (add_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            (div_pos (hP.trans_le hξ) hP).le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

private lemma eventually_construction_fourier_block_decay (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {a : ℝ} (ha : 0 < a) (has : a < s / 2) :
    let A := spectralMoranData s hs hs₁
    ∀ᶠ n : ℕ in atTop, ∀ ξ : ℝ, A.scale n ≤ 2 * ξ → 2 * ξ ≤ A.scale (n + 1) →
      ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        3 * ξ ^ (-a) := by
  intro A
  have hcost := eventually_construction_mask_cost_le_scale s hs hs₁ has
  filter_upwards [hcost, (tendsto_add_atTop_nat 1).eventually hcost] with n hn hn₁
  intro ξ hlow hhigh
  have hP : 0 < (A.scale n : ℝ) := Nat.cast_pos.mpr (A.prefix_product_pos (n + 1))
  have hξ : 0 < ξ := by linarith
  have hscale : (A.scale (n + 1) : ℝ) = A.scale n * A.base (n + 1) := by
    simp only [Data.scale, Finset.prod_range_succ, Nat.cast_mul]
  have htN : ξ / A.scale n ≤ A.base (n + 1) / 2 :=
    (div_le_iff₀ hP).mpr (by nlinarith)
  exact (spectralMoranData_fourier_block_bound s hs hs₁ ξ n (div_pos hξ hP) htN).trans
    (block_bound_le_rpow hP hξ hlow (by linarith) ha.le (by linarith)
      (inv_base_le_construction_mask_cost s hs hs₁ n) hn hn₁)

private lemma eventually_construction_full_block_decay (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {a : ℝ} (ha : 0 < a) (has : a < s / 2) :
    let A := spectralMoranData s hs hs₁
    ∀ᶠ n : ℕ in atTop, ∀ ξ : ℝ, A.scale n ≤ ξ → ξ ≤ A.scale (n + 1) →
      ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        9 * ξ ^ (-a) := by
  intro A
  have hcost := eventually_construction_mask_cost_le_scale s hs hs₁ has
  filter_upwards [eventually_construction_fourier_block_decay s hs hs₁ ha has,
    (tendsto_add_atTop_nat 1).eventually hcost,
    (tendsto_add_atTop_nat 2).eventually hcost] with n hlow hn₁ hn₂
  intro ξ hPξ hξP
  have hP : (0 : ℝ) < A.scale n := Nat.cast_pos.mpr (A.prefix_product_pos (n + 1))
  have hξ : 0 < ξ := hP.trans_le hPξ
  have hscale (j : ℕ) : (A.scale (j + 1) : ℝ) = A.scale j * A.base (j + 1) := by
    simp only [Data.scale, Finset.prod_range_succ, Nat.cast_mul]
  by_cases ht : ξ / A.scale n ≤ A.base (n + 1) / 2
  · exact (hlow ξ (by linarith) (by rw [hscale]; nlinarith [(div_le_iff₀ hP).mp ht])).trans
      (by nlinarith [Real.rpow_nonneg hξ.le (-a)])
  · have hnext : ξ ≤ A.scale (n + 2) := by
      have hb : (2 : ℝ) ≤ A.base (n + 2) := by exact_mod_cast A.two_le_base (n + 2)
      rw [show n + 2 = (n + 1) + 1 by omega, hscale]
      nlinarith
    have hδ := hn₁.trans (Real.rpow_le_rpow_of_nonpos hξ hξP (neg_nonpos.mpr ha.le))
    have hη := hn₂.trans (Real.rpow_le_rpow_of_nonpos hξ hnext (neg_nonpos.mpr ha.le))
    have hinv := (inv_base_le_construction_mask_cost s hs hs₁ (n + 1)).trans hδ
    have h := spectralMoranData_fourier_upper_half_bound s hs hs₁ ξ n
      (le_of_not_ge ht) ((div_le_iff₀ hP).mpr (by simpa only [hscale, mul_comm] using hξP))
    rw [div_eq_mul_inv] at h
    nlinarith [mul_le_mul_of_nonneg_left hδ Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hinv Real.pi_pos.le,
      mul_le_mul_of_nonneg_right Real.pi_le_four (Real.rpow_nonneg hξ.le (-a))]

private lemma eventually_construction_fourier_decay_pos (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {a : ℝ} (ha : 0 < a) (has : a < s / 2) :
    ∀ᶠ ξ : ℝ in atTop,
      ‖Fourier.fourierIntegral Real.fourierChar
        (spectralMoranData s hs hs₁).measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤ 3 * ξ ^ (-a) := by
  obtain ⟨b, hab, hbs⟩ := exists_between has
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_construction_full_block_decay s hs hs₁ (ha.trans hab) hbs)
  have hsmall : ∀ᶠ ξ : ℝ in atTop, 9 * ξ ^ (-(b - a)) ≤ 3 :=
    ((tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul 9).eventually
      (ge_mem_nhds (by norm_num : (9 : ℝ) * 0 < 3))
  filter_upwards [eventually_ge_atTop ((spectralMoranData s hs hs₁).scale N : ℝ),
    hsmall] with ξ hξ hc
  obtain ⟨n, hn, hlo, hhi⟩ := exists_scale_block (spectralMoranData s hs hs₁) N hξ
  have hξ₀ : 0 < ξ :=
    (Nat.cast_pos.mpr ((spectralMoranData s hs hs₁).prefix_product_pos (N + 1))).trans_le hξ
  refine (hN n hn ξ hlo hhi).trans ?_
  convert mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hξ₀.le (-a)) using 1
  rw [mul_assoc, ← Real.rpow_add hξ₀]
  congr 2
  ring

/-- The Fourier transform decays at every exponent strictly below half the target dimension. -/
theorem spectralMoranData_fourier_decay (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {a : ℝ} (ha : 0 < a) (has : a < s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖Fourier.fourierIntegral Real.fourierChar
        (spectralMoranData s hs hs₁).measure (fun _ ↦ (1 : ℂ)) ξ‖ ≤
          C * (1 + |ξ|) ^ (-a) := by
  let A := spectralMoranData s hs hs₁
  obtain ⟨C, hC, hbound⟩ := exists_weighted_bound_of_eventual_decay ha.le (by linarith)
    (fun ξ ↦ show ‖Fourier.fourierIntegral Real.fourierChar A.measure
      (fun _ ↦ (1 : ℂ)) ξ‖ ≤ 1 from by
        simpa using norm_fourier_le_prod_masks A ξ ∅)
    (eventually_construction_fourier_decay_pos s hs hs₁ ha has)
  refine ⟨C, hC, fun ξ ↦ ?_⟩
  have heq : ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) |ξ|‖ =
      ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) ξ‖ := by
    by_cases hξ : 0 ≤ ξ
    · simp only [abs_of_nonneg hξ]
    · simpa only [abs_of_neg (lt_of_not_ge hξ)] using norm_fourier_neg A.measure ξ
  simpa only [Real.rpow_neg (by positivity : 0 ≤ 1 + |ξ|), div_eq_mul_inv, heq] using
    (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < 1 + |ξ|) a)).mpr
      (hbound |ξ| (abs_nonneg ξ))

private lemma eventually_construction_mask_error_le_inv_pi (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ ξ : ℝ,
      ‖mask ((spectralMoranData s hs hs₁).digits n) ξ -
        mask (Finset.range ((spectralMoranData s hs hs₁).base n)) ξ‖ ≤ 1 / Real.pi := by
  let A := spectralMoranData s hs hs₁
  have hlim : Tendsto (fun n ↦ (A.scale n : ℝ) ^ (-(s / 4))) atTop (𝓝 0) := by
    simpa only [Data.scale, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < s / 4)).comp
        ((tendsto_prefix_product_atTop A).comp (tendsto_add_atTop_nat 1))
  filter_upwards [eventually_construction_mask_cost_le_scale s hs hs₁
      (by linarith : s / 4 < s / 2),
    hlim.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / Real.pi))] with n hn hsmall
  exact fun ξ ↦ (spectralMoranData_mask_error s hs hs₁ n ξ).trans (hn.trans hsmall)

private structure HadamardTower (A : Data) where
  frequencies : ℕ → Finset ℤ
  zero_mem : ∀ n, 0 ∈ frequencies n
  card_eq : ∀ n, (frequencies n).card = (A.digits n).card
  mask_zero : ∀ n (k l : frequencies n), k ≠ l →
    mask (A.digits n) (((k : ℤ) - (l : ℤ) : ℤ) / A.base n) = 0

private def HadamardTower.choice {A : Data} (T : HadamardTower A) {n : ℕ}
    (k : ∀ j : Fin n, T.frequencies j) (j : ℕ) : ℤ :=
  if hj : j < n then k ⟨j, hj⟩ else 0

private lemma HadamardTower.choice_mem {A : Data} (T : HadamardTower A) {n : ℕ}
    (k : ∀ j : Fin n, T.frequencies j) (j : ℕ) : T.choice k j ∈ T.frequencies j := by
  by_cases hj : j < n <;> simp only [HadamardTower.choice, hj, ↓reduceDIte]
  · exact (k ⟨j, hj⟩).property
  · exact T.zero_mem j

private lemma HadamardTower.finite_orthonormal {A : Data} (T : HadamardTower A) (n : ℕ) :
    Orthonormal ℂ (fun k : (∀ j : Fin n, T.frequencies j) ↦
      finiteFourierVector A n (finiteFrequency A (T.choice k) n)) := by
  classical
  refine orthonormal_iff_ite.mpr fun k l ↦ ?_
  rw [finiteFourierVector_inner, ← Int.cast_sub]
  split_ifs with hkl
  · simp [hkl, mask, Nat.ne_of_gt (A.digits_nonempty _).card_pos]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hkl
    refine prod_masks_finiteFrequency_sub_eq_zero A _ _ n
      ⟨j, j.isLt, by simpa only [HadamardTower.choice, dif_pos j.isLt] using
        (Subtype.val_injective.ne hj)⟩ ?_
    intro i hi hdiff
    exact T.mask_zero i ⟨T.choice k i, T.choice_mem k i⟩
      ⟨T.choice l i, T.choice_mem l i⟩ (fun h ↦ hdiff (congrArg Subtype.val h))

private def HadamardTower.finiteBasis {A : Data} (T : HadamardTower A) (n : ℕ) :
    OrthonormalBasis (∀ j : Fin n, T.frequencies j) ℂ
      (EuclideanSpace ℂ (∀ j : Fin n, A.digits j)) :=
  letI : Nonempty (∀ j : Fin n, T.frequencies j) := ⟨fun j ↦ ⟨0, T.zero_mem j⟩⟩
  (basisOfOrthonormalOfCardEqFinrank (T.finite_orthonormal n)
    (by simp only [finrank_euclideanSpace, Fintype.card_pi, Fintype.card_coe, T.card_eq]))
    |>.toOrthonormalBasis (by
      simpa only [coe_basisOfOrthonormalOfCardEqFinrank] using T.finite_orthonormal n)

private lemma HadamardTower.cylinder_parseval {A : Data} (T : HadamardTower A) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    (∑ k : (∀ j : Fin n, T.frequencies j),
      ‖(Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
        inner ℂ (finiteFourierVector A n (finiteFrequency A (T.choice k) n))
          (WithLp.toLp 2 w)‖ ^ 2) = ‖productCylinderVector A n w‖ ^ 2 := by
  have h := (T.finiteBasis n).sum_sq_norm_inner_right (WithLp.toLp 2 w)
  simp only [HadamardTower.finiteBasis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank, PiLp.norm_sq_eq_of_L2] at h
  simp only [norm_productCylinderVector_sq, norm_mul, mul_pow, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    ← Finset.mul_sum, h]

private def HadamardTower.spectrum {A : Data} (T : HadamardTower A) : Set ℝ :=
  {ξ | ∃ n, ∃ k : (∀ j : Fin n, T.frequencies j),
    ξ = (finiteFrequency A (T.choice k) n : ℝ)}

private lemma HadamardTower.fourier_sub_eq_zero {A : Data} (T : HadamardTower A) {ξ η : ℝ}
    (hξ : ξ ∈ T.spectrum) (hη : η ∈ T.spectrum) (hξη : ξ ≠ η) :
    Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) (ξ - η) = 0 := by
  rcases hξ with ⟨n, k, rfl⟩
  rcases hη with ⟨m, l, rfl⟩
  have hk : ∀ i, n ≤ i → T.choice k i = 0 := fun i hi ↦ dif_neg (not_lt.mpr hi)
  have hl : ∀ i, m ≤ i → T.choice l i = 0 := fun i hi ↦ dif_neg (not_lt.mpr hi)
  rw [← finiteFrequency_eq_of_zero_tail A (T.choice k) (le_max_left n m) hk,
    ← finiteFrequency_eq_of_zero_tail A (T.choice l) (le_max_right n m) hl] at hξη ⊢
  rw [← Int.cast_sub]
  exact fourier_sub_eq_zero_of_digit_masks A _ _ (max n m)
    (fun h ↦ hξη (congrArg (fun z : ℤ ↦ (z : ℝ)) h)) fun j _ hj ↦
      T.mask_zero j ⟨T.choice k j, T.choice_mem k j⟩
        ⟨T.choice l j, T.choice_mem l j⟩ (fun h ↦ hj (congrArg Subtype.val h))

private lemma HadamardTower.orthonormal {A : Data} (T : HadamardTower A) :
    Orthonormal ℂ (fun ξ : T.spectrum ↦ spectralVector A.measure ξ) := by
  classical
  refine orthonormal_iff_ite.mpr fun ξ η ↦ ?_
  rw [spectralVector_inner]
  split_ifs with h
  · simp [h, fourierIntegral_one_eq]
  · exact T.fourier_sub_eq_zero ξ.property η.property (fun hξη ↦ h (Subtype.ext hξη))

private lemma HadamardTower.product_orthonormal {A : Data} (T : HadamardTower A) :
    Orthonormal ℂ (fun ξ : T.spectrum ↦ productSpectralVector A ξ) := by
  refine orthonormal_iff_ite.mpr fun ξ η ↦ ?_
  rw [productSpectralVector, productSpectralVector, (codingPullback A).inner_map_map]
  exact orthonormal_iff_ite.mp T.orthonormal ξ η

private def HadamardTower.finiteEmbedding {A : Data} (T : HadamardTower A) (n : ℕ) :
    (∀ j : Fin n, T.frequencies j) ↪ T.spectrum where
  toFun k := ⟨finiteFrequency A (T.choice k) n, n, k, rfl⟩
  inj' := fun _ _ h ↦ (T.finite_orthonormal n).linearIndependent.injective
    (congrArg (finiteFourierVector A n) (congrArg Subtype.val h))

private lemma HadamardTower.product_complete {A : Data} (T : HadamardTower A)
    {C : ℝ} (hC : 0 < C)
    (hz : ∀ᶠ n : ℕ in atTop, ∀ k : (∀ j : Fin (n + 1), T.frequencies j),
      C ≤ ‖Fourier.fourierIntegral Real.fourierChar (tailData A (n + 1)).measure
        (fun _ ↦ (1 : ℂ)) ((finiteFrequency A (T.choice k) (n + 1) : ℝ) /
          ((∏ j ∈ Finset.range (n + 1), A.base j : ℕ) : ℝ))‖ ^ 2) :
    (Submodule.span ℂ (Set.range (fun ξ : T.spectrum ↦ productSpectralVector A ξ)))ᗮ = ⊥ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hz
  refine orthogonal_eq_bot_of_dense_frame_bound T.product_orthonormal
    (dense_positiveCylinderSubmodule A) hC ?_
  rintro f ⟨n, w, rfl⟩
  let M := max n N
  have hnm : n + 1 ≤ M + 1 := Nat.succ_le_succ (le_max_left n N)
  rw [← productCylinderVector_promote A hnm w]
  exact frame_bound_of_finite_coefficients T.product_orthonormal (T.finiteEmbedding (M + 1))
    (productCylinderVector A (M + 1) (promoteCylinderWeight A hnm w))
    (fun k ↦ (Real.sqrt (Fintype.card (∀ j : Fin (M + 1), A.digits j)) : ℂ)⁻¹ *
      inner ℂ (finiteFourierVector A (M + 1) (finiteFrequency A (T.choice k) (M + 1)))
        (WithLp.toLp 2 (promoteCylinderWeight A hnm w)))
    (fun k ↦ Fourier.fourierIntegral Real.fourierChar (tailData A (M + 1)).measure
      (fun _ ↦ (1 : ℂ)) ((finiteFrequency A (T.choice k) (M + 1) : ℝ) /
        ((∏ j ∈ Finset.range (M + 1), A.base j : ℕ) : ℝ)))
    (T.cylinder_parseval (M + 1) (promoteCylinderWeight A hnm w))
    (fun k ↦ productCylinder_inner_finiteFourier A (M + 1) _ _)
    (hN M (le_max_right n N))

private lemma HadamardTower.is_spectral {A : Data} (T : HadamardTower A)
    {C : ℝ} (hC : 0 < C)
    (hz : ∀ᶠ n : ℕ in atTop, ∀ k : (∀ j : Fin (n + 1), T.frequencies j),
      C ≤ ‖Fourier.fourierIntegral Real.fourierChar (tailData A (n + 1)).measure
        (fun _ ↦ (1 : ℂ)) ((finiteFrequency A (T.choice k) (n + 1) : ℝ) /
          ((∏ j ∈ Finset.range (n + 1), A.base j : ℕ) : ℝ))‖ ^ 2) :
    is_spectral A.measure := by
  refine ⟨inferInstance, T.spectrum, HilbertBasis.mkOfOrthogonalEqBot T.orthonormal
    (orthogonal_eq_bot_of_linearIsometry (codingPullback A) _ (T.product_complete hC hz)), ?_⟩
  simpa only [HilbertBasis.coe_mkOfOrthogonalEqBot] using
    (fun ξ : T.spectrum ↦ spectralVector_ae_eq A.measure ξ)

private def galoisPowerHadamardTower (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) : HadamardTower (galoisPowerMoranData p r m hr) where
  frequencies j := Finset.univ.image (powerFrequency (p j) (r j) (m j))
  zero_mem j := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [powerFrequency]⟩
  card_eq j := by simp only [Finset.card_image_of_injective _ powerFrequency_injective,
    Finset.card_univ, ZMod.card, galoisPowerMoranData_card_digits]
  mask_zero j k l hkl := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp k.property
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp l.property
    have hab : a ≠ b := fun h ↦ hkl (Subtype.ext (ha.symm.trans ((congrArg _ h).trans hb)))
    simpa only [ha, hb] using galoisPowerMoranData_mask_zero p r m hr j hab

private lemma galoisPowerHadamardTower_spectrum (p r m : ℕ → ℕ)
    [∀ j, Fact (p j).Prime] (hr : ∀ j, 0 < r j) :
    (galoisPowerHadamardTower p r m hr).spectrum = galoisPowerSpectrum p r m hr := by
  let T := galoisPowerHadamardTower p r m hr
  ext ξ
  constructor
  · rintro ⟨n, k, rfl⟩
    refine ⟨T.choice k, ?_, n, fun j hj ↦ dif_neg (not_lt.mpr hj), rfl⟩
    intro j
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (T.choice_mem k j)
    exact ⟨a, ha.symm⟩
  · rintro ⟨L, hL, n, _, rfl⟩
    let k : ∀ j : Fin n, T.frequencies j := fun j ↦
      ⟨L j, by obtain ⟨a, ha⟩ := hL j; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha.symm⟩⟩
    refine ⟨n, k, congrArg (fun z : ℤ ↦ (z : ℝ)) (Finset.sum_congr rfl ?_)⟩
    intro j hj
    simp only [HadamardTower.choice, dif_pos (Finset.mem_range.mp hj), k]

private lemma galoisPowerHadamardTower_choice (p r m : ℕ → ℕ)
    [∀ j, Fact (p j).Prime] (hr : ∀ j, 0 < r j) (n : ℕ)
    (k : ∀ j : Fin n, (galoisPowerHadamardTower p r m hr).frequencies j) :
    ∃ l : ∀ j : Fin n, ZMod (p j ^ r j),
      (galoisPowerHadamardTower p r m hr).choice k = finitePowerChoice p r m l := by
  choose l _ hl using fun j : Fin n ↦ Finset.mem_image.mp (k j).property
  refine ⟨l, funext fun j ↦ ?_⟩
  by_cases hj : j < n
  · simpa only [HadamardTower.choice, finitePowerChoice, dif_pos hj] using (hl ⟨j, hj⟩).symm
  · simp [HadamardTower.choice, finitePowerChoice, hj, powerFrequency]

private lemma productSpectrum_orthogonal_eq_bot_of_eventually_finiteTailFactor
    (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime] (hr : ∀ j, 0 < r j)
    {C : ℝ} (hC : 0 < C)
    (hz : ∀ᶠ n : ℕ in atTop, ∀ k : (∀ j : Fin (n + 1), ZMod (p j ^ r j)),
      C ≤ ‖finiteTailFactor p r m hr (n + 1) k‖ ^ 2) :
    let A := galoisPowerMoranData p r m hr
    (Submodule.span ℂ (Set.range (fun ξ : galoisPowerSpectrum p r m hr ↦
      productSpectralVector A ξ)))ᗮ = ⊥ := by
  intro A
  rw [← galoisPowerHadamardTower_spectrum p r m hr]
  apply (galoisPowerHadamardTower p r m hr).product_complete hC
  filter_upwards [hz] with n hn
  intro k
  obtain ⟨l, hl⟩ := galoisPowerHadamardTower_choice p r m hr (n + 1) k
  simpa only [hl, finiteTailFactor] using hn l

private lemma exp_mul_mask_eq_centered_sum (B : Finset ℕ) (N : ℕ) (x : ℝ) :
    Complex.exp ((Real.pi * x : ℝ) * Complex.I) * mask B (x / N) =
      (B.card : ℂ)⁻¹ * ∑ d ∈ B,
        Complex.exp ((Real.pi * x * (1 - 2 * (d : ℝ) / N) : ℝ) * Complex.I) := by
  rw [mask, mul_left_comm]
  simp only [Finset.mul_sum, ← Complex.exp_add]
  refine Finset.sum_congr rfl fun d _ ↦ congrArg ((B.card : ℂ)⁻¹ * ·)
    (congrArg Complex.exp ?_)
  push_cast
  ring

private lemma abs_centered_digit_phase_le {N d : ℕ} (hN : 0 < N) (hd : d < N) (x : ℝ) :
    |Real.pi * x * (1 - 2 * (d : ℝ) / N)| ≤ Real.pi * |x| := by
  have hfrac : 0 ≤ (d : ℝ) / N ∧ (d : ℝ) / N ≤ 1 :=
    ⟨by positivity, (div_le_one (Nat.cast_pos.mpr hN)).mpr (Nat.cast_le.mpr hd.le)⟩
  simpa only [abs_mul, abs_of_pos Real.pi_pos, mul_one, mul_div_assoc] using
    mul_le_mul_of_nonneg_left (show |1 - 2 * ((d : ℝ) / N)| ≤ 1 from
      abs_le.mpr ⟨by linarith [hfrac.2], by linarith [hfrac.1]⟩)
      (show 0 ≤ Real.pi * |x| by positivity)

private lemma cos_le_norm_mask (B : Finset ℕ) (hB : B.Nonempty) {N : ℕ} (hN : 0 < N)
    (hBN : ∀ d ∈ B, d < N) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.cos (Real.pi * |x|) ≤ ‖mask B (x / N)‖ := by
  have hcos (d : ℕ) (hd : d ∈ B) : Real.cos (Real.pi * |x|) ≤
      Real.cos (Real.pi * x * (1 - 2 * (d : ℝ) / N)) := by
    simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg (Real.pi * x * (1 - 2 * (d : ℝ) / N)))
      (by nlinarith [Real.pi_pos]) (abs_centered_digit_phase_le hN (hBN d hd) x)
  have hsum : Real.cos (Real.pi * |x|) ≤
      (Complex.exp ((Real.pi * x : ℝ) * Complex.I) * mask B (x / N)).re := by
    rw [exp_mul_mask_eq_centered_sum]
    simpa [Complex.mul_re, Complex.exp_re,
      hB.card_pos.ne'] using mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcos)
        (show 0 ≤ (B.card : ℝ)⁻¹ by positivity)
  simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] using
    hsum.trans (Complex.re_le_norm _)

private lemma one_sub_norm_mask_sq_le (B : Finset ℕ) (hB : B.Nonempty) {N : ℕ} (hN : 0 < N)
    (hBN : ∀ d ∈ B, d < N) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    1 - ‖mask B (x / N)‖ ^ 2 ≤ Real.pi ^ 2 * x ^ 2 := by
  have hcos : 0 ≤ Real.cos (Real.pi * |x|) := Real.cos_nonneg_of_mem_Icc
    ⟨by nlinarith [Real.pi_pos, abs_nonneg x], by nlinarith [Real.pi_pos]⟩
  nlinarith [pow_le_pow_left₀ hcos (cos_le_norm_mask B hB hN hBN hx) 2,
    Real.sin_sq_add_cos_sq (Real.pi * |x|),
    Real.sin_sq_le_sq (x := Real.pi * |x|), sq_abs x]

private def tailSquareError (r : ℕ) : ℝ :=
  Real.pi ^ 2 / (4 * 27 ^ (2 * (r + 1)))

private lemma summable_tailSquareError : Summable tailSquareError := by
  refine ((summable_geometric_of_abs_lt_one
    (by norm_num : |(1 / (27 ^ 2) : ℝ)| < 1)).mul_left
      (Real.pi ^ 2 / (4 * 27 ^ 2))).congr fun r ↦ ?_
  simp only [tailSquareError, pow_mul, pow_succ (27 ^ 2 : ℝ) r, div_pow, one_pow]
  ring

private lemma one_sub_tailSquareError_pos (r : ℕ) : 0 < 1 - tailSquareError r := by
  have hpow : (27 : ℝ) ^ 2 ≤ 27 ^ (2 * (r + 1)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact sub_pos.mpr ((div_lt_one (by positivity : (0 : ℝ) < 4 * 27 ^ (2 * (r + 1)))).mpr
    (by nlinarith [Real.pi_pos, Real.pi_le_four]))

private lemma multipliable_one_sub_tailSquareError :
    Multipliable (fun r ↦ 1 - tailSquareError r) := by
  simpa only [Pi.neg_apply, ← sub_eq_add_neg] using
    Real.multipliable_one_add_of_summable summable_tailSquareError.neg

private def uniformTailLower : ℝ :=
  (Real.pi ^ 2)⁻¹ * ∏' r, (1 - tailSquareError r)

private lemma uniformTailLower_pos : 0 < uniformTailLower := by
  have hne : ∏' r, (1 - tailSquareError r) ≠ 0 := by
    simpa only [Pi.neg_apply, ← sub_eq_add_neg] using
      tprod_one_add_ne_zero_of_summable
        (fun r ↦ show 1 + -tailSquareError r ≠ 0 from (one_sub_tailSquareError_pos r).ne')
        summable_tailSquareError.neg.norm
  exact mul_pos (inv_pos.mpr (sq_pos_of_pos Real.pi_pos))
    (lt_of_le_of_ne (ge_of_tendsto multipliable_one_sub_tailSquareError.hasProd
      (Filter.Eventually.of_forall fun S ↦
        Finset.prod_nonneg (fun r _ ↦ (one_sub_tailSquareError_pos r).le))) hne.symm)

private lemma pow_le_scale_of_base_ge (A : Data) (hbase : ∀ j, 27 ≤ A.base j) (n : ℕ) :
    (27 : ℝ) ^ (n + 1) ≤ A.scale n := by
  exact_mod_cast (show 27 ^ (n + 1) ≤ A.scale n from by
    simpa only [Data.scale, Finset.prod_const, Finset.card_range] using
      Finset.prod_le_prod (s := Finset.range (n + 1)) (f := fun _ ↦ 27) (g := A.base)
        (fun _ _ ↦ Nat.zero_le _) (fun j _ ↦ hbase j))

private lemma abs_div_scale_le_geometric (A : Data) (hbase : ∀ j, 27 ≤ A.base j)
    {t : ℝ} (ht : |t| ≤ 1 / 2) (r : ℕ) :
    |t / A.scale r| ≤ 1 / (2 * 27 ^ (r + 1)) := by
  simpa only [abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ A.scale r from Nat.cast_nonneg _), div_div] using
    div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ht (by positivity)
      (pow_le_scale_of_base_ge A hbase r)

private lemma tailSquareError_le_norm_mask_sq (A : Data) (hbase : ∀ j, 27 ≤ A.base j)
    {t : ℝ} (ht : |t| ≤ 1 / 2) (r : ℕ) :
    1 - tailSquareError r ≤
      ‖mask (A.digits (r + 1)) (t / A.scale (r + 1))‖ ^ 2 := by
  have hx := abs_div_scale_le_geometric A hbase ht r
  have hpow : (1 : ℝ) ≤ 27 ^ (r + 1) := one_le_pow₀ (by norm_num)
  have hhalf : |t / A.scale r| ≤ 1 / 2 :=
    hx.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hsq := one_sub_norm_mask_sq_le (A.digits (r + 1)) (A.digits_nonempty (r + 1))
    (Nat.zero_lt_two.trans_le (A.two_le_base (r + 1))) (A.digit_lt_base (r + 1)) hhalf
  have herror : Real.pi ^ 2 * (t / A.scale r) ^ 2 ≤ tailSquareError r := by
    simpa only [sq_abs, tailSquareError, div_pow, one_pow, mul_pow,
      ← pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.mul_comm (r + 1) 2,
      mul_one_div] using mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hx 2) (sq_nonneg Real.pi)
  have hscale : t / A.scale (r + 1) = (t / A.scale r) / A.base (r + 1) := by
    simp only [Data.scale, Finset.prod_range_succ, Nat.cast_mul, div_mul_eq_div_div]
  rw [hscale]
  linarith

private lemma uniformTailLower_le_norm_fourier_sq (A : Data)
    (hbase : ∀ j, 27 ≤ A.base j) {t : ℝ} (ht : |t| ≤ 1 / 2)
    (hfirst : 1 / Real.pi ≤ ‖mask (A.digits 0) (t / A.base 0)‖) :
    uniformTailLower ≤
      ‖Fourier.fourierIntegral Real.fourierChar A.measure (fun _ ↦ (1 : ℂ)) t‖ ^ 2 := by
  have hzero : (Real.pi ^ 2)⁻¹ ≤ ‖mask (A.digits 0) (t / A.scale 0)‖ ^ 2 := by
    simpa only [Data.scale, zero_add, Finset.prod_range_one, one_div, inv_pow] using
      pow_le_pow_left₀ (by positivity) hfirst 2
  refine le_of_tendsto_of_tendsto
    (multipliable_one_sub_tailSquareError.hasProd.tendsto_prod_nat.const_mul
      (Real.pi ^ 2)⁻¹)
    (((A.hasProd_mask t).norm.pow 2).tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)) ?_
  exact Filter.Eventually.of_forall fun n ↦ by
    dsimp only [Function.comp_apply]
    rw [Finset.prod_range_succ', mul_comm _ (‖mask (A.digits 0) (t / A.scale 0)‖ ^ 2)]
    exact mul_le_mul hzero
      (Finset.prod_le_prod (fun r _ ↦ (one_sub_tailSquareError_pos r).le)
        (fun r _ ↦ tailSquareError_le_norm_mask_sq A hbase ht r))
      (Finset.prod_nonneg (fun r _ ↦ (one_sub_tailSquareError_pos r).le)) (sq_nonneg _)

private lemma uniformTailLower_le_norm_fourier_tail_sq (A : Data) (L : ℕ → ℤ)
    (hL : ∀ j, 2 * |L j| ≤ (A.base j : ℤ) - 1) (n : ℕ)
    (hbase : ∀ j, 27 ≤ A.base j)
    (herror : ∀ ξ : ℝ, ‖mask (A.digits (n + 1)) ξ -
      mask (Finset.range (A.base (n + 1))) ξ‖ ≤ 1 / Real.pi) :
    uniformTailLower ≤ ‖Fourier.fourierIntegral Real.fourierChar
      (tailData A (n + 1)).measure (fun _ ↦ (1 : ℂ))
        ((finiteFrequency A L (n + 1) : ℝ) / A.scale n)‖ ^ 2 := by
  have ht := (abs_finiteFrequency_div_scale_lt A L hL n).le
  refine uniformTailLower_le_norm_fourier_sq (tailData A (n + 1))
    (fun j ↦ hbase (n + 1 + j)) ht ?_
  have hmask := two_div_pi_sub_le_norm_mask (A.digits (n + 1))
    (Nat.zero_lt_two.trans_le (A.two_le_base (n + 1))) ht (herror _)
  simpa only [tailData, Nat.add_zero,
    show 2 / Real.pi - 1 / Real.pi = 1 / Real.pi by ring] using hmask

private lemma spectralMoranData_base_ge (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    27 ≤ (spectralMoranData s hs hs₁).base n := by
  simpa only [spectralMoranData_base, show 3 ^ 3 = 27 by norm_num] using
    (Nat.pow_le_pow_left (Nat.succ_le_of_lt ((constructionDegree_two_le hs hs₁ n).trans_lt
      (constructionPrime_spec s hs hs₁ n).2.2.1)) 3).trans
        (Nat.pow_le_pow_right (constructionPrime_spec s hs hs₁ n).1.pos
          ((Nat.succ_le_succ (constructionRank_two_le hs n)).trans
            (constructionRank_lt hs hs₁ n)))

private lemma spectralMoranData_base_growth (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    27 ^ ((n + 1) * n) ≤ (spectralMoranData s hs hs₁).base n := by
  calc
    _ = (27 ^ n) ^ (n + 1) := by rw [← pow_mul, Nat.mul_comm n]
    _ ≤ (∏ j ∈ Finset.range n, (spectralMoranData s hs hs₁).base j) ^ (n + 1) :=
      Nat.pow_le_pow_left (by
        simpa using Finset.prod_le_prod (s := Finset.range n) (f := fun _ ↦ 27)
          (g := (spectralMoranData s hs hs₁).base) (fun _ _ ↦ Nat.zero_le _)
          (fun j _ ↦ spectralMoranData_base_ge s hs hs₁ j)) (n + 1)
    _ ≤ _ := (spectralMoranData_scale_separation s hs hs₁ n).le

private lemma eventually_construction_finiteTailFactor_lower
    (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ k : (∀ j : Fin (n + 1),
      ZMod (constructionPrime s hs hs₁ j ^ constructionRank s j)),
      uniformTailLower ≤
        ‖finiteTailFactor (constructionPrime s hs hs₁) (constructionRank s)
          (fun j ↦ constructionLength s j - constructionRank s j)
          (constructionRank_pos hs) (n + 1) k‖ ^ 2 := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually
    (eventually_construction_mask_error_le_inv_pi s hs hs₁)] with n hn
  intro k
  let k' : ∀ j, ZMod (constructionPrime s hs hs₁ j ^ constructionRank s j) :=
    fun j ↦ if hj : j < n + 1 then k ⟨j, hj⟩ else 0
  have h := uniformTailLower_le_norm_fourier_tail_sq (spectralMoranData s hs hs₁)
    (fun j ↦ powerFrequency (constructionPrime s hs hs₁ j) (constructionRank s j)
      (constructionLength s j - constructionRank s j) (k' j))
    (fun j ↦ powerFrequency_bound (constructionPrime_spec s hs hs₁ j).2.1 (k' j))
    n (spectralMoranData_base_ge s hs hs₁) hn
  exact h

/-- The finite sums of centered digit frequencies for the prescribed-dimension construction. -/
def spectralMoranSpectrum (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) : Set ℝ :=
  galoisPowerSpectrum (constructionPrime s hs hs₁) (constructionRank s)
    (fun j ↦ constructionLength s j - constructionRank s j) (constructionRank_pos hs)

private lemma spectralMoranSpectrum_orthogonal_eq_bot (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    (Submodule.span ℂ (Set.range (fun ξ : spectralMoranSpectrum s hs hs₁ ↦
      spectralVector (spectralMoranData s hs hs₁).measure ξ)))ᗮ = ⊥ := by
  exact orthogonal_eq_bot_of_linearIsometry (codingPullback (spectralMoranData s hs hs₁)) _
    (productSpectrum_orthogonal_eq_bot_of_eventually_finiteTailFactor
      (constructionPrime s hs hs₁) (constructionRank s)
      (fun j ↦ constructionLength s j - constructionRank s j) (constructionRank_pos hs)
      uniformTailLower_pos
      (eventually_construction_finiteTailFactor_lower s hs hs₁))

private def constructionHilbertBasis (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    HilbertBasis (spectralMoranSpectrum s hs hs₁) ℂ (Lp ℂ 2 (spectralMoranData s hs hs₁).measure) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (galoisPowerSpectrum_orthonormal (constructionPrime s hs hs₁) (constructionRank s)
      (fun j ↦ constructionLength s j - constructionRank s j) (constructionRank_pos hs))
    (spectralMoranSpectrum_orthogonal_eq_bot s hs hs₁)

private lemma constructionHilbertBasis_ae_eq (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (ξ : spectralMoranSpectrum s hs hs₁) :
    ∀ᵐ x ∂(spectralMoranData s hs hs₁).measure,
      (constructionHilbertBasis s hs hs₁ ξ : ℝ → ℂ) x =
        Complex.exp ((2 * Real.pi * (ξ : ℝ) * x : ℝ) * Complex.I) := by
  have hb : constructionHilbertBasis s hs hs₁ ξ =
      spectralVector (spectralMoranData s hs hs₁).measure ξ := by
    exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) ξ
  simpa only [hb] using spectralVector_ae_eq (spectralMoranData s hs hs₁).measure (ξ : ℝ)

private lemma spectralMoranData_is_spectral (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    is_spectral (spectralMoranData s hs hs₁).measure :=
  ⟨inferInstance, spectralMoranSpectrum s hs hs₁, constructionHilbertBasis s hs hs₁,
    constructionHilbertBasis_ae_eq s hs hs₁⟩

private lemma tendsto_weighted_average {ρ w : ℕ → ℝ} {s : ℝ}
    (hρ : Tendsto ρ atTop (𝓝 s)) (hw : ∀ n, 0 ≤ w n)
    (hW : Tendsto (fun n ↦ ∑ j ∈ Finset.range n, w j) atTop atTop) :
    Tendsto (fun n ↦ (∑ j ∈ Finset.range n, ρ j * w j) /
      (∑ j ∈ Finset.range n, w j)) atTop (𝓝 s) := by
  have he : (fun n ↦ (ρ n - s) * w n) =o[atTop] w := by
    simpa only [one_mul] using
      ((Asymptotics.isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hρ)).mul_isBigO
        (Asymptotics.isBigO_refl w atTop)
  refine tendsto_sub_nhds_zero_iff.mp
    ((he.sum_range hw hW).tendsto_div_nhds_zero.congr' ?_)
  exact (hW.eventually_gt_atTop 0).mono fun n hn ↦ by
    simp [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sub_div, hn.ne']

private lemma tendsto_sum_log_base (A : Data) :
    Tendsto (fun n ↦ ∑ j ∈ Finset.range n, Real.log (A.base j : ℝ)) atTop atTop := by
  simpa only [Function.comp_def, Nat.cast_prod, Real.log_prod (fun j _ ↦
    Nat.cast_ne_zero.mpr (Nat.zero_lt_two.trans_le (A.two_le_base j)).ne')] using
    Real.tendsto_log_atTop.comp (tendsto_prefix_product_atTop A)

private lemma spectralMoranData_log_card_digits (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (n : ℕ) :
    Real.log (((spectralMoranData s hs hs₁).digits n).card : ℝ) =
      constructionRatio s n * Real.log ((spectralMoranData s hs hs₁).base n : ℝ) := by
  rw [spectralMoranData_base]
  simp only [spectralMoranData, galoisPowerMoranData_card_digits,
    Nat.cast_pow, Real.log_pow, constructionRatio]
  rw [← mul_assoc, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (constructionLength_pos s n).ne')]

private lemma tendsto_spectralMoranData_log_ratio (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    let A := spectralMoranData s hs hs₁
    Tendsto (fun n ↦ Real.log ((∏ j ∈ Finset.range n, (A.digits j).card : ℕ) : ℝ) /
      Real.log ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)) atTop (𝓝 s) := by
  simpa only [Nat.cast_prod, Real.log_prod (fun j _ ↦ Nat.cast_ne_zero.mpr
      ((spectralMoranData s hs hs₁).digits_nonempty j).card_pos.ne'),
    Real.log_prod (fun j _ ↦ Nat.cast_ne_zero.mpr
      (Nat.zero_lt_two.trans_le ((spectralMoranData s hs hs₁).two_le_base j)).ne'),
    spectralMoranData_log_card_digits] using
    tendsto_weighted_average (tendsto_constructionRatio hs)
      (fun j ↦ Real.log_nonneg (by exact_mod_cast
        (Nat.le_trans (by decide : 1 ≤ 2) ((spectralMoranData s hs hs₁).two_le_base j))))
      (tendsto_sum_log_base (spectralMoranData s hs hs₁))

private lemma tendsto_cover_cost_of_log_ratio (A : Data) {s d : ℝ} (hsd : s < d)
    (hlim : Tendsto (fun n ↦
      Real.log ((∏ j ∈ Finset.range n, (A.digits j).card : ℕ) : ℝ) /
        Real.log ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n ↦ ((∏ j ∈ Finset.range n, (A.digits j).card : ℕ) : ℝ) *
      ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ) ^ (-d)) atTop (𝓝 0) := by
  refine (Real.tendsto_exp_atBot.comp ((hlim.sub_const d).neg_mul_atTop (sub_neg.mpr hsd)
    (Real.tendsto_log_atTop.comp (tendsto_prefix_product_atTop A)))).congr' ?_
  filter_upwards [(tendsto_prefix_product_atTop A).eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, sub_mul, mul_assoc, inv_mul_cancel₀ (Real.log_pos hn).ne',
    mul_one,
    Real.exp_sub, Real.exp_log (Nat.cast_pos.mpr (Finset.prod_pos
      (fun j _ ↦ (A.digits_nonempty j).card_pos))),
    Real.rpow_def_of_pos (zero_lt_one.trans hn), mul_neg, Real.exp_neg,
    div_eq_mul_inv, mul_comm d]

private lemma spectralMoranData_dimH_le (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    dimH (spectralMoranData s hs hs₁).carrier ≤ ENNReal.ofReal s := by
  exact dimH_carrier_le_of_cover_cost _ hs.le fun d hd ↦
    tendsto_cover_cost_of_log_ratio _ hd (tendsto_spectralMoranData_log_ratio s hs hs₁)

/-- The constructed measure and carrier have the prescribed Fourier and Hausdorff dimensions. -/
theorem spectralMoranData_dimensions_eq (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    fourierDim (spectralMoranData s hs hs₁).measure = s ∧
      dimH (spectralMoranData s hs hs₁).carrier = ENNReal.ofReal s := by
  let A := spectralMoranData s hs hs₁
  have hF : s ≤ fourierDim A.measure := le_fourierDim_of_decay A.measure hs₁
    (fun t ht hts ↦ by simpa only [neg_div, Real.rpow_eq_pow] using
      spectralMoranData_fourier_decay s hs hs₁ (half_pos ht) (by linarith : t / 2 < s / 2))
  have hFH := ofReal_fourierDim_le_dimH A.measure
    A.nonempty_isCompact_carrier.2.measurableSet A.measure_compl_carrier
  have hH := spectralMoranData_dimH_le s hs hs₁
  exact ⟨le_antisymm ((ENNReal.ofReal_le_ofReal_iff hs.le).mp (hFH.trans hH)) hF,
    le_antisymm hH ((ENNReal.ofReal_le_ofReal hF).trans hFH)⟩

/-- The constructed frequency set is a spectrum of the associated Moran measure. -/
theorem spectralMoranData_has_spectrum (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    ∃ b : HilbertBasis (spectralMoranSpectrum s hs hs₁) ℂ
      (Lp ℂ 2 (spectralMoranData s hs hs₁).measure),
      ∀ ξ : spectralMoranSpectrum s hs hs₁, ∀ᵐ x ∂(spectralMoranData s hs hs₁).measure,
        (b ξ : ℝ → ℂ) x = Complex.exp ((2 * Real.pi * (ξ : ℝ) * x : ℝ) * Complex.I) :=
  ⟨constructionHilbertBasis s hs hs₁, constructionHilbertBasis_ae_eq s hs hs₁⟩

/-- The carrier of the prescribed-dimension construction is a Salem set. -/
theorem spectralMoranData_is_salem (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    is_salem (spectralMoranData s hs hs₁).carrier :=
  is_salem_of_measure _ (spectralMoranData s hs hs₁).nonempty_isCompact_carrier.2.measurableSet
    (spectralMoranData s hs hs₁).measure_compl_carrier
    (spectralMoranData_dimensions_eq s hs hs₁).1 (spectralMoranData_dimensions_eq s hs hs₁).2

/-- The constructed spectrum is countable. -/
theorem spectralMoranSpectrum_countable (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    (spectralMoranSpectrum s hs hs₁).Countable := by
  refine (Set.countable_range (fun z : ℤ ↦ (z : ℝ))).mono ?_
  rintro ξ ⟨L, _, n, _, hξ⟩
  exact ⟨_, hξ.symm⟩

/-- Every dimension in `(0, 1]` is attained by a spectral Cantor–Moran measure
whose Moran set has the same Hausdorff dimension. -/
theorem exists_moran_measure (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    ∃ A : Data,
      fourierDim A.measure = s ∧
      dimH A.carrier = ENNReal.ofReal s ∧
      is_spectral A.measure := by
  obtain ⟨hfourier, hhausdorff⟩ := spectralMoranData_dimensions_eq s hs hs₁
  refine ⟨spectralMoranData s hs hs₁, hfourier, hhausdorff, ?_⟩
  exact spectralMoranData_is_spectral s hs hs₁

/-- Every dimension in `(0, 1]` is attained by a homogeneous Moran Salem set. -/
theorem exists_salem_moran_set (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    ∃ A : Data,
      dimH A.carrier = ENNReal.ofReal s ∧ is_salem A.carrier := by
  obtain ⟨hfourier, hhausdorff⟩ := spectralMoranData_dimensions_eq s hs hs₁
  exact ⟨_, hhausdorff, is_salem_of_measure _
    (spectralMoranData s hs hs₁).nonempty_isCompact_carrier.2.measurableSet
    (spectralMoranData s hs hs₁).measure_compl_carrier hfourier hhausdorff⟩

end Moran
