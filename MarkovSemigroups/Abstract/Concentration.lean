/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Concentration of Lipschitz Functions from LSI

This file contains the standard Borell-style / Herbst concentration
theorem: a measure satisfying a log-Sobolev inequality (LSI) with
constant `c > 0` makes Lipschitz functions sub-Gaussian, with rate
`c / L²` where `L` is the Lipschitz constant. Quantitatively:

  μ({x : F x − E_μ F > t}) ≤ exp(−c · t² / (2 L²)).

This is the Otto-Villani / Herbst concentration consequence of LSI.

## Status

* `herbst_mgf_bound` — textbook axiom: the moment-generating function
  of `F − E_μ F` is bounded by `exp(L²t²/(2c))` (sub-Gaussian with
  parameter `L²/c`). This is Herbst's lemma proper (BGL §5.4).
* `lipschitz_concentration_of_lsi` — *proven theorem* from
  `herbst_mgf_bound` + Mathlib's Chernoff
  (`measure_ge_le_exp_mul_mgf`).
* `lipschitz_concentration_left_of_lsi` — *proven* by reflection on
  `-F` against the right-tail concentration theorem.

The factoring isolates the deep step (Herbst's lemma — requires
truncation/mollification of test function `exp(λF/2)`) from the
mechanical Chernoff optimization. The latter is now fully proven.

## References

* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §5.4 (Herbst's argument).
* Ledoux, *The Concentration of Measure Phenomenon*, AMS, 2001, §1.
* Otto and Villani, "Generalization of an inequality by Talagrand and
  links with the logarithmic Sobolev inequality," *J. Funct. Anal.*
  173 (2000), §3.
-/

import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Topology.MetricSpace.Lipschitz
import MarkovSemigroups.DobrushinZegarlinski.LocalLSI

noncomputable section

namespace MarkovSemigroups.Abstract

open MeasureTheory MarkovSemigroups.DobrushinZegarlinski ProbabilityTheory
open Real
open scoped NNReal

/-- **Borell-Herbst concentration from LSI (textbook axiom).**

For a measure `μ` on a finite-dimensional inner-product space `E`
satisfying a log-Sobolev inequality with constant `c > 0`, every
`L`-Lipschitz function `F : E → ℝ` is sub-Gaussian:

  μ({x : F x − E_μ F > t}) ≤ exp(−c · t² / (2 L²)).

Reference: Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov
Diffusion Operators*, Springer, 2014, Proposition 5.4.1 (Herbst
argument). Also Ledoux 2001 §1 and Otto-Villani 2000 §3.

Strategy: Apply LSI to the test function `exp(λF/2)`. The entropy
and gradient calculations yield, for the cumulant generating function
`K(λ) = log E_μ exp(λ(F − E_μ F))`,

  λ K'(λ) − K(λ) ≤ L² λ² / (2 c).

Dividing by `λ²` and integrating from `0` (using
`lim_{λ→0⁺} K(λ)/λ = 0` since `F − E_μ F` is centered) gives

  K(λ) ≤ L² λ² / (2 c).

Combined with the Chernoff bound (Markov on `exp(λ X)`), this yields
the sub-Gaussian tail. The argument is standard but technically
delicate to formalize because applying LSI to `exp(λF/2)` requires
exponential integrability that is *equivalent* to the conclusion;
the rigorous treatment uses truncation `F_n = max(min(F, n), -n)`
and a limit argument. We axiomatize the final bound to avoid this
bookkeeping.

(NOT VERIFIED — axiom stands until peer review or full formalization
of the Herbst argument with truncation.)

We axiomatize the *MGF bound* (Herbst's lemma proper); the
concentration `lipschitz_concentration_of_lsi` is then a *theorem*
proved by Mathlib's Chernoff bound `measure_ge_le_exp_mul_mgf`.
This factoring isolates the deep step (Herbst's lemma — derived from
LSI via the test function `exp(λF/2)`) from the mechanical step
(Chernoff optimization). -/
axiom herbst_mgf_bound
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂μ))) μ ∧
    mgf (fun x => F x - ∫ y, F y ∂μ) μ t
      ≤ Real.exp ((L : ℝ) ^ 2 * t ^ 2 / (2 * c))

/-- **Borell-Herbst concentration from LSI (theorem).**

For `μ` satisfying LSI with constant `c > 0` and an `L`-Lipschitz `F`:

  μ({x : F x − E_μ F > t}) ≤ exp(−c · t² / (2 L²)).

Derived from `herbst_mgf_bound` (the textbook axiom) by Chernoff
optimization. The optimal multiplier in the Chernoff bound is
`τ = c · t / L²`, which substitutes into the MGF bound
`mgf X μ τ ≤ exp(L² τ² / (2 c))` to give the optimized exponent. -/
theorem lipschitz_concentration_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {x | F x - ∫ y, F y ∂μ > t}).toReal
      ≤ Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  set X : E → ℝ := fun x => F x - ∫ y, F y ∂μ with hX
  -- Case split on L = 0 (constant F).
  rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with hL_zero | hL_pos
  · -- L = 0: RHS = exp(0) = 1; LHS is a probability ≤ 1.
    have hL_eq : (L : ℝ) = 0 := hL_zero.symm
    have h_rhs_one :
        Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) = 1 := by
      rw [hL_eq]; simp
    rw [h_rhs_one]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans (le_of_eq measure_univ)
  -- L > 0: choose Chernoff multiplier τ = c · t / L².
  have hc_pos : 0 < c := h_lsi.c_pos
  set τ : ℝ := c * t / (L : ℝ) ^ 2 with hτ
  have hτ_nn : 0 ≤ τ := by
    apply div_nonneg
    · exact mul_nonneg hc_pos.le ht
    · exact sq_nonneg _
  obtain ⟨h_int_τ, h_mgf_τ⟩ := herbst_mgf_bound h_lsi hF_lip hF_int τ
  have h_cher := measure_ge_le_exp_mul_mgf (X := X) (μ := μ) t hτ_nn h_int_τ
  have h_combined :
      μ.real {x | t ≤ X x}
        ≤ Real.exp (-τ * t) * Real.exp ((L : ℝ) ^ 2 * τ ^ 2 / (2 * c)) :=
    h_cher.trans (mul_le_mul_of_nonneg_left h_mgf_τ (Real.exp_pos _).le)
  -- Algebra: -τ·t + L²·τ²/(2c) = -c·t²/(2L²) where τ = c·t/L².
  have h_exp_eq :
      Real.exp (-τ * t) * Real.exp ((L : ℝ) ^ 2 * τ ^ 2 / (2 * c))
        = Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    have hLsq_ne : (L : ℝ) ^ 2 ≠ 0 := ne_of_gt (pow_pos hL_pos 2)
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    show -τ * t + (L : ℝ) ^ 2 * τ ^ 2 / (2 * c)
          = -c * t ^ 2 / (2 * (L : ℝ) ^ 2)
    rw [hτ]
    field_simp
    ring
  rw [h_exp_eq] at h_combined
  -- Pass from {≥ t} to {> t}.
  have h_subset : {x | X x > t} ⊆ {x | t ≤ X x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact hx.le
  have h_mono : (μ {x | X x > t}).toReal ≤ μ.real {x | t ≤ X x} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h_subset)
  exact h_mono.trans h_combined

/-- **Left-tail concentration.**

Direct application of the axiom to `-F`: `μ({x : F x − E_μ F < −t}) ≤
exp(−c · t² / (2 L²))`. The factor-of-2 two-sided bound is obtained
by combining this with the right-tail axiom via the union bound,
and is left to the caller. -/
theorem lipschitz_concentration_left_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {x | F x - ∫ y, F y ∂μ < -t}).toReal
      ≤ Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  have h := lipschitz_concentration_of_lsi h_lsi hF_lip.neg hF_int.neg t ht
  -- The set `{x | (-F) x - ∫ y, (-F) y ∂μ > t}` equals `{x | F x - ∫ y, F y ∂μ < -t}`.
  have h_set_eq :
      {x | (-F) x - ∫ y, (-F) y ∂μ > t}
        = {x | F x - ∫ y, F y ∂μ < -t} := by
    ext x
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, integral_neg]
    constructor
    · intro hx; linarith
    · intro hx; linarith
  rw [h_set_eq] at h
  exact h

/-! ### Mathlib `HasSubgaussianMGF` interop

For downstream use with Mathlib's sub-Gaussian framework
(`ProbabilityTheory.HasSubgaussianMGF`): the centered Lipschitz
function under LSI is sub-Gaussian with variance proxy `L²/c`.
This bridge lets consumers feed our Herbst MGF bound into any
Mathlib lemma that expects `HasSubgaussianMGF`. -/

/-- **Bridge: LSI ⇒ HasSubgaussianMGF.**

The centered random variable `F − E_μ F` is sub-Gaussian (in
Mathlib's sense) with variance proxy `L² / c`, given LSI(c) and
`L`-Lipschitz `F`. -/
theorem hasSubgaussianMGF_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun x => F x - ∫ y, F y ∂μ)
      ⟨(L : ℝ) ^ 2 / c, div_nonneg (sq_nonneg _) h_lsi.c_pos.le⟩
      μ where
  integrable_exp_mul := fun t =>
    (herbst_mgf_bound h_lsi hF_lip hF_int t).1
  mgf_le := fun t => by
    -- Mathlib form: `mgf X μ t ≤ exp(c_sg · t² / 2)` where c_sg = L²/c.
    -- Our form: `mgf X μ t ≤ exp(L² · t² / (2c))`.
    -- These coincide: `c_sg · t² / 2 = (L²/c) · t² / 2 = L² · t² / (2c)`.
    have h_mgf := (herbst_mgf_bound h_lsi hF_lip hF_int t).2
    refine h_mgf.trans (le_of_eq ?_)
    congr 1
    show (L : ℝ) ^ 2 * t ^ 2 / (2 * c)
          = (⟨(L : ℝ) ^ 2 / c, _⟩ : ℝ≥0) * t ^ 2 / 2
    have hc_ne : c ≠ 0 := ne_of_gt h_lsi.c_pos
    show (L : ℝ) ^ 2 * t ^ 2 / (2 * c)
          = ((L : ℝ) ^ 2 / c) * t ^ 2 / 2
    field_simp

/-- **L^p integrability of Lipschitz F under LSI.**

Direct corollary of `hasSubgaussianMGF_of_lsi` via Mathlib's
`HasSubgaussianMGF.memLp`: any L-Lipschitz F is in `L^p(μ)` for
every `p`, given LSI(c) and `Integrable F μ`. The sub-Gaussian
tails imply finite moments of all orders. -/
theorem memLp_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ) (p : ℝ≥0) :
    MeasureTheory.MemLp (fun x => F x - ∫ y, F y ∂μ) p μ :=
  (hasSubgaussianMGF_of_lsi h_lsi hF_lip hF_int).memLp p

/-- **Two-sided Lipschitz concentration from LSI.**

Combines the one-sided concentration with its left-tail companion
via a union bound:

  μ({|F − E_μ F| > t}) ≤ 2 · exp(−c · t² / (2 L²)).

Proof: `{|X| > t} = {X > t} ∪ {-X > t}` (where X = F − E F), apply
the one-sided bound to X and to -X (which is L-Lipschitz with the
same constant), union bound. -/
theorem lipschitz_concentration_two_sided_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {x | t < |F x - ∫ y, F y ∂μ|}).toReal
      ≤ 2 * Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  set X : E → ℝ := fun x => F x - ∫ y, F y ∂μ with hX
  -- {|X| > t} ⊆ {X > t} ∪ {-X > t}
  have h_subset :
      {x | t < |X x|} ⊆ {x | X x > t} ∪ {x | -X x > t} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases abs_cases (X x) with ⟨heq, _⟩ | ⟨heq, _⟩
    · -- |X x| = X x (≥ 0): conclude X x > t.
      left; rw [heq] at hx; exact hx
    · -- |X x| = -X x: conclude -X x > t.
      right
      simp only [Set.mem_ofPred_eq]
      rw [heq] at hx; exact hx
  have h_right := lipschitz_concentration_of_lsi h_lsi hF_lip hF_int t ht
  -- For -F: still L-Lipschitz, integrable; gives {(-F) − ∫(-F) > t}.
  -- That set equals {-X > t} since (-F) − ∫(-F) = -F + ∫F = -X.
  have h_left_raw :=
    lipschitz_concentration_of_lsi h_lsi hF_lip.neg hF_int.neg t ht
  have h_left_set_eq :
      {x | (- F) x - ∫ y, (- F) y ∂μ > t} = {x | -X x > t} := by
    ext x
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, integral_neg, hX]
    constructor
    · intro hx; linarith
    · intro hx; linarith
  rw [h_left_set_eq] at h_left_raw
  -- Combine.
  calc (μ {x | t < |X x|}).toReal
      ≤ (μ ({x | X x > t} ∪ {x | -X x > t})).toReal := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
        exact measure_mono h_subset
    _ ≤ (μ {x | X x > t}).toReal + (μ {x | -X x > t}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        refine ENNReal.toReal_mono ?_ (measure_union_le _ _)
        rw [Ne, ENNReal.add_eq_top, not_or]
        exact ⟨measure_ne_top _ _, measure_ne_top _ _⟩
    _ ≤ Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2))
        + Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
        linarith
    _ = 2 * Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by ring

/-! ### LSI ⇒ Poincaré → variance bound -/

section PoincareOfLSI

/-- Second-order expansion of `u log u` at `u = 1` with a cubic remainder:
`|(1 + x) log (1 + x) - x - x² / 2| ≤ 4 |x|³` for `|x| ≤ 1/2`. -/
lemma abs_one_add_mul_log_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |(1 + x) * Real.log (1 + x) - x - x ^ 2 / 2| ≤ 4 * |x| ^ 3 := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le hx1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hlog
  set r := Real.log (1 + x) - (x - x ^ 2 / 2) with hr_def
  have hden : (1 : ℝ) / 2 ≤ 1 - |x| := by linarith
  have hr : |r| ≤ 2 * |x| ^ 3 := by
    have h1 : |r| ≤ |x| ^ 3 / (1 - |x|) := by
      convert hlog using 2
      rw [hr_def]; push_cast; ring
    calc |r| ≤ |x| ^ 3 / (1 - |x|) := h1
      _ ≤ |x| ^ 3 / (1 / 2) := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = 2 * |x| ^ 3 := by ring
  have hexp : (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 = -x ^ 3 / 2 + (1 + x) * r := by
    rw [hr_def]; ring
  rw [hexp]
  have h1x : |1 + x| ≤ 3 / 2 := by
    calc |1 + x| ≤ |1| + |x| := abs_add_le _ _
      _ ≤ 3 / 2 := by rw [abs_one]; linarith
  calc |-x ^ 3 / 2 + (1 + x) * r| ≤ |-x ^ 3 / 2| + |(1 + x) * r| := abs_add_le _ _
    _ = |x| ^ 3 / 2 + |1 + x| * |r| := by
        rw [abs_mul, abs_div, abs_neg, abs_pow]; norm_num
    _ ≤ |x| ^ 3 / 2 + 3 / 2 * (2 * |x| ^ 3) := by
        gcongr
    _ ≤ 4 * |x| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg x) 3]

variable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [FiniteDimensional ℝ E] in
/-- A bounded measurable real function is integrable for a probability measure. -/
lemma integrable_of_abs_le {μ : Measure E} [IsProbabilityMeasure μ] {F : E → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- **LSI ⇒ Poincaré for bounded functions** (linearization of the LSI at
the constant `1`). -/
theorem variance_le_of_lsi_of_abs_le
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {g : E → ℝ} (hg : Differentiable ℝ g) {A : ℝ} (hA : 0 < A)
    (hgA : ∀ x, |g x| ≤ A)
    (hgrad_int : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) μ) :
    variance g μ ≤ (1 / c) * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂μ := by
  have hc := h_lsi.c_pos
  have hgc : Continuous g := hg.continuous
  have hgm : Measurable g := hgc.measurable
  set m1 := ∫ x, g x ∂μ with hm1_def
  set m2 := ∫ x, g x ^ 2 ∂μ with hm2_def
  set D := ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂μ with hD_def
  set V := variance g μ with hV_def
  have hgi : Integrable g μ := integrable_of_abs_le hgm hgA
  have hg2b : ∀ x, |g x ^ 2| ≤ A ^ 2 := by
    intro x; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgA x) 2
  have hg2i : Integrable (fun x => g x ^ 2) μ :=
    integrable_of_abs_le (hgm.pow_const 2) hg2b
  have hm1 : |m1| ≤ A := by
    calc |m1| ≤ ∫ x, |g x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _, A ∂μ := integral_mono hgi.abs (integrable_const A) hgA
      _ = A := by simp
  have hm2 : 0 ≤ m2 ∧ m2 ≤ A ^ 2 := by
    refine ⟨integral_nonneg fun x => sq_nonneg _, ?_⟩
    calc m2 ≤ ∫ _, A ^ 2 ∂μ :=
          integral_mono hg2i (integrable_const _) fun x => (abs_le.mp (hg2b x)).2
      _ = A ^ 2 := by simp
  have hV : V = ∫ x, (g x - m1) ^ 2 ∂μ := variance_eq_integral hgm.aemeasurable
  -- Main estimate at scale `ε`.
  have key : ∀ ε : ℝ, 0 < ε → ε * A ≤ 1 / 8 →
      2 * ε ^ 2 * V - 221 * A ^ 3 * ε ^ 3 ≤ 2 / c * (ε ^ 2 * D) := by
    intro ε hε hεA
    have hεA0 : 0 ≤ ε * A := by positivity
    set h : E → ℝ := fun x => 1 + ε * g x with hh_def
    have hh : Differentiable ℝ h := (differentiable_const 1).add (hg.const_mul ε)
    have hfd : ∀ x, fderiv ℝ h x = ε • fderiv ℝ g x := by
      intro x
      have := ((hasFDerivAt_const (1 : ℝ) x).add ((hg x).hasFDerivAt.const_mul ε))
      rw [zero_add] at this
      exact this.fderiv
    set X : E → ℝ := fun x => 2 * ε * g x + ε ^ 2 * g x ^ 2 with hX_def
    have hXm : Measurable X := by
      simp only [hX_def]; fun_prop
    have hhX : ∀ x, h x ^ 2 = 1 + X x := by
      intro x; simp only [hh_def, hX_def]; ring
    have hXb : ∀ x, |X x| ≤ 3 * (ε * A) := by
      intro x
      have hgx := hgA x
      have h1 : |X x| ≤ 2 * ε * |g x| + ε ^ 2 * |g x| ^ 2 := by
        calc |X x| ≤ |2 * ε * g x| + |ε ^ 2 * g x ^ 2| := abs_add_le _ _
          _ = 2 * ε * |g x| + ε ^ 2 * |g x| ^ 2 := by
              rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos hε]; norm_num
      have h2 : ε * |g x| ≤ ε * A := by gcongr
      have h3 : ε ^ 2 * |g x| ^ 2 = (ε * |g x|) ^ 2 := by ring
      nlinarith [abs_nonneg (g x), mul_nonneg hε.le (abs_nonneg (g x))]
    have hXh : ∀ x, |X x| ≤ 1 / 2 := fun x => by linarith [hXb x]
    have hXi : Integrable X μ := integrable_of_abs_le hXm hXb
    set m := ∫ x, X x ∂μ with hm_def
    have hmb : |m| ≤ 3 * (ε * A) := by
      calc |m| ≤ ∫ x, |X x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _, 3 * (ε * A) ∂μ := integral_mono hXi.abs (integrable_const _) hXb
        _ = 3 * (ε * A) := by simp
    have hmh : |m| ≤ 1 / 2 := by linarith
    have hm_eq : m = 2 * ε * m1 + ε ^ 2 * m2 := by
      simp only [hm_def, hX_def]
      rw [integral_add (hgi.const_mul _) (hg2i.const_mul _), integral_const_mul,
        integral_const_mul]
    -- LSI applied to `h`.
    have hh2b : ∀ x, |h x ^ 2| ≤ 2 := fun x => by
      rw [hhX]; calc |1 + X x| ≤ |1| + |X x| := abs_add_le _ _
        _ ≤ 2 := by rw [abs_one]; linarith [hXh x]
    have hhm : Measurable h := by simp only [hh_def]; fun_prop
    have hh2i : Integrable (fun x => h x ^ 2) μ :=
      integrable_of_abs_le (hhm.pow_const 2) hh2b
    have hphib : ∀ x, |h x ^ 2 * Real.log (h x ^ 2)| ≤ 2 := by
      intro x
      rw [hhX]
      have hpos : 0 < 1 + X x := by linarith [abs_le.mp (hXh x)]
      have hle : 1 + X x ≤ 3 / 2 := by linarith [abs_le.mp (hXh x)]
      have hge : 1 / 2 ≤ 1 + X x := by linarith [abs_le.mp (hXh x)]
      rw [abs_mul, abs_of_pos hpos]
      have hlog : |Real.log (1 + X x)| ≤ 1 := by
        rw [abs_le]; constructor
        · have h1 := Real.one_sub_inv_le_log_of_pos hpos
          have h2 : (1 + X x)⁻¹ ≤ 2 := by
            rw [inv_le_comm₀ hpos (by norm_num)]; linarith
          linarith
        · have := Real.log_le_sub_one_of_pos hpos; linarith
      nlinarith [abs_nonneg (Real.log (1 + X x))]
    have hphim : Measurable fun x => h x ^ 2 * Real.log (h x ^ 2) := by
      fun_prop
    have hphii : Integrable (fun x => h x ^ 2 * Real.log (h x ^ 2)) μ :=
      integrable_of_abs_le hphim hphib
    have hgrad_h : (fun x => ‖fderiv ℝ h x‖ ^ 2) = fun x => ε ^ 2 * ‖fderiv ℝ g x‖ ^ 2 := by
      funext x; rw [hfd, norm_smul, Real.norm_eq_abs, abs_of_pos hε]; ring
    have hgradi : Integrable (fun x => ‖fderiv ℝ h x‖ ^ 2) μ := by
      rw [hgrad_h]; exact hgrad_int.const_mul _
    have hLSI := h_lsi.entropy_le hh hh2i hphii hgradi
    rw [hgrad_h, integral_const_mul] at hLSI
    -- Rewrite the entropy through `X`.
    have hEnt : entropy μ (fun x => h x ^ 2) =
        (∫ x, (1 + X x) * Real.log (1 + X x) ∂μ) - (1 + m) * Real.log (1 + m) := by
      have h1 : (∫ x, h x ^ 2 ∂μ) = 1 + m := by
        simp_rw [hhX]
        rw [integral_add (integrable_const _) hXi]; simp [hm_def]
      simp only [entropy]
      rw [h1]; simp_rw [hhX]
    -- Pointwise second-order bounds.
    have hlow : ∀ x, X x + X x ^ 2 / 2 - 4 * (3 * (ε * A)) ^ 3 ≤
        (1 + X x) * Real.log (1 + X x) := by
      intro x
      have h1 := abs_one_add_mul_log_one_add_sub_le (hXh x)
      have h2 : |X x| ^ 3 ≤ (3 * (ε * A)) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) (hXb x) 3
      have := (abs_le.mp h1).1
      linarith
    have hup : (1 + m) * Real.log (1 + m) ≤ m + m ^ 2 / 2 + 4 * (3 * (ε * A)) ^ 3 := by
      have h1 := abs_one_add_mul_log_one_add_sub_le hmh
      have h2 : |m| ^ 3 ≤ (3 * (ε * A)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hmb 3
      have := (abs_le.mp h1).2
      linarith
    have hX2i : Integrable (fun x => X x ^ 2) μ :=
      integrable_of_abs_le (hXm.pow_const 2) (C := (3 * (ε * A)) ^ 2) fun x => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hXb x) 2
    have hphiXi : Integrable (fun x => (1 + X x) * Real.log (1 + X x)) μ := by
      have : (fun x => (1 + X x) * Real.log (1 + X x)) =
          fun x => h x ^ 2 * Real.log (h x ^ 2) := by
        funext x; rw [hhX]
      rw [this]; exact hphii
    have hint_low : (∫ x, X x ∂μ) + (∫ x, X x ^ 2 ∂μ) / 2 - 4 * (3 * (ε * A)) ^ 3 ≤
        ∫ x, (1 + X x) * Real.log (1 + X x) ∂μ := by
      have hli : Integrable (fun x => X x + X x ^ 2 / 2 - 4 * (3 * (ε * A)) ^ 3) μ :=
        ((hXi.add (hX2i.div_const 2)).sub (integrable_const _))
      have := integral_mono hli hphiXi hlow
      have e1 : ∫ x, (X x + X x ^ 2 / 2 - 4 * (3 * (ε * A)) ^ 3) ∂μ =
          (∫ x, X x ∂μ) + (∫ x, X x ^ 2 ∂μ) / 2 - 4 * (3 * (ε * A)) ^ 3 := by
        rw [integral_sub, integral_add, integral_div, integral_const]
        · simp
        · exact hXi
        · exact hX2i.div_const 2
        · exact hXi.add (hX2i.div_const 2)
        · exact integrable_const _
      linarith
    -- Variance of `X` controls `4 ε² V`.
    have hVX : (∫ x, X x ^ 2 ∂μ) - m ^ 2 = ∫ x, (X x - m) ^ 2 ∂μ := by
      have hXmem : MemLp X 2 μ :=
        MemLp.of_bound hXm.aestronglyMeasurable (3 * (ε * A))
          (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hXb x)
      rw [← variance_eq_integral hXm.aemeasurable, variance_eq_sub hXmem]
      simp [hm_def, Pi.pow_apply]
    have hdev : ∀ x, 4 * ε ^ 2 * (g x - m1) ^ 2 - 8 * ε ^ 3 * A ^ 3 ≤ (X x - m) ^ 2 := by
      intro x
      have hu : |g x - m1| ≤ 2 * A := by
        calc |g x - m1| ≤ |g x| + |m1| := abs_sub _ _
          _ ≤ 2 * A := by linarith [hgA x]
      have hw : |g x ^ 2 - m2| ≤ A ^ 2 := by
        have h0 : 0 ≤ g x ^ 2 := sq_nonneg _
        have h1 : g x ^ 2 ≤ A ^ 2 := (abs_le.mp (hg2b x)).2
        rw [abs_le]; constructor <;> linarith [hm2.1, hm2.2]
      have hdecomp : X x - m = 2 * ε * (g x - m1) + ε ^ 2 * (g x ^ 2 - m2) := by
        rw [hm_eq]; simp only [hX_def]; ring
      rw [hdecomp]
      have huw : |(g x - m1) * (g x ^ 2 - m2)| ≤ 2 * A * A ^ 2 := by
        rw [abs_mul]; exact mul_le_mul hu hw (abs_nonneg _) (by positivity)
      have hε3 : 0 ≤ ε ^ 3 := by positivity
      nlinarith [abs_le.mp huw, sq_nonneg (ε ^ 2 * (g x ^ 2 - m2)), hε3,
        mul_le_mul_of_nonneg_left (abs_le.mp huw).1 (by positivity : (0:ℝ) ≤ 4 * ε ^ 3)]
    have hint_dev : 4 * ε ^ 2 * V - 8 * ε ^ 3 * A ^ 3 ≤ ∫ x, (X x - m) ^ 2 ∂μ := by
      have hu2i : Integrable (fun x => (g x - m1) ^ 2) μ :=
        integrable_of_abs_le ((hgm.sub_const m1).pow_const 2) (C := (2 * A) ^ 2) fun x => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (by calc |g x - m1| ≤ |g x| + |m1| := abs_sub _ _
                  _ ≤ 2 * A := by linarith [hgA x]) 2
      have hdi : Integrable (fun x => (X x - m) ^ 2) μ :=
        integrable_of_abs_le ((hXm.sub_const m).pow_const 2) (C := (6 * (ε * A)) ^ 2)
          fun x => by
            rw [abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _)
              (by calc |X x - m| ≤ |X x| + |m| := abs_sub _ _
                    _ ≤ 6 * (ε * A) := by linarith [hXb x]) 2
      have hli : Integrable (fun x => 4 * ε ^ 2 * (g x - m1) ^ 2 - 8 * ε ^ 3 * A ^ 3) μ :=
        (hu2i.const_mul _).sub (integrable_const _)
      have := integral_mono hli hdi hdev
      have e1 : ∫ x, (4 * ε ^ 2 * (g x - m1) ^ 2 - 8 * ε ^ 3 * A ^ 3) ∂μ =
          4 * ε ^ 2 * V - 8 * ε ^ 3 * A ^ 3 := by
        rw [integral_sub, integral_const_mul, ← hV, integral_const]
        · simp
        · exact hu2i.const_mul _
        · exact integrable_const _
      linarith
    -- Assemble.
    rw [hEnt] at hLSI
    have hA3 : 0 ≤ A ^ 3 * ε ^ 3 := by positivity
    have hcube : 4 * (3 * (ε * A)) ^ 3 = 108 * (A ^ 3 * ε ^ 3) := by ring
    have hεA3 : 8 * ε ^ 3 * A ^ 3 = 8 * (A ^ 3 * ε ^ 3) := by ring
    rw [hcube] at hint_low hup
    rw [hεA3] at hint_dev
    linarith [hint_low, hup, hVX, hint_dev, hLSI]
  -- Let `ε → 0`.
  have hA3 : 0 < A ^ 3 := by positivity
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set ε := min (1 / (8 * A)) (δ / (221 * A ^ 3)) with hε_def
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεA : ε * A ≤ 1 / 8 := by
    calc ε * A ≤ 1 / (8 * A) * A := by gcongr; exact min_le_left _ _
      _ = 1 / 8 := by field_simp
  have hεδ : 221 * A ^ 3 * ε ≤ δ := by
    calc 221 * A ^ 3 * ε ≤ 221 * A ^ 3 * (δ / (221 * A ^ 3)) := by
          gcongr; exact min_le_right _ _
      _ = δ := by field_simp
  have hk := key ε hε hεA
  have hε2 : 0 < ε ^ 2 := by positivity
  -- divide by 2 ε²
  have : V ≤ 1 / c * D + 221 * A ^ 3 * ε / 2 := by
    have h2 : 2 * ε ^ 2 * V ≤ 2 * ε ^ 2 * (1 / c * D + 221 * A ^ 3 * ε / 2) := by
      have : 2 / c * (ε ^ 2 * D) = 2 * ε ^ 2 * (1 / c * D) := by ring
      nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  linarith

/-- `(n + 1) · arctan (y / (n + 1)) → y`: the arctangent truncations converge
pointwise. -/
lemma tendsto_mul_arctan_div (y : ℝ) :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.arctan (y / ((n : ℝ) + 1)))
      Filter.atTop (nhds y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hslope := (Real.hasDerivAt_arctan 0).tendsto_slope_zero
  simp only [zero_add, Real.arctan_zero, sub_zero, one_div] at hslope
  norm_num at hslope
  have ht : Filter.Tendsto (fun n : ℕ => y / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul y
      rw [mul_zero] at this
      exact this.congr fun n => by rw [mul_one_div]
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact div_ne_zero hy (by positivity)
  have := (hslope.comp ht).const_mul y
  simp only [mul_one] at this
  refine this.congr fun n => ?_
  simp only [Function.comp_apply]
  field_simp

/-- **LSI implies Poincaré.** `SatisfiesLSI μ c` implies the Poincaré
inequality with the same constant: for differentiable `f` with `f`, `f²`
and `‖∇f‖²` integrable, `Var_μ(f) ≤ (1/c) ∫ ‖∇f‖² dμ`.

Bounded case: linearize the LSI at `1 + εg`
(`variance_le_of_lsi_of_abs_le`). General case: apply it to the smooth
bounded truncations `(n+1) · arctan (f / (n+1))`, whose gradients are
dominated by `‖∇f‖`, and pass to the limit by dominated convergence.

Reference: Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov
Diffusion Operators*, Springer, 2014, Proposition 5.1.3. -/
theorem poincare_of_lsi
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    (f : E → ℝ) (hf : Differentiable ℝ f)
    (hf_int : Integrable f μ)
    (hf_sq_int : Integrable (fun x => (f x) ^ 2) μ)
    (hgrad_int : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ) :
    ProbabilityTheory.variance f μ ≤ (1 / c) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  have hc := h_lsi.c_pos
  have hfm : Measurable f := hf.continuous.measurable
  set T : ℕ → E → ℝ := fun n x => ((n : ℝ) + 1) * Real.arctan (f x / ((n : ℝ) + 1))
    with hT_def
  have hTd : ∀ n x, HasFDerivAt (T n)
      (((n : ℝ) + 1) • ((1 / (1 + (f x / ((n : ℝ) + 1)) ^ 2)) •
        (((n : ℝ) + 1)⁻¹ • fderiv ℝ f x))) x := by
    intro n x
    have h1 : HasFDerivAt (fun x => ((n : ℝ) + 1)⁻¹ * f x)
        (((n : ℝ) + 1)⁻¹ • fderiv ℝ f x) x := (hf x).hasFDerivAt.const_mul _
    have h2 := (Real.hasDerivAt_arctan (((n : ℝ) + 1)⁻¹ * f x)).comp_hasFDerivAt x h1
    have h3 := h2.const_mul ((n : ℝ) + 1)
    convert h3 using 2 <;> simp [hT_def, div_eq_inv_mul]
  have hTdiff : ∀ n, Differentiable ℝ (T n) := fun n x => (hTd n x).differentiableAt
  have hTgrad : ∀ n x, ‖fderiv ℝ (T n) x‖ ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2 := by
    intro n x
    rw [(hTd n x).fderiv]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ha : 0 < 1 / (1 + (f x / ((n : ℝ) + 1)) ^ 2) := by positivity
    have ha1 : 1 / (1 + (f x / ((n : ℝ) + 1)) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (f x / ((n : ℝ) + 1))]
    have : ‖((n : ℝ) + 1) • ((1 / (1 + (f x / ((n : ℝ) + 1)) ^ 2)) •
        (((n : ℝ) + 1)⁻¹ • fderiv ℝ f x))‖ ≤ ‖fderiv ℝ f x‖ := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hn, abs_of_pos ha, abs_of_pos (inv_pos.mpr hn)]
      calc ((n : ℝ) + 1) * (1 / (1 + (f x / ((n : ℝ) + 1)) ^ 2) *
            (((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ f x‖))
          = 1 / (1 + (f x / ((n : ℝ) + 1)) ^ 2) * ‖fderiv ℝ f x‖ := by
            field_simp
        _ ≤ 1 * ‖fderiv ℝ f x‖ := by gcongr
        _ = ‖fderiv ℝ f x‖ := one_mul _
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hTm : ∀ n, Measurable (T n) := fun n => (hTdiff n).continuous.measurable
  have hTb : ∀ n x, |T n x| ≤ ((n : ℝ) + 1) * (Real.pi / 2) := by
    intro n x
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hT_def]
    rw [abs_mul, abs_of_pos hn]
    gcongr
    rw [abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have hTle : ∀ n x, |T n x| ≤ |f x| := by
    intro n x
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hT_def]
    rw [abs_mul, abs_of_pos hn]
    calc ((n : ℝ) + 1) * |Real.arctan (f x / ((n : ℝ) + 1))|
        ≤ ((n : ℝ) + 1) * |f x / ((n : ℝ) + 1)| :=
          mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs hn.le
      _ = |f x| := by rw [abs_div, abs_of_pos hn]; field_simp
  -- Poincaré for each truncation.
  have hn : ∀ n, variance (T n) μ ≤ (1 / c) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    intro n
    have hgradT : Integrable (fun x => ‖fderiv ℝ (T n) x‖ ^ 2) μ := by
      refine hgrad_int.mono' ?_ (ae_of_all _ fun x => ?_)
      · exact ((measurable_fderiv ℝ (T n)).norm.pow_const 2).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hTgrad n x
    calc variance (T n) μ ≤ (1 / c) * ∫ x, ‖fderiv ℝ (T n) x‖ ^ 2 ∂μ :=
          variance_le_of_lsi_of_abs_le h_lsi (hTdiff n) (by positivity) (hTb n) hgradT
      _ ≤ (1 / c) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_left (integral_mono hgradT hgrad_int (hTgrad n))
            (by positivity)
  -- Variance convergence by dominated convergence.
  have hlim : ∀ x, Filter.Tendsto (fun n => T n x) Filter.atTop (nhds (f x)) :=
    fun x => tendsto_mul_arctan_div (f x)
  have h1 : Filter.Tendsto (fun n => ∫ x, T n x ∂μ) Filter.atTop (nhds (∫ x, f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (hTm n).aestronglyMeasurable) hf_int.abs
      (fun n => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hTle n x)
      (ae_of_all _ hlim)
  have h2 : Filter.Tendsto (fun n => ∫ x, T n x ^ 2 ∂μ) Filter.atTop
      (nhds (∫ x, f x ^ 2 ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
      (fun n => ((hTm n).pow_const 2).aestronglyMeasurable) hf_sq_int
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow, ← sq_abs (f x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hTle n x) 2)
      (ae_of_all _ fun x => (hlim x).pow 2)
  have hTmem : ∀ n, MemLp (T n) 2 μ := fun n =>
    MemLp.of_bound (hTm n).aestronglyMeasurable _
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hTb n x)
  have hfmem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hf_sq_int
  have hvar : Filter.Tendsto (fun n => variance (T n) μ) Filter.atTop
      (nhds (variance f μ)) := by
    have := h2.sub (h1.pow 2)
    rw [variance_eq_sub hfmem]
    refine this.congr fun n => ?_
    rw [variance_eq_sub (hTmem n)]
    simp [Pi.pow_apply]
  exact le_of_tendsto' hvar hn

end PoincareOfLSI

/-- **Variance bound for Lipschitz observables under LSI.**

For an L-Lipschitz `F` under `LSI(c)`,

  Var_μ(F) ≤ L² / c.

Direct corollary of `poincare_of_lsi` plus the pointwise bound
`‖∇F‖ ≤ L` for a differentiable `L`-Lipschitz `F`
(`norm_fderiv_le_of_lipschitz`). -/
theorem variance_lipschitz_le_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_diff : Differentiable ℝ F)
    (hF_int : Integrable F μ)
    (hF_sq_int : Integrable (fun x => (F x) ^ 2) μ)
    (hgrad_int : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) μ) :
    ProbabilityTheory.variance F μ ≤ ((L : ℝ) ^ 2) / c := by
  have h_poincare := poincare_of_lsi h_lsi F hF_diff hF_int hF_sq_int hgrad_int
  -- Bound: ∫ ‖fderiv ℝ F x‖² ∂μ ≤ L²·μ(univ) = L².
  have h_grad_pt : ∀ x, ‖fderiv ℝ F x‖ ≤ (L : ℝ) :=
    fun x => norm_fderiv_le_of_lipschitz ℝ hF_lip
  have h_grad_sq_le : ∀ x, ‖fderiv ℝ F x‖ ^ 2 ≤ (L : ℝ) ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (h_grad_pt x) 2
  have h_int_grad_le : ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ ≤ (L : ℝ) ^ 2 := by
    calc ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ
        ≤ ∫ _, (L : ℝ) ^ 2 ∂μ :=
          integral_mono hgrad_int (integrable_const _) h_grad_sq_le
      _ = (L : ℝ) ^ 2 := by
          rw [integral_const]
          simp
  have hc_pos : 0 < c := h_lsi.c_pos
  have hc_inv_nn : 0 ≤ 1 / c := div_nonneg zero_le_one hc_pos.le
  calc ProbabilityTheory.variance F μ
      ≤ (1 / c) * ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ := h_poincare
    _ ≤ (1 / c) * (L : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left h_int_grad_le hc_inv_nn
    _ = (L : ℝ) ^ 2 / c := by ring

end MarkovSemigroups.Abstract

end
