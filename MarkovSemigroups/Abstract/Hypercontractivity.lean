/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hypercontractivity and the Gross Equivalence

A *symmetric Markov semigroup* `P_t` on a probability space is
hypercontractive if it maps `L^p → L^q` for suitable `(p, q, t)`. Nelson
(1973) proved this for the OU semigroup; Gross (1975) showed the
equivalence with the log-Sobolev inequality.

## Main definitions

- `MarkovSemigroup` — a symmetric Markov semigroup on a probability
  space, carried by bounded linear operators on `L²(μ)`
  (`Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`).
- `DirichletMarkovSemigroup` — bundles a `MarkovSemigroup` with the
  semigroup's canonical Dirichlet form (the user supplies the form
  data plus the right-derivative-at-zero compatibility on a core
  algebra).
- `MarkovSemigroup.IsHypercontractive` — `‖P_t f‖_{L^q} ≤ ‖f‖_{L^p}`
  when `q ≤ 1 + (p − 1) e^{2ρt}`, formulated with an `L²` source plus
  an explicit `MemLp` hypothesis for the input `L^p` exponent.

## Main results

- `DirichletMarkovSemigroup.not_forall_lsi_implies_hypercontractive` —
  LSI alone does **not** imply hypercontractivity for the bundled
  structure (the core may be too small); the forward direction with its
  core hypotheses is `gross_lsi_implies_hypercontractive_of_hypotheses`
  in `MarkovSemigroups.Abstract.GrossODE`.
- `gross_hypercontractive_implies_lsi` — hypercontractivity ⇒ LSI.

## Why bundle?

The form-vs-semigroup link `E(f, g) = -(d/dt)|_{t=0+} ⟨[f], P_t [g]⟩` is
essential for Gross. Without it the two are unrelated and Gross's
theorem has no content. Bundling them into a single structure
(`DirichletMarkovSemigroup`) makes the link a structural invariant
rather than a side hypothesis.

The semigroup is the *primary* datum: for symmetric Markov semigroups,
the Dirichlet form is canonically determined (Fukushima–Oshima–Takeda
construction). The user-supplied `energy`/`IsCore` fields are a
certified presentation of that canonical form on a chosen core
algebra.

## References

- Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973)
- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975)
- Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §1.3-1.4 and §5.2
- Fukushima-Oshima-Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 1994, §1.3
- Simon, *The P(φ)₂ Euclidean QFT*, Princeton, 1974, Ch. I
-/

import MarkovSemigroups.Abstract.DirichletForm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open MeasureTheory ENNReal Set
open scoped ENNReal InnerProductSpace

noncomputable section

/-- A *symmetric Markov semigroup* on a probability space `(X, μ)`.

This is the standard setup for Gross's LSI/HC equivalence: a strongly
continuous *symmetric* contraction semigroup on `L²(μ)` preserving
positivity and any a.e.-constant-`1` element.

Time parameter `t : ℝ` is conventionally only meaningful for `t ≥ 0` —
all properties below are stated under that condition. Restricting to
`t ≥ 0` (rather than allowing all of `ℝ`) avoids the trap where a
two-sided contraction semigroup is forced by Stone's theorem to be a
group of isometries with skew-adjoint generator, incompatible with the
self-adjointness implied by symmetry. -/
structure MarkovSemigroup (X : Type*) [MeasurableSpace X] where
  /-- Reference probability measure. -/
  μ : Measure X
  /-- The measure is a probability measure. -/
  hμ : IsProbabilityMeasure μ
  /-- Bounded linear operator on `L²(μ)` at each time `t`. -/
  P : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  /-- `P 0 = id`. -/
  P_zero : P 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)
  /-- Semigroup property (for `s, t ≥ 0`). -/
  P_semigroup : ∀ s t, 0 ≤ s → 0 ≤ t → P (s + t) = (P s).comp (P t)
  /-- Strong continuity at `t = 0+`. -/
  P_strong_cont : ∀ f : Lp ℝ 2 μ,
    Filter.Tendsto (fun t : ℝ => P t f) (nhdsWithin 0 (Set.Ici 0)) (nhds f)
  /-- Operator-norm contraction on `L²(μ)`. -/
  P_contraction : ∀ t, 0 ≤ t → ‖P t‖ ≤ 1
  /-- Markov property: `P_t` fixes any a.e.-constant-`1` element of `L²(μ)`. -/
  P_conservation : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ,
    (∀ᵐ x ∂μ, (f : X → ℝ) x = 1) → P t f = f
  /-- Positivity preservation on `L²(μ)`. -/
  P_positivity : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ, 0 ≤ f → 0 ≤ P t f
  /-- Symmetry of `P_t` on `L²(μ)`. -/
  P_symmetric : ∀ t, 0 ≤ t → ∀ f g : Lp ℝ 2 μ,
    ⟪f, P t g⟫_ℝ = ⟪P t f, g⟫_ℝ

attribute [instance] MarkovSemigroup.hμ

namespace MarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- Each `P_t` is self-adjoint on `L²(μ)` by the symmetry field. -/
lemma isSelfAdjoint (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (S.P t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simpa using (S.P_symmetric t ht f g).symm

/-- **L^∞-contraction.** For a symmetric Markov semigroup with conservation
of constants (i.e., `P_t 1 = 1`), if `|f y| ≤ M` a.e. then
`|(P_t f) y| ≤ M` a.e. Standard textbook fact derivable purely from the
existing `MarkovSemigroup` fields (no extra hypothesis needed): the trick
is `0 ≤ Lp.const M - f` (a.e. from the bound) + `P_positivity` +
`P_conservation` (used to deduce `P_t (Lp.const M) = Lp.const M` via
`Lp.const M = M • Lp.const 1`). -/
lemma Linfty_contraction (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {M : ℝ}
    (hf : ∀ᵐ y ∂S.μ, |(f : X → ℝ) y| ≤ M) :
    ∀ᵐ y ∂S.μ, |(S.P t f : X → ℝ) y| ≤ M := by
  haveI : IsFiniteMeasure S.μ := inferInstance
  set Mlp : Lp ℝ 2 S.μ := Lp.const 2 S.μ M with hMlp_def
  have hMlp_coe : (Mlp : X → ℝ) =ᵐ[S.μ] fun _ => M := Lp.coeFn_const 2 S.μ M
  -- Conservation: P_t (Lp.const 1) = Lp.const 1.
  have hPt_const1 : S.P t (Lp.const 2 S.μ (1:ℝ)) = Lp.const 2 S.μ (1:ℝ) := by
    refine S.P_conservation t ht _ ?_
    filter_upwards [Lp.coeFn_const 2 S.μ (1:ℝ)] with x hx
    exact hx
  -- Lp.const M = M • Lp.const 1 (Lp identifies a.e. equal functions).
  have hMlp_smul : Mlp = M • Lp.const 2 S.μ (1:ℝ) := by
    refine Lp.ext ?_
    filter_upwards [hMlp_coe, Lp.coeFn_smul M (Lp.const 2 S.μ (1:ℝ)),
                    Lp.coeFn_const 2 S.μ (1:ℝ)] with y h1 h2 _
    simp [h1, h2]
  -- Hence P_t (Lp.const M) = Lp.const M.
  have hPt_Mlp : S.P t Mlp = Mlp := by
    calc S.P t Mlp
        = S.P t (M • Lp.const 2 S.μ (1:ℝ)) := by rw [hMlp_smul]
      _ = M • S.P t (Lp.const 2 S.μ (1:ℝ)) := (S.P t).map_smul M _
      _ = M • Lp.const 2 S.μ (1:ℝ) := by rw [hPt_const1]
      _ = Mlp := hMlp_smul.symm
  -- Upper bound: P_t f ≤ M pointwise a.e. via 0 ≤ Mlp - f in Lp.
  have h_upper : ∀ᵐ y ∂S.μ, (S.P t f : X → ℝ) y ≤ M := by
    -- The a.e.-pointwise nonneg of ↑↑(Mlp - f), via Lp.coeFn_sub bridge.
    have h_diff_ae : 0 ≤ᵐ[S.μ] (↑↑(Mlp - f) : X → ℝ) := by
      filter_upwards [hf, hMlp_coe, Lp.coeFn_sub Mlp f] with y hy hMy hSubY
      have : (↑↑(Mlp - f) : X → ℝ) y = M - (f : X → ℝ) y := by
        rw [hSubY]; simp [hMy]
      rw [Pi.zero_apply, this]
      linarith [le_of_abs_le hy]
    have h_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ Mlp - f := (Lp.coeFn_nonneg _).mp h_diff_ae
    have h_pt_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (Mlp - f) :=
      S.P_positivity t ht _ h_diff_nn
    have h_pt_orbit_sub : S.P t (Mlp - f) = Mlp - S.P t f := by
      rw [map_sub, hPt_Mlp]
    rw [h_pt_orbit_sub] at h_pt_diff_nn
    have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_diff_nn
    filter_upwards [h_ae, Lp.coeFn_sub Mlp (S.P t f), hMlp_coe] with y hy hSub hMy
    have h_pt : (↑↑(Mlp - S.P t f) : X → ℝ) y = M - (S.P t f : X → ℝ) y := by
      rw [hSub]; simp [hMy]
    rw [Pi.zero_apply, h_pt] at hy
    linarith
  -- Lower bound: -M ≤ P_t f pointwise a.e. via 0 ≤ Mlp + f in Lp.
  have h_lower : ∀ᵐ y ∂S.μ, (-M : ℝ) ≤ (S.P t f : X → ℝ) y := by
    have h_sum_ae : 0 ≤ᵐ[S.μ] (↑↑(Mlp + f) : X → ℝ) := by
      filter_upwards [hf, hMlp_coe, Lp.coeFn_add Mlp f] with y hy hMy hAddY
      have : (↑↑(Mlp + f) : X → ℝ) y = M + (f : X → ℝ) y := by
        rw [hAddY]; simp [hMy]
      rw [Pi.zero_apply, this]
      linarith [neg_le_of_abs_le hy]
    have h_sum_nn : (0 : Lp ℝ 2 S.μ) ≤ Mlp + f := (Lp.coeFn_nonneg _).mp h_sum_ae
    have h_pt_sum_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (Mlp + f) :=
      S.P_positivity t ht _ h_sum_nn
    have h_pt_orbit_add : S.P t (Mlp + f) = Mlp + S.P t f := by
      rw [map_add, hPt_Mlp]
    rw [h_pt_orbit_add] at h_pt_sum_nn
    have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_sum_nn
    filter_upwards [h_ae, Lp.coeFn_add Mlp (S.P t f), hMlp_coe] with y hy hAdd hMy
    have h_pt : (↑↑(Mlp + S.P t f) : X → ℝ) y = M + (S.P t f : X → ℝ) y := by
      rw [hAdd]; simp [hMy]
    rw [Pi.zero_apply, h_pt] at hy
    linarith
  filter_upwards [h_upper, h_lower] with y hyu hyl
  exact abs_le.mpr ⟨hyl, hyu⟩

/-- **L^∞ orbit ⇒ all L^p memberships.** Companion to `Linfty_contraction`:
once the orbit is uniformly bounded a.e., it lies in every `MemLp p` on
the finite measure `S.μ`. -/
lemma orbit_memLp (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {M : ℝ}
    (hf : ∀ᵐ y ∂S.μ, |(f : X → ℝ) y| ≤ M) (p : ℝ≥0∞) :
    MemLp ((S.P t f : X → ℝ)) p S.μ := by
  haveI : IsFiniteMeasure S.μ := inferInstance
  refine MemLp.of_bound (Lp.aestronglyMeasurable _) M ?_
  filter_upwards [S.Linfty_contraction ht hf] with y hy
  simpa using hy

/-- **Lower-bound contraction.** Companion to `Linfty_contraction`: if
`f ≥ ε` a.e., then `(P_t f) ≥ ε` a.e. (for `t ≥ 0`). Same template:
`0 ≤ f - Lp.const ε` (a.e.) + `P_positivity` + `P_t (Lp.const ε) = Lp.const ε`
(via conservation + scalar). The dual of `Linfty_contraction`, but stated
in *one-sided* form because Gross-style positivity arguments only need
the lower bound `(P_s f) ≥ ε`, not |·| ≤ M. -/
lemma orbit_lower_bound (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {ε : ℝ}
    (hf : ∀ᵐ y ∂S.μ, ε ≤ (f : X → ℝ) y) :
    ∀ᵐ y ∂S.μ, ε ≤ (S.P t f : X → ℝ) y := by
  haveI : IsFiniteMeasure S.μ := inferInstance
  set εlp : Lp ℝ 2 S.μ := Lp.const 2 S.μ ε with hεlp_def
  have hεlp_coe : (εlp : X → ℝ) =ᵐ[S.μ] fun _ => ε := Lp.coeFn_const 2 S.μ ε
  have hPt_const1 : S.P t (Lp.const 2 S.μ (1:ℝ)) = Lp.const 2 S.μ (1:ℝ) := by
    refine S.P_conservation t ht _ ?_
    filter_upwards [Lp.coeFn_const 2 S.μ (1:ℝ)] with x hx
    exact hx
  have hεlp_smul : εlp = ε • Lp.const 2 S.μ (1:ℝ) := by
    refine Lp.ext ?_
    filter_upwards [hεlp_coe, Lp.coeFn_smul ε (Lp.const 2 S.μ (1:ℝ)),
                    Lp.coeFn_const 2 S.μ (1:ℝ)] with y h1 h2 _
    simp [h1, h2]
  have hPt_εlp : S.P t εlp = εlp := by
    calc S.P t εlp
        = S.P t (ε • Lp.const 2 S.μ (1:ℝ)) := by rw [hεlp_smul]
      _ = ε • S.P t (Lp.const 2 S.μ (1:ℝ)) := (S.P t).map_smul ε _
      _ = ε • Lp.const 2 S.μ (1:ℝ) := by rw [hPt_const1]
      _ = εlp := hεlp_smul.symm
  -- 0 ≤ f - εlp via the a.e. bound.
  have h_diff_ae : 0 ≤ᵐ[S.μ] (↑↑(f - εlp) : X → ℝ) := by
    filter_upwards [hf, hεlp_coe, Lp.coeFn_sub f εlp] with y hy hMy hSubY
    have : (↑↑(f - εlp) : X → ℝ) y = (f : X → ℝ) y - ε := by
      rw [hSubY]; simp [hMy]
    rw [Pi.zero_apply, this]
    linarith
  have h_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ f - εlp := (Lp.coeFn_nonneg _).mp h_diff_ae
  have h_pt_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (f - εlp) :=
    S.P_positivity t ht _ h_diff_nn
  have h_pt_orbit_sub : S.P t (f - εlp) = S.P t f - εlp := by
    rw [map_sub, hPt_εlp]
  rw [h_pt_orbit_sub] at h_pt_diff_nn
  have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_diff_nn
  filter_upwards [h_ae, Lp.coeFn_sub (S.P t f) εlp, hεlp_coe] with y hy hSub hMy
  have h_pt : (↑↑(S.P t f - εlp) : X → ℝ) y = (S.P t f : X → ℝ) y - ε := by
    rw [hSub]; simp [hMy]
  rw [Pi.zero_apply, h_pt] at hy
  linarith

/-- **Strong continuity at any `s ≥ 0`.** `P_strong_cont` gives this at
`t = 0`; the semigroup property + `P_contraction` (`‖P t‖ ≤ 1`)
upgrade it to every `s ≥ 0`, via the standard textbook argument:
* Approach from above: for `σ = s + t` with `t > 0`,
  `‖P σ g - P s g‖ = ‖P s (P t g) - P s g‖ ≤ ‖P t g - g‖ → 0`.
* Approach from below: for `σ < s`, `P s g = P σ (P (s-σ) g)`, so
  `‖P σ g - P s g‖ = ‖P σ (g - P (s-σ) g)‖ ≤ ‖g - P (s-σ) g‖ → 0`. -/
lemma strong_cont_at (S : MarkovSemigroup X) (g : Lp ℝ 2 S.μ) {s : ℝ}
    (hs : 0 ≤ s) :
    Filter.Tendsto (fun σ : ℝ => S.P σ g) (nhdsWithin s (Set.Ici 0))
      (nhds (S.P s g)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcont0 := S.P_strong_cont g
  rw [Metric.tendsto_nhdsWithin_nhds] at hcont0
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont0 ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro σ hσ_in hσ_dist
  rcases lt_trichotomy σ s with hσ_lt | hσ_eq | hσ_gt
  · -- σ < s: P s g = P σ (P (s-σ) g), so P σ g - P s g = P σ (g - P (s-σ) g).
    have hr_pos : 0 < s - σ := sub_pos.mpr hσ_lt
    have hr_dist : dist (s - σ) 0 < δ := by
      have : dist (s - σ) 0 = s - σ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr_pos]
      rw [this]
      have habsσ : |σ - s| < δ := by simpa [Real.dist_eq] using hσ_dist
      have := abs_lt.mp habsσ; linarith
    have h_g_close : dist (S.P (s - σ) g) g < ε := hδ hr_pos.le hr_dist
    have h_decomp : S.P s g = S.P σ (S.P (s - σ) g) := by
      have h_sg : S.P (σ + (s - σ)) = (S.P σ).comp (S.P (s - σ)) :=
        S.P_semigroup σ (s - σ) hσ_in hr_pos.le
      calc S.P s g = S.P (σ + (s - σ)) g := by rw [show σ + (s - σ) = s from by ring]
        _ = ((S.P σ).comp (S.P (s - σ))) g := by rw [h_sg]
        _ = S.P σ (S.P (s - σ) g) := rfl
    rw [h_decomp]
    -- dist (P σ g) (P σ (P (s-σ) g)) ≤ ‖P σ‖ · dist g (P (s-σ) g) ≤ dist g (P (s-σ) g) < ε.
    calc dist (S.P σ g) (S.P σ (S.P (s - σ) g))
        ≤ ‖S.P σ‖ * dist g (S.P (s - σ) g) := by
          simpa [dist_eq_norm] using (S.P σ).lipschitzWith.norm_sub_le g (S.P (s - σ) g)
      _ ≤ dist g (S.P (s - σ) g) :=
          mul_le_of_le_one_left dist_nonneg (S.P_contraction σ hσ_in)
      _ = dist (S.P (s - σ) g) g := dist_comm _ _
      _ < ε := h_g_close
  · -- σ = s.
    subst hσ_eq; simpa using hε
  · -- σ > s: P σ g = P s (P (σ-s) g).
    have hr_pos : 0 < σ - s := sub_pos.mpr hσ_gt
    have hr_dist : dist (σ - s) 0 < δ := by
      have : dist (σ - s) 0 = σ - s := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr_pos]
      rw [this]
      have habsσ : |σ - s| < δ := by simpa [Real.dist_eq] using hσ_dist
      linarith [abs_lt.mp habsσ]
    have h_g_close : dist (S.P (σ - s) g) g < ε := hδ hr_pos.le hr_dist
    have h_decomp : S.P σ g = S.P s (S.P (σ - s) g) := by
      have h_sg : S.P (s + (σ - s)) = (S.P s).comp (S.P (σ - s)) :=
        S.P_semigroup s (σ - s) hs hr_pos.le
      calc S.P σ g = S.P (s + (σ - s)) g := by rw [show s + (σ - s) = σ from by ring]
        _ = ((S.P s).comp (S.P (σ - s))) g := by rw [h_sg]
        _ = S.P s (S.P (σ - s) g) := rfl
    rw [h_decomp]
    calc dist (S.P s (S.P (σ - s) g)) (S.P s g)
        ≤ ‖S.P s‖ * dist (S.P (σ - s) g) g := by
          simpa [dist_eq_norm] using (S.P s).lipschitzWith.norm_sub_le (S.P (σ - s) g) g
      _ ≤ dist (S.P (σ - s) g) g := mul_le_of_le_one_left dist_nonneg (S.P_contraction s hs)
      _ < ε := h_g_close

/-- **Orbit has right derivative `P_s Af` at any `s ≥ 0`.** From the
strong-L² derivative `Af` at `t = 0` (given by e.g. `GeneratorCompat`),
the orbit `σ ↦ P_σ f` is differentiable at every `s ≥ 0` (within
`Ici 0`) with derivative `P_s Af`. Standard semigroup commutation
trick + `strong_cont_at`:
* For `σ > s`: write `σ = s + t`, then
  `(σ-s)⁻¹ • (P_σ f - P_s f) = P_s (t⁻¹ • (P_t f - f)) → P_s Af`
  by linearity of `P_s` and the `t→0+` limit.
* For `σ < s`: write `s = σ + r`, then
  `(σ-s)⁻¹ • (P_σ f - P_s f) = P_σ (r⁻¹ • (P_r f - f))`,
  and we need the joint limit `P_σ (x_σ) → P_s (Af)` where
  `x_σ → Af` and `P_σ → P_s` strongly. The standard triangle bound
  `‖P_σ x_σ - P_s Af‖ ≤ ‖P_σ‖·‖x_σ - Af‖ + ‖P_σ Af - P_s Af‖` plus
  `‖P_σ‖ ≤ 1` + `strong_cont_at` closes it. -/
lemma orbit_hasDerivWithinAt (S : MarkovSemigroup X)
    {f Af : Lp ℝ 2 S.μ}
    (hAf : Filter.Tendsto (fun t : ℝ => t⁻¹ • (S.P t f - f))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Af))
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun σ : ℝ => S.P σ f) (S.P s Af) (Set.Ici 0) s := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  -- Goal: Tendsto (slope (fun σ => P σ f) s) (𝓝[Ici 0 \ {s}] s) (𝓝 (P s Af))
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- From hAf in metric form.
  have hAf_metric :
      ∀ ε' > 0, ∃ δ' > 0, ∀ t, 0 < t → dist t 0 < δ' →
        dist (t⁻¹ • (S.P t f - f)) Af < ε' := by
    intro ε' hε'
    rw [Metric.tendsto_nhdsWithin_nhds] at hAf
    obtain ⟨δ, hδ, h⟩ := hAf ε' hε'
    exact ⟨δ, hδ, fun t ht hdt => h ht hdt⟩
  -- From strong_cont_at at s for Af.
  have hcont := S.strong_cont_at Af hs
  rw [Metric.tendsto_nhdsWithin_nhds] at hcont
  obtain ⟨δ_cont, hδ_cont_pos, hδ_cont⟩ := hcont (ε / 2) (by linarith)
  obtain ⟨δ_Af, hδ_Af_pos, hδ_Af⟩ := hAf_metric (ε / 2) (by linarith)
  refine ⟨min δ_cont δ_Af, by positivity, ?_⟩
  intro σ hσ_in hσ_dist
  -- hσ_in : σ ∈ Ici 0 \ {s}.
  obtain ⟨hσ_ge0, hσ_ne⟩ := hσ_in
  simp only [Set.mem_singleton_iff] at hσ_ne
  have hσ_dist_cont : dist σ s < δ_cont :=
    lt_of_lt_of_le hσ_dist (min_le_left _ _)
  have hσ_dist_Af : dist σ s < δ_Af :=
    lt_of_lt_of_le hσ_dist (min_le_right _ _)
  -- Slope: (σ - s)⁻¹ • (P σ f - P s f)
  show dist (slope (fun σ => S.P σ f) s σ) (S.P s Af) < ε
  rw [slope_def_module]
  rcases lt_or_gt_of_ne hσ_ne with hσ_lt | hσ_gt
  · -- σ < s: write s = σ + (s - σ), use P s = P σ ∘ P (s-σ).
    have hr_pos : 0 < s - σ := sub_pos.mpr hσ_lt
    have hr_dist : dist (s - σ) 0 < δ_Af := by
      have : |s - σ| = s - σ := abs_of_pos hr_pos
      have : dist (s - σ) 0 = s - σ := by rw [Real.dist_eq, sub_zero, this]
      rw [this]
      have habsσ : |σ - s| < δ_Af := by simpa [Real.dist_eq] using hσ_dist_Af
      linarith [abs_lt.mp habsσ]
    have h_close_inner :
        dist ((s - σ)⁻¹ • (S.P (s - σ) f - f)) Af < ε / 2 :=
      hδ_Af _ hr_pos hr_dist
    -- P s f = P σ (P (s - σ) f).
    have hP_decomp : S.P s f = S.P σ (S.P (s - σ) f) := by
      have h := S.P_semigroup σ (s - σ) hσ_ge0 hr_pos.le
      have : S.P (σ + (s - σ)) f = (S.P σ).comp (S.P (s - σ)) f := by
        rw [h]
      simpa [show σ + (s - σ) = s from by ring] using this
    -- Slope: (σ - s)⁻¹ • (P σ f - P s f) = (σ - s)⁻¹ • (P σ f - P σ (P (s-σ) f))
    --      = (σ - s)⁻¹ • P σ (f - P (s-σ) f)
    --      = - (s - σ)⁻¹ • P σ (f - P (s-σ) f)
    --      = (s - σ)⁻¹ • P σ (P (s-σ) f - f)
    --      = P σ ((s - σ)⁻¹ • (P (s-σ) f - f))
    have h_slope_eq : (σ - s)⁻¹ • (S.P σ f - S.P s f)
        = S.P σ ((s - σ)⁻¹ • (S.P (s - σ) f - f)) := by
      rw [hP_decomp, ← map_sub (S.P σ), ← map_smul]
      congr 1
      calc (σ - s)⁻¹ • (f - S.P (s - σ) f)
          = -((s - σ)⁻¹) • (f - S.P (s - σ) f) := by
              rw [show σ - s = -(s - σ) from by ring, inv_neg]
        _ = -((s - σ)⁻¹ • (f - S.P (s - σ) f)) := by rw [neg_smul]
        _ = (s - σ)⁻¹ • -(f - S.P (s - σ) f) := by rw [← smul_neg]
        _ = (s - σ)⁻¹ • (S.P (s - σ) f - f) := by rw [neg_sub]
    rw [h_slope_eq]
    set inner := (s - σ)⁻¹ • (S.P (s - σ) f - f)
    -- Step 1: dist (P σ inner) (P σ Af) ≤ ‖P σ‖ * dist inner Af ≤ dist inner Af.
    have h1 : dist (S.P σ inner) (S.P σ Af) ≤ dist inner Af := by
      have hnorm : ‖S.P σ inner - S.P σ Af‖ ≤ ‖S.P σ‖ * ‖inner - Af‖ := by
        rw [← map_sub]; exact (S.P σ).le_opNorm _
      calc dist (S.P σ inner) (S.P σ Af)
          = ‖S.P σ inner - S.P σ Af‖ := dist_eq_norm _ _
        _ ≤ ‖S.P σ‖ * ‖inner - Af‖ := hnorm
        _ ≤ 1 * ‖inner - Af‖ := by
            have hle : ‖S.P σ‖ ≤ 1 := S.P_contraction σ hσ_ge0
            have hnn : 0 ≤ ‖inner - Af‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_right hle hnn
        _ = ‖inner - Af‖ := one_mul _
        _ = dist inner Af := (dist_eq_norm _ _).symm
    -- Step 2: dist (P σ Af) (P s Af) < ε / 2 by strong continuity at s.
    have h2 : dist (S.P σ Af) (S.P s Af) < ε / 2 := hδ_cont hσ_ge0 hσ_dist_cont
    -- Triangle: < ε/2 + ε/2.
    calc dist (S.P σ inner) (S.P s Af)
        ≤ dist (S.P σ inner) (S.P σ Af) + dist (S.P σ Af) (S.P s Af) :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by linarith [h1, h_close_inner]
      _ = ε := by ring
  · -- σ > s: write σ = s + (σ - s), use P σ = P s ∘ P (σ-s).
    have ht_pos : 0 < σ - s := sub_pos.mpr hσ_gt
    have ht_dist : dist (σ - s) 0 < δ_Af := by
      have : |σ - s| = σ - s := abs_of_pos ht_pos
      have heq : dist (σ - s) 0 = σ - s := by rw [Real.dist_eq, sub_zero, this]
      rw [heq]
      have habsσ : |σ - s| < δ_Af := by simpa [Real.dist_eq] using hσ_dist_Af
      linarith [abs_lt.mp habsσ]
    have h_close_inner :
        dist ((σ - s)⁻¹ • (S.P (σ - s) f - f)) Af < ε / 2 :=
      hδ_Af _ ht_pos ht_dist
    -- P σ f = P s (P (σ - s) f).
    have hP_decomp : S.P σ f = S.P s (S.P (σ - s) f) := by
      have h := S.P_semigroup s (σ - s) hs ht_pos.le
      have : S.P (s + (σ - s)) f = (S.P s).comp (S.P (σ - s)) f := by rw [h]
      simpa [show s + (σ - s) = σ from by ring] using this
    -- Slope: (σ - s)⁻¹ • (P σ f - P s f) = (σ - s)⁻¹ • (P s (P (σ-s) f) - P s f)
    --      = P s ((σ - s)⁻¹ • (P (σ-s) f - f))
    have h_slope_eq : (σ - s)⁻¹ • (S.P σ f - S.P s f)
        = S.P s ((σ - s)⁻¹ • (S.P (σ - s) f - f)) := by
      rw [hP_decomp, ← map_sub (S.P s), ← map_smul]
    rw [h_slope_eq]
    set inner := (σ - s)⁻¹ • (S.P (σ - s) f - f)
    have hnorm : ‖S.P s inner - S.P s Af‖ ≤ ‖S.P s‖ * ‖inner - Af‖ := by
      rw [← map_sub]; exact (S.P s).le_opNorm _
    calc dist (S.P s inner) (S.P s Af)
        = ‖S.P s inner - S.P s Af‖ := dist_eq_norm _ _
      _ ≤ ‖S.P s‖ * ‖inner - Af‖ := hnorm
      _ ≤ 1 * ‖inner - Af‖ := by
          have hle : ‖S.P s‖ ≤ 1 := S.P_contraction s hs
          exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = ‖inner - Af‖ := one_mul _
      _ = dist inner Af := (dist_eq_norm _ _).symm
      _ < ε / 2 := h_close_inner
      _ < ε := by linarith

/-- A symmetric Markov semigroup is *hypercontractive* with rate `ρ > 0`
if `P_t : L^p → L^q` is a contraction whenever
`q ≤ 1 + (p − 1) · e^{2ρt}`:

  `‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}`.

The source is the `L²(μ)` carrier, together with an explicit `MemLp`
hypothesis at exponent `p`. This handles both `p < 2` and `p > 2`
without changing the abstract carrier. -/
def IsHypercontractive (S : MarkovSemigroup X) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ (p q t : ℝ),
    1 < p → p ≤ q → 0 < t →
    q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t) →
    ∀ f : Lp ℝ 2 S.μ,
      MemLp ((⇑f) : X → ℝ) (ENNReal.ofReal p) S.μ →
      eLpNorm (((S.P t f) : X → ℝ)) (ENNReal.ofReal q) S.μ ≤
        eLpNorm ((⇑f) : X → ℝ) (ENNReal.ofReal p) S.μ

end MarkovSemigroup

/-- A *Dirichlet-Markov semigroup*: a symmetric Markov semigroup
bundled with its canonical Dirichlet form.

For a symmetric Markov semigroup the Dirichlet form is uniquely
determined by the semigroup as

  `E(f, g) = lim_{t↘0} (1/t) · ⟨[f], (I − P_t)[g]⟩
          = -(d/dt)|_{t=0+} ⟨[f], P_t[g]⟩`

(Fukushima–Oshima–Takeda construction). The user supplies a candidate
form `energy` together with an admissible core algebra `IsCore`, and
asserts via `energy_eq_deriv` that the candidate equals the canonical
form on the core (as a right-derivative at `0`). -/
structure DirichletMarkovSemigroup (X : Type*) [MeasurableSpace X]
    extends MarkovSemigroup X where
  /-- The Dirichlet form `E(f, g)`. -/
  energy : (X → ℝ) → (X → ℝ) → ℝ
  /-- Energy is symmetric. -/
  energy_symm : ∀ f g, energy f g = energy g f
  /-- Energy is nonnegative on the diagonal. -/
  energy_nonneg : ∀ f, 0 ≤ energy f f
  /-- Admissible core functions. -/
  IsCore : (X → ℝ) → Prop
  /-- Constants are core. -/
  IsCore_const : ∀ c : ℝ, IsCore (fun _ => c)
  /-- Core is closed under addition. -/
  IsCore_add : ∀ {f g}, IsCore f → IsCore g → IsCore (f + g)
  /-- Core is closed under scalar multiplication. -/
  IsCore_smul : ∀ (c : ℝ) {f}, IsCore f → IsCore (c • f)
  /-- **Strict-positive rpow closure** (Gross's strictly-positive escape).
  When `f` is in the core and `f ≥ ε > 0` a.e. for some explicit
  `ε > 0`, then `x ↦ f x ^ r` is also in the core for any real `r`. This
  is the standard "Markovian core" closure under smooth functional
  calculus, restricted to strictly positive elements (which is all we
  need for the Gross argument — see
  `plans/archive/gross-design-strictly-positive-escape.md`). Note that the
  axiom uses `Real.rpow` directly (the syntactic form appearing in
  `grossPow`), so no a.e./pointwise bridging is needed; the null set
  where `f y ≤ 0` is benign because `rpow_def_of_neg` matches the
  convention used everywhere in this file (compare BGL Ch 1, "algebra
  of admissible test functions"). Mathematically, for concrete cores
  like `C^∞_b(ℝ^n)` on Gaussian measure, this is immediate: adding a
  positive constant to a `C^∞_b` element gives `f ≥ ε > 0` *everywhere*,
  and `f^r` is then `C^∞_b` by chain rule. -/
  IsCore_rpow_pos_strict : ∀ {f : X → ℝ} (_ : IsCore f) {ε : ℝ} (_ : 0 < ε),
    (∀ᵐ y ∂μ, ε ≤ f y) → ∀ (r : ℝ), IsCore (fun x => f x ^ r)
  /-- **L^∞ membership.** Every core function is essentially bounded.
  This is the standard BGL hypothesis on the "algebra of admissible
  test functions" (cf. BGL §1.4: "an algebra of *bounded* functions
  in the generator domain"). For `C^∞_b`-style cores (`IsCoreFin`,
  Schwartz-with-Gaussian-tweaks, polynomial cores on probability
  measures) this is immediate from the bounded-derivatives part of
  the definition. Needed by `grossPow_hasDerivWithinAt` to invoke
  `hasDerivAt_integral_rpow_exponent` (which requires a uniform
  bound `|w y| ≤ M` on the integrand) and to combine with `hf_pos`
  for `ε ≤ f ≤ M` framing. -/
  IsCore_memLp_top : ∀ {f : X → ℝ}, IsCore f → ∃ M : ℝ, ∀ᵐ y ∂μ, |f y| ≤ M
  /-- Energy is bilinear on the left. -/
  energy_add_left : ∀ f₁ f₂ g, IsCore f₁ → IsCore f₂ → IsCore g →
    energy (f₁ + f₂) g = energy f₁ g + energy f₂ g
  /-- Energy is homogeneous on the left. -/
  energy_smul_left : ∀ (c : ℝ) f g, IsCore f → IsCore g →
    energy (c • f) g = c * energy f g
  /-- Constants have zero energy. -/
  energy_const : ∀ c : ℝ, energy (fun _ => c) (fun _ => c) = 0
  /-- Every core function lies in `L²(μ)`. -/
  IsCore_memLp : ∀ {f}, IsCore f → MemLp f 2 μ
  /-- **Generator–Dirichlet-form compatibility.** The energy form is
  the (negated) right-derivative-at-zero of the `L²(μ)` pairing
  `⟨[f], P_t[g]⟩`. -/
  energy_eq_deriv : ∀ f g (hf : IsCore f) (hg : IsCore g),
    let coreToL2 : ∀ {h : X → ℝ}, IsCore h → Lp ℝ 2 μ :=
      fun {h} hh => (IsCore_memLp hh).toLp h
    HasDerivWithinAt
      (fun t : ℝ => ⟪coreToL2 hf, P t (coreToL2 hg)⟫_ℝ)
      (-energy f g) (Set.Ici 0) 0

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- View a core function as an element of `L²(μ)`. -/
def coreToL2 (D : DirichletMarkovSemigroup X) {f : X → ℝ} (hf : D.IsCore f) :
    Lp ℝ 2 D.μ :=
  (D.IsCore_memLp hf).toLp f

/-- The Dirichlet form data of a `DirichletMarkovSemigroup` packages
into a `DirichletSpace`. -/
@[reducible]
def toDirichletSpace (D : DirichletMarkovSemigroup X) : DirichletSpace X where
  μ := D.μ
  hμ := D.hμ
  energy := D.energy
  energy_symm := D.energy_symm
  energy_nonneg := D.energy_nonneg
  IsCore := D.IsCore
  IsCore_const := D.IsCore_const
  IsCore_add := D.IsCore_add
  IsCore_smul := D.IsCore_smul
  energy_add_left := D.energy_add_left
  energy_smul_left := D.energy_smul_left
  energy_const := D.energy_const

/-- LSI for the bundled structure: LSI for the underlying Dirichlet form. -/
def SatisfiesLogSobolev (D : DirichletMarkovSemigroup X) (ρ : ℝ) : Prop :=
  let _ : DirichletSpace X := D.toDirichletSpace
  DirichletSpace.SatisfiesLogSobolev (X := X) ρ

/-- Hypercontractivity for the bundled structure: hypercontractivity
of the underlying `L²` semigroup. -/
def IsHypercontractive (D : DirichletMarkovSemigroup X) (ρ : ℝ) : Prop :=
  D.toMarkovSemigroup.IsHypercontractive ρ

end DirichletMarkovSemigroup

/-! ## Stroock–Varopoulos inequality (intermediate-step lemma) -/

/-! ### Stroock–Varopoulos for Markov operators on `L²`

Generic `L²` facts for a positive, conservative, symmetric operator `T`:
the Dirichlet-type form `⟪φ∘F, (I - T)(ψ∘F)⟫` of a finite-valued `F` as a
double sum over level sets, and the operator Stroock–Varopoulos inequality
for bounded nonnegative `F`. -/

namespace MarkovOperator

open scoped InnerProductSpace

/-- **Scalar Stroock–Varopoulos inequality.** For `p > 1` and `a, b ≥ 0`,
`(4(p-1)/p²) (a^{p/2} - b^{p/2})² ≤ (a - b)(a^{p-1} - b^{p-1})`
(Cauchy–Schwarz for `∫_b^a s^{p/2-1} ds`). -/
lemma sv_scalar {p : ℝ} (hp : 1 < p) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * (p - 1) / p ^ 2 * (a ^ (p / 2) - b ^ (p / 2)) ^ 2 ≤
      (a - b) * (a ^ (p - 1) - b ^ (p - 1)) := by
  wlog hab : b ≤ a generalizing a b
  · have := this hb ha (le_of_not_ge hab)
    calc 4 * (p - 1) / p ^ 2 * (a ^ (p / 2) - b ^ (p / 2)) ^ 2
        = 4 * (p - 1) / p ^ 2 * (b ^ (p / 2) - a ^ (p / 2)) ^ 2 := by ring
      _ ≤ (b - a) * (b ^ (p - 1) - a ^ (p - 1)) := this
      _ = (a - b) * (a ^ (p - 1) - b ^ (p - 1)) := by ring
  have hp0 : 0 < p := by linarith
  have hc1 : 4 * (p - 1) / p ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (p - 2)]
  have hc0 : 0 ≤ 4 * (p - 1) / p ^ 2 := by
    apply div_nonneg _ (by positivity); linarith
  rcases hb.eq_or_lt with rfl | hb0
  · rw [Real.zero_rpow (by positivity), Real.zero_rpow (by linarith), sub_zero, sub_zero,
      sub_zero]
    have h1 : (a ^ (p / 2)) ^ 2 = a * a ^ (p - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
      have : p / 2 * ((2 : ℕ) : ℝ) = 1 + (p - 1) := by push_cast; ring
      rw [this, Real.rpow_add' ha (by linarith), Real.rpow_one]
    rw [h1]
    have : 0 ≤ a * a ^ (p - 1) := mul_nonneg ha (Real.rpow_nonneg ha _)
    nlinarith
  -- `0 < b ≤ a`: Cauchy–Schwarz on `[b, a]`.
  have hzero : (0 : ℝ) ∉ Set.uIcc b a := by
    rw [Set.uIcc_of_le hab]; exact fun h => absurd h.1 (not_le.mpr hb0)
  have I1 : ∫ s in b..a, s ^ (p / 2 - 1) = (a ^ (p / 2) - b ^ (p / 2)) / (p / 2) := by
    rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
    congr 1 <;> ring_nf
  have I2 : ∫ s in b..a, s ^ (p - 2) = (a ^ (p - 1) - b ^ (p - 1)) / (p - 1) := by
    rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
    congr 1 <;> ring_nf
  have hcont1 : ContinuousOn (fun s : ℝ => s ^ (p / 2 - 1)) (Set.uIcc b a) :=
    fun s hs => (Real.continuousAt_rpow_const _ _
      (Or.inl (ne_of_gt (by
        rw [Set.uIcc_of_le hab] at hs; exact lt_of_lt_of_le hb0 hs.1)))).continuousWithinAt
  have hcont2 : ContinuousOn (fun s : ℝ => s ^ (p - 2)) (Set.uIcc b a) :=
    fun s hs => (Real.continuousAt_rpow_const _ _
      (Or.inl (ne_of_gt (by
        rw [Set.uIcc_of_le hab] at hs; exact lt_of_lt_of_le hb0 hs.1)))).continuousWithinAt
  have hi1 : IntervalIntegrable (fun s : ℝ => s ^ (p / 2 - 1)) MeasureTheory.volume b a :=
    hcont1.intervalIntegrable
  have hi2 : IntervalIntegrable (fun s : ℝ => s ^ (p - 2)) MeasureTheory.volume b a :=
    hcont2.intervalIntegrable
  -- `∫ (s^{p/2-1} - λ)² ≥ 0` for every `λ`.
  have hsq : ∀ s ∈ Set.Icc b a, (s ^ (p / 2 - 1)) ^ 2 = s ^ (p - 2) := by
    intro s hs
    have hs0 : 0 ≤ s := hb.trans hs.1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]; norm_num; ring_nf
  have hCS : ∀ l : ℝ, 0 ≤ (∫ s in b..a, s ^ (p - 2)) -
      2 * l * (∫ s in b..a, s ^ (p / 2 - 1)) + l ^ 2 * (a - b) := by
    intro l
    have h0 : 0 ≤ ∫ s in b..a, (s ^ (p / 2 - 1) - l) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
    have hexp : ∫ s in b..a, (s ^ (p / 2 - 1) - l) ^ 2 =
        (∫ s in b..a, s ^ (p - 2)) - 2 * l * (∫ s in b..a, s ^ (p / 2 - 1)) +
          l ^ 2 * (a - b) := by
      have e1 : ∀ s ∈ Set.uIcc b a, (s ^ (p / 2 - 1) - l) ^ 2 =
          s ^ (p - 2) - 2 * l * s ^ (p / 2 - 1) + l ^ 2 := by
        intro s hs
        rw [Set.uIcc_of_le hab] at hs
        rw [sub_sq, hsq s hs]; ring
      rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_add
        (hi2.sub (hi1.const_mul _)) intervalIntegrable_const,
        intervalIntegral.integral_sub hi2 (hi1.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]; ring
    linarith
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hab0 : 0 < a - b := by linarith
  have := hCS ((∫ s in b..a, s ^ (p / 2 - 1)) / (a - b))
  rw [I1, I2] at this
  have hp1 : 0 < p - 1 := by linarith
  set U := a ^ (p / 2) - b ^ (p / 2)
  set G := a ^ (p - 1) - b ^ (p - 1)
  have key : (U / (p / 2)) ^ 2 ≤ (a - b) * (G / (p - 1)) := by
    set V := U / (p / 2)
    have h' : 0 ≤ G / (p - 1) - V ^ 2 / (a - b) := by
      have e : G / (p - 1) - 2 * (V / (a - b)) * V + (V / (a - b)) ^ 2 * (a - b) =
          G / (p - 1) - V ^ 2 / (a - b) := by
        field_simp; ring
      linarith
    rw [sub_nonneg, div_le_iff₀ hab0] at h'
    linarith
  have : 4 * (p - 1) / p ^ 2 * U ^ 2 = (p - 1) * (U / (p / 2)) ^ 2 := by
    field_simp; ring
  rw [this]
  calc (p - 1) * (U / (p / 2)) ^ 2 ≤ (p - 1) * ((a - b) * (G / (p - 1))) :=
        mul_le_mul_of_nonneg_left key hp1.le
    _ = (a - b) * G := by field_simp

section Operator

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

open Classical in
/-- The `L²` class of `F` (`0` if `F ∉ L²`). -/
def toL2 (μ : Measure X) (F : X → ℝ) : Lp ℝ 2 μ :=
  if h : MemLp F 2 μ then h.toLp F else 0

lemma toL2_of_memLp {F : X → ℝ} (h : MemLp F 2 μ) : toL2 μ F = h.toLp F := by
  classical
  simp only [toL2, h, ↓reduceDIte]

lemma inner_real (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  rw [RCLike.inner_apply']; simp

lemma toL2_congr {F G : X → ℝ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (h : F =ᵐ[μ] G) :
    toL2 μ F = toL2 μ G := by
  rw [toL2_of_memLp hF, toL2_of_memLp hG]; exact MemLp.toLp_congr hF hG h

lemma coeFn_toL2 {F : X → ℝ} (h : MemLp F 2 μ) : (toL2 μ F : X → ℝ) =ᵐ[μ] F := by
  rw [toL2_of_memLp h]; exact MemLp.coeFn_toLp h

lemma toL2_add {F G : X → ℝ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    toL2 μ (fun x => F x + G x) = toL2 μ F + toL2 μ G := by
  change toL2 μ (F + G) = _
  rw [toL2_of_memLp (hF.add hG), toL2_of_memLp hF, toL2_of_memLp hG, ← MemLp.toLp_add]

lemma toL2_const_mul {F : X → ℝ} (c : ℝ) (hF : MemLp F 2 μ) :
    toL2 μ (fun x => c * F x) = c • toL2 μ F := by
  change toL2 μ (c • F) = _
  rw [toL2_of_memLp (hF.const_smul c), toL2_of_memLp hF, ← MemLp.toLp_const_smul]

lemma toL2_sum {ι : Type*} (s : Finset ι) (F : ι → X → ℝ) (hF : ∀ i, MemLp (F i) 2 μ) :
    toL2 μ (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, toL2 μ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [toL2_of_memLp (MemLp.zero' (p := 2) (μ := μ))]
    exact MemLp.toLp_zero _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [toL2_add (hF a) (memLp_finsetSum s fun i _ => hF i), ih]

/-- The indicator of the level set `{F' = v}`. -/
def lev (F' : X → ℝ) (v : ℝ) : X → ℝ := fun x => if F' x = v then 1 else 0

lemma measurable_lev {F' : X → ℝ} (hF' : Measurable F') (v : ℝ) : Measurable (lev F' v) :=
  Measurable.ite (hF' (measurableSet_singleton v)) measurable_const measurable_const

lemma memLp_of_abs_le [IsFiniteMeasure μ] {F : X → ℝ} (hF : AEStronglyMeasurable F μ)
    {C : ℝ} (hC : ∀ x, |F x| ≤ C) : MemLp F 2 μ :=
  MemLp.of_bound hF C (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

lemma memLp_lev [IsFiniteMeasure μ] {F' : X → ℝ} (hF' : Measurable F') (v : ℝ) :
    MemLp (lev F' v) 2 μ :=
  memLp_of_abs_le (measurable_lev hF' v).aestronglyMeasurable (C := 1) fun x => by
    simp only [lev]; split_ifs <;> simp

omit [MeasurableSpace X] in
lemma comp_eq_sum_lev {F' : X → ℝ} {V : Finset ℝ} (hV : ∀ x, F' x ∈ V) (φ : ℝ → ℝ) :
    (fun x => φ (F' x)) = fun x => ∑ v ∈ V, φ v * lev F' v x := by
  funext x
  rw [Finset.sum_eq_single (F' x)]
  · simp [lev]
  · intro b _ hb; simp [lev, Ne.symm hb]
  · intro h; exact absurd (hV x) h

lemma inner_nonneg_of_nonneg {f g : Lp ℝ 2 μ} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    0 ≤ ⟪f, g⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x hx hy
  simp only [Pi.zero_apply] at hx hy
  rw [inner_real]
  exact mul_nonneg hx hy

variable [IsProbabilityMeasure μ] (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)

/-- **The Dirichlet-type form of a Markov operator on a finite-valued function.**
For a positive, conservative, symmetric `T` and `F'` with values in a finite set `V`,
`⟪φ∘F', ψ∘F'⟫ - ⟪φ∘F', T(ψ∘F')⟫ = Σ_{v,w} T_{vw} φ(v) (ψ(v) - ψ(w))` with
`T_{vw} = ⟪1_{F'=v}, T 1_{F'=w}⟫`. -/
lemma form_eq_double_sum
    (hcons : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, (f : X → ℝ) x = 1) → T f = f)
    {F' : X → ℝ} (hF' : Measurable F') {V : Finset ℝ} (hV : ∀ x, F' x ∈ V)
    (φ ψ : ℝ → ℝ) :
    ⟪toL2 μ (fun x => φ (F' x)), toL2 μ (fun x => ψ (F' x))⟫_ℝ -
        ⟪toL2 μ (fun x => φ (F' x)), T (toL2 μ (fun x => ψ (F' x)))⟫_ℝ =
      ∑ v ∈ V, ∑ w ∈ V, ⟪toL2 μ (lev F' v), T (toL2 μ (lev F' w))⟫_ℝ *
        (φ v * (ψ v - ψ w)) := by
  set e : ℝ → Lp ℝ 2 μ := fun v => toL2 μ (lev F' v) with he_def
  have hexp : ∀ χ : ℝ → ℝ, toL2 μ (fun x => χ (F' x)) = ∑ v ∈ V, χ v • e v := by
    intro χ
    rw [comp_eq_sum_lev hV χ,
      toL2_sum V (fun v x => χ v * lev F' v x) fun v => (memLp_lev hF' v).const_mul _]
    refine Finset.sum_congr rfl fun v _ => ?_
    exact toL2_const_mul (χ v) (memLp_lev hF' v)
  -- orthogonality of the level indicators
  have horth : ∀ v w, v ≠ w → ⟪e v, e w⟫_ℝ = 0 := by
    intro v w hvw
    simp only [he_def]
    rw [MeasureTheory.L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [coeFn_toL2 (memLp_lev hF' v) (μ := μ),
      coeFn_toL2 (memLp_lev hF' w) (μ := μ)] with x hx hy
    rw [inner_real, hx, hy]
    simp only [lev, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all
  -- row sums of `T_{vw}`
  have hone : ∑ w ∈ V, e w = toL2 μ (fun _ => (1 : ℝ)) := by
    have := hexp (fun _ => 1)
    simp only [one_smul] at this
    exact this.symm
  have hT1 : T (toL2 μ (fun _ => (1 : ℝ))) = toL2 μ (fun _ => (1 : ℝ)) :=
    hcons _ (coeFn_toL2 (memLp_const 1))
  have hrow : ∀ v ∈ V, ∑ w ∈ V, ⟪e v, T (e w)⟫_ℝ = ⟪e v, e v⟫_ℝ := by
    intro v hv
    rw [← inner_sum, ← map_sum, hone, hT1, ← hone, inner_sum,
      Finset.sum_eq_single v (fun w _ hw => horth v w (Ne.symm hw))
        (fun h => absurd hv h)]
  rw [hexp φ, hexp ψ, sum_inner, sum_inner, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [map_sum, inner_sum, inner_sum, ← Finset.sum_sub_distrib]
  have hdiag : ∑ w ∈ V, ⟪φ v • e v, ψ w • e w⟫_ℝ = φ v * ψ v * ⟪e v, e v⟫_ℝ := by
    rw [Finset.sum_eq_single v (fun w _ hw => by
        rw [real_inner_smul_left, real_inner_smul_right, horth v w (Ne.symm hw)]; ring)
      (fun h => absurd hv h)]
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  rw [Finset.sum_sub_distrib, hdiag, ← hrow v hv, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Stroock–Varopoulos for a Markov operator, finite-valued case.** -/
lemma sv_finite
    (hpos : ∀ f : Lp ℝ 2 μ, 0 ≤ f → 0 ≤ T f)
    (hcons : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, (f : X → ℝ) x = 1) → T f = f)
    (hsymm : ∀ f g : Lp ℝ 2 μ, ⟪f, T g⟫_ℝ = ⟪T f, g⟫_ℝ)
    {p : ℝ} (hp : 1 < p) {F' : X → ℝ} (hF' : Measurable F') {V : Finset ℝ}
    (hV : ∀ x, F' x ∈ V) (hV0 : ∀ v ∈ V, 0 ≤ v) :
    4 * (p - 1) / p ^ 2 *
        (⟪toL2 μ (fun x => F' x ^ (p / 2)), toL2 μ (fun x => F' x ^ (p / 2))⟫_ℝ -
          ⟪toL2 μ (fun x => F' x ^ (p / 2)), T (toL2 μ (fun x => F' x ^ (p / 2)))⟫_ℝ) ≤
      ⟪toL2 μ (fun x => F' x), toL2 μ (fun x => F' x ^ (p - 1))⟫_ℝ -
        ⟪toL2 μ (fun x => F' x), T (toL2 μ (fun x => F' x ^ (p - 1)))⟫_ℝ := by
  have h1 := form_eq_double_sum T hcons hF' hV (fun s => s) (fun s => s ^ (p - 1))
  have h2 := form_eq_double_sum T hcons hF' hV (fun s => s ^ (p / 2)) (fun s => s ^ (p / 2))
  rw [h1, h2]
  set t : ℝ → ℝ → ℝ := fun v w => ⟪toL2 μ (lev F' v), T (toL2 μ (lev F' w))⟫_ℝ with ht_def
  have ht_symm : ∀ v w, t v w = t w v := by
    intro v w
    simp only [ht_def]
    rw [hsymm, real_inner_comm]
  have hlev_nonneg : ∀ v, 0 ≤ toL2 μ (lev F' v) := by
    intro v
    refine (Lp.coeFn_nonneg _).mp ?_
    filter_upwards [coeFn_toL2 (memLp_lev hF' v) (μ := μ)] with x hx
    rw [hx]; simp only [lev, Pi.zero_apply]; split_ifs <;> norm_num
  have ht_nonneg : ∀ v w, 0 ≤ t v w := fun v w =>
    inner_nonneg_of_nonneg (hlev_nonneg v) (hpos _ (hlev_nonneg w))
  set c := 4 * (p - 1) / p ^ 2
  set A : ℝ → ℝ → ℝ := fun v w =>
    t v w * (v * (v ^ (p - 1) - w ^ (p - 1))) -
      c * (t v w * (v ^ (p / 2) * (v ^ (p / 2) - w ^ (p / 2)))) with hA_def
  have hsum : ∑ v ∈ V, ∑ w ∈ V, A v w =
      (∑ v ∈ V, ∑ w ∈ V, t v w * (v * (v ^ (p - 1) - w ^ (p - 1)))) -
        c * ∑ v ∈ V, ∑ w ∈ V, t v w * (v ^ (p / 2) * (v ^ (p / 2) - w ^ (p / 2))) := by
    simp only [hA_def, Finset.sum_sub_distrib, Finset.mul_sum]
  have hswap : ∑ v ∈ V, ∑ w ∈ V, A v w = ∑ v ∈ V, ∑ w ∈ V, A w v := Finset.sum_comm
  have hpair : ∀ v ∈ V, ∀ w ∈ V, 0 ≤ A v w + A w v := by
    intro v hv w hw
    have hsc := sv_scalar hp (hV0 v hv) (hV0 w hw)
    have : A v w + A w v = t v w * ((v - w) * (v ^ (p - 1) - w ^ (p - 1)) -
        c * (v ^ (p / 2) - w ^ (p / 2)) ^ 2) := by
      simp only [hA_def]; rw [ht_symm w v]; ring
    rw [this]
    exact mul_nonneg (ht_nonneg v w) (by linarith)
  have hdouble : ∑ v ∈ V, ∑ w ∈ V, (A v w + A w v) = 2 * ∑ v ∈ V, ∑ w ∈ V, A v w := by
    simp only [Finset.sum_add_distrib]; rw [← hswap]; ring
  have h2A : 0 ≤ 2 * ∑ v ∈ V, ∑ w ∈ V, A v w := by
    rw [← hdouble]
    exact Finset.sum_nonneg fun v hv => Finset.sum_nonneg fun w hw => hpair v hv w hw
  have : 0 ≤ ∑ v ∈ V, ∑ w ∈ V, A v w := by linarith
  rw [hsum] at this
  linarith

/-- `L²` convergence of `φ ∘ Fₙ` under uniform convergence `Fₙ → F` in `[0, M]`. -/
lemma tendsto_toL2_comp {φ : ℝ → ℝ} (hφ : Continuous φ) {M : ℝ} {F : X → ℝ}
    {Fn : ℕ → X → ℝ} (hFm : Measurable F) (hFnm : ∀ n, Measurable (Fn n))
    (hF : ∀ x, F x ∈ Set.Icc 0 M) (hFn : ∀ n x, Fn n x ∈ Set.Icc 0 M)
    (hconv : ∀ n x, |Fn n x - F x| ≤ 1 / ((n : ℝ) + 1)) :
    Filter.Tendsto (fun n => toL2 μ (fun x => φ (Fn n x))) Filter.atTop
      (nhds (toL2 μ (fun x => φ (F x)))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := φ)
    (s := Set.Icc 0 M) hφ.continuousOn
  have hmem : ∀ G : X → ℝ, Measurable G → (∀ x, G x ∈ Set.Icc 0 M) →
      MemLp (fun x => φ (G x)) 2 μ := fun G hG hGI =>
    memLp_of_abs_le (hφ.measurable.comp hG).aestronglyMeasurable (C := C) fun x => by
      rw [← Real.norm_eq_abs]; exact hC _ (hGI x)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous (s := Set.Icc (0 : ℝ) M)
    hφ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδφ⟩ := huc (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn => ?_⟩
  have hn' : 1 / ((n : ℝ) + 1) < δ :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hn)) hN
  rw [dist_eq_norm, toL2_of_memLp (hmem _ (hFnm n) (hFn n)),
    toL2_of_memLp (hmem _ hFm hF), ← MemLp.toLp_sub]
  refine lt_of_le_of_lt (Lp.norm_le_of_ae_bound (C := ε / 2) (by positivity) ?_) ?_
  · filter_upwards [MemLp.coeFn_toLp ((hmem _ (hFnm n) (hFn n)).sub (hmem _ hFm hF))]
      with x hx
    rw [hx, Pi.sub_apply, Real.norm_eq_abs, ← Real.dist_eq]
    exact (hδφ _ (hFn n x) _ (hF x) (by
      rw [Real.dist_eq]; exact lt_of_le_of_lt (hconv n x) hn')).le
  · have h1 : (measureUnivNNReal μ : ℝ) = 1 := by simp [measureUnivNNReal]
    rw [h1, Real.one_rpow, one_mul]
    linarith

/-- **Stroock–Varopoulos for a Markov operator, bounded case.** For a positive,
conservative, symmetric `T` on `L²(μ)` and a measurable `F` with values in `[0, M]`,
`(4(p-1)/p²) ⟪F^{p/2}, (I - T) F^{p/2}⟫ ≤ ⟪F, (I - T) F^{p-1}⟫`. -/
lemma sv_bounded
    (hpos : ∀ f : Lp ℝ 2 μ, 0 ≤ f → 0 ≤ T f)
    (hcons : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, (f : X → ℝ) x = 1) → T f = f)
    (hsymm : ∀ f g : Lp ℝ 2 μ, ⟪f, T g⟫_ℝ = ⟪T f, g⟫_ℝ)
    {p : ℝ} (hp : 1 < p) {F : X → ℝ} (hF : Measurable F) {M : ℝ}
    (hFM : ∀ x, F x ∈ Set.Icc 0 M) :
    4 * (p - 1) / p ^ 2 *
        (⟪toL2 μ (fun x => F x ^ (p / 2)), toL2 μ (fun x => F x ^ (p / 2))⟫_ℝ -
          ⟪toL2 μ (fun x => F x ^ (p / 2)), T (toL2 μ (fun x => F x ^ (p / 2)))⟫_ℝ) ≤
      ⟪toL2 μ (fun x => F x), toL2 μ (fun x => F x ^ (p - 1))⟫_ℝ -
        ⟪toL2 μ (fun x => F x), T (toL2 μ (fun x => F x ^ (p - 1)))⟫_ℝ := by
  -- dyadic-free floor discretization
  set Fn : ℕ → X → ℝ := fun n x => (⌊((n : ℝ) + 1) * F x⌋₊ : ℝ) / ((n : ℝ) + 1)
    with hFn_def
  have hFnm : ∀ n, Measurable (Fn n) := fun n =>
    (measurable_from_nat.comp (Measurable.nat_floor (hF.const_mul _))).div_const _
  have hpos' : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hFn_le : ∀ (n : ℕ) x, Fn n x ≤ F x := by
    intro n x
    simp only [hFn_def]
    rw [div_le_iff₀ (hpos' n)]
    exact (Nat.floor_le (mul_nonneg (hpos' n).le (hFM x).1)).trans (le_of_eq (mul_comm _ _))
  have hFn_ge : ∀ (n : ℕ) x, F x - 1 / ((n : ℝ) + 1) < Fn n x := by
    intro n x
    simp only [hFn_def]
    rw [lt_div_iff₀ (hpos' n), sub_mul, one_div, inv_mul_cancel₀ (hpos' n).ne', mul_comm]
    linarith [Nat.lt_floor_add_one (((n : ℝ) + 1) * F x)]
  have hFn_nonneg : ∀ (n : ℕ) x, 0 ≤ Fn n x := fun n x => by
    simp only [hFn_def]; positivity
  have hFnI : ∀ (n : ℕ) x, Fn n x ∈ Set.Icc 0 M := fun n x =>
    ⟨hFn_nonneg n x, (hFn_le n x).trans (hFM x).2⟩
  have hconv : ∀ (n : ℕ) x, |Fn n x - F x| ≤ 1 / ((n : ℝ) + 1) := by
    intro n x
    rw [abs_le]; constructor <;> linarith [hFn_le n x, hFn_ge n x]
  -- finite value sets
  have hfin : ∀ n, ∃ V : Finset ℝ, (∀ x, Fn n x ∈ V) ∧ ∀ v ∈ V, 0 ≤ v := by
    intro n
    refine ⟨(Finset.range (⌊((n : ℝ) + 1) * M⌋₊ + 1)).image
      (fun k : ℕ => (k : ℝ) / ((n : ℝ) + 1)), fun x => ?_, fun v hv => ?_⟩
    · refine Finset.mem_image.mpr ⟨⌊((n : ℝ) + 1) * F x⌋₊, ?_, rfl⟩
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left (hFM x).2 (hpos' n).le)
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
      positivity
  have hstep : ∀ n, 4 * (p - 1) / p ^ 2 *
        (⟪toL2 μ (fun x => Fn n x ^ (p / 2)), toL2 μ (fun x => Fn n x ^ (p / 2))⟫_ℝ -
          ⟪toL2 μ (fun x => Fn n x ^ (p / 2)), T (toL2 μ (fun x => Fn n x ^ (p / 2)))⟫_ℝ) ≤
      ⟪toL2 μ (fun x => Fn n x), toL2 μ (fun x => Fn n x ^ (p - 1))⟫_ℝ -
        ⟪toL2 μ (fun x => Fn n x), T (toL2 μ (fun x => Fn n x ^ (p - 1)))⟫_ℝ := by
    intro n
    obtain ⟨V, hV, hV0⟩ := hfin n
    exact sv_finite T hpos hcons hsymm hp (hFnm n) hV hV0
  have hu := tendsto_toL2_comp (μ := μ) (Real.continuous_rpow_const (by linarith : 0 ≤ p / 2))
    hF hFnm hFM hFnI hconv
  have hg := tendsto_toL2_comp (μ := μ) (Real.continuous_rpow_const (by linarith : 0 ≤ p - 1))
    hF hFnm hFM hFnI hconv
  have hid := tendsto_toL2_comp (μ := μ) continuous_id hF hFnm hFM hFnI hconv
  have hT := T.continuous.tendsto
  refine le_of_tendsto_of_tendsto' (b := Filter.atTop) ?_ ?_ hstep
  · exact ((hu.inner hu).sub (hu.inner ((hT _).comp hu))).const_mul _
  · exact (hid.inner hg).sub (hid.inner ((hT _).comp hg))

end Operator

end MarkovOperator

open MarkovOperator in
/-- **Stroock–Varopoulos inequality** (proved).

For a `DirichletMarkovSemigroup` `D`, any nonnegative `f ∈ D.IsCore`,
any `p > 1`, and assuming `f^{p/2}` and `f^{p-1}` lie in the core:

  `(4(p − 1) / p²) · E(f^{p/2}, f^{p/2}) ≤ E(f, f^{p−1})`.

(The exponent range is `p > 1` — the full range the Gross interpolation
path `q(s) = 1+(p₀-1)e^{2ρs}` visits for `p₀ > 1`. S–V holds throughout
`p > 1`; for diffusion/gradient forms it is in fact an equality. The
`2 ≤ p → 1 < p` relaxation is deep-think vetted, rating Standard — see
`plans/archive/sv-q-relaxation-vetting.md`, which vetted the matching
`StroockVaropoulos._hq` predicate relaxation.)

In operator form (using `E(f, g) = -⟨[f], L[g]⟩` on the core):
  `-⟨[f^{p−1}], L[f]⟩ ≥ (4(p − 1) / p²) · ⟨-[L(f^{p/2})], [f^{p/2}]⟩`.

Proof: for each `t ≥ 0`, `P_t` is positive, conservative and symmetric on
`L²(μ)`, and `MarkovOperator.sv_bounded` gives
`(4(p-1)/p²)⟪u, (I - P_t)u⟫ ≤ ⟪f, (I - P_t)f^{p-1}⟫` for `u = f^{p/2}` (for
finite-valued `f` this is a double sum over level sets with nonnegative
weights `⟪1_{f=v}, P_t 1_{f=w}⟫`, controlled by the scalar inequality
`MarkovOperator.sv_scalar`; general bounded `f` by uniform approximation).
Dividing by `t` and letting `t → 0⁺` through `energy_eq_deriv` gives the
claim.

This is the key intermediate-step lemma in Gross's proof that LSI
implies hypercontractivity. Combined with LSI applied to `f^{p/2}`
and the chain rule for `(d/dt) ‖P_t f‖_p^p`, it closes the
differential inequality `(d/dt) ‖P_t f‖_{q(t)} ≤ 0` along the path
`q(t) = 1 + (p − 1) · e^{2ρt}`. -/
theorem stroock_varopoulos {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (p : ℝ) (hp : 1 < p)
    (f : X → ℝ) (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_p_half : D.IsCore (fun x => f x ^ (p / 2)))
    (hf_p_one : D.IsCore (fun x => f x ^ (p - 1))) :
    (4 * (p - 1) / p ^ 2) *
      D.energy (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
    D.energy f (fun x => f x ^ (p - 1)) := by
  have : IsProbabilityMeasure D.μ := D.hμ
  set μ := D.μ
  -- a bounded measurable modification of `f`
  obtain ⟨M, hM⟩ := D.IsCore_memLp_top hf
  have hfm : AEStronglyMeasurable f μ := (D.IsCore_memLp hf).aestronglyMeasurable
  set F : X → ℝ := fun x => max (min (hfm.mk f x) M) 0 with hF_def
  have hFm : Measurable F :=
    ((hfm.stronglyMeasurable_mk.measurable.min measurable_const).max measurable_const)
  have hFf : F =ᵐ[μ] f := by
    filter_upwards [hfm.ae_eq_mk, hM] with x h1 h2
    simp only [hF_def, ← h1]
    rw [min_eq_left ((le_abs_self _).trans h2), max_eq_left (hf_nonneg x)]
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hM.exists
    exact (abs_nonneg _).trans hx
  have hFI : ∀ x, F x ∈ Set.Icc 0 M := fun x =>
    ⟨le_max_right _ _, max_le (min_le_right _ _) hM0⟩
  -- the `L²` classes of the three core functions, through `F`
  have hcl : ∀ (χ : ℝ → ℝ), Continuous χ → ∀ {g : X → ℝ} (hg : D.IsCore g),
      (∀ x, g x = χ (f x)) →
      (D.IsCore_memLp hg).toLp g = toL2 μ (fun x => χ (F x)) := by
    intro χ hχ g hg hgχ
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := χ)
      (s := Set.Icc 0 M) hχ.continuousOn
    have hmem : MemLp (fun x => χ (F x)) 2 μ :=
      memLp_of_abs_le (hχ.measurable.comp hFm).aestronglyMeasurable (C := C) fun x => by
        rw [← Real.norm_eq_abs]; exact hC _ (hFI x)
    rw [← toL2_of_memLp (D.IsCore_memLp hg)]
    refine toL2_congr (D.IsCore_memLp hg) hmem ?_
    filter_upwards [hFf] with x hx
    rw [hgχ x, hx]
  have hf_cl := hcl (fun s => s) continuous_id hf (fun x => rfl)
  have hu_cl := hcl (fun s => s ^ (p / 2)) (Real.continuous_rpow_const (by linarith))
    hf_p_half (fun x => rfl)
  have hg_cl := hcl (fun s => s ^ (p - 1)) (Real.continuous_rpow_const (by linarith))
    hf_p_one (fun x => rfl)
  set uh := toL2 μ (fun x => F x ^ (p / 2))
  set fh := toL2 μ (fun x => F x)
  set gh := toL2 μ (fun x => F x ^ (p - 1))
  have hA := D.energy_eq_deriv _ _ hf_p_half hf_p_half
  have hB := D.energy_eq_deriv _ _ hf hf_p_one
  simp only at hA hB
  rw [hu_cl] at hA
  rw [hf_cl, hg_cl] at hB
  -- per-time inequality
  have hstep : ∀ t : ℝ, 0 ≤ t →
      4 * (p - 1) / p ^ 2 * (⟪uh, uh⟫_ℝ - ⟪uh, D.P t uh⟫_ℝ) ≤ ⟪fh, gh⟫_ℝ - ⟪fh, D.P t gh⟫_ℝ :=
    fun t ht => sv_bounded (D.P t) (D.P_positivity t ht) (D.P_conservation t ht)
      (D.P_symmetric t ht) hp hFm hFI
  have hP0 : ∀ g : Lp ℝ 2 μ, D.P 0 g = g := fun g => by
    rw [D.P_zero, ContinuousLinearMap.id_apply]
  -- pass to the limit `t → 0⁺`
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  have hA' := hasDerivWithinAt_iff_tendsto_slope.mp hA
  have hB' := hasDerivWithinAt_iff_tendsto_slope.mp hB
  rw [hset] at hA' hB'
  have hlim : 4 * (p - 1) / p ^ 2 * -(-D.energy (fun x => f x ^ (p / 2))
      (fun x => f x ^ (p / 2))) ≤ -(-D.energy f (fun x => f x ^ (p - 1))) := by
    refine le_of_tendsto_of_tendsto (hA'.neg.const_mul _) hB'.neg ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have h := hstep t ht0.le
    simp only [slope_def_field, sub_zero, hP0]
    rw [← neg_div, ← neg_div, neg_sub, neg_sub, mul_div_assoc', div_le_div_iff_of_pos_right ht0]
    exact h
  simpa using hlim

/-! ## Gross's theorem -/

/-! ### The forward implication needs core hypotheses

Gross's forward direction (LSI ⇒ hypercontractivity) is **false** for a
bare `DirichletMarkovSemigroup`: the structure ties the form to the
semigroup only on the core, and nothing forces the core to be large.
On `Bool` with the uniform measure, the identity semigroup with the
zero form on the constants satisfies LSI for every `ρ > 0`, while
`P_1 = id` is not a contraction `L² → L⁴`
(`DirichletMarkovSemigroup.not_forall_lsi_implies_hypercontractive`).
The former axiom `gross_lsi_implies_hypercontractive` therefore proved
`False`; it is removed. The correct statement carries the core
hypotheses (`CoreSemigroupInvariant`, `GeneratorCompat`,
`StroockVaropoulos`, `CoreLpL2Approx`) and is the proved theorem
`gross_lsi_implies_hypercontractive_of_hypotheses`
(`MarkovSemigroups.Abstract.GrossODE`). -/

namespace MarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- The identity semigroup `P_t = id` on `L²(μ)`: a symmetric Markov
semigroup for any probability measure `μ`. -/
def identity (μ : Measure X) [IsProbabilityMeasure μ] : MarkovSemigroup X where
  μ := μ
  hμ := inferInstance
  P := fun _ => ContinuousLinearMap.id ℝ _
  P_zero := rfl
  P_semigroup := fun _ _ _ _ => rfl
  P_strong_cont := fun _ => tendsto_const_nhds
  P_contraction := fun _ _ => ContinuousLinearMap.norm_id_le
  P_conservation := fun _ _ _ _ => rfl
  P_positivity := fun _ _ _ hf => hf
  P_symmetric := fun _ _ _ _ => rfl

end MarkovSemigroup

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- The identity semigroup with the zero form on the core of constant
functions. All fields of `DirichletMarkovSemigroup` hold. -/
def constCore (μ : Measure X) [IsProbabilityMeasure μ] :
    DirichletMarkovSemigroup X where
  toMarkovSemigroup := MarkovSemigroup.identity μ
  energy := fun _ _ => 0
  energy_symm := fun _ _ => rfl
  energy_nonneg := fun _ => le_rfl
  IsCore := fun f => ∃ c : ℝ, f = fun _ => c
  IsCore_const := fun c => ⟨c, rfl⟩
  IsCore_add := by
    rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, rfl⟩
  IsCore_smul := by
    rintro c f ⟨a, rfl⟩
    exact ⟨c * a, rfl⟩
  IsCore_rpow_pos_strict := by
    rintro f ⟨a, rfl⟩ ε - - r
    exact ⟨a ^ r, rfl⟩
  IsCore_memLp_top := by
    rintro f ⟨a, rfl⟩
    exact ⟨|a|, ae_of_all _ fun _ => le_rfl⟩
  energy_add_left := fun _ _ _ _ _ _ => by simp
  energy_smul_left := fun _ _ _ _ _ => by simp
  energy_const := fun _ => rfl
  IsCore_memLp := by
    rintro f ⟨a, rfl⟩
    exact memLp_const a
  energy_eq_deriv := fun f g hf hg => by
    simp only [neg_zero, MarkovSemigroup.identity]
    apply hasDerivWithinAt_const

/-- `constCore μ` satisfies the log-Sobolev inequality for every `ρ > 0`:
its core functions are constant, with zero entropy. -/
theorem constCore_satisfiesLogSobolev (μ : Measure X) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) : (constCore μ).SatisfiesLogSobolev ρ := by
  refine ⟨hρ, ?_⟩
  rintro f ⟨a, rfl⟩
  have h0 : (constCore μ).energy (fun _ => a) (fun _ => a) = 0 := rfl
  change DirichletSpace.entropy (ds := (constCore μ).toDirichletSpace) _ ≤
    2 / ρ * (constCore μ).energy (fun _ => a) (fun _ => a)
  rw [h0]
  simp [DirichletSpace.entropy]

/-- **LSI does not imply hypercontractivity for a bare
`DirichletMarkovSemigroup`.** On `Bool` with the uniform measure,
`constCore` satisfies LSI with `ρ = 1`, but `P_1 = id` maps the
indicator of `{true}` (with `‖·‖_{L²} = 2^{-1/2}`) to itself, whose
`L⁴` norm `2^{-1/4}` is larger. -/
theorem not_forall_lsi_implies_hypercontractive :
    ¬ ∀ (D : DirichletMarkovSemigroup Bool) (ρ : ℝ), 0 < ρ →
      D.SatisfiesLogSobolev ρ → D.toMarkovSemigroup.IsHypercontractive ρ := by
  intro h
  set μ : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
  have hHC :=
    (h (constCore μ) 1 one_pos (constCore_satisfiesLogSobolev μ one_pos)).2
  set s : Set Bool := {true}
  have hs : MeasurableSet s := measurableSet_singleton true
  have hμs : μ s = 2⁻¹ := by
    simp [μ, s, PMF.uniformOfFintype_apply]
  set f : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)
  have hexp : (4 : ℝ) ≤ 1 + (2 - 1) * Real.exp (2 * 1 * 1) := by
    have := Real.add_one_le_exp 2
    norm_num at this ⊢
    linarith
  have key := hHC 2 4 1 one_lt_two (by norm_num) one_pos hexp f (by simp)
  change eLpNorm (((f : Lp ℝ 2 μ)) : Bool → ℝ) (ENNReal.ofReal 4) μ ≤
    eLpNorm ((f : Bool → ℝ)) (ENNReal.ofReal 2) μ at key
  rw [eLpNorm_congr_ae indicatorConstLp_coeFn, eLpNorm_congr_ae indicatorConstLp_coeFn,
    eLpNorm_indicator_const hs.nullMeasurableSet (by simp) (by simp),
    eLpNorm_indicator_const hs.nullMeasurableSet (by simp) (by simp), hμs] at key
  simp only [enorm_one, one_mul] at key
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)] at key
  have hlt : (2⁻¹ : ℝ≥0∞) ^ (1 / 2 : ℝ) < (2⁻¹ : ℝ≥0∞) ^ (1 / 4 : ℝ) :=
    ENNReal.rpow_lt_rpow_of_exponent_gt (by simp) (by simp) (by norm_num)
  exact absurd key (not_le.mpr hlt)

end DirichletMarkovSemigroup

/-! ### Gross's converse: hypercontractivity implies LSI

For a core `f` (bounded, in `L²`) and `q(t) = 1 + e^{2ρt}`, Hölder plus
hypercontractivity `L² → L^{q(t)}` give
`G(t) = ⟪P_t f, φ_{q(t)}(f)⟫ - ‖f‖₂ (∫ |f|^{q(t)})^{(q(t)-1)/q(t)} ≤ 0` for `t > 0`
(`φ_q(s) = s |s|^{q-2}`), with `G(0) = 0`. The right derivative at `0` is
`-E(f,f) + (ρ/2) Ent(f²)`, computed through `energy_eq_deriv` only, so it is `≤ 0`,
which is the log-Sobolev inequality. -/

section GrossConverseSection

open Filter
open scoped Topology

namespace GrossODE

/-- **Pointwise `rpow`-exponent derivative** (the elementary calculus
core, fully proved). For `c : ℝ` and a path `a` with
`HasDerivAt a a' s`, all values of `a` positive,
`∂_σ |c|^{a σ} = |c|^{a s} · log|c| · a'` at `s`. The `|c| = 0` case
is the constant `0` (`0^{a σ} = 0` since `a > 0`), consistent with
`0^{a s}·log 0·a' = 0`. -/
theorem hasDerivAt_abs_rpow_exponent (c : ℝ) {a : ℝ → ℝ} {a' s : ℝ}
    (ha : HasDerivAt a a' s) (ha_pos : ∀ σ, 0 < a σ) :
    HasDerivAt (fun σ => |c| ^ a σ)
      (|c| ^ a s * Real.log |c| * a') s := by
  rcases eq_or_lt_of_le (abs_nonneg c) with hc | hc
  · -- `|c| = 0`: the function is constantly `0`.
    have hzero : (fun σ => |c| ^ a σ) = fun _ => (0 : ℝ) := by
      funext σ; rw [← hc, Real.zero_rpow (ha_pos σ).ne']
    rw [hzero]
    have hd : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 s := hasDerivAt_const s 0
    convert hd using 1
    rw [← hc, Real.zero_rpow (ha_pos s).ne']; ring
  · -- `|c| > 0`: `|c|^{a σ} = exp (log|c| · a σ)`.
    have hrw : (fun σ => |c| ^ a σ)
        = fun σ => Real.exp (Real.log |c| * a σ) := by
      funext σ; rw [Real.rpow_def_of_pos hc]
    rw [hrw]
    have hmul : HasDerivAt (fun σ => Real.log |c| * a σ)
        (Real.log |c| * a') s := ha.const_mul _
    have hexp := (Real.hasDerivAt_exp (Real.log |c| * a s)).comp s hmul
    convert hexp using 1
    · rfl
    rw [Real.rpow_def_of_pos hc]; ring

/-- **General (Mathlib-native): parametric `rpow`-exponent Leibniz.**
For a bounded measurable `w` on a finite measure space and a
`C¹`-differentiable positive exponent path `a`,
`σ ↦ ∫ |w|^{a σ}` is differentiable at `s` with derivative
`a'(s) · ∫ |w|^{a s} · log|w|`. The pointwise exponent
derivative is `∂_σ |w y|^{a σ} = |w y|^{a σ} · log|w y| · a'`
(`hasDerivAt_abs_rpow_exponent` above; the `w y = 0` case is constant
`0` since `a > 0`).

**Strategy** (apply Mathlib
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`):

* Nbhd `Metric.ball s 1` ⊆ `Icc (s-1) (s+1)`; compactness +
  `ContDiff ℝ 1 a` give bounds `a_min ≤ a σ ≤ a_max` on `Icc` and
  `|deriv a σ| ≤ K`. `a_min > 0` from `ha_pos`.
* Bound on `|F'(σ, y)| = |w y|^{a σ} · |log |w y|| · |deriv a σ|`:
    - `|w y| ∈ [0, M]` (or `[0, max(M, 1)]`).
    - For `|w y| ∈ (0, 1]`: `t^a · |log t| ≤ 1/(e · a) ≤ 1/(e · a_min)`
      (max of `t ↦ t^a · log(1/t)` on `(0,1]` at `t = e^{-1/a}`).
    - For `|w y| ∈ [1, M]` (M ≥ 1): `t^a · log t ≤ M^{a_max} · log M`.
    - For `|w y| = 0`: value is 0 (`Real.zero_rpow (ha_pos σ).ne'`).
  Total bound `B := K · max(1/(e·a_min), max(M, 1)^{a_max} · log max(M, 1))`,
  a constant ⇒ integrable on finite measure.
* `h_diff` from `hasDerivAt_abs_rpow_exponent (w y) (ha_cd.differentiable
  le_rfl).differentiableAt.hasDerivAt ha_pos`.
* The resulting `∫ F' s = (deriv a s) · ∫ |w|^{a s} · log|w|` via
  `integral_mul_const`; identify `deriv a s = a'` via `ha.deriv`.

**Effort:** ~150–200 LOC; the `t^a · |log t|` analytic supremum
(`(e · a)⁻¹` on `(0,1]`) requires a manual proof (not in Mathlib as a
direct lemma). No project definitions; Mathlib-upstreamable. -/
theorem hasDerivAt_integral_rpow_exponent {Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    {w : Y → ℝ} (hw : AEStronglyMeasurable w ν) {M : ℝ}
    (hM : ∀ᵐ y ∂ν, |w y| ≤ M)
    {a : ℝ → ℝ} {a' s : ℝ}
    (ha_cd : ContDiff ℝ 1 a) (ha : HasDerivAt a a' s)
    (ha_pos : ∀ σ, 0 < a σ) :
    HasDerivAt (fun σ => ∫ y, |w y| ^ a σ ∂ν)
      (a' * ∫ y, |w y| ^ a s * Real.log |w y| ∂ν) s := by
  -- Notation + continuity from ContDiff 1.
  have ha_cont : Continuous a := ha_cd.continuous
  have ha_diff : Differentiable ℝ a := ha_cd.differentiable (by decide)
  have ha_deriv_cont : Continuous (deriv a) := ha_cd.continuous_deriv le_rfl
  -- Compact J = [s-1, s+1]; bounds.
  set J : Set ℝ := Set.Icc (s - 1) (s + 1) with hJ_def
  have hJ_cpt : IsCompact J := isCompact_Icc
  have hJ_ne : J.Nonempty := ⟨s, by constructor <;> linarith⟩
  obtain ⟨σ_amin, _, h_amin⟩ := hJ_cpt.exists_isMinOn hJ_ne ha_cont.continuousOn
  set a_min : ℝ := a σ_amin with ha_min_def
  have ha_min_pos : 0 < a_min := ha_pos σ_amin
  obtain ⟨σ_amax, _, h_amax⟩ := hJ_cpt.exists_isMaxOn hJ_ne ha_cont.continuousOn
  set a_max : ℝ := a σ_amax with ha_max_def
  have ha_max_pos : 0 < a_max := ha_pos σ_amax
  obtain ⟨σ_K, _, h_K⟩ := hJ_cpt.exists_isMaxOn hJ_ne
    (continuous_abs.comp ha_deriv_cont).continuousOn
  set K : ℝ := |deriv a σ_K| with hK_def
  have hK_nn : 0 ≤ K := abs_nonneg _
  set M' : ℝ := max M 1 with hM'_def
  have hM'_one : (1 : ℝ) ≤ M' := le_max_right _ _
  have hM'_pos : 0 < M' := lt_of_lt_of_le one_pos hM'_one
  have hM'_log_nn : 0 ≤ Real.log M' := Real.log_nonneg hM'_one
  have hw_le_M' : ∀ᵐ y ∂ν, |w y| ≤ M' := by
    filter_upwards [hM] with y hy
    exact le_trans hy (le_max_left _ _)
  set Cprod : ℝ := 1 / (Real.exp 1 * a_min) + M' ^ a_max * Real.log M' with hCprod_def
  have hCprod_nn : 0 ≤ Cprod := by
    refine add_nonneg ?_ ?_
    · positivity
    · exact mul_nonneg (Real.rpow_nonneg hM'_pos.le _) hM'_log_nn
  set B : ℝ := K * Cprod with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hK_nn hCprod_nn
  -- Open neighborhood `ball s 1 ⊆ J`.
  set U : Set ℝ := Metric.ball s 1 with hU_def
  have hU_subJ : U ⊆ J := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    refine ⟨?_, ?_⟩ <;> [linarith [abs_lt.mp hx]; linarith [abs_lt.mp hx]]
  have hU_nhds : U ∈ nhds s := Metric.ball_mem_nhds s one_pos
  -- Pointwise bound on `t ^ a σ * log t` for `t ∈ [0, M']` and `a σ ∈ [a_min, a_max]`.
  have h_prod_bound : ∀ (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ M') (σ : ℝ) (_ : σ ∈ J),
      |t ^ a σ * Real.log t| ≤ Cprod := by
    intro t ht_nn ht_M' σ hσ
    have ha_σ_pos : 0 < a σ := ha_pos σ
    have h_amin_le : a_min ≤ a σ := h_amin hσ
    have h_amax_ge : a σ ≤ a_max := h_amax hσ
    have hM'_term_nn : 0 ≤ M' ^ a_max * Real.log M' :=
      mul_nonneg (Real.rpow_nonneg hM'_pos.le _) hM'_log_nn
    have hEmin_nn : (0:ℝ) ≤ 1 / (Real.exp 1 * a_min) := by positivity
    rcases eq_or_lt_of_le ht_nn with ht_eq | ht_pos
    · -- t = 0: |0^{a σ} * log 0| = 0 ≤ Cprod.
      have h0 : |t ^ a σ * Real.log t| = 0 := by
        rw [show t = 0 from ht_eq.symm, Real.zero_rpow ha_σ_pos.ne']
        simp
      linarith
    rcases le_or_gt t 1 with ht_le1 | ht_gt1
    · -- t ∈ (0, 1].
      have hlog_np : Real.log t ≤ 0 := Real.log_nonpos ht_nn ht_le1
      have h_abs : |t ^ a σ * Real.log t| = t ^ a σ * (-Real.log t) := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht_nn _),
            abs_of_nonpos hlog_np]
      rw [h_abs]
      -- y := a σ · (-log t) ≥ 0. Apply mul_exp_neg_le_exp_neg_one.
      have h_y_bd :
          a σ * (-Real.log t) * Real.exp (-(a σ * (-Real.log t))) ≤ Real.exp (-1) :=
        Real.mul_exp_neg_le_exp_neg_one _
      have h_exp_eq : Real.exp (-(a σ * (-Real.log t))) = t ^ a σ := by
        have h_eq : -(a σ * (-Real.log t)) = Real.log t * a σ := by ring
        rw [h_eq, ← Real.rpow_def_of_pos ht_pos]
      rw [h_exp_eq] at h_y_bd
      -- (-log t) · t^{a σ} ≤ exp(-1) / (a σ) = 1/(e·a σ) ≤ 1/(e·a_min).
      have h_div : t ^ a σ * (-Real.log t) ≤ 1 / (Real.exp 1 * a σ) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < Real.exp 1 * a σ)]
        have h_calc :
            t ^ a σ * (-Real.log t) * (Real.exp 1 * a σ)
              = a σ * (-Real.log t) * t ^ a σ * Real.exp 1 := by ring
        rw [h_calc]
        have hexp1_nn : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
        calc a σ * (-Real.log t) * t ^ a σ * Real.exp 1
            ≤ Real.exp (-1) * Real.exp 1 :=
                mul_le_mul_of_nonneg_right h_y_bd hexp1_nn
          _ = 1 := by
                rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h_div_amin : 1 / (Real.exp 1 * a σ) ≤ 1 / (Real.exp 1 * a_min) := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact mul_le_mul_of_nonneg_left h_amin_le (Real.exp_pos 1).le
      linarith
    · -- t ∈ (1, M'].
      have ht_pos : 0 < t := lt_trans one_pos ht_gt1
      have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht_gt1.le
      have h_abs : |t ^ a σ * Real.log t| = t ^ a σ * Real.log t := by
        rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht_nn _) hlog_nn)]
      rw [h_abs]
      have h_pow_le_t_amax : t ^ a σ ≤ t ^ a_max :=
        Real.rpow_le_rpow_of_exponent_le ht_gt1.le h_amax_ge
      have h_t_amax_le : t ^ a_max ≤ M' ^ a_max :=
        Real.rpow_le_rpow ht_nn ht_M' ha_max_pos.le
      have h_pow_le : t ^ a σ ≤ M' ^ a_max := le_trans h_pow_le_t_amax h_t_amax_le
      have h_log_le : Real.log t ≤ Real.log M' :=
        Real.log_le_log ht_pos ht_M'
      have h_prod_le : t ^ a σ * Real.log t ≤ M' ^ a_max * Real.log M' := by
        gcongr
      linarith
  -- Apply the parametric Leibniz lemma.
  have ha'_eq : a' = deriv a s := ha.deriv.symm
  -- F σ y := |w y|^{a σ}; F' σ y := |w y|^{a σ} · log|w y| · deriv a σ.
  set F : ℝ → Y → ℝ := fun σ y => |w y| ^ a σ with hF_def
  set F' : ℝ → Y → ℝ := fun σ y => |w y| ^ a σ * Real.log |w y| * deriv a σ
    with hF'_def
  -- AEStronglyMeasurable of `F σ` and `F' σ`.
  have hF_aesm : ∀ σ, AEStronglyMeasurable (F σ) ν := fun σ => by
    show AEStronglyMeasurable (fun y => |w y| ^ a σ) ν
    exact (continuous_abs.rpow_const
      (fun _ => Or.inr (ha_pos σ).le)).comp_aestronglyMeasurable hw
  have hF'_aesm : ∀ σ, AEStronglyMeasurable (F' σ) ν := fun σ => by
    show AEStronglyMeasurable (fun y => |w y| ^ a σ * Real.log |w y| * deriv a σ) ν
    refine ((hF_aesm σ).mul ?_).mul_const _
    -- AEStronglyMeasurable (fun y => Real.log |w y|) ν.
    refine (Real.measurable_log.comp_aemeasurable ?_).aestronglyMeasurable
    exact (continuous_abs.comp_aestronglyMeasurable hw).aemeasurable
  -- Bound: ‖F' σ y‖ ≤ B for σ ∈ U, a.e. y.
  have h_F'_bound : ∀ᵐ y ∂ν, ∀ σ ∈ U, ‖F' σ y‖ ≤ B := by
    filter_upwards [hw_le_M'] with y hy_M' σ hσU
    have hσ_J : σ ∈ J := hU_subJ hσU
    have hd_le : |deriv a σ| ≤ K := h_K hσ_J
    have hprod := h_prod_bound (|w y|) (abs_nonneg _) hy_M' σ hσ_J
    have : ‖F' σ y‖ = |F' σ y| := Real.norm_eq_abs _
    rw [this]
    show |(|w y| ^ a σ * Real.log |w y|) * deriv a σ| ≤ K * Cprod
    rw [abs_mul]
    calc |(|w y| ^ a σ * Real.log |w y|)| * |deriv a σ|
        ≤ Cprod * K := mul_le_mul hprod hd_le (abs_nonneg _) hCprod_nn
      _ = K * Cprod := by ring
  -- Integrable F s.
  have hFs_int : Integrable (F s) ν := by
    refine Integrable.mono' (g := fun _ => M' ^ a_max + 1) (integrable_const _)
      (hF_aesm s) ?_
    filter_upwards [hw_le_M'] with y hy_M'
    show ‖|w y| ^ a s‖ ≤ M' ^ a_max + 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hs_J : s ∈ J := ⟨by linarith, by linarith⟩
    have has_max : a s ≤ a_max := h_amax hs_J
    rcases le_or_gt (|w y|) 1 with hle | hgt
    · have : |w y| ^ a s ≤ 1 := Real.rpow_le_one (abs_nonneg _) hle (ha_pos s).le
      linarith [Real.rpow_nonneg hM'_pos.le a_max]
    · have h_pow : |w y| ^ a s ≤ M' ^ a_max := by
        calc |w y| ^ a s ≤ |w y| ^ a_max :=
              Real.rpow_le_rpow_of_exponent_le hgt.le has_max
          _ ≤ M' ^ a_max := Real.rpow_le_rpow (abs_nonneg _) hy_M' ha_max_pos.le
      linarith
  -- h_diff: pointwise differentiability for σ ∈ U (holds for all y).
  have h_diff : ∀ᵐ y ∂ν, ∀ σ ∈ U, HasDerivAt (fun σ' => |w y| ^ a σ') (F' σ y) σ := by
    refine Filter.Eventually.of_forall (fun y σ _ => ?_)
    exact hasDerivAt_abs_rpow_exponent (w y) (ha_diff.differentiableAt.hasDerivAt) ha_pos
  -- Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le.
  have h_main :
      Integrable (F' s) ν ∧
      HasDerivAt (fun σ => ∫ y, F σ y ∂ν) (∫ y, F' s y ∂ν) s := by
    apply hasDerivAt_integral_of_dominated_loc_of_deriv_le hU_nhds
      (Filter.Eventually.of_forall hF_aesm) hFs_int (hF'_aesm s)
      h_F'_bound
      (integrable_const _)
      h_diff
  -- Identify ∫ F' s = a' * ∫ |w|^{a s} · log|w|.
  have h_int_F's : ∫ y, F' s y ∂ν =
      deriv a s * ∫ y, |w y| ^ a s * Real.log |w y| ∂ν := by
    show ∫ y, |w y| ^ a s * Real.log |w y| * deriv a s ∂ν
        = deriv a s * ∫ y, |w y| ^ a s * Real.log |w y| ∂ν
    rw [integral_mul_const, mul_comm]
  convert h_main.2 using 1
  rw [h_int_F's, ha.deriv]

end GrossODE

namespace GrossConverse

/-- The critical exponent path `q(t) = 1 + e^{2ρt}` from `p = 2`. -/
def expPath (ρ t : ℝ) : ℝ := 1 + Real.exp (2 * ρ * t)

/-- The duality map `φ_q(s) = s · |s|^{q-2}`, so that `s · φ_q(s) = |s|^q`. -/
def dualPow (q s : ℝ) : ℝ := s * |s| ^ (q - 2)

/-- `q(0) = 2`. -/
lemma expPath_zero (ρ : ℝ) : expPath ρ 0 = 2 := by
  simp [expPath]; norm_num

/-- `q(t) > 0`. -/
lemma expPath_pos (ρ t : ℝ) : 0 < expPath ρ t := by
  unfold expPath; positivity

/-- `q(t) > 1`. -/
lemma one_lt_expPath (ρ t : ℝ) : 1 < expPath ρ t := by
  unfold expPath; linarith [Real.exp_pos (2 * ρ * t)]

/-- `q(t) ≥ 2` for `ρ, t ≥ 0`. -/
lemma two_le_expPath {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t) : 2 ≤ expPath ρ t := by
  unfold expPath
  have : 1 ≤ Real.exp (2 * ρ * t) := Real.one_le_exp (by positivity)
  linarith

/-- `q'(t) = 2ρ e^{2ρt}`. -/
lemma hasDerivAt_expPath (ρ t : ℝ) :
    HasDerivAt (expPath ρ) (Real.exp (2 * ρ * t) * (2 * ρ)) t := by
  have h := (((hasDerivAt_id t).const_mul (2 * ρ)).exp).const_add 1
  show HasDerivAt (fun t => 1 + Real.exp (2 * ρ * t)) _ t
  convert h using 1 <;> simp

/-- `q'(0) = 2ρ`. -/
lemma hasDerivAt_expPath_zero (ρ : ℝ) : HasDerivAt (expPath ρ) (2 * ρ) 0 := by
  simpa using hasDerivAt_expPath ρ 0

/-- The exponent path is `C¹`. -/
lemma contDiff_expPath (ρ : ℝ) : ContDiff ℝ 1 (expPath ρ) := by
  unfold expPath; fun_prop

/-- `φ_2(s) = s`. -/
lemma dualPow_two (s : ℝ) : dualPow 2 s = s := by
  simp [dualPow]

/-- `s · φ_q(s) = |s|^q` for `q > 0`. -/
lemma mul_dualPow {q : ℝ} (hq : 0 < q) (s : ℝ) : s * dualPow q s = |s| ^ q := by
  unfold dualPow
  have h : |s| ^ q = |s| ^ ((2 : ℝ) + (q - 2)) := by ring_nf
  rw [h, Real.rpow_add' (abs_nonneg s) (by linarith), Real.rpow_two, sq_abs]
  ring

/-- `|φ_q(s)| = |s|^{q-1}` for `q > 1`. -/
lemma abs_dualPow {q : ℝ} (hq : 1 < q) (s : ℝ) : |dualPow q s| = |s| ^ (q - 1) := by
  unfold dualPow
  have h : |s| ^ (q - 1) = |s| ^ ((1 : ℝ) + (q - 2)) := by ring_nf
  rw [h, Real.rpow_add' (abs_nonneg s) (by linarith), Real.rpow_one, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg s) _)]

/-- The duality map is measurable. -/
lemma measurable_dualPow (q : ℝ) : Measurable (dualPow q) := by
  unfold dualPow
  exact measurable_id.mul (continuous_abs.measurable.pow_const _)

/-- Elementary bound: `|u (u^r - 1)| ≤ r (1 + M³)` for `0 ≤ u ≤ M`, `r ∈ [0, 1]`. -/
lemma abs_mul_rpow_sub_one_le {u r M : ℝ} (hu : 0 ≤ u) (huM : u ≤ M) (hr : 0 ≤ r)
    (hr1 : r ≤ 1) : |u * (u ^ r - 1)| ≤ r * (1 + M ^ 3) := by
  have hM0 : 0 ≤ M := hu.trans huM
  have hM3 : 0 ≤ M ^ 3 := pow_nonneg hM0 3
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0; simp; positivity
  have hur : u ^ r = Real.exp (Real.log u * r) := Real.rpow_def_of_pos hpos r
  rcases le_or_gt u 1 with hle | hgt
  · -- `u ≤ 1`: `0 ≤ 1 - u^r ≤ -r log u` and `-u log u ≤ 1`.
    have hlog : Real.log u ≤ 0 := Real.log_nonpos hu hle
    have hle1 : u ^ r ≤ 1 := Real.rpow_le_one hu hle hr
    have hexp := Real.add_one_le_exp (Real.log u * r)
    rw [← hur] at hexp
    have hul : |Real.log u * u| < 1 := Real.abs_log_mul_self_lt u hpos hle
    have hul' : -(Real.log u * u) ≤ 1 := by linarith [neg_abs_le (Real.log u * u)]
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hu (by linarith))]
    have h1 : u * (1 - u ^ r) ≤ u * (-(Real.log u * r)) :=
      mul_le_mul_of_nonneg_left (by linarith) hu
    have h2 : u * (-(Real.log u * r)) = r * (-(Real.log u * u)) := by ring
    nlinarith
  · -- `u > 1`: `0 ≤ u^r - 1 ≤ r log u · u^r ≤ r u log u ≤ r u²`.
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hgt.le
    have hge1 : 1 ≤ u ^ r := Real.one_le_rpow hgt.le hr
    have hur_le : u ^ r ≤ u := by
      calc u ^ r ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hgt.le hr1
        _ = u := Real.rpow_one u
    have hexp := Real.add_one_le_exp (-(Real.log u * r))
    have hprod : Real.exp (-(Real.log u * r)) * u ^ r = 1 := by
      rw [hur, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    -- `u^r - 1 ≤ r log u · u^r`.
    have hkey : u ^ r - 1 ≤ Real.log u * r * u ^ r := by
      have := mul_le_mul_of_nonneg_right hexp (by linarith : (0 : ℝ) ≤ u ^ r)
      nlinarith
    have hlogu : Real.log u ≤ u := by
      have := Real.log_le_sub_one_of_pos hpos; linarith
    rw [abs_of_nonneg (mul_nonneg hu (by linarith))]
    have hu3 : u ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ hu huM 3
    have h1 : u * (u ^ r - 1) ≤ u * (Real.log u * r * u ^ r) :=
      mul_le_mul_of_nonneg_left hkey hu
    have h2 : u * (Real.log u * r * u ^ r) ≤ r * u ^ 3 := by
      have hlr : 0 ≤ Real.log u * r := mul_nonneg hlog hr
      have : Real.log u * r * u ^ r ≤ u * r * u := by
        have := mul_le_mul hlogu hur_le (by linarith) hu
        have := mul_le_mul_of_nonneg_right this hr
        nlinarith
      nlinarith
    nlinarith

/-- Pointwise Lipschitz bound of the duality map in the exponent near `q = 2`. -/
lemma abs_dualPow_sub_le {q s M : ℝ} (hs : |s| ≤ M) (hq2 : 2 ≤ q) (hq3 : q ≤ 3) :
    |dualPow q s - s| ≤ (q - 2) * (1 + M ^ 3) := by
  have h : |dualPow q s - s| = |(|s| * (|s| ^ (q - 2) - 1))| := by
    unfold dualPow
    rw [show s * |s| ^ (q - 2) - s = s * (|s| ^ (q - 2) - 1) by ring, abs_mul, abs_mul,
      abs_abs]
  rw [h]
  exact abs_mul_rpow_sub_one_le (abs_nonneg s) hs (by linarith) (by linarith)

/-! ### Hölder plus hypercontractivity -/

variable {X : Type*} [MeasurableSpace X]

/-- **Hölder + hypercontractivity.** For `t > 0`, `q = q(t)` and a bounded `h`,
`∫ (P_t F) · φ_q(h) ≤ ‖F‖₂ · (∫ |h|^q)^{(q-1)/q}`: Hölder with exponents `q`,
`q/(q-1)` and `‖P_t F‖_q ≤ ‖F‖_2`. -/
lemma integral_mul_dualPow_le (S : MarkovSemigroup X) {ρ : ℝ}
    (h_hyp : S.IsHypercontractive ρ) (F : Lp ℝ 2 S.μ) {t : ℝ} (ht : 0 < t)
    {h : X → ℝ} (hh : AEStronglyMeasurable h S.μ) {M : ℝ}
    (hM : ∀ᵐ x ∂S.μ, |h x| ≤ M) :
    ∫ x, (S.P t F : X → ℝ) x * dualPow (expPath ρ t) (h x) ∂S.μ ≤
      ‖F‖ * (∫ x, |h x| ^ expPath ρ t ∂S.μ) ^ ((expPath ρ t - 1) / expPath ρ t) := by
  set q := expPath ρ t with hq_def
  have hq1 : 1 < q := one_lt_expPath ρ t
  have hq0 : 0 < q := expPath_pos ρ t
  set u : X → ℝ := (S.P t F : X → ℝ)
  have hHC : eLpNorm u (ENNReal.ofReal q) S.μ ≤
      eLpNorm (F : X → ℝ) (ENNReal.ofReal 2) S.μ :=
    h_hyp.2 2 q t one_lt_two (two_le_expPath h_hyp.1.le ht.le) ht
      (by norm_num [hq_def, expPath]) F (by rw [ENNReal.ofReal_ofNat]; exact Lp.memLp F)
  have hF2 : eLpNorm (F : X → ℝ) (ENNReal.ofReal 2) S.μ ≠ ⊤ := by
    rw [ENNReal.ofReal_ofNat]; exact Lp.eLpNorm_ne_top F
  have hu_mem : MemLp u (ENNReal.ofReal q) S.μ :=
    hHC.trans_lt hF2.lt_top
  have hu_abs : MemLp (fun x => |u x|) (ENNReal.ofReal q) S.μ := by
    simpa [Real.norm_eq_abs] using hu_mem.norm
  set q' := q / (q - 1) with hq'_def
  have hconj : q.HolderConjugate q' := Real.HolderConjugate.conjExponent hq1
  have hφ_meas : AEStronglyMeasurable (fun x => |dualPow q (h x)|) S.μ :=
    continuous_abs.comp_aestronglyMeasurable
      ((measurable_dualPow q).comp_aemeasurable hh.aemeasurable).aestronglyMeasurable
  have hφ_mem : MemLp (fun x => |dualPow q (h x)|) (ENNReal.ofReal q') S.μ := by
    refine MemLp.of_bound hφ_meas (M ^ (q - 1)) ?_
    filter_upwards [hM] with x hx
    rw [Real.norm_eq_abs, abs_abs, abs_dualPow hq1]
    exact Real.rpow_le_rpow (abs_nonneg _) hx (by linarith)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (ae_of_all _ fun x => abs_nonneg (u x))
    (ae_of_all _ fun x => abs_nonneg (dualPow q (h x))) hu_abs hφ_mem
  -- the `L^{q'}` factor
  have hφ_pow : ∀ x, |dualPow q (h x)| ^ q' = |h x| ^ q := by
    intro x
    rw [abs_dualPow hq1, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    have hq1' : q - 1 ≠ 0 := by linarith
    rw [hq'_def]; field_simp
  simp only [hφ_pow] at hHolder
  rw [show (1 : ℝ) / q' = (q - 1) / q by rw [hq'_def, one_div_div]] at hHolder
  -- the `L^q` factor
  have hnorm : (∫ x, |u x| ^ q ∂S.μ) ^ (1 / q) ≤ ‖F‖ := by
    have he := hu_mem.eLpNorm_eq_integral_rpow_norm (by simp [hq0]) ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hq0.le] at he
    have hle := ENNReal.toReal_mono hF2 hHC
    rw [he, ENNReal.toReal_ofReal (by positivity), ENNReal.ofReal_ofNat, ← Lp.norm_def]
      at hle
    simpa [Real.norm_eq_abs, one_div] using hle
  have hY : 0 ≤ (∫ x, |h x| ^ q ∂S.μ) ^ ((q - 1) / q) :=
    Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _
  calc ∫ x, u x * dualPow q (h x) ∂S.μ
      ≤ |∫ x, u x * dualPow q (h x) ∂S.μ| := le_abs_self _
    _ ≤ ∫ x, |u x * dualPow q (h x)| ∂S.μ := abs_integral_le_integral_abs
    _ = ∫ x, |u x| * |dualPow q (h x)| ∂S.μ := by simp_rw [abs_mul]
    _ ≤ _ := hHolder
    _ ≤ ‖F‖ * (∫ x, |h x| ^ q ∂S.μ) ^ ((q - 1) / q) := mul_le_mul_of_nonneg_right hnorm hY

/-! ### Right-derivative bookkeeping at `t = 0` -/

/-- A right derivative within `Ici 0` at `0` is the limit of the slopes from the right. -/
lemma tendsto_slope_of_hasDerivWithinAt {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivWithinAt g g' (Ici 0) 0) :
    Tendsto (fun t => t⁻¹ * (g t - g 0)) (𝓝[>] 0) (𝓝 g') := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi (0 : ℝ)) (by simp)).1
    (hg.mono Ioi_subset_Ici_self)
  refine h.congr fun t => ?_
  rw [slope_def_module, sub_zero, smul_eq_mul]

/-- A two-sided derivative at `0` is the limit of the slopes from the right. -/
lemma tendsto_slope_of_hasDerivAt {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0) :
    Tendsto (fun t => t⁻¹ * (g t - g 0)) (𝓝[>] 0) (𝓝 g') :=
  tendsto_slope_of_hasDerivWithinAt hg.hasDerivWithinAt

/-- If `G ≤ 0` on `(0, ∞)` and `G(t)/t → L` as `t → 0⁺`, then `L ≤ 0`. -/
lemma nonpos_of_tendsto_slope {G : ℝ → ℝ} {L : ℝ}
    (hG : Tendsto (fun t => t⁻¹ * G t) (𝓝[>] 0) (𝓝 L)) (hneg : ∀ t, 0 < t → G t ≤ 0) :
    L ≤ 0 := by
  refine le_of_tendsto hG ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt ht)) (hneg t ht)

/-! ### The Gross differentiation at `t = 0` -/

/-- **Gross's converse for one core function, nondegenerate case.** If `P_t` is
hypercontractive with rate `ρ`, `f` is core and `I = ∫ f² > 0`, then
`2 ∫ |f|² log|f| - I log I ≤ (2/ρ) E(f, f)`. The proof differentiates at `t = 0⁺` the
nonpositive function `G(t) = ⟪P_t f, φ_{q(t)}(f)⟫ - ‖f‖₂ (∫ |f|^{q(t)})^{(q(t)-1)/q(t)}`. -/
theorem entropy_le_of_hypercontractive_of_pos (D : DirichletMarkovSemigroup X) {ρ : ℝ}
    (h_hyp : D.toMarkovSemigroup.IsHypercontractive ρ) {f : X → ℝ} (hf : D.IsCore f)
    (hIpos : 0 < ∫ x, |f x| ^ expPath ρ 0 ∂D.μ) :
    2 * ∫ x, |f x| ^ expPath ρ 0 * Real.log |f x| ∂D.μ -
        (∫ x, |f x| ^ expPath ρ 0 ∂D.μ) * Real.log (∫ x, |f x| ^ expPath ρ 0 ∂D.μ) ≤
      2 / ρ * D.energy f f := by
  have hρ : 0 < ρ := h_hyp.1
  obtain ⟨M₀, hM₀⟩ := D.IsCore_memLp_top hf
  set M : ℝ := max M₀ 1
  have hM : ∀ᵐ x ∂D.μ, |f x| ≤ M := hM₀.mono fun x hx => hx.trans (le_max_left _ _)
  have hf2 : MemLp f 2 D.μ := D.IsCore_memLp hf
  have hfm : AEStronglyMeasurable f D.μ := hf2.aestronglyMeasurable
  set F : Lp ℝ 2 D.μ := hf2.toLp f
  have hFf : (F : X → ℝ) =ᵐ[D.μ] f := hf2.coeFn_toLp
  -- The scalar functions `J`, `K` and their derivatives at `0`.
  set J : ℝ → ℝ := fun t => ∫ x, |f x| ^ expPath ρ t ∂D.μ
  set I : ℝ := J 0
  set L : ℝ := ∫ x, |f x| ^ expPath ρ 0 * Real.log |f x| ∂D.μ
  have hJ_deriv : HasDerivAt J (2 * ρ * L) 0 :=
    GrossODE.hasDerivAt_integral_rpow_exponent D.μ hfm hM (contDiff_expPath ρ)
      (hasDerivAt_expPath_zero ρ) (expPath_pos ρ)
  set e : ℝ → ℝ := fun t => (expPath ρ t - 1) / expPath ρ t with he_def
  have he0 : e 0 = 1 / 2 := by simp only [he_def, expPath_zero]; norm_num
  have he_deriv : HasDerivAt e (ρ / 2) 0 := by
    have h1 := hasDerivAt_expPath_zero ρ
    have h := (h1.sub_const 1).div h1 (by rw [expPath_zero]; norm_num)
    convert h using 1
    rw [expPath_zero]; ring
  set K : ℝ → ℝ := fun t => J t ^ e t
  have hK_deriv : HasDerivAt K
      (2 * ρ * L * e 0 * I ^ (e 0 - 1) + ρ / 2 * I ^ e 0 * Real.log I) 0 :=
    hJ_deriv.rpow he_deriv hIpos
  -- `⟪F, F⟫ = I` and `‖F‖ = I^{1/2}`.
  have hFF : ⟪F, F⟫_ℝ = I := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hFf] with x hx
    simp only [hx, expPath_zero, Real.rpow_two, sq_abs, RCLike.inner_apply, conj_trivial]
    ring
  have hnormF : ‖F‖ = I ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hFF, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  -- The duality elements `Φ t = [φ_{q(t)} ∘ f]`.
  have hΦmem : ∀ t, MemLp (fun x => dualPow (expPath ρ t) (f x)) 2 D.μ := by
    intro t
    refine MemLp.of_bound ((measurable_dualPow _).comp_aemeasurable
      hfm.aemeasurable).aestronglyMeasurable (M ^ (expPath ρ t - 1)) ?_
    filter_upwards [hM] with x hx
    rw [Real.norm_eq_abs, abs_dualPow (one_lt_expPath ρ t)]
    exact Real.rpow_le_rpow (abs_nonneg _) hx (by linarith [one_lt_expPath ρ t])
  set Φ : ℝ → Lp ℝ 2 D.μ := fun t => (hΦmem t).toLp _
  have hΦ_coe : ∀ t, (Φ t : X → ℝ) =ᵐ[D.μ] fun x => dualPow (expPath ρ t) (f x) :=
    fun t => (hΦmem t).coeFn_toLp
  have hinner : ∀ (u : Lp ℝ 2 D.μ) (t : ℝ),
      ⟪u, Φ t⟫_ℝ = ∫ x, (u : X → ℝ) x * dualPow (expPath ρ t) (f x) ∂D.μ := by
    intro u t
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hΦ_coe t] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
    ring
  have hJ_inner : ∀ t, ⟪F, Φ t⟫_ℝ = J t := by
    intro t
    rw [hinner]
    refine integral_congr_ae ?_
    filter_upwards [hFf] with x hx
    rw [hx, mul_dualPow (expPath_pos ρ t)]
  -- `‖Φ t - F‖₂ ≤ (q(t) - 2)(1 + M³)` while `q(t) ≤ 3`.
  have hΦ_sub : ∀ t, 0 ≤ t → expPath ρ t ≤ 3 →
      ‖Φ t - F‖ ≤ (expPath ρ t - 2) * (1 + M ^ 3) := by
    intro t ht ht3
    have h2 := two_le_expPath hρ.le ht
    have hC : 0 ≤ (expPath ρ t - 2) * (1 + M ^ 3) :=
      mul_nonneg (by linarith) (by positivity)
    have hb := Lp.norm_le_of_ae_bound (f := Φ t - F) hC (by
      filter_upwards [Lp.coeFn_sub (Φ t) F, hΦ_coe t, hFf, hM] with x hsub h1 h2' hx
      rw [hsub, Pi.sub_apply, h1, h2', Real.norm_eq_abs]
      exact abs_dualPow_sub_le hx h2 ht3)
    simpa [measureUnivNNReal] using hb
  -- Slopes of the four pieces.
  have hPF : Tendsto (fun t => ‖D.P t F - F‖) (𝓝[>] 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      ((D.P_strong_cont F).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))
  have hq_slope : Tendsto (fun t => t⁻¹ * (expPath ρ t - 2)) (𝓝[>] 0) (𝓝 (2 * ρ)) := by
    simpa [expPath_zero] using tendsto_slope_of_hasDerivAt (hasDerivAt_expPath_zero ρ)
  have hq3 : ∀ᶠ t in 𝓝[>] 0, expPath ρ t ≤ 3 := by
    have hc : Tendsto (expPath ρ) (𝓝[>] 0) (𝓝 2) := by
      have := (hasDerivAt_expPath_zero ρ).continuousAt.tendsto
      rw [expPath_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hc.eventually (ge_mem_nhds (by norm_num))
  have hB : Tendsto (fun t => t⁻¹ * ⟪D.P t F - F, Φ t - F⟫_ℝ) (𝓝[>] 0) (𝓝 0) := by
    have hbound : Tendsto
        (fun t => ‖D.P t F - F‖ * ((1 + M ^ 3) * (t⁻¹ * (expPath ρ t - 2))))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using hPF.mul (tendsto_const_nhds.mul hq_slope)
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hq3, self_mem_nhdsWithin] with t ht3 ht
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 ht')]
    calc t⁻¹ * |⟪D.P t F - F, Φ t - F⟫_ℝ|
        ≤ t⁻¹ * (‖D.P t F - F‖ * ‖Φ t - F‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (inv_nonneg.2 ht'.le)
      _ ≤ t⁻¹ * (‖D.P t F - F‖ * ((expPath ρ t - 2) * (1 + M ^ 3))) := by
          gcongr
          exact hΦ_sub t ht'.le ht3
      _ = ‖D.P t F - F‖ * ((1 + M ^ 3) * (t⁻¹ * (expPath ρ t - 2))) := by ring
  have hA : Tendsto (fun t => t⁻¹ * (⟪F, D.P t F⟫_ℝ - ⟪F, D.P 0 F⟫_ℝ)) (𝓝[>] 0)
      (𝓝 (-D.energy f f)) := by
    have h : HasDerivWithinAt (fun t => ⟪F, D.P t F⟫_ℝ) (-D.energy f f) (Ici 0) 0 :=
      D.energy_eq_deriv f f hf hf
    exact tendsto_slope_of_hasDerivWithinAt h
  have hP0 : D.P 0 F = F := by rw [D.P_zero]; rfl
  rw [hP0] at hA
  have hJs := tendsto_slope_of_hasDerivAt hJ_deriv
  have hKs := tendsto_slope_of_hasDerivAt hK_deriv
  -- `G(t) = ⟪P_t F, Φ t⟫ - ‖F‖ K(t)` and its decomposition.
  have hK0 : ‖F‖ * K 0 = I := by
    show ‖F‖ * I ^ e 0 = I
    rw [he0, hnormF, ← Real.rpow_add hIpos, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      Real.rpow_one]
  have hdecomp : ∀ t, ⟪D.P t F, Φ t⟫_ℝ - ‖F‖ * K t =
      ⟪D.P t F - F, Φ t - F⟫_ℝ + (⟪F, D.P t F⟫_ℝ - ⟪F, F⟫_ℝ) + (J t - J 0) -
        ‖F‖ * (K t - K 0) := by
    intro t
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hJ_inner, real_inner_comm F (D.P t F),
      hFF]
    have := hK0
    linarith
  have hG : Tendsto (fun t => t⁻¹ * (⟪D.P t F, Φ t⟫_ℝ - ‖F‖ * K t)) (𝓝[>] 0)
      (𝓝 (0 + -D.energy f f + 2 * ρ * L -
        ‖F‖ * (2 * ρ * L * e 0 * I ^ (e 0 - 1) + ρ / 2 * I ^ e 0 * Real.log I))) := by
    have h := ((hB.add hA).add hJs).sub (hKs.const_mul ‖F‖)
    refine h.congr fun t => ?_
    rw [hdecomp t]; ring
  have hGneg : ∀ t, 0 < t → ⟪D.P t F, Φ t⟫_ℝ - ‖F‖ * K t ≤ 0 := by
    intro t ht
    rw [hinner, sub_nonpos]
    exact integral_mul_dualPow_le D.toMarkovSemigroup h_hyp F ht hfm hM
  have hL := nonpos_of_tendsto_slope hG hGneg
  -- Algebra: `‖F‖ K'(0) = ρ L + (ρ/2) I log I`.
  rw [he0, hnormF] at hL
  have h1 : I ^ (1 / 2 : ℝ) * I ^ (1 / 2 - 1 : ℝ) = 1 := by
    rw [← Real.rpow_add hIpos, show (1 / 2 : ℝ) + (1 / 2 - 1) = 0 by norm_num,
      Real.rpow_zero]
  have h2 : I ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ) = I := by
    rw [← Real.rpow_add hIpos, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  have hE : ρ * L - ρ / 2 * (I * Real.log I) ≤ D.energy f f := by
    have : I ^ (1 / 2 : ℝ) * (2 * ρ * L * (1 / 2) * I ^ (1 / 2 - 1 : ℝ) +
        ρ / 2 * I ^ (1 / 2 : ℝ) * Real.log I) = ρ * L + ρ / 2 * (I * Real.log I) := by
      linear_combination (ρ * L) * h1 + (ρ / 2 * Real.log I) * h2
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
  nlinarith

/-- **Gross's converse for one core function.** Hypercontractivity with rate `ρ` gives
`Ent(f²) ≤ (2/ρ) E(f, f)` for every core `f`; the degenerate case `∫ f² = 0` has zero
entropy. -/
theorem entropy_le_of_hypercontractive (D : DirichletMarkovSemigroup X) {ρ : ℝ}
    (h_hyp : D.toMarkovSemigroup.IsHypercontractive ρ) {f : X → ℝ} (hf : D.IsCore f) :
    ∫ x, f x * f x * Real.log (f x * f x) ∂D.μ -
        (∫ x, f x * f x ∂D.μ) * Real.log (∫ x, f x * f x ∂D.μ) ≤
      2 / ρ * D.energy f f := by
  have hρ : 0 < ρ := h_hyp.1
  have hsq : ∀ x, f x * f x = |f x| ^ expPath ρ 0 := by
    intro x; rw [expPath_zero, Real.rpow_two, sq_abs, sq]
  have hI : ∫ x, f x * f x ∂D.μ = ∫ x, |f x| ^ expPath ρ 0 ∂D.μ := by simp_rw [hsq]
  have hL : ∫ x, f x * f x * Real.log (f x * f x) ∂D.μ =
      2 * ∫ x, |f x| ^ expPath ρ 0 * Real.log |f x| ∂D.μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show f x * f x * Real.log (f x * f x) = 2 * (|f x| ^ expPath ρ 0 * Real.log |f x|)
    rw [hsq x, expPath_zero, Real.rpow_two, Real.log_pow]; push_cast; ring
  have hI0 : 0 ≤ ∫ x, f x * f x ∂D.μ := integral_nonneg fun x => mul_self_nonneg (f x)
  rcases hI0.eq_or_lt with h0 | hpos
  · -- Degenerate case: `f = 0` a.e., so both entropy terms vanish.
    have hf2 : MemLp f 2 D.μ := D.IsCore_memLp hf
    have hint : Integrable (fun x => f x * f x) D.μ := by
      have := (memLp_two_iff_integrable_sq hf2.aestronglyMeasurable).1 hf2
      simpa [sq] using this
    have hae : (fun x => f x * f x) =ᵐ[D.μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (f x)) hint).1 h0.symm
    have hent : ∫ x, f x * f x * Real.log (f x * f x) ∂D.μ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      rw [hx, zero_mul]
    rw [hent, ← h0]
    simp only [zero_mul, sub_zero]
    exact mul_nonneg (div_nonneg zero_le_two hρ.le) (D.energy_nonneg f)
  · rw [hL, hI]
    exact entropy_le_of_hypercontractive_of_pos D h_hyp hf (hI ▸ hpos)

end GrossConverse

open GrossConverse in
/-- **Gross 1975, Theorem 2 (hypercontractivity ⇒ LSI).** Hypercontractivity
of the bundled `L²(μ)` semigroup implies the log-Sobolev inequality for the
bundled Dirichlet form (on the core), by differentiating the hypercontractive
bound at `t = 0` along `q(t) = 1 + e^{2ρt}` (see the section docstring). -/
theorem gross_hypercontractive_implies_lsi {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (ρ : ℝ)
    (h_hyp : D.toMarkovSemigroup.IsHypercontractive ρ) :
    D.SatisfiesLogSobolev ρ := by
  refine ⟨h_hyp.1, fun f hf => ?_⟩
  exact entropy_le_of_hypercontractive D h_hyp hf

end GrossConverseSection

/-! ## H0 — hypothesis-parameterised Gross (Route A scaffold)

The forward Gross implication (stated with the hypotheses below) keeps the
abstract `DirichletMarkovSemigroup` (and its shipped sorry-free
GaussianFin instance) **unchanged**: the strong-generator facts are
explicit `Prop` hypotheses, not new structural fields — the same
leaf-placement design already used for `stroock_varopoulos`,
Gemini-vetted (passes 1–4). They are discharged per instance at the
call-site (GaussianFin in gaussian-hilbert). See
`plans/gross-discharge.md` (§2–§3) and
`plans/gaussianfin-0b-readiness.md`. -/

variable {X : Type*} [MeasurableSpace X]

/-- **Core invariance under the semigroup.** Applying the `L²`
semigroup `P_t` (`t ≥ 0`) to (the `L²` class of) a core function
yields the `L²` class of *some* core function. Phrased `L²`-side
because the abstract structure exposes only the `Lp` operator, not a
function-level action. Discharged for GaussianFin by
`ouSemigroupFin_preserves_IsCore` (`g' := ouSemigroupFin t g`). -/
def CoreSemigroupInvariant (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ {g : X → ℝ} (hg : D.IsCore g),
    ∃ (g' : X → ℝ) (hg' : D.IsCore g'),
      D.P t (D.coreToL2 hg) = D.coreToL2 hg'

/-- **Generator–form compatibility (strong).** `coreToL2 f ∈ dom(A)`
with the difference quotient converging in `L²`-*norm* (not merely
weakly), and the generator value `Af` pinned by the Dirichlet form
against every core test function. Strengthens `energy_eq_deriv`
(weak, scalar-paired). Gemini pass-3 green-lit; uses the explicit
`nhdsWithin (0:ℝ) (Set.Ioi 0)` / `nhds` idiom of this file (matching
`P_strong_cont`). Discharged for GaussianFin via the proved 1D linear
heat equation lifted + pointwise→strong-`L²` DCT. -/
def GeneratorCompat (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {f : X → ℝ} (hf : D.IsCore f), ∃ Af : Lp ℝ 2 D.μ,
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hf) - D.coreToL2 hf))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Af)
    ∧ ∀ {g : X → ℝ} (hg : D.IsCore g),
        ⟪D.coreToL2 hg, Af⟫_ℝ = - D.energy g f

/-- **Stroock–Varopoulos, generator-paired** (Gemini pass-3 trap fix:
`u^{q-1} ∉ core` makes the abstract `E(u,u^{q-1})` unusable; pass-4
binding fix: `GeneratorCompat` is existential, so the generator
element `Au` + its strong-limit witness are passed explicitly rather
than via a global `A`). The core-power hypotheses match the existing
`stroock_varopoulos` axiom (cleaner than `MemLp.toLp` packaging and
equivalent for the GaussianFin discharge, which has the core
powers). `_hq`/`_hu_half` are contract antecedents (the inequality is
claimed for `q > 1` with `u^{q/2}` core — this is the full range the
Gross interpolation path `q(s) = 1+(p-1)e^{2ρs}` visits for `p > 1`, and
S–V holds throughout: for diffusion/gradient forms it is in fact an
equality `(4(q-1)/q²)Γ(u^{q/2}) = Γ(u,u^{q-1})`. The `2 ≤ q → 1 < q`
relaxation is deep-think vetted, rating Standard — see
`plans/archive/sv-q-relaxation-vetting.md`); `_`-prefixed per the
Mathlib convention for binders required by the statement's shape but
not referenced in the body — the discharger still supplies them
positionally. -/
def StroockVaropoulos (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {u : X → ℝ} (hu : D.IsCore u) (_hu_pos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ y ∂D.μ, ε ≤ u y)
    (q : ℝ) (_hq : 1 < q)
    (_hu_half : D.IsCore (fun x => u x ^ (q / 2)))
    (hu_one : D.IsCore (fun x => u x ^ (q - 1)))
    (Au : Lp ℝ 2 D.μ),
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hu) - D.coreToL2 hu))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Au) →
    (4 * (q - 1) / q ^ 2) *
        D.energy (fun x => u x ^ (q / 2)) (fun x => u x ^ (q / 2))
      ≤ ⟪D.coreToL2 hu_one, - Au⟫_ℝ

/-- **Core `L^p`/`L²` density** (per-instance hypothesis, Gemini-vetted
2026-05-21 — `plans/archive/corelpapprox-vetting.md`). Every nonnegative
`f ∈ L²(μ) ∩ L^p(μ)` is approximated by a sequence of *core, pointwise
strictly-positive* functions `gₙ` converging to `f` in **both** `L^p` and
`L²`. This is the density input the abstract structure cannot supply; the
orbit convergence needed for hypercontractivity is recovered abstractly from
`L²`-contraction of the semigroup (so neither `t` nor `P_t` appears here).
Discharged per instance — e.g. for the Gaussian/OU semigroup by mollified
bounded truncations `+ 1/n` (smooth, bounded, `≥ 1/n` everywhere, hence
core and pointwise strictly positive). -/
def CoreLpL2Approx (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {p : ℝ}, 1 ≤ p → ∀ (f : Lp ℝ 2 D.μ),
    MemLp ((f : X → ℝ)) (ENNReal.ofReal p) D.μ → 0 ≤ f →
    ∃ (g : ℕ → X → ℝ) (_hg : ∀ n, D.IsCore (g n)),
      (∀ n, ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ g n x) ∧
      Filter.Tendsto (fun n => eLpNorm ((f : X → ℝ) - g n) (ENNReal.ofReal p) D.μ)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => eLpNorm ((f : X → ℝ) - g n) 2 D.μ)
        Filter.atTop (nhds 0)

/-! **Gross 1975, Theorem 1 — hypothesis-parameterised (Route A
target).** The predicates `CoreSemigroupInvariant` / `GeneratorCompat`
/ `StroockVaropoulos` (above) live here; the **theorem and its proof**
`gross_lsi_implies_hypercontractive_of_hypotheses` (LSI ⇒
hypercontractivity given those three; Gross's differentiation
argument — Phases P2/P3 of `plans/gross-discharge.md`) are relocated
to `MarkovSemigroups.Abstract.GrossODE` (which imports this file), so
the heavy ODE scaffolding does not bloat this module. The former
hypothesis-free axiom `gross_lsi_implies_hypercontractive` was false
(`DirichletMarkovSemigroup.not_forall_lsi_implies_hypercontractive`)
and has been removed. -/

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- Gross's theorem (reverse direction): hypercontractivity ⇒ LSI. -/
theorem logSobolev_of_hypercontractive (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (h_hyp : D.IsHypercontractive ρ) :
    D.SatisfiesLogSobolev ρ := by
  change D.toMarkovSemigroup.IsHypercontractive ρ at h_hyp
  exact gross_hypercontractive_implies_lsi D ρ h_hyp

/-! ## Direct consequence: the semigroup improves integrability -/

/-- Direct application of hypercontractivity to an `L²(μ)` function
that also lies in `L^p(μ)`:

  `‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}`

whenever `q ≤ 1 + (p − 1) e^{2ρt}`. -/
theorem semigroup_lp_improvement (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (h_hyp : D.IsHypercontractive ρ)
    (f : Lp ℝ 2 D.μ) (p q : ℝ)
    (hf_memLp : MemLp ((⇑f) : X → ℝ) (ENNReal.ofReal p) D.μ)
    (hp : 1 < p) (hpq : p ≤ q)
    (t : ℝ) (ht : 0 < t)
    (h_bound : q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t)) :
    eLpNorm (((D.P t f) : X → ℝ)) (ENNReal.ofReal q) D.μ ≤
      eLpNorm ((⇑f) : X → ℝ) (ENNReal.ofReal p) D.μ :=
  h_hyp.2 p q t hp hpq ht h_bound f hf_memLp

end DirichletMarkovSemigroup

end
