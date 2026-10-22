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

/-- **Postulated (Gross 1975, Theorem 2).** Hypercontractivity of the
bundled `L²(μ)` semigroup implies LSI for the bundled Dirichlet form.

The proof differentiates the hypercontractive bound at `t = 0` with
`p = 2`, `q = 2 + ε`, and takes `ε → 0`. -/
axiom gross_hypercontractive_implies_lsi {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (ρ : ℝ)
    (h_hyp : D.toMarkovSemigroup.IsHypercontractive ρ) :
    D.SatisfiesLogSobolev ρ

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
