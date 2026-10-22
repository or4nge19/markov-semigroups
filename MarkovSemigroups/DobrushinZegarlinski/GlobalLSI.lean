/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Zegarlinski's weak-coupling hypothesis

The hypotheses of Zegarlinski's theorem for continuous spin systems
on `EuclideanSpace ℝ Λ`. The theorem itself (not formalized here, see
Status): if every single-site conditional
satisfies a log-Sobolev inequality with constant `c > 0` (uniformly in
the boundary), and the gradient interaction matrix `c · J` has column
sums uniformly bounded by some `α < 1`, then the global Gibbs measure
satisfies a log-Sobolev inequality with a constant `C > 0` that depends
only on `c` and `α` — *not* on the volume `|Λ|`.

The proof strategy is the standard *spatial sweeping* / martingale
decomposition of the entropy:

  Ent_μ(f²)  ≤  Σ_x  E_μ [ Ent_{μ_x(·|σ_∖x)}(f²) ]            (chain rule)
              ≤  Σ_x  E_μ [ (2/c) · ∫ ‖∂_x f‖² dμ_x(·|σ_∖x) ]   (local LSI)
              ≤  (2C/c) · ∫ Σ_x ‖∂_x f‖² dμ                    (Neumann)

where the bound at the last step uses the resolvent `(I - c · J)⁻¹`
with operator norm at most `1 / (1 - α)` from the abstract Neumann
series. This gives `C = c · (1 - α)`.

## Status

* `ZegarlinskiCondition` is fully defined; it is the Dobrushin-style
  weak-coupling hypothesis on `c · J`, together with boundedness of the
  mixed second partials (`mixed_bdd`), without which `interactionMatrix`
  (a real `⨆`) takes the junk value `0`.
* `toAbstract` bridges it to `AbstractInfluenceMatrix` (proved).
* `IsGibbsSpecificationFor` records the Boltzmann-density link between
  a specification and its potential.
* **Zegarlinski's global LSI is not formalized.** The former axiom
  `zegarlinski_lsi_inequality` (and the wrapper `global_lsi_of_zegarlinski`)
  were removed on 2026-10-22: as stated, without `mixed_bdd`, they were
  false. For `V(x₁,x₂) = (x₁² + x₂²)/2 − x₁x₂/2 + ε x₁²x₂²` the mixed
  partial `−1/2 + 4ε x₁x₂` is unbounded, so `interactionMatrix V = 0` and
  the condition holds with `α = 0`; every single-site conditional is
  Gaussian with precision `1 + 2ε x_j² ≥ 1`, so the local LSI holds with
  `c = 1`; the axiom then asserted LSI(1), hence Poincaré(1), for the
  Gibbs measure, but `Var(x₁ + x₂) → 4 > 2 = ∫ ‖∇(x₁ + x₂)‖²` as `ε → 0`.
  The true statement (bounded mixed partials, Otto–Reznikoff 2007,
  Thm. 1) is a multi-page entropy iteration and remains open here.

## References

* Zegarlinski, *Lett. Math. Phys.* 20 (1990).
* Stroock and Zegarlinski, *Comm. Math. Phys.* 144 (1992), Thm. 0.1.
* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, §5.7.
-/

import MarkovSemigroups.DobrushinZegarlinski.AbstractInfluence
import MarkovSemigroups.DobrushinZegarlinski.EntropyChainRule
import MarkovSemigroups.DobrushinZegarlinski.EuclideanTransport
import MarkovSemigroups.DobrushinZegarlinski.InteractionMatrix
import MarkovSemigroups.DobrushinZegarlinski.LocalLSI

noncomputable section

namespace MarkovSemigroups.DobrushinZegarlinski

open scoped BigOperators
open MeasureTheory

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Dobrushin–Zegarlinski weak coupling hypothesis.**

Given a potential `V` and a local-LSI constant `c > 0`, there exists
`α < 1` such that the (off-diagonal) interaction is small relative
to the local curvature:

* every column `(J_{·, y} / c)` summed over rows `x ≠ y` is bounded by α;
* every row    `(J_{x, ·} / c)` summed over cols `y ≠ x` is bounded by α.

By Schur's test on `ℓ²`, both bounds together imply the operator-norm
bound `‖J‖_op ≤ α · c`. The global LSI constant expected from
Zegarlinski's theorem is `c · (1 - α)`, the Otto–Reznikoff (2007)
formula `ρ_global = ρ - ‖W‖_op = c - α·c`.

We keep the column and row bounds as separate hypotheses (no Clairaut
symmetry imposed at the structure level), and gate the structure on
`ContDiff ℝ 2 V` and bounded mixed partials (`mixed_bdd`) so that the
`interactionMatrix` is mathematically meaningful (Clairaut-symmetric,
the true supremum). The smoothness witness is
preserved as a field for downstream theorem use.

The hypothesis `c_pos : 0 < c` is required for the division `J/c` to
make sense; for `c = 0` the LSI hypothesis is vacuous anyway. -/
structure ZegarlinskiCondition (V : EuclideanSpace ℝ Λ → ℝ) (c : ℝ) where
  α : ℝ
  α_nonneg : 0 ≤ α
  α_lt_one : α < 1
  c_pos : 0 < c
  /-- C² smoothness of the potential. Required for the
      `interactionMatrix` entries to be mathematically meaningful;
      see `gradInteractionMatrix` for discussion. -/
  hV : ContDiff ℝ 2 V
  /-- The mixed second partials are bounded, so that
      `interactionMatrix V x y` is their true supremum (a real `⨆` of an
      unbounded family is `0`). -/
  mixed_bdd : ∀ x y : Λ, BddAbove (Set.range fun ψ : EuclideanSpace ℝ Λ =>
    ‖fderiv ℝ (fun ψ' => fderiv ℝ V ψ' (EuclideanSpace.single x 1)) ψ
        (EuclideanSpace.single y 1)‖)
  /-- Column sum of `J/c` over rows `x ≠ y` is at most `α`. -/
  col_bound : ∀ y : Λ,
    ∑ x ∈ Finset.univ.erase y, interactionMatrix V x y / c ≤ α
  /-- Row sum of `J/c` over cols `y ≠ x` is at most `α`. -/
  row_bound : ∀ x : Λ,
    ∑ y ∈ Finset.univ.erase x, interactionMatrix V x y / c ≤ α

namespace ZegarlinskiCondition

variable {V : EuclideanSpace ℝ Λ → ℝ} {c : ℝ}

/-- Convert a Zegarlinski condition into the abstract-influence-matrix
data needed to apply the Neumann series.

The off-diagonal entries are `c · J_{xy}`; the diagonal is set to `0`
(the local restorative force lives in the LSI hypothesis on the
conditional at site `x`, not in the interaction matrix). With `Λ`
finite, summability is automatic; the column/row bound reductions
collapse `∑' x : Λ, (if x = y then 0 else f x) = ∑ x ∈ univ.erase y, f x`
via `Finset.sum_erase`. -/
def toAbstract (h : ZegarlinskiCondition V c) :
    AbstractInfluenceMatrix Λ where
  entry x y := if x = y then 0 else interactionMatrix V x y / c
  α := h.α
  α_nonneg := h.α_nonneg
  α_lt_one := h.α_lt_one
  entry_nonneg x y := by
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy]
      exact div_nonneg (interactionMatrix_nonneg V x y) h.c_pos.le
  col_summable _ :=
    summable_of_ne_finset_zero (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)
  col_bound y := by
    rw [tsum_eq_sum (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)]
    rw [show (Finset.univ : Finset Λ) = insert y (Finset.univ.erase y) from
          (Finset.insert_erase (Finset.mem_univ y)).symm,
        Finset.sum_insert (Finset.notMem_erase y _),
        ite_eq_left (rfl : y = y), zero_add]
    rw [Finset.sum_congr rfl
      (fun x hx => ite_eq_right (Finset.ne_of_mem_erase hx))]
    exact h.col_bound y
  row_summable _ :=
    summable_of_ne_finset_zero (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)
  row_bound x := by
    rw [tsum_eq_sum (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)]
    rw [show (Finset.univ : Finset Λ) = insert x (Finset.univ.erase x) from
          (Finset.insert_erase (Finset.mem_univ x)).symm,
        Finset.sum_insert (Finset.notMem_erase x _),
        ite_eq_left (rfl : x = x), zero_add]
    rw [Finset.sum_congr rfl
      (fun y hy => ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hy)))]
    exact h.row_bound x

end ZegarlinskiCondition

/-! ## Gibbs specifications generated by a potential -/

/-- **Witness that a Gibbs specification is generated by a potential.**

The single-site conditionals of `spec` coincide with the Boltzmann-
weight measures associated to `V`:

  (`spec.condDist {x} σ`).map (`τ ↦ τ x`)
    = `(1/Z(x, σ)) · e^{-V(σ extended with value a at x)} · da`

as a measure on `ℝ`, where `Z(x, σ)` is the local partition function
(`> 0`) and `da` is Lebesgue measure on `ℝ`. The extension uses
`Function.update σ x a : SpinConfig Λ ℝ` lifted through
`(EuclideanSpace.equiv Λ ℝ).symm` to evaluate `V`.

This Prop is the load-bearing link between `spec` (used in
`UniformLocalLSI` and `IsGibbsMeasure`) and `V` (used in
`ZegarlinskiCondition`). Without a substantive content, one could
pair a frozen-conditional spec with `V = 0` and derive false
covariance bounds; making the Boltzmann identity explicit makes such
pairings impossible. -/
class IsGibbsSpecificationFor (spec : GibbsSpec Λ ℝ)
    (V : EuclideanSpace ℝ Λ → ℝ) : Prop where
  /-- The Boltzmann-density identity. For every site `x` and every
      boundary configuration `σ`, the σ-x marginal of the spec's
      single-site conditional admits a density proportional to
      `e^{-V(extend σ x a)}` with respect to Lebesgue measure on
      the value coordinate `a : ℝ`. -/
  density_eq : ∀ (x : Λ) (σ : SpinConfig Λ ℝ),
    ∃ Z : ℝ, 0 < Z ∧
      (spec.condDist {x} σ).map (fun τ : SpinConfig Λ ℝ => τ x)
        = Measure.withDensity volume (fun a : ℝ =>
            ENNReal.ofReal ((1 / Z) *
              Real.exp (-V ((EuclideanSpace.equiv Λ ℝ).symm
                              (Function.update σ x a)))))

end MarkovSemigroups.DobrushinZegarlinski

end
