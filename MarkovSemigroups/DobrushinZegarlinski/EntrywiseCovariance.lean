/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Entrywise Neumann coefficients and coordinate covariance

Support for an entrywise covariance bound under the Zegarlinski
hypothesis: the entrywise Neumann sum `Σₙ ((J/c)ⁿ)_{xy}` of an
`AbstractInfluenceMatrix` and the covariance `Cov_μ(σ_x, σ_y)` of
coordinate functions.

The intended bound (not formalized, see Status) is

  |Cov_μ(σ_x, σ_y)| ≤ (1/c) · Σₙ ((J/c)ⁿ)_{xy} ≤ 1/(c · (1-α)),

a Helffer–Sjöstrand-type estimate for uniformly log-concave Gibbs
measures (`Hess V` with diagonal `≥ c` and off-diagonal entries bounded
by `J`). For finite-range interactions the entrywise iterate vanishes
for `n < d(x, y)/R` (`AbstractInfluenceMatrix.iterate_dist_zero`,
proved), which would give exponential decay `α^{d(x,y)/R}/(c · (1-α))`.

## Status

* `neumannEntrywise` — the entrywise Neumann sum, defined and
  bounded by `1/(1-α)` (proven in `AbstractInfluence.lean`).
* `coord`, `covCoord` — coordinate functions and their covariance.
* **The entrywise covariance bound is not formalized.** The former axiom
  `cov_entrywise_bound_of_zegarlinski` and its corollaries
  `cov_entrywise_decay_nn` / `cov_entrywise_decay_finite_range` were
  removed on 2026-10-22. Without bounded mixed partials the axiom was
  false: `interactionMatrix` is a real `⨆`, equal to `0` for an unbounded
  family, so for `V(x₁,x₂) = (x₁² + x₂²)/2 − x₁x₂/2 + ε x₁²x₂²` (diagonal
  Hessian `≥ 1`, mixed partial `−1/2 + 4ε x₁x₂`) it asserted
  `Cov_μ(σ₁, σ₂) = 0`, whereas `Cov_μ(σ₁, σ₂) → 2/3` as `ε → 0`. The
  intended statement (with `ZegarlinskiCondition.mixed_bdd`) is a
  Helffer–Sjöstrand covariance estimate and remains open here.

## References

* Helffer & Sjöstrand, "On the correlations for Kac-like models in
  the convex case," *J. Stat. Phys.* 74 (1994).
* Naddaf & Spencer, "On homogenization and scaling limit of some
  gradient perturbations of a massless free field," *Comm. Math. Phys.*
  183 (1997).
* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §4.5 (variance and covariance under
  log-concavity).
-/

import MarkovSemigroups.DobrushinZegarlinski.AbstractInfluence
import MarkovSemigroups.DobrushinZegarlinski.GlobalLSI

noncomputable section

namespace MarkovSemigroups.DobrushinZegarlinski

open MeasureTheory

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Entrywise Neumann sum.** For an `AbstractInfluenceMatrix`,
the (x, y) entry of `(I - M)⁻¹` is `Σₙ Mⁿ(x, y)`. This is the
canonical "spatial decay coefficient" between sites x and y. -/
noncomputable def AbstractInfluenceMatrix.neumannEntrywise
    (M : AbstractInfluenceMatrix Λ) (x y : Λ) : ℝ :=
  ∑' n, M.iterate n x y

section
omit [Fintype Λ]

/-- The entrywise Neumann sum is bounded by the resolvent norm
`1/(1-α)`. This is `neumann_series_pointwise_bound` (proved). -/
lemma AbstractInfluenceMatrix.neumannEntrywise_le
    (M : AbstractInfluenceMatrix Λ) (x y : Λ) :
    M.neumannEntrywise x y ≤ (1 - M.α)⁻¹ :=
  M.neumann_series_pointwise_bound x y

/-- The entrywise Neumann sum is nonnegative. -/
lemma AbstractInfluenceMatrix.neumannEntrywise_nonneg
    (M : AbstractInfluenceMatrix Λ) (x y : Λ) :
    0 ≤ M.neumannEntrywise x y :=
  tsum_nonneg fun n => M.iterate_nonneg n x y

end

/-! ## Coordinate functions and covariance -/

/-- The coordinate function at site `x`: maps a configuration to its
value at `x`. Used as the test function for the Helffer-Sjöstrand
covariance representation. -/
def coord (x : Λ) : SpinConfig Λ ℝ → ℝ := fun σ => σ x

/-- Covariance of two coordinate functions under measure `μ`. -/
def covCoord (μ : Measure (SpinConfig Λ ℝ)) (x y : Λ) : ℝ :=
  (∫ σ, σ x * σ y ∂μ) - (∫ σ, σ x ∂μ) * (∫ σ, σ y ∂μ)

end MarkovSemigroups.DobrushinZegarlinski

end
