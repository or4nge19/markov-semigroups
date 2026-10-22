# markov-semigroups

Markov semigroups, functional inequalities, and convergence to
equilibrium in Lean 4. Built on the
[hille-yosida](https://github.com/mrdouglasny/hille-yosida) C₀-semigroup
framework. The downstream
[gaussian-hilbert](https://github.com/mrdouglasny/gaussian-hilbert) library
combines this repo with
[gaussian-field](https://github.com/mrdouglasny/gaussian-field) for
finite-dim Wiener chaos / polynomial-chaos concentration work.

## What this project proves

The central result chain:

1. **Abstract functional inequalities** (Poincaré, log-Sobolev,
   Holley-Stroock perturbation) for general Dirichlet forms and Markov
   semigroups — no geometry required.

2. **Bakry-Émery curvature criterion** for diffusion generators on
   Riemannian manifolds: $\Gamma_2 \geq \rho \Gamma$ implies LSI($\rho$).

3. **Brascamp-Lieb inequality** for log-concave measures mu = e^{-V} dx
   with V strictly convex: Var_mu(f) <= integral of (nabla f, (Hess V)^{-1} nabla f) dmu.
   Proven from two fields of `LogConcaveMeasure` (resolvent IBP + integrated Bochner identity)
   via weighted Young's inequality. Poincare corollary when Hess V >= rho I.

4. **Ornstein-Uhlenbeck semigroup** defined abstractly for any Hilbert
   space with a positive covariance operator. Mehler's formula, Gaussian
   invariant measure, hypercontractivity.

5. **Concrete instances:** R^n (standard Gaussian, Gross's theorem) and
   T^d (torus GFF, Fourier mode decomposition). Identification of the
   OU invariant measure on T^d with the Gaussian free field from
   gaussian-field.

6. **Convergence to equilibrium:** spectral gap → exponential mixing,
   LSI → entropy decay, ergodicity from spectral gap.

7. **TV coupling characterization:** total variation distance equals
   the infimum over couplings of the disagreement probability.
   Maximal coupling construction.

8. **Dobrushin uniqueness theory:** for lattice spin systems on compact
   state spaces, Dobrushin's condition (column sums of influence matrix
   < 1) implies unique Gibbs measure with exponential correlation decay.
   Includes canonical maximal coupling, iterated Dobrushin coupling via
   Prokhorov compactness, multi-site covariance bounds via condKernel
   disintegration, and Neumann series exponential decay. Used by
   [lgt](https://github.com/mrdouglasny/lgt) for the Yang-Mills mass gap.

9. **Diamagnetic inequality** for finite matrices: |(M+iV)^{-1}(x,y)|
   ≤ M^{-1}(x,y) via a Jacobi–Neumann series dominated by the M-matrix series.

10. **Dobrushin-Zegarlinski infrastructure for continuous spins:** the
    Zegarlinski weak-coupling condition (`J/c ≤ α < 1`, bounded mixed
    partials), the AbstractInfluenceMatrix Neumann theory with
    distance-aware decay, and the single-site entropy decomposition.
    The global LSI (Otto–Reznikoff) and the Helffer–Sjöstrand
    covariance bound themselves are not formalized (their former axioms
    were false as stated; see `AXIOM_AUDIT.md`).

11. **Borell-Herbst concentration from LSI:** for any LSI measure with
    constant `c > 0`, every L-Lipschitz function is sub-Gaussian:
    `μ({F − E_μ F > t}) ≤ exp(−c·t²/(2L²))`. Proven via the Herbst MGF
    bound (`herbst_mgf_bound`, proved) + Mathlib's Chernoff.
    One/two-sided variants, `MemLp` moment bounds, and a Mathlib
    `HasSubgaussianMGF` interop are all proven.

12. **LSI ⇒ Poincaré (variance bound):** standard textbook implication
    that LSI(c) implies the Poincaré inequality with the same constant:
    `Var_μ(f) ≤ (1/c) ∫ ‖∇f‖² dμ`. For L-Lipschitz F, gives
    `Var_μ(F) ≤ L²/c`. Closes the LSI → concentration → variance /
    spectral-gap chain.

**Multivariate Hermite / Wiener chaos / OU eigenfunctions /
polynomial-chaos concentration** (Janson Theorem 5.10) live in
[gaussian-hilbert](https://github.com/mrdouglasny/gaussian-hilbert)
since 2026-05-10. They were originally drafted here in a `Gaussian/`
subdirectory, but the content is "facts about the standard Gaussian
measure" rather than "facts about abstract Markov semigroups", and
gaussian-hilbert (which sits on top of gaussian-field +
markov-semigroups + Mathlib) is the natural home. Removing the cluster
also cleanly eliminated markov-semigroups' cross-repo dependency on
gaussian-field.

## Architecture: three layers of abstraction

The project is organized into three layers, each requiring progressively
more structure. Most results live in the most general layer possible.

### Layer 1: Abstract/ — Measure space + energy form

**Assumes:** A probability space (X, mu) and a symmetric bilinear form
E(f,g) (the Dirichlet form / energy). No gradient, no metric, no
manifold.

**Typeclass:**
```
class DirichletSpace (X : Type*) where
  mu : Measure X                          -- reference probability measure
  energy : (X -> R) -> (X -> R) -> R      -- Dirichlet form E(f,g)
  -- symmetric, positive, closed, Markov property
```

**What lives here:** Poincare inequality, log-Sobolev inequality,
Holley-Stroock perturbation, Gross equivalence (LSI <-> hypercontractivity),
spectral gap, entropy decay, ergodicity. These are all statements about
E and mu with no geometry.

### Layer 2: Diffusion/ — Abstract diffusion generator

**Assumes:** A Dirichlet space with a *carre du champ* operator
Gamma(f,g), which plays the role of |nabla f|^2 without requiring an
actual gradient or Riemannian metric.

**Typeclass:**
```
class MarkovDiffusion (X : Type*) extends DirichletSpace X where
  Gamma : (X -> R) -> (X -> R) -> (X -> R)    -- carre du champ
  -- E(f,g) = integral Gamma(f,g) d mu
```

On a Riemannian manifold, Gamma(f,g) = <nabla f, nabla g>. But the
abstract definition works for any diffusion generator. The iterated
carre du champ Gamma_2 and the Bakry-Emery curvature condition
Gamma_2 >= rho * Gamma are defined at this level. The Bochner-Weitzenbock
formula (connecting Gamma_2 to Ricci curvature) is a *theorem* for
specific instances, not part of the axioms.

**What lives here:** Bakry-Emery criterion, carre du champ, iterated
carre du champ, abstract Ornstein-Uhlenbeck semigroup, invariant measures.

### Layer 3: Instances/ — Concrete spaces

**Assumes:** A specific space with explicit structure.

- **Euclidean.lean** (R^n): Gamma(f,g) = <nabla f, nabla g> via Mathlib's
  `fderiv`. Standard Gaussian, Mehler formula, Bakry-Emery curvature = 1.
- **Torus.lean** (T^d): Fourier eigenvalues lambda_k = 4 pi^2 |k|^2 / L^2 + m^2.
  Heat semigroup as Fourier multiplier. Bakry-Emery curvature = m^2.
  No dependence on Mathlib's manifold library — the torus is handled
  entirely via its Fourier decomposition.
- **GFFIdentification.lean**: OU invariant measure on T^d equals the
  Gaussian free field from gaussian-field (by covariance uniqueness).

### Why no Riemannian manifold library?

The Bakry-Emery framework is designed to avoid needing the full
Riemannian apparatus. The carre du champ Gamma is an *abstract*
bilinear operation satisfying axioms, not necessarily <nabla f, nabla g>
on a smooth manifold. For R^n we use Mathlib's `fderiv`; for T^d we use
Fourier modes. If someone later wants to add a general Riemannian
instance (using Mathlib's `SmoothManifold`), the abstract layers are
ready for it.

## File structure

```
MarkovSemigroups/
  Abstract/                     -- Layer 1: measures + Dirichlet forms
    DirichletForm.lean          -- Symmetric Dirichlet form, variance, entropy
    Poincare.lean               -- Spectral gap <-> variance decay
    LogSobolev.lean             -- Gross LSI, entropy decay
    HolleyStroock.lean          -- Bounded density perturbation of LSI
    Hypercontractivity.lean     -- DirichletMarkovSemigroup; Stroock-Varopoulos; HC => LSI (Gross); LSI => HC needs core hypotheses (counterexample)
    GrossODE.lean               -- Gross-ODE proof of LSI=>HC (FULLY PROVED, sorry-free: gross_lsi_implies_hypercontractive_of_hypotheses, via the 4 per-instance predicates incl. CoreLpL2Approx)
    Concentration.lean          -- Borell-Herbst sub-Gaussian concentration from LSI
  Diffusion/                    -- Layer 2: abstract diffusions (Gamma, Gamma_2)
    CarreDuChamp.lean           -- BakryEmerySpace: Gamma, semigroup, curvature
    StroockVaropoulos.lean      -- RpowChainRule + stroockVaropoulos_eq (S-V equality for diffusion forms)
    BakryEmery.lean             -- Bakry-Emery curvature criterion
    L2Semigroup.lean            -- Bridge to hille-yosida semigroup theory
    InvariantMeasure.lean       -- Invariant probability measures
    OrnsteinUhlenbeck.lean      -- Abstract OU semigroup on Hilbert spaces
  -- (Wiener chaos / multivariate Hermite / OU eigenfunctions /
  -- polynomial-chaos concentration moved to gaussian-hilbert as
  -- GaussianHilbert.* on 2026-05-10.)
  Instances/                    -- Layer 3: concrete spaces (sorry-free)
    Torus.lean                  -- T^d: heat semigroup, Fourier modes (header)
    GFFIdentification.lean      -- OU invariant on T^d = GFF (header)
    BrascampLieb.lean           -- Brascamp-Lieb for log-concave measures
    WorkInProgress/             -- Layer 3, in progress (honest sorries)
      Euclidean.lean            --   R: standard Gaussian, OU semigroup (no sorry, axiom-free; Mehler-kernel axioms discharged)
      TwoPoint.lean             --   {0,1}: not a diffusion — gamma_leibniz_fails PROVES Γ_leibniz fails (0 sorry, 0 axiom)
      EuclideanHypercontractive.lean -- R^n Gaussian: discharges the 4 Gross hypotheses + assembles stdGaussianFin_isHypercontractive (no gross_lsi_implies_hypercontractive axiom)
  Convergence/                  -- Consequences (uses Layer 1 only)
    SpectralGap.lean            -- Exponential mixing from gap
    RelativeEntropy.lean        -- Entropy decay under semigroup
    Ergodicity.lean             -- Uniqueness of invariant measure
    IntegralBounds.lean         -- TV-integral bound (layer cake)
    Doeblin.lean                -- Doeblin's condition, n-step mixing
  Coupling/                     -- Coupling theory
    TVCoupling.lean             -- TV = inf coupling disagreement, maximal coupling
    CanonicalCoupling.lean      -- Constructive pointwise-min coupling, Giry measurability
    DobrushinCoupling.lean      -- Iterated Dobrushin coupling via min-disagreement
    ProkhorovCoupling.lean      -- Prokhorov coupling for compact spin spaces (0 sorry)
  Dobrushin/                    -- Dobrushin uniqueness for lattice spin systems
    Specification.lean          -- Gibbs specifications, conditional distributions
    Uniqueness.lean             -- Uniqueness + exponential correlation decay
    StrongCoupling.lean         -- Strong-coupling verification of Dobrushin condition
    CovarianceBound.lean        -- Single-site covariance bounds
    CondTVBridge.lean           -- Conditional TV bridge, single-site disintegration
    CovarianceBoundMultisite.lean -- Multi-site covariance bounds via condKernel
    CondKernelDLR.lean          -- condKernel inherits DLR, ae bound
    NeumannSeries.lean          -- Neumann series for influence matrix
    FiniteLattice.lean          -- Finite lattice distance structure
  DobrushinZegarlinski/         -- Zegarlinski's theorem for continuous spins
    AbstractInfluence.lean      -- Abstract Neumann decay (pure linear algebra, 0 axioms)
    EuclideanTransport.lean     -- GibbsSpec.toEuclideanMeasure adapter (PiLp 2 transport)
    InteractionMatrix.lean      -- Gradient interaction J_{xy} = sup |∂_y ∂_x V|
    LocalLSI.lean               -- Thin SatisfiesLSI predicate, UniformLocalLSI class
    EntropyChainRule.lean       -- Bochner DLR identity (proved), single-site decomposition (proved)
    GlobalLSI.lean              -- ZegarlinskiCondition (Zegarlinski's global LSI not formalized)
    EntrywiseCovariance.lean    -- Neumann coefficients, coordinate covariance (HS bound not formalized)
  Matrix/                       -- Finite matrix semigroup theory
    HeatKernel.lean             -- exp(-tM) >= 0 for Z-matrices (proved)
    LaplaceTransform.lean       -- M^{-1} = integral exp(-tM) dt
    Trotter.lean                -- Lie-Trotter product formula
    Diamagnetic.lean            -- |(M+iV)^{-1}| <= M^{-1} entrywise
  Tools/                        -- Shared utilities
    SingleSiteDisintegration.lean -- Single-site disintegration of measures on SpinConfig
```

## Formalization status

**No `axiom` and no `sorry`** in any module (default target or not),
verified 2026-10-22 with `#print axioms` (only `propext`,
`Classical.choice`, `Quot.sound`) and a full build of all modules.

### Fully proved (zero sorry's)

- **Bakry-Émery Poincaré** — Var(f) ≤ (1/ρ) E(f,f) from
  semigroup L² decay bound + ergodicity
- **Bakry-Émery variance decay** — Var(P_t f) ≤ e^{-2ρt} Var(f)
  from Poincaré + Grönwall's inequality
- **Bakry-Émery log-Sobolev** — Ent(f²) ≤ (2/ρ) E(f,f) from
  entropy decay bound + entropy ergodicity
- **Brascamp-Lieb inequality** and Poincaré corollary
- **Doeblin's condition** — one-step contraction, TV contraction,
  n-step mixing (by induction), correlation decay
- **TV-integral bound** via layer cake formula
- **TV coupling characterization** — maximal coupling construction
- **Heat kernel positivity** for Z-matrices (Metzler shift)
- **Hessian invertibility** — injectivity, surjectivity, continuity
- **Weighted Young's inequality** from Hessian symmetry
- **Variance nonnegativity** via Mathlib's `ProbabilityTheory.variance_nonneg`

### Axioms: none

See [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md). As of 2026-10-22 the library
declares no `axiom` and has no `sorry`:

| Former axiom | File | Resolution (2026-10-22) |
|---|---|---|
| `herbst_mgf_bound` | `Abstract/Concentration.lean` | **Proved.** Herbst ODE for bounded smooth `G` (`mgf_le_of_lsi_of_bounded`), then mollified truncations of Lipschitz `F` (`exists_differentiable_approx_of_lipschitz`) and Fatou. |
| `poincare_of_lsi` | `Abstract/Concentration.lean` | **Proved.** Linearize the LSI at `1 + εg` for bounded `g` (`variance_le_of_lsi_of_abs_le`), then arctan truncation and dominated convergence. |
| `stroock_varopoulos` | `Abstract/Hypercontractivity.lean` | **Proved.** For each `P_t`: level-set double sum with weights `⟪1_{f=v}, P_t 1_{f=w}⟫ ≥ 0` and the scalar inequality `MarkovOperator.sv_scalar`, uniform approximation, then `t → 0⁺` through `energy_eq_deriv`. |
| `gross_lsi_implies_hypercontractive` | `Abstract/Hypercontractivity.lean` | **False as stated** — the core may consist of constants: `DirichletMarkovSemigroup.not_forall_lsi_implies_hypercontractive` (identity semigroup on `Bool`). Removed, with the wrappers `hypercontractive_of_logSobolev` and `gross_equivalence`. The forward direction with its core hypotheses is the proved `gross_lsi_implies_hypercontractive_of_hypotheses` (`Abstract/GrossODE.lean`). |
| `gross_hypercontractive_implies_lsi` | `Abstract/Hypercontractivity.lean` | **Proved.** Differentiate the hypercontractive bound at `t = 0` along `q(t) = 1 + e^{2ρt}` (Hölder against `φ_q(f) = f|f|^{q-2}`), using only `energy_eq_deriv`. |
| `diamagnetic_resolvent` | `Matrix/Diamagnetic.lean` | **Proved.** Jacobi–Neumann series for `(M + iV)⁻¹`, dominated entrywise by the nonnegative series for `M⁻¹`. |
| `zegarlinski_lsi_inequality` | `DobrushinZegarlinski/GlobalLSI.lean` | **False as stated** — `interactionMatrix` is a real `⨆`, which is `0` for unbounded mixed partials; e.g. `V = (x₁²+x₂²)/2 − x₁x₂/2 + εx₁²x₂²` meets every hypothesis with `α = 0`, `c = 1`, but `Var(x₁+x₂) → 4 > 2`. Removed with `global_lsi_of_zegarlinski` and `DobrushinZegarlinski/Concentration.lean`. `ZegarlinskiCondition` gained `mixed_bdd`. The true statement (Otto–Reznikoff 2007, Thm. 1) is not formalized. |
| `cov_entrywise_bound_of_zegarlinski` | `DobrushinZegarlinski/EntrywiseCovariance.lean` | **False as stated** (same junk value: it asserts `Cov(x₁,x₂) = 0` for the potential above, while `Cov → 2/3`). Removed with `cov_entrywise_decay_nn` / `cov_entrywise_decay_finite_range`. The Helffer–Sjöstrand bound is not formalized. |
| `contDiff_top_convolution_schwartzKernel` | `General/SchwartzConvolution.lean` | **Removed** (file deleted): unused, and `ContDiff ℝ ⊤` means analytic at this Mathlib. |
| `gaussianResolvent`, `gaussianResolvent_ibp`, `gaussianResolvent_ibp_integrable`, `gaussianBochner_identity` | `Instances/WorkInProgress/EuclideanTests.lean` | **Removed** (local scaffolding; `gaussianResolvent` was an opaque function axiom) with the unconditional instance built from them; the file was repaired and builds. |

**For downstream consumers:** [lgt](https://github.com/mrdouglasny/lgt)
imports `MarkovSemigroups.Convergence.Doeblin` (Doeblin mixing); its
closure is `Convergence/Doeblin.lean` + `Convergence/IntegralBounds.lean`.

### History: the Gaussian Bakry–Émery chain

The Gaussian1D concrete instance and the abstract
`MarkovSemigroups/General/OUEntropyDecomposition.lean` are both now
**axiom-free**: all BGL Ch. 2 and §5.5 facts for the Gaussian OU
semigroup have been discharged. As of **2026-05-19**, all multivariate
Gaussian BE axioms are discharged to axiom-free theorems: the de Bruijn
derivative `ouSemigroupFin_l2_sq_hasDerivWithinAt` (in
`Instances/WorkInProgress/EuclideanFinBE.lean`),
`ouSemigroupFin_preserves_IsCore` (Workstream N1.b, Cameron–Martin
kernel route), and `ouSemigroupFin_entropy_sq_decay_bound` (Workstream
N1.c, the 1-parameter telescoping route) — leaving **0 GaussianFin
Bakry–Émery *curvature* axioms**. (The OU *generator* subsystem in
`Instances/WorkInProgress/EuclideanGenerator*.lean`, added later for the
`GeneratorCompat` discharge, is now theorem-only: the coordinatewise Gaussian
integration by parts, pointwise endpoint heat equation, and strong-`L²`
difference quotient were all discharged on 2026-05-22. See the W-step note
below.)

**W-step — Gross axiom bypassed (2026-05-22):**
`Instances/WorkInProgress/EuclideanHypercontractive.lean` discharges all four
per-instance hypotheses of the *proved* `gross_lsi_implies_hypercontractive_of_hypotheses`
for the standard Gaussian OU bundle — `CoreSemigroupInvariant`, `GeneratorCompat`,
`StroockVaropoulos`, `CoreLpL2Approx` — and assembles
`stdGaussianFin_isHypercontractive`. Consequently `#print axioms` of that theorem
(and of the downstream gaussian-hilbert `…_isHypercontractive`) lists only
the 3 Lean built-ins `[propext, Classical.choice, Quot.sound]` — **not**
`gaussianFin_diffQuot_tendsto_Lp`, not `gaussianFin_integrationByParts`, not
`gross_lsi_implies_hypercontractive`, and (since 2026-05-22) **not**
`stroock_varopoulos`. The latter is discharged in the concrete chain as the
diffusion *equality* `BakryEmerySpace.stroockVaropoulos_eq`
(`Diffusion/StroockVaropoulos.lean`) via the `rpow` chain rule; the `StroockVaropoulos`
predicate carries `∃ε>0, ε≤u` a.e. (the chain rule needs strict positivity), supplied
at the unique abstract call site from the positive orbit. No new axioms introduced.

**Discharged 2026-05-12:**
* `ouSemigroup_fisher_info_decay` (A1, BGL Proposition 5.5.2) — the
  Fisher info gradient decay `I(P_t g) ≤ e^{-2t} I(g)`. Proved via
  Cauchy-Schwarz on the Mehler probability kernel + the Mehler
  derivative formula + γ-invariance. ~400 lines including a
  polynomial-discriminant Cauchy-Schwarz helper for γ.
* `hasDerivWithinAt_entropy_ouSemigroup_zero` (A2 at `t = 0+`) —
  derived from A2 (`t > 0` interior version) + DCT-based continuity
  of entropy and Fisher info at `s = 0+` + Mathlib's
  `hasDerivWithinAt_Ici_of_tendsto_deriv`. ~330 lines.
* `hasDerivAt_entropy_ouSemigroup` (A2 interior, BGL §5.5
  de Bruijn identity for `t > 0`) — proved via a Stein-IBP-based
  formula for `(P_t g)''` (avoiding the need for `g''`), parametric
  DCT for the entropy integral, and the bilinear Dirichlet form
  identity (`gaussian_dirichlet_form_bilinear` in
  `EuclideanStein.lean`). ~740 lines.
The previously-axiomatized `ouSemigroup_gradient_decay` (BGL Theorem
5.5.2) is now **PROVED** via the new theorem `hasDerivAt_ouSemigroup`
(Mehler derivative formula via Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) + Jensen +
γ-invariance. Additionally, **Stein's identity** for the
standard Gaussian (BGL §1.15: `∫ y · g(y) dγ = ∫ g'(y) dγ` for
bounded C¹ g) is now **PROVED** as `stein_identity_standard` via the
Gaussian-PDF ODE `pdf'(y) = -y · pdf(y)` + FTC on infinite intervals
(`integral_of_hasDerivAt_of_tendsto`) + `withDensity` bridge. The
**Gaussian Dirichlet form identity** `∫ g · L g dγ = -∫ (g')² dγ`
(`gaussian_dirichlet_form_identity`, BGL §1.6) follows from Stein
applied to `h := g · g'`. `ouSemigroup_preserves_IsCore` was
**DECOMPOSED** (2026-05-12) — the bounded parts `|P_t f|, |(P_t f)'|,
|(P_t f)''| ≤ M` are now proved (`ouSemigroup_preserves_bounds`) via a
generalized Mehler-derivative `hasDerivAt_ouSemigroup_C1` + iterated
formula `hasDerivAt_deriv_ouSemigroup` (giving `(P_t f)'' = e^{-2t}
P_t(f'')`); the `C^∞` smoothing residue (`ouSemigroup_contDiff`) was
then **FULLY DISCHARGED** via the **Hermite IBP path** (Path C):
the closed-form iterated-derivative identity
`(P_t f)^{(n)}(x) = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ` is proved
by induction on `n`, combining parametric integral differentiation
with the n-th-order Stein identity `∫ H_n · F' dγ = ∫ H_{n+1} · F dγ`
(`hermite_ibp_gaussian`). C^∞ conclusion via
`contDiff_of_differentiable_iteratedDeriv`. See
`Instances/WorkInProgress/EuclideanHermite.lean`. As part of this
discharge, `IsCore` was refactored from `ContDiff ℝ ⊤` (analyticity in
current Mathlib) to `ContDiff ℝ ∞` (C^∞), matching the project's
long-standing C^∞ intent. All originally-introduced
axioms were vetted in one pass via Gemini chat
(gemini-3-pro-preview), which flagged a missing `IsCore` hypothesis
on the Mehler-composition axiom — patched in both the axiom and the
upstream `BakryEmerySpace.semigroup_add` field. Five of the original
nine were **reduced to theorems** proved from the remaining four
atomic axioms plus Mathlib's Gaussian infrastructure:
`ouSemigroup_l2_decay_bound` (FTC + gradient decay),
`ouSemigroup_ergodic` (double DCT on Mehler integrand),
`ouSemigroup_entropy_sq_ergodic` (DCT for `s log s` + compactness),
`ouSemigroup_compose` (Gaussian convolution via
`gaussianReal_add_gaussianReal_of_indepFun`), and
`gaussian2D_orthogonal_invariance` (proved by Codex via
`stdGaussian_map` + `map_pi_eq_stdGaussian` through the
`EuclideanSpace ℝ (Fin 2) ≃ₗᵢ WithLp 2 (ℝ × ℝ)` isometry).

(`exp_entryNonneg_of_entryNonneg`, `trotter_product_formula`, and
`m_matrix_inverse_nonneg` were previously axiomatized but are now
proved as theorems in `Matrix/HeatKernel.lean`, `Matrix/Trotter.lean`,
and `Matrix/LaplaceTransform.lean` respectively. `hermiteMulti_dense`
was previously a free-standing axiom in `Gaussian/HermitePolynomials.lean`
but is now a theorem proved from the `polynomial_dense_L2_of_subGaussian`
axiom in gaussian-field's `GeneralResults/PolynomialDensityGaussian.lean`
(decomposed via a `Submodule.span`-based change-of-basis between
multivariate monomials and multivariate Hermite polynomials, fully
proved). An earlier free-standing `entropy_chain_rule_local` axiom was
REMOVED after external review (Gemini, gemini-3-pro-preview): the
statement was mathematically false for general Gibbs measures because
Dirac single-site conditionals at low temperature produce a vanishing
RHS while the LHS remains positive. The DZ proof does not factor
through such a separate chain rule; the iteration is interleaved
inside `zegarlinski_lsi_inequality`.)

### Concrete instances

- **TwoPoint** ({0,1}, uniform measure): not a diffusion —
  `gamma_leibniz_fails` proves that the Γ-Leibniz rule fails for this jump
  process (no sorry, no axiom).
- **Gaussian1D** (ℝ, N(0,1), OU semigroup): axiom-free; all BGL Ch. 2 /
  §5.5 Mehler-kernel facts are proved (see the history section above).

### Verification / validation tests (Instances/WorkInProgress/EuclideanTests.lean)

Test theorems exercising the `Gaussian1D` `BakryEmerySpace ℝ` instance
on concrete inputs. Zero sorries.

| Set | Theorem | Axioms |
|---|---|---|
| **A. Mehler eigenfunctions** | `ouSemigroup_const`, `ouSemigroup_id`, `ouSemigroup_hermite_two`, `ouSemigroup_hermite_three` (eigenvalues `1, e^{-t}, e^{-2t}, e^{-3t}` on `H₀, H₁, H₂, H₃`) | none (Mathlib only) |
| **A. Helpers** | `integral_sq_γ` (= 1), `integral_cube_γ` (= 0), `integrable_cube_γ` | none |
| **B. Bakry-Émery on `cos`** | `cos_isCore`, `cos_poincare` (`Var_γ(cos) ≤ ∫sin² dγ`), `cos_variance_decay` (`Var_γ(P_t cos) ≤ e^{-2t} Var_γ(cos)`) | none |
| **C. Conditional BL → Gaussian Poincaré** | `brascampLieb_recovers_gaussian_poincare` (conditional on a `LogConcaveMeasure ℝ` with `μ = γ`) | none |
| **C. Gaussian potential — structural** | `V_gauss = x²/2`, `contDiff_V_gauss`, `hessianBilin_V_gauss` (= `v · w`), `hV_gauss_convex`, `hV_gauss_curvature` (`‖v‖² ≤ Hess V(v,v)`) | none |

(The unconditional `gaussianLogConcaveMeasure` built from four local
OU-resolvent axioms was removed on 2026-10-22 together with those axioms.)

**Verification summary.** Set A confirms that the Mehler integral
`ouSemigroup` evaluates to the textbook eigenvalues on the first four
Hermite polynomials — operationally verifying it really is the Mehler
kernel. Set B
confirms the abstract `satisfiesPoincare` / `variance_decay` theorems
plug correctly into the concrete instance with `ρ = 1`. Set C confirms
that the Brascamp-Lieb route to Gaussian Poincaré with `ρ = 1` agrees
with the Bakry-Émery route on the same constant.

### TV coupling (Coupling/)

- `tvDist_le_coupling`: TV ≤ P(σ ≠ τ) for any coupling — **proved**
- `maximal_coupling`: optimal coupling construction — **proved**
- `tvDist_eq_inf_coupling`: coupling characterization — **proved**
- `canonicalMaximalCoupling`: constructive pointwise-min coupling — **proved**
- Giry measurability of canonical coupling — **proved** (for countable S)
- `dobrushin_iterated_coupling_fintype`: min-disagreement coupling (finite S) — **proved**
- `prokhorov_coupling_theorem`: min-disagreement coupling (compact S) — **proved**
  via Prokhorov compactness + Portmanteau lsc + kernel Radon-Nikodym

### Dobrushin uniqueness (Dobrushin/)

- `GibbsSpec`, `IsGibbsMeasure`: Gibbs specifications — **defined**
- `DobrushinCondition`: influence matrix condition — **defined**
- `dobrushin_uniqueness`: Dobrushin uniqueness theorem — **proved**
- `influenceCoeff`, `influenceCoeff_le_of_cylinder_ratio_bound` — **proved**
- Single-site disintegration (`condSingleSiteMeasure`) — **proved**
- Multi-site covariance bounds via `condKernel` — **proved**
- `condKernel_ae_bound`: condKernel fiber inherits DLR — **proved**
- Neumann series exponential decay — **proved**

### Matrix semigroup theory (Matrix/)

- **Heat kernel positivity** for Z-matrices: exp(-tM) ≥ 0 entrywise —
  proved via Metzler shift decomposition
- **Euler factor nonnegativity**: I - (t/n)M ≥ 0 for large n — proved
- **Entrywise-nonneg matrix algebra**: pow, mul, add, smul — proved

## Application to P(Phi)_2

The Gaussian results (Phases 1-3) provide the free-field infrastructure
for stochastic quantization. For the interacting theory, the simple
Holley-Stroock perturbation does not apply (the interaction V_a is
unbounded above, so osc(V) = infinity). See [docs/plan.md](docs/plan.md)
for the Gemini review and three alternative approaches for the
interacting spectral gap.

## Development plan

See [docs/plan.md](docs/plan.md) for the full development plan, timeline,
risk assessment, and Gemini review.

### Discharging the Gross axiom (Route A)

The hypothesis-free Gross LSI ⇒ hypercontractivity axiom
(`gross_lsi_implies_hypercontractive`) was false for the bundled
structure and has been removed (2026-10-22); the forward direction is
the proved `gross_lsi_implies_hypercontractive_of_hypotheses`, the
converse `gross_hypercontractive_implies_lsi` is proved. History of the
Route A program:

- [`plans/gross-discharge.md`](plans/gross-discharge.md) — overall
  Route A roadmap (H0/G1/G2/P2/P3/W workstreams). H0, G1, G2 ✅;
  P2 Leibniz kernel ✅ (2026-05-20).
- [`plans/archive/p2-strongL2-leibniz-discharge.md`](plans/archive/p2-strongL2-leibniz-discharge.md)
  — discharge plan for the P2 Bochner-Leibniz kernel.
- [`plans/archive/grosspow-hasderivwithinAt-structural-blockers.md`](plans/archive/grosspow-hasderivwithinAt-structural-blockers.md)
  — analysis of the 4 structural blockers encountered while
  composing `grossPow_hasDerivWithinAt`; 3 of 4 discharged from
  existing structure fields (2026-05-20).
- [`plans/archive/gross-design-strictly-positive-escape.md`](plans/archive/gross-design-strictly-positive-escape.md)
  — design decision (Path A vs Path B) for the remaining Blocker 3.
  Gemini-vetted; Path A (strictly-positive escape, matching Gross
  1975's original proof structure) chosen.

## Dependencies

- [hille-yosida](https://github.com/mrdouglasny/hille-yosida) — C₀-semigroup
  theory, generators, resolvents, Hille-Yosida bound
- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) — Gaussian
  measures on nuclear spaces, hypercontractivity, tightness
- [Mathlib](https://github.com/leanprover-community/mathlib4) — Lean 4
  mathematics library

## Building

```bash
lake update
lake build
```

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014.
- Gross, "Logarithmic Sobolev inequalities," *Amer. J. Math.* 97 (1975),
  1061-1083.
- Holley and Stroock, "Logarithmic Sobolev inequalities and stochastic
  Ising models," *J. Stat. Phys.* 46 (1987), 1159-1194.
- Da Prato and Zabczyk, *Stochastic Equations in Infinite Dimensions*,
  Cambridge, 2014.
- Nelson, "The free Markoff field," *J. Funct. Anal.* 12 (1973), 211-227.
- Fukushima, Oshima, and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 2011.
- Simon, *Functional Integration and Quantum Physics*, Academic Press,
  1979 (Ch. 22: diamagnetic inequality).
- Dobrushin, "The description of a random field by means of conditional
  probabilities," *Theor. Prob. Appl.* 13 (1968), 197–224.
- Lindvall, *Lectures on the Coupling Method*, Wiley, 1992.
- Chatterjee, *Gauge Theory Lecture Notes*, 2026.

## Author

Michael R. Douglas

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
