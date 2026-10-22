/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Diamagnetic Inequality for Finite Matrices

For M a real PD Z-matrix and V a real diagonal matrix:

  |(M+iV)⁻¹(x,y)| ≤ M⁻¹(x,y)

(§11 of mass-gap-v3.tex). The proof here is algebraic: a Jacobi–Neumann
series for `(M + iV)⁻¹`, dominated entrywise by the nonnegative Neumann
series for `M⁻¹` (`m_matrix_inverse_nonneg`, from `LaplaceTransform.lean`).
The semigroup route of the reference (Laplace transform, Trotter product,
phase bound, heat-kernel positivity) is not needed.

## References

- Simon, Functional Integration and Quantum Physics (1979), Ch. 22
- Reed-Simon IV, §X.4 (Kato's inequality)
-/

import MarkovSemigroups.Matrix.LaplaceTransform
import MarkovSemigroups.Matrix.Trotter

noncomputable section

open Matrix BigOperators

namespace MatrixSemigroup

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- The complex matrix M + iV where M is real and V is real diagonal. -/
def complexShiftedMatrix (M : Matrix n n ℝ) (V : n → ℝ) : Matrix n n ℂ :=
  M.map (↑· : ℝ → ℂ) + Complex.I • Matrix.diagonal (fun i => (V i : ℂ))

/-- **Diamagnetic inequality (resolvent level).**

|(M+iV)⁻¹(x,y)| ≤ M⁻¹(x,y)

for M a positive definite Z-matrix and V real diagonal.

Proof (Jacobi–Neumann series). Write `M = D (I − P)` with `D = diag M`
(positive by positive definiteness) and `P = I − D⁻¹M ≥ 0` entrywise
(Z-matrix). From `(Σ_{k<K} Pᵏ)(I − P) = I − Pᴷ` and `M⁻¹ ≥ 0`
(`m_matrix_inverse_nonneg`), the partial sums satisfy
`Σ_{k<K} Pᵏ D⁻¹ = M⁻¹ − Pᴷ M⁻¹ ≤ M⁻¹`, so `Σ_k Pᵏ` converges entrywise.
Likewise `M + iV = W (I − Q)` with `W = diag(M_ii + i V_i)`,
`|W_ii| ≥ M_ii`, and `|Qᵏ| ≤ Pᵏ` entrywise; hence `R = Σ_k Qᵏ` converges,
`(I − Q) R = I`, `(M + iV)⁻¹ = R W⁻¹`, and
`|(R W⁻¹)(x,y)| ≤ (Σ_k Pᵏ)(x,y) / M_yy ≤ M⁻¹(x,y)`.

This replaces the earlier five-step semigroup plan (Laplace transform +
Trotter) by a purely algebraic argument. -/
theorem diamagnetic_resolvent (M : Matrix n n ℝ) (V : n → ℝ)
    (hPD : IsPosDef M) (hZ : IsZMatrix M) (x y : n) :
    ‖(complexShiftedMatrix M V)⁻¹ x y‖ ≤ M⁻¹ x y := by
  have hPD' := hPD.toMathlib
  have hdiag : ∀ i, 0 < M i i := fun i => hPD'.diag_pos
  have hdet : IsUnit M.det := (hPD'.det_pos).ne'.isUnit
  have hMinv : IsEntryNonneg M⁻¹ := m_matrix_inverse_nonneg M hPD hZ
  -- Jacobi splitting `M = D (I - P)`, with `P ≥ 0` entrywise.
  set P : Matrix n n ℝ := fun i l => if i = l then 0 else -M i l / M i i with hP_def
  have hP_nonneg : IsEntryNonneg P := by
    intro i l
    simp only [hP_def]
    split_ifs with h
    · exact le_rfl
    · exact div_nonneg (neg_nonneg.mpr (hZ i l h)) (hdiag i).le
  set Dinv : Matrix n n ℝ := Matrix.diagonal fun i => (M i i)⁻¹ with hDinv_def
  have hIP : 1 - P = Dinv * M := by
    refine Matrix.ext fun i l => ?_
    rw [Matrix.sub_apply, Matrix.one_apply, hDinv_def, Matrix.diagonal_mul]
    simp only [hP_def]
    by_cases h : i = l
    · subst h; simp [(hdiag i).ne']
    · simp only [h, ite_false]; field_simp [(hdiag i).ne']; ring
  -- Partial sums of the real Neumann series are bounded by `M⁻¹ D`.
  have hpartial : ∀ K i j, ∑ k ∈ Finset.range K, (P ^ k) i j ≤ M⁻¹ i j * M j j := by
    intro K i j
    have hgeom : (∑ k ∈ Finset.range K, P ^ k) * (1 - P) = 1 - P ^ K := geom_sum_mul_neg P K
    rw [hIP] at hgeom
    have h2 : (∑ k ∈ Finset.range K, P ^ k) * Dinv = M⁻¹ - P ^ K * M⁻¹ := by
      have := congrArg (· * M⁻¹) hgeom
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
        Matrix.sub_mul, Matrix.one_mul] at this
      exact this
    have h3 := congrFun (congrFun h2 i) j
    simp only [hDinv_def, Matrix.mul_diagonal, Matrix.sub_apply] at h3
    have h4 : 0 ≤ (P ^ K * M⁻¹) i j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ =>
        mul_nonneg (isEntryNonneg_pow hP_nonneg K i l) (hMinv l j)
    rw [Matrix.sum_apply] at h3
    have h5 : ∑ k ∈ Finset.range K, (P ^ k) i j =
        (M⁻¹ i j - (P ^ K * M⁻¹) i j) * M j j := by
      rw [← h3]; field_simp [(hdiag j).ne']
    rw [h5]
    exact mul_le_mul_of_nonneg_right (by linarith) (hdiag j).le
  have hsumm : ∀ i j, Summable fun k => (P ^ k) i j := fun i j =>
    summable_of_sum_range_le (fun k => isEntryNonneg_pow hP_nonneg k i j) (hpartial · i j)
  have htsum : ∀ i j, ∑' k, (P ^ k) i j ≤ M⁻¹ i j * M j j := fun i j =>
    Real.tsum_le_of_sum_range_le (fun k => isEntryNonneg_pow hP_nonneg k i j) (hpartial · i j)
  -- The complex splitting `M + iV = W (I - Q)`, `|Q| ≤ P` entrywise.
  set w : n → ℂ := fun i => (M i i : ℂ) + Complex.I * V i with hw_def
  have hw_norm : ∀ i, M i i ≤ ‖w i‖ := by
    intro i
    have : ‖w i‖ = Real.sqrt (M i i ^ 2 + V i ^ 2) := by
      simp only [hw_def, Complex.norm_def, Complex.normSq_apply]
      congr 1; simp; ring
    rw [this]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (V i)])
  have hw_ne : ∀ i, w i ≠ 0 := fun i h => by
    have := hw_norm i; rw [h, norm_zero] at this; linarith [hdiag i]
  set Q : Matrix n n ℂ := fun i l => if i = l then 0 else -(M i l : ℂ) / w i with hQ_def
  have hQP : ∀ i l, ‖Q i l‖ ≤ P i l := by
    intro i l
    simp only [hQ_def, hP_def]
    split_ifs with h
    · simp
    · rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (hZ i l h)]
      exact div_le_div_of_nonneg_left (neg_nonneg.mpr (hZ i l h)) (hdiag i) (hw_norm i)
  have hQk : ∀ k i j, ‖(Q ^ k) i j‖ ≤ (P ^ k) i j := by
    intro k
    induction k with
    | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split_ifs <;> simp
    | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (ih i l) (hQP l j) (norm_nonneg _)
        (isEntryNonneg_pow hP_nonneg k i l)
  have hQsumm : ∀ i j, Summable fun k => (Q ^ k) i j := fun i j =>
    Summable.of_norm_bounded (hsumm i j) (hQk · i j)
  set R : Matrix n n ℂ := fun i j => ∑' k, (Q ^ k) i j with hR_def
  have hR : ∀ i j, HasSum (fun k => (Q ^ k) i j) (R i j) := fun i j => (hQsumm i j).hasSum
  -- `(I - Q) R = I`.
  have hQR : ∀ i j, ∑ l, Q i l * R l j = R i j - (1 : Matrix n n ℂ) i j := by
    intro i j
    have h1 : HasSum (fun k => ∑ l, Q i l * (Q ^ k) l j) (∑ l, Q i l * R l j) :=
      hasSum_sum fun l _ => (hR l j).mul_left (Q i l)
    have h2 : HasSum (fun k => (Q ^ (k + 1)) i j) (R i j - (1 : Matrix n n ℂ) i j) := by
      have := (hasSum_nat_add_iff' 1).mpr (hR i j)
      simpa using this
    have h3 : (fun k => ∑ l, Q i l * (Q ^ k) l j) = fun k => (Q ^ (k + 1)) i j := by
      funext k; rw [pow_succ', Matrix.mul_apply]
    rw [h3] at h1
    exact h1.unique h2
  -- The inverse of `M + iV` is `R W⁻¹`.
  set X : Matrix n n ℂ := fun i j => R i j / w j with hX_def
  have hshift : ∀ i l, complexShiftedMatrix M V i l =
      w i * ((1 : Matrix n n ℂ) i l - Q i l) := by
    intro i l
    simp only [complexShiftedMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, hQ_def, smul_eq_mul]
    split_ifs with h
    · subst h; simp [hw_def]
    · rw [mul_zero, add_zero, zero_sub, neg_div, neg_neg, mul_div_cancel₀ _ (hw_ne i)]
  have hinv : complexShiftedMatrix M V * X = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [hshift, hX_def]
    have : ∑ l, w i * ((1 : Matrix n n ℂ) i l - Q i l) * (R l j / w j) =
        w i / w j * (∑ l, (1 : Matrix n n ℂ) i l * R l j - ∑ l, Q i l * R l j) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      field_simp [hw_ne j]
    rw [this, hQR]
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    split_ifs with h
    · subst h; field_simp [hw_ne i]; ring
    · simp
  rw [Matrix.inv_eq_right_inv hinv]
  -- The entrywise bound.
  have hRb : ‖R x y‖ ≤ M⁻¹ x y * M y y := by
    calc ‖R x y‖ ≤ ∑' k, (P ^ k) x y :=
          tsum_of_norm_bounded (hsumm x y).hasSum (hQk · x y)
      _ ≤ M⁻¹ x y * M y y := htsum x y
  simp only [hX_def, norm_div]
  rw [div_le_iff₀ (lt_of_lt_of_le (hdiag y) (hw_norm y))]
  calc ‖R x y‖ ≤ M⁻¹ x y * M y y := hRb
    _ ≤ M⁻¹ x y * ‖w y‖ := mul_le_mul_of_nonneg_left (hw_norm y) (hMinv x y)

end MatrixSemigroup

end
