/-
Formal verification of the spectral (singular value) form of the regularized
solution in "Reconstruction method based on Fourier series for attenuated
photoacoustic tomography in a circular geometry", Section 3.2.
-/
import AttenuatedPAT.Prelude
import AttenuatedPAT.Tikhonov

/-!
# The singular value form of the Tikhonov solution

The paper writes the regularized solution in terms of a singular value
decomposition `A_l = U_l Σ_l V_l^*` as

`x_l^{(λ)} = ∑_j σ_{l,j} / (σ_{l,j}^2 + λ) * (u_{l,j}^* b_l) * v_{l,j}`,

and concludes from `σ / (σ^2 + λ) ≤ 1 / (2 √λ)` that "the components belonging
to small singular values are damped rather than amplified".

Mathlib has no singular value decomposition, but it does have the spectral
theorem for symmetric operators, and the right singular system is exactly an
orthonormal eigenbasis of `Aᴴ A`.  That is what `GSRT.IsSingularSystem` records:
`v i` is the `i`-th right singular vector and `mu i = σ_i ^ 2`.

* `GSRT.exists_isSingularSystem` : such a system always exists, so the results
  below are not vacuous.
* `GSRT.isNormalEqSolution_tikhonovSol` : the explicit spectral formula solves
  the normal equation, hence (with `GSRT.existsUnique_normalEqSolution`) *is* the
  regularized solution.
* `GSRT.norm_inner_tikhonovSol_le` : the damping statement.  Each singular
  component of the solution is bounded by `‖b‖ / (2 √λ)`, uniformly in the
  singular value — this is the paper's conclusion, in the form that makes the
  filter factor bound do its work.
-/

namespace GSRT

open scoped InnerProductSpace
open RCLike

section Spectral

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
variable {n : ℕ}

/-- `v` is a right singular system for `A` with squared singular values `mu`:
an orthonormal eigenbasis of `Aᴴ A`. -/
def IsSingularSystem (A : E →ₗ[ℂ] F) (v : OrthonormalBasis (Fin n) ℂ E)
    (mu : Fin n → ℝ) : Prop :=
  ∀ i, LinearMap.adjoint A (A (v i)) = (mu i : ℂ) • v i

omit [FiniteDimensional ℂ E] in
/-- Expansion of a vector in an orthonormal basis. -/
theorem sum_inner_smul (v : OrthonormalBasis (Fin n) ℂ E) (x : E) :
    ∑ i, (inner ℂ (v i) x) • v i = x := by
  simpa [OrthonormalBasis.repr_apply_apply] using v.sum_repr x

namespace IsSingularSystem

variable {A : E →ₗ[ℂ] F} {v : OrthonormalBasis (Fin n) ℂ E} {mu : Fin n → ℝ}

/-- `mu i` is the square of the `i`-th singular value `‖A (v i)‖`. -/
theorem norm_apply_sq (h : IsSingularSystem A v mu) (i : Fin n) : ‖A (v i)‖ ^ 2 = mu i := by
  have h1 : re (inner ℂ (A (v i)) (A (v i))) = ‖A (v i)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (A (v i))
  have h2 : inner ℂ (A (v i)) (A (v i)) = inner ℂ (v i) (LinearMap.adjoint A (A (v i))) :=
    (LinearMap.adjoint_inner_right A (v i) (A (v i))).symm
  have h3 : inner ℂ (v i) (LinearMap.adjoint A (A (v i))) = (mu i : ℂ) := by
    rw [h i, inner_smul_right, inner_self_eq_norm_sq_to_K, v.orthonormal.1 i]
    norm_num
  rw [← h1, h2, h3]
  simp

theorem mu_nonneg (h : IsSingularSystem A v mu) (i : Fin n) : 0 ≤ mu i := by
  rw [← h.norm_apply_sq i]
  positivity

end IsSingularSystem

/-- The spectral formula for the regularized solution:
`x^{(λ)} = ∑_i (μ_i + λ)⁻¹ ⟪v i, Aᴴ b⟫ v i`.  Since `⟪v i, Aᴴ b⟫ = ⟪A (v i), b⟫`
and `‖A (v i)‖ = σ_i`, this is the paper's
`∑_j σ_j / (σ_j^2 + λ) (u_j^* b) v_j`. -/
noncomputable def tikhonovSol (A : E →ₗ[ℂ] F) (v : OrthonormalBasis (Fin n) ℂ E)
    (mu : Fin n → ℝ) (lam : ℝ) (b : F) : E :=
  ∑ i, ((((mu i + lam : ℝ) : ℂ))⁻¹ * inner ℂ (v i) (LinearMap.adjoint A b)) • v i

variable {A : E →ₗ[ℂ] F} {v : OrthonormalBasis (Fin n) ℂ E} {mu : Fin n → ℝ}

/-- **The spectral formula solves the normal equation.**  Together with
`GSRT.existsUnique_normalEqSolution` this identifies it with the regularized
solution `x_l^{(λ)}`. -/
theorem isNormalEqSolution_tikhonovSol (h : IsSingularSystem A v mu) {lam : ℝ}
    (hlam : 0 < lam) (b : F) :
    IsNormalEqSolution A b lam (tikhonovSol A v mu lam b) := by
  have hden : ∀ i, mu i + lam ≠ 0 := fun i => by
    have := h.mu_nonneg i; positivity
  show normalOp A lam (tikhonovSol A v mu lam b) = LinearMap.adjoint A b
  rw [tikhonovSol, map_sum]
  have hstep : ∀ i : Fin n,
      normalOp A lam (((((mu i + lam : ℝ) : ℂ))⁻¹ *
          inner ℂ (v i) (LinearMap.adjoint A b)) • v i)
        = (inner ℂ (v i) (LinearMap.adjoint A b)) • v i := by
    intro i
    rw [map_smul, normalOp_apply, h i, ← add_smul, smul_smul]
    congr 1
    have hcast : ((mu i : ℂ) + (lam : ℂ)) = (((mu i + lam : ℝ)) : ℂ) := by push_cast; ring
    have hne : (((mu i + lam : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hden i)
    rw [hcast]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  exact sum_inner_smul v (LinearMap.adjoint A b)

/-- The `i`-th singular component of the regularized solution. -/
theorem inner_tikhonovSol (lam : ℝ) (b : F) (i : Fin n) :
    inner ℂ (v i) (tikhonovSol A v mu lam b)
      = (((mu i + lam : ℝ) : ℂ))⁻¹ * inner ℂ (v i) (LinearMap.adjoint A b) :=
  v.orthonormal.inner_right_fintype _ i

/-- **Damping of the singular components.**  Every singular component of the
regularized solution is bounded by `‖b‖ / (2 √λ)`, however small the
corresponding singular value.  This is the paper's conclusion that small
singular values are damped rather than amplified. -/
theorem norm_inner_tikhonovSol_le (h : IsSingularSystem A v mu) {lam : ℝ}
    (hlam : 0 < lam) (b : F) (i : Fin n) :
    ‖inner ℂ (v i) (tikhonovSol A v mu lam b)‖ ≤ ‖b‖ / (2 * Real.sqrt lam) := by
  have hmu := h.mu_nonneg i
  have hden : 0 < mu i + lam := by positivity
  have hsq : ‖A (v i)‖ ^ 2 = mu i := h.norm_apply_sq i
  have hcs : ‖inner ℂ (v i) (LinearMap.adjoint A b)‖ ≤ ‖A (v i)‖ * ‖b‖ := by
    rw [LinearMap.adjoint_inner_right]
    exact norm_inner_le_norm (𝕜 := ℂ) (A (v i)) b
  have hfilter : ‖A (v i)‖ / (‖A (v i)‖ ^ 2 + lam) ≤ 1 / (2 * Real.sqrt lam) :=
    filterFactor_le hlam
  calc ‖inner ℂ (v i) (tikhonovSol A v mu lam b)‖
      = (mu i + lam)⁻¹ * ‖inner ℂ (v i) (LinearMap.adjoint A b)‖ := by
        rw [inner_tikhonovSol, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hden]
    _ ≤ (mu i + lam)⁻¹ * (‖A (v i)‖ * ‖b‖) := by
        have hpos : (0 : ℝ) ≤ (mu i + lam)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left hcs hpos
    _ = (‖A (v i)‖ / (‖A (v i)‖ ^ 2 + lam)) * ‖b‖ := by
        rw [hsq]; field_simp
    _ ≤ (1 / (2 * Real.sqrt lam)) * ‖b‖ :=
        mul_le_mul_of_nonneg_right hfilter (norm_nonneg b)
    _ = ‖b‖ / (2 * Real.sqrt lam) := by ring

/-! ### Existence of a singular system -/

theorem isSymmetric_adjoint_comp (A : E →ₗ[ℂ] F) :
    (LinearMap.adjoint A ∘ₗ A).IsSymmetric := by
  intro x y
  simp only [LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]

/-- **A right singular system always exists**, by the spectral theorem for the
symmetric operator `Aᴴ A`.  Hence the hypotheses of this file are never
vacuous. -/
theorem exists_isSingularSystem (A : E →ₗ[ℂ] F) :
    ∃ (v : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (mu : Fin (Module.finrank ℂ E) → ℝ), IsSingularSystem A v mu := by
  have hT := isSymmetric_adjoint_comp A
  refine ⟨hT.eigenvectorBasis rfl, hT.eigenvalues rfl, fun i => ?_⟩
  have := hT.apply_eigenvectorBasis rfl i
  simpa [LinearMap.comp_apply] using this

end Spectral

end GSRT
