/-
Formal verification of the Tikhonov regularization step used in
"Reconstruction method based on Fourier series for attenuated photoacoustic
tomography in a circular geometry", Section 3.2.
-/
import AttenuatedPAT.Prelude

/-!
# Zero-order Tikhonov regularization

This file verifies the claims the paper makes about the regularized linear
systems `b_l ≈ A_l x_l`.

* `GSRT.tikhonovObj_eq_add` : the exact excess identity
  `Q x = Q x₀ + ‖A (x - x₀)‖ ^ 2 + lam * ‖x - x₀‖ ^ 2` whenever `x₀` solves the
  normal equation `(Aᴴ A + lam I) x₀ = Aᴴ b`.
* `GSRT.tikhonovObj_le_of_isNormalEqSolution` : hence such an `x₀` is a global
  minimiser of the Tikhonov functional.
* `GSRT.eq_of_isNormalEqSolution_of_le` and `GSRT.existsUnique_normalEqSolution` :
  for `0 < lam` the minimiser exists and is unique, which is the paper's
  assertion that the regularized solution is *the* unique solution of the
  normal equation.
* `GSRT.filterFactor_le` : the filter factor bound
  `σ / (σ ^ 2 + lam) ≤ 1 / (2 * √lam)` used to argue that the components
  belonging to small singular values are damped rather than amplified.
* `GSRT.cond_regularized_le` : the conditioning bound
  `(σmax ^ 2 + lam) / (σmin ^ 2 + lam) ≤ (σmax ^ 2 + lam) / lam`.

The matrices `A_l` of the paper are finite dimensional, so we work with linear
maps between finite dimensional complex inner product spaces, where
`LinearMap.adjoint` is available.
-/

namespace GSRT

open scoped InnerProductSpace
open RCLike

section Tikhonov

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The zero-order Tikhonov functional `x ↦ ‖A x - b‖ ^ 2 + lam * ‖x‖ ^ 2`. -/
noncomputable def tikhonovObj (A : E →ₗ[ℂ] F) (b : F) (lam : ℝ) (x : E) : ℝ :=
  ‖A x - b‖ ^ 2 + lam * ‖x‖ ^ 2

/-- The regularized normal operator `Aᴴ A + lam I`. -/
noncomputable def normalOp (A : E →ₗ[ℂ] F) (lam : ℝ) : E →ₗ[ℂ] E :=
  LinearMap.adjoint A ∘ₗ A + (lam : ℂ) • LinearMap.id

@[simp]
theorem normalOp_apply (A : E →ₗ[ℂ] F) (lam : ℝ) (x : E) :
    normalOp A lam x = LinearMap.adjoint A (A x) + (lam : ℂ) • x := rfl

/-- `x` solves the normal equation `(Aᴴ A + lam I) x = Aᴴ b`. -/
def IsNormalEqSolution (A : E →ₗ[ℂ] F) (b : F) (lam : ℝ) (x : E) : Prop :=
  normalOp A lam x = LinearMap.adjoint A b

theorem isNormalEqSolution_iff (A : E →ₗ[ℂ] F) (b : F) (lam : ℝ) (x : E) :
    IsNormalEqSolution A b lam x ↔
      LinearMap.adjoint A (A x) + (lam : ℂ) • x = LinearMap.adjoint A b := Iff.rfl

/-- The energy identity `re ⟪x, (Aᴴ A + lam I) x⟫ = ‖A x‖ ^ 2 + lam * ‖x‖ ^ 2`. -/
theorem re_inner_normalOp (A : E →ₗ[ℂ] F) (lam : ℝ) (x : E) :
    re (inner ℂ x (normalOp A lam x)) = ‖A x‖ ^ 2 + lam * ‖x‖ ^ 2 := by
  rw [normalOp_apply, inner_add_right, inner_smul_right,
    LinearMap.adjoint_inner_right, map_add,
    inner_self_eq_norm_sq (𝕜 := ℂ) (A x)]
  simp [← Complex.ofReal_pow]

/-- **Excess identity.** If `x₀` solves the normal equation, then for every `x`
the Tikhonov functional exceeds its value at `x₀` by exactly
`‖A (x - x₀)‖ ^ 2 + lam * ‖x - x₀‖ ^ 2`. -/
theorem tikhonovObj_eq_add (A : E →ₗ[ℂ] F) (b : F) (lam : ℝ) {x₀ : E}
    (h : IsNormalEqSolution A b lam x₀) (x : E) :
    tikhonovObj A b lam x
      = tikhonovObj A b lam x₀ + (‖A (x - x₀)‖ ^ 2 + lam * ‖x - x₀‖ ^ 2) := by
  set d : E := x - x₀ with hd
  have hx : x = x₀ + d := by rw [hd]; abel
  have hzero : LinearMap.adjoint A (A x₀ - b) + (lam : ℂ) • x₀ = 0 := by
    rw [map_sub]
    have h' : LinearMap.adjoint A (A x₀) + (lam : ℂ) • x₀ = LinearMap.adjoint A b := h
    rw [show LinearMap.adjoint A (A x₀) - LinearMap.adjoint A b + (lam : ℂ) • x₀
        = LinearMap.adjoint A (A x₀) + (lam : ℂ) • x₀ - LinearMap.adjoint A b by abel,
      h', sub_self]
  -- the cross terms cancel because of the normal equation
  have hcross : re (inner ℂ (A x₀ - b) (A d)) + lam * re (inner ℂ x₀ d) = 0 := by
    have h1 : inner ℂ (A x₀ - b) (A d)
        = inner ℂ (LinearMap.adjoint A (A x₀ - b)) d := (LinearMap.adjoint_inner_left _ _ _).symm
    have h2 : ((lam : ℂ)) * inner ℂ x₀ d = inner ℂ ((lam : ℂ) • x₀) d := by
      rw [inner_smul_left]
      simp
    have h5 : inner ℂ (A x₀ - b) (A d) + (lam : ℂ) * inner ℂ x₀ d = 0 := by
      rw [h1, h2, ← inner_add_left, hzero, inner_zero_left]
    have h6 := congrArg re h5
    simp only [map_add, map_zero] at h6
    rw [show re ((lam : ℂ) * inner ℂ x₀ d) = lam * re (inner ℂ x₀ d) by
      simp] at h6
    exact h6
  have hA : A x - b = (A x₀ - b) + A d := by rw [hx, map_add]; abel
  have hxx : ‖x‖ ^ 2 = ‖x₀‖ ^ 2 + 2 * re (inner ℂ x₀ d) + ‖d‖ ^ 2 := by
    rw [hx]; exact norm_add_sq (𝕜 := ℂ) x₀ d
  have hAA : ‖A x - b‖ ^ 2
      = ‖A x₀ - b‖ ^ 2 + 2 * re (inner ℂ (A x₀ - b) (A d)) + ‖A d‖ ^ 2 := by
    rw [hA]; exact norm_add_sq (𝕜 := ℂ) (A x₀ - b) (A d)
  simp only [tikhonovObj]
  rw [hAA, hxx]
  nlinarith [hcross]

/-- A solution of the normal equation minimises the Tikhonov functional. -/
theorem tikhonovObj_le_of_isNormalEqSolution (A : E →ₗ[ℂ] F) (b : F) {lam : ℝ}
    (hlam : 0 ≤ lam) {x₀ : E} (h : IsNormalEqSolution A b lam x₀) (x : E) :
    tikhonovObj A b lam x₀ ≤ tikhonovObj A b lam x := by
  rw [tikhonovObj_eq_add A b lam h x]
  have hnn : 0 ≤ ‖A (x - x₀)‖ ^ 2 + lam * ‖x - x₀‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hlam (sq_nonneg _))
  linarith

/-- For `0 < lam` the minimiser is unique. -/
theorem eq_of_isNormalEqSolution_of_le (A : E →ₗ[ℂ] F) (b : F) {lam : ℝ}
    (hlam : 0 < lam) {x₀ x : E} (h : IsNormalEqSolution A b lam x₀)
    (hx : tikhonovObj A b lam x ≤ tikhonovObj A b lam x₀) : x = x₀ := by
  have hid := tikhonovObj_eq_add A b lam h x
  have h0 : ‖A (x - x₀)‖ ^ 2 + lam * ‖x - x₀‖ ^ 2 ≤ 0 := by linarith
  have h2 : ‖x - x₀‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖A (x - x₀)‖]
  have h2' : ‖x - x₀‖ ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
  exact eq_of_sub_eq_zero (norm_eq_zero.mp (sq_eq_zero_iff.mp h2'))

/-- For `0 < lam` the regularized normal operator is injective. -/
theorem injective_normalOp (A : E →ₗ[ℂ] F) {lam : ℝ} (hlam : 0 < lam) :
    Function.Injective (normalOp A lam) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := re_inner_normalOp A lam x
  rw [hx, inner_zero_right, map_zero] at h
  have h2 : ‖x‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖A x‖]
  have h2' : ‖x‖ ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2')

/-- **Existence and uniqueness of the regularized solution.** For `0 < lam` the
normal equation `(Aᴴ A + lam I) x = Aᴴ b` has exactly one solution. -/
theorem existsUnique_normalEqSolution (A : E →ₗ[ℂ] F) (b : F) {lam : ℝ}
    (hlam : 0 < lam) : ∃! x : E, IsNormalEqSolution A b lam x := by
  have hinj := injective_normalOp A hlam
  have hsurj : Function.Surjective (normalOp A lam) :=
    LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨x, hx⟩ := hsurj (LinearMap.adjoint A b)
  exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩

/-- The regularized solution is the unique global minimiser of the Tikhonov
functional. -/
theorem existsUnique_tikhonov_minimizer (A : E →ₗ[ℂ] F) (b : F) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃! x₀ : E, ∀ x : E, tikhonovObj A b lam x₀ ≤ tikhonovObj A b lam x := by
  obtain ⟨x₀, hx₀, -⟩ := existsUnique_normalEqSolution A b hlam
  refine ⟨x₀, tikhonovObj_le_of_isNormalEqSolution A b hlam.le hx₀, fun y hy => ?_⟩
  exact eq_of_isNormalEqSolution_of_le A b hlam hx₀ (hy x₀)

end Tikhonov

section Filter

/-- **Filter factor bound** (Section 3.2): for every real `σ` and `0 < lam`,
`σ / (σ ^ 2 + lam) ≤ 1 / (2 * √lam)`.  This is the paper's justification that
the components belonging to small singular values are damped rather than
amplified. -/
theorem filterFactor_le {σ lam : ℝ} (hlam : 0 < lam) :
    σ / (σ ^ 2 + lam) ≤ 1 / (2 * Real.sqrt lam) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  have hden : 0 < σ ^ 2 + lam := by positivity
  rw [div_le_div_iff₀ hden (by positivity)]
  nlinarith [sq_nonneg (σ - Real.sqrt lam)]

/-- The regularized condition number is bounded by `(σmax ^ 2 + lam) / lam`,
as stated in Section 4.2. -/
theorem cond_regularized_le {σmax σmin lam : ℝ} (hlam : 0 < lam) :
    (σmax ^ 2 + lam) / (σmin ^ 2 + lam) ≤ (σmax ^ 2 + lam) / lam := by
  have hnum : 0 ≤ σmax ^ 2 + lam := by positivity
  have hle : lam ≤ σmin ^ 2 + lam := by nlinarith [sq_nonneg σmin]
  gcongr

end Filter

end GSRT
