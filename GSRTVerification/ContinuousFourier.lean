/-
Formal verification of the continuous angular Fourier extraction used in
"Reconstruction method based on Fourier series for attenuated photoacoustic
tomography in a circular geometry", Section 3.1.
-/
import GSRTVerification.Prelude
import GSRTVerification.AngularFourier

/-!
# Continuous angular orthogonality

Passing from the expansion of the boundary data to the radial integral relation
is, on the angular side, the extraction of the `l`-th Fourier coefficient of a
trigonometric polynomial.  This file verifies that step in continuous form.

* `GSRT.integral_exp_int_mul_I` : `∫₀^{2π} e^{i n θ} dθ = 2π` if `n = 0` and `0`
  otherwise.
* `GSRT.integral_synth_mul_exp` : integrating a truncated angular expansion
  against `e^{-i l θ}` returns `2π` times its `l`-th coefficient.

Together with `GSRT.discrete_angular_extraction` (the same statement on the
sensor grid) this is the angular half of the derivation of the radial relation
from the expansion of the data.
-/

namespace GSRT

open Complex

theorem intCast_mul_I_ne_zero {n : ℤ} (hn : n ≠ 0) : ((n : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (Int.cast_ne_zero.mpr hn) Complex.I_ne_zero

theorem continuous_exp_int_mul_I (n : ℤ) :
    Continuous fun t : ℝ => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I) := by
  fun_prop

/-- `θ ↦ e^{i n θ} / (i n)` is a primitive of `θ ↦ e^{i n θ}`. -/
theorem hasDerivAt_exp_int_mul_I {n : ℤ} (hn : n ≠ 0) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I) / ((n : ℂ) * Complex.I))
      (Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) θ := by
  have hne := intCast_mul_I_ne_zero hn
  have h1 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => (n : ℂ) * (t : ℂ) * Complex.I) ((n : ℂ) * Complex.I) θ := by
    simpa using (h1.const_mul ((n : ℂ))).mul_const Complex.I
  have h4 := h2.cexp.div_const ((n : ℂ) * Complex.I)
  simpa [mul_div_cancel_right₀ _ hne] using h4

/-- **Continuous angular orthogonality.** -/
theorem integral_exp_int_mul_I (n : ℤ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I))
      = if n = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    push_cast
    ring
  · have hne := intCast_mul_I_ne_zero hn
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hasDerivAt_exp_int_mul_I hn θ)
      ((continuous_exp_int_mul_I n).intervalIntegrable _ _)]
    have h2pi : Complex.exp ((n : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show (n : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I
          = (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h2pi]
    simp

/-- **Extraction of the `l`-th angular Fourier coefficient.**  This is the step
that turns the expansion of the boundary data into the radial relation. -/
theorem integral_synth_mul_exp (L : ℕ) (c : ℤ → ℂ) (l : ℤ)
    (hl : l ∈ Finset.Icc (-(L : ℤ)) (L : ℤ)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        synth L c θ * Complex.exp (-((l : ℂ) * (θ : ℂ) * Complex.I)))
      = ((2 * Real.pi : ℝ) : ℂ) * c l := by
  have hfun : ∀ θ : ℝ, synth L c θ * Complex.exp (-((l : ℂ) * (θ : ℂ) * Complex.I))
      = ∑ j ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
          c j * Complex.exp (((j - l : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
    intro θ
    rw [synth, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hfun]
  rw [intervalIntegral.integral_finsetSum
    (fun j _ => ((continuous_exp_int_mul_I (j - l)).const_mul (c j)).intervalIntegrable _ _)]
  have hterm : ∀ j ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          c j * Complex.exp (((j - l : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
        = c j * (if j - l = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
    intro j _
    rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I (j - l)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single l]
  · simp [mul_comm]
  · intro j _ hjl
    simp [sub_eq_zero, hjl]
  · intro hl'
    exact absurd hl hl'

end GSRT
