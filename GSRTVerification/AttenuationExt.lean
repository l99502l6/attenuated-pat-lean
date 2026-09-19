/-
Formal verification of condition (ii) of Definition 2.1 for the two attenuation
models of "Reconstruction method based on Fourier series for attenuated
photoacoustic tomography in a circular geometry".
-/
import GSRTVerification.Prelude
import GSRTVerification.Attenuation

/-!
# The holomorphic extensions of `κ₁` and `κ₂`

Condition (ii) of Definition 2.1 asks for an extension
`K ∈ C(closed upper half plane; closed upper half plane)` which is holomorphic
on the open upper half plane, restricts to `κ` on `ℝ`, and grows at most
polynomially.  This file constructs that extension for both models and verifies
each of those requirements:

* `GSRT.kappa1C_ofReal`, `GSRT.kappa2C_ofReal` : the extensions restrict to the
  coefficients of Section 4.1;
* `GSRT.kappa1C_im_nonneg`, `GSRT.kappa2C_im_nonneg` : the closed upper half
  plane is mapped into itself;
* `GSRT.kappa1C_differentiableAt`, `GSRT.kappa2C_differentiableAt` and the
  `continuousOn` corollaries : holomorphy and continuity;
* `GSRT.norm_kappa1C_le`, `GSRT.norm_kappa2C_le` : the polynomial bounds
  `‖K z‖ ≤ 1 * (1 + ‖z‖) ^ 1` and `‖K z‖ ≤ C * (1 + ‖z‖) ^ 2`.

The one field of `GSRT.IsAttenuationCoefficient` not established here is
`polyGrowth`, the polynomial growth of *every* real iterated derivative; see the
README.
-/

namespace GSRT

open Complex

-- keep `psqrt` from unfolding into `exp (log _ / 2)` during unification
attribute [local irreducible] psqrt

/-! ### `1 - i a z` for a real parameter `a` -/

/-- The complex affine function `z ↦ 1 - i a z`, the argument of the square root
in both models. -/
noncomputable def oneSubIC (a : ℝ) (z : ℂ) : ℂ := 1 - (a : ℂ) * z * Complex.I

@[simp] theorem oneSubIC_re (a : ℝ) (z : ℂ) : (oneSubIC a z).re = 1 + a * z.im := by
  simp [oneSubIC]

@[simp] theorem oneSubIC_im (a : ℝ) (z : ℂ) : (oneSubIC a z).im = -(a * z.re) := by
  simp [oneSubIC]

theorem oneSubIC_ofReal (a om : ℝ) : oneSubIC a (om : ℂ) = oneSubI (a * om) := by
  simp only [oneSubIC, oneSubI]
  push_cast
  ring

theorem oneSubIC_re_pos {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.im) :
    0 < (oneSubIC a z).re := by
  rw [oneSubIC_re]
  nlinarith

theorem oneSubIC_ne_zero {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.im) : oneSubIC a z ≠ 0 := by
  intro h
  have := oneSubIC_re_pos ha hz
  rw [h] at this
  simp at this

theorem one_le_norm_oneSubIC {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.im) :
    1 ≤ ‖oneSubIC a z‖ := by
  have h1 : (oneSubIC a z).re ≤ ‖oneSubIC a z‖ := Complex.re_le_norm _
  have h2 : 1 ≤ (oneSubIC a z).re := by rw [oneSubIC_re]; nlinarith
  linarith

theorem norm_oneSubIC_le (a : ℝ) (z : ℂ) : ‖oneSubIC a z‖ ≤ 1 + |a| * ‖z‖ := by
  refine (norm_sub_le _ _).trans ?_
  simp

/-! ### Norm of the principal square root -/

theorem norm_psqrt_sq {z : ℂ} (hz : z ≠ 0) : ‖psqrt z‖ ^ 2 = ‖z‖ := by
  rw [← norm_pow, psqrt_sq hz]

theorem one_le_norm_psqrt {z : ℂ} (hz : z ≠ 0) (h : 1 ≤ ‖z‖) : 1 ≤ ‖psqrt z‖ := by
  have h2 := norm_psqrt_sq hz
  nlinarith [norm_nonneg (psqrt z)]

theorem norm_psqrt_le {z : ℂ} (hz : z ≠ 0) {C : ℝ} (h : ‖z‖ ≤ C) (hC : 1 ≤ C) :
    ‖psqrt z‖ ≤ C := by
  have h2 := norm_psqrt_sq hz
  nlinarith [norm_nonneg (psqrt z)]

/-! ### The extension of the thermoviscous model -/

/-- The holomorphic extension of `κ₁` to the closed upper half plane. -/
noncomputable def kappa1C (tau : ℝ) (z : ℂ) : ℂ := z / psqrt (oneSubIC tau z)

theorem kappa1C_ofReal (tau om : ℝ) : kappa1C tau (om : ℂ) = kappa1 tau om := by
  rw [kappa1C, kappa1, oneSubIC_ofReal]

/-- **The extension maps the closed upper half plane into itself.** -/
theorem kappa1C_im_nonneg {tau : ℝ} (htau : 0 < tau) {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ (kappa1C tau z).im := by
  set s : ℂ := psqrt (oneSubIC tau z) with hs
  have hre : 0 < s.re := psqrt_re_pos (oneSubIC_re_pos htau hz)
  have hkey : 2 * s.re * s.im = -(tau * z.re) := by
    have h := two_mul_re_mul_im_psqrt (z := oneSubIC tau z) (oneSubIC_ne_zero htau hz)
    rw [← hs] at h
    simpa using h
  have h1 : 0 ≤ tau * z.im * s.re := mul_nonneg (mul_nonneg htau.le hz) hre.le
  have h2 : 0 ≤ s.re * s.im ^ 2 := mul_nonneg hre.le (sq_nonneg _)
  have hexp : tau * (z.im * s.re - z.re * s.im)
      = tau * z.im * s.re + 2 * (s.re * s.im ^ 2) := by
    linear_combination (-s.im) * hkey
  have hpos : 0 ≤ tau * (z.im * s.re - z.re * s.im) := by rw [hexp]; linarith
  have hnum : 0 ≤ z.im * s.re - z.re * s.im := by nlinarith [hpos, htau]
  rw [kappa1C, ← hs, Complex.div_im]
  rw [show z.im * s.re / Complex.normSq s - z.re * s.im / Complex.normSq s
      = (z.im * s.re - z.re * s.im) / Complex.normSq s by ring]
  exact div_nonneg hnum (Complex.normSq_nonneg _)

/-- **Holomorphy of the extension** at every point of the closed upper half
plane; in particular on the open upper half plane, as Definition 2.1 (ii)
requires. -/
theorem kappa1C_differentiableAt {tau : ℝ} (htau : 0 < tau) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (kappa1C tau) z := by
  have hlin : DifferentiableAt ℂ (oneSubIC tau) z := by
    unfold oneSubIC
    fun_prop
  have hsq : DifferentiableAt ℂ (fun w : ℂ => psqrt (oneSubIC tau w)) z :=
    (psqrt_differentiableAt (oneSubIC_re_pos htau hz)).comp z hlin
  exact differentiableAt_id.div hsq (psqrt_ne_zero _)

theorem kappa1C_differentiableOn {tau : ℝ} (htau : 0 < tau) :
    DifferentiableOn ℂ (kappa1C tau) {z : ℂ | 0 < z.im} :=
  fun _z hz => (kappa1C_differentiableAt htau (le_of_lt hz)).differentiableWithinAt

theorem kappa1C_continuousOn {tau : ℝ} (htau : 0 < tau) :
    ContinuousOn (kappa1C tau) {z : ℂ | 0 ≤ z.im} :=
  fun _z hz => (kappa1C_differentiableAt htau hz).continuousAt.continuousWithinAt

/-- **Polynomial growth of the extension**: `‖κ₁(z)‖ ≤ 1 * (1 + ‖z‖) ^ 1`. -/
theorem norm_kappa1C_le {tau : ℝ} (htau : 0 < tau) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖kappa1C tau z‖ ≤ 1 * (1 + ‖z‖) ^ 1 := by
  have hne := oneSubIC_ne_zero htau hz
  have hs1 : 1 ≤ ‖psqrt (oneSubIC tau z)‖ :=
    one_le_norm_psqrt hne (one_le_norm_oneSubIC htau hz)
  rw [kappa1C, norm_div]
  have hpos : (0 : ℝ) < ‖psqrt (oneSubIC tau z)‖ := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [norm_nonneg z]

/-! ### The extension of the Nachman–Smith–Waag model -/

/-- The holomorphic extension of `κ₂` to the closed upper half plane. -/
noncomputable def kappa2C (c0 taut tau : ℝ) (z : ℂ) : ℂ :=
  (z / (c0 : ℂ)) * psqrt (oneSubIC taut z / oneSubIC tau z)

theorem kappa2C_ofReal (c0 taut tau om : ℝ) :
    kappa2C c0 taut tau (om : ℂ) = kappa2 c0 taut tau om := by
  rw [kappa2C, kappa2, oneSubIC_ofReal, oneSubIC_ofReal]
  congr 1
  push_cast
  ring

theorem nswC_ratio_re_pos {taut tau : ℝ} (ht : 0 < taut) (htt : taut < tau) {z : ℂ}
    (hz : 0 ≤ z.im) : 0 < (oneSubIC taut z / oneSubIC tau z).re := by
  have hq : (0 : ℝ) < Complex.normSq (oneSubIC tau z) :=
    Complex.normSq_pos.mpr (oneSubIC_ne_zero (ht.trans htt) hz)
  rw [Complex.div_re, oneSubIC_re, oneSubIC_im, oneSubIC_re, oneSubIC_im]
  rw [show (1 + taut * z.im) * (1 + tau * z.im) / Complex.normSq (oneSubIC tau z) +
        -(taut * z.re) * -(tau * z.re) / Complex.normSq (oneSubIC tau z)
      = ((1 + taut * z.im) * (1 + tau * z.im) + taut * tau * z.re ^ 2) /
          Complex.normSq (oneSubIC tau z) by ring]
  apply div_pos _ hq
  have htau : 0 < tau := ht.trans htt
  have h1 : (0 : ℝ) < 1 + taut * z.im := by nlinarith
  have h2 : (0 : ℝ) < 1 + tau * z.im := by nlinarith
  nlinarith [mul_pos h1 h2, mul_nonneg (mul_nonneg ht.le htau.le) (sq_nonneg z.re)]

theorem nswC_ratio_ne_zero {taut tau : ℝ} (ht : 0 < taut) (htt : taut < tau) {z : ℂ}
    (hz : 0 ≤ z.im) : oneSubIC taut z / oneSubIC tau z ≠ 0 := by
  intro h
  have := nswC_ratio_re_pos ht htt hz
  rw [h] at this
  simp at this

theorem nswC_ratio_im {taut tau : ℝ} (ht : 0 < taut) (htt : taut < tau) {z : ℂ}
    (hz : 0 ≤ z.im) :
    (oneSubIC taut z / oneSubIC tau z).im
      = z.re * (tau - taut) / Complex.normSq (oneSubIC tau z) := by
  rw [Complex.div_im, oneSubIC_re, oneSubIC_im, oneSubIC_re, oneSubIC_im]
  ring

/-- **The extension maps the closed upper half plane into itself.** -/
theorem kappa2C_im_nonneg {c0 taut tau : ℝ} (hc0 : 0 < c0) (ht : 0 < taut)
    (htt : taut < tau) {z : ℂ} (hz : 0 ≤ z.im) : 0 ≤ (kappa2C c0 taut tau z).im := by
  set s : ℂ := psqrt (oneSubIC taut z / oneSubIC tau z) with hs
  have hre : 0 < s.re := psqrt_re_pos (nswC_ratio_re_pos ht htt hz)
  have hq : (0 : ℝ) < Complex.normSq (oneSubIC tau z) :=
    Complex.normSq_pos.mpr (oneSubIC_ne_zero (ht.trans htt) hz)
  have hkey : 2 * s.re * s.im = z.re * (tau - taut) / Complex.normSq (oneSubIC tau z) := by
    have h := two_mul_re_mul_im_psqrt (z := oneSubIC taut z / oneSubIC tau z)
      (nswC_ratio_ne_zero ht htt hz)
    rw [← hs] at h
    rw [h, nswC_ratio_im ht htt hz]
  have h1 : 0 ≤ z.im * s.re := mul_nonneg hz hre.le
  have h2 : 0 ≤ z.re ^ 2 * (tau - taut) / Complex.normSq (oneSubIC tau z) := by
    apply div_nonneg _ hq.le
    nlinarith [sq_nonneg z.re]
  have hexp : 2 * s.re * (z.re * s.im)
      = z.re ^ 2 * (tau - taut) / Complex.normSq (oneSubIC tau z) := by
    linear_combination z.re * hkey
  have h3 : 0 ≤ z.re * s.im := by nlinarith [hexp, h2, hre]
  have hnum : 0 ≤ z.im * s.re + z.re * s.im := by linarith
  rw [kappa2C, ← hs, Complex.mul_im]
  rw [show (z / (c0 : ℂ)).re = z.re / c0 by
    rw [Complex.div_re]; simp [Complex.normSq_apply]; field_simp]
  rw [show (z / (c0 : ℂ)).im = z.im / c0 by
    rw [Complex.div_im]; simp [Complex.normSq_apply]; field_simp]
  rw [show z.re / c0 * s.im + z.im / c0 * s.re
      = (z.im * s.re + z.re * s.im) / c0 by ring]
  exact div_nonneg hnum hc0.le

/-- **Holomorphy of the extension.** -/
theorem kappa2C_differentiableAt {c0 taut tau : ℝ} (hc0 : c0 ≠ 0) (ht : 0 < taut)
    (htt : taut < tau) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (kappa2C c0 taut tau) z := by
  have hlint : DifferentiableAt ℂ (oneSubIC taut) z := by unfold oneSubIC; fun_prop
  have hlin : DifferentiableAt ℂ (oneSubIC tau) z := by unfold oneSubIC; fun_prop
  have hratio : DifferentiableAt ℂ (fun w : ℂ => oneSubIC taut w / oneSubIC tau w) z :=
    hlint.div hlin (oneSubIC_ne_zero (ht.trans htt) hz)
  have hsq : DifferentiableAt ℂ
      (fun w : ℂ => psqrt (oneSubIC taut w / oneSubIC tau w)) z :=
    (psqrt_differentiableAt (nswC_ratio_re_pos ht htt hz)).comp z hratio
  have hlead : DifferentiableAt ℂ (fun w : ℂ => w / (c0 : ℂ)) z :=
    differentiableAt_id.div_const _
  exact hlead.mul hsq

theorem kappa2C_differentiableOn {c0 taut tau : ℝ} (hc0 : c0 ≠ 0) (ht : 0 < taut)
    (htt : taut < tau) : DifferentiableOn ℂ (kappa2C c0 taut tau) {z : ℂ | 0 < z.im} :=
  fun _z hz => (kappa2C_differentiableAt hc0 ht htt (le_of_lt hz)).differentiableWithinAt

theorem kappa2C_continuousOn {c0 taut tau : ℝ} (hc0 : c0 ≠ 0) (ht : 0 < taut)
    (htt : taut < tau) : ContinuousOn (kappa2C c0 taut tau) {z : ℂ | 0 ≤ z.im} :=
  fun _z hz => (kappa2C_differentiableAt hc0 ht htt hz).continuousAt.continuousWithinAt

/-- **Polynomial growth of the extension**:
`‖κ₂(z)‖ ≤ ((1 + τ̃) / c₀) * (1 + ‖z‖) ^ 2`. -/
theorem norm_kappa2C_le {c0 taut tau : ℝ} (hc0 : 0 < c0) (ht : 0 < taut)
    (htt : taut < tau) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖kappa2C c0 taut tau z‖ ≤ ((1 + taut) / c0) * (1 + ‖z‖) ^ 2 := by
  have hqne := oneSubIC_ne_zero (ht.trans htt) hz
  have hq1 : 1 ≤ ‖oneSubIC tau z‖ := one_le_norm_oneSubIC (ht.trans htt) hz
  have hp : ‖oneSubIC taut z‖ ≤ 1 + taut * ‖z‖ := by
    have := norm_oneSubIC_le taut z
    rwa [abs_of_pos ht] at this
  have hnn : (0 : ℝ) ≤ 1 + taut * ‖z‖ := by
    have := mul_nonneg ht.le (norm_nonneg z); linarith
  have hratio : ‖oneSubIC taut z / oneSubIC tau z‖ ≤ 1 + taut * ‖z‖ := by
    rw [norm_div, div_le_iff₀ (by linarith : (0:ℝ) < ‖oneSubIC tau z‖)]
    calc ‖oneSubIC taut z‖ ≤ 1 + taut * ‖z‖ := hp
      _ = (1 + taut * ‖z‖) * 1 := by ring
      _ ≤ (1 + taut * ‖z‖) * ‖oneSubIC tau z‖ := mul_le_mul_of_nonneg_left hq1 hnn
  have hC : (1 : ℝ) ≤ 1 + taut * ‖z‖ := by nlinarith [norm_nonneg z]
  have hs : ‖psqrt (oneSubIC taut z / oneSubIC tau z)‖ ≤ 1 + taut * ‖z‖ :=
    norm_psqrt_le (nswC_ratio_ne_zero ht htt hz) hratio hC
  rw [kappa2C, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hstep : ‖z‖ / c0 * ‖psqrt (oneSubIC taut z / oneSubIC tau z)‖
      ≤ ‖z‖ / c0 * (1 + taut * ‖z‖) := by
    apply mul_le_mul_of_nonneg_left hs
    positivity
  refine hstep.trans ?_
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc0]
  nlinarith [hz0, ht.le, sq_nonneg ‖z‖, mul_nonneg ht.le hz0]

end GSRT
