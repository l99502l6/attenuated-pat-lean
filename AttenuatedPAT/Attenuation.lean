/-
Formal verification of the attenuation coefficients of
"Reconstruction method based on Fourier series for attenuated photoacoustic
tomography in a circular geometry", Definition 2.1 and Section 4.1.
-/
import AttenuatedPAT.Prelude

/-!
# Attenuation coefficients

## Principal square root

The paper says that "in both models, the principal branch of the square root is
used".  We realise the principal branch as `GSRT.psqrt z = exp (log z / 2)` and
prove the properties that the paper's arguments rely on:

* `GSRT.psqrt_sq` : `psqrt z ^ 2 = z` for `z ≠ 0`;
* `GSRT.psqrt_re_pos` : the principal square root of a point of the open right
  half plane again lies in the open right half plane;
* `GSRT.psqrt_conj` : the principal branch commutes with conjugation there;
* `GSRT.psqrt_differentiableAt` : it is holomorphic there.

## The two models

For the thermoviscous coefficient `κ₁ ω = ω / √(1 - i τ ω)` and the
Nachman–Smith–Waag coefficient `κ₂ ω = (ω / c₀) √((1 - i τ̃ ω) / (1 - i τ ω))`
we verify exactly the assertions made in Section 4.1:

* `GSRT.kappa1_im_nonneg`, `GSRT.kappa2_im_nonneg` : `0 ≤ Im κ(ω)` for all real
  `ω`, i.e. the values lie in the closed upper half plane.  For `κ₂` this is the
  paper's statement that "the condition `0 < τ̃ < τ` ensures `Im κ₂(ω) ≥ 0` for
  real `ω`".
* `GSRT.kappa1_symm`, `GSRT.kappa2_symm` : the symmetry condition (iii) of
  Definition 2.1, `κ(-ω) = -conj (κ ω)`.
* `GSRT.kappa1_ne_zero`, `GSRT.kappa2_ne_zero` : `κ(ω) ≠ 0` for `ω ≠ 0`, which
  is the hypothesis "for the attenuation models considered below, `κ(ω) ≠ 0` on
  `I_ω`" used for the compactness of `T_l`.

## Definition 2.1

`GSRT.IsAttenuationCoefficient` is a faithful transcription of Definition 2.1.
Its elementary consequences are recorded in `GSRT.IsAttenuationCoefficient.re_zero`,
`re_neg` and `im_neg`.
-/

namespace GSRT

open Complex

/-! ### The principal square root -/

/-- The principal square root, defined through the principal logarithm. -/
noncomputable def psqrt (z : ℂ) : ℂ := Complex.exp (Complex.log z / 2)

theorem psqrt_ne_zero (z : ℂ) : psqrt z ≠ 0 := Complex.exp_ne_zero _

/-- `psqrt` is a square root. -/
theorem psqrt_sq {z : ℂ} (hz : z ≠ 0) : psqrt z ^ 2 = z := by
  rw [psqrt, sq, ← Complex.exp_add, show Complex.log z / 2 + Complex.log z / 2
    = Complex.log z by ring]
  exact Complex.exp_log hz

theorem psqrt_im (z : ℂ) : (psqrt z).im = Real.exp (Real.log ‖z‖ / 2) * Real.sin (z.arg / 2) := by
  rw [psqrt, Complex.exp_im]
  simp [Complex.log_re, Complex.log_im]

/-- The principal square root maps the open right half plane into itself. -/
theorem psqrt_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (psqrt z).re := by
  have harg : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [psqrt, Complex.exp_re]
  have him : (Complex.log z / 2).im = z.arg / 2 := by
    simp [Complex.log_im]
  rw [him]
  have hb := abs_lt.mp harg
  have hcos : 0 < Real.cos (z.arg / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hb.1], by linarith [hb.2]⟩
  exact mul_pos (Real.exp_pos _) hcos

/-- On the open right half plane the principal square root commutes with
conjugation. -/
theorem psqrt_conj {z : ℂ} (hz : 0 < z.re) :
    psqrt ((starRingEnd ℂ) z) = (starRingEnd ℂ) (psqrt z) := by
  have hne : z.arg ≠ Real.pi := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    linarith [h.1]
  rw [psqrt, psqrt, Complex.log_conj z hne, ← Complex.exp_conj]
  congr 1
  rw [map_div₀, show (starRingEnd ℂ) 2 = 2 by simp [Complex.ext_iff]]

/-- On the open right half plane the principal square root is holomorphic;
this is the regularity needed for condition (ii) of Definition 2.1. -/
theorem psqrt_differentiableAt {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ psqrt z := by
  have hslit : z ∈ Complex.slitPlane := Or.inl hz
  exact (Complex.differentiableAt_log hslit).div_const 2 |>.cexp

/-- The defining relation between the imaginary parts: `2 (Re s) (Im s) = Im z`
for `s = psqrt z`. -/
theorem two_mul_re_mul_im_psqrt {z : ℂ} (hz : z ≠ 0) :
    2 * (psqrt z).re * (psqrt z).im = z.im := by
  have h := congrArg Complex.im (psqrt_sq hz)
  rw [sq, Complex.mul_im] at h
  linarith

/-! ### The building block `1 - i a` -/

/-- The complex number `1 - i a` for a real parameter `a`. -/
noncomputable def oneSubI (a : ℝ) : ℂ := 1 - (a : ℂ) * Complex.I

@[simp] theorem oneSubI_re (a : ℝ) : (oneSubI a).re = 1 := by simp [oneSubI]

@[simp] theorem oneSubI_im (a : ℝ) : (oneSubI a).im = -a := by simp [oneSubI]

theorem oneSubI_ne_zero (a : ℝ) : oneSubI a ≠ 0 := by
  intro h
  have : (oneSubI a).re = 0 := by rw [h]; simp
  simp at this

theorem oneSubI_neg (a : ℝ) : oneSubI (-a) = (starRingEnd ℂ) (oneSubI a) := by
  apply Complex.ext <;> simp

theorem normSq_oneSubI (a : ℝ) : Complex.normSq (oneSubI a) = 1 + a ^ 2 := by
  rw [Complex.normSq_apply, oneSubI_re, oneSubI_im]
  ring

/-- The real part of the Nachman–Smith–Waag ratio. -/
theorem ratio_re (a b : ℝ) : (oneSubI b / oneSubI a).re = (1 + a * b) / (1 + a ^ 2) := by
  rw [Complex.div_re, normSq_oneSubI, oneSubI_re, oneSubI_im, oneSubI_re, oneSubI_im]
  ring

/-- The imaginary part of the Nachman–Smith–Waag ratio. -/
theorem ratio_im (a b : ℝ) : (oneSubI b / oneSubI a).im = (a - b) / (1 + a ^ 2) := by
  rw [Complex.div_im, normSq_oneSubI, oneSubI_re, oneSubI_im, oneSubI_re, oneSubI_im]
  ring

theorem ratio_conj (a b : ℝ) :
    oneSubI (-b) / oneSubI (-a) = (starRingEnd ℂ) (oneSubI b / oneSubI a) := by
  rw [oneSubI_neg, oneSubI_neg, map_div₀]

/-! ### The thermoviscous model -/

/-- The thermoviscous attenuation coefficient `κ₁(ω) = ω / √(1 - i τ ω)`. -/
noncomputable def kappa1 (tau om : ℝ) : ℂ := (om : ℂ) / psqrt (oneSubI (tau * om))

theorem kappa1_ne_zero {tau om : ℝ} (hom : om ≠ 0) : kappa1 tau om ≠ 0 := by
  rw [kappa1, div_ne_zero_iff]
  exact ⟨by simpa using hom, psqrt_ne_zero _⟩

/-- **Symmetry condition (iii) for the thermoviscous model.** -/
theorem kappa1_symm (tau om : ℝ) :
    kappa1 tau (-om) = -(starRingEnd ℂ) (kappa1 tau om) := by
  have hre : (0 : ℝ) < (oneSubI (tau * om)).re := by simp
  rw [kappa1, kappa1, show tau * -om = -(tau * om) by ring, oneSubI_neg,
    psqrt_conj hre, map_div₀]
  simp [neg_div]

/-- **The thermoviscous coefficient takes values in the closed upper half
plane.** -/
theorem kappa1_im_nonneg {tau : ℝ} (htau : 0 < tau) (om : ℝ) : 0 ≤ (kappa1 tau om).im := by
  set s : ℂ := psqrt (oneSubI (tau * om)) with hs
  have hre : 0 < s.re := psqrt_re_pos (by simp)
  have hkey : 2 * s.re * s.im = -(tau * om) := by
    have h := two_mul_re_mul_im_psqrt (z := oneSubI (tau * om)) (oneSubI_ne_zero _)
    rw [← hs] at h
    simpa using h
  have hns : 0 < Complex.normSq s := Complex.normSq_pos.mpr (psqrt_ne_zero _)
  have h2 : 2 * s.re * (om * s.im) = -(tau * om ^ 2) := by linear_combination om * hkey
  have h3 : 0 ≤ -(om * s.im) := by nlinarith [h2, hre, htau, sq_nonneg om]
  rw [kappa1, ← hs, Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [show (0 : ℝ) * s.re / Complex.normSq s - om * s.im / Complex.normSq s
      = -(om * s.im) / Complex.normSq s by ring]
  exact div_nonneg h3 hns.le

/-! ### The Nachman–Smith–Waag model -/

/-- The Nachman–Smith–Waag attenuation coefficient
`κ₂(ω) = (ω / c₀) √((1 - i τ̃ ω) / (1 - i τ ω))`. -/
noncomputable def kappa2 (c0 taut tau om : ℝ) : ℂ :=
  ((om / c0 : ℝ) : ℂ) * psqrt (oneSubI (taut * om) / oneSubI (tau * om))

/-- Under `0 < τ̃ < τ` the Nachman–Smith–Waag ratio lies in the open right half
plane, so the principal square root behaves as expected. -/
theorem nsw_ratio_re_pos {taut tau om : ℝ} (ht : 0 < taut) (htt : taut < tau) :
    0 < (oneSubI (taut * om) / oneSubI (tau * om)).re := by
  rw [ratio_re]
  have h1 : (0 : ℝ) < 1 + (tau * om) ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + tau * om * (taut * om) := by nlinarith [sq_nonneg om]
  exact div_pos h2 h1

theorem kappa2_ne_zero {c0 taut tau om : ℝ} (hc0 : c0 ≠ 0) (hom : om ≠ 0) :
    kappa2 c0 taut tau om ≠ 0 := by
  rw [kappa2, mul_ne_zero_iff]
  refine ⟨?_, psqrt_ne_zero _⟩
  simpa using div_ne_zero hom hc0

/-- **Symmetry condition (iii) for the Nachman–Smith–Waag model.** -/
theorem kappa2_symm {c0 taut tau : ℝ} (ht : 0 < taut) (htt : taut < tau) (om : ℝ) :
    kappa2 c0 taut tau (-om) = -(starRingEnd ℂ) (kappa2 c0 taut tau om) := by
  have hre := nsw_ratio_re_pos (taut := taut) (tau := tau) (om := om) ht htt
  rw [kappa2, kappa2, show taut * -om = -(taut * om) by ring,
    show tau * -om = -(tau * om) by ring, ratio_conj, psqrt_conj hre]
  rw [show ((-om / c0 : ℝ) : ℂ) = -((om / c0 : ℝ) : ℂ) by push_cast; ring]
  simp

/-- **The Nachman–Smith–Waag coefficient takes values in the closed upper half
plane**, which is the paper's assertion that `0 < τ̃ < τ` ensures
`Im κ₂(ω) ≥ 0`. -/
theorem kappa2_im_nonneg {c0 taut tau : ℝ} (hc0 : 0 < c0) (ht : 0 < taut)
    (htt : taut < tau) (om : ℝ) : 0 ≤ (kappa2 c0 taut tau om).im := by
  set z : ℂ := oneSubI (taut * om) / oneSubI (tau * om) with hz
  have hzre : 0 < z.re := nsw_ratio_re_pos ht htt
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hzre
    simp at hzre
  set s : ℂ := psqrt z with hs
  have hre : 0 < s.re := psqrt_re_pos hzre
  have hkey : 2 * s.re * s.im = (tau * om - taut * om) / (1 + (tau * om) ^ 2) := by
    have h := two_mul_re_mul_im_psqrt (z := z) hzne
    rw [← hs] at h
    rw [h, hz, ratio_im]
  have hden : (0 : ℝ) < 1 + (tau * om) ^ 2 := by positivity
  have hsim : 0 ≤ om * s.im := by
    have hnum : 0 ≤ om * ((tau * om - taut * om) / (1 + (tau * om) ^ 2)) := by
      rw [show om * ((tau * om - taut * om) / (1 + (tau * om) ^ 2))
          = (tau - taut) * om ^ 2 / (1 + (tau * om) ^ 2) by field_simp]
      apply div_nonneg _ hden.le
      nlinarith [sq_nonneg om]
    have h2 : 2 * s.re * (om * s.im)
        = om * ((tau * om - taut * om) / (1 + (tau * om) ^ 2)) := by
      linear_combination om * hkey
    nlinarith [h2, hre, hnum]
  rw [kappa2, ← hs, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [div_mul_eq_mul_div]
  exact div_nonneg hsim hc0.le

/-! ### Definition 2.1 -/

/-- Definition 2.1 of the paper (following Elbau–Scherzer–Shi): `kap` is an
attenuation coefficient. -/
structure IsAttenuationCoefficient (kap : ℝ → ℂ) : Prop where
  /-- `kap` is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) kap
  /-- `kap` is not the zero function. -/
  ne_zero : kap ≠ 0
  /-- `kap` takes values in the closed upper half plane. -/
  im_nonneg : ∀ om : ℝ, 0 ≤ (kap om).im
  /-- (i) all derivatives of `kap` have at most polynomial growth. -/
  polyGrowth : ∀ n : ℕ, ∃ C > (0 : ℝ), ∃ N : ℕ,
    ∀ om : ℝ, ‖iteratedDeriv n kap om‖ ≤ C * (1 + |om|) ^ N
  /-- (ii) `kap` extends continuously to the closed upper half plane, the
  extension maps it into itself, is holomorphic on the open upper half plane
  and has at most polynomial growth. -/
  hasExtension : ∃ K : ℂ → ℂ,
    ContinuousOn K {z : ℂ | 0 ≤ z.im} ∧
    (∀ z : ℂ, 0 ≤ z.im → 0 ≤ (K z).im) ∧
    (∀ om : ℝ, K (om : ℂ) = kap om) ∧
    DifferentiableOn ℂ K {z : ℂ | 0 < z.im} ∧
    ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ z : ℂ, 0 ≤ z.im → ‖K z‖ ≤ C * (1 + ‖z‖) ^ N
  /-- (iii) the symmetry condition `kap (-ω) = -conj (kap ω)`. -/
  symm : ∀ om : ℝ, kap (-om) = -(starRingEnd ℂ) (kap om)

namespace IsAttenuationCoefficient

variable {kap : ℝ → ℂ}

/-- The symmetry condition forces `kap 0` to be purely imaginary. -/
theorem re_zero (h : IsAttenuationCoefficient kap) : (kap 0).re = 0 := by
  have h0 := h.symm 0
  rw [neg_zero] at h0
  have := congrArg Complex.re h0
  simp at this
  linarith

/-- The real part of an attenuation coefficient is odd. -/
theorem re_neg (h : IsAttenuationCoefficient kap) (om : ℝ) :
    (kap (-om)).re = -(kap om).re := by
  have := congrArg Complex.re (h.symm om)
  simpa using this

/-- The imaginary part of an attenuation coefficient is even. -/
theorem im_neg (h : IsAttenuationCoefficient kap) (om : ℝ) :
    (kap (-om)).im = (kap om).im := by
  have := congrArg Complex.im (h.symm om)
  simpa using this

end IsAttenuationCoefficient

/-! ### The non-attenuating case -/

/-- The non-attenuating model `κ(ω) = ω` satisfies the symmetry condition (iii). -/
theorem nonAttenuating_symm (om : ℝ) :
    ((-om : ℝ) : ℂ) = -(starRingEnd ℂ) ((om : ℝ) : ℂ) := by simp

/-- For the non-attenuating model the Fourier symbol of `𝒜_κ` is `-ω ^ 2`,
i.e. `𝒜_κ = ∂ₜ²`. -/
theorem nonAttenuating_symbol (om : ℝ) : -(((om : ℝ) : ℂ)) ^ 2 = -((om ^ 2 : ℝ) : ℂ) := by
  push_cast
  ring

end GSRT
