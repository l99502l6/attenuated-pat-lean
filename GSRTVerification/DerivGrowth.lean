/-
Formal verification of condition (i) of Definition 2.1 for the two attenuation
models of "Reconstruction method based on Fourier series for attenuated
photoacoustic tomography in a circular geometry".
-/
import GSRTVerification.Prelude
import GSRTVerification.AttenuationExt

/-!
# Polynomial growth of all derivatives

Condition (i) of Definition 2.1 asks that every derivative of `κ` grow at most
polynomially.  Both models are restrictions to `ℝ` of functions holomorphic on a
half plane strictly below the real axis, and there they satisfy a polynomial
bound; Cauchy's estimate on discs of a fixed radius then transfers the bound to
every derivative.

* `GSRT.iteratedDeriv_restrict` : the real iterated derivatives of the
  restriction of a holomorphic function are its complex iterated derivatives.
* `GSRT.polyGrowth_of_bounded` : the Cauchy estimate in the form needed here.
* `GSRT.kappa1_polyGrowth`, `GSRT.kappa2_polyGrowth` : condition (i) for the two
  models.
-/

namespace GSRT

open Complex

attribute [local irreducible] psqrt

/-! ### Elementary half plane estimates -/

/-- If `z.im > -1/τ` and `0 < a ≤ τ`, then `1 + a z.im > 0`. -/
theorem one_add_mul_im_pos {a tau : ℝ} (ha : 0 < a) (hat : a ≤ tau) (htau : 0 < tau)
    {z : ℂ} (hz : -(1 / tau) < z.im) : 0 < 1 + a * z.im := by
  have hmul : a * (-(1 / tau)) < a * z.im := mul_lt_mul_of_pos_left hz ha
  have hval : a * (-(1 / tau)) = -(a / tau) := by field_simp
  have hfrac : a / tau ≤ 1 := (div_le_one htau).mpr hat
  linarith

/-- If `z.im ≥ -1/(2τ)` then `1 + τ z.im ≥ 1/2`. -/
theorem half_le_one_add_mul_im {tau : ℝ} (htau : 0 < tau) {z : ℂ}
    (hz : -(1 / (2 * tau)) ≤ z.im) : (1 : ℝ) / 2 ≤ 1 + tau * z.im := by
  have hmul : tau * (-(1 / (2 * tau))) ≤ tau * z.im :=
    mul_le_mul_of_nonneg_left hz htau.le
  have hval : tau * (-(1 / (2 * tau))) = -(1 / 2) := by field_simp
  linarith

theorem im_lt_of_half {tau : ℝ} (htau : 0 < tau) {z : ℂ}
    (hz : -(1 / (2 * tau)) ≤ z.im) : -(1 / tau) < z.im := by
  have h : (1 : ℝ) / (2 * tau) < 1 / tau := by
    rw [div_lt_div_iff₀ (by positivity) htau]
    nlinarith
  linarith

/-! ### Real iterated derivatives of a holomorphic function -/

/-- On an open set meeting the real axis everywhere, the real iterated
derivatives of the restriction of a holomorphic function are the restrictions of
its complex iterated derivatives. -/
theorem iteratedDeriv_restrict {S : Set ℂ} (hS : IsOpen S) (hmem : ∀ om : ℝ, (om : ℂ) ∈ S) :
    ∀ (n : ℕ) (K : ℂ → ℂ), DifferentiableOn ℂ K S → ∀ om : ℝ,
      iteratedDeriv n (fun t : ℝ => K (t : ℂ)) om = iteratedDeriv n K (om : ℂ) := by
  intro n
  induction n with
  | zero => intro K _ om; simp
  | succ n ih =>
    intro K hK om
    have hana : AnalyticOnNhd ℂ K S := hK.analyticOnNhd hS
    have hderiv : DifferentiableOn ℂ (deriv K) S :=
      (hana.deriv_of_isOpen hS).differentiableOn
    have hcomp : deriv (fun t : ℝ => K (t : ℂ)) = fun t : ℝ => deriv K (t : ℂ) := by
      funext t
      exact ((hK.differentiableAt (hS.mem_nhds (hmem t))).hasDerivAt.comp_ofReal).deriv
    rw [iteratedDeriv_succ', hcomp, ih (deriv K) hderiv om, ← iteratedDeriv_succ']

/-! ### Cauchy's estimate in the form needed here -/

/-- If `K` is holomorphic on the half plane `-2R < Im z` and satisfies
`‖K z‖ ≤ M (1 + ‖z‖)^N` on `-R ≤ Im z`, then every real iterated derivative of
its restriction to `ℝ` satisfies a bound of the same polynomial degree. -/
theorem polyGrowth_of_bounded {K : ℂ → ℂ} {R M : ℝ} {N : ℕ} (hR : 0 < R) (hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℂ K {z : ℂ | -(2 * R) < z.im})
    (hbound : ∀ z : ℂ, -R ≤ z.im → ‖K z‖ ≤ M * (1 + ‖z‖) ^ N)
    (n : ℕ) (om : ℝ) :
    ‖iteratedDeriv n (fun t : ℝ => K (t : ℂ)) om‖
      ≤ ((n.factorial : ℝ) * (M * (1 + R) ^ N) / R ^ n) * (1 + |om|) ^ N := by
  have hS : IsOpen {z : ℂ | -(2 * R) < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hmem : ∀ t : ℝ, ((t : ℝ) : ℂ) ∈ {z : ℂ | -(2 * R) < z.im} := by
    intro t
    change -(2 * R) < ((t : ℝ) : ℂ).im
    rw [Complex.ofReal_im]
    linarith
  rw [iteratedDeriv_restrict hS hmem n K hdiff om]
  -- the closed disc of radius `R` around `om` lies in the half plane
  have him : ∀ z : ℂ, z ∈ Metric.closedBall ((om : ℂ)) R → -R ≤ z.im := by
    intro z hz
    have h2 : |(z - (om : ℂ)).im| ≤ ‖z - (om : ℂ)‖ := Complex.abs_im_le_norm _
    have h3 : ‖z - (om : ℂ)‖ ≤ R := by
      rw [← Complex.dist_eq]
      exact Metric.mem_closedBall.mp hz
    have h4 : |z.im| ≤ R := by simpa using h2.trans h3
    linarith [(abs_le.mp h4).1]
  have hsub : Metric.closedBall ((om : ℂ)) R ⊆ {z : ℂ | -(2 * R) < z.im} := by
    intro z hz
    have hzz := him z hz
    change -(2 * R) < z.im
    linarith
  have hdc : DiffContOnCl ℂ K (Metric.ball ((om : ℂ)) R) := hdiff.diffContOnCl_ball hsub
  -- bound on the boundary circle
  have hC : ∀ z ∈ Metric.sphere ((om : ℂ)) R, ‖K z‖ ≤ M * (1 + R + |om|) ^ N := by
    intro z hz
    have hdist : ‖z - (om : ℂ)‖ = R := by
      rw [← Complex.dist_eq]
      exact Metric.mem_sphere.mp hz
    have hnorm : ‖z‖ ≤ R + |om| := by
      have hle : ‖z‖ ≤ ‖z - (om : ℂ)‖ + ‖(om : ℂ)‖ := by
        simpa using norm_add_le (z - (om : ℂ)) ((om : ℂ))
      rw [hdist] at hle
      simpa [Complex.norm_real, Real.norm_eq_abs] using hle
    have hz' : -R ≤ z.im := him z (Metric.sphere_subset_closedBall hz)
    refine (hbound z hz').trans ?_
    have hmono : (1 : ℝ) + ‖z‖ ≤ 1 + R + |om| := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmono N) hM
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hdc hC
  refine hcauchy.trans ?_
  have hstep : (1 + R + |om|) ^ N ≤ (1 + R) ^ N * (1 + |om|) ^ N := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    nlinarith [abs_nonneg om, hR.le]
  have hnum : (n.factorial : ℝ) * (M * (1 + R + |om|) ^ N)
      ≤ (n.factorial : ℝ) * (M * ((1 + R) ^ N * (1 + |om|) ^ N)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hM) (by positivity)
  have hRn : (0 : ℝ) < R ^ n := by positivity
  rw [show ((n.factorial : ℝ) * (M * (1 + R) ^ N) / R ^ n) * (1 + |om|) ^ N
      = ((n.factorial : ℝ) * (M * ((1 + R) ^ N * (1 + |om|) ^ N))) / R ^ n by ring]
  exact (div_le_div_iff_of_pos_right hRn).mpr hnum

/-! ### Condition (i) for the thermoviscous model -/

theorem kappa1C_differentiableAt_of_im {tau : ℝ} {z : ℂ}
    (hz : 0 < 1 + tau * z.im) : DifferentiableAt ℂ (kappa1C tau) z := by
  have hre : 0 < (oneSubIC tau z).re := by rw [oneSubIC_re]; exact hz
  have hlin : DifferentiableAt ℂ (oneSubIC tau) z := by unfold oneSubIC; fun_prop
  exact differentiableAt_id.div ((psqrt_differentiableAt hre).comp z hlin) (psqrt_ne_zero _)

theorem norm_kappa1C_le_of_im {tau : ℝ} (htau : 0 < tau) {z : ℂ}
    (hz : -(1 / (2 * tau)) ≤ z.im) : ‖kappa1C tau z‖ ≤ 2 * (1 + ‖z‖) ^ 1 := by
  have hre : (1 : ℝ) / 2 ≤ (oneSubIC tau z).re := by
    rw [oneSubIC_re]
    exact half_le_one_add_mul_im htau hz
  have hne : oneSubIC tau z ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hnorm : (1 : ℝ) / 2 ≤ ‖oneSubIC tau z‖ := le_trans hre (Complex.re_le_norm _)
  have hs : (1 : ℝ) / 2 ≤ ‖psqrt (oneSubIC tau z)‖ := by
    have h2 := norm_psqrt_sq hne
    nlinarith [norm_nonneg (psqrt (oneSubIC tau z))]
  rw [kappa1C, norm_div, div_le_iff₀ (by linarith : (0:ℝ) < ‖psqrt (oneSubIC tau z)‖)]
  nlinarith [norm_nonneg z, hs]

/-- **Condition (i) of Definition 2.1 for the thermoviscous model.** -/
theorem kappa1_polyGrowth {tau : ℝ} (htau : 0 < tau) (n : ℕ) :
    ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ om : ℝ,
      ‖iteratedDeriv n (kappa1 tau) om‖ ≤ C * (1 + |om|) ^ N := by
  set R : ℝ := 1 / (2 * tau) with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  have h2R : 2 * R = 1 / tau := by rw [hRdef]; field_simp
  have hdiff : DifferentiableOn ℂ (kappa1C tau) {z : ℂ | -(2 * R) < z.im} := by
    intro z hz
    have hz' : -(1 / tau) < z.im := by rw [← h2R]; exact hz
    exact (kappa1C_differentiableAt_of_im
      (one_add_mul_im_pos htau le_rfl htau hz')).differentiableWithinAt
  have hbound : ∀ z : ℂ, -R ≤ z.im → ‖kappa1C tau z‖ ≤ 2 * (1 + ‖z‖) ^ 1 := by
    intro z hz
    exact norm_kappa1C_le_of_im htau (by rw [← hRdef]; exact hz)
  have hfun : kappa1 tau = fun t : ℝ => kappa1C tau (t : ℂ) := by
    funext t; rw [kappa1C_ofReal]
  refine ⟨((n.factorial : ℝ) * (2 * (1 + R) ^ 1) / R ^ n) + 1, by positivity, 1, fun om => ?_⟩
  have hmain := polyGrowth_of_bounded hR (by norm_num) hdiff hbound n om
  rw [hfun]
  refine hmain.trans ?_
  have hp : (0 : ℝ) < (1 + |om|) ^ 1 := by positivity
  nlinarith [hp]

/-! ### Condition (i) for the Nachman–Smith–Waag model -/

theorem nsw_ratio_re_pos_of_im {taut tau : ℝ} (ht : 0 < taut) (htt : taut < tau) {z : ℂ}
    (hz : -(1 / tau) < z.im) : 0 < (oneSubIC taut z / oneSubIC tau z).re := by
  have htau : 0 < tau := ht.trans htt
  have h1 : (0 : ℝ) < 1 + tau * z.im := one_add_mul_im_pos htau le_rfl htau hz
  have h2 : (0 : ℝ) < 1 + taut * z.im := one_add_mul_im_pos ht htt.le htau hz
  have hq : oneSubIC tau z ≠ 0 := by
    intro h
    have hre : (oneSubIC tau z).re = 1 + tau * z.im := oneSubIC_re _ _
    rw [h] at hre
    simp at hre
    linarith
  have hqn : (0 : ℝ) < Complex.normSq (oneSubIC tau z) := Complex.normSq_pos.mpr hq
  rw [Complex.div_re, oneSubIC_re, oneSubIC_im, oneSubIC_re, oneSubIC_im]
  rw [show (1 + taut * z.im) * (1 + tau * z.im) / Complex.normSq (oneSubIC tau z) +
        -(taut * z.re) * -(tau * z.re) / Complex.normSq (oneSubIC tau z)
      = ((1 + taut * z.im) * (1 + tau * z.im) + taut * tau * z.re ^ 2) /
          Complex.normSq (oneSubIC tau z) by ring]
  apply div_pos _ hqn
  nlinarith [mul_pos h1 h2, mul_nonneg (mul_nonneg ht.le htau.le) (sq_nonneg z.re)]

theorem kappa2C_differentiableAt_of_im {c0 taut tau : ℝ} (ht : 0 < taut)
    (htt : taut < tau) {z : ℂ} (hz : -(1 / tau) < z.im) :
    DifferentiableAt ℂ (kappa2C c0 taut tau) z := by
  have htau : 0 < tau := ht.trans htt
  have h1 : (0 : ℝ) < 1 + tau * z.im := one_add_mul_im_pos htau le_rfl htau hz
  have hq : oneSubIC tau z ≠ 0 := by
    intro h
    have hre : (oneSubIC tau z).re = 1 + tau * z.im := oneSubIC_re _ _
    rw [h] at hre
    simp at hre
    linarith
  have hlint : DifferentiableAt ℂ (oneSubIC taut) z := by unfold oneSubIC; fun_prop
  have hlin : DifferentiableAt ℂ (oneSubIC tau) z := by unfold oneSubIC; fun_prop
  have hratio : DifferentiableAt ℂ (fun w : ℂ => oneSubIC taut w / oneSubIC tau w) z :=
    hlint.div hlin hq
  have hsq : DifferentiableAt ℂ
      (fun w : ℂ => psqrt (oneSubIC taut w / oneSubIC tau w)) z :=
    (psqrt_differentiableAt (nsw_ratio_re_pos_of_im ht htt hz)).comp z hratio
  exact (differentiableAt_id.div_const ((c0 : ℂ))).mul hsq

theorem norm_kappa2C_le_of_im {c0 taut tau : ℝ} (hc0 : 0 < c0) (ht : 0 < taut)
    (htt : taut < tau) {z : ℂ} (hz : -(1 / (2 * tau)) ≤ z.im) :
    ‖kappa2C c0 taut tau z‖ ≤ (2 * (1 + taut) / c0) * (1 + ‖z‖) ^ 2 := by
  have htau : 0 < tau := ht.trans htt
  have hzim : -(1 / tau) < z.im := im_lt_of_half htau hz
  have hqre : (1 : ℝ) / 2 ≤ (oneSubIC tau z).re := by
    rw [oneSubIC_re]
    exact half_le_one_add_mul_im htau hz
  have hq : oneSubIC tau z ≠ 0 := by
    intro h
    rw [h] at hqre
    simp at hqre
    linarith
  have hqnorm : (1 : ℝ) / 2 ≤ ‖oneSubIC tau z‖ := le_trans hqre (Complex.re_le_norm _)
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hp : ‖oneSubIC taut z‖ ≤ 1 + taut * ‖z‖ := by
    have hnorm := norm_oneSubIC_le taut z
    rwa [abs_of_pos ht] at hnorm
  have hrne : oneSubIC taut z / oneSubIC tau z ≠ 0 := by
    intro h
    have hpos := nsw_ratio_re_pos_of_im ht htt hzim
    rw [h] at hpos
    simp at hpos
  have hratio : ‖oneSubIC taut z / oneSubIC tau z‖ ≤ 2 * (1 + taut * ‖z‖) := by
    rw [norm_div, div_le_iff₀ (by linarith : (0:ℝ) < ‖oneSubIC tau z‖)]
    nlinarith [hp, hqnorm, mul_nonneg ht.le hz0]
  have hbig : (1 : ℝ) ≤ 2 * (1 + taut * ‖z‖) := by
    have := mul_nonneg ht.le hz0; linarith
  have hs : ‖psqrt (oneSubIC taut z / oneSubIC tau z)‖ ≤ 2 * (1 + taut * ‖z‖) :=
    norm_psqrt_le hrne hratio hbig
  rw [kappa2C, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hstep : ‖z‖ / c0 * ‖psqrt (oneSubIC taut z / oneSubIC tau z)‖
      ≤ ‖z‖ / c0 * (2 * (1 + taut * ‖z‖)) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  refine hstep.trans ?_
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc0]
  nlinarith [hz0, ht.le, sq_nonneg ‖z‖, mul_nonneg ht.le hz0]

/-- **Condition (i) of Definition 2.1 for the Nachman–Smith–Waag model.** -/
theorem kappa2_polyGrowth {c0 taut tau : ℝ} (hc0 : 0 < c0) (ht : 0 < taut)
    (htt : taut < tau) (n : ℕ) :
    ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ om : ℝ,
      ‖iteratedDeriv n (kappa2 c0 taut tau) om‖ ≤ C * (1 + |om|) ^ N := by
  have htau : 0 < tau := ht.trans htt
  set R : ℝ := 1 / (2 * tau) with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  have h2R : 2 * R = 1 / tau := by rw [hRdef]; field_simp
  have hdiff : DifferentiableOn ℂ (kappa2C c0 taut tau) {z : ℂ | -(2 * R) < z.im} := by
    intro z hz
    have hz' : -(1 / tau) < z.im := by rw [← h2R]; exact hz
    exact (kappa2C_differentiableAt_of_im ht htt hz').differentiableWithinAt
  have hbound : ∀ z : ℂ, -R ≤ z.im →
      ‖kappa2C c0 taut tau z‖ ≤ (2 * (1 + taut) / c0) * (1 + ‖z‖) ^ 2 := by
    intro z hz
    exact norm_kappa2C_le_of_im hc0 ht htt (by rw [← hRdef]; exact hz)
  have hM : (0 : ℝ) ≤ 2 * (1 + taut) / c0 := by positivity
  have hfun : kappa2 c0 taut tau = fun t : ℝ => kappa2C c0 taut tau (t : ℂ) := by
    funext t; rw [kappa2C_ofReal]
  refine ⟨((n.factorial : ℝ) * ((2 * (1 + taut) / c0) * (1 + R) ^ 2) / R ^ n) + 1,
    by positivity, 2, fun om => ?_⟩
  have hmain := polyGrowth_of_bounded hR hM hdiff hbound n om
  rw [hfun]
  refine hmain.trans ?_
  have hp : (0 : ℝ) < (1 + |om|) ^ 2 := by positivity
  nlinarith [hp]

end GSRT
