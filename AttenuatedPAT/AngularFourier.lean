/-
Formal verification of the angular Fourier series steps of
"Reconstruction method based on Fourier series for attenuated photoacoustic
tomography in a circular geometry", Section 3 and Algorithm 1.
-/
import AttenuatedPAT.Prelude

/-!
# Angular Fourier series, symmetrisation and orthogonality

The reconstruction is synthesised from angular Fourier coefficients by
formula (22) of the paper,
`f_rec(r, φ) = (2π)^{-1/2} ∑_{|l| ≤ L} f_l(r) e^{i l φ}`.
The paper observes that the separately computed coefficients
`x_l^{(λ)}` need not satisfy `x_{-l} = conj x_l`, and therefore replaces them by
`(x_l + conj x_{-l}) / 2` before interpolating, "so that the reconstruction
(22) is real-valued".  This file verifies exactly that chain of statements.

* `GSRT.ConjSymm` : the conjugate symmetry `y (-l) = conj (y l)` satisfied by
  the angular coefficients of a real-valued function.
* `GSRT.synth_im_eq_zero` : a conjugate symmetric family synthesises to a
  real-valued function.
* `GSRT.conjSymm_symmetrize`, `GSRT.synth_symmetrize_im_eq_zero` : Algorithm 1's
  symmetrisation step produces a conjugate symmetric family, hence a
  real-valued reconstruction.
* `GSRT.symmetrize_zero`, `GSRT.symmetrize_eq_self` : the step reduces to
  `x₀ ← Re x₀` at `l = 0` and does nothing on already symmetric families.
* `GSRT.sum_exp_two_pi_I` : the discrete angular orthogonality relation behind
  the trapezoidal formula (17) for `b_{l,α}`.
* `GSRT.conj_fourierIntegral` : Hermitian symmetry in `ω` of the temporal
  Fourier transform of a real-valued record, used in Section 4.1 to extend the
  data to negative frequencies.
-/

namespace GSRT

open Complex

/-! ### Conjugate symmetric families and the angular synthesis -/

/-- The conjugate symmetry `y (-l) = conj (y l)` satisfied by the angular
Fourier coefficients of a real-valued function. -/
def ConjSymm (y : ℤ → ℂ) : Prop := ∀ l : ℤ, y (-l) = (starRingEnd ℂ) (y l)

/-- The truncated angular synthesis `φ ↦ ∑_{|l| ≤ L} y l * e^{i l φ}`.  The
normalising factor `(2π)^{-1/2}` of formula (22) is a positive real constant and
is irrelevant for the reality statements below, so it is omitted. -/
noncomputable def synth (L : ℕ) (y : ℤ → ℂ) (phi : ℝ) : ℂ :=
  ∑ l ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), y l * Complex.exp ((l : ℂ) * (phi : ℂ) * Complex.I)

theorem conj_exp_mul_I (l : ℤ) (phi : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((l : ℂ) * (phi : ℂ) * Complex.I))
      = Complex.exp (((-l : ℤ) : ℂ) * (phi : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp

/-- **A conjugate symmetric family synthesises to a real-valued function.** -/
theorem synth_im_eq_zero (L : ℕ) {y : ℤ → ℂ} (h : ConjSymm y) (phi : ℝ) :
    (synth L y phi).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  rw [synth, map_sum]
  refine Finset.sum_equiv (Equiv.neg ℤ) (fun l => ?_) (fun l hl => ?_)
  · simp only [Equiv.neg_apply, Finset.mem_Icc]
    omega
  · simp only [Equiv.neg_apply, map_mul]
    rw [conj_exp_mul_I l phi, ← h l]

/-! ### The symmetrisation step of Algorithm 1 -/

/-- The symmetrisation of Algorithm 1: `x_l ↦ (x_l + conj x_{-l}) / 2`. -/
noncomputable def symmetrize (x : ℤ → ℂ) : ℤ → ℂ :=
  fun l => (x l + (starRingEnd ℂ) (x (-l))) / 2

/-- **The symmetrised family is conjugate symmetric.** -/
theorem conjSymm_symmetrize (x : ℤ → ℂ) : ConjSymm (symmetrize x) := by
  intro l
  simp only [symmetrize, neg_neg, map_div₀, map_add, Complex.conj_conj]
  rw [show (starRingEnd ℂ) 2 = 2 by simp [Complex.ext_iff]]
  ring

/-- **Algorithm 1 produces a real-valued reconstruction.** -/
theorem synth_symmetrize_im_eq_zero (L : ℕ) (x : ℤ → ℂ) (phi : ℝ) :
    (synth L (symmetrize x) phi).im = 0 :=
  synth_im_eq_zero L (conjSymm_symmetrize x) phi

/-- At `l = 0` the symmetrisation is the step `x₀ ← Re x₀` of Algorithm 1. -/
theorem symmetrize_zero (x : ℤ → ℂ) : symmetrize x 0 = ((x 0).re : ℂ) := by
  simp only [symmetrize, neg_zero]
  rw [Complex.add_conj]
  push_cast
  ring

/-- The symmetrisation does nothing on an already conjugate symmetric family. -/
theorem symmetrize_eq_self {x : ℤ → ℂ} (h : ConjSymm x) : symmetrize x = x := by
  funext l
  have hl : (starRingEnd ℂ) (x (-l)) = x l := by
    rw [h l, Complex.conj_conj]
  rw [symmetrize, hl]
  ring

/-! ### Discrete angular orthogonality -/

/-- **Discrete orthogonality of the angular exponentials.**  For `N` uniformly
distributed sensor angles `θ_m = 2π m / N`, the sum `∑_m e^{i k θ_m}` equals `N`
when `N ∣ k` and vanishes otherwise.  This is what makes the trapezoidal sum
(17) reproduce the angular Fourier coefficients for `|l| < N / 2`. -/
theorem sum_exp_two_pi_I (N : ℕ) (hN : 0 < N) (k : ℤ) :
    ∑ m ∈ Finset.range N,
        Complex.exp ((k : ℂ) * (2 * Real.pi * (m : ℂ) / (N : ℂ)) * Complex.I)
      = if (N : ℤ) ∣ k then (N : ℂ) else 0 := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set z : ℂ := Complex.exp ((k : ℂ) * (2 * Real.pi / (N : ℂ)) * Complex.I) with hz
  have hterm : ∀ m ∈ Finset.range N,
      Complex.exp ((k : ℂ) * (2 * Real.pi * (m : ℂ) / (N : ℂ)) * Complex.I) = z ^ m := by
    intro m _
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hzN : z ^ N = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    rw [show (N : ℂ) * ((k : ℂ) * (2 * Real.pi / (N : ℂ)) * Complex.I)
        = (k : ℂ) * (2 * Real.pi * Complex.I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I k
  by_cases hdvd : (N : ℤ) ∣ k
  · have hz1 : z = 1 := by
      have hk : (k : ℂ) * (2 * Real.pi / (N : ℂ)) * Complex.I
          = ((k / (N : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        have hkc : (k : ℂ) = ((N : ℤ) : ℂ) * ((k / (N : ℤ) : ℤ) : ℂ) := by
          have hint : k = (N : ℤ) * (k / (N : ℤ)) := (Int.mul_ediv_cancel' hdvd).symm
          exact_mod_cast congrArg (fun t : ℤ => (t : ℂ)) hint
        rw [hkc]
        push_cast
        field_simp
      rw [hz, hk]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [hz1, hdvd]
  · have hz1 : z ≠ 1 := by
      intro hone
      rw [hz, Complex.exp_eq_one_iff] at hone
      obtain ⟨n, hn⟩ := hone
      apply hdvd
      have hfac : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hk : (k : ℂ) / (N : ℂ) = (n : ℂ) := by
        refine mul_right_cancel₀ hfac ?_
        rw [← hn]
        ring
      have hk2 : (k : ℂ) = (N : ℂ) * (n : ℂ) := by
        field_simp at hk
        linear_combination hk
      exact ⟨n, by exact_mod_cast hk2⟩
    rw [geom_sum_eq hz1, hzN, sub_self, zero_div]
    simp [hdvd]

/-! ### Hermitian symmetry of the frequency domain data -/

/-- **Hermitian symmetry.**  The temporal Fourier transform
`ω ↦ ∫ h t * e^{i ω t}` of a real-valued record `h` satisfies
`conj (ĥ ω) = ĥ (-ω)`, which is the relation used in Section 4.1 to extend the
positive frequency data to negative frequencies. -/
theorem conj_fourierIntegral (h : ℝ → ℝ) (om : ℝ) :
    (starRingEnd ℂ) (∫ t : ℝ, (h t : ℂ) * Complex.exp ((om : ℂ) * (t : ℂ) * Complex.I))
      = ∫ t : ℝ, (h t : ℂ) * Complex.exp (((-om : ℝ) : ℂ) * (t : ℂ) * Complex.I) := by
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  push_cast
  simp

end GSRT
