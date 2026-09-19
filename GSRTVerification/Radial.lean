/-
Formal verification of the radial systems of
"Reconstruction method based on Fourier series for attenuated photoacoustic
tomography in a circular geometry", Section 3.2 and Section 4.2.
-/
import GSRTVerification.Prelude
import GSRTVerification.AngularFourier

/-!
# The discrete radial systems `A_l`

* `GSRT.discrete_angular_extraction` : the trapezoidal sum (17) recovers the
  angular Fourier coefficients of a band limited boundary trace exactly,
  provided `2 L < N_θ`.  This is the reason for the paper's condition
  `L_max < N_θ / 2` and for the choice `L_max = N_θ / 2 - 1` in Table 1.
* `GSRT.Aentry_neg` : `A_{-l} = A_l`, the identity that lets Section 4.2 restrict
  the conditioning study to `l ≥ 0`.

Mathlib provides the Bessel function of the first kind `Complex.besselJ` and its
parity `Complex.besselJ_neg_int`.  It does not provide the Hankel function of the
first kind, so the single property of `H^{(1)}` that the argument uses, namely
`H^{(1)}_{-l} = (-1)^l H^{(1)}_l`, is carried explicitly as the field
`GSRT.HankelFirstKind.neg_order` rather than assumed globally: every statement
below is conditional on it.
-/

namespace GSRT

open Complex

/-! ### Exact recovery of the angular coefficients on the sensor grid -/

/-- The `m`-th sensor angle `θ_m = 2π m / N_θ` of formula (13). -/
noncomputable def sensorAngle (N m : ℕ) : ℝ := 2 * Real.pi * m / N

/-- **Exactness of the discrete angular transform.**  If the boundary trace is
an angular trigonometric polynomial of degree at most `L` and `2 L < N`, the
trapezoidal sum over the `N` sensors returns `N` times the `l`-th angular
Fourier coefficient, for every `|l| ≤ L`.  Aliasing is exactly what the
condition `2 L < N` excludes. -/
theorem discrete_angular_extraction (N L : ℕ) (hN : 0 < N) (hL : 2 * L < N)
    (c : ℤ → ℂ) (l : ℤ) (hl : l ∈ Finset.Icc (-(L : ℤ)) (L : ℤ)) :
    ∑ m ∈ Finset.range N,
        synth L c (sensorAngle N m) *
          Complex.exp (-((l : ℂ) * ((sensorAngle N m : ℝ) : ℂ) * Complex.I))
      = (N : ℂ) * c l := by
  simp only [synth, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      ∑ m ∈ Finset.range N,
          c j * Complex.exp ((j : ℂ) * ((sensorAngle N m : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-((l : ℂ) * ((sensorAngle N m : ℝ) : ℂ) * Complex.I))
        = c j * (if (N : ℤ) ∣ (j - l) then (N : ℂ) else 0) := by
    intro j _
    have hstep : ∀ m ∈ Finset.range N,
        c j * Complex.exp ((j : ℂ) * ((sensorAngle N m : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-((l : ℂ) * ((sensorAngle N m : ℝ) : ℂ) * Complex.I))
          = c j * Complex.exp (((j - l : ℤ) : ℂ) *
              (2 * Real.pi * (m : ℂ) / (N : ℂ)) * Complex.I) := by
      intro m _
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      simp only [sensorAngle]
      push_cast
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, sum_exp_two_pi_I N hN (j - l)]
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_eq_single l]
  · simp [mul_comm]
  · intro j hj hjl
    have hjmem := Finset.mem_Icc.mp hj
    have hlmem := Finset.mem_Icc.mp hl
    have hne : j - l ≠ 0 := sub_ne_zero.mpr hjl
    have hnd : ¬ ((N : ℤ) ∣ (j - l)) := fun hdvd =>
      hne (Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega))
    simp [hnd]
  · intro hl'
    exact absurd hl hl'

/-! ### The matrices `A_l` -/

/-- The data of the Hankel function of the first kind that the paper's argument
uses.  Mathlib has no Hankel functions, so the parity relation
`H^{(1)}_{-l} = (-1)^l H^{(1)}_l` is carried as a hypothesis. -/
structure HankelFirstKind where
  /-- The family `H^{(1)}_l`. -/
  H : ℤ → ℂ → ℂ
  /-- `H^{(1)}_{-l} = (-1)^l H^{(1)}_l`. -/
  neg_order : ∀ (l : ℤ) (z : ℂ), H (-l) z = (-1 : ℂ) ^ l * H l z

/-- The entry `(A_l)_{αβ}` of formula (20). -/
noncomputable def Aentry (hk : HankelFirstKind) (kap : ℝ → ℂ) (l : ℤ) (om r dr : ℝ) : ℂ :=
  ((om * Real.pi / 2 : ℝ) : ℂ) * hk.H l (kap om) *
    Complex.besselJ ((l : ℤ) : ℂ) ((r : ℂ) * kap om) * (r : ℂ) * (dr : ℂ)

/-- **`A_{-l} = A_l`.**  Both the Hankel and the Bessel factor pick up the same
sign `(-1)^l`, and the two cancel.  This is the identity used in Section 4.2 to
restrict the conditioning study to `l ≥ 0`. -/
theorem Aentry_neg (hk : HankelFirstKind) (kap : ℝ → ℂ) (l : ℤ) (om r dr : ℝ) :
    Aentry hk kap (-l) om r dr = Aentry hk kap l om r dr := by
  have hsign : ((-1 : ℂ) ^ l) * ((-1 : ℂ) ^ l) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), show l + l = 2 * l by ring, zpow_mul]
    norm_num
  have hcast : ((-l : ℤ) : ℂ) = -((l : ℤ) : ℂ) := by push_cast; ring
  rw [Aentry, Aentry, hk.neg_order, hcast, Complex.besselJ_neg_int]
  linear_combination (((om * Real.pi / 2 : ℝ) : ℂ) * hk.H l (kap om) *
    Complex.besselJ ((l : ℤ) : ℂ) ((r : ℂ) * kap om) * (r : ℂ) * (dr : ℂ)) * hsign

end GSRT
