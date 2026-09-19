# Formal verification report

Machine-checked formalization, in Lean 4 with Mathlib, of statements made in

> *Reconstruction method based on Fourier series for attenuated photoacoustic
> tomography in a circular geometry.*

**This report states exactly what was and was not verified. Please read
section 3 before describing this work as "the paper was verified in Lean".**

---

## 0. How to reproduce

```
lake build                          # type-checks every proof
lake env lean AttenuatedPAT/Main.lean   # prints the axiom audit
```

Toolchain: `leanprover/lean4:v4.35.0-rc2`, Mathlib pinned at the same revision
(see `lake-manifest.json`).

Evidence files:

| File | What it shows |
| --- | --- |
| `AttenuatedPAT/*.lean` | the proofs themselves |
| `axioms.txt` | output of `#print axioms` for every headline theorem |
| `lake-manifest.json` | the exact Mathlib revision used |

There are **no `sorry`s and no `axiom` declarations** anywhere in this
development. Every theorem listed in section 1 depends only on Lean's three
standard axioms — `propext`, `Classical.choice`, `Quot.sound` — which is what
`axioms.txt` records. A `sorryAx` in any of those lists would mean the
corresponding statement is *not* proved.

---

## 1. What **is** verified

### 1.1 Zero-order Tikhonov regularization — `Tikhonov.lean`, `Spectral.lean`

Setting: linear maps between finite-dimensional complex inner product spaces,
which is exactly the setting of the paper's matrices `A_l`.

| Lean theorem | Paper statement |
| --- | --- |
| `tikhonovObj_eq_add` | `Q x = Q x₀ + ‖A(x−x₀)‖² + λ‖x−x₀‖²` for `x₀` solving the normal equation |
| `tikhonovObj_le_of_isNormalEqSolution` | a normal-equation solution minimizes the Tikhonov functional |
| `existsUnique_normalEqSolution` | for `λ > 0`, `(AᴴA + λI)x = Aᴴb` has exactly one solution |
| `existsUnique_tikhonov_minimizer` | "the unique solution of the normal equation" |
| `filterFactor_le` | `σ/(σ²+λ) ≤ 1/(2√λ)` |
| `cond_regularized_le` | `cond(AᴴA+λI) = (σ₁²+λ)/(σ_min²+λ) ≤ (σ₁²+λ)/λ` |
| `isNormalEqSolution_tikhonovSol` | the SVD formula `x^{(λ)} = Σ σⱼ/(σⱼ²+λ)(uⱼ*b)vⱼ` **is** the regularized solution |
| `norm_inner_tikhonovSol_le` | "small singular values are damped rather than amplified": every singular component obeys `‖⟪vᵢ,x⟫‖ ≤ ‖b‖/(2√λ)` |
| `exists_isSingularSystem` | a right singular system always exists (results are not vacuous) |

Mathlib has no SVD factorization theorem, so the right singular system is
carried as an orthonormal eigenbasis of `AᴴA`, and its existence is proved from
the spectral theorem.

### 1.2 The attenuation coefficients — `Attenuation.lean`, `AttenuationExt.lean`, `DerivGrowth.lean`

The principal branch of the square root is realized as `psqrt z = exp(log z / 2)`
and all branch facts used are proved (`psqrt_sq`, `psqrt_re_pos`, `psqrt_conj`,
`psqrt_differentiableAt`).

Thermoviscous `κ₁(ω) = ω/√(1−iτω)` and Nachman–Smith–Waag
`κ₂(ω) = (ω/c₀)√((1−iτ̃ω)/(1−iτω))`:

| Lean theorem | Paper statement |
| --- | --- |
| `kappa1_im_nonneg` | `Im κ₁(ω) ≥ 0` for `τ > 0` |
| `kappa2_im_nonneg` | "the condition `0 < τ̃ < τ` ensures `Im κ₂(ω) ≥ 0` for real ω" |
| `kappa1_symm`, `kappa2_symm` | Definition 2.1 (iii): `κ(−ω) = −conj κ(ω)` |
| `kappa1_ne_zero`, `kappa2_ne_zero` | "`κ(ω) ≠ 0` on `I_ω`" |
| `nsw_ratio_re_pos` | `0 < τ̃ < τ` keeps the NSW ratio off the branch cut |

**Definition 2.1 is verified for both models**, condition by condition:

| Condition of Definition 2.1 | Lean theorem | Status |
| --- | --- | --- |
| values in the closed upper half plane | `kappa1_im_nonneg`, `kappa2_im_nonneg` | ✅ |
| (i) polynomial growth of **every** derivative | `kappa1_polyGrowth`, `kappa2_polyGrowth` | ✅ |
| (ii) extension continuous on `Im z ≥ 0` | `kappa1C_continuousOn`, `kappa2C_continuousOn` | ✅ |
| (ii) extension maps `Im z ≥ 0` into itself | `kappa1C_im_nonneg`, `kappa2C_im_nonneg` | ✅ |
| (ii) extension restricts to `κ` on `ℝ` | `kappa1C_ofReal`, `kappa2C_ofReal` | ✅ |
| (ii) extension holomorphic on `Im z > 0` | `kappa1C_differentiableOn`, `kappa2C_differentiableOn` | ✅ |
| (ii) extension of polynomial growth | `norm_kappa1C_le`, `norm_kappa2C_le` | ✅ |
| (iii) symmetry | `kappa1_symm`, `kappa2_symm` | ✅ |

Condition (i) is obtained from Cauchy's estimate on discs of radius `1/(2τ)`
together with `iteratedDeriv_restrict`, which identifies the real iterated
derivatives of the restriction of a holomorphic function with its complex
iterated derivatives.

`IsAttenuationCoefficient` transcribes Definition 2.1 as a structure; its
elementary consequences (`re_zero`, odd real part, even imaginary part) are
proved.

### 1.3 Reality of the reconstruction — `AngularFourier.lean`

| Lean theorem | Paper statement |
| --- | --- |
| `synth_im_eq_zero` | a conjugate-symmetric coefficient family synthesizes to a real-valued function |
| `conjSymm_symmetrize` | Algorithm 1's step `x_l ← (x_l + conj x_{−l})/2` restores conjugate symmetry |
| `synth_symmetrize_im_eq_zero` | "so that the reconstruction is real-valued" |
| `symmetrize_zero` | at `l = 0` the step is exactly `x₀ ← Re x₀` (Algorithm 1, line 7) |
| `symmetrize_eq_self` | the step does nothing on an already symmetric family |
| `conj_fourierIntegral` | Hermitian symmetry in `ω` of the transform of a real record |

### 1.4 Angular orthogonality — `AngularFourier.lean`, `ContinuousFourier.lean`, `Radial.lean`

| Lean theorem | Paper statement |
| --- | --- |
| `integral_exp_int_mul_I` | `∫₀^{2π} e^{inθ}dθ = 2π` if `n = 0`, else `0` |
| `integral_synth_mul_exp` | extraction of the `l`-th angular Fourier coefficient |
| `sum_exp_two_pi_I` | discrete orthogonality `Σ_m e^{ikθ_m} = N·[N ∣ k]` on the sensor grid |
| `discrete_angular_extraction` | the trapezoidal angular sum is **exact** when `2L < N_θ` — this is why the paper requires `L_max < N_θ/2` and takes `L_max = N_θ/2 − 1` |
| `Aentry_neg` | `A_{−l} = A_l` (see the caveat in section 2) |

---

## 2. Caveat: one result is conditional

`Aentry_neg` (`A_{−l} = A_l`) is proved **relative to a hypothesis**.

Mathlib provides `Complex.besselJ` (merged 2026-09-15) and its parity
`besselJ_neg_int`, which supplies the Bessel factor. It provides **no Hankel
function of the first kind**. The one property of `H^{(1)}` that the argument
needs,

```
H^{(1)}_{−l}(z) = (−1)^l H^{(1)}_l(z),
```

is therefore carried as the field `HankelFirstKind.neg_order` of a structure,
not proved. So the verified statement is:

> *If* `H` is a family satisfying that parity relation, *then* `A_{−l} = A_l`.

The parity relation is a standard classical fact, but it is **not** machine-
checked here, because the object it is about does not exist in Mathlib.

---

## 3. What is **not** verified

Nothing below is assumed as a global `axiom`; it is simply outside the scope of
what was formalized.

### 3.1 The central derivation chain

The paper's mathematical core —

```
attenuated wave equation
  → Green function representation  −(i/4)H₀^{(1)}(κ|x−y|)
  → Graf's addition theorem
  → radial integral equation for the angular modes
```

— is **not verified**. It cannot currently be, because:

* Mathlib has Bessel `J` only. There is **no** Bessel `Y`, hence no
  `H^{(1)} = J + iY`. A survey of the mathlib4 repository found no pull request
  for either, open or merged.
* Graf's addition theorem needs Bessel integral representations or generating
  functions, both still listed as TODO in Mathlib's `Bessel.lean`.
* The Green function statement needs distributional fundamental solutions of the
  Helmholtz operator, which Mathlib does not have at the required depth.

What **is** verified is the *angular half* of that derivation: the orthogonality
and coefficient-extraction steps, in both continuous (`integral_synth_mul_exp`)
and discrete (`discrete_angular_extraction`) form.

### 3.2 Other unverified items

* **Compactness of `T_l`.** The paper's argument "continuous kernel ⟹
  Hilbert–Schmidt ⟹ compact". Mathlib has `IsCompactOperator` but no
  Hilbert–Schmidt integral operators.
* **The forward model**: the distributional solution of the attenuated wave
  equation, the definition of `W_κ`, the closed-form disk integral.
* **All numerical content**: the singular values and condition numbers of
  Table 2, the L-curve parameter selection, the MSE/PSNR/SSIM values of Table 4,
  and every figure. These are results of a particular floating-point
  computation, not theorems. Verifying them formally would require a verified
  interval-arithmetic stack able to certify singular values down to `10⁻³⁰⁶` of
  a `256 × 96` complex matrix; no such thing exists in Lean in practical form.

---

## 4. Suggested wording for the paper

Accurate:

> Auxiliary results of this paper — the regularization theory of Section 3.2,
> the properties of the attenuation coefficients of Section 4.1 including their
> membership in the class of Definition 2.1, the reality of the reconstruction
> produced by Algorithm 1, and the angular orthogonality relations — have been
> formally verified in Lean 4 with Mathlib. Graf's addition theorem and the
> Green function representation lie outside the scope of the formalization,
> because Hankel functions are not available in Mathlib; they are used here as
> cited literature results.

Not accurate: "this paper has been verified in Lean".
