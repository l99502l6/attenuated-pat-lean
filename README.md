# GSRTVerification

A Lean 4 / Mathlib formalization of mathematical statements made in

> *Reconstruction method based on Fourier series for attenuated photoacoustic
> tomography in a circular geometry.*

**Read [`VERIFICATION.md`](VERIFICATION.md) for what is and is not verified.**
The paper as a whole is *not* verified; a specific list of its claims is.

## Status

| | |
| --- | --- |
| Build | `lake build` succeeds, 9 modules |
| `sorry` / `axiom` declarations | none |
| Theorems audited | 52 |
| Axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` only — see `axioms.txt` |

## Build

```bash
lake build
lake env lean GSRTVerification/Main.lean > axioms.txt
```

Every line of `axioms.txt` must read
`'...' depends on axioms: [propext, Classical.choice, Quot.sound]`.
A `sorryAx` in any line would mean that statement is not proved.

Toolchain `leanprover/lean4:v4.35.0-rc2`; the exact Mathlib revision is pinned in
`lake-manifest.json`.

### A note on imports

`GSRTVerification/Prelude.lean` imports only the parts of Mathlib that are used,
and every other module imports it. This is deliberate: `import Mathlib` loads
roughly 5 GB of `.olean` files, and on a machine with less RAM than that every
elaboration re-reads them from disk, which pushed per-file compile times from
minutes to over half an hour. Do not replace it with `import Mathlib`.

## Layout

| Module | Contents |
| --- | --- |
| `Prelude.lean` | curated Mathlib imports |
| `Attenuation.lean` | principal square root, `κ₁`, `κ₂`, Definition 2.1 |
| `AttenuationExt.lean` | Definition 2.1 (ii): the holomorphic extensions |
| `DerivGrowth.lean` | Definition 2.1 (i): polynomial growth of all derivatives |
| `AngularFourier.lean` | reality of the reconstruction, Algorithm 1's symmetrisation, discrete orthogonality |
| `ContinuousFourier.lean` | continuous angular orthogonality and coefficient extraction |
| `Radial.lean` | exactness of the discrete angular transform, `A_{-l} = A_l` |
| `Tikhonov.lean` | regularization: existence, uniqueness, filter and conditioning bounds |
| `Spectral.lean` | the singular value form of the regularized solution and its damping bound |
| `Main.lean` | axiom audit (`#print axioms`) |
