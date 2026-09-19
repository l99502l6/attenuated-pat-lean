-- tactics
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.FunProp

-- complex analysis
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

-- Bessel functions
import Mathlib.Analysis.SpecialFunctions.Bessel

-- inner product spaces, adjoints, spectral theorem
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum

-- integration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Prelude

Every module of this development imports this file instead of all of `Mathlib`.

`import Mathlib` pulls in roughly 5 GB of `.olean` files.  On a machine whose
RAM is smaller than that, every elaboration re-reads them from disk, which makes
each file take tens of minutes.  Importing only the parts that are actually used
keeps the working set small enough to stay in the page cache.
-/
