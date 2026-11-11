/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DarbouxLean.Geometry.Manifold.VectorBundle.AlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Differential forms on a manifold

*Provenance:* copied from csd-lean4 (`zblore/csd-lean4`, commit `8b99f249`), file
`CsdLean4/Mathlib/Geometry/Manifold/DifferentialForm.lean`,
with imports renamed from `CsdLean4.Mathlib` to `DarbouxLean`. The code is unchanged. The
comments were edited for this repository to remove csd-lean4's internal notes and anything that
was out of date here.

A differential form on a manifold is a smooth section of the bundle of alternating maps on the
tangent bundle. The ingredient that makes "smooth" mean anything is the `ContMDiffVectorBundle`
instance for the alternating-map bundle, built in `VectorBundle/AlternatingMap.lean` on top of
the pullback analyticity in `Analysis/Normed/Module/Alternating/Pullback.lean`.

* `DifferentialForm` — the type: a `C^n` section of `x ↦ TₓM [⋀^ι]→L[𝕜] G`.

This module defines the type only. The exterior derivative is `ExteriorDerivative.lean`, and
symplectic forms are `SymplecticForm.lean`.

References: `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (the flat case).
-/

@[expose] public section

open Bundle
open scoped Manifold Bundle Topology ContDiff

section

variable {𝕜 EM HM : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]

/-- **A `C^n` differential form** of degree `ι` on `M`, valued in `G`: a `C^n` section of the
bundle whose fibre at `x` is the continuous alternating maps `(TₓM)^ι → G`.

Explicit arguments in the order `DifferentialForm IM M n ι G`. -/
abbrev DifferentialForm (IM : ModelWithCorners 𝕜 EM HM) (M : Type*) [TopologicalSpace M]
    [ChartedSpace HM M] [IsManifold IM 1 M] (n : WithTop ℕ∞) (ι : Type*) [Fintype ι]
    (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] :=
  ContMDiffSection IM (EM [⋀^ι]→L[𝕜] G) n
    (fun x : M => TangentSpace IM x [⋀^ι]→L[𝕜] Bundle.Trivial M G x)

end
