/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DarbouxLean.Geometry.Manifold.ExteriorDerivative

/-!
# Symplectic forms on a manifold

*Provenance:* copied from csd-lean4 (`zblore/csd-lean4`, commit `8b99f249`), file
`CsdLean4/Mathlib/Geometry/Manifold/SymplecticForm.lean`,
with imports renamed from `CsdLean4.Mathlib` to `DarbouxLean`. The code is unchanged. The
comments were edited for this repository to remove csd-lean4's internal notes and anything that
was out of date here.

With differential forms (`DifferentialForm.lean`) and their exterior derivative
(`ExteriorDerivative.lean`), "a symplectic form on `M`" can be written down:

* `DifferentialForm.IsSymplectic α` — a `C^∞` 2-form `α` on a real boundaryless manifold is
  **symplectic** when it is **closed** (`α.mextDeriv = 0`) and **non-degenerate at every point**
  (for every nonzero tangent vector `v` some `w` has `α x (v, w) ≠ 0`).

This module states the predicate only. Darboux's theorem for it is
`Geometry/Manifold/Darboux.lean` and `Geometry/Manifold/DarbouxStandardForm.lean`.

Non-degeneracy is the finite-dimensional reading: "`v ≠ 0 → ∃ w, α x (v, w) ≠ 0`" is weak
non-degeneracy in general; for finite-dimensional real manifolds it is the usual condition.
`∞` and `𝓘(ℝ, E)` only, inherited from `ExteriorDerivative.lean`.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]

/-- **A symplectic form**: a `C^∞` 2-form that is closed and non-degenerate at every point. -/
structure IsSymplectic (α : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 2) ℝ) :
    Prop where
  /-- Closedness: `d α = 0`. -/
  closed : α.mextDeriv = 0
  /-- Non-degeneracy at every point: every nonzero tangent vector pairs non-trivially with some
  other. -/
  nondegenerate : ∀ (x : M) (v : TangentSpace (𝓘(ℝ, E)) x), v ≠ 0 →
    ∃ w, α x ![v, w] ≠ 0

end DifferentialForm
