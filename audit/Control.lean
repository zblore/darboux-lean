/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DarbouxLean

/-!
# Controls

* The axiom audit would catch a `sorry`: `#print axioms` reports `sorryAx` for an unproved
  statement.
* The hypotheses can hold, so the theorem is not vacuous: in every dimension `2n`, the standard
  symplectic form, constant in `x`, is symplectic on the whole space.
* The conclusion is not trivial: the zero form on `ℝ²` is not in Darboux normal form.
-/

open LeanEval.Geometry.Darboux DarbouxLean

public theorem unproved : ∀ n : ℕ, Nonempty (Fin n) := by
  sorry

/-- info: 'unproved' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms unproved

/-- The standard symplectic form on `ℝ^{2n}`, in lean-eval's coordinates. -/
noncomputable def ω₀ (n : ℕ) : E n [⋀^Fin 2]→L[ℝ] ℝ :=
  (standardSymplecticForm (Fin n)).compContinuousLinearMap
    (coord n : E n →L[ℝ] (Fin n ⊕ Fin n → ℝ))

/-- The constant standard form is symplectic on the whole space. -/
theorem hypotheses_hold (n : ℕ) : IsSymplecticOn (fun _ : E n => ω₀ n) Set.univ := by
  refine ⟨contDiffOn_const, fun x _ => extDeriv_const_apply _ x, fun x _ v hv => ?_⟩
  have hTv : coord n v ≠ 0 := (map_ne_zero_iff _ (coord n).injective).2 hv
  obtain ⟨s, hs⟩ := Function.ne_iff.1 hTv
  rcases s with k | k
  · refine ⟨(coord n).symm (Pi.single (Sum.inr k) 1), ?_⟩
    simpa [ω₀, ContinuousAlternatingMap.compContinuousLinearMap_apply, Pi.single_apply]
      using hs
  · refine ⟨(coord n).symm (Pi.single (Sum.inl k) 1), ?_⟩
    simpa [ω₀, ContinuousAlternatingMap.compContinuousLinearMap_apply, Pi.single_apply]
      using hs

/-- The zero form is not in Darboux normal form. -/
theorem zero_not_normal : ¬ IsDarbouxNormal (0 : E 1 [⋀^Fin 2]→L[ℝ] ℝ) := by
  intro h
  have := h.1 0 0
  simp at this
