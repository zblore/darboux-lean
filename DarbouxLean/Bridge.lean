/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DarbouxLean.Defs
public import DarbouxLean.Geometry.Manifold.DarbouxStandardForm

/-!
# From Darboux on a ball to lean-eval's statement

`exists_openPartialHomeomorph_pullback_standard` gives, for a closed form on a ball that is
non-degenerate at the centre, a chart `Ψ` into `Fin n ⊕ Fin n → ℝ` along which the form is the
pullback of the standard symplectic form `ω_std = ∑ᵢ dpᵢ ∧ dqᵢ`. lean-eval's statement wants a
local diffeomorphism `φ` of `ℝ^{2n} = EuclideanSpace ℝ (Fin (2 * n))` itself, with the pullback of
the form by `φ⁻¹` taking the standard values on the standard basis (`IsDarbouxNormal`).

The bridge is a change of coordinates. `coord n` reads a point of `ℝ^{2n}` as its `p`
coordinates (the first `n`, `idxP`) and its `q` coordinates (the last `n`, `idxQ`). Then
`φ = coord⁻¹ ∘ Ψ`, the derivative of `φ⁻¹ = Ψ⁻¹ ∘ coord` at `z` is `D⁻¹ ∘ coord` (the easy half of
the inverse function theorem), and the pullback of `α = ω_std ∘ D` along it is `ω_std ∘ coord`,
which takes the standard values on the standard basis (`isDarbouxNormal_coord`).
-/

@[expose] public section

open Set Function Matrix Metric Module
open scoped ContDiff

namespace DarbouxLean

open LeanEval.Geometry.Darboux

/-- The coordinates of `ℝ^{2n}`, listed as the `p`'s then the `q`'s. -/
def pq (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (two_mul n).symm)

theorem pq_inl {n : ℕ} (i : Fin n) : pq n (Sum.inl i) = idxP i := by
  ext
  simp [pq, idxP]

theorem pq_inr {n : ℕ} (i : Fin n) : pq n (Sum.inr i) = idxQ i := by
  ext
  simp [pq, idxQ, add_comm]

/-- `ℝ^{2n}` in `p, q` coordinates: `coord n y (inl i) = y (idxP i)` and
`coord n y (inr i) = y (idxQ i)`. -/
noncomputable def coord (n : ℕ) : E n ≃L[ℝ] (Fin n ⊕ Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    ((WithLp.linearEquiv 2 ℝ (Fin (2 * n) → ℝ)).trans (LinearEquiv.funCongrLeft ℝ ℝ (pq n)))

theorem coord_apply {n : ℕ} (y : E n) (s : Fin n ⊕ Fin n) : coord n y s = y (pq n s) := by
  simp [coord, LinearEquiv.funCongrLeft_apply]

theorem coord_single {n : ℕ} (k : Fin (2 * n)) (s : Fin n ⊕ Fin n) :
    coord n (EuclideanSpace.single k (1 : ℝ)) s = if pq n s = k then 1 else 0 := by
  rw [coord_apply]
  simp

theorem coord_single_idxP {n : ℕ} (i : Fin n) (s : Fin n ⊕ Fin n) :
    coord n (EuclideanSpace.single (idxP i) (1 : ℝ)) s = if s = Sum.inl i then 1 else 0 := by
  rw [coord_single, ← pq_inl]
  exact if_congr (pq n).apply_eq_iff_eq rfl rfl

theorem coord_single_idxQ {n : ℕ} (i : Fin n) (s : Fin n ⊕ Fin n) :
    coord n (EuclideanSpace.single (idxQ i) (1 : ℝ)) s = if s = Sum.inr i then 1 else 0 := by
  rw [coord_single, ← pq_inr]
  exact if_congr (pq n).apply_eq_iff_eq rfl rfl

/-- The standard symplectic form, read in the coordinates of `ℝ^{2n}`, takes the standard values
on the standard basis. -/
theorem isDarbouxNormal_coord (n : ℕ) :
    IsDarbouxNormal ((standardSymplecticForm (Fin n)).compContinuousLinearMap
      (coord n : E n →L[ℝ] (Fin n ⊕ Fin n → ℝ))) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩ <;>
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply, coord_single_idxP,
      coord_single_idxQ, eq_comm]

/-- **Darboux's theorem**, in lean-eval's form, from Darboux on a ball. -/
theorem darboux_of_ball {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    (α : E n → E n [⋀^Fin 2]→L[ℝ] ℝ) (hα : IsSymplecticOn α U)
    {x : E n} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (E n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → E n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : E n → E n) φ.target ∧
      ∀ z ∈ φ.target,
        IsDarbouxNormal
          ((α (φ.symm z)).compContinuousLinearMap
            (fderiv ℝ (φ.symm : E n → E n) z)) := by
  obtain ⟨hsm, hcl, hnd⟩ := hα
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨m, Ψ, hm, hsub, hx₀, hΨ, hΨs, hD⟩ :=
    exists_openPartialHomeomorph_pullback_standard (k := ⊤) le_top
      (hsm.mono hRU) hR (fun y hy => hcl y (hRU hy)) (hnd x hx)
  have hmn : m = n := by
    rw [finrank_euclideanSpace_fin] at hm
    omega
  subst hmn
  set T := coord m
  set φ : OpenPartialHomeomorph (E m) (E m) :=
    Ψ.trans T.symm.toHomeomorph.toOpenPartialHomeomorph with hφ
  have hφsrc : φ.source = Ψ.source := by
    rw [hφ, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ]
  have hφc : (⇑φ : E m → E m) = ⇑T.symm ∘ ⇑Ψ := by
    rw [hφ, OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph]
  have hφs : (⇑φ.symm : E m → E m) = ⇑Ψ.symm ∘ ⇑T := by
    funext z
    rfl
  have hφt : ∀ z ∈ φ.target, T z ∈ Ψ.target := by
    intro z hz
    rw [hφ, OpenPartialHomeomorph.trans_target] at hz
    exact hz.2
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφsrc]
    exact hx₀
  · rw [hφsrc]
    exact hsub.trans hRU
  · rw [hφsrc, hφc]
    exact T.symm.contDiff.contDiffOn.comp hΨ (mapsTo_univ _ _)
  · rw [hφs]
    exact hΨs.comp T.contDiff.contDiffOn fun z hz => hφt z hz
  · intro z hz
    have hTz := hφt z hz
    have hy : Ψ.symm (T z) ∈ Ψ.source := Ψ.map_target hTz
    obtain ⟨D, hDf, hDp⟩ := hD _ hy
    have hsymm : HasFDerivAt Ψ.symm (D.symm : _ →L[ℝ] E m) (T z) := Ψ.hasFDerivAt_symm hTz hDf
    have hder : HasFDerivAt (⇑φ.symm : E m → E m)
        ((D.symm : (Fin m ⊕ Fin m → ℝ) →L[ℝ] E m).comp
          (T : E m →L[ℝ] (Fin m ⊕ Fin m → ℝ))) z := by
      rw [hφs]
      exact hsymm.comp z (T : E m →L[ℝ] (Fin m ⊕ Fin m → ℝ)).hasFDerivAt
    have hpt : φ.symm z = Ψ.symm (T z) := by rw [hφs, Function.comp_apply]
    have key : (α (φ.symm z)).compContinuousLinearMap (fderiv ℝ (φ.symm : E m → E m) z) =
        (standardSymplecticForm (Fin m)).compContinuousLinearMap
          (T : E m →L[ℝ] (Fin m ⊕ Fin m → ℝ)) := by
      rw [hder.fderiv, hpt, hDp]
      ext v
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
    rw [key]
    exact isDarbouxNormal_coord m

end DarbouxLean

open LeanEval.Geometry.Darboux
open Set Function Matrix
open scoped ContDiff

/-- **Darboux's theorem**, lean-eval's statement `darboux`, under its name. -/
theorem darboux {n : ℕ} {U : Set (E n)} (_hU : IsOpen U)
    (α : E n → E n [⋀^Fin 2]→L[ℝ] ℝ) (_hα : IsSymplecticOn α U)
    {x : E n} (_hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (E n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → E n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : E n → E n) φ.target ∧
      ∀ z ∈ φ.target,
        IsDarbouxNormal
          ((α (φ.symm z)).compContinuousLinearMap
            (fderiv ℝ (φ.symm : E n → E n) z)) :=
  DarbouxLean.darboux_of_ball _hU α _hα _hx
