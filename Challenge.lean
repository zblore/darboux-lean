module

public import Mathlib

/-!
# Darboux's theorem

Kim Morrison's statement of Darboux's theorem, the problem `darboux` of lean-eval
(`leanprover/lean-eval`, commit `85a88c37f80170d9f08651dc63ce6b81a8a48cb9`): the definitions of
`generated/darboux/ChallengeDeps.lean`, then the statement of `generated/darboux/Challenge.lean`.
lean-eval's text is Copyright 2026 Lean FRO, LLC, under the Apache License 2.0. Both files are
unchanged apart from the module header, `@[expose] public section`, moving the definitions into
this file, and one divergence: the bound proofs in `idxP` and `idxQ` are term proofs here, where
lean-eval uses `by have := i.isLt; omega`. `omega` leaves an auxiliary lemma that is private to
the module, so a copy of the definitions in another module is a different constant and Comparator
rejects the match. The term proofs leave none. Both versions give the same `Fin` values, so the
definitions say the same thing. The statement is the theorem `darboux` in the root namespace, as
in lean-eval's `Challenge.lean`.

lean-eval's own docstring below dates from May 2026. Its last sentence is out of date: Darboux's
theorem has since been proved in Lean in other statements (see `README.md`).
-/

@[expose] public section

namespace LeanEval
namespace Geometry
namespace Darboux

/-!
# Darboux's theorem

§39 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Every
symplectic form on an open `U ⊆ ℝ^{2n}` is locally symplectomorphic to the
standard symplectic form `ω₀ = ∑_{i=1}^n dxᵢ ∧ dx_{n+i}`.

The local content lives entirely on open subsets of `ℝ^{2n}`; we formalize
Darboux against mathlib's normed-space differential-form machinery.

mathlib has continuous alternating maps, the exterior derivative `extDeriv`,
pullbacks of alternating forms, `Matrix.symplecticGroup`, and
`OpenPartialHomeomorph`, but no symplectic forms, no `ω₀` value, and no
Darboux theorem (`Analysis/Calculus/Darboux.lean` is the unrelated
derivative-IVT theorem). No formalization of Darboux's theorem was found in
any other proof assistant.
-/

open Set Function Matrix
open scoped ContDiff

/-- The model space `ℝ^{2n}` for the local Darboux theorem. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

/-- The "p" coordinate index `i ∈ Fin n` viewed in `Fin (2n)`. -/
def idxP {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_left n Nat.two_pos)⟩

/-- The "q" coordinate index `i ∈ Fin n` viewed in `Fin (2n)`. -/
def idxQ {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val + n, Nat.lt_of_lt_of_eq (Nat.add_lt_add_right i.isLt n) (Nat.two_mul n).symm⟩

/-- A continuous alternating 2-form on `E n = ℝ^{2n}` is in **Darboux normal
form** if its values on the standard basis are the Liouville symplectic
values: `ω(eP_i, eQ_j) = δ_{ij}`, and `ω(eP_i, eP_j) = ω(eQ_i, eQ_j) = 0`.
By antisymmetry these conditions uniquely determine the form (it is the
standard symplectic form `ω₀ = ∑_i dxᵢ ∧ dx_{n+i}`). -/
def IsDarbouxNormal {n : ℕ} (α : E n [⋀^Fin 2]→L[ℝ] ℝ) : Prop :=
  (∀ i j : Fin n,
      α ![EuclideanSpace.single (idxP i) (1 : ℝ),
          EuclideanSpace.single (idxQ j) (1 : ℝ)]
        = if i = j then (1 : ℝ) else 0) ∧
  (∀ i j : Fin n,
      α ![EuclideanSpace.single (idxP i) (1 : ℝ),
          EuclideanSpace.single (idxP j) (1 : ℝ)] = 0) ∧
  (∀ i j : Fin n,
      α ![EuclideanSpace.single (idxQ i) (1 : ℝ),
          EuclideanSpace.single (idxQ j) (1 : ℝ)] = 0)

/-- A 2-form field `α` on an open set `U ⊆ ℝ^{2n}` is **symplectic** on `U`
if it is smooth on `U`, closed on `U` (`dα = 0`), and pointwise
non-degenerate. -/
def IsSymplecticOn {n : ℕ}
    (α : E n → E n [⋀^Fin 2]→L[ℝ] ℝ) (U : Set (E n)) : Prop :=
  ContDiffOn ℝ ∞ α U ∧
  (∀ x ∈ U, extDeriv α x = 0) ∧
  (∀ x ∈ U, ∀ v : E n, v ≠ 0 → ∃ w : E n, α x ![v, w] ≠ 0)



end Darboux
end Geometry
end LeanEval

open LeanEval.Geometry.Darboux
open Set Function Matrix
open scoped ContDiff

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
            (fderiv ℝ (φ.symm : E n → E n) z)) := by
  sorry
