/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# The pullback of a continuous alternating map is jointly analytic

*Provenance:* copied from csd-lean4 (`zblore/csd-lean4`, commit `8b99f249`), file
`CsdLean4/Mathlib/Analysis/Normed/Module/Alternating/Pullback.lean`,
with imports renamed from `CsdLean4.Mathlib` to `DarbouxLean`. The code is unchanged. The
comments were edited for this repository to remove csd-lean4's internal notes and anything that
was out of date here.

Differential forms on a manifold, as smooth sections, need a `ContMDiffVectorBundle` instance for
the alternating-map bundle, whose crux is smoothness of the coordinate change. That reduces to
smoothness of the **pullback** `(g, ω) ↦ ω ∘ g` in both arguments jointly.

When this was written, Mathlib had that for the **multilinear** pullback
(`ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap`,
`Analysis/Analytic/CPolynomial.lean`) and, for the **alternating** one, only continuity and the
first derivative (`Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`). The obvious reduction
fails: the alternating pullback is the diagonal restriction of the multilinear one (degree
`card ι` in `g`, not linear), so it is not itself a continuous multilinear map.

**What unlocks it is a left inverse.** Alternatization sends a continuous multilinear map to a
continuous alternating one, and on an already-alternating map it multiplies by `(card ι)!`, so in
characteristic zero it is a continuous linear **retraction** of the inclusion. Analyticity then
reflects: the alternating pullback is that retraction applied to the multilinear pullback of the
inclusion, along the diagonal.

* `ContinuousMultilinearMap.continuous_alternatization` and
  ★ `ContinuousMultilinearMap.alternatizationCLM` — alternatization as a **continuous linear
  map** (Mathlib has it as an `AddMonoidHom`, `ContinuousMultilinearMap.alternatization`);
* `alternatizationCLM_of_alternating` — on an alternating map it is `(card ι)!`;
* `compContinuousLinearMap_eq_smul_alternatization` — the pullback written through the
  retraction, which is the whole idea in one equation;
* ★★ `ContinuousAlternatingMap.analyticAt_uncurry_compContinuousLinearMap` — the pullback is
  jointly analytic, and
* ★ `contDiffAt_uncurry_compContinuousLinearMap` / `contDiff_uncurry_compContinuousLinearMap`
  — the `ContDiff` corollaries, the form `Geometry/Manifold/VectorBundle/AlternatingMap.lean`
  uses;
* `ContinuousAlternatingMap.compContinuousLinearMap_apply_pair` — the degree-`2` evaluation
  `(ω ∘ L) ⦃a, b⦄ = ω ⦃L a, L b⦄`, which is how a pulled-back `2`-form is read off a pair of
  tangent vectors.

Characteristic zero is essential: the retraction divides by `(card ι)!`. `contDiffAt_…` needs
`[CompleteSpace G]`, inherited from `AnalyticAt.contDiffAt`; the analyticity statement does not.

References: `Mathlib/Analysis/Analytic/CPolynomial.lean` (the multilinear twin this reflects
from); `Mathlib/Topology/Algebra/Module/Alternating/Basic.lean` (`alternatization`).
-/

@[expose] public section

open ContinuousAlternatingMap

namespace ContinuousMultilinearMap

variable {𝕜 ι M N : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N]

/-- Alternatization is continuous: it is a finite signed sum of index permutations, and the
topology on the alternating maps is induced from the multilinear ones. -/
lemma continuous_alternatization :
    Continuous (alternatization :
      ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N → (M [⋀^ι]→L[𝕜] N)) := by
  refine isUniformEmbedding_toContinuousMultilinearMap.isInducing.continuous_iff.2 ?_
  simp only [Function.comp_def]
  have h : (fun f : ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N =>
        (alternatization f).toContinuousMultilinearMap)
      = fun f => ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℤ) • f.domDomCongr σ := by
    funext f
    rw [alternatization_apply_toContinuousMultilinearMap]
    exact Finset.sum_congr rfl fun σ _ => by rw [Units.smul_def]
  rw [h]
  refine continuous_finsetSum _ fun σ _ => Continuous.const_smul ?_ _
  exact (domDomCongrₗᵢ 𝕜 M N σ).continuous

/-- ★ **Alternatization as a continuous linear map.** Upstream has this only as an
`AddMonoidHom`; the scalar action and the continuity are what make it usable as a
retraction. -/
noncomputable def alternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N →L[𝕜] (M [⋀^ι]→L[𝕜] N) where
  toFun := alternatization
  map_add' f g := map_add alternatization f g
  map_smul' c f := by
    ext v
    have hl : alternatization (c • f) v
        = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • c • f (v ∘ (σ : Equiv.Perm ι)) := by
      simp [alternatization_apply_apply]
    have hr : (c • alternatization f) v
        = c • ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ (σ : Equiv.Perm ι)) := by
      simp [alternatization_apply_apply]
    rw [RingHom.id_apply, hl, hr, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => smul_comm _ _ _
  cont := continuous_alternatization

end ContinuousMultilinearMap

namespace ContinuousMultilinearMap
variable {𝕜 ι M N : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N]

/-- Alternatizing something already alternating multiplies it by `(card ι)!` — so in
characteristic zero `alternatizationCLM` is a continuous linear **retraction** of the
inclusion of alternating maps into multilinear ones. -/
theorem alternatizationCLM_of_alternating (ω : M [⋀^ι]→L[𝕜] N) :
    alternatizationCLM (ω.toContinuousMultilinearMap) = (Fintype.card ι).factorial • ω := by
  ext v
  simp only [alternatizationCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, alternatization_apply_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.coe_toContinuousMultilinearMap]
  have hperm : ∀ σ : Equiv.Perm ι, ω (v ∘ σ) = Equiv.Perm.sign σ • ω v := by
    intro σ
    simpa using ω.toAlternatingMap.map_perm v σ
  rw [Finset.sum_congr rfl (fun σ _ => by
    rw [hperm σ, smul_smul, Int.units_mul_self, one_smul])]
  simp [Finset.card_univ, Fintype.card_perm]

end ContinuousMultilinearMap

namespace ContinuousAlternatingMap
open ContinuousMultilinearMap
variable {𝕜 ι E F G : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CharZero 𝕜]

/-- **The idea, in one equation.** The pullback of an alternating map is the retraction
applied to the pullback of its inclusion — so anything true of the multilinear pullback and
stable under continuous linear maps transfers. -/
theorem compContinuousLinearMap_eq_smul_alternatization (g : E →L[𝕜] F) (ω : F [⋀^ι]→L[𝕜] G) :
    ω.compContinuousLinearMap g
      = ((Fintype.card ι).factorial : 𝕜)⁻¹ •
          alternatizationCLM
            (ω.toContinuousMultilinearMap.compContinuousLinearMap (fun _ => g)) := by
  have hfac : ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h : ω.toContinuousMultilinearMap.compContinuousLinearMap (fun _ => g)
      = (ω.compContinuousLinearMap g).toContinuousMultilinearMap := rfl
  rw [h, alternatizationCLM_of_alternating, ← Nat.cast_smul_eq_nsmul 𝕜,
    inv_smul_smul₀ hfac]

/-- The bundled linear reindexing used in the analyticity proof. -/
noncomputable def pullbackPairCLM :
    ((E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G)) →L[𝕜]
      (((i : ι) → E →L[𝕜] F) × ContinuousMultilinearMap 𝕜 (fun _ : ι => F) G) :=
  (ContinuousLinearMap.pi fun _ : ι =>
      ContinuousLinearMap.fst 𝕜 (E →L[𝕜] F) (F [⋀^ι]→L[𝕜] G)).prod
    ((toContinuousMultilinearMapCLM 𝕜).comp
      (ContinuousLinearMap.snd 𝕜 (E →L[𝕜] F) (F [⋀^ι]→L[𝕜] G)))

/-- ★ **The missing lemma.** The pullback of a continuous alternating map along a continuous
linear map is **analytic in both arguments jointly**. -/
theorem analyticAt_uncurry_compContinuousLinearMap
    (q : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G)) :
    AnalyticAt 𝕜
      (fun p : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G) => p.2.compContinuousLinearMap p.1) q := by
  have key : (fun p : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G) => p.2.compContinuousLinearMap p.1)
      = fun p => (((Fintype.card ι).factorial : 𝕜)⁻¹ • alternatizationCLM)
            ((pullbackPairCLM p).2.compContinuousLinearMap (pullbackPairCLM p).1) := by
    funext p
    rw [compContinuousLinearMap_eq_smul_alternatization p.1 p.2]
    rfl
  rw [key]
  have hmul : AnalyticAt 𝕜
      (fun P : ((i : ι) → E →L[𝕜] F) × ContinuousMultilinearMap 𝕜 (fun _ : ι => F) G =>
        P.2.compContinuousLinearMap P.1) (pullbackPairCLM q) :=
    ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap
  exact (((((Fintype.card ι).factorial : 𝕜)⁻¹ • alternatizationCLM)).analyticAt _).comp
    (hmul.comp (pullbackPairCLM.analyticAt q))

end ContinuousAlternatingMap

namespace ContinuousAlternatingMap
variable {𝕜 ι E F G : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CharZero 𝕜] [CompleteSpace G]

/-- ★ The `ContDiffAt` corollary — the form a smooth-bundle instance consumes. -/
theorem contDiffAt_uncurry_compContinuousLinearMap {n : WithTop ℕ∞}
    (q : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G)) :
    ContDiffAt 𝕜 n (fun p : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G) =>
      p.2.compContinuousLinearMap p.1) q :=
  (analyticAt_uncurry_compContinuousLinearMap q).contDiffAt

/-- ★ The `ContDiff` corollary. -/
theorem contDiff_uncurry_compContinuousLinearMap {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun p : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G) =>
      p.2.compContinuousLinearMap p.1) :=
  contDiff_iff_contDiffAt.2 fun q => contDiffAt_uncurry_compContinuousLinearMap q

end ContinuousAlternatingMap

/-! ### The operator-valued form, and postcomposition

What a smooth-bundle instance actually consumes is not the *application* `(g, ω) ↦ ω ∘ g` but
the operator-valued map `g ↦ (ω ↦ ω ∘ g)`, together with its postcomposition partner. Both are
here. ⚠️ See the honest-scope note at the top of the file for where the next layer stops. -/

namespace ContinuousAlternatingMap
open ContinuousMultilinearMap
variable {𝕜 ι E F G : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CharZero 𝕜]

/-- The retraction identity in operator form. -/
theorem compContinuousLinearMapCLM_eq (g : E →L[𝕜] F) :
    (compContinuousLinearMapCLM g : (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G))
      = (((Fintype.card ι).factorial : 𝕜)⁻¹ • alternatizationCLM).comp
          (((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
              (fun _ : ι => E) (fun _ : ι => F) G) (fun _ => g)).comp
            (toContinuousMultilinearMapCLM 𝕜)) := by
  ext ω v
  have h := compContinuousLinearMap_eq_smul_alternatization (ι := ι) g ω
  simpa using congrArg (fun x : E [⋀^ι]→L[𝕜] G => x v) h

/-- ★ **The pullback operator is smooth in the linear map.** This is the form the coordinate
change of an alternating-map bundle is built from. -/
theorem contDiff_compContinuousLinearMapCLM {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun g : E →L[𝕜] F =>
      (compContinuousLinearMapCLM g : (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G))) := by
  simp only [compContinuousLinearMapCLM_eq]
  have hM : ContDiff 𝕜 n (fun g : E →L[𝕜] F =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : ι => E) (fun _ : ι => F) G) (fun _ => g)) :=
    (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.2 fun _ => contDiff_id)
  exact contDiff_const.clm_comp (hM.clm_comp contDiff_const)

omit [CharZero 𝕜] in
/-- The pullback of a `2`-form, read on a pair of vectors: `(ω ∘ L) ⦃a, b⦄ = ω ⦃L a, L b⦄`. The
`Matrix.cons` notation does not reduce under the composition on its own, so this is the lemma every
degree-`2` pullback computation starts with. -/
theorem compContinuousLinearMap_apply_pair (alt : F [⋀^Fin 2]→L[𝕜] G) (L : E →L[𝕜] F) (a b : E) :
    (alt.compContinuousLinearMap L) ![a, b] = alt ![L a, L b] := by
  have hfam : (fun k => L (![a, b] k)) = ![L a, L b] := by
    funext k
    fin_cases k <;> rfl
  show alt (fun k => L (![a, b] k)) = alt ![L a, L b]
  rw [hfam]

end ContinuousAlternatingMap
