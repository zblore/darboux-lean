# Darboux's theorem, in Lean

A Lean 4 proof of Darboux's theorem, in the form Kim Morrison stated it as the problem `darboux` in [lean-eval](https://github.com/leanprover/lean-eval/blob/85a88c37f80170d9f08651dc63ce6b81a8a48cb9/generated/darboux/Challenge.lean):

Let α be a 2-form on an open set U of ℝ²ⁿ that is smooth, closed (dα = 0) and non-degenerate. Then every point of U has a neighbourhood with a smooth chart, smooth in both directions, in which α takes the standard values on the standard basis. So in that chart α is the standard symplectic form ∑ dxᵢ ∧ dxₙ₊ᵢ.

Darboux's theorem (1882) says symplectic geometry has no local invariants: every symplectic form looks the same near a point. The theorem is classical and I claim no priority.

## Other Lean proofs

Mathlib has no symplectic forms and no Darboux theorem. When lean-eval posed the problem in May 2026 it found no formalisation in any proof assistant. Since then three Lean proofs have appeared, each by Moser's method and each with its own statement, not lean-eval's:

- [`t4v1/damian_formalizare`](https://github.com/t4v1/damian_formalizare/blob/545ebb1a7d4c55299b1f59787a7ff0d4d703af27/MorseFloer/Part2/Darboux.lean) (16 Sep 2026), part of a formalisation of Audin and Damian's *Morse Theory and Floer Homology*. Its `MorseFloer.Darboux.darboux` pulls a C¹ closed form on a finite-dimensional space, non-degenerate at a point, back to its constant value there.
- Tau Ceti's [`Darboux/Basic.lean`](https://github.com/TauCetiProject/TauCeti/blob/7ca783d4c8d324c9c74efaacd641c8a40f69f284/TauCeti/Geometry/Symplectic/Darboux/Basic.lean) (first merged 19 Oct 2026): `exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq`, for a closed form on an open subset of a finite-dimensional real normed space.
- Tau Ceti's [`Manifold/Darboux.lean`](https://github.com/TauCetiProject/TauCeti/blob/7ca783d4c8d324c9c74efaacd641c8a40f69f284/TauCeti/Geometry/Symplectic/Manifold/Darboux.lean) (4 Nov 2026): `IsSymplectic.exists_standardDarbouxChart` and related charts on symplectic manifolds.

This proof is independent of all three, and none of them states lean-eval's problem.

lean-eval's audit of 20 Aug 2026 records four accepted solutions of this problem, from four users, the first on 17 Jun 2026. I couldn't find any of them published, and this proof doesn't use them. It comes from my csd-lean4 library. There I proved Darboux on a ball on 21–23 Sep 2026, on top of files I wrote from July.

## The proof

The proof is Moser's (`DarbouxLean/Geometry/Manifold/Darboux.lean`). Fix a point x₀ and let ω₀ be the constant form α(x₀).

1. **Interpolate.** Put ωₜ = ω₀ + t(α − ω₀). Non-degeneracy is an open condition, so every ωₜ is non-degenerate near x₀.
2. **A primitive.** α − ω₀ is closed and vanishes at x₀, so a Poincaré lemma (`DarbouxLean/Analysis/Calculus/DifferentialForm/Poincare.lean`) gives a 1-form β with dβ = α − ω₀ and β(x₀) = 0.
3. **Moser's field.** Solve ι(Xₜ)ωₜ = −β for a time-dependent vector field Xₜ. It vanishes at x₀.
4. **The flow.** Flow Xₜ to time 1 on a small ball (`DarbouxLean/Analysis/ODE/`). Cartan's formula shows the flow carries ωₜ along, so its time-1 map pulls α back to ω₀. The map is close to the identity, so the inverse function theorem makes it a chart, smooth in both directions.
5. **Standard coordinates** (`DarbouxLean/Geometry/Manifold/DarbouxStandardForm.lean`). A symplectic basis of ω₀ (`DarbouxLean/LinearAlgebra/BilinearForm/SymplecticBasis.lean`) turns the constant form into ∑ dpᵢ ∧ dqᵢ. That gives Darboux on a ball, `exists_openPartialHomeomorph_pullback_standard`, for any finite-dimensional real space and any smoothness from C¹ to C^∞.
6. **lean-eval's form** (`DarbouxLean/Bridge.lean`). Read ℝ²ⁿ's coordinates as the p's then the q's, compose, and check the standard basis values.

## Files

- `Challenge.lean` is lean-eval's statement, ending in `sorry`. It's Kim Morrison's text from `generated/darboux/ChallengeDeps.lean` and `generated/darboux/Challenge.lean`, with four changes: the module header, `@[expose] public section`, moving the definitions into the one file, and the bounds in `idxP` and `idxQ`.
- **The one change inside the definitions.** lean-eval proves the bounds in `idxP` and `idxQ` with `by have := i.isLt; omega`. `omega` leaves an auxiliary lemma that is private to its module, so the definitions in a second module are different constants and Comparator rejects the match. Here both bounds are term proofs, which leave no private lemma. `idxP` and `idxQ` give the same `Fin` values either way, so the statement says the same thing.
- `DarbouxLean/Defs.lean` repeats the definitions exactly as in `Challenge.lean`, for the proof to use.
- `DarbouxLean/Bridge.lean` proves `darboux` from Darboux on a ball.
- The other 18 files under `DarbouxLean/` are copied from csd-lean4 at commit `8b99f249`, with imports renamed. Each says so at the top. Their code is unchanged. I edited their comments to remove csd-lean4's internal notes and anything that was out of date here.
- `Solution.lean` re-exports `DarbouxLean`, which proves the statement under lean-eval's name.

## Checks

- `scripts/check-lean-eval-match.py` regenerates Challenge's code from lean-eval's two files at the pinned commit, makes exactly the two `idxP` and `idxQ` substitutions, and requires an exact match. It pins both files by SHA-256, and `--self-test` confirms that 21 altered inputs fail, including any other change to those two lines. This compares text. lean-eval builds this problem with the same Lean, v4.35.0-rc3, but a different Mathlib commit.
- I compared every constant that `darboux`'s statement reaches in `Challenge` and in `Solution`, by name and by term. They match up to the names of bound variables, which Comparator ignores, and none is private to `Challenge` or to this repository's modules, so Palomar's renaming of the Challenge module can't break the match. `lake comparator` in CI is the real check.
- `audit/Axioms.lean` uses `#guard_msgs` to require that the main result and key lemmas use only `propext`, `Classical.choice` and `Quot.sound`.
- `audit/Control.lean` confirms that the audit detects `sorry`, that the hypotheses can hold (the constant standard form is symplectic in every dimension), and that the conclusion isn't trivial (the zero form isn't in Darboux normal form).
- `scripts/verify-comparator.sh` runs `lake comparator` in CI, which replays the proof through Lean's kernel, nanoda and con-ron. It needs Linux, so it doesn't run on my Windows machine.

## Building

Lean `v4.35.0-rc3` and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.

```
lake exe cache get
lake build
lake env lean audit/Axioms.lean
lake env lean audit/Control.lean
python3 scripts/check-lean-sources.py
python3 scripts/check-lean-eval-match.py --self-test
ruby scripts/validate-formalization.rb
```

## How it was made

I drafted the Lean with Claude Code. I've checked every line myself and can explain all of it.

## Licence

Apache 2.0. `Challenge.lean` and `DarbouxLean/Defs.lean` copy lean-eval's text, which is Copyright 2026 Lean FRO, LLC, under Apache 2.0 too. `NOTICE` records this.
