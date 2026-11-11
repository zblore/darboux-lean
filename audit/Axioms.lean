/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DarbouxLean

/-!
# Axioms of the main results

Fails if the main result, or a key lemma, comes to depend on anything beyond Lean's three
standard axioms.
-/

/-- info: 'darboux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms darboux

/--
info: 'exists_openPartialHomeomorph_pullback_standard' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_openPartialHomeomorph_pullback_standard

/--
info: 'DarbouxLean.isDarbouxNormal_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DarbouxLean.isDarbouxNormal_coord
