#!/usr/bin/env python3
"""Check that Challenge.lean states lean-eval's Darboux problem, and nothing else.

Palomar's Comparator checks that Solution proves the statement of Challenge.lean. This script checks
the other link: that Challenge.lean is lean-eval's text.

lean-eval (`leanprover/lean-eval`) generates, for its problem `darboux`, a workspace with two
files: `generated/darboux/ChallengeDeps.lean` (`import Mathlib`, then the definitions `E`, `idxP`,
`idxQ`, `IsDarbouxNormal` and `IsSymplecticOn` in namespace `LeanEval.Geometry.Darboux`) and
`generated/darboux/Challenge.lean` (`import ChallengeDeps`, then the statement `darboux` in the
root namespace, ending `sorry`). This script fetches both at LEAN_EVAL_COMMIT, requires each to
have the SHA-256 recorded below, and requires Challenge.lean to be exactly:

* a module header, `public import Mathlib` and a module docstring, and nothing else (the docstring
  may not contain `/-`, so nested comments cannot hide or expose code);
* `@[expose] public section`;
* the text of ChallengeDeps.lean after its `import Mathlib` line, with trailing blank lines
  trimmed, and with exactly two substitutions (SUBSTITUTIONS below): the `omega` proofs of the
  bounds in `idxP` and `idxQ` replaced by term proofs. `omega` leaves an auxiliary lemma private
  to the module, so a copy of the definitions in another module is a different constant and
  Comparator rejects the match; the term proofs leave only public auxiliary lemmas, which match;
* a blank line, then the text of Challenge.lean after its `import ChallengeDeps` line.

The two lean-eval files were read by hand at that commit: ChallengeDeps.lean contains only
`import Mathlib`, the namespaces, a module docstring, `open Set Function Matrix`,
`open scoped ContDiff` and the five definitions; Challenge.lean contains only its import, three
`open` lines and the statement. Neither has a notation, macro, `set_option`, `attribute`,
`variable` or `instance`.

What this script does not establish: it compares text. lean-eval builds its workspace with Lean
`v4.35.0-rc3` and Mathlib `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`; this repository uses the
same Lean and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`. So this checks that the text is
the same, not that it elaborates to the same terms against lean-eval's Mathlib.

Usage:
  check-lean-eval-match.py              check (downloads lean-eval's two files)
  check-lean-eval-match.py --self-test  check, then confirm a list of altered inputs all fail
"""
import hashlib
import re
import sys
import urllib.request
from pathlib import Path

LEAN_EVAL_COMMIT = "85a88c37f80170d9f08651dc63ce6b81a8a48cb9"
DEPS = "generated/darboux/ChallengeDeps.lean"
CHAL = "generated/darboux/Challenge.lean"
SHA = {
    DEPS: "0169259ebf7a2bf8cff1eb6466e343ae6b20b8c9c70dd85151d25a7c5ef20224",
    CHAL: "2d26752b3db082d2bbafacd167915643cbe76e8c5b25a9202e99eb8ba7acf50d",
}
EXPOSE = "@[expose] public section\n"
# The one divergence from lean-eval's text: each pair is (lean-eval's line, this repository's
# line), and each lean-eval line must occur exactly once.
SUBSTITUTIONS = (
    ("  ⟨i.val, by have := i.isLt; omega⟩\n",
     "  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_left n Nat.two_pos)⟩\n"),
    ("  ⟨i.val + n, by have := i.isLt; omega⟩\n",
     "  ⟨i.val + n, Nat.lt_of_lt_of_eq (Nat.add_lt_add_right i.isLt n) (Nat.two_mul n).symm⟩\n"),
)
ROOT = Path(__file__).resolve().parent.parent


class Mismatch(Exception):
    pass


def fetch(path):
    url = f"https://raw.githubusercontent.com/leanprover/lean-eval/{LEAN_EVAL_COMMIT}/{path}"
    with urllib.request.urlopen(url) as r:
        return r.read().decode("utf8").replace("\r\n", "\n")


def expected_code(deps, chal):
    for path, text in ((DEPS, deps), (CHAL, chal)):
        if hashlib.sha256(text.encode("utf8")).hexdigest() != SHA[path]:
            raise Mismatch(f"lean-eval {path}: differs from the text read at the pinned commit")
    if not deps.startswith("import Mathlib\n\n"):
        raise Mismatch("lean-eval ChallengeDeps.lean: does not start with `import Mathlib`")
    if not chal.startswith("import ChallengeDeps\n\n"):
        raise Mismatch("lean-eval Challenge.lean: does not start with `import ChallengeDeps`")
    dbody = deps[len("import Mathlib\n\n"):].rstrip("\n")
    for old, new in SUBSTITUTIONS:
        if dbody.count(old) != 1:
            raise Mismatch(f"lean-eval ChallengeDeps.lean: expected exactly one {old.strip()!r}")
        dbody = dbody.replace(old, new)
    cbody = chal[len("import ChallengeDeps\n\n"):]
    return EXPOSE + "\n" + dbody + "\n\n" + cbody


COMMENT_BODY = r"(?:(?!-/|/-)[\s\S])*"
PREAMBLE = re.compile(r"\Amodule\n\npublic import Mathlib\n\n/-!" + COMMENT_BODY + r"-/\n\n")


def check(challenge, deps, chal):
    expected = expected_code(deps, chal)
    m = PREAMBLE.match(challenge)
    if not m:
        raise Mismatch("Challenge.lean: the preamble is not `module`, `public import Mathlib` and "
                       "a module docstring")
    rest = challenge[m.end():]
    if rest != expected:
        n = next((i for i, (x, y) in enumerate(zip(rest, expected)) if x != y),
                 min(len(rest), len(expected)))
        raise Mismatch(f"Challenge.lean: differs from lean-eval's text at code line "
                       f"{rest.count(chr(10), 0, n) + 1}")


def mutations(c, deps, chal):
    def sub(text, a, b):
        assert text.count(a) >= 1, a
        return text.replace(a, b, 1)
    yield "Challenge: smoothness weakened", sub(c, "ContDiffOn ℝ ∞ α U ∧", "ContDiffOn ℝ 1 α U ∧"), deps, chal
    yield "Challenge: closedness dropped", sub(c, "(∀ x ∈ U, extDeriv α x = 0) ∧\n", ""), deps, chal
    yield "Challenge: a normal-form value changed", sub(c, "= if i = j then (1 : ℝ) else 0", "= if i = j then (2 : ℝ) else 0"), deps, chal
    yield "Challenge: idxQ changed", sub(c, "⟨i.val + n, Nat", "⟨i.val, Nat"), deps, chal
    (p_old, p_new), (q_old, q_new) = SUBSTITUTIONS
    yield "Challenge: lean-eval's omega proof kept in idxP", sub(c, p_new, p_old), deps, chal
    yield "Challenge: idxP's bound proved another way", sub(c, p_new, "  ⟨i.val, by omega⟩\n"), deps, chal
    yield "Challenge: idxQ's value changed with its proof", sub(c, q_new, p_new), deps, chal
    yield "lean-eval: an omega proof changed upstream", c, sub(deps, q_old, "  ⟨i.val + n, by omega⟩\n"), chal
    yield "Challenge: the dimension changed", sub(c, "EuclideanSpace ℝ (Fin (2 * n))", "EuclideanSpace ℝ (Fin (2 * n + 1))"), deps, chal
    yield "Challenge: the inverse dropped", sub(c, "ContDiffOn ℝ ∞ (φ.symm : E n → E n) φ.target ∧\n", ""), deps, chal
    yield "Challenge: source not in U", sub(c, "x ∈ φ.source ∧ φ.source ⊆ U ∧", "x ∈ φ.source ∧"), deps, chal
    yield "Challenge: the statement renamed", sub(c, "theorem darboux ", "theorem darboux' "), deps, chal
    yield "Challenge: the statement proved", sub(c, "  sorry\n", "  exact absurd rfl (by sorry)\n"), deps, chal
    yield "Challenge: code before the expose line", sub(c, EXPOSE, "set_option autoImplicit true\n\n" + EXPOSE), deps, chal
    yield "Challenge: code hidden in a nested comment", sub(c, "/-!", "/-! /- -/", ), deps, chal
    yield "Challenge: an extra theorem", c + "\ntheorem extra : True := trivial\n", deps, chal
    yield "Challenge: an axiom after an early end of the docstring", sub(c, "-/\n\n" + EXPOSE, "-/\naxiom Injected : False\n-- -/\n\n" + EXPOSE), deps, chal
    yield "Challenge: a notation added", sub(c, "namespace Darboux\n", "namespace Darboux\n\nlocal notation \"ℝ\" => ℚ\n"), deps, chal
    yield "lean-eval: a definition changed", c, sub(deps, "ContDiffOn ℝ ∞ α U ∧", "ContDiffOn ℝ 1 α U ∧"), chal
    yield "lean-eval: the statement changed", c, deps, sub(chal, "x ∈ φ.source ∧ φ.source ⊆ U ∧", "x ∈ φ.source ∧")
    yield "lean-eval: an extra import", c, sub(deps, "import Mathlib\n", "import Mathlib\nimport Lean\n"), chal


def main(argv):
    sys.stdout.reconfigure(encoding="utf-8", newline="\n")
    deps, chal = fetch(DEPS), fetch(CHAL)
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf8")
    try:
        check(challenge, deps, chal)
    except Mismatch as e:
        print(f"FAIL: {e}")
        return 1
    print(f"OK: Challenge.lean is lean-eval's Darboux problem, and nothing else "
          f"(lean-eval at {LEAN_EVAL_COMMIT})")
    if "--self-test" not in argv:
        return 0
    count = 0
    for label, c, d, h in mutations(challenge, deps, chal):
        count += 1
        try:
            check(c, d, h)
        except Mismatch as e:
            print(f"  fails as it should: {label}: {e}")
            continue
        print(f"FAIL: self-test: {label} passed the check")
        return 1
    print(f"OK: self-test, all {count} altered inputs fail")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
