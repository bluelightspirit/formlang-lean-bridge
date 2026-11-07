# Expanded tests for formlang-lean-bridge

Copy the `tests/` directory and `pytest.ini` into the root of the bridge checkout.

The suite covers DFA/NFA acceptance against the exported manifest, nondeterministic
branches, multiple start states, empty words, missing transitions, Unicode symbols,
unusual state names, unknown test symbols, epsilon rejection, JSON sidecar output,
bounded determinization/minimization checks, seeded randomized differential checks,
and optional Lean/PyPantograph integration.

Run the normal suite with `pytest -v`.

The Lean compile test is skipped unless `lake` is on PATH and `LEAN_PROJECT_PATH`
points to a Lean project. The PyPantograph test is opt-in with
`RUN_PANTOGRAPH_TESTS=1`; the adapter is version-sensitive and must be checked
against the installed PyPantograph release.

Bounded and randomized tests are finite regression tests, not proofs of language
equivalence for all words. The manifest differential tests independently evaluate
the exported transition table, but do not replace Lean compilation.
