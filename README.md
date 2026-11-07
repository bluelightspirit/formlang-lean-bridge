# formlang-lean-bridge

A starter Python package connecting **Pyformlang** automata with **Lean 4**.
It exports finite automata to executable Lean definitions and can optionally
use **PyPantograph** to interact with Lean goals.

## Scope in 0.2.0

### Implemented

- DFA, NFA, and EpsilonNFA export from Pyformlang to self-contained Lean 4 definitions.
- Explicit integer encodings for states and alphabet symbols, with a JSON manifest mapping exported identifiers back to their original values.
- Support for multiple initial states and nondeterministic transitions.
- Executable Lean acceptance semantics for DFAs, NFAs, and epsilon-NFAs, including epsilon closure.
- Optional concrete acceptance checks generated as Lean `by decide` examples.
- Optional PyPantograph integration for loading definitions, inspecting declarations, and submitting propositions to Lean.
- Python/Lean differential tests and edge-case tests for exported automata.
- Python-side determinization and minimization, with bounded transformation and equivalence tests.

### Formal verification

The Lean formalization includes:

- NFA and DFA definitions and executable acceptance semantics.
- Subset construction and a finite canonical subset-DFA construction.
- A well-formedness predicate for NFAs.
- A proved acceptance-preservation theorem:

  `FormalAutomata.finite_subset_acceptance_preserved`

  This establishes that the finite subset DFA accepts the same words as its source NFA, provided the NFA is well-formed and the input word uses symbols from its declared alphabet.

- A concrete finite subset-construction example checked using the Lean compiler.
- Compiler-level checks for unfinished proofs (`sorryAx`) in the concrete theorem.

The formal acceptance-preservation result is narrower than a general proof of correctness for the entire Python-to-Lean export pipeline. The Lean theorem does not establish correctness for arbitrary Pyformlang objects or all possible exporter inputs.

### Not implemented or not yet formally verified

- FST (finite-state transducer), CFG (context-free grammar), and PDA (pushdown automaton) export.
- A general formal proof that the Python exporter preserves the language of every supported Pyformlang automaton.
- A general Lean proof of minimization correctness.
- Formal equivalence proofs for every Python-side transformation and every possible input.

### Testing

The test suite covers Python export, Lean compilation, acceptance semantics, edge cases, differential testing, transformations, and optional PyPantograph integration.

The latest full test run completed with **26 passing tests**, including the configured PyPantograph and actual Lean compiler checks.

Lean and PyPantograph tests require their respective external tools and a configured Lean project.

Not implemented yet: FST/CFG/PDA export, a general proof that the Python
and Lean automata denote the same language, or verified determinization/minimization.

## Install

```bash
python -m venv .venv
# activate the environment, then:
pip install -e .
```

For PyPantograph, install the version compatible with your Lean toolchain using
the instructions in its upstream repository:
https://github.com/stanford-centaur/PyPantograph

You also need Lean 4 and elan. The Lean toolchain used by your project must be
compatible with the installed PyPantograph version.

## Example

```python
from pyformlang.finite_automaton import NondeterministicFiniteAutomaton
from formlang_lean_bridge import export_automaton

nfa = NondeterministicFiniteAutomaton()
nfa.add_transitions([
    ("q0", "a", "q0"),
    ("q0", "a", "q1"),
    ("q1", "b", "q2"),
])
nfa.add_start_state("q0")
nfa.add_final_state("q2")

artifact = export_automaton(nfa, "ExampleNFA", words=[
    ["a", "b"],
    ["a"],
    [],
])
artifact.write("lean/ExampleNFA.lean")
print(artifact.manifest)
```

Compile the generated module from your Lean project:

```bash
lake env lean lean/ExampleNFA.lean
```

The generated module defines `stateCount`, `symbolCount`, `transitions`,
`startStates`, `finalStates`, `step`, `run`, and `accepts`.

## PyPantograph

The wrapper is deliberately optional because PyPantograph's API can vary by
release. See `pantograph.py`; it uses the upstream `pantograph.server.Server`
interface and exposes a small `prove()` method. You may need to adapt its
constructor or result handling to the exact version installed.

```python
from formlang_lean_bridge import PantographVerifier

verifier = PantographVerifier(project_path=".")
result = verifier.prove("ExampleNFA.accepts [0, 1] = true")
print(result)
```

Ensure the generated module is imported by the Lean project before submitting
qualified propositions to the server.

## What the generated checks prove

A generated `example ... := by decide` is checked by Lean's kernel for that
specific finite word and exported transition table. It does **not** by itself
prove that the exporter preserves the semantics of every Pyformlang automaton.
A general correctness theorem needs a formal relation between the source
automaton and its integer-encoded Lean representation.

## Development

```bash
pip install -e ".[dev]"
pytest
```
