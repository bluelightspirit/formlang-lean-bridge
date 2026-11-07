# formlang-lean-bridge

A starter Python package connecting **Pyformlang** automata with **Lean 4**.
It exports finite automata to executable Lean definitions and can optionally
use **PyPantograph** to interact with Lean goals.

## Scope in 0.1.0

- DFA/NFA export to a self-contained Lean 4 module.
- Explicit integer encodings for states and alphabet symbols, with a JSON manifest.
- Multiple initial states and nondeterministic transitions.
- Executable acceptance semantics.
- Optional concrete acceptance checks generated as Lean `by decide` examples.
- Optional PyPantograph adapter for submitting propositions to Lean.

Not implemented yet: epsilon-transition export, FST/CFG/PDA export, a general
proof that the Python and Lean automata denote the same language, or verified
determinization/minimization. Epsilon transitions are rejected explicitly.

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
