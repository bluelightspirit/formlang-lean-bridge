import os
import shutil
import subprocess

import pytest
from pyformlang.finite_automaton import NondeterministicFiniteAutomaton

from formlang_lean_bridge import export_automaton


@pytest.mark.lean
def test_edge_cases_are_verified_by_lean(tmp_path):
    lake = shutil.which("lake")
    project = os.environ.get("LEAN_PROJECT_PATH")

    if not lake or not project:
        pytest.skip("Requires lake and LEAN_PROJECT_PATH")

    cases = []

    # Multiple initial and final states.
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transitions([
        ("s1", "a", "f1"),
        ("s2", "b", "f2"),
    ])
    nfa.add_start_state("s1")
    nfa.add_start_state("s2")
    nfa.add_final_state("f1")
    nfa.add_final_state("f2")
    cases.append(("MultipleStarts", nfa, [[], ["a"], ["b"], ["a", "b"]]))

    # Empty word accepted.
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_start_state("q")
    nfa.add_final_state("q")
    nfa.add_transition("q", "a", "dead")
    cases.append(("EmptyAccepted", nfa, [[], ["a"]]))

    # Empty word rejected; missing transition rejects longer word.
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transition("s", "a", "f")
    nfa.add_start_state("s")
    nfa.add_final_state("f")
    cases.append(("MissingTransition", nfa, [[], ["a"], ["a", "a"]]))

    # Nondeterministic branching.
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transitions([
        ("s", "a", "x"),
        ("s", "a", "y"),
        ("x", "b", "f"),
        ("y", "c", "f"),
    ])
    nfa.add_start_state("s")
    nfa.add_final_state("f")
    cases.append(("Branching", nfa, [["a"], ["a", "b"], ["a", "c"], ["a", "a"]]))

    # Unicode state names and alphabet symbol.
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transition("état-α", "α", "状態-β")
    nfa.add_start_state("état-α")
    nfa.add_final_state("状態-β")
    cases.append(("Unicode", nfa, [[], ["α"], ["α", "α"]]))

    modules = []

    for name, automaton, words in cases:
        artifact = export_automaton(automaton, name, words)
        modules.append(
            artifact.source.replace("import Std\n", "", 1)
        )

    source = "import Std\n\n" + "\n".join(modules)
    lean_file = tmp_path / "LeanEdgeCases.lean"
    lean_file.write_text(source, encoding="utf-8")

    result = subprocess.run(
        [lake, "env", "lean", str(lean_file)],
        cwd=project,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert result.returncode == 0, result.stdout + result.stderr
