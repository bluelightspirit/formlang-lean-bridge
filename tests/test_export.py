import pytest
from pyformlang.finite_automaton import NondeterministicFiniteAutomaton, EpsilonNFA
from formlang_lean_bridge import export_automaton


def make_nfa():
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transitions([
        ("q0", "a", "q0"),
        ("q0", "a", "q1"),
        ("q1", "b", "q2"),
    ])
    nfa.add_start_state("q0")
    nfa.add_final_state("q2")
    return nfa


def test_export_has_lean_semantics_and_checks():
    artifact = export_automaton(
        make_nfa(), "ExampleNFA", [["a", "b"], ["a"], []]
    )
    assert "def accepts" in artifact.source
    assert "by decide" in artifact.source
    assert len(artifact.manifest["transitions"]) == 3


def test_epsilon_is_rejected():
    enfa = EpsilonNFA()
    enfa.add_transition("s", "epsilon", "f")
    enfa.add_start_state("s")
    enfa.add_final_state("f")
    with pytest.raises(NotImplementedError):
        export_automaton(enfa)
