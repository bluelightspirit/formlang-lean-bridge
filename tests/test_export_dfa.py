from pyformlang.finite_automaton import DeterministicFiniteAutomaton
from formlang_lean_bridge import export_automaton
from tests.conftest import accepts_from_manifest


def make_dfa():
    dfa = DeterministicFiniteAutomaton()
    dfa.add_start_state("start")
    dfa.add_final_state("ends_b")
    dfa.add_transitions([
        ("start", "a", "start"), ("start", "b", "ends_b"),
        ("ends_b", "a", "start"), ("ends_b", "b", "ends_b"),
    ])
    return dfa


def test_dfa_acceptance_matches_exported_manifest():
    dfa = make_dfa()
    words = [[], ["a"], ["b"], ["a", "b"], ["b", "a"], ["a", "a"]]
    artifact = export_automaton(dfa, "EndsInB", words)
    for word in words:
        assert accepts_from_manifest(artifact.manifest, word) == bool(dfa.accepts(word))


def test_dfa_export_structure():
    artifact = export_automaton(make_dfa(), "EndsInB")
    assert len(artifact.manifest["states"]) == 2
    assert len(artifact.manifest["alphabet"]) == 2
    assert len(artifact.manifest["start_state_ids"]) == 1
    assert "def accepts" in artifact.source
