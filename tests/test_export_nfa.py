from pyformlang.finite_automaton import NondeterministicFiniteAutomaton
from formlang_lean_bridge import export_automaton
from tests.conftest import accepts_from_manifest


def make_nfa():
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transitions([
        ("q0", "a", "q0"), ("q0", "a", "q1"), ("q1", "b", "q2"),
    ])
    nfa.add_start_state("q0")
    nfa.add_final_state("q2")
    return nfa


def test_nondeterministic_edges_are_preserved():
    artifact = export_automaton(make_nfa(), "BranchingNFA")
    a_id = next(x["id"] for x in artifact.manifest["alphabet"] if x["python_repr"] == "'a'")
    q0_id = next(x["id"] for x in artifact.manifest["states"] if x["python_repr"] == "'q0'")
    targets = {
        edge["target"] for edge in artifact.manifest["transitions"]
        if edge["source"] == q0_id and edge["symbol"] == a_id
    }
    assert len(targets) == 2


def test_nfa_acceptance_matches_exported_manifest():
    nfa = make_nfa()
    words = [[], ["a"], ["a", "b"], ["a", "a", "b"], ["b"]]
    artifact = export_automaton(nfa, "BranchingNFA", words)
    for word in words:
        assert accepts_from_manifest(artifact.manifest, word) == bool(nfa.accepts(word))
