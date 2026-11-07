import json
import pytest
from pyformlang.finite_automaton import EpsilonNFA, NondeterministicFiniteAutomaton
from formlang_lean_bridge import export_automaton


def test_multiple_start_states_preserved():
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transition("left", "x", "final")
    nfa.add_transition("right", "y", "final")
    nfa.add_start_state("left")
    nfa.add_start_state("right")
    nfa.add_final_state("final")
    assert len(export_automaton(nfa, "MultiStart").manifest["start_state_ids"]) == 2


def test_empty_word_acceptance_and_rejection():
    yes = NondeterministicFiniteAutomaton()
    yes.add_start_state("s")
    yes.add_final_state("s")
    no = NondeterministicFiniteAutomaton()
    no.add_start_state("s")
    no.add_final_state("f")
    no.add_transition("s", "a", "f")
    assert "accepts [] = true" in export_automaton(yes, "AcceptsEmpty", [[]]).source
    assert "accepts [] = false" in export_automaton(no, "RejectsEmpty", [[]]).source


def test_missing_transition_rejects_the_test_word():
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_start_state("s")
    nfa.add_final_state("f")
    nfa.add_transition("s", "a", "f")
    artifact = export_automaton(nfa, "MissingEdge", [["a", "a"]])
    a_id = next(x["id"] for x in artifact.manifest["alphabet"] if x["python_repr"] == "'a'")
    assert f"accepts [{a_id}, {a_id}] = false" in artifact.source


def test_unicode_alphabet():
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transition("état-α", "α", "状態-β")
    nfa.add_start_state("état-α")
    nfa.add_final_state("状態-β")
    artifact = export_automaton(nfa, "UnicodeAutomaton", [["α"]])
    assert artifact.manifest["alphabet"][0]["python_repr"] == "'α'"
    assert "accepts [0] = true" in artifact.source


def test_unusual_state_names():
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transition("state with spaces", "go!", "state/2")
    nfa.add_start_state("state with spaces")
    nfa.add_final_state("state/2")
    manifest = export_automaton(nfa, "OddNames", [["go!"]]).manifest
    assert len(manifest["states"]) == 2
    assert all(isinstance(state["id"], int) for state in manifest["states"])


def test_unknown_test_symbol_raises():
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transition("s", "a", "f")
    nfa.add_start_state("s")
    nfa.add_final_state("f")
    with pytest.raises(ValueError, match="not in the automaton alphabet"):
        export_automaton(nfa, "Unknown", [["missing"]])


def test_epsilon_edges_rejected():
    enfa = EpsilonNFA()
    enfa.add_transition("s", "epsilon", "f")
    enfa.add_start_state("s")
    enfa.add_final_state("f")
    with pytest.raises(NotImplementedError, match="Epsilon transitions"):
        export_automaton(enfa, "EpsilonRejected")


def test_manifest_sidecar_written(tmp_path):
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transition("s", "a", "f")
    nfa.add_start_state("s")
    nfa.add_final_state("f")
    target = export_automaton(nfa, "WriteTest").write(tmp_path / "A.lean")
    data = json.loads(target.with_suffix(".lean.json").read_text(encoding="utf-8"))
    assert data["format"] == "formlang-lean-bridge/0.1.0"
