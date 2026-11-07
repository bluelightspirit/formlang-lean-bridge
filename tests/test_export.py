from pyformlang.finite_automaton import NondeterministicFiniteAutomaton, EpsilonNFA, Epsilon
from tests.conftest import accepts_from_manifest
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


def test_epsilon_chain_cycle_and_acceptance():
    enfa = EpsilonNFA()
    enfa.add_transitions([
        ("s", Epsilon(), "p"),
        ("p", Epsilon(), "q"),
        ("q", "a", "r"),
        ("r", Epsilon(), "f"),
        ("f", Epsilon(), "r"),
    ])
    enfa.add_start_state("s")
    enfa.add_final_state("f")

    words = [[], ["a"], ["a", "a"]]
    artifact = export_automaton(enfa, "EpsilonChainCycle", words)

    assert len(artifact.manifest["epsilon_transitions"]) == 4
    assert len(artifact.manifest["alphabet"]) == 1
    assert "def epsilonClosure" in artifact.source

    for word in words:
        assert accepts_from_manifest(artifact.manifest, word) == bool(enfa.accepts(word))


def test_epsilon_looking_strings_are_ordinary_symbols():
    enfa = EpsilonNFA()
    enfa.add_transitions([
        ("s", "eps", "middle"),
        ("middle", "λ", "f"),
    ])
    enfa.add_start_state("s")
    enfa.add_final_state("f")

    artifact = export_automaton(enfa, "LiteralEpsilonNames", [["eps", "λ"]])

    assert len(artifact.manifest["epsilon_transitions"]) == 0
    assert len(artifact.manifest["transitions"]) == 2
    assert len(artifact.manifest["alphabet"]) == 2
    assert accepts_from_manifest(artifact.manifest, ["eps", "λ"])
    assert not accepts_from_manifest(artifact.manifest, [])
