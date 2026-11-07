import random
from pyformlang.finite_automaton import NondeterministicFiniteAutomaton
from formlang_lean_bridge import export_automaton
from tests.conftest import accepts_from_manifest


def test_seeded_random_nfas_match_exported_transition_table():
    rng = random.Random(20261105)
    alphabet = ["a", "b"]
    for case in range(25):
        nfa = NondeterministicFiniteAutomaton()
        states = [f"q{i}" for i in range(rng.randint(1, 5))]
        for state in states:
            if rng.random() < 0.45:
                nfa.add_start_state(state)
            if rng.random() < 0.40:
                nfa.add_final_state(state)
        if not nfa.start_states:
            nfa.add_start_state(states[0])
        # Ensure both symbols occur in the alphabet in every generated case.
        nfa.add_transition(states[0], "a", states[0])
        nfa.add_transition(states[0], "b", states[0])
        for source in states:
            for symbol in alphabet:
                for target in states:
                    if rng.random() < 0.18:
                        nfa.add_transition(source, symbol, target)
        words = [[]] + [
            [rng.choice(alphabet) for _ in range(rng.randint(0, 6))]
            for _ in range(30)
        ]
        artifact = export_automaton(nfa, f"RandomCase{case}", words)
        for word in words:
            assert accepts_from_manifest(artifact.manifest, word) == bool(nfa.accepts(word))
