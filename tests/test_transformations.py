import itertools
from pyformlang.finite_automaton import NondeterministicFiniteAutomaton
from formlang_lean_bridge import export_automaton


def make_nfa():
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transitions([
        ("s", "0", "s"), ("s", "0", "p"), ("s", "1", "s"),
        ("p", "1", "f"), ("f", "0", "f"), ("f", "1", "f"),
    ])
    nfa.add_start_state("s")
    nfa.add_final_state("f")
    return nfa


def bounded_words(alphabet, max_length):
    words = [[]]
    for size in range(1, max_length + 1):
        words.extend([list(word) for word in itertools.product(alphabet, repeat=size)])
    return words


def test_determinization_preserves_language_on_bounded_words():
    nfa = make_nfa()
    dfa = nfa.to_deterministic()
    for word in bounded_words(["0", "1"], 4):
        assert bool(nfa.accepts(word)) == bool(dfa.accepts(word))


def test_minimization_preserves_language_on_bounded_words():
    dfa = make_nfa().to_deterministic()
    minimized = dfa.minimize()
    for word in bounded_words(["0", "1"], 4):
        assert bool(dfa.accepts(word)) == bool(minimized.accepts(word))


def test_export_contains_one_lean_check_per_word():
    words = bounded_words(["0", "1"], 3)
    artifact = export_automaton(make_nfa().to_deterministic(), "Determinized", words)
    assert artifact.source.count(" := by decide") == len(words)
