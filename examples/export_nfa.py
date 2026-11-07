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

artifact = export_automaton(
    nfa,
    "ExampleNFA",
    words=[["a", "b"], ["a"], []],
)
artifact.write("lean/ExampleNFA.lean")
print(artifact.manifest)
