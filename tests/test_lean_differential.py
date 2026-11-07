import os
import random
import shutil
import subprocess

import pytest
from pyformlang.finite_automaton import NondeterministicFiniteAutomaton

from formlang_lean_bridge import export_automaton


@pytest.mark.lean
def test_seeded_random_nfas_are_verified_by_lean(tmp_path):
    lake = shutil.which("lake")
    project = os.environ.get("LEAN_PROJECT_PATH")

    if not lake or not project:
        pytest.skip("Requires lake and LEAN_PROJECT_PATH")

    rng = random.Random(20261105)
    alphabet = ["a", "b"]
    modules = []

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

        artifact = export_automaton(
            nfa, f"RandomLeanCase{case}", words
        )

        # Keep each generated namespace, but use one shared import.
        module = artifact.source.replace("import Std\n", "", 1)
        modules.append(module)

    lean_source = "import Std\n\n" + "\n".join(modules)
    lean_file = tmp_path / "RandomDifferential.lean"
    lean_file.write_text(lean_source, encoding="utf-8")

    result = subprocess.run(
        [lake, "env", "lean", str(lean_file)],
        cwd=project,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert result.returncode == 0, result.stdout + result.stderr
