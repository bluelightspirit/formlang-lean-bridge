import os
import shutil
import subprocess
import pytest
from pyformlang.finite_automaton import NondeterministicFiniteAutomaton
from formlang_lean_bridge import export_automaton


@pytest.mark.lean
def test_generated_lean_module_compiles(tmp_path):
    lake = shutil.which("lake")
    project = os.environ.get("LEAN_PROJECT_PATH")
    if not lake or not project:
        pytest.skip("Requires `lake` on PATH and LEAN_PROJECT_PATH pointing to a Lean project")
    nfa = NondeterministicFiniteAutomaton()
    nfa.add_transition("s", "a", "f")
    nfa.add_start_state("s")
    nfa.add_final_state("f")
    artifact = export_automaton(nfa, "BridgeCompile", [["a"], []])
    lean_file = tmp_path / "BridgeCompile.lean"
    lean_file.write_text(artifact.source, encoding="utf-8")
    result = subprocess.run(
        [lake, "env", "lean", str(lean_file)], cwd=project,
        capture_output=True, text=True, timeout=120,
    )
    assert result.returncode == 0, result.stdout + result.stderr

