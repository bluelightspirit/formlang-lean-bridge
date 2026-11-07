import os
import subprocess
from pathlib import Path

import pytest


@pytest.mark.pantograph
def test_pantograph_proves_concrete_subset_dfa_acceptance_and_rejection(tmp_path):
    if os.environ.get("RUN_PANTOGRAPH_TESTS") != "1":
        pytest.skip("Set RUN_PANTOGRAPH_TESTS=1 to enable Pantograph tests")

    pytest.importorskip("pantograph")

    from formlang_lean_bridge import PantographVerifier

    project = os.environ.get("LEAN_PROJECT_PATH")
    if not project:
        pytest.skip("Set LEAN_PROJECT_PATH to a configured Lean project")

    formal_file = (
        Path(__file__).resolve().parents[1]
        / "formal"
        / "AutomataIntegrated.lean"
    )
    source = formal_file.read_text(encoding="utf-8")
    source = source.removeprefix("import Std\n")

    example = """
def pantographExampleNFA : FormalAutomata.NFA Nat Bool where
  states := [0, 1]
  alphabet := [true]
  initial := [0]
  accepting := [1]
  transition := fun q a =>
    if q = 0 then (if a then [1] else []) else []

theorem pantographConcreteFiniteSubsetCorrect :
    FormalAutomata.DFA.accepts
      (FormalAutomata.finiteSubsetDFA pantographExampleNFA) [true] =
    FormalAutomata.NFA.accepts pantographExampleNFA [true] := by
  apply FormalAutomata.finite_subset_acceptance_preserved
  · simp [FormalAutomata.WellFormed, pantographExampleNFA]
    intro q q' _ hq hq'
    subst q
    subst q'
    simp
  · intro a ha
    simpa [pantographExampleNFA] using ha
"""

    accepting_proposition = """
FormalAutomata.DFA.accepts
  (FormalAutomata.subsetDFA pantographExampleNFA)
  [true] = true
"""

    rejecting_proposition = """
FormalAutomata.DFA.accepts
  (FormalAutomata.subsetDFA pantographExampleNFA)
  [] = false
"""

    with PantographVerifier(project_path=project, imports=["Std"]) as verifier:
        verifier.load_definitions(source)
        verifier.load_definitions(example)

        accepted = verifier.prove_by_decide(accepting_proposition)
        rejected = verifier.prove_by_decide(rejecting_proposition)

        declaration = verifier._server.env_inspect(
            "pantographConcreteFiniteSubsetCorrect",
            print_value=True,
            print_dependency=True,
        )

        units = verifier._server.check_compile(
            "#print axioms pantographConcreteFiniteSubsetCorrect"
        )
        axiom_report = "\n".join(
            str(message.data)
            for unit in units
            for message in unit.messages
        )

    assert "sorryAx" not in repr(declaration.get("valueDependency", []))
    assert "sorryAx" not in axiom_report
    assert "propext" in axiom_report
    assert "Quot.sound" in axiom_report

    assert accepted.is_solved
    assert accepted.goals == []
    assert rejected.is_solved
    assert rejected.goals == []

    # Independently compile the formal source and concrete theorem with Lean.
    lean_file = tmp_path / "PantographCompilerCheck.lean"
    lean_file.write_text(
        "import Std\n\n" + source + "\n" + example
        + "\n#print axioms pantographConcreteFiniteSubsetCorrect\n",
        encoding="utf-8",
    )

    compiled = subprocess.run(
        ["lake", "env", "lean", str(lean_file)],
        cwd=project,
        capture_output=True,
        text=True,
        check=False,
    )
    compiler_output = compiled.stdout + compiled.stderr

    assert compiled.returncode == 0, compiler_output
    assert "sorryAx" not in compiler_output, compiler_output
    assert "propext" in compiler_output
    assert "Quot.sound" in compiler_output
