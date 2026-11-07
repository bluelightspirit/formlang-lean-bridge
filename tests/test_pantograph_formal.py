import os
from pathlib import Path

import pytest


@pytest.mark.pantograph
def test_pantograph_loads_and_inspects_formal_automata_theorem():
    if os.environ.get("RUN_PANTOGRAPH_TESTS") != "1":
        pytest.skip("Set RUN_PANTOGRAPH_TESTS=1 to enable Pantograph tests")

    pytest.importorskip("pantograph")

    from formlang_lean_bridge import PantographVerifier

    project_path = os.environ.get("LEAN_PROJECT_PATH")
    if not project_path:
        pytest.skip("Set LEAN_PROJECT_PATH to a configured Lean project")

    formal_file = (
        Path(__file__).resolve().parents[1]
        / "formal"
        / "AutomataIntegrated.lean"
    )
    source = formal_file.read_text(encoding="utf-8")
    source = source.removeprefix("import Std\n")

    theorem_name = "FormalAutomata.finite_subset_acceptance_preserved"

    with PantographVerifier(
        project_path=project_path,
        imports=["Std"],
    ) as verifier:
        verifier.load_definitions(source)
        result = verifier.inspect_declaration(theorem_name)

    assert result["isUnsafe"] is False
    theorem_type = result["type"]["pp"]
    assert "finiteSubsetDFA" in theorem_type
    assert "A.accepts word" in theorem_type
