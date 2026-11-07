import os
import pytest


@pytest.mark.pantograph
def test_pantograph_adapter_is_opt_in():
    if os.environ.get("RUN_PANTOGRAPH_TESTS") != "1":
        pytest.skip("Set RUN_PANTOGRAPH_TESTS=1 to enable; adapter API is version-sensitive")
    pytest.importorskip("pantograph")
    from formlang_lean_bridge import PantographVerifier
    verifier = PantographVerifier(project_path=os.environ.get("LEAN_PROJECT_PATH", "."))
    result = verifier.prove_by_decide("2 + 2 = 4")
    assert result is not None
