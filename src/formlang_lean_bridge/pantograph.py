from __future__ import annotations

from pathlib import Path
from typing import Any


class VerificationUnavailable(RuntimeError):
    """PyPantograph is missing or its Lean server could not be started."""


class PantographVerifier:
    """
    Small optional adapter around PyPantograph.

    PyPantograph is not a hard dependency. The constructor and goal API should
    be checked against the installed upstream release; the package's README
    links to the upstream project and documents this adapter's narrow scope.
    """

    def __init__(
        self,
        project_path: str | Path = ".",
        imports: list[str] | None = None,
    ) -> None:
        try:
            from pantograph.server import Server
        except ImportError as exc:
            raise VerificationUnavailable(
                "PyPantograph is not installed. See "
                "https://github.com/stanford-centaur/PyPantograph"
            ) from exc

        self.project_path = Path(project_path).resolve()
        self.imports = ["Init"] if imports is None else imports
        try:
            self._server = Server(
                imports=self.imports,
                project_path=str(self.project_path),
            )
        except Exception as exc:
            raise VerificationUnavailable(
                f"Could not initialize PyPantograph: {exc}"
            ) from exc

        self._closed = False

    def load_definitions(self, source: str) -> None:
        """Load Lean definitions into the Pantograph environment."""
        try:
            self._server.load_definitions(source)
        except Exception as exc:
            raise VerificationUnavailable(
                f"Could not load Lean definitions: {exc}"
            ) from exc

    def inspect_declaration(self, name: str) -> dict[str, Any]:
        """Inspect a Lean declaration and return its type and metadata."""
        try:
            return self._server.env_inspect(name)
        except Exception as exc:
            raise VerificationUnavailable(
                f"Could not inspect Lean declaration {name!r}: {exc}"
            ) from exc

    def close(self) -> None:
        """Shut down the underlying Lean server."""
        if not self._closed:
            self._server.__exit__(None, None, None)
            self._closed = True

    def __enter__(self) -> PantographVerifier:
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        if not self._closed:
            self._server.__exit__(exc_type, exc_val, exc_tb)
            self._closed = True

    def prove_by_decide(self, proposition: str) -> Any:
        """Ask Lean to solve a proposition using `decide`."""
        try:
            state = self._server.goal_start(proposition)
            return self._server.goal_tactic(state, tactic="decide")
        except Exception as exc:
            raise VerificationUnavailable(
                f"PyPantograph could not prove the proposition: {exc}"
            ) from exc
