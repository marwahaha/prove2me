import subprocess
import tempfile
import os
from .config import get_settings

settings = get_settings()


def compile_lean(code: str, allow_sorry: bool = True) -> tuple[bool, str]:
    """
    Compile Lean code and return (success, error_message).
    If allow_sorry=False, also check for 'sorry' keyword.
    """
    if not allow_sorry and "sorry" in code:
        return False, "Proof cannot contain 'sorry'"

    with tempfile.NamedTemporaryFile(
        mode='w',
        suffix='.lean',
        delete=False,
        dir=settings.lean_project_path
    ) as f:
        f.write(code)
        f.flush()
        temp_path = f.name

    try:
        result = subprocess.run(
            ['lake', 'env', 'lean', temp_path],
            capture_output=True,
            text=True,
            timeout=settings.lean_timeout,
            cwd=settings.lean_project_path
        )

        if result.returncode == 0:
            return True, ""
        else:
            error = result.stderr or result.stdout
            return False, error
    except subprocess.TimeoutExpired:
        return False, "Compilation timed out"
    except FileNotFoundError:
        return False, "Lean not found. Make sure 'lake' is in PATH and lean_project_path is configured."
    except Exception as e:
        return False, f"Compilation error: {str(e)}"
    finally:
        try:
            os.unlink(temp_path)
        except:
            pass


def compile_statement(statement_code: str) -> tuple[bool, str]:
    """
    Compile a Lean statement (allows sorry).
    """
    return compile_lean(statement_code, allow_sorry=True)


def compile_proof(statement_code: str, proof_code: str) -> tuple[bool, str]:
    """
    Compile statement + proof together (does not allow sorry).
    """
    combined = f"{statement_code}\n\n{proof_code}"
    return compile_lean(combined, allow_sorry=False)
