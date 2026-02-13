import subprocess
import tempfile
import os
import re
import logging
from .config import get_settings

settings = get_settings()
logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO)


def run_lean(code: str) -> tuple[bool, str]:
    """
    Run Lean code and return (success, error_message).
    """
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
        # Determine lake command path
        if settings.lean_bin_path:
            lake_cmd = os.path.join(settings.lean_bin_path, 'lake')
            env = os.environ.copy()
            env['PATH'] = settings.lean_bin_path + ':' + env.get('PATH', '')
        else:
            lake_cmd = 'lake'
            env = None

        logger.info(f"Running Lean: {lake_cmd} env lean {temp_path}")
        logger.info(f"Code:\n{code[:500]}{'...' if len(code) > 500 else ''}")

        # Use Popen to stream output
        process = subprocess.Popen(
            [lake_cmd, 'env', 'lean', temp_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=settings.lean_project_path,
            env=env
        )

        try:
            stdout, stderr = process.communicate(timeout=settings.lean_timeout)

            if stdout:
                for line in stdout.splitlines():
                    logger.info(f"[lean stdout] {line}")
            if stderr:
                for line in stderr.splitlines():
                    logger.info(f"[lean stderr] {line}")

            logger.info(f"Lean finished with return code: {process.returncode}")

            if process.returncode == 0:
                return True, ""
            else:
                error = stderr or stdout
                return False, error

        except subprocess.TimeoutExpired:
            process.kill()
            process.communicate()
            logger.warning("Lean compilation timed out")
            return False, "Compilation timed out"
    except FileNotFoundError:
        return False, "Lean not found. Make sure 'lake' is in PATH and lean_project_path is configured."
    except Exception as e:
        logger.error(f"Compilation error: {str(e)}")
        return False, f"Compilation error: {str(e)}"
    finally:
        try:
            os.unlink(temp_path)
        except:
            pass


def compile_statement(statement_code: str, definitions: str = None) -> tuple[bool, str]:
    """
    Validate a Lean statement:
    1. Must be valid Lean syntax
    2. Must have type Prop

    The user submits a proposition (e.g., "∀ n : Nat, n + 0 = n").
    We wrap it to verify it has type Prop.
    """
    # Build the code with optional definitions
    definitions_block = definitions.strip() + "\n\n" if definitions and definitions.strip() else ""

    wrapped_code = f"""import Mathlib

{definitions_block}-- Verify the statement has type Prop
#check ({statement_code} : Prop)
"""

    success, error = run_lean(wrapped_code)

    if not success:
        # Try to give a cleaner error message
        if "type mismatch" in error.lower() or "expected type" in error.lower():
            return False, "Statement must have type Prop"
        return False, error

    return True, ""


def compile_proof(statement_code: str, proof_code: str, theorem_name: str, definitions: str = None) -> tuple[bool, str]:
    """
    Validate a proof:
    1. Must be valid Lean syntax
    2. Must not contain 'sorry'
    3. The specified theorem must have type exactly matching the statement

    The user submits full Lean code and specifies which theorem proves the statement.
    """
    # Check for sorry in the proof
    if "sorry" in proof_code:
        return False, "Proof cannot contain 'sorry'"

    # Check for axiom declarations - users could cheat by declaring arbitrary axioms
    if re.search(r'\baxiom\b', proof_code):
        return False, "Proof cannot contain axiom declarations"

    # Build the code with optional definitions from the statement
    definitions_block = definitions.strip() + "\n\n" if definitions and definitions.strip() else ""

    # First, compile the user's proof code to make sure it compiles
    # Then check that the theorem has the correct type
    wrapped_code = f"""import Mathlib

{definitions_block}-- User's proof code
{proof_code}

-- The statement (proposition to prove)
def _statement : Prop := {statement_code}

-- Verify the theorem has exactly the type of the statement
#check ({theorem_name} : _statement)
"""

    success, error = run_lean(wrapped_code)

    if not success:
        if "type mismatch" in error.lower():
            return False, f"Theorem '{theorem_name}' does not have the correct type"
        if "unknown identifier" in error.lower() or "unknown constant" in error.lower():
            return False, f"Theorem '{theorem_name}' not found in the proof code"
        return False, error

    return True, ""


def validate_lean_syntax(code: str) -> tuple[bool, str]:
    """
    Just check if Lean code is syntactically valid.
    Used for testing/preview.
    """
    wrapped_code = f"""import Mathlib

{code}
"""
    return run_lean(wrapped_code)
