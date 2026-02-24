import asyncio
import json
import logging
import os
import tempfile
from datetime import datetime
from uuid import UUID

from .database import SessionLocal
from .models import Statement, User, Comment
from .lean_runner import compile_proof
from .prize import get_prize_settings
from .config import get_settings

logger = logging.getLogger(__name__)


def build_lean_input(statement: Statement, previous_error: str = None, is_disproof: bool = False) -> str:
    """Build the Lean 4 file to send to Aristotle."""
    parts = ["import Mathlib"]
    if previous_error:
        parts.append(f"-- Previous attempt failed: {previous_error}")
    if statement.definitions and statement.definitions.strip():
        parts.append(statement.definitions.strip())
    parts.append(f"def _statement : Prop := {statement.lean_code}")
    target = "¬_statement" if is_disproof else "_statement"
    hint = "" if is_disproof else "-- If the proposition is false, prove ¬_statement instead.\n"
    parts.append(f"{hint}theorem gatekeeper_proof : {target} := by\n  sorry")
    return "\n\n".join(parts) + "\n"


async def attempt_with_aristotle(lean_text: str, api_key: str, deadline: datetime) -> str | None:
    """
    Submit lean_text to Aristotle and poll until COMPLETE/FAILED or deadline.
    Returns solution text if successful, None otherwise.
    """
    tmp_path = None
    try:
        import aristotlelib
        from aristotlelib.project import Project, ProjectStatus  # type: ignore

        if api_key:
            aristotlelib.set_api_key(api_key)

        # No context_file_paths and validate_lean_project_root=False to avoid
        # scanning or uploading any local filesystem paths to Harmonic's servers.
        project = await Project.create(validate_lean_project_root=False)
        await project.solve(input_content=lean_text)

        while True:
            if datetime.utcnow() >= deadline:
                logger.info("Gatekeeper: deadline reached while polling Aristotle")
                return None

            await asyncio.sleep(30)
            await project.refresh()

            logger.info(f"Gatekeeper: Aristotle status = {project.status}")

            if project.status == ProjectStatus.COMPLETE:
                # Use an anonymous temp file so no real project paths are sent
                fd, tmp_path = tempfile.mkstemp(suffix=".lean")
                os.close(fd)
                solution_path = await project.get_solution(output_path=tmp_path)
                solution_text = solution_path.read_text()
                logger.info(f"Gatekeeper: Aristotle solution:\n{solution_text}")
                return solution_text
            elif project.status in (ProjectStatus.FAILED, ProjectStatus.CANCELED):
                return None
            # else keep polling (QUEUED/IN_PROGRESS/UNKNOWN)

    except ImportError:
        logger.warning("aristotlelib not installed; skipping Aristotle attempt")
        return None
    except Exception as e:
        logger.error(f"Gatekeeper: Aristotle error: {e}")
        return None
    finally:
        if tmp_path and os.path.exists(tmp_path):
            os.unlink(tmp_path)


def _extract_proof_parts(solution_text: str) -> tuple[str, str | None]:
    """
    Returns (proof_code, extra_imports) from Aristotle's full solution file.
    - proof_code: everything from 'theorem gatekeeper_proof' onwards
    - extra_imports: any import lines beyond 'import Mathlib' (already added by compile_proof)
    """
    without_header = _strip_aristotle_header(solution_text)

    extra_imports = []
    for line in without_header.splitlines():
        stripped = line.strip()
        if stripped.startswith("import ") and stripped != "import Mathlib":
            extra_imports.append(stripped)

    idx = without_header.find("theorem gatekeeper_proof")
    proof_code = without_header[idx:].strip() if idx != -1 else without_header.strip()
    imports = "\n".join(extra_imports) if extra_imports else None
    return proof_code, imports


def _extract_proof_code(solution_text: str) -> str:
    """Backwards-compat wrapper — returns just the proof code."""
    proof_code, _ = _extract_proof_parts(solution_text)
    return proof_code


def _strip_aristotle_header(code: str) -> str:
    """
    Aristotle prepends a metadata block comment (/-...-/) to the solution.
    This block contains nested ```lean fences that break markdown rendering.
    Strip it so only the actual proof code is displayed in the transcript.
    """
    stripped = code.strip()
    if stripped.startswith("/-"):
        end = stripped.find("\n-/")
        if end != -1:
            return stripped[end + 3:].strip()
    return stripped


def try_compile_solution(statement: Statement, solution_text: str) -> tuple[bool, bool, str | None, str | None]:
    """
    Try to compile Aristotle's solution as a proof or disproof.
    Checks the proof direction first, then disproof.
    Returns (success, is_disproof, error_or_None, imports_or_None).
    """
    proof_code, imports = _extract_proof_parts(solution_text)
    error = None
    for is_disproof in (False, True):
        success, error = compile_proof(
            statement.lean_code,
            proof_code,
            "gatekeeper_proof",
            statement.definitions,
            imports=imports,
            is_disproof=is_disproof,
        )
        if success:
            return True, is_disproof, None, imports
    return False, False, error, imports


def mark_solved_by_gatekeeper(
    db,
    statement: Statement,
    gatekeeper_user: User,
    proof_code: str,
    is_disproof: bool,
    imports: str | None = None,
) -> None:
    """Mark statement as solved by the gatekeeper. No points awarded."""
    statement.is_solved = True
    statement.is_disproved = is_disproof
    statement.solved_at = datetime.utcnow()
    statement.solver_id = gatekeeper_user.id
    statement.proof_code = proof_code
    statement.proof_imports = imports
    statement.proof_theorem_name = "gatekeeper_proof"
    db.commit()


def post_transcript_comment(
    db,
    statement: Statement,
    gatekeeper_user: User,
    chat_log: list,
    holding_period_minutes: int,
) -> None:
    """Post a formatted transcript comment from the gatekeeper user."""
    lines = [
        f"**Automated Prover Transcript** (holding period expired after {holding_period_minutes} minutes)",
        "",
    ]

    for entry in chat_log:
        attempt_num = entry.get("attempt", "?")
        lines.append(f"**Attempt {attempt_num}:**")
        lines.append("")

        lean_code = entry.get("lean")
        if lean_code:
            lines.append("")
            for line in lean_code.strip().splitlines():
                lines.append("    " + line)
            lean_error = entry.get("lean_error")
            if lean_error:
                lines.append("")
                lines.append("Lean error:")
                lines.append("")
                for line in lean_error.strip().splitlines():
                    lines.append("    " + line)
        else:
            reason = entry.get("reason", "Aristotle failed to find a solution.")
            lines.append(reason)

        lines.append("")

    lines.append("This statement is now open for community proofs.")

    content = "\n".join(lines)
    comment = Comment(
        content=content,
        statement_id=statement.id,
        author_id=gatekeeper_user.id,
    )
    db.add(comment)
    db.commit()


async def run_gatekeeper(statement_id: UUID) -> None:
    """
    Main gatekeeper loop. Runs as a background asyncio task.
    Attempts to prove/disprove the statement via Aristotle during the holding period.
    """
    db = SessionLocal()
    try:
        statement = db.query(Statement).filter(Statement.id == statement_id).first()
        if not statement or statement.holding_period_ends_at is None:
            logger.warning(f"Gatekeeper: statement {statement_id} not found or no holding period")
            return

        deadline = statement.holding_period_ends_at
        settings = get_prize_settings(db)
        config = get_settings()

        gatekeeper_username = settings.get("gatekeeper_username", "admin")
        holding_period_minutes = settings.get("holding_period_minutes", 10)
        api_key = config.aristotle_api_key

        logger.info(
            f"Gatekeeper: starting for statement {statement_id}, "
            f"deadline={deadline.isoformat()}, user={gatekeeper_username}"
        )

        chat_log: list = []
        attempt = 0
        previous_error: str | None = None

        while datetime.utcnow() < deadline and not statement.is_solved:
            attempt += 1
            logger.info(f"Gatekeeper: attempt {attempt} for statement {statement_id}")

            lean_text = build_lean_input(statement, previous_error)
            logger.info(f"Gatekeeper: sending to Aristotle (attempt {attempt}):\n{lean_text}")
            solution = await attempt_with_aristotle(lean_text, api_key, deadline)

            # If Aristotle signals negation, re-query explicitly for a disproof
            if solution and "The following was negated by Aristotle" in solution:
                logger.info(f"Gatekeeper: Aristotle signalled negation, re-querying for disproof")
                disproof_text = build_lean_input(statement, previous_error, is_disproof=True)
                logger.info(f"Gatekeeper: sending disproof query to Aristotle (attempt {attempt}):\n{disproof_text}")
                solution = await attempt_with_aristotle(disproof_text, api_key, deadline) or solution

            if solution is None:
                chat_log.append({
                    "attempt": attempt,
                    "status": "failed",
                    "reason": "Aristotle returned no solution",
                })
                previous_error = "Aristotle could not find a solution"
            else:
                success, is_disproof, error, imports = try_compile_solution(statement, solution)
                chat_log.append({
                    "attempt": attempt,
                    "lean": solution,
                    "lean_error": error,
                })

                if success:
                    db.refresh(statement)
                    if statement.is_solved:
                        logger.info(f"Gatekeeper: statement {statement_id} already solved, aborting")
                        return

                    gatekeeper_user = db.query(User).filter(
                        User.username == gatekeeper_username
                    ).first()
                    if not gatekeeper_user:
                        logger.error(f"Gatekeeper: user '{gatekeeper_username}' not found")
                        return

                    mark_solved_by_gatekeeper(db, statement, gatekeeper_user, solution, is_disproof, imports)
                    logger.info(
                        f"Gatekeeper: statement {statement_id} solved "
                        f"({'disproof' if is_disproof else 'proof'})"
                    )
                    return
                else:
                    previous_error = error or "Lean compilation failed"

            # Save chat progress
            statement.gatekeeper_chat = json.dumps(chat_log)
            db.commit()

            # Wait 60s between attempts
            remaining = (deadline - datetime.utcnow()).total_seconds()
            if remaining <= 0:
                break
            await asyncio.sleep(min(60, remaining))

        # Holding period expired without success
        db.refresh(statement)
        if not statement.is_solved:
            gatekeeper_user = db.query(User).filter(
                User.username == gatekeeper_username
            ).first()
            if gatekeeper_user:
                post_transcript_comment(
                    db, statement, gatekeeper_user, chat_log, holding_period_minutes
                )
            logger.info(
                f"Gatekeeper: holding period expired for statement {statement_id}, "
                f"posted transcript with {len(chat_log)} attempt(s)"
            )

    except Exception as e:
        logger.error(f"Gatekeeper: unexpected error for statement {statement_id}: {e}", exc_info=True)
    finally:
        db.close()
