#!/usr/bin/env python3
"""Reproduce JSP539's pinned build, literal statements, axioms and declaring-module replay.

Python 3.10+ and the already installed fixed Elan toolchain are required.
This script does not install software, repair sources, upload or publish results.
Lake may retrieve locked dependencies. Use --cache for the optional official
Mathlib cache command recorded in the original successful dependency setup.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time


TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
LEAN_VERSION = "4.35.0-rc3"
MATHLIB_REV = "2a885768dae569d938bb9ff3474da6a8753bb90a"
DEPENDENCY_REVISIONS = {
    "mathlib": "2a885768dae569d938bb9ff3474da6a8753bb90a",
    "plausible": "b7fb2b866d25bd937a2069931f9733197521cb27",
    "LeanSearchClient": "c35806f43135ab3f254429d0c00bd13fc0123f77",
    "importGraph": "103cd9a46972ee39d9defb2f54ae49823b1228eb",
    "proofwidgets": "87dfe779d5dfd03142ee4fe158911b8eb553ec98",
    "aesop": "a92ed98e694702934d40d12f24a1a449144db43e",
    "Qq": "37b0ba0b26109cf9f9c541f0f9557e50cfa1a3b9",
    "batteries": "950339ce0fd0cc0673a22d87036075737586aed2",
    "Cli": "843844fa601dd56767b1eb22b7ada5b64d5e567a",
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_TARGETS = (
    "audit_literal_exact_design_unbounded_real",
    "audit_literal_original_block_design_real",
    "audit_literal_family_formulation_real",
)
SOURCE_AXIOM_TARGETS = (
    "JSP539.exists_bad_fin_design",
    "JSP539.OriginalScope.erdos_664",
    "JSP539.OriginalScope.two_fifths",
    "JSP539.OriginalScope.two_fifths_exact_pairs",
    "JSP539.OriginalScope.block_design",
    "JSP539.exists_bad_fin_design_real",
    "JSP539.OriginalScope.erdos_664_real",
    "JSP539.OriginalScope.block_design_real",
)
KERNEL_MODULES = (
    "JSP539.RandomRestriction",
    "JSP539.OriginalScope",
    "JSP539.RealScope",
)
EXPECTED_PROCESSES_WITHOUT_CACHE = 25

# Optional official cache of the complete pinned Mathlib import closure.
CACHE_MODULES = ("Mathlib",)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_snapshot(project: Path) -> dict[str, str]:
    """Active root/library Lean files and all project build/lock inputs."""
    paths = set()
    for directory, dirs, names in os.walk(project, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".lake", ".git", "__pycache__", "verification_logs"}]
        for name in names:
            path = Path(directory) / name
            if path.suffix == ".lean" or name in {"lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json"}:
                paths.add(path)
    return {path.relative_to(project).as_posix(): sha256(path.read_bytes()) for path in sorted(paths)}


def default_project() -> Path | None:
    script_dir = Path(__file__).resolve().parent
    for candidate in (script_dir, script_dir.parent, Path.cwd()):
        if (candidate / "lean-toolchain").is_file() and (candidate / "JSP539.lean").is_file():
            return candidate
    return None


def axiom_audit(output: str, expected_targets=AXIOM_TARGETS) -> dict:
    rows = re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    by_name: dict[str, list[list[str]]] = {}
    reported_expressions: dict[str, list[list[str]]] = {}
    def constant_name(expression: str) -> str:
        return re.sub(r"\.\{[^{}]*\}$", "", expression.strip())
    for name, body in rows:
        name = constant_name(name)
        expressions = [token.strip() for token in body.split(",") if token.strip()]
        axioms = [constant_name(token) for token in expressions]
        by_name.setdefault(name, []).append(axioms)
        reported_expressions.setdefault(name, []).append(expressions)
    empty_rows = re.findall(r"'([^']+)'\s+does not depend on any axioms", output)
    for name in empty_rows:
        name = constant_name(name)
        by_name.setdefault(name, []).append([])
        reported_expressions.setdefault(name, []).append([])
    issues = []
    for name in expected_targets:
        matches = by_name.get(name, [])
        if len(matches) != 1:
            issues.append(f"Expected exactly one actual axiom report for {name}; got {len(matches)}")
        elif not set(matches[0]).issubset(STANDARD_AXIOMS) or len(matches[0]) != len(set(matches[0])):
            issues.append(f"Unexpected axiom dependencies for {name}: {matches[0]}")
    extras = sorted(set(by_name) - set(expected_targets))
    if extras:
        issues.append(f"Unexpected theorem axiom reports: {extras}")
    return {"status": "PASSED" if not issues else "FAILED", "expected_reports": len(expected_targets),
            "actual_reports": len(rows) + len(empty_rows), "reports": by_name,
            "reported_axiom_expressions": reported_expressions, "issues": issues}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path,
                        help="Extracted project root; default: project beside this script, its parent, or cwd")
    parser.add_argument("--threads", type=int, default=2,
                        help="LEAN_NUM_THREADS for whole build (default: 2)")
    parser.add_argument("--check-threads", type=int, default=1,
                        help="LEAN_NUM_THREADS for version/cache/checker/replay (default: 1)")
    parser.add_argument("--cache", action="store_true",
                        help="Download the official cache for the pinned Mathlib import closure before building")
    parser.add_argument("--log-root", type=Path,
                        help="Output directory; default: PROJECT/verification_logs, with a new directory per run")
    args = parser.parse_args()  # --help ends here, before Lean/network/project access.
    if sys.version_info < (3, 10):
        parser.error("Python 3.10 or later is required")
    if args.threads < 1 or args.check_threads < 1:
        parser.error("Thread counts must be positive")
    selected = args.project if args.project is not None else default_project()
    if selected is None:
        parser.error("Could not locate the extracted project; pass --project PATH")
    project = selected.resolve()
    required = ("lean-toolchain", "lakefile.lean", "lake-manifest.json", "JSP539.lean",
                "LicensedContainers.lean", "Verify.lean", "VerifyOriginalStatement.lean",
                "JSP539/RandomRestriction.lean", "JSP539/OriginalScope.lean", "JSP539/RealScope.lean")
    absent = [name for name in required if not (project / name).is_file()]
    if absent:
        parser.error("Missing project inputs: " + ", ".join(absent))
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="backslashreplace")

    log_root = args.log_root.resolve() if args.log_root is not None else project / "verification_logs"
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    logs = log_root / stamp
    logs.mkdir(parents=True, exist_ok=False)
    summary_path = logs / "verification.json"
    before = source_snapshot(project)
    state = {
        "status": "RUNNING", "started_utc": utc_now(), "project": str(project),
        "script_sha256": sha256(Path(__file__).read_bytes()),
        "fixed_toolchain": TOOLCHAIN, "fixed_mathlib_rev": MATHLIB_REV,
        "fixed_dependency_revisions": DEPENDENCY_REVISIONS,
        "elan_install_flag": "Not used; elan run requires the fixed toolchain to be already installed",
        "build_threads": args.threads, "check_threads": args.check_threads,
        "official_cache_requested": args.cache, "lake_cache_present_at_start": (project / ".lake").exists(),
        "steps": [], "sources_before": before,
        "kernel_replay_scope": "Replay the three declaring modules RandomRestriction, OriginalScope and RealScope using their imported environments; no --fresh; unsafe/partial declarations skipped and axiom declarations permitted by leanchecker; eight actual source and three literal-wrapper axiom reports required",
        "expected_axiom_reports": {"source": len(SOURCE_AXIOM_TARGETS), "literal": len(AXIOM_TARGETS), "total": len(SOURCE_AXIOM_TARGETS) + len(AXIOM_TARGETS)},
        "expected_kernel_modules": list(KERNEL_MODULES),
        "expected_process_count": EXPECTED_PROCESSES_WITHOUT_CACHE + int(args.cache),
        "verification_scope": "Observed natural process exits, all nine fixed dependency pins and clean checkouts, actual source/literal axiom checks and three declaring-module replays; no software installation or publication",
    }

    def save() -> None:
        temporary = summary_path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        temporary.replace(summary_path)

    def run(label: str, lake_args: list[str], threads: int, *, use_lake: bool = True,
            use_elan: bool = True) -> dict:
        command = (["elan", "run", TOOLCHAIN] + (["lake"] if use_lake else []) + lake_args
                   if use_elan else lake_args)
        number = len(state["steps"]) + 1
        text_path = logs / f"{number:02d}-{label}.log"
        raw_path = logs / f"{number:02d}-{label}.raw"
        record = {"label": label, "command": command, "cwd": str(project),
                  "lean_num_threads": threads, "started_utc": utc_now(),
                  "status": "RUNNING", "log": text_path.name, "raw_log": raw_path.name,
                  "natural_returncode": None, "forced_termination": False}
        state["steps"].append(record)
        save()
        environment = dict(os.environ, LEAN_NUM_THREADS=str(threads), PYTHONUTF8="1")
        process = None
        started = time.monotonic()
        interrupted = False

        def stop_started_process() -> None:
            if process is None:
                return
            if process.poll() is None:
                record["forced_termination"] = True
                if os.name == "nt":
                    cleanup_command = ["taskkill", "/PID", str(process.pid), "/T", "/F"]
                    try:
                        cleanup = subprocess.run(cleanup_command, stdout=subprocess.PIPE,
                                                 stderr=subprocess.STDOUT, timeout=10, check=False)
                        record["process_tree_cleanup"] = {
                            "command": cleanup_command, "returncode": cleanup.returncode,
                            "output": cleanup.stdout.decode("utf-8", errors="backslashreplace")}
                    except (OSError, subprocess.TimeoutExpired) as error:
                        record["process_tree_cleanup_error"] = str(error)
                    if process.poll() is None:
                        try:
                            process.terminate()
                        except OSError:
                            pass
                else:
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    if os.name != "nt":
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    elif process.poll() is None:
                        process.kill()
                    process.wait()
            else:
                process.wait()
            record["returncode"] = process.returncode

        try:
            with text_path.open("w", encoding="utf-8", newline="") as text_log, raw_path.open("wb") as raw_log:
                process = subprocess.Popen(command, cwd=project, env=environment,
                                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                           start_new_session=(os.name != "nt"))
                assert process.stdout is not None
                for raw_line in iter(process.stdout.readline, b""):
                    raw_log.write(raw_line)
                    raw_log.flush()
                    line = raw_line.decode("utf-8", errors="backslashreplace")
                    text_log.write(line)
                    text_log.flush()
                    print(line, end="", flush=True)
                code = process.wait()  # No timeout or fabricated exit code.
                record.update(natural_returncode=code, returncode=code,
                              status="PASSED" if code == 0 else "FAILED")
        except KeyboardInterrupt:
            interrupted = True
            record.update(status="INTERRUPTED", error="Interrupted by operator")
            stop_started_process()
        except OSError as error:
            record.update(status="EXECUTION_ERROR", error=str(error),
                          returncode=process.returncode if process is not None else None)
            stop_started_process()
        finally:
            record.update(ended_utc=utc_now(), elapsed_seconds=time.monotonic() - started)
            if process is not None and process.stdout is not None:
                process.stdout.close()
            for key, path in (("log_sha256", text_path), ("raw_log_sha256", raw_path)):
                if path.is_file():
                    record[key] = sha256(path.read_bytes())
            record["utf8_log_identical_to_raw"] = record.get("log_sha256") == record.get("raw_log_sha256")
            save()
        if interrupted:
            raise KeyboardInterrupt
        return record

    def require_process(record: dict) -> None:
        if record.get("natural_returncode") != 0 or record["status"] != "PASSED":
            raise RuntimeError(f"{record['label']} failed: status={record['status']}, returncode={record.get('returncode')}; see {record['log']}")

    save()
    result = 1
    try:
        declared = (project / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
        if declared != TOOLCHAIN:
            raise RuntimeError(f"lean-toolchain mismatch: {declared}; expected {TOOLCHAIN}")
        manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8-sig"))
        state["declared_toolchain"] = declared
        state["dependency_manifest"] = manifest
        packages = manifest.get("packages", [])
        actual_revisions = {package.get("name"): package.get("rev") for package in packages}
        if len(packages) != len(DEPENDENCY_REVISIONS) or actual_revisions != DEPENDENCY_REVISIONS:
            raise RuntimeError("Dependency manifest does not match all nine fixed verified revisions")
        for package in packages:
            if package.get("type") != "git" or not re.fullmatch(r"[0-9a-fA-F]{40}", package.get("rev", "")):
                raise RuntimeError(f"Dependency is not locked to a full Git revision: {package.get('name')}")
        if shutil.which("elan") is None:
            raise RuntimeError("elan is not on PATH; install/configure it separately before verification")
        version = run("lean-version", ["lean", "--version"], args.check_threads, use_lake=False)
        require_process(version)
        version_text = (logs / version["log"]).read_text(encoding="utf-8")
        state["actual_lean_version_output"] = version_text
        if not re.search(r"\bversion\s+" + re.escape(LEAN_VERSION) + r"(?:,|\s|\))", version_text):
            raise RuntimeError("Executed Lean version differs from the fixed release")
        if args.cache:
            cache = run("official-mathlib-cache", ["exe", "cache", "get", *CACHE_MODULES], args.check_threads)
            require_process(cache)
        build = run("whole-project-build", ["--rehash", "build", "JSP539", "LicensedContainers"], args.threads)
        require_process(build)
        if manifest.get("packagesDir") != ".lake/packages":
            raise RuntimeError("Unexpected dependency directory in the fixed manifest")
        state["dependency_checkout_audit"] = {"status": "RUNNING", "packages": []}
        for name, expected_revision in DEPENDENCY_REVISIONS.items():
            directory = project / ".lake" / "packages" / name
            checkout = {"name": name, "expected_revision": expected_revision,
                        "directory": str(directory), "status": "RUNNING"}
            state["dependency_checkout_audit"]["packages"].append(checkout)
            head = run(f"dependency-{name}-HEAD", ["git", "-C", str(directory), "rev-parse", "HEAD"],
                       args.check_threads, use_elan=False)
            require_process(head)
            checkout["actual_revision"] = (logs / head["log"]).read_text(encoding="utf-8").strip()
            clean = run(f"dependency-{name}-tracked-status",
                        ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=all"],
                        args.check_threads, use_elan=False)
            require_process(clean)
            checkout["tracked_status_output"] = (logs / clean["log"]).read_text(encoding="utf-8")
            checkout["head_matches_pin"] = checkout["actual_revision"] == expected_revision
            checkout["tracked_clean"] = not checkout["tracked_status_output"].strip()
            checkout["status"] = "PASSED" if checkout["head_matches_pin"] and checkout["tracked_clean"] else "FAILED"
            save()
            if checkout["status"] != "PASSED":
                raise RuntimeError(f"Dependency {name}: HEAD differs from the fixed revision or tracked files are modified")
        state["dependency_checkout_audit"]["status"] = "PASSED"
        save()
        source_axioms = run("actual-source-statements-and-axioms", ["env", "lean", "Verify.lean"], args.check_threads)
        require_process(source_axioms)
        state["source_axiom_audit"] = axiom_audit((logs / source_axioms["log"]).read_text(encoding="utf-8"), SOURCE_AXIOM_TARGETS)
        save()
        if state["source_axiom_audit"]["status"] != "PASSED":
            raise RuntimeError("; ".join(state["source_axiom_audit"]["issues"]))
        statements = run("literal-statements-and-axioms", ["env", "lean", "VerifyOriginalStatement.lean"], args.check_threads)
        require_process(statements)
        state["literal_axiom_audit"] = axiom_audit((logs / statements["log"]).read_text(encoding="utf-8"), AXIOM_TARGETS)
        save()
        if state["literal_axiom_audit"]["status"] != "PASSED":
            raise RuntimeError("; ".join(state["literal_axiom_audit"]["issues"]))
        state["declaration_module_replays"] = []
        for module in KERNEL_MODULES:
            replay = run("kernel-replay-" + module.replace(".", "-"),
                         ["env", "leanchecker", "--verbose", module], args.check_threads)
            require_process(replay)
            replay_text = (logs / replay["log"]).read_text(encoding="utf-8")
            observed = bool(re.search(r"^replaying " + re.escape(module) + r"\s*$", replay_text, re.M))
            state["declaration_module_replays"].append({"module": module, "natural_returncode": replay["natural_returncode"], "marker_observed": observed})
            save()
            if not observed:
                raise RuntimeError(f"leanchecker exited zero but no actual 'replaying {module}' output was observed")
        if len(state["steps"]) != state["expected_process_count"]:
            raise RuntimeError("Observed verification process count differs from the complete plan")
        if any(step.get("natural_returncode") != 0 or step.get("forced_termination") for step in state["steps"]):
            raise RuntimeError("Every completed verification process must have a natural zero exit")
        state["sources_after"] = source_snapshot(project)
        state["sources_unchanged_during_run"] = before == state["sources_after"]
        if not state["sources_unchanged_during_run"]:
            raise RuntimeError("Active proof/build/lock sources changed during verification")
        state["status"] = "PASSED"
        result = 0
    except KeyboardInterrupt:
        state.update(status="INTERRUPTED", reason="Interrupted by operator; verification incomplete")
        result = 130
    except (OSError, ValueError, RuntimeError) as error:
        state.update(status="FAILED", reason=str(error))
    finally:
        if "sources_after" not in state:
            try:
                state["sources_after"] = source_snapshot(project)
                state["sources_unchanged_during_run"] = before == state["sources_after"]
            except OSError as error:
                state["source_snapshot_error"] = str(error)
        state["observed_process_count"] = len(state["steps"])
        state["observed_natural_exit_count"] = sum(step.get("natural_returncode") is not None for step in state["steps"])
        state["observed_natural_zero_exit_count"] = sum(step.get("natural_returncode") == 0 for step in state["steps"])
        state["observed_forced_termination_count"] = sum(bool(step.get("forced_termination")) for step in state["steps"])
        state["ended_utc"] = utc_now()
        save()
    print(f"\nVerification status: {state['status']}\nEvidence: {summary_path}")
    return result


if __name__ == "__main__":
    raise SystemExit(main())
