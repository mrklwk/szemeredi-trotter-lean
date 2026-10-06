#!/usr/bin/env python3
"""Record a Linux build and run the unchanged official Comparator launcher."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent


def output(*command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def main():
    if platform.system() != "Linux":
        raise SystemExit("This verification runner requires Linux.")
    version = output("lean", "--version")
    if "version 4.35.0-rc2," not in version:
        raise SystemExit("Wrong compiler: " + version)
    run = ROOT / "build" / ("linux-" + datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
    run.mkdir(parents=True, exist_ok=False)
    result = {
        "source_commit": output("git", "rev-parse", "HEAD"),
        "source_status_before": output("git", "status", "--porcelain", "--untracked-files=no"),
        "platform": platform.platform(),
        "lean": version,
        "lean_prefix": output("lean", "--print-prefix"),
        "bubblewrap": output("bwrap", "--version"),
        "cache_directory": os.environ.get("MATHLIB_CACHE_DIR"),
        "project_build_directory_existed": (ROOT / ".lake/build").exists(),
        "source_sha256": {
            str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(ROOT.rglob("*.lean")) if ".lake" not in p.parts
        },
        "dependencies": [],
        "stages": [],
        "status": "running",
    }
    for package in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        path = ROOT / ".lake/packages" / package["name"]
        head = output("git", "rev-parse", "HEAD", cwd=path)
        dirty = output("git", "status", "--porcelain", "--untracked-files=no", cwd=path)
        if head != package["rev"] or dirty:
            raise SystemExit("Unpinned or modified dependency: " + package["name"])
        result["dependencies"].append({"name": package["name"], "rev": head, "tracked_changes": dirty})

    def save():
        (run / "result.json").write_text(json.dumps(result, indent=2) + "\n")

    save()
    print("Evidence directory: " + str(run), flush=True)
    stages = [
        ("source-check", [sys.executable, "scripts/check-sources.py"]),
        ("full-build", ["lake", "--no-cache", "--wfail", "build"]),
        ("solution-axioms", ["lake", "env", "lean", "-DwarningAsError=true", "Solution.lean"]),
        ("official-comparator", ["bash", "scripts/verify-comparator.sh"]),
    ]
    for label, command in stages:
        print("Starting " + label, flush=True)
        start = time.monotonic()
        with (run / (label + ".log")).open("w") as log:
            completed = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        result["stages"].append({
            "name": label, "command": command, "exit_code": completed.returncode,
            "seconds": round(time.monotonic() - start, 3),
            "log_sha256": hashlib.sha256((run / (label + ".log")).read_bytes()).hexdigest(),
        })
        save()
        print(label + ": exit " + str(completed.returncode), flush=True)
        if completed.returncode:
            result["status"] = "failed"
            save()
            return completed.returncode
    result["status"] = "passed"
    result["source_status_after"] = output("git", "status", "--porcelain", "--untracked-files=no")
    save()
    print("PASS: full Linux build and official Comparator; inspect recorded kernel results.", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
