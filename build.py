#!/usr/bin/env python3
"""Check the pinned toolchain and compile the production _CoqProject in order."""
import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import time
from pathlib import Path


def project_entries(path):
    """Read the project's explicit load paths and ordered compilation units."""
    tokens = shlex.split(path.read_text(), comments=True)
    flags, sources = [], []
    while tokens:
        token = tokens.pop(0)
        if token in ("-Q", "-R") and len(tokens) >= 2:
            flags.extend([token, tokens.pop(0), tokens.pop(0)])
        elif token.endswith(".v") and not token.startswith("-"):
            sources.append(token)
        else:
            raise ValueError(f"Unsupported _CoqProject entry: {token}")
    if not sources:
        raise ValueError("_CoqProject contains no compilation units")
    return flags, sources


def pinned_packages(path):
    """Use the exported switch as the single full dependency-version lock."""
    installed = re.search(r"installed:\s*\[(.*?)\]", path.read_text(), re.S)
    if installed is None:
        raise ValueError("Missing installed package list in switch snapshot")
    return dict(entry.split(".", 1)
                for entry in re.findall(r'"([^\"]+)"', installed.group(1)))


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--switch", default=str(root / ".toolchain"),
                        help="opam switch name or path (default: theories/.toolchain)")
    args = parser.parse_args()
    # Resolve existing local switches before subprocesses change directory.
    switch = str(Path(args.switch).resolve()) if Path(args.switch).exists() else args.switch
    flags, sources = project_entries(root / "_CoqProject")
    expected = pinned_packages(root / "toolchain.opam-switch")
    output_dir = root / ".build"
    output_dir.mkdir(exist_ok=True)
    # Keep opam's own diagnostics in the workspace, alongside our build logs.
    opam_logs = output_dir / "opam-logs"
    opam_logs.mkdir(exist_ok=True)
    build_env = dict(os.environ, OPAMLOGS=str(opam_logs))
    before = {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
              for name in sources}
    report = {"switch": switch, "opam_log_dir": str(opam_logs),
              "sources_sha256": before, "builds": []}
    success = False
    with (output_dir / "build.log").open("w") as log:
        def run(command):
            log.write("$ " + shlex.join(command) + "\n")
            log.flush()
            result = subprocess.run(command, cwd=root, env=build_env,
                                    capture_output=True, text=True)
            log.write(result.stdout + result.stderr)
            log.flush()
            return result

        try:
            installed = run(["opam", "list", "--switch=" + switch, "--installed",
                             "--columns=name,version", "--short", "--color=never"])
            if installed.returncode:
                raise RuntimeError(installed.stdout + installed.stderr)
            actual = dict(line.split() for line in installed.stdout.splitlines() if line.strip())
            mismatches = [f"{name}: expected {version}, found {actual.get(name, 'missing')}"
                          for name, version in expected.items() if actual.get(name) != version]
            if mismatches:
                raise RuntimeError("Toolchain mismatch:\n" + "\n".join(mismatches))
            report["verified_packages"] = expected
            print(f"Verified {len(expected)} pinned package versions.", flush=True)

            # Always rebuild in order: no stale .vo is accepted as validation.
            for source in sources:
                started = time.monotonic()
                result = run(["opam", "exec", "--switch=" + switch, "--",
                              "rocq", "compile", "-q", *flags, source])
                report["builds"].append({"file": source, "exit_code": result.returncode,
                                         "seconds": round(time.monotonic() - started, 3)})
                print(f"{source}: exit {result.returncode}", flush=True)
                if result.returncode:
                    raise RuntimeError((result.stdout + result.stderr)[-6000:])
            success = True
        except (OSError, RuntimeError) as error:
            report["error"] = str(error)
            print(str(error), flush=True)
        finally:
            unchanged = all(before[name] == hashlib.sha256((root / name).read_bytes()).hexdigest()
                            for name in sources)
            report["sources_unchanged"] = unchanged
            report["success"] = success and unchanged
            (output_dir / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Build log: {output_dir / 'build.log'}", flush=True)
    return 0 if report["success"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
