#!/usr/bin/env python3
"""Build and check the memory observation add-on in a new scratch directory."""

import argparse
import csv
import hashlib
import json
import shutil
import statistics
import subprocess
import tempfile
from pathlib import Path


NI = Path(__file__).resolve().parent
ROOT = NI.parent
OPAM = ["opam", "exec", "--switch=genllvm", "--"]


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def copy_sources(source, destination, suffixes):
    for path in sorted(source.rglob("*")):
        if path.is_file() and path.suffix in suffixes:
            target = destination / path.relative_to(source)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)


def verify_diagnostics(stdout, stderr):
    labels = [line.removeprefix("PASS ") for line in stdout.splitlines()]
    if len(labels) != 19 or len(set(labels)) != 19:
        raise RuntimeError("Expected 19 distinct successful fixture runs")
    if any(not line.startswith("PASS ") for line in stdout.splitlines()):
        raise RuntimeError("A fixture did not pass")
    messages = {}
    active = None
    for line in stderr.splitlines():
        if line.startswith("NI_BEGIN "):
            if active is not None:
                raise RuntimeError("Overlapping fixture diagnostics")
            active = line.removeprefix("NI_BEGIN ")
            if active in messages:
                raise RuntimeError("Repeated fixture diagnostics")
            messages[active] = []
        elif line.startswith("NI_END "):
            if active != line.removeprefix("NI_END "):
                raise RuntimeError("Unmatched fixture end")
            active = None
        elif line.startswith("NI_DIAGNOSTIC ") and active is not None:
            messages[active].append(line)
        else:
            raise RuntimeError(f"Unassociated diagnostic: {line}")
    if active is not None or set(messages) != set(labels):
        raise RuntimeError("Missing diagnostic boundaries")
    expected = {
        "bad_load": "Reading from unallocated memory.",
        "bad_store": "Writing to unallocated memory",
        "non_pointer": "Loading from something that isn't an ptress.",
        "failure_prefix": "Reading from unallocated memory.",
        "poison_intrinsic": "Store to poisoned address in va_start.",
        "ub_boundary": "NI fixture UB",
        "oom_prefix": "NI fixture OOM",
        "failure_kind": "NI fixture failure",
        "memory_failure": "convert_impure: addrspacecast unimplemented",
    }
    for label, text in expected.items():
        if len(messages[label]) != 1 or text not in messages[label][0]:
            raise RuntimeError(f"Missing or repeated diagnostic for {label}")
    debug_messages = messages["debug_resume"]
    if len(debug_messages) != 2 or any("NI fixture debug" not in m for m in debug_messages):
        raise RuntimeError("Expected one diagnostic from each Debug fixture run")
    return messages


def summarize_benchmark(path):
    with path.open() as stream:
        rows = list(csv.DictReader(stream))
    result = {}
    for workload in ("memory", "locals"):
        result[workload] = {}
        for method in ("stock", "disabled", "discard", "observed"):
            group = [r for r in rows if r["workload"] == workload and r["method"] == method]
            times = [float(r["seconds"]) for r in group]
            result[workload][method] = {
                "median_seconds": statistics.median(times),
                "min_seconds": min(times),
                "max_seconds": max(times),
                "median_cpu_seconds": statistics.median(float(r["cpu_seconds"]) for r in group),
                "median_allocated_bytes": statistics.median(
                    float(r["allocated_bytes"]) for r in group),
            }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", action="store_true")
    parser.add_argument("--count", type=int, default=2000)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if not 1 <= args.count <= 1_000_000 or args.repeats < 1 or args.jobs < 1:
        parser.error("Use count 1..1000000 and positive repeats/jobs")

    scratch = Path(tempfile.mkdtemp(prefix="genllvm-ni-memory-"))
    logs = scratch / "logs"
    logs.mkdir()
    print(f"Scratch directory: {scratch}", flush=True)
    commands = []

    def run(label, command, cwd, timeout=300):
        print(label, flush=True)
        record = {"label": label, "argv": OPAM + command, "cwd": str(cwd)}
        commands.append(record)
        try:
            with (logs / f"{label}.stdout").open("w") as out, \
                 (logs / f"{label}.stderr").open("w") as err:
                completed = subprocess.run(
                    OPAM + command, cwd=cwd, stdout=out, stderr=err, timeout=timeout)
            record["exit_code"] = completed.returncode
            if completed.returncode != 0:
                raise RuntimeError(f"{label} failed; see {logs / (label + '.stderr')}")
        finally:
            write_json(logs / "commands.json", commands)

    # Copy sources only: no cached .vo files or generated extraction output.
    vsrc = scratch / "vellvm" / "src"
    copy_sources(ROOT / "vellvm" / "src" / "rocq", vsrc / "rocq", {".v"})
    shutil.copy2(ROOT / "vellvm" / "src" / "_RocqProject", vsrc)
    general = scratch / "src" / "rocq"
    general.mkdir(parents=True)
    shutil.copy2(ROOT / "src" / "rocq" / "QCExtractionFix.v", general)
    target = scratch / "ni"
    copy_sources(NI / "rocq", target / "rocq", {".v"})
    copy_sources(NI / "ml", target / "ml", {".ml"})
    shutil.copy2(NI / "_RocqProject", target)
    hashes = {str(p.relative_to(scratch)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted(scratch.rglob("*")) if p.is_file()}
    write_json(logs / "inputs.json", {
        "source_root": str(ROOT), "arguments": vars(args), "sha256": hashes,
        "harness_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "genllvm_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "vellvm_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT / "vellvm", text=True).strip(),
    })
    run("rocq-version", ["rocq", "-v"], target)
    run("ocaml-version", ["ocamlopt", "-version"], target)
    run("packages", ["opam", "list", "--installed", "--columns=name,version"], target)
    run("dependency-makefile", ["rocq", "makefile", "-f", "_RocqProject",
                                "-o", "NIRocqMakefile"], vsrc)
    run("dependencies", ["make", "-f", "NIRocqMakefile", f"-j{args.jobs}",
                         "rocq/Semantics.vo"], vsrc, timeout=900)
    run("extraction-fix", ["rocq", "compile", "-R", "rocq", "GenLLVM",
                           "rocq/QCExtractionFix.v"], general.parent)
    compile_command = ["rocq", "compile", "-R", "rocq", "GenLLVMNI",
                       "-R", "../vellvm/src/rocq", "Vellvm",
                       "-R", "../src/rocq", "GenLLVM"]
    files = [line.strip() for line in (target / "_RocqProject").read_text().splitlines()
             if line.strip().endswith(".v")]
    for name in files + ["rocq/Tests/ExtractMemory.v"]:
        run(Path(name).stem, compile_command + [name], target)
    # Record, rather than conceal, the inherited library assumptions.
    (target / "Assumptions.v").write_text(
        "From GenLLVMNI.Semantics Require Import Preservation.\n"
        "Print Assumptions erase_interpreter_memory_gen.\n")
    run("proof-assumptions", compile_command + ["Assumptions.v"], target)
    native = ["ocamlfind", "ocamlopt", "-w", "-a", "-package", "zarith,unix", "-linkpkg"]
    run("native-checks", native + ["memory_extracted.mli", "memory_extracted.ml",
                                  "ml/memory_checks.ml", "-o", "memory_checks.exe"], target)
    run("fixtures", ["./memory_checks.exe"], target, timeout=60)
    messages = verify_diagnostics((logs / "fixtures.stdout").read_text(),
                                  (logs / "fixtures.stderr").read_text())
    write_json(logs / "diagnostics.json", messages)
    if args.benchmark:
        run("native-benchmark", native + ["memory_extracted.cmx", "ml/memory_bench.ml",
                                          "-o", "memory_bench.exe"], target)
        # This high-water mark covers the complete shared benchmark process;
        # it must not be attributed to an individual method.
        resource_driver = (
            "import json, resource, subprocess, sys\n"
            "subprocess.run(sys.argv[2:], check=True, timeout=240)\n"
            "r = resource.getrusage(resource.RUSAGE_CHILDREN)\n"
            "with open(sys.argv[1], 'w') as out:\n"
            "    json.dump({'max_rss_kib_linux': r.ru_maxrss, "
            "'user_seconds': r.ru_utime, 'system_seconds': r.ru_stime}, out)\n"
        )
        run("benchmark", ["python3", "-c", resource_driver,
                          str(logs / "benchmark-resource.json"), "./memory_bench.exe",
                          str(args.count), str(args.repeats)], target)
        summary = summarize_benchmark(logs / "benchmark.stdout")
        write_json(logs / "benchmark-summary.json", summary)
    print(f"PASS: preservation proofs, 7 runner examples, 19 extracted fixtures; logs: {logs}",
          flush=True)


if __name__ == "__main__":
    main()
