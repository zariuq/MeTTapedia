#!/usr/bin/env python3
"""Exercise the actual native fail-stop path using private link instrumentation.

No production source is changed. All runtime object hashes are checked against
the selected build manifest. The uninjected executable must return every exact
Lean packet; one refused allocation after a client checkpoint must abort and
cannot qualify its partial output as a completed answer. This does not turn a
process signal into a resumable in-process provider fault.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import shlex
import signal
import subprocess
import time


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-manifest", type=Path, required=True)
    parser.add_argument("--cetta-tree", type=Path, required=True)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root, output = args.cetta_tree.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    here = Path(__file__).resolve().parent
    lean_root = here.parents[1]
    oracle = lean_root.parents[1] / "metta/gslt/tools/qualify_inductive_append.lean"
    manifest = args.build_manifest.resolve()
    library = args.library.resolve()
    probe = here / "cetta_allocation_fault_probe.c"
    record = dict(status="running", qualified=False, records=[],
                  started_at=datetime.now(timezone.utc).isoformat())

    def save():
        (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(label, command, *, cwd=lean_root, accepted=True):
        start = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=environment, capture_output=True,
                                text=True, timeout=180)
        (output / f"{label}.out").write_text(result.stdout)
        (output / f"{label}.err").write_text(result.stderr)
        record["records"].append(dict(label=label, returncode=result.returncode,
                                      seconds=round(time.monotonic() - start, 6)))
        save()
        if (result.returncode == 0) != accepted:
            raise RuntimeError(f"{label}: unexpected return code {result.returncode}")
        return result

    environment = dict(os.environ, CETTA_GC="1", CETTA_GC_BUDGET_MB="1",
                       ASAN_OPTIONS="detect_leaks=1:halt_on_error=1",
                       UBSAN_OPTIONS="halt_on_error=1:print_stacktrace=1")
    save()
    try:
        build = json.loads(manifest.read_text())
        if not build.get("qualified") or build.get("status") != "passed":
            raise RuntimeError("native build is not qualified")
        pins = dict(build["inputs"])
        for item in build["objects"]:
            pins[item["command"][-1]] = item["sha256"]
        if pins.get(str(root / "src/atom.c")) != digest(root / "src/atom.c"):
            raise RuntimeError("allocator source differs from the native build")
        pins.update({str(path): digest(path) for path in (Path(__file__).resolve(), manifest, library, probe, oracle)})
        if any(digest(path) != expected for path, expected in pins.items()):
            raise RuntimeError("native build inputs or object hashes changed")
        config = build["configuration"]
        compiler = shlex.split(config["CC"])
        wrapper = output / "allocation-fault.o"
        compiled = run("compile-probe", compiler + shlex.split(config["CPPFLAGS"]) +
            shlex.split(config["CFLAGS"]) + ["-c", str(probe), "-o", str(wrapper)], cwd=root)
        if compiled.stderr:
            raise RuntimeError("fault instrumentation compilation emitted diagnostics")
        link = list(build["link_command"])
        binary = output / "cetta-fault-probe"
        link[link.index("-o") + 1] = str(binary)
        link += [str(wrapper), "-Wl,--wrap=malloc"]
        linked = run("link-probe", link, cwd=root)
        if linked.stderr:
            raise RuntimeError("fault instrumentation link emitted diagnostics")
        run("generate", ["lean", "--run", str(oracle), "emit-lifetime", str(library), "1024", str(output)])
        lines = (output / "array-lifetime.metta").read_text().splitlines()
        insertion = [index for index, line in enumerate(lines) if '"retained-large"' in line]
        if len(insertion) != 1:
            raise RuntimeError("client checkpoint is not uniquely identified")
        lines.insert(insertion[0], '!(println! "ArrayAllocationReady")')
        workload = output / "allocation-failure.metta"
        workload.write_text("\n".join(lines) + "\n")
        pins[str(workload)] = digest(workload)

        def packet_text(text):
            return "\n".join(line for line in text.splitlines()
                if line.strip() not in ('ArrayAllocationReady', '"ArrayAllocationReady"')) + "\n"

        for mode in ("prime", "petta"):
            command = [str(binary), "--lang", mode, "--quiet", str(workload)]
            baseline = run(f"{mode}-uninjected", command)
            if baseline.stderr:
                raise RuntimeError("uninjected runtime emitted diagnostics")
            complete = output / f"{mode}-complete.packets"
            complete.write_text(packet_text(baseline.stdout))
            run(f"{mode}-complete-check", ["lean", "--run", str(oracle), "check-lifetime", "1024", str(complete)])
            started = time.monotonic()
            process = subprocess.Popen(command, cwd=lean_root, env=environment,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            prefix = bytearray()
            armed = False
            try:
                with selectors.DefaultSelector() as selector:
                    selector.register(process.stdout, selectors.EVENT_READ)
                    while time.monotonic() - started < 60:
                        ready = selector.select(timeout=0.25)
                        if ready:
                            chunk = os.read(process.stdout.fileno(), 65536)
                            prefix.extend(chunk)
                            if b"ArrayAllocationReady" in prefix:
                                process.send_signal(signal.SIGUSR2)
                                armed = True
                                break
                            if not chunk:
                                break
                        if process.poll() is not None:
                            break
                if not armed:
                    raise RuntimeError("runtime never reached the allocation checkpoint")
                rest, error = process.communicate(timeout=60)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.communicate()
            text = (bytes(prefix) + rest).decode()
            diagnostic = error.decode()
            (output / f"{mode}-fault.out").write_text(text)
            (output / f"{mode}-fault.err").write_text(diagnostic)
            if (process.returncode != -signal.SIGABRT or
                    re.fullmatch("qualification: allocation refusal injected\\n"
                                 r"fatal: out of memory allocating [0-9]+ bytes\n", diagnostic) is None):
                raise RuntimeError(f"{mode}: actual allocation fault did not follow the expected fail-stop path")
            partial = output / f"{mode}-partial.packets"
            partial.write_text(packet_text(text))
            refused = run(f"{mode}-partial-refused", ["lean", "--run", str(oracle), "check-lifetime", "1024", str(partial)], accepted=False)
            if "missing result packets" not in refused.stdout + refused.stderr:
                raise RuntimeError("partial output failed for an unrelated reason")
            record["records"].append(dict(label=f"{mode}-allocation-fault", returncode=process.returncode,
                seconds=round(time.monotonic() - started, 6), fault_injected=True, completed_packet=False))
        if any(digest(path) != expected for path, expected in pins.items()):
            raise RuntimeError("fault qualification inputs changed")
        record.update(status="passed", qualified=True, inputs=pins, link_command=link,
                      instrumented_binary_sha256=digest(binary), original_binary_sha256=build["binary_sha256"],
                      failure_policy="process terminates; no completed answer; no resumable provider fault",
                      production_source_edited=False)
        print("Prime and PeTTa allocation failures abort; incomplete packets refused; uninjected packets exact")
    except Exception as error:
        record.update(status="failed", error=str(error))
        raise
    finally:
        record["finished_at"] = datetime.now(timezone.utc).isoformat()
        save()


if __name__ == "__main__":
    main()
