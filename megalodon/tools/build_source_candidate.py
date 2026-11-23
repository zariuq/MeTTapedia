#!/usr/bin/env python3
"""Build a private Mathdata source-export candidate using upstream makeopt.

Accept the pinned 1.13 release or a tree already carrying the checked proof
stream prerequisite. Patch private copies; the source tree, its objects and
installed executable are untouched.
Successful compilation is recorded separately from semantic qualification.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shlex
import shutil
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="unpacked Megalodon source with makeopt (default: the local installation)")
    args = parser.parse_args()
    root = args.source_root.resolve()
    out = args.output.resolve()
    if out.exists():
        parser.error("candidate output must be a new directory")
    if not (root / "makeopt").is_file() or not (root / "src/megalodon.ml").is_file():
        parser.error("missing upstream source; unpack the pinned 1.13 release and pass --source-root")
    out.mkdir(parents=True)
    tool_dir = Path(__file__).resolve().parent
    patch = tool_dir / "mathdata-export.patch"
    prerequisite = tool_dir / "checked-proof-stream.patch"
    sources = [root / "makeopt", patch, prerequisite, Path(__file__).resolve(),
               *(root / "src").glob("*.ml"), *(root / "src").glob("*.mli"),
               root / "src/lexer.mll", root / "src/hashbtcstub.c",
               *(root / "secp256k1").rglob("*.h")]
    programs = {}
    for name in ("ocamlopt", "ocamlc", "ocamllex", "patch"):
        program = shutil.which(name)
        if program is None:
            parser.error(f"required program is unavailable: {name}")
        programs[name] = Path(program).resolve()
    sources += list(programs.values())
    inputs = {str(path): digest(path) for path in sources}
    record = dict(built=False, status="running", semantic_qualification=False,
                  inputs=inputs, commands=[],
                  scope="Private compilation of the source producer; toolchain remains trusted")

    def save():
        (out / "build.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(command, **kwargs):
        record["commands"].append(list(map(str, command)))
        result = subprocess.run(list(map(str, command)), cwd=root,
                                text=True, capture_output=True, timeout=300, **kwargs)
        (out / f"build-{len(record['commands']):02}.log").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f"candidate build command {len(record['commands'])} failed")
        return result

    started = time.monotonic()
    save()
    try:
        private = out / "inputs"
        (private / "src").mkdir(parents=True)
        copied = {"src/megalodon.ml", "src/interpret.ml", "src/interpret.mli"}
        for name in copied:
            shutil.copyfile(root / name, private / name)
        basis = [programs["patch"], "-d", private, "-p1", "--fuzz=0", "-i", prerequisite]
        forward = subprocess.run([*basis, "--forward", "--dry-run"], capture_output=True)
        if forward.returncode == 0:
            run([*basis, "--forward", "--batch"])
            record["proof_stream_basis"] = "applied"
        else:
            # A mixed or unknown basis fails here. A reverse dry run does
            # not modify the files or discard prior proof-stream support.
            run([*basis, "--reverse", "--force", "--dry-run"])
            record["proof_stream_basis"] = "already-present"
        main_source = private / "src/megalodon.ml"
        run([programs["patch"], "--silent", "--batch", "--forward", "--fuzz=0", main_source],
            input=patch.read_text())
        run([programs["ocamllex"], "-o", out / "lexer.ml", "src/lexer.mll"])
        recipes = (root / "makeopt").read_text().splitlines()
        c_recipes = [shlex.split(line) for line in recipes if line.startswith("ocamlc -ccopt ")]
        if len(c_recipes) != 1:
            raise RuntimeError("unsupported makeopt C recipe inventory")
        c_command = [programs["ocamlc"], *c_recipes[0][1:], "-o", out / "hashbtcstub.o"]
        run(c_command)
        ocaml_recipes = [shlex.split(line)[1:] for line in recipes if line.startswith("$OCAMLOPT ")]
        if not ocaml_recipes or "-c" in ocaml_recipes[-1]:
            raise RuntimeError("makeopt has no final native link recipe")
        for recipe in ocaml_recipes:
            command = [programs["ocamlopt"]]
            for argument in recipe:
                if argument == "bin":
                    argument = str(out)
                elif argument.startswith("bin/"):
                    argument = str(out / argument[4:])
                elif argument == "src/lexer.ml":
                    argument = str(out / "lexer.ml")
                elif argument in copied:
                    argument = str(private / argument)
                command.append(argument)
            run(command)
        if any(digest(Path(path)) != value for path, value in inputs.items()):
            raise RuntimeError("source or tool inputs changed during compilation")
        record.update(built=True, status="passed", binary=str(out / "megalodon"),
                      binary_sha256=digest(out / "megalodon"),
                      patched_source_sha256=digest(main_source),
                      seconds=round(time.monotonic() - started, 6),
                      compiler_version=run([programs["ocamlopt"], "-version"]).stdout.strip())
        print(json.dumps({key: record[key] for key in
                          ("built", "semantic_qualification", "binary_sha256", "seconds")}))
    except (OSError, subprocess.SubprocessError, RuntimeError) as error:
        record.update(status="failed", error=str(error))
        raise
    finally:
        save()


if __name__ == "__main__":
    main()
