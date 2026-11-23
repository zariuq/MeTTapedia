"""Build the existing native packed reader for an exported source grammar."""

from pathlib import Path
import shutil
import subprocess
import time
import json


TOOLS = Path(__file__).resolve().parent
REPO = TOOLS.parents[2]
LEAN = REPO / "lean/mettapedia"


class Commands:
    def __init__(self, work):
        self.work = Path(work)
        self.work.mkdir(parents=True, exist_ok=True)
        self.rows = []

    def run(self, label, arguments, cwd=LEAN, *, input=None, env=None):
        started = time.monotonic()
        with (self.work / f"{label}.out").open("wb") as out, (self.work / f"{label}.err").open("wb") as err:
            result = subprocess.run([str(arg) for arg in arguments], cwd=cwd,
                                    input=input, stdout=out, stderr=err, env=env)
        self.rows.append({"label": label, "seconds": time.monotonic() - started,
                          "exit_code": result.returncode})
        (self.work / "commands.json").write_text(json.dumps(self.rows, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(f"{label} failed; its output is retained in the work directory")
        return self.work / f"{label}.out"


def build_native_reader(host, output, commands, *, selections=False):
    host, output = Path(host).resolve(), Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    native = host / "experiments/gslt2parse_foundation/native"
    sources = [host / name for name in [
        "src/symbol.c", "src/atom.c", "src/binding/frame_identity.c", "src/name_key.c",
        "src/lib_parse_native_grammar.c", "src/gslt_dense_bitset_v1.c", "src/native_sha256.c"]]
    sources += [native / name for name in [
        "finite_horn_gslt_v1.c", "finite_horn_ground_term_v1.c", "parser_pack_abi_v1.c",
        "parser_pack_abi_stream_v1.c", "parser_action_bytecode_v1.c",
        "parser_pack_native_v1.c", "parser_pack_gll_v1.c", "parser_pack_glr_v1.c"]]
    sources.append(TOOLS / "parse_gslt_source.c")
    if (host / "src/scalar_trie.c").is_file():
        sources.append(host / "src/scalar_trie.c")
    compiler = shutil.which("cc")
    if compiler is None:
        raise RuntimeError("a C compiler is required")
    flags = ["-O2", "-std=c11", "-Wall", "-Werror", "-pthread", "-ffunction-sections",
             "-fdata-sections", "-D_POSIX_C_SOURCE=200809L", "-DCETTA_BUILD_WITH_GMP=0",
             "-I" + str(host), "-I" + str(host / "src"), "-I" + str(native)]
    if selections:
        flags.append("-DGSLT_SOURCE_SELECTION=1")
    objects = []
    for index, source in enumerate(sources):
        obj = output / f"parser-{index}.o"
        commands.run(f"cc-{index}", [compiler, *flags, "-c", source, "-o", obj], host)
        objects.append(obj)
    binary = output / "source-reader"
    commands.run("link", [compiler, "-Wl,--gc-sections", "-o", binary, *objects,
                          "-lm", "-pthread", "-ldl"], host)
    headers = [TOOLS / "source_plan_identity.h", host / "native/source_plan_identity_v1.h"]
    if selections:
        headers.append(host / "native/source_family_selection_v1.h")
    return binary, [*sources, *headers]


def compile_pack(host, exported, commands, label):
    host, exported = Path(host).resolve(), Path(exported).resolve()
    presentations = host / "experiments/gslt2parse_foundation/presentations"
    support = ["parserpack/parser_pack_core_v1.metta", "reflection/finite_horn_reflection_v1.metta",
               "compiler/syntax_compiler_v1.metta", "compiler/relational_cfg_lowering_v1.metta",
               "compiler/relational_cfg_link_v1.metta", "compiler/parser_pack_compiler_v1.metta",
               "core/syntax_core_v1.metta", "shared/lookahead_core_v1.metta",
               "shared/ground_relations_v1.metta"]
    for name in support:
        destination = exported / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(presentations / name, destination)
    exporter = host / "experiments/gslt2parse_foundation/prolog/parser_pack_abi_export_v1.pl"
    stream = commands.run(label, ["swipl", "-q", "-f", exporter, "--", exported,
        "source:whole", "closed", "core/syntax_core_v1.metta", "shared/lookahead_core_v1.metta",
        "shared/ground_relations_v1.metta", "source-structural.metta", "source-classes.metta"], host)
    abi = exported / "reader.abi"
    abi.write_bytes(stream.read_bytes())
    start = exported / "reader-start.term"
    start.write_bytes((exported / "source-start.term").read_bytes().rstrip(b"\n"))
    return abi, start, [exporter, *(presentations / name for name in support)]


def parse_source(binary, abi, start, source, forest, commands, label, *, recognize_only=False,
                 selection=None, result_limit=2):
    arguments = [binary, abi, start, source, forest]
    if recognize_only:
        arguments.append("--recognize-only")
    if selection is not None:
        if recognize_only:
            raise ValueError("recognition and selected replay are separate calls")
        arguments.extend(["--select", selection, result_limit])
    output = commands.run(label, arguments)
    lines = output.read_text().splitlines()
    if not lines:
        raise RuntimeError(f"{label}: no parser outcome")
    row = json.loads(lines[0])
    if row["outcome"] in (1, 2):
        raise RuntimeError(f"{label}: unsupported grammar or unfinished recognition")
    if not Path(forest).is_file() or row["forestWireBytes"] != Path(forest).stat().st_size:
        raise RuntimeError(f"{label}: the complete packed forest was not retained")
    if row["selected"] != (selection is not None):
        raise RuntimeError(f"{label}: selected replay differs from its declared policy request")
    return row


def parse_direct_source(binary, exported, source, forest, commands, label, *,
                        recognize_only=False, selected=False, result_limit=2):
    """Run the exported direct plan; no foreign grammar compiler is invoked."""
    exported = Path(exported)
    arguments = [binary, "--direct", exported / "direct-productions.terms",
                 exported / "direct-classes.terms", exported / "direct-start.term", source, forest]
    if recognize_only and selected:
        raise ValueError("recognition and selected replay are separate calls")
    if recognize_only:
        arguments.append("--recognize-only")
    if selected:
        arguments.extend(["--select", exported / "direct-selection.term", result_limit])
    output = commands.run(label, arguments)
    lines = output.read_text().splitlines()
    if not lines:
        raise RuntimeError(f"{label}: no parser outcome")
    row = json.loads(lines[0])
    if row["outcome"] in (1, 2):
        raise RuntimeError(f"{label}: grammar refused or recognition remains unfinished")
    if not Path(forest).is_file() or row["forestWireBytes"] != Path(forest).stat().st_size:
        raise RuntimeError(f"{label}: exported packed forest was not retained")
    if row["selected"] != selected:
        raise RuntimeError(f"{label}: replay differs from the requested selection policy")
    return row


def retained_reader_files(directory):
    """The exact parser artifacts retained by a source/compiler invocation."""
    directory = Path(directory)
    for root in (directory, directory / "reader"):
        grammar = root / "grammar"
        if (grammar / "direct-productions.terms").is_file():
            return [root / "native/source-reader", *(grammar / name for name in
                ("direct-productions.terms", "direct-classes.terms", "direct-start.term", "direct-selection.term"))]
    return [directory / name for name in ("source-reader", "reader.abi", "start.term")]


def retained_reader_arguments(directory, source, forest):
    """Replay a retained direct plan or an existing evidence-bearing ABI pack."""
    files = retained_reader_files(directory)
    if len(files) == 5:
        binary, productions, classes, start, selection = files
        return [binary, "--direct", productions, classes, start, source, forest, "--select", selection, 256]
    binary, abi, start = files
    return [binary, abi, start, source, forest]
