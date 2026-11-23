#!/usr/bin/env python3
"""Export untrusted native source/AST candidates for independent Lean admission.

The original parser, typed source admission and every candidate are checked by
Lean.  Hashes identify the physical inputs; they do not prove their semantics.
This exporter never writes or changes production native source.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

from generate_vibe_itp_binary_scan import REPLAY_BLOCK_ROWS
from generate_vibe_itp_binary_source import character_definitions
from vibe_itp_source_slices import (
    GuestSourceSlices,
    SLICE_FILE,
    VIEW_IMPORTS,
    assembly_theorem,
    component_span,
    snapshot_identity,
)

LEAN_ROOT = Path(__file__).resolve().parents[1]
NATIVE_ROOT = LEAN_ROOT.parents[2] / "hyperon/cetta-prime-nik-20260811"
DESTINATION = LEAN_ROOT / "Mettapedia/GSLT/LanguageDef"
NAMESPACE = "Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot"
OUTPUT = DESTINATION / "NativeOpsSourceGuestSnapshot.lean"
OPERATION_VIEWS = ("sourceChars", "leadingChars", "componentChars", "trailingChars")


def q(value):
    return json.dumps(value, ensure_ascii=False)


def seq(values):
    return "[" + ", ".join(values) + "]"


def ty(value):
    if value.element is not None:
        return f"(.{value.kind} {ty(value.element)})"
    return {"unit": ".unit", "u64": ".word", "byte": ".byte", "bool": ".bool"}.get(
        value.kind, "(.named " + q(value.kind) + ")")


def parameter(value):
    return "{ name := %s, type := %s }" % (q(value.name), ty(value.type))


def header(value):
    return "{ name := %s, parameters := %s, result := %s }" % (
        q(value.name), seq(parameter(p) for p in value.parameters), ty(value.result))


def opaque(value):
    return "{ name := %s, cType := %s, includeHeader := %s }" % (
        q(value.name), q(value.c_type), q(value.header))


def external(value):
    return "{ header := %s, cSymbol := %s, effect := .%s, includeHeader := %s }" % (
        header(value), q(value.c_symbol), value.effect,
        "none" if value.header is None else "some " + q(value.header))


WORD_OPERATORS = {name: ".word ." + name for name in
                  "add sub mul div mod shl shr band bor bxor".split()}
COMPARISONS = {name: ".compare ." + name for name in "eq ne lt le gt ge".split()}
UNARIES = {"not": "not", "bnot": "complement", "to-u64": "toWord", "to-byte": "toByte"}


def expression(value):
    tag, args = value.tag, value.args
    if tag in {"u64", "byte"}:
        width = 64 if tag == "u64" else 8
        return f"(.{'word' if width == 64 else 'byte'} (NativeWord64.bounded {width} {args[0]}))"
    if tag == "bool":
        return "(.bool " + str(args[0]).lower() + ")"
    if tag == "var":
        return "(.variable " + q(args[0]) + ")"
    if tag in {"zero", "null", "new"}:
        return f"(.{tag} {ty(args[0])})"
    if tag == "new-array":
        return f"(.newArray {ty(args[0])} {expression(args[1])})"
    if tag == "field":
        return f"(.field {expression(args[0])} {q(args[1])})"
    if tag in {"index", "slice"}:
        return f"(.{tag} " + " ".join(expression(a) for a in args) + ")"
    if tag in {"length", "address", "load"}:
        return f"(.{tag} {expression(args[0])})"
    if tag == "call":
        return f"(.call {q(args[0])} {seq(expression(a) for a in args[1])})"
    if tag in UNARIES:
        return f"(.unary .{UNARIES[tag]} {expression(args[0])})"
    operation = WORD_OPERATORS.get(tag) or COMPARISONS.get(tag) or {"and": ".and", "or": ".or"}.get(tag)
    if operation is None:
        raise ValueError(f"unrecognized frozen compiler expression tag {tag}")
    return f"(.binary ({operation}) {expression(args[0])} {expression(args[1])})"


def statements(body):
    return seq(statement(value) for value in body)


def statement(value):
    tag, args = value.tag, value.args
    if tag == "let":
        return f"(.declare {q(args[0])} {ty(args[1])} {expression(args[2])})"
    if tag == "set":
        return f"(.set {expression(args[0])} {expression(args[1])})"
    if tag == "if":
        return f"(.branch {expression(args[0])} {statements(args[1])} {statements(args[2])})"
    if tag == "while":
        return f"(.while {expression(args[0])} {statements(args[1])})"
    if tag == "switch":
        cases = seq(f"(NativeWord64.bounded 64 {word}, {statements(body)})" for word, body in args[1])
        return f"(.switch {expression(args[0])} {cases} {statements(args[2])})"
    if tag in {"break", "continue"}:
        return "." + tag
    if tag in {"effect", "free"}:
        return f"(.{tag} {expression(args[0])})"
    if tag == "return":
        return "(.return " + ("none" if args[0] is None else "(some " + expression(args[0]) + ")") + ")"
    if tag == "block":
        return f"(.block {statements(args[0])})"
    raise ValueError(f"unrecognized frozen compiler statement tag {tag}")


def source_expression(value, StringLiteral):
    if isinstance(value, tuple):
        return ".list " + seq(source_expression(child, StringLiteral) for child in value)
    if isinstance(value, StringLiteral):
        token = json.dumps(value.text, ensure_ascii=False)
    elif isinstance(value, int):
        token = str(value)
    else:
        token = value.text
    return ".atom " + q(token)


def identifier_certificate(theorem_name, source, encoded):
    characters = source.replace("_", "_u_").replace("-", "_h_")
    lines = [f"theorem {theorem_name} : cIdentifier {q(source)} = {q(encoded)} := by"]
    if characters == encoded:
        lines += [f"  exact cIdentifier_of_characters {q(source)} {q(encoded)} (by rfl) (by decide +kernel)"]
    else:
        if encoded != "gslt_keyword_" + characters:
            raise ValueError("compiler identifier differs from admitted character encoding")
        lines += [f"  rw [cIdentifier_of_keyword_characters {q(source)} {q(characters)} (by rfl) (by decide +kernel)]",
                  "  apply String.toList_injective", "  simp only [String.toList_append]", "  rfl"]
    return lines + [""]


def render(native, source, catalogue_path, slices: GuestSourceSlices | None = None):
    sys.path.insert(0, str(native / "tools"))
    from compile_gslt_native_ops_v1 import catalogue, compile_source, c_identifier
    from gslt2parse_schema_v1 import parse_sexprs, Symbol, StringLiteral
    text = slices.text if slices is not None else source.read_text(encoding="utf-8")
    parsed = parse_sexprs(text)
    if len(parsed) != 1:
        raise ValueError("expected exactly one authored source form")
    whole = parsed[0]
    if not isinstance(whole, tuple):
        raise ValueError("native source must be a form")
    if whole[0] == Symbol("gslt-native-guest-v1"):
        components = [component[1] for component in whole[2:]
                      if isinstance(component, tuple) and component[0] == Symbol("operations")]
        if len(components) != 1:
            raise ValueError("expected exactly one operational component")
        syntax = components[0]
    else:
        if slices is not None:
            raise ValueError("shared slices require a native guest package")
        syntax = whole
    if syntax[0] != Symbol("gslt-native-ops-v1"):
        raise ValueError("expected native operations root")
    start, end = component_span(text, text.index("(gslt-native-ops-v1"))
    component = text[start:end]
    if parse_sexprs(component) != [syntax]:
        raise ValueError("verbatim component differs from selected source syntax")
    # The text certificates retain exact quoted token spelling. Current required
    # source uses literal ASCII catalogue names without escaped spellings.
    if ";" in component or "\\" in component:
        raise ValueError("candidate text exporter requires a comment-free component without escapes")
    projected = native / "langdef/vibe-itp/vibe_itp_native_kernel_v1.metta"
    if parse_sexprs(projected.read_text()) != [syntax]:
        raise ValueError("operational projection differs from the authored component")
    module = compile_source(projected, catalogue_path)
    catalogue_opaques, catalogue_externs, _ = catalogue(catalogue_path)
    declarations = syntax[2:]
    if slices is None:
        character_views = [
            *character_definitions("componentChars", component),
            *character_definitions("sourceChars", text),
            *character_definitions("leadingChars", text[:start]),
            *character_definitions("trailingChars", text[end:]),
        ]
        factorization = [
            "theorem source_character_factorization : sourceChars =",
            "    leadingChars ++ componentChars ++ trailingChars := by rfl", "",
        ]
    else:
        if (start, end) != slices.operations:
            raise ValueError("operational span differs from shared source view")
        character_views = slices.render_views(OPERATION_VIEWS, slices.operations)
        factorization = assembly_theorem("source_character_factorization", OPERATION_VIEWS)
    lines = [
        "import Mettapedia.GSLT.LanguageDef.NativeOpsDeclarationReplay",
        *(VIEW_IMPORTS if slices is not None else []),
        "import Mettapedia.GSLT.LanguageDef.NativeOpsAdmissionLaws",
        "", "/-! Verbatim source and untrusted AST candidates. Generated by",
        "`scripts/gen_native_ops_source_snapshot.py`; independent checks live alongside. -/", "",
        "set_option autoImplicit false", "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 4000000", "set_option Elab.async false", "",
        "namespace " + NAMESPACE, "", "open NativeOps", "",
        *character_views,        "def componentText : String := String.ofList componentChars",
        "def sourceText : String := String.ofList sourceChars",
        "def leadingText : String := String.ofList leadingChars",
        "def trailingText : String := String.ofList trailingChars", "",
        "def primitiveCatalogue : Catalogue := {", "  opaques := " + seq(opaque(o) for o in catalogue_opaques.values()),
        "  externals := " + seq(external(e) for e in catalogue_externs.values()), "}", "",
        "def expectedInterface : Interface := {",
        "  records := " + seq("{ name := %s, fields := %s }" % (q(name), seq(parameter(p) for p in fields))
                                 for name, fields in module.records.items()),
        "  opaques := " + seq(opaque(o) for o in module.opaques.values()),
        "  functions := " + seq(header(f) for f in module.functions.values()),
        "  externals := " + seq(external(e) for e in module.externs.values()), "}", "",
    ]
    lines += identifier_certificate("module_identifier_exact", module.name, c_identifier(module.name))
    function_indexes = []
    for index, declaration in enumerate(declarations):
        name = declaration[1].text
        tag = declaration[0].text
        sid = f"{index:03d}"
        lines.append(f"def syntax_{sid} : Algorithms.MeTTa.Simple.Parser.SExpr := " +
                     source_expression(declaration, StringLiteral))
        if tag == "record":
            expected = ".record { name := %s, fields := %s }" % (
                q(name), seq(parameter(p) for p in module.records[name]))
        elif tag == "opaque":
            expected = ".opaqueDeclaration " + opaque(module.opaques[name])
        elif tag == "extern":
            expected = ".external " + external(module.externs[name])
        elif tag == "function":
            function = module.functions[name]
            lines.append(f"def function_{sid} : Function := {{ header := {header(function)}, body := {statements(function.body)} }}")
            expected = ".function function_" + sid
            function_indexes.append(index)
        else:
            raise ValueError(f"unrecognized source declaration {tag}")
        lines += [f"def declaration_{sid} : Declaration := {expected}", "",
                  f"theorem declaration_{sid}_exact : declaration? primitiveCatalogue syntax_{sid} =",
                  f"    some declaration_{sid} := by cbv", ""]
        if tag == "function":
            lines += [f"theorem function_{sid}_checked : checkFunction expectedInterface function_{sid} = true :=",
                      "  by decide +kernel", ""]
            lines += identifier_certificate(f"function_{sid}_identifier", name, c_identifier(name))
            lines += [f"theorem function_{sid}_symbol : functionSymbol {q(module.name)} function_{sid}.header.name =",
                      f"    {q(module.function_symbol(name))} := by",
                      f"  exact functionSymbol_of_characters {q(module.name)} {q(name)}",
                      f"    {q(c_identifier(module.name))} {q(c_identifier(name))} {q(module.function_symbol(name))}",
                      f"    module_identifier_exact function_{sid}_identifier (by rfl)", ""]
    count = len(declarations)
    lines += [f"def syntaxTail_{count:03d} : List Algorithms.MeTTa.Simple.Parser.SExpr := []",
              f"def declarationTail_{count:03d} : List Declaration := []",
              f"theorem tail_{count:03d}_exact : (syntaxTail_{count:03d}).mapM (declaration? primitiveCatalogue) =",
              f"    some declarationTail_{count:03d} := rfl", ""]
    for last in range(count, 0, -REPLAY_BLOCK_ROWS):
        first = max(0, last - REPLAY_BLOCK_ROWS)
        lines.append(f"native_declaration_suffix {first} to {last}")
    lines.append("")
    lines += [
        "def sourceSyntax : Algorithms.MeTTa.Simple.Parser.SExpr :=",
        f"  .list (.atom \"gslt-native-ops-v1\" :: .atom {q(module.name)} :: syntaxTail_000)",
        "def expectedProgram : Program := {",
        f"  name := {q(module.name)}", "  interface := expectedInterface",
        "  functions := " + seq(f"function_{index:03d}" for index in function_indexes), "}", "",
        *factorization,        "theorem catalogue_checked : catalogueValid primitiveCatalogue = true := by cbv", "",
        "theorem parsed_program_exact : parseProgram? primitiveCatalogue sourceSyntax =",
        "    some expectedProgram := by",
        "  simp only [parseProgram?, sourceSyntax]",
        "  have named : name? (.atom " + q(module.name) + ") = some " + q(module.name) + " := by cbv",
        "  rw [named]",
        "  simp only [bind, Option.bind]",
        "  rw [tail_000_exact]", "  rfl", "",
    ]
    # The function checks above are individual semantic admission computations.
    # They can be composed without reducing all 53 bodies in one giant proof.
    functions = seq(f"function_{index:03d}" for index in function_indexes)
    names = seq(q(name) for name in [*module.records, *module.opaques, *module.externs, *module.functions])
    lines += [
        "def expectedNames : List String := " + names, "",
        "theorem program_names_exact : expectedInterface.records.map Record.name ++",
        "    expectedInterface.opaques.map Opaque.name ++",
        "    expectedInterface.externals.map (fun external => external.header.name) ++",
        "    (" + functions + ").map (fun function => function.header.name) = expectedNames := rfl", "",
        "theorem program_names_unique : decide expectedNames.Nodup = true := by decide +kernel", "",
        "theorem program_names_valid : expectedNames.all (fun name => identifier name &&",
        '    !(["unit", "u64", "byte", "bool", "bytes"].contains name)) = true := by cbv', "",
        "theorem program_records_valid : expectedInterface.records.all (fun record =>",
        "    !record.fields.isEmpty && (record.fields.map Parameter.name).Nodup &&",
        "    record.fields.all (fun field => validType expectedInterface field.type true)) = true :=",
        "  by decide +kernel", "",
        "theorem program_record_order_valid :",
        "    (recordOrder? expectedInterface.records.length [] expectedInterface.records).isSome = true :=",
        "  by decide +kernel", "",
        "theorem program_external_symbols_unique :",
        "    decide (expectedInterface.externals.map External.cSymbol).Nodup = true := by decide +kernel", "",
        "theorem program_external_symbols_disjoint : expectedInterface.externals.all (fun external =>",
        "    !(" + functions + ").any (fun function =>",
        "      functionSymbol " + q(module.name) + " function.header.name == external.cSymbol)) = true := by",
        "  simp only [expectedInterface, List.all_cons, List.all_nil, List.any_cons, List.any_nil, " +
        ", ".join(f"function_{index:03d}_symbol" for index in function_indexes) + "]",
        "  decide +kernel", "",
        "theorem program_external_types_valid : expectedInterface.externals.all (fun external =>",
        "    external.header.parameters.all (fun field => validType expectedInterface field.type true) &&",
        "    validType expectedInterface external.header.result (external.header.result != NativeType.unit)) = true :=",
        "  by decide +kernel", "",
        "theorem program_headers_exact : decide (expectedInterface.functions =",
        "    (" + functions + ").map Function.header) = true := by decide +kernel", "",
    ]
    lines += [
        "theorem expected_program_checked : programValid expectedProgram = true := by",
        "  have functions_checked : (" + functions +
        ").all (checkFunction expectedInterface) = true := by",
        "    simp only [List.all_cons, List.all_nil, " +
        ", ".join(f"function_{index:03d}_checked" for index in function_indexes) + ", Bool.and_self]",
        "  apply (programValid_iff expectedProgram).mpr",
        "  refine ⟨by cbv, by rfl, ?_, ?_, program_records_valid, program_record_order_valid,",
        "    of_decide_eq_true program_external_symbols_unique, program_external_symbols_disjoint,",
        "    program_external_types_valid, of_decide_eq_true program_headers_exact, functions_checked⟩",
        "  · simp only [declaredNames, expectedProgram, program_names_exact]",
        "    exact of_decide_eq_true program_names_unique",
        "  · simp only [declaredNames, expectedProgram, program_names_exact]",
        "    exact program_names_valid", "",
        "theorem source_admitted : admitProgram? primitiveCatalogue sourceSyntax = some expectedProgram := by",
        "  unfold admitProgram?", "  rw [catalogue_checked]", "  simp only [Bool.not_true, Bool.false_eq_true, if_false]",
        "  rw [parsed_program_exact]", "  change (if programValid expectedProgram then some expectedProgram else none) = _",
        "  rw [expected_program_checked]", "  rfl", "",
        f"theorem exact_function_count : expectedProgram.functions.length = {len(module.functions)} := rfl",
        f"theorem exact_record_count : expectedProgram.interface.records.length = {len(module.records)} := rfl",
        f"theorem exact_external_count : expectedProgram.interface.externals.length = {len(module.externs)} := rfl", "",
    ]
    inputs = {"authoredSourceSHA256": source, "operationalProjectionSHA256": projected,
              "primitiveCatalogueSHA256": catalogue_path,
              "operationalCompilerSHA256": native / "tools/compile_gslt_native_ops_v1.py",
              "sourceCarrierSHA256": native / "tools/gslt2parse_schema_v1.py"}
    for name, path in inputs.items():
        digest = (slices.digest if name == "authoredSourceSHA256" and slices is not None
                  else hashlib.sha256(path.read_bytes()).hexdigest())
        lines.append(f"def {name} : String := {q(digest)}")
        if name == "authoredSourceSHA256" and slices is not None:
            lines += ["", *snapshot_identity()]
    lines += ["", "end " + NAMESPACE, ""]
    return "\n".join(lines), component


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--catalogue", type=Path)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--slices-output", type=Path, help="path to the shared character store")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    authored = args.native_root / "langdef/vibe-itp/vibe_itp_native_guest_v1.metta"
    source = args.source or authored
    catalogue = args.catalogue or args.native_root / "langdef/native/native_guest_primitives_v1.json"
    table_output = args.slices_output
    if (table_output is None and args.output.resolve() == OUTPUT.resolve()
            and source.resolve() == authored.resolve()):
        sys.path.insert(0, str(args.native_root / "tools"))
        from gslt2parse_schema_v1 import Symbol, parse_sexprs

        parsed = parse_sexprs(source.read_text(encoding="utf-8"))
        if (len(parsed) == 1 and isinstance(parsed[0], tuple) and parsed[0]
                and parsed[0][0] == Symbol("gslt-native-guest-v1")):
            table_output = LEAN_ROOT / SLICE_FILE
    outputs = {}
    slices = None
    if table_output is not None:
        if table_output.resolve() == args.output.resolve():
            parser.error("the source wrapper and character store require distinct paths")
        slices = GuestSourceSlices.read(source)
        outputs[table_output] = slices.render_table()
    content, _ = render(args.native_root, source, catalogue, slices)
    outputs[args.output] = content
    for path, generated in outputs.items():
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != generated:
                parser.error(f"generated operational source input is missing or stale in {path.name}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(generated, encoding="utf-8")
    print("checked" if args.check else "generated", args.output.name)


if __name__ == "__main__":
    main()
