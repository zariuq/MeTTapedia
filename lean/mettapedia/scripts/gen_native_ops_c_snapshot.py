#!/usr/bin/env python3
"""Export actual generated-C syntax candidates for independent Lean checking.

This parser reads the C/header bytes, not authored semantic bodies. The output
is untrusted data until the corresponding Lean lexer, parser, layout and
normalization certificates have passed. No production source is modified.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys

LEAN_ROOT = Path(__file__).resolve().parents[1]
NATIVE_ROOT = LEAN_ROOT.parents[2] / "hyperon/cetta-prime-nik-20260811"
DESTINATION = LEAN_ROOT / "Mettapedia/GSLT/LanguageDef"
NS = "Mettapedia.GSLT.LanguageDef.NativeOpsCGuest"

TOKEN_RE = re.compile(r"(?P<space>\s+)|(?P<block>/\*.*?\*/)|(?P<line>//[^\n]*)|"
    r'(?P<quoted>"[^"\\\r\n]*")|(?P<identifier>[A-Za-z_][A-Za-z_0-9]*)|'
    r"(?P<number>[0-9]+)|(?P<punctuation>->|\+\+|--|<<|>>|&&|\|\||[-+=!<>&|*%\^]=|[(){}\[\].,;:?#~+\-*/%=!<>&|\^])", re.S)

@dataclass(frozen=True)
class Token:
    kind: str
    value: str
    begin: int
    end: int

def tokens(text):
    out, position = [], 0
    while position < len(text):
        match = TOKEN_RE.match(text, position)
        if not match:
            raise ValueError(f"unsupported C character at offset {position}: {text[position:position+40]!r}")
        kind, value = match.lastgroup, match.group()
        if kind not in {"space", "block", "line"}:
            if kind == "quoted": value = value[1:-1]
            if kind == "number" and match.end() < len(text) and re.match(r"[A-Za-z_]", text[match.end()]):
                raise ValueError("nondecimal C numeral")
            out.append(Token(kind, value, position, match.end()))
        position = match.end()
    return out

OPS = {"||": ("or", 1), "&&": ("and", 2), "|": ("bitOr", 3), "^": ("bitXor", 4), "&": ("bitAnd", 5),
    "==": ("eq", 6), "!=": ("ne", 6), "<": ("lt", 7), "<=": ("le", 7), ">": ("gt", 7), ">=": ("ge", 7),
    "<<": ("shiftLeft", 8), ">>": ("shiftRight", 8), "+": ("add", 9), "-": ("sub", 9),
    "*": ("mul", 10), "/": ("div", 10), "%": ("mod", 10)}

class Parser:
    def __init__(self, input_, names=()):
        self.tokens, self.names, self.position = input_, set(names), 0
    def peek(self, offset=0):
        p = self.position + offset
        return self.tokens[p].value if p < len(self.tokens) else None
    def take(self, value=None, kind=None):
        if self.position >= len(self.tokens): raise ValueError("unexpected C end")
        token = self.tokens[self.position]
        if value is not None and token.value != value: raise ValueError(f"expected {value}, got {token.value}")
        if kind is not None and token.kind != kind: raise ValueError(f"expected {kind}, got {token}")
        self.position += 1
        return token.value
    def type(self, *, raw=False):
        saved = self.position
        if saved >= len(self.tokens) or self.tokens[saved].kind != "identifier": return None
        name = self.take(kind="identifier")
        if not raw and name not in self.names:
            self.position = saved
            return None
        depth = 0
        while self.peek() == "*": self.take("*"); depth += 1
        return name, depth
    def expression(self, minimum=0):
        left = self.prefix()
        while self.peek() in OPS and OPS[self.peek()][1] >= minimum:
            operator, precedence = OPS[self.take()]
            right = self.expression(precedence + 1)
            left = ("binary", operator, left, right)
        if minimum == 0 and self.peek() == "?":
            self.take("?")
            yes = self.expression()
            self.take(":")
            no = self.expression()
            left = ("conditional", left, yes, no)
        return left
    def prefix(self):
        spelling = self.peek()
        unary = {"!": "not", "~": "complement", "*": "dereference", "&": "address", "++": "increment"}
        if spelling in unary:
            self.take()
            return ("unary", unary[spelling], self.prefix())
        if spelling == "(":
            self.take("(")
            saved = self.position
            type_ = self.type()
            if type_ is not None and self.peek() == ")":
                self.take(")")
                if self.peek() == "{":
                    self.take("{"); self.take("0", "number"); self.take("}")
                    return self.postfix(("zero", type_))
                return ("cast", type_, self.prefix())
            self.position = saved
            inside = self.expression()
            self.take(")")
            return self.postfix(inside)
        token = self.tokens[self.position]
        if token.kind == "identifier":
            name = self.take(kind="identifier")
            if self.peek() == "(":
                self.take("(")
                if name in {"UINT64_C", "UINT8_C"}:
                    value = int(self.take(kind="number"))
                    width = 64 if name == "UINT64_C" else 8
                    if not 0 <= value < 2**width: raise ValueError("oversized unsigned macro")
                    self.take(")")
                    return self.postfix(("word" if width == 64 else "byte", value))
                if name == "sizeof":
                    type_ = self.type()
                    if type_ is None: raise ValueError("unknown sizeof type")
                    self.take(")")
                    return self.postfix(("sizeOf", type_))
                args = self.arguments()
                return self.postfix(("call", name, args))
            return self.postfix(("bool", name == "true") if name in {"true", "false"} else
                ("null",) if name == "NULL" else ("identifier", name))
        if token.kind == "number": return self.postfix(("decimal", int(self.take(kind="number"))))
        raise ValueError(f"unsupported C expression prefix {token}")
    def postfix(self, base):
        while True:
            if self.peek() in {".", "->"}:
                through = self.take() == "->"
                base = ("field", base, self.take(kind="identifier"), through)
            elif self.peek() == "[":
                self.take("["); index = self.expression(); self.take("]")
                base = ("index", base, index)
            else: return base
    def arguments(self):
        if self.peek() == ")": self.take(")"); return []
        out = []
        while True:
            out.append(self.expression())
            if self.peek() == ")": self.take(")"); return out
            self.take(",")
            if self.peek() == ")": raise ValueError("trailing argument comma")
    def parameters(self, *, raw=False):
        if self.peek() == ")": self.take(")"); return []
        if self.peek() == "void" and self.peek(1) == ")": self.take("void"); self.take(")"); return []
        out = []
        while True:
            type_ = self.type(raw=raw)
            if type_ is None: raise ValueError("unknown parameter type")
            out.append((type_, self.take(kind="identifier")))
            if self.peek() == ")": self.take(")"); return out
            self.take(",")
            if self.peek() == ")": raise ValueError("trailing parameter comma")
    def block(self):
        self.take("{")
        out = []
        while self.peek() != "}": out.append(self.statement())
        self.take("}")
        return out
    def statement(self):
        value = self.peek()
        if value == ";": self.take(";"); return ("empty",)
        if value == "{": return ("block", self.block())
        if value == "if":
            self.take("if"); self.take("("); cond = self.expression(); self.take(")")
            yes = self.block()
            no = []
            if self.peek() == "else": self.take("else"); no = self.block()
            return ("branch", cond, yes, no)
        if value == "for":
            self.take("for"); self.take("(")
            type_ = self.type()
            if type_ is None: raise ValueError("unknown for type")
            name = self.take(kind="identifier"); self.take("=")
            initial = self.expression(); self.take(";")
            cond = self.expression(); self.take(";")
            step = self.expression(); self.take(")")
            return ("forLoop", type_, name, initial, cond, step, self.block())
        if value == "switch":
            self.take("switch"); self.take("("); select = self.expression(); self.take(")"); self.take("{")
            cases = []
            while self.peek() == "case":
                self.take("case"); select_case = self.expression(); self.take(":")
                cases.append((select_case, self.block()))
            self.take("default"); self.take(":"); otherwise = self.block(); self.take("}")
            return ("switch", select, cases, otherwise)
        if value == "goto":
            self.take("goto"); label = self.take(kind="identifier"); self.take(";")
            return ("jump", label)
        if value == "break": self.take("break"); self.take(";"); return ("break",)
        if value == "return":
            self.take("return")
            ret = None if self.peek() == ";" else self.expression()
            self.take(";")
            return ("return", ret)
        if self.tokens[self.position].kind == "identifier" and self.peek(1) == ":":
            name = self.take(kind="identifier"); self.take(":")
            return ("label", name)
        saved = self.position
        type_ = self.type()
        if type_ is not None:
            name = self.take(kind="identifier"); self.take("=")
            expr = self.expression(); self.take(";")
            return ("declare", type_, name, expr)
        self.position = saved
        expr = self.expression()
        if self.peek() == "=":
            self.take("="); right = self.expression(); self.take(";")
            return ("assign", expr, right)
        self.take(";")
        return ("effect", expr)
    def function(self):
        result = self.type()
        if result is None: raise ValueError("unknown function return type")
        name = self.take(kind="identifier"); self.take("(")
        params = self.parameters()
        return result, name, params, self.block()
    def header(self):
        self.take("#"); self.take("ifndef"); guard = self.take(kind="identifier")
        self.take("#"); self.take("define")
        if self.take(kind="identifier") != guard: raise ValueError("different include guard")
        items = []
        while True:
            if self.peek() == "#":
                self.take("#")
                directive = self.take(kind="identifier")
                if directive == "endif": break
                if directive != "include": raise ValueError("unaccounted preprocessor directive")
                items.append(("include", self.take(kind="quoted")))
            elif self.peek() == "typedef":
                self.take("typedef"); self.take("struct")
                if self.peek() == "{":
                    self.take("{"); fields = self.fields()
                    spelling = self.take(kind="identifier"); self.take(";")
                    items.append(("array", spelling, fields))
                else:
                    tag = self.take(kind="identifier"); spelling = self.take(kind="identifier"); self.take(";")
                    items.append(("forward", tag, spelling))
            elif self.peek() == "struct":
                self.take("struct"); tag = self.take(kind="identifier"); self.take("{")
                fields = self.fields(); self.take(";")
                items.append(("record", tag, fields))
            else:
                result = self.type(raw=True)
                if result is None: raise ValueError("missing prototype type")
                name = self.take(kind="identifier"); self.take("(")
                params = self.parameters(raw=True); self.take(";")
                items.append(("prototype", result, name, params))
        if self.position != len(self.tokens): raise ValueError("extra header tokens")
        return guard, items
    def fields(self):
        out = []
        while self.peek() != "}":
            type_ = self.type(raw=True)
            if type_ is None: raise ValueError("missing field type")
            name = self.take(kind="identifier"); self.take(";")
            out.append((type_, name))
        self.take("}")
        return out


def q(value): return json.dumps(value, ensure_ascii=False)
def charlist(value):
    # Exact Unicode codepoints; current emitted target fragment is ASCII.
    return "[" + ", ".join("Char.ofNat " + str(ord(c)) for c in value) + "]"
def seq(values): return "[" + ", ".join(values) + "]"
def ctype(value): return "⟨%s, %d⟩" % (charlist(value[0]), value[1])
def parameter(value): return "⟨%s, %s⟩" % (ctype(value[0]), charlist(value[1]))
def expression(value):
    tag, args = value[0], value[1:]
    if tag == "identifier": return "(.identifier " + charlist(args[0]) + ")"
    if tag in {"word", "byte", "decimal"}: return f"(.{tag} {args[0]})"
    if tag == "bool": return "(.bool " + str(args[0]).lower() + ")"
    if tag == "null": return ".null"
    if tag in {"zero", "sizeOf"}: return f"(.{tag} {ctype(args[0])})"
    if tag == "call": return f"(.call {charlist(args[0])} {seq(expression(a) for a in args[1])})"
    if tag == "unary": return f"(.unary .{args[0]} {expression(args[1])})"
    if tag == "cast": return f"(.cast {ctype(args[0])} {expression(args[1])})"
    if tag == "binary": return f"(.binary .{args[0]} {expression(args[1])} {expression(args[2])})"
    if tag == "conditional": return "(.conditional " + " ".join(expression(a) for a in args) + ")"
    if tag == "field": return f"(.field {expression(args[0])} {charlist(args[1])} {str(args[2]).lower()})"
    if tag == "index": return f"(.index {expression(args[0])} {expression(args[1])})"
    raise ValueError(tag)
def statement(value, render_block=None):
    if render_block is None:
        render_block = statements
    tag, args = value[0], value[1:]
    if tag in {"empty", "break"}: return "." + tag
    if tag == "declare": return f"(.declare {ctype(args[0])} {charlist(args[1])} {expression(args[2])})"
    if tag in {"assign", "effect"}: return f"(.{tag} " + " ".join(expression(a) for a in args) + ")"
    if tag == "branch": return f"(.branch {expression(args[0])} {render_block(args[1])} {render_block(args[2])})"
    if tag == "forLoop": return f"(.forLoop {ctype(args[0])} {charlist(args[1])} " + " ".join(expression(a) for a in args[2:5]) + " " + render_block(args[5]) + ")"
    if tag == "switch": return f"(.switch {expression(args[0])} " + seq(f"({expression(c)}, {render_block(b)})" for c,b in args[1]) + " " + render_block(args[2]) + ")"
    if tag == "block": return f"(.block {render_block(args[0])})"
    if tag in {"label", "jump"}: return f"(.{tag} {charlist(args[0])})"
    if tag == "return": return "(.return " + ("none" if args[0] is None else "(some " + expression(args[0]) + ")") + ")"
    raise ValueError(tag)
def statements(value): return seq(statement(s) for s in value)
def function(value): return "⟨%s, %s, %s, %s⟩" % (ctype(value[0]), charlist(value[1]), seq(parameter(p) for p in value[2]), statements(value[3]))
def header_item(value):
    tag,args=value[0],value[1:]
    if tag == "include": return "(.include " + charlist(args[0]) + ")"
    if tag == "forward": return "(.forward " + charlist(args[0]) + " " + charlist(args[1]) + ")"
    if tag in {"record", "array"}: return f"(.{tag} {charlist(args[0])} {seq(parameter(p) for p in args[1])})"
    if tag == "prototype": return f"(.prototype {ctype(args[0])} {charlist(args[1])} {seq(parameter(p) for p in args[2])})"
    raise ValueError(tag)
def lean_tokens(value): return seq(f".{t.kind} {charlist(t.value)}" for t in value)

class FunctionPayload:
    """Split long lists of syntax constructors into separate Lean definitions."""

    block_limit = 24_000

    def __init__(self, stem: str):
        self.stem = stem
        self.declarations: list[str] = []

    def block(self, type_name: str, contents: list[str]) -> str:
        name = f"function_{self.stem}_block_{len(self.declarations):03d}"
        self.declarations.append(f"private def {name} : List {type_name} := {seq(contents)}")
        return name

    def split(self, type_name: str, contents: list[str]) -> str:
        if sum(len(value) + 2 for value in contents) <= self.block_limit:
            return seq(contents)
        blocks, block = [], []
        size = 0
        for value in contents:
            if block and size + len(value) + 2 > self.block_limit:
                blocks.append(self.block(type_name, block))
                block = []
                size = 0
            block.append(value)
            size += len(value) + 2
        blocks.append(self.block(type_name, block))
        return "(" + " ++ ".join(blocks) + ")"

    def statements(self, body) -> str:
        return self.split("CStatement", [statement(value, self.statements) for value in body])

    def render(self, function, tokens) -> list[str]:
        result, name, parameters, body = function
        body_source = self.statements(body)
        token_source = self.split("Token", [f".{token.kind} {charlist(token.value)}" for token in tokens])
        return self.declarations + [
            "",
            f"def function_{self.stem} : CFunction := ⟨{ctype(result)}, {charlist(name)}, "
            f"{seq(parameter(p) for p in parameters)}, {body_source}⟩",
            "",
            f"def functionTokens_{self.stem} : List Token := {token_source}",
        ]


def render(native):
    header_path = native / "src/generated/vibe_itp_native_kernel_v1.generated.h"
    c_path = native / "src/generated/vibe_itp_native_kernel_v1.generated.c"
    htext, ctext = header_path.read_text(), c_path.read_text()
    htoks, ctoks = tokens(htext), tokens(ctext)
    hsyntax = Parser(htoks).header()
    names = {"void", "uint64_t", "uint8_t", "bool", "CettaGsltNativeOpsContextV1", "CettaGsltNativeOpsBytesV1"}
    for item in hsyntax[1]:
        if item[0] in {"forward", "record", "array"}: names.add(item[1])
        if item[0] in {"record", "array"}:
            names.update(field[0][0] for field in item[2])
        if item[0] == "prototype":
            names.add(item[1][0]); names.update(p[0][0] for p in item[3])
    parser = Parser(ctoks, names)
    parser.take("#"); parser.take("include"); include = parser.take(kind="quoted")
    functions, spans = [], []
    while parser.position < len(ctoks):
        first = parser.position
        functions.append(parser.function())
        last = parser.position
        spans.append((first,last))
    if len(functions) != 53:
        raise ValueError(f"live guest function count changed: {len(functions)}")
    sys.path.insert(0, str(native / "tools"))
    from compile_gslt_native_ops_v1 import compile_source, Type
    from gen_native_ops_source_snapshot import ty
    module = compile_source(native / "langdef/vibe-itp/vibe_itp_native_kernel_v1.metta",
        native / "langdef/native/native_guest_primitives_v1.json")
    native_types = {"void":Type("unit"),"uint64_t":Type("u64"),"uint8_t":Type("byte"),"bool":Type("bool"),
        "CettaGsltNativeOpsBytesV1":Type("array",Type("byte"))}
    native_types.update({module.record_symbol(name):Type(name) for name in module.records})
    native_types.update({opaque.c_type:Type(opaque.name) for opaque in module.opaques.values()})
    array_aliases=[]
    for item in hsyntax[1]:
        if item[0]!="array": continue
        fields=item[2]
        if len(fields)!=2 or fields[0][1]!="data" or fields[1]!=(("uint64_t",0),"length"):
            raise ValueError("unexpected physical array declaration")
        name,depth=fields[0][0]
        if depth<1 or name not in native_types: raise ValueError("unknown array element declaration")
        element=native_types[name]
        for _ in range(depth-1): element=Type("ref",element)
        array_aliases.append((element,item[1]))
        native_types[item[1]]=Type("array",element)
    base = ["import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization", "import Mettapedia.GSLT.LanguageDef.NativeOpsCLexSegments", "",
        "/-! Actual C/header syntax candidates. Generated from target bytes by",
        "`scripts/gen_native_ops_c_snapshot.py`; certificates are checked separately. -/", "",
        "set_option autoImplicit false", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 4000000", "set_option Elab.async false", "",
        "namespace " + NS, "", "open NativeOps NativeOps.NativeC", ""]
    hlines = base + ["def candidateHeader : CHeader := ⟨" + charlist(hsyntax[0]) + ", " + seq(header_item(i) for i in hsyntax[1]) + "⟩", "",
        "def headerTokens : List Token := " + lean_tokens(htoks), "",
        "def candidateTypeNames : TypeNames := " + seq(charlist(name) for name in sorted(names)), "",
        "end " + NS, ""]
    output = {DESTINATION / "NativeOpsCGuestHeaderSnapshot.lean": "\n".join(hlines)}
    representation_lines=["import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSnapshot",
        "import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot", "",
        "set_option autoImplicit false", "set_option maxHeartbeats 4000000", "set_option maxRecDepth 1000000",
        "set_option Elab.async false", "", "namespace "+NS, "", "open NativeOps NativeOps.NativeC", "",
        "def representation : Representation := ⟨"+q(module.name)+", NativeOpsSourceGuestSnapshot.expectedInterface, "+
        seq("("+ty(element)+", "+charlist(name)+")" for element,name in array_aliases)+"⟩", "",
        "end "+NS, ""]
    output[DESTINATION / "NativeOpsCGuestRepresentation.lean"]="\n".join(representation_lines)
    manifest_functions = []
    for i,(fn,(first,last)) in enumerate(zip(functions,spans)):
        sid=f"{i:03d}"
        lines = [
            "import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSnapshot", "",
            "set_option autoImplicit false", "set_option maxRecDepth 1000000",
            "set_option maxHeartbeats 4000000", "set_option Elab.async false", "",
            "namespace " + NS, "", "open NativeOps NativeOps.NativeC", "",
        ]
        if last - first > 8000:
            lines += FunctionPayload(sid).render(fn, ctoks[first:last])
        else:
            lines += [
                f"def function_{sid} : CFunction := " + function(fn), "",
                f"def functionTokens_{sid} : List Token := " + lean_tokens(ctoks[first:last]),
            ]
        lines += ["", "end " + NS, ""]
        destination = DESTINATION / ("NativeOpsCGuestFunction" + sid + ".lean")
        output[destination]="\n".join(lines)
        manifest_functions.append({"index":i,"symbol":fn[1],"tokens":last-first,"byte_start":ctoks[first].begin,"byte_end":ctoks[last-1].end})
    manifest={"kind":"untrusted-generated-C-syntax-candidates","header_sha256":hashlib.sha256(header_path.read_bytes()).hexdigest(),
        "c_sha256":hashlib.sha256(c_path.read_bytes()).hexdigest(),"function_count":len(functions),"header_tokens":len(htoks),"c_tokens":len(ctoks),"functions":manifest_functions,
        "qualification":"Candidate transcriptions only; original lexer/parser, typed layout, control normalization and evaluator adequacy are separate checks."}
    return output,manifest

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--native",type=Path,default=NATIVE_ROOT)
    mode=ap.add_mutually_exclusive_group(required=True);mode.add_argument("--write",action="store_true");mode.add_argument("--check",action="store_true")
    ap.add_argument("--manifest",type=Path)
    args=ap.parse_args()
    output,manifest=render(args.native)
    errors=[]
    for path,text in output.items():
        if args.write: path.write_text(text)
        elif not path.exists() or path.read_text()!=text: errors.append(str(path.relative_to(LEAN_ROOT)))
    if args.manifest:
        encoded=json.dumps(manifest,indent=2,sort_keys=True)+"\n"
        if args.write: args.manifest.parent.mkdir(parents=True,exist_ok=True);args.manifest.write_text(encoded)
        elif not args.manifest.exists() or args.manifest.read_text()!=encoded: errors.append("candidate manifest")
    if errors: raise SystemExit("stale candidates: "+", ".join(errors))
    print(json.dumps({"mode":"write" if args.write else "check","files":len(output),"functions":manifest["function_count"],"C_tokens":manifest["c_tokens"],"header_tokens":manifest["header_tokens"],"certified":False},sort_keys=True))

if __name__ == "__main__": main()
