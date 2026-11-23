#!/usr/bin/env python3
"""Untrusted Lean-export data adapter; this module does not check Lean proofs.

Keep every NDJSON record in an invertible, typed JSON S-expression. Expressions
retain their original table IDs, so conversion never unfolds the term DAG.
The separate facts expose declarations and direct constant dependencies for
ordinary MeTTa queries. Structural IDs are not definitional-equality classes.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def unique_object(fields):
    result = {}
    for key, value in fields:
        if key in result:
            raise ValueError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def loads(text):
    def invalid(value):
        raise ValueError(f"nonfinite JSON number: {value}")
    return json.loads(text, object_pairs_hook=unique_object, parse_constant=invalid)


def quote(text):
    return json.dumps(text, ensure_ascii=False)


def needs_codepoints(text):
    # MeTTa readers need not implement JSON's Unicode/control escape syntax.
    return any(ord(c) < 32 or 0xD800 <= ord(c) <= 0xDFFF for c in text)


def name_atom(text):
    return encode(text) if needs_codepoints(text) else quote(text)


def encode(value):
    if value is None:
        return "(jnull)"
    if isinstance(value, bool):
        return "(jbool true)" if value else "(jbool false)"
    if isinstance(value, str):
        if needs_codepoints(value):
            return "(jcodes" + "".join(" " + str(ord(c)) for c in value) + ")"
        return "(jstr " + quote(value) + ")"
    if isinstance(value, (int, float)):
        return "(jnum " + quote(json.dumps(value, allow_nan=False)) + ")"
    if isinstance(value, list):
        return "(jarr" + "".join(" " + encode(x) for x in value) + ")"
    if isinstance(value, dict):
        if not all(isinstance(k, str) for k in value):
            raise ValueError("JSON object keys must be strings")
        return "(jobj" + "".join(
            " (jfield " + encode(k) + " " + encode(v) + ")" for k, v in value.items()) + ")"
    raise ValueError(f"not JSON: {type(value).__name__}")


def decode(text):
    """Parse the tagged representation, including escaped strings and whitespace."""
    cursor = 0
    decoder = json.JSONDecoder()

    def whitespace():
        nonlocal cursor
        while cursor < len(text) and text[cursor].isspace():
            cursor += 1

    def token():
        nonlocal cursor
        whitespace()
        start = cursor
        while cursor < len(text) and not text[cursor].isspace() and text[cursor] not in "()":
            cursor += 1
        if start == cursor:
            raise ValueError("expected symbol")
        return text[start:cursor]

    def string():
        nonlocal cursor
        whitespace()
        value, end = decoder.raw_decode(text, cursor)
        if not isinstance(value, str):
            raise ValueError("expected string")
        cursor = end
        return value

    def expect(char):
        nonlocal cursor
        whitespace()
        if cursor == len(text) or text[cursor] != char:
            raise ValueError(f"expected {char}")
        cursor += 1

    def value():
        expect("(")
        tag = token()
        if tag == "jnull":
            result = None
        elif tag == "jbool":
            word = token()
            if word not in ("true", "false"):
                raise ValueError("invalid boolean")
            result = word == "true"
        elif tag == "jstr":
            result = string()
        elif tag == "jcodes":
            chars = []
            while True:
                whitespace()
                if cursor < len(text) and text[cursor] == ")":
                    break
                code = token()
                if not code.isascii() or not code.isdecimal() or int(code) > 0x10FFFF:
                    raise ValueError("invalid character code")
                chars.append(chr(int(code)))
            result = "".join(chars)
        elif tag == "jnum":
            result = loads(string())
            if type(result) not in (int, float):
                raise ValueError("invalid number")
        elif tag in ("jarr", "jobj"):
            entries = []
            while True:
                whitespace()
                if cursor < len(text) and text[cursor] == ")":
                    break
                if tag == "jarr":
                    entries.append(value())
                else:
                    expect("(")
                    if token() != "jfield":
                        raise ValueError("expected field")
                    key = value()
                    if not isinstance(key, str):
                        raise ValueError("expected string key")
                    entries.append((key, value()))
                    expect(")")
            result = entries if tag == "jarr" else unique_object(entries)
        else:
            raise ValueError(f"unknown tag {tag}")
        expect(")")
        return result

    result = value()
    whitespace()
    if cursor != len(text):
        raise ValueError("trailing input")
    return result


class Export:
    """Structural census, not a source-language type or conversion checker."""
    def __init__(self, records):
        self.records = records
        self.names = {0: ""}
        self.levels = {0: {"zero": True}}
        self.exprs = {}
        self.children = {}
        self.decls = {}
        self.features = Counter()
        self.groups = Counter()
        if not records or "meta" not in records[0]:
            raise ValueError("missing export metadata")
        if records[0]["meta"]["format"]["version"] != "3.1.0":
            raise ValueError("unsupported export format")
        for row in records[1:]:
            self.add(row)
        for row in self.exprs.values():
            if "const" in row and row["const"]["name"] not in self.decls:
                raise ValueError("constant dependency absent from export closure")
        for _, row in self.decls.values():
            for root in self.roots(row):
                if root not in self.exprs:
                    raise ValueError("declaration references missing expression")

    @staticmethod
    def insert(table, index, value):
        if type(index) is not int or index < 0 or index in table:
            raise ValueError("invalid or duplicate table ID")
        table[index] = value

    def add(self, row):
        if "in" in row:
            key = "str" if "str" in row else "num"
            data = row[key]
            prefix = self.names[data["pre"]]
            name = str(data["str"] if key == "str" else data["i"])
            self.insert(self.names, row["in"], prefix + ("." if prefix else "") + name)
        elif "il" in row:
            kind = next(k for k in row if k != "il")
            data = row[kind]
            refs = [data] if kind == "succ" else data if kind in ("max", "imax") else []
            if any(x not in self.levels for x in refs):
                raise ValueError("forward or missing level reference")
            if kind == "param" and data not in self.names:
                raise ValueError("missing level-parameter name")
            if kind not in ("succ", "max", "imax", "param"):
                raise ValueError("unknown level form")
            self.insert(self.levels, row["il"], row)
            self.features["level:" + kind] += 1
        elif "ie" in row:
            kind = next(k for k in row if k != "ie")
            data = row[kind]
            if kind == "app":
                refs = [data["fn"], data["arg"]]
            elif kind in ("lam", "forallE"):
                refs = [data["type"], data["body"]]
            elif kind == "letE":
                refs = [data["type"], data["value"], data["body"]]
            elif kind == "proj":
                refs = [data["struct"]]
            elif kind in ("bvar", "sort", "const", "natVal", "strVal"):
                refs = []
            else:
                raise ValueError(f"unsupported expression form {kind}")
            if any(x not in self.exprs for x in refs):
                raise ValueError("forward or missing expression reference")
            if kind == "sort" and data not in self.levels:
                raise ValueError("missing sort level")
            if kind == "const":
                if data["name"] not in self.names or any(x not in self.levels for x in data["us"]):
                    raise ValueError("missing constant name or universe")
            self.insert(self.exprs, row["ie"], row)
            self.children[row["ie"]] = refs
            self.features["expr:" + kind] += 1
        else:
            if len(row) != 1:
                raise ValueError("invalid declaration record")
            kind, data = next(iter(row.items()))
            self.groups[kind] += 1
            if kind == "inductive":
                for field, form in (("types", "inductive"), ("ctors", "constructor"), ("recs", "recursor")):
                    for decl in data[field]:
                        self.add_decl(form, decl)
            elif kind in ("def", "thm", "opaque", "axiom", "quot"):
                self.add_decl(kind, data)
            else:
                raise ValueError(f"unknown declaration form {kind}")

    def add_decl(self, kind, row):
        if row["name"] not in self.names:
            raise ValueError("missing declaration name")
        self.insert(self.decls, row["name"], (kind, row))
        self.features["decl:" + kind] += 1
        if kind == "recursor" and row.get("k"):
            self.features["recursor:k-flag"] += 1

    @staticmethod
    def roots(row):
        return [row[k] for k in ("type", "value") if k in row] + [x["rhs"] for x in row.get("rules", [])]

    def dependencies(self, row):
        todo = self.roots(row)
        seen, result = set(), set()
        while todo:
            node = todo.pop()
            if node in seen:
                continue
            seen.add(node)
            term = self.exprs[node]
            if "const" in term:
                result.add(term["const"]["name"])
            todo.extend(self.children[node])
        return sorted(result)


def convert(source, target):
    records = [loads(line) for line in source.read_text().splitlines() if line.strip()]
    export = Export(records)
    with target.open("w") as stream:
        stream.write("; Untrusted Lean export data; no checking authority is attached.\n")
        for index, row in enumerate(records):
            payload = encode(row)
            if decode(payload) != row:
                raise ValueError(f"round-trip mismatch at record {index}")
            stream.write(f"(lean:record {index} {payload})\n")
        for identifier, (kind, row) in export.decls.items():
            name = name_atom(export.names[identifier])
            # Names displayed with dots are labels, not identities: a string
            # component can itself contain dots. Keep original name IDs on edges.
            stream.write(f"(lean:declaration {identifier} {name} {kind} {row['type']})\n")
            if "value" in row:
                stream.write(f"(lean:body {identifier} {row['value']})\n")
            for dep in export.dependencies(row):
                stream.write(f"(lean:uses {identifier} {dep})\n")
        for feature, count in sorted(export.features.items()):
            stream.write(f"(lean:feature {quote(feature)} {count})\n")
    summary = {
        "format": "lean-export-json-sexpr-v1", "records": len(records),
        "names": len(export.names), "levels": len(export.levels),
        "expressions": len(export.exprs), "declarations": len(export.decls),
        "groups": dict(export.groups), "features": dict(export.features),
        "axioms": [export.names[n] for n, (k, _) in export.decls.items() if k == "axiom"],
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "sexpr_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
        "checked_authority": False,
        "scope": "Exact JSON-value round-trip and structural closure; no typing, defeq, or tactic-history claim."
    }
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    parser.add_argument("census", type=Path)
    args = parser.parse_args()
    summary = convert(args.source, args.target)
    args.census.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))
