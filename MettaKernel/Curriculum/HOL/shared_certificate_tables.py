"""Untrusted source adapter for SharedCertificateExport's structural tables.

The mixin extends the existing HOLR stream producer. It validates framing and
backward references, then proposes the same native requests and expected
sequents. It implements no HOL inference rule or proof-verification verdict.
The existing native receiver remains responsible for those checks.
"""

def natural(value):
    if type(value) is not int or value < 0:
        raise ValueError("expected natural number")
    return value


def reference(values, index):
    index = natural(index)
    if index >= len(values):
        raise ValueError("future or missing table reference")
    return values[index]


def row(value, length):
    if not isinstance(value, (list, tuple)) or len(value) != length:
        raise ValueError("wrong table row arity")
    return value


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, (list, tuple)) else value


class SharedStreamMixin:
    """Use with the existing recorded/canonical HOLR producer classes."""

    def initialize_shared(self, name_encoder):
        self.shared_names = []
        self.shared_types = []
        self.shared_named = []
        self.named_nodes = []
        self.named_ids = {}
        self.shared_name_encoder = name_encoder

    def type(self, value):
        if value[0] == "tyref":
            row(value, 2)
            value = reference(self.shared_types, value[1])
        return super().type(value)

    def intern_named_key(self, key):
        if key not in self.named_ids:
            self.named_ids[key] = len(self.named_nodes)
            self.named_nodes.append(key)
        return self.named_ids[key]

    def intern_named(self, value):
        kind = value[0]
        if kind in ("var", "const"):
            row(value, 3)
            key = (kind, freeze(value[1]), freeze(value[2]))
        elif kind == "app":
            row(value, 3)
            key = (kind, self.intern_named(value[1]), self.intern_named(value[2]))
        elif kind == "abs":
            row(value, 4)
            key = (kind, freeze(value[1]), freeze(value[2]), self.intern_named(value[3]))
        else:
            raise ValueError("unknown named term")
        return self.intern_named_key(key)

    def emit_named(self, root):
        # Visit children before parents without expanding a shared term tree.
        pending = [(root, False)]
        while pending:
            index, ready = pending.pop()
            key = ("shared-named", index)
            if key in self.terms:
                continue
            node = reference(self.named_nodes, index)
            kind = node[0]
            if kind in ("var", "const"):
                name = self.shared_name_encoder(node[1])
                typ = self.type(node[2])
                if kind == "const" and name not in self.constant_declarations:
                    raise ValueError("undeclared constant")
                self.add(4 if kind == "var" else 5, self.name(name), typ)
            elif kind == "app":
                if not ready:
                    pending.extend([(index, True), (node[2], False), (node[1], False)])
                    continue
                self.add(6, self.terms[("shared-named", node[1])],
                         self.terms[("shared-named", node[2])])
            else:
                binder = self.intern_named_key(("var", node[1], node[2]))
                if not ready:
                    pending.extend([(index, True), (node[3], False), (binder, False)])
                    continue
                self.add(7, self.terms[("shared-named", binder)],
                         self.terms[("shared-named", node[3])])
            self.terms[key] = len(self.terms)
        return self.terms[("shared-named", root)]

    def term(self, value):
        if value[0] == "tmref":
            row(value, 2)
            return self.emit_named(reference(self.shared_named, value[1]))
        if value[0] in ("var", "const", "app", "abs"):
            return self.emit_named(self.intern_named(value))
        return super().term(value)

    def shared_tables(self, tables):
        names, types, canonical, named = row(tables, 4)
        for value in names:
            namespace, component = row(value, 2)
            if not isinstance(namespace, list) or not all(isinstance(x, str) for x in namespace):
                raise ValueError("invalid namespace")
            if not isinstance(component, str):
                raise ValueError("invalid name")
            self.shared_names.append([namespace, component])
        for value in types:
            tag = natural(value[0])
            if tag == 0:
                row(value, 2)
                result = ["var", reference(self.shared_names, value[1])]
            elif tag == 1:
                row(value, 3)
                result = ["op", reference(self.shared_names, value[1]),
                          [reference(self.shared_types, child) for child in value[2]]]
            else:
                raise ValueError("unknown type node")
            self.shared_types.append(result)
        for value in canonical:
            tag = natural(value[0])
            if tag in (0, 1):
                row(value, 3)
                result = ["const" if tag == 0 else "free", reference(self.shared_names, value[1]),
                          reference(self.shared_types, value[2])]
            elif tag == 2:
                row(value, 2)
                result = ["bound", natural(value[1])]
            elif tag == 3:
                row(value, 3)
                reference(self.external_db, value[1])
                reference(self.external_db, value[2])
                result = ["app", value[1], value[2]]
            elif tag == 4:
                row(value, 3)
                reference(self.external_db, value[2])
                result = ["abs", reference(self.shared_types, value[1]), value[2]]
            else:
                raise ValueError("unknown canonical node")
            self.define(result)
        for value in named:
            tag = natural(value[0])
            if tag in (0, 1):
                row(value, 3)
                key = ("var" if tag == 0 else "const", freeze(reference(self.shared_names, value[1])),
                       freeze(reference(self.shared_types, value[2])))
            elif tag == 2:
                row(value, 3)
                key = ("app", reference(self.shared_named, value[1]), reference(self.shared_named, value[2]))
            elif tag == 3:
                row(value, 4)
                key = ("abs", freeze(reference(self.shared_names, value[1])),
                       freeze(reference(self.shared_types, value[2])), reference(self.shared_named, value[3]))
            else:
                raise ValueError("unknown named node")
            self.shared_named.append(self.intern_named_key(key))

    def shared_receipt(self, value):
        operation, arguments, parents, hypotheses, conclusion, dependencies, origin, ordinal = row(value, 8)
        operation = natural(operation)
        opcodes = ["REFL", "TRANS", "MK_COMB", "ABS", "BETA", "ASSUME", "EQ_MP",
                   "DEDUCT_ANTISYM_RULE", "INST_TYPE", "INST", "AXIOM"]
        if operation >= len(opcodes):
            raise ValueError("unknown inference request")
        if operation in (0, 5, 10):
            row(arguments, 1)
            reference(self.external_db, arguments[0])
            request = [opcodes[operation], ["dbref", arguments[0]]]
        elif operation in (3, 4):
            row(arguments, 1)
            reference(self.shared_named, arguments[0])
            request = [opcodes[operation], ["tmref", arguments[0]]]
        elif operation in (8, 9):
            tag, values = ("tyref", self.shared_types) if operation == 8 else ("tmref", self.shared_named)
            entries = []
            for pair in arguments:
                first, second = row(pair, 2)
                reference(values, first)
                reference(values, second)
                entries.append([[tag, first], [tag, second]])
            request = [opcodes[operation], entries]
        else:
            row(arguments, 0)
            request = [opcodes[operation]]
        for hypothesis in hypotheses:
            reference(self.external_db, hypothesis)
        reference(self.external_db, conclusion)
        origin_name = reference(self.shared_names, origin)
        if origin_name[0]:
            raise ValueError("namespaced receipt origin")
        return {"request": request, "parents": [natural(x) for x in parents],
                "claim": {"hypotheses": [["dbref", x] for x in hypotheses],
                          "conclusion": ["dbref", conclusion],
                          "axiomRoots": [natural(x) for x in dependencies]},
                "origin": [origin_name[1], natural(ordinal)]}

    def shared_counts(self):
        return {"names": len(self.shared_names), "types": len(self.shared_types),
                "canonical": len(self.external_db), "named": len(self.shared_named)}
