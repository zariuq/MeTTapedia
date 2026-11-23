"""Passive source-data boundary and owner-bound MM2 outcome observations."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from mm2_atoms import Atom, Expr, Symbol, atoms_equal, head, render, walk


INITIAL_ARITIES = {
    "mm-source-start": 1, "mm-source-end": 2, "mm-linked-row": 5,
    "mm-row": 4, "mm-index-successor": 3,
    "mm-source-object-frontier": 2, "mm-source-activity-frontier": 2,
    "mm-source-dv-occurrence-frontier": 2,
    "mm-source-dv-pair-plan-header": 4, "mm-source-dv-pair-plan-frontier": 2,
    "mm-source-essential-candidate": 6, "mm-source-assertion-candidate": 9,
    "mm-source-assertion-publication-plan": 9, "mm-source-action-plan": 6,
    "mm-source-action-kind": 3, "mm-source-theorem-prepared": 7,
    "mm-source-theorem-assertion-header": 4, "mm-source-proof-control-prepared": 3,
    "mm-normal-label-frontier": 2, "mm-proof": 5, "mm-proof-end": 2,
    "mm-compressed-header-end": 2, "mm-compressed-index-successor": 3,
    "mm-compressed-machine": 5,
    "mm-assertion-hypothesis": 4, "mm-assertion-hypothesis-successor": 4,
    "mm-assertion-dv-header": 3, "mm-assertion-dv-pair": 5,
    "mm-assertion-dv-successor": 4, "mm-assertion-result": 4,
}

ASSERTION_ROWS = {
    "mm-assertion-header": 4, "mm-assertion-hypothesis": 4,
    "mm-assertion-hypothesis-successor": 4, "mm-assertion-dv-header": 3,
    "mm-assertion-dv-pair": 5, "mm-assertion-dv-successor": 4,
    "mm-assertion-result": 4,
}

STATEMENT_ARITIES = {
    "mm-source-const": 3, "mm-source-var": 3, "mm-source-dv": 3,
    "mm-source-open-scope": 1, "mm-source-close-scope": 1,
    "mm-source-floating": 5, "mm-source-essential": 5,
    "mm-source-axiom": 5, "mm-source-theorem": 7,
}

NESTED_ARITIES = INITIAL_ARITIES | ASSERTION_ROWS | STATEMENT_ARITIES | {
    "mm-nat": 1, "mm-string": 1, "mm-char-cons": 2, "mm-char-nil": 0,
    "mm-cons": 2, "mm-nil": 0, "mm-pair": 2,
    "mm-const": 1, "mm-variable": 1, "mm-formula": 2, "mm-frame": 2,
    "mm-floating": 3, "mm-essential": 2, "mm-assertion": 4,
    "mm-hypothesis-lookup": 3, "mm-source-name": 2, "mm-source-token": 2,
    "mm-source-span": 3, "mm-source-normal-proof": 1,
    "mm-source-compressed-proof": 4, "mm-source-action-add": 1,
    "mm-source-action-owner": 2, "mm-source-proof-owner": 2,
    "mm-source-assertion-publication-owner": 2, "mm-source-dv-pair-plan-owner": 2,
    "mm-source-active-variable-ledger": 1, "mm-source-variable-typecode-ledger": 1,
    "mm-source-active-hypothesis-ledger": 1, "mm-source-active-distinct-ledger": 1,
    "mm-source-object-root": 0, "mm-source-dv-pair-witness": 3,
    "mm-normal-label-entry": 2, "mm-normal-control": 4,
    "mm-compressed-header-control": 3, "mm-compressed-header-mandatory": 2,
    "mm-compressed-header-explicit": 1, "mm-compressed-index-code": 2,
    "mm-compressed-heap-owner": 1, "mm-compressed-node-owner": 1,
    "mm-compressed-stack-owner": 1,
}

FORBIDDEN_HEADS = {
    "exec", "mm-accepted", "mm-rejected", "mm-fault", "mm-incomplete",
    "mm-source-theorem-admitted", "mm-source-theorem-rejected",
    "mm-source-statement-applied", "mm-source-statement-rejected",
    "mm-source-control", "mm-source-current", "mm-source-environment",
    "mm-normal-final-formula-candidate", "mm-body-match", "mm-body-prefix",
    "mm-proof-fault", "mm-compressed-proof-incomplete",
}

OWNER_WRAPPERS = {
    "mm-source-action-owner", "mm-source-proof-owner",
    "mm-source-assertion-publication-owner", "mm-source-dv-pair-plan-owner",
    "mm-source-active-variable-ledger", "mm-source-variable-typecode-ledger",
    "mm-source-active-hypothesis-ledger", "mm-source-active-distinct-ledger",
    "mm-compressed-heap-owner", "mm-compressed-node-owner", "mm-compressed-stack-owner",
}


def nat_atom(value: int) -> Expr:
    return Expr((Symbol("mm-nat"), Symbol(str(value))))


def string_atom(text: str) -> Expr:
    tail = Expr((Symbol("mm-char-nil"),))
    for char in reversed(text):
        code = ord(char)
        if 0xD800 <= code <= 0xDFFF:
            raise ValueError("Owner names must contain Unicode scalar values")
        tail = Expr((Symbol("mm-char-cons"), nat_atom(code), tail))
    return Expr((Symbol("mm-string"), tail))


def decode_nat(atom: Atom) -> int:
    if not isinstance(atom, Expr) or head(atom) != "mm-nat" or len(atom.items) != 2:
        raise ValueError("Expected a canonical mm-nat")
    token = atom.items[1]
    if not isinstance(token, Symbol) or not token.text.isascii() or not token.text.isdecimal():
        raise ValueError("Expected a decimal mm-nat")
    if len(token.text) > 1 and token.text.startswith("0"):
        raise ValueError("Noncanonical leading zero in mm-nat")
    return int(token.text)


def decode_string(atom: Atom) -> str:
    if not isinstance(atom, Expr) or head(atom) != "mm-string" or len(atom.items) != 2:
        raise ValueError("Expected a structural mm-string")
    chars: list[str] = []
    tail = atom.items[1]
    while head(tail) == "mm-char-cons":
        if not isinstance(tail, Expr) or len(tail.items) != 3:
            raise ValueError("Malformed mm-char-cons")
        code = decode_nat(tail.items[1])
        if code > 0x10FFFF or 0xD800 <= code <= 0xDFFF:
            raise ValueError("Invalid Unicode scalar in mm-string")
        chars.append(chr(code))
        tail = tail.items[2]
    if not isinstance(tail, Expr) or tail.items != (Symbol("mm-char-nil"),):
        raise ValueError("Unterminated structural mm-string")
    return "".join(chars)


def owner_root(atom: Atom) -> Atom:
    while head(atom) in OWNER_WRAPPERS:
        assert isinstance(atom, Expr)
        atom = atom.items[1]
    return atom


@dataclass(frozen=True)
class SourceData:
    owner: Atom
    owner_name: str
    end: int
    statements: dict[int, Atom]

    @property
    def theorem_positions(self) -> set[int]:
        return {position for position, statement in self.statements.items() if head(statement) == "mm-source-theorem"}


def validate_passive_data(atoms: Iterable[Atom], *, owner: str = "metamath-test-unit") -> SourceData:
    rows = tuple(atoms)
    expected_owner = string_atom(owner)
    prepared_controls: set[int] = set()
    for row in rows:
        tag = head(row)
        if not isinstance(row, Expr) or tag not in INITIAL_ARITIES:
            raise ValueError(f"Not an initial source-data row: {tag!r}")
        if len(row.items) != INITIAL_ARITIES[tag] + 1:
            raise ValueError(f"Wrong initial arity for {tag}")
        if tag == "mm-source-proof-control-prepared":
            control = row.items[3]
            if head(control) not in {"mm-normal-control", "mm-compressed-header-control"}:
                raise ValueError("A prepared proof control must contain its initial cursor")
            prepared_controls.add(id(control))
        for atom in walk(row):
            if isinstance(atom, Symbol):
                if atom.is_variable:
                    raise ValueError("Raw variables are forbidden in passive source data")
                continue
            current = head(atom)
            if current in FORBIDDEN_HEADS or (current or "").startswith(("mm-internal-", "mm-reload-", "mm-compressed-owned-")):
                raise ValueError(f"Verifier-owned or terminal atom in passive source data: {current}")
            if current not in NESTED_ARITIES or len(atom.items) != NESTED_ARITIES[current] + 1:
                raise ValueError(f"Unknown or malformed passive constructor: {current!r}")
            if current in {"mm-normal-control", "mm-compressed-header-control"} and id(atom) not in prepared_controls:
                raise ValueError("Initial proof cursors are allowed only inside prepared-control rows")
            if current == "mm-source-action-add" and head(atom.items[1]) not in ASSERTION_ROWS:
                raise ValueError("A prepared publication action may add only an assertion row")
            if current == "mm-nat":
                decode_nat(atom)
            if current == "mm-string":
                decode_string(atom)
        # Most rows put their owner first. Generic linked/word tables put
        # their table name first; the DV plan uses a positioned owner first.
        own = row.items[1]
        if tag in {"mm-linked-row", "mm-row"} and head(own) == "mm-string":
            own = row.items[2]
        if not atoms_equal((owner_root(own),), (expected_owner,)):
            raise ValueError(f"Source-data owner mismatch in {tag}")
    starts = [row for row in rows if head(row) == "mm-source-start"]
    ends = [row for row in rows if head(row) == "mm-source-end"]
    if len(starts) != 1 or len(ends) != 1:
        raise ValueError("Source data requires exactly one start and one end")
    end = decode_nat(ends[0].items[2])
    statements: dict[int, Atom] = {}
    for row in rows:
        if head(row) != "mm-linked-row" or head(row.items[1]) != "mm-string" or decode_string(row.items[1]) != "source-statement":
            continue
        if not atoms_equal((row.items[2],), (expected_owner,)):
            raise ValueError("Source statement rows require the source owner")
        position = decode_nat(row.items[3])
        if decode_nat(row.items[4]) != position + 1 or position in statements:
            raise ValueError("Source statement links must be unique consecutive edges")
        statement = row.items[5]
        if head(statement) not in STATEMENT_ARITIES:
            raise ValueError("Source statement row contains no raw statement")
        statements[position] = statement
    if end != len(statements) or any(position != index for index, position in enumerate(sorted(statements))):
        raise ValueError("Source statement chain does not cover the declared end")
    return SourceData(expected_owner, owner, end, statements)


def observe_result(atoms: Iterable[Atom], source: SourceData) -> dict:
    """Classify a quiescent result; execution/budget checks belong to the runner."""
    rows = tuple(atoms)
    owned: dict[str, list[Expr]] = {}
    for row in rows:
        if isinstance(row, Expr) and len(row.items) > 1 and atoms_equal((owner_root(row.items[1]),), (source.owner,)):
            owned.setdefault(head(row) or "", []).append(row)

    def failure(detail: str) -> dict:
        return {"outcome": "execution-failure", "detail": detail}

    ends = owned.get("mm-source-end", [])
    if len(ends) != 1 or len(ends[0].items) != 3 or decode_nat(ends[0].items[2]) != source.end:
        return failure("The original source-end boundary is missing or inconsistent")
    admitted: dict[int, Expr] = {}
    applied: dict[int, Expr] = {}
    rejections: list[Expr] = []
    for tag, expected_length in (("mm-source-statement-applied", 4), ("mm-source-theorem-admitted", 5),
                                 ("mm-source-statement-rejected", 6), ("mm-source-theorem-rejected", 8)):
        for row in owned.get(tag, []):
            if len(row.items) != expected_length:
                return failure(f"Malformed owner-bound {tag} receipt")
            position = decode_nat(row.items[2])
            original = source.statements.get(position)
            if original is None or not atoms_equal((row.items[3],), (original,)):
                return failure(f"{tag} receipt is not bound to its original statement")
            if "theorem" in tag and position not in source.theorem_positions:
                return failure("A theorem receipt names a non-theorem statement")
            if tag.endswith("rejected"):
                rejections.append(row)
            else:
                target = admitted if "theorem" in tag else applied
                if position in target:
                    return failure(f"Duplicate receipt at source position {position}")
                target[position] = row
    controls = owned.get("mm-source-control", [])
    if rejections:
        if len(rejections) != 1 or controls:
            return failure("Rejection did not stop the owner-bound source cursor")
        rejected = rejections[0]
        position = decode_nat(rejected.items[2])
        if position in admitted or any(at >= position for at in applied):
            return failure("A rejected statement was also committed or its suffix was executed")
        if set(applied) != {at for at in source.statements if at < position} or set(admitted) != {at for at in source.theorem_positions if at < position}:
            return failure("Rejection is missing the exact committed source prefix")
        return {"outcome": "rejected", "detail": render(rejected.items[4]), "source_position": position}
    if len(controls) != 1 or len(controls[0].items) != 3 or decode_nat(controls[0].items[2]) != source.end:
        return failure("No completed owner-bound source cursor")
    if set(applied) != set(source.statements):
        return failure("Source completion is missing exact statement-applied receipts")
    for tag in ("mm-source-start", "mm-source-current", "mm-source-action-running",
                "mm-source-theorem-pending", "mm-source-theorem-proof-context",
                "mm-normal-control", "mm-compressed-control", "mm-compressed-header-control",
                "mm-proof-fault", "mm-source-theorem-action-release", "mm-source-theorem-admission-pending"):
        if owned.get(tag):
            return failure(f"Source completion left an active {tag} cursor")
    incomplete: set[int] = set()
    for marker in owned.get("mm-compressed-proof-incomplete", []):
        if len(marker.items) != 5 or head(marker.items[2]) != "mm-source-proof-owner":
            return failure("An incomplete marker is not bound to a source proof owner")
        proof_owner = marker.items[2]
        if not isinstance(proof_owner, Expr) or len(proof_owner.items) != 3 or not atoms_equal((proof_owner.items[1],), (source.owner,)):
            return failure("An incomplete marker names a different source owner")
        position = decode_nat(proof_owner.items[2])
        if position not in source.theorem_positions:
            return failure("An incomplete marker names no original theorem")
        incomplete.add(position)
    if incomplete:
        if incomplete.intersection(admitted):
            return failure("A matching incomplete theorem was also admitted")
        if set(admitted) != source.theorem_positions - incomplete:
            return failure("Source completion is missing an admission for a different theorem")
        return {"outcome": "incomplete-proof", "detail": "Explicitly incomplete theorems reached the source outcome boundary without admission", "incomplete_positions": sorted(incomplete)}
    if set(admitted) != source.theorem_positions:
        return failure("Source completion is missing exact theorem-admission receipts")
    return {"outcome": "accepted", "detail": "All source statements completed and every theorem was admitted", "statements": source.end, "theorems": len(admitted)}
