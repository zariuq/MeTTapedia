"""Small, iterative reader for MORK's textual atom format.

Symbol spelling, quoted tokens, variables, expression arities, and form order
are retained.  Quoted tokens are not JSON strings: MORK interns their complete
text, including quotes and escapes.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from pathlib import Path
from typing import Iterable, Iterator, TypeAlias


class AtomSyntaxError(ValueError):
    """A malformed textual atom, with its source offset."""


@dataclass(frozen=True, slots=True)
class Symbol:
    text: str

    @property
    def is_variable(self) -> bool:
        return self.text.startswith("$")


@dataclass(frozen=True, slots=True, eq=False)
class Expr:
    items: tuple[Atom, ...]

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Expr) and atoms_equal((self,), (other,))

    __hash__ = None


Atom: TypeAlias = Symbol | Expr


@dataclass(frozen=True, slots=True)
class Form:
    atom: Atom
    start: int
    end: int


def parse_forms(source: str) -> list[Form]:
    """Parse complete top-level forms without recursive Python calls.

    The separators and semicolon-comment boundary match MORK's reader: space,
    tab, newline; a semicolon begins a comment only at the start of a token.
    """
    forms: list[Form] = []
    stack: list[tuple[int, list[Atom]]] = []
    index = 0
    length = len(source)
    separators = " \t\n"

    def append(atom: Atom, start: int, end: int) -> None:
        if stack:
            stack[-1][1].append(atom)
        else:
            forms.append(Form(atom, start, end))

    while index < length:
        char = source[index]
        if char in separators:
            index += 1
        elif char == ";":
            newline = source.find("\n", index)
            index = length if newline == -1 else newline + 1
        elif char == "(":
            stack.append((index, []))
            index += 1
        elif char == ")":
            if not stack:
                raise AtomSyntaxError(f"Unexpected ')' at offset {index}")
            start, items = stack.pop()
            index += 1
            append(Expr(tuple(items)), start, index)
        else:
            start = index
            if char == '"':
                index += 1
                while index < length:
                    char = source[index]
                    if char == "\\":
                        index += 2
                    elif char == '"':
                        index += 1
                        break
                    else:
                        index += 1
                else:
                    raise AtomSyntaxError(f"Unterminated quoted token at offset {start}")
                if index > length:
                    raise AtomSyntaxError(f"Unterminated quoted token at offset {start}")
            else:
                while index < length and source[index] not in "() \t\n":
                    index += 1
            append(Symbol(source[start:index]), start, index)
    if stack:
        raise AtomSyntaxError(f"Unclosed '(' at offset {stack[-1][0]}")
    return forms


def parse_atoms(source: str) -> list[Atom]:
    return [form.atom for form in parse_forms(source)]


def read_atoms(path: str | Path) -> list[Atom]:
    return parse_atoms(Path(path).read_text(encoding="utf-8"))


def head(atom: Atom) -> str | None:
    if isinstance(atom, Expr) and atom.items and isinstance(atom.items[0], Symbol):
        return atom.items[0].text
    return None


def walk(atom: Atom) -> Iterator[Atom]:
    pending = [atom]
    while pending:
        current = pending.pop()
        yield current
        if isinstance(current, Expr):
            pending.extend(reversed(current.items))


def atoms_equal(left: Iterable[Atom], right: Iterable[Atom]) -> bool:
    left_items, right_items = tuple(left), tuple(right)
    if len(left_items) != len(right_items):
        return False
    pending = list(zip(left_items, right_items))
    while pending:
        first, second = pending.pop()
        if isinstance(first, Symbol):
            if not isinstance(second, Symbol) or first.text != second.text:
                return False
        elif not isinstance(second, Expr) or len(first.items) != len(second.items):
            return False
        else:
            pending.extend(zip(first.items, second.items))
    return True


def atom_digest(atoms: Iterable[Atom]) -> str:
    """SHA-256 of an unambiguous arity/token encoding, not source formatting."""
    roots = tuple(atoms)
    digest = hashlib.sha256(b"mm2-parsed-atoms-v1\0")
    digest.update(len(roots).to_bytes(8, "big"))
    pending = list(reversed(roots))
    while pending:
        atom = pending.pop()
        if isinstance(atom, Symbol):
            token = atom.text.encode("utf-8")
            digest.update(b"V" if atom.is_variable else b"S")
            digest.update(len(token).to_bytes(8, "big"))
            digest.update(token)
        else:
            digest.update(b"E")
            digest.update(len(atom.items).to_bytes(8, "big"))
            pending.extend(reversed(atom.items))
    return digest.hexdigest()


def render(atom: Atom) -> str:
    chunks: list[str] = []
    pending: list[Atom | str] = [atom]
    while pending:
        current = pending.pop()
        if isinstance(current, str):
            chunks.append(current)
        elif isinstance(current, Symbol):
            chunks.append(current.text)
        else:
            chunks.append("(")
            pending.append(")")
            for index in range(len(current.items) - 1, -1, -1):
                pending.append(current.items[index])
                if index:
                    pending.append(" ")
    return "".join(chunks)


def render_atoms(atoms: Iterable[Atom]) -> str:
    return "".join(render(atom) + "\n" for atom in atoms)
