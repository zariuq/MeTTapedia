"""Native compilation and ancestor-only reevaluation of incumbent circuits.

The arithmetic graph is exported from each incumbent's actual compiled object.
Optional private-atom unfolding is checked against every local input and seed
before native compilation. It uses ordinary Horn resolution, not commonality.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
import ctypes
from pathlib import Path
import math
import heapq
import json
import os
import subprocess
import time
from typing import Any

import numpy as np

from closure_response import Component, Rule, LocalState, Program, Unsupported, close


@lru_cache(maxsize=None)
def check_unfolding(width, choices, original, unfolded):
    """Exhaust the finite response interface, independently of query extraction."""
    mask = (1 << width) - 1
    for world in range(1 << choices):
        for seed in range(1 << width):
            initial = seed | (world << width)
            if close(original, initial) & mask != close(unfolded, initial) & mask:
                raise AssertionError('private-atom unfolding changed a response')


def unfold_private(program: Program) -> Program:
    """Eliminate private heads by Horn resolution and discard self-support rules.

    This ordinary source simplification can expand the rule set. Validation is
    exhaustive in the component's interface and base choices; it is a tested
    preprocessing pass, not a Lean-certified implementation.
    """
    program.validate()
    components = []
    for component in program.components:
        rules = {(r.head, frozenset(r.body)) for r in component.rules if r.head not in r.body}
        for private in component.private:
            definitions = [body for head, body in rules if head == private]
            result = set()
            for head, body in rules:
                if head == private:
                    continue
                replacements = [(body - {private}) | definition for definition in definitions] if private in body else [body]
                result.update((head, body) for body in replacements if head not in body)
            rules = result
        normalized = tuple(sorted((Rule(head, tuple(sorted(body))) for head, body in rules), key=lambda r: (r.head, r.body)))
        positions = {a: i for i, a in enumerate(program.boundary + component.choices + program.shared + component.private)}
        def encode(rs):
            return tuple((sum(1 << i for i in {positions[a] for a in r.body}), 1 << positions[r.head]) for r in rs)
        check_unfolding(len(program.boundary), len(component.choices) + len(program.shared), encode(component.rules), encode(normalized))
        components.append(Component(component.name, component.choices, (), normalized))
    result = Program(program.boundary, tuple(components), program.shared)
    result.validate()
    return result


@dataclass(frozen=True)
class Gate:
    operation: str
    children: tuple[int, ...] = ()
    payload: Any = None


class ArithmeticCircuit:
    def __init__(self):
        self.gates: list[Gate] = []
        self.interned: dict[Gate, int] = {}
        self.parents: list[set[int]] = []
        self.leaves: dict[int, int] = {}
        self.values: list[Any] = []
        self.visits = 0
        self.arithmetic = 0
        self.initialized = False

    def add(self, gate: Gate) -> int:
        if gate in self.interned:
            return self.interned[gate]
        index = len(self.gates)
        self.interned[gate] = index
        self.gates.append(gate)
        self.values.append(None)
        self.parents.append(set())
        for child in gate.children:
            if child >= index:
                raise AssertionError("circuit is not topologically ordered")
            self.parents[child].add(index)
        if gate.operation == 'leaf':
            self.leaves[gate.payload] = index
        return index

    def leaf(self, literal: int) -> int:
        return self.add(Gate('leaf', payload=literal))

    def constant(self, value: float) -> int:
        return self.add(Gate('constant', payload=value))

    def operation(self, operation: str, children) -> int:
        children = tuple(children)
        if not children:
            return self.constant(1.0 if operation == 'multiply' else 0.0)
        if len(children) == 1:
            return children[0]
        return self.add(Gate(operation, children))

    def _compute(self, index: int):
        gate = self.gates[index]
        if gate.operation == 'constant':
            self.values[index] = gate.payload
        elif gate.operation == 'add':
            self.values[index] = sum((self.values[c] for c in gate.children), 0.0)
            self.arithmetic += len(gate.children)
        elif gate.operation == 'multiply':
            value = 1.0
            for c in gate.children:
                value = value * self.values[c]
            self.values[index] = value
            self.arithmetic += len(gate.children)
        self.visits += 1

    def full(self, weights: dict[int, Any]):
        for index, gate in enumerate(self.gates):
            if gate.operation == 'leaf':
                self.values[index] = weights[gate.payload]
                self.visits += 1
            else:
                self._compute(index)
        self.initialized = True

    def update(self, weights: dict[int, Any]):
        if not self.initialized:
            raise RuntimeError("initialize before incremental updates")
        dirty = set()
        pending = []
        def enqueue(index):
            if index not in dirty:
                dirty.add(index)
                heapq.heappush(pending, index)
        for literal, value in weights.items():
            index = self.leaves.get(literal)
            if index is not None:
                if np.array_equal(self.values[index], value):
                    continue
                self.values[index] = value
                for parent in self.parents[index]:
                    enqueue(parent)
        while pending:
            index = heapq.heappop(pending)
            previous = self.values[index]
            self._compute(index)
            if not np.array_equal(previous, self.values[index]):
                for parent in self.parents[index]:
                    enqueue(parent)

    def rebalanced(self, roots):
        """Reassociate unshared arithmetic folds; retain every shared DAG node."""
        result = ArithmeticCircuit()
        protected = set(roots)
        mapped = {}
        children = {}
        for root in roots:
            pending = [(root, False)]
            while pending:
                index, ready = pending.pop()
                if index in mapped:
                    continue
                gate = self.gates[index]
                if gate.operation in ('leaf', 'constant'):
                    mapped[index] = result.add(gate)
                    continue
                if not ready:
                    expanded = []
                    todo = list(reversed(gate.children))
                    while todo:
                        child = todo.pop()
                        child_gate = self.gates[child]
                        if child_gate.operation == gate.operation and len(self.parents[child]) == 1 and child not in protected:
                            todo.extend(reversed(child_gate.children))
                        else:
                            expanded.append(child)
                    children[index] = expanded
                    pending.append((index, True))
                    pending.extend((child, False) for child in reversed(expanded) if child not in mapped)
                else:
                    level = [mapped[child] for child in children[index]]
                    while len(level) > 1:
                        level = [result.operation(gate.operation, level[j:j+2]) for j in range(0, len(level), 2)]
                    mapped[index] = level[0] if level else result.constant(1.0 if gate.operation == 'multiply' else 0.0)
        return result, [mapped[root] for root in roots]

    def pruned(self, roots):
        reachable = set()
        pending = list(roots)
        while pending:
            index = pending.pop()
            if index not in reachable:
                reachable.add(index)
                pending.extend(self.gates[index].children)
        graph, mapped = ArithmeticCircuit(), {}
        for index in sorted(reachable):
            gate = self.gates[index]
            mapped[index] = graph.add(Gate(gate.operation, tuple(mapped[c] for c in gate.children), gate.payload))
        return graph, [mapped[root] for root in roots]


class CircuitSemiring:
    def __init__(self, graph: ArithmeticCircuit):
        self.graph = graph

    def one(self):
        return self.graph.constant(1.0)

    def zero(self):
        return self.graph.constant(0.0)

    def plus(self, a, b):
        return self.graph.operation('add', (a, b))

    def times(self, a, b):
        return self.graph.operation('multiply', (a, b))

    @staticmethod
    def is_nsp():
        return True


def export_sdd(manager, nodes, variables):
    """Weighted evaluation in native vtree scopes, sharing smoothing products."""
    graph = ArithmeticCircuit()
    vtree = manager.get_manager().vtree()
    trees, normalizers = {}, {}
    pending = [(vtree, False)]
    while pending:
        tree, ready = pending.pop()
        position = tree.position()
        trees[position] = tree
        if tree.is_leaf():
            var = tree.var()
            if var not in variables:
                if manager.get_manager().var_count() == 1 and not variables:
                    normalizers[position] = graph.constant(1.0)
                else:
                    raise ValueError(f'unmapped native SDD variable {var}')
            else:
                normalizers[position] = graph.operation('add', (graph.leaf(var), graph.leaf(-var)))
        elif ready:
            normalizers[position] = graph.operation('multiply',
                (normalizers[tree.left().position()], normalizers[tree.right().position()]))
        else:
            pending.extend(((tree, True), (tree.right(), False), (tree.left(), False)))
    memo, descriptors = {}, {}
    roots = []
    for root in nodes:
        pending = [(root, vtree.position(), False)]
        while pending:
            node, scope, ready = pending.pop()
            key = (node.id, scope)
            if key in memo:
                continue
            tree = trees[scope]
            if node.is_false():
                memo[key] = graph.constant(0.0)
            elif node.is_true():
                memo[key] = normalizers[scope]
            elif ready:
                kind, dependencies, extra = descriptors[key]
                if kind == 'embed':
                    memo[key] = graph.operation('multiply', (memo[dependencies[0]], extra))
                else:
                    branches = [graph.operation('multiply', (memo[dependencies[j]], memo[dependencies[j+1]]))
                                for j in range(0, len(dependencies), 2)]
                    memo[key] = graph.operation('add', branches)
            else:
                position = node.vtree().position()
                if position == scope and node.is_literal():
                    memo[key] = graph.leaf(node.literal)
                    continue
                if tree.is_leaf():
                    raise ValueError('native SDD node outside its variable-tree scope')
                left, right = tree.left().position(), tree.right().position()
                children = []
                if position != scope:
                    child_scope, other_scope = (left, right) if position < scope else (right, left)
                    children = [(node, child_scope)]
                    descriptors[key] = ('embed', [(node.id, child_scope)], normalizers[other_scope])
                else:
                    for prime, sub in node.elements():
                        if not prime.is_false() and not sub.is_false():
                            children.extend(((prime, left), (sub, right)))
                    descriptors[key] = ('decision', [(child.id, child_scope) for child, child_scope in children], None)
                pending.append((node, scope, True))
                pending.extend((child, child_scope, False) for child, child_scope in reversed(children)
                               if (child.id, child_scope) not in memo)
        roots.append(memo[(root.id, vtree.position())])
    return graph.pruned(roots)


class CompiledArithmeticCircuit:
    """The identical arithmetic graph, evaluated by the small C++ cache."""
    def __init__(self, source: ArithmeticCircuit, lanes: int, library: Path):
        self.source, self.gates, self.leaves, self.lanes = source, source.gates, source.leaves, lanes
        self.library = ctypes.CDLL(str(library.resolve()))
        u32 = ctypes.POINTER(ctypes.c_uint32)
        f64 = ctypes.POINTER(ctypes.c_double)
        self.library.closure_dag_create.argtypes = [ctypes.c_uint32, ctypes.c_uint32, u32, u32, u32]
        self.library.closure_dag_create.restype = ctypes.c_void_p
        self.library.closure_dag_initialize.argtypes = [ctypes.c_void_p, f64]
        self.library.closure_dag_update.argtypes = [ctypes.c_void_p, ctypes.c_uint32, u32, f64]
        self.library.closure_dag_update.restype = ctypes.c_int
        self.library.closure_dag_values.argtypes = [ctypes.c_void_p]
        self.library.closure_dag_values.restype = f64
        self.library.closure_dag_stats.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint64)]
        self.library.closure_dag_reset_stats.argtypes = [ctypes.c_void_p]
        self.library.closure_dag_destroy.argtypes = [ctypes.c_void_p]
        operations, offsets, children = [], [0], []
        for gate in source.gates:
            if gate.operation == 'constant' and gate.payload not in (0.0, 1.0):
                raise Unsupported('compiled Boolean-counting adapter expects zero/one constants')
            operations.append({'leaf': 0, 'add': 3, 'multiply': 4}.get(gate.operation,
                               2 if gate.payload == 1 else 1))
            children.extend(gate.children)
            offsets.append(len(children))
        arrays = [np.ascontiguousarray(values, dtype=np.uint32) for values in (operations, offsets, children)]
        self.pointer = self.library.closure_dag_create(len(source.gates), lanes,
            *(array.ctypes.data_as(u32) for array in arrays))
        if not self.pointer:
            raise ValueError('compiled evaluator rejected graph')
        self._values = np.ctypeslib.as_array(self.library.closure_dag_values(self.pointer),
                                             shape=(len(source.gates) * lanes,)).reshape((-1, lanes))
        self.initialized = False

    @property
    def values(self):
        return self._values[:, 0] if self.lanes == 1 else self._values

    def full(self, weights):
        data = np.zeros((len(self.gates), self.lanes), dtype=np.float64)
        for literal, index in self.leaves.items():
            data[index] = weights[literal]
        self.library.closure_dag_initialize(self.pointer, data.ctypes.data_as(ctypes.POINTER(ctypes.c_double)))
        self.initialized = True

    def update(self, weights):
        if not self.initialized:
            raise RuntimeError('initialize before incremental updates')
        chosen = [(self.leaves[literal], value) for literal, value in weights.items() if literal in self.leaves]
        indices = np.ascontiguousarray([index for index, _ in chosen], dtype=np.uint32)
        values = np.empty((len(chosen), self.lanes), dtype=np.float64)
        for i, (_, value) in enumerate(chosen):
            values[i] = value
        accepted = self.library.closure_dag_update(self.pointer, len(chosen),
            indices.ctypes.data_as(ctypes.POINTER(ctypes.c_uint32)),
            values.ctypes.data_as(ctypes.POINTER(ctypes.c_double)))
        if not accepted:
            raise ValueError('compiled evaluator rejected update')

    def _statistics(self):
        values = (ctypes.c_uint64 * 2)()
        self.library.closure_dag_stats(self.pointer, values)
        return values

    @property
    def visits(self):
        return self._statistics()[0]

    @visits.setter
    def visits(self, value):
        if value != 0:
            raise ValueError('statistics can only be reset')
        self.library.closure_dag_reset_stats(self.pointer)

    @property
    def arithmetic(self):
        return self._statistics()[1]

    @arithmetic.setter
    def arithmetic(self, value):
        self.visits = value

    def __del__(self):
        pointer = getattr(self, 'pointer', None)
        if pointer:
            self.library.closure_dag_destroy(pointer)
            self.pointer = None


def source_text(program: Program, *, evidence_declarations: bool) -> tuple[str, dict[str, str]]:
    """Use the identical ground rules and choices in both compiler frontends."""
    program.validate()
    atoms = list(program.boundary) + list(program.shared)
    for component in program.components:
        atoms.extend(component.choices + component.private)
    names = {name: f'a{i}' for i, name in enumerate(atoms)}
    chance = list(program.shared) + [a for c in program.components for a in c.choices]
    lines = [f'0.5::{names[a]}.' for a in chance]
    for i, port in enumerate(program.boundary):
        lines.extend((f'0.5::seed{i}.', f'{names[port]} :- seed{i}.'))
    for component in program.components:
        for rule in component.rules:
            body = ','.join(names[a] for a in rule.body)
            lines.append(f'{names[rule.head]}' + (f' :- {body}.' if body else '.'))
    lines.extend(f'query({names[port]}).' for port in program.boundary)
    if evidence_declarations:
        lines.extend(f'evidence({names[a]},none).' for a in chance)
        lines.extend(f'evidence(seed{i},none).' for i in range(len(program.boundary)))
    return '\n'.join(lines) + '\n', names


def choice_weights(program: Program, states: list[LocalState], shared: LocalState, seed: int,
                   components=None, *, include_shared=True, include_seed=True):
    result = {}
    ids = range(len(states)) if components is None else components
    for i in ids:
        for name, p, evidence in zip(program.components[i].choices, states[i].probabilities, states[i].evidence):
            result[name] = (float(p) if evidence is not False else 0.0,
                            float(1 - p) if evidence is not True else 0.0)
    if include_shared:
        for name, p, evidence in zip(program.shared, shared.probabilities, shared.evidence):
            result[name] = (float(p) if evidence is not False else 0.0,
                            float(1 - p) if evidence is not True else 0.0)
    if include_seed:
        for i in range(len(program.boundary)):
            result[f'@seed{i}'] = (float(bool(seed >> i & 1)), float(not (seed >> i & 1)))
    return result


class ProbLogSDD:
    def __init__(self, program: Program, artifact: Path, *, targets=None, forward=False, timeout=None, grouped=False, unfold=False):
        from problog import get_evaluatable
        from problog.program import PrologString
        self.program = program
        self.targets = list(range(len(program.boundary))) if targets is None else list(targets)
        if unfold:
            program = unfold_private(program)
        text, names = source_text(program, evidence_declarations=True)
        artifact = artifact.resolve()
        artifact.mkdir(parents=True, exist_ok=True)
        (artifact / 'source.pl').write_text(text)
        started = time.perf_counter()
        if forward:
            from problog.formula import LogicFormula
            from problog.forward import _ForwardSDD
            from problog.dd_formula import build_dd
            ground = LogicFormula.create_from(PrologString(text))
            print(json.dumps({'stage': 'grounded', 'nodes': len(ground), 'seconds': time.perf_counter() - started}), flush=True)
            if grouped:
                from problog.sdd_formula import x_constrained
                order = [f'seed{i}' for i in range(len(program.boundary))] + [names[a] for a in program.shared]
                external_count = len(order)
                order += [names[a] for component in program.components for a in component.choices]
                class OrderedForward(_ForwardSDD):
                    def build_dd(inner):
                        named_atoms = {str(name): index for name, index in inner.get_names()}
                        for name in order:
                            inner.get_inode(named_atoms[name])
                        return super().build_dd()
                destination = OrderedForward(init_varcount=len(order), sdd_auto_gc=True,
                    var_constraint=x_constrained(set(range(1, external_count + 1))),
                    compile_timeout=None if timeout is None else int(timeout))
            else:
                destination = _ForwardSDD(compile_timeout=None if timeout is None else int(timeout))
            self.knowledge = build_dd(ground, destination)
            for _, index in self.knowledge.queries():
                if self.knowledge.is_probabilistic(index) and not self.knowledge.is_complete(index):
                    raise TimeoutError('forward compilation returned an incomplete query')
        else:
            from problog.formula import LogicFormula, LogicDAG
            ground = LogicFormula.create_from(PrologString(text))
            print(json.dumps({'stage': 'grounded', 'nodes': len(ground), 'seconds': time.perf_counter() - started}), flush=True)
            dag = LogicDAG.create_from(ground)
            print(json.dumps({'stage': 'cycles_broken', 'nodes': len(dag), 'seconds': time.perf_counter() - started}), flush=True)
            self.knowledge = get_evaluatable(name='sdd').create_from(dag)
        self.compile_seconds = time.perf_counter() - started
        print(json.dumps({'stage': 'native_compiled', 'seconds': self.compile_seconds}), flush=True)
        self.manager = self.knowledge.get_manager()
        named = {str(name): index for name, index in self.knowledge.get_names()}
        self.variables = {}
        chance = list(program.shared) + [a for c in program.components for a in c.choices]
        for name in chance:
            self.variables[name] = self.knowledge.atom2var[named[names[name]]]
        for i in range(len(program.boundary)):
            self.variables[f'@seed{i}'] = self.knowledge.atom2var[named[f'seed{i}']]
        constraints = self.knowledge.get_constraint_inode()
        self.nodes = [constraints]
        for port in (program.boundary[i] for i in self.targets):
            self.nodes.append(self.manager.conjoin(constraints, self.knowledge.get_inode(named[names[port]])))
        for node in self.nodes:
            self.manager.ref(node)
        variables = set(self.variables.values())
        self.graph, self.roots = export_sdd(self.manager, self.nodes, variables)
        self.weights = {}
        self.artifact = artifact

    def rebalance(self):
        self.graph, self.roots = self.graph.rebalanced(self.roots)

    def set_state(self, states, shared, seed, changed=None, *, include_shared=True, include_seed=True, evaluation='incremental'):
        changed_weights = choice_weights(self.program, states, shared, seed, changed,
                                        include_shared=include_shared, include_seed=include_seed)
        literals = {}
        for name, (pos, neg) in changed_weights.items():
            var = self.variables[name]
            self.weights[var] = (pos, neg)
            literals[var], literals[-var] = pos, neg
        if evaluation == 'native':
            return self.native()
        if changed is None or not self.graph.initialized:
            self.graph.full(literals)
        else:
            self.graph.update(literals)
        return self.results()

    def results(self):
        denominator = self.graph.values[self.roots[0]]
        return None if denominator == 0 else [self.graph.values[r] / denominator for r in self.roots[1:]]

    def full_graph(self):
        literals = {literal: values[0 if literal > 0 else 1]
                    for var, values in self.weights.items() for literal in (var, -var)}
        self.graph.full(literals)
        return self.results()

    def native(self):
        from problog.evaluator import SemiringProbability
        semiring = SemiringProbability()
        denominator = self.manager.wmc(self.nodes[0], self.weights, semiring)
        if denominator == 0:
            return None
        return [self.manager.wmc(node, self.weights, semiring) / denominator for node in self.nodes[1:]]


def read_ddnnf(path: Path) -> tuple[ArithmeticCircuit, int]:
    graph = ArithmeticCircuit()
    source_nodes = []
    with path.open() as stream:
        header = stream.readline().split()
        if len(header) != 4 or header[0] not in ('nnf', 'sdd'):
            raise ValueError(f'unsupported circuit header {header}')
        for line in stream:
            fields = line.split()
            if not fields or fields[0] == 'c':
                continue
            if fields[0] == 'L':
                node = graph.leaf(int(fields[1]))
            elif fields[0] == 'A':
                node = graph.operation('multiply', [source_nodes[int(x)] for x in fields[2:]])
            elif fields[0] == 'O':
                node = graph.operation('add', [source_nodes[int(x)] for x in fields[3:]])
            else:
                raise ValueError(f'unsupported circuit record {fields[:2]}')
            source_nodes.append(node)
    if not source_nodes:
        raise ValueError('empty compiled circuit')
    return graph, source_nodes[-1]


def read_d4(path: Path) -> tuple[ArithmeticCircuit, int]:
    """Preserve d4's edge literals and smoothing factors in a cached arithmetic DAG."""
    graph, values, multiplicative = ArithmeticCircuit(), [None], [False]
    with path.open() as stream:
        for line in stream:
            fields = line.split()
            if not fields:
                continue
            if fields[0] in ('t', 'f', 'a', 'o'):
                if int(fields[1]) != len(values):
                    raise Unsupported('nonsequential d4 node declaration')
                product = fields[0] in ('t', 'a')
                values.append(graph.constant(int(product)))
                multiplicative.append(product)
            else:
                parent, child = map(int, fields[:2])
                if not 0 < parent < len(values) or not 0 < child < len(values):
                    raise Unsupported('undeclared d4 edge endpoint')
                value = values[child]
                if not multiplicative[parent]:
                    cut = fields.index('0', 2)
                    factors = [value] + [graph.leaf(int(x)) for x in fields[2:cut]]
                    if fields[-1] != '0':
                        raise Unsupported('unterminated d4 smoothing list')
                    factors += [graph.operation('add', [graph.leaf(int(x)), graph.leaf(-int(x))])
                                for x in fields[cut + 1:-1]]
                    value = graph.operation('multiply', factors)
                values[parent] = graph.operation('multiply' if multiplicative[parent] else 'add',
                                                 [values[parent], value])
    if len(values) == 1:
        raise Unsupported('empty d4 circuit')
    return graph, values[1]


def native_cached_circuit(graph: ArithmeticCircuit, variable_count: int):
    """Instantiate the incumbent evaluator with distinct reverse-edge lists.

    Literal occurrences share their native input object, and every arithmetic
    node retains its actual children. This avoids shared mutable default lists
    in the external Node constructor and duplicate input queue entries.
    """
    from aspmc.compile.circuit import Circuit, Node
    result = Circuit.__new__(Circuit)
    result.literals = [Node(Node.IN if sign > 0 else Node.NEG, sign * var, [], [])
                       for var in range(1, variable_count + 1) for sign in (1, -1)]
    result.nodes = []
    for index, gate in enumerate(graph.gates):
        if gate.operation == 'leaf':
            literal = gate.payload
            node = result.literals[2 * (abs(literal) - 1) + (literal < 0)]
        else:
            kind = Node.AND if gate.operation == 'multiply' or (gate.operation == 'constant' and gate.payload == 1) else Node.OR
            node = Node(kind, index, [result.nodes[c] for c in gate.children], [])
            for child in node.children:
                child.ancestors.append(node)
        result.nodes.append(node)
    return result


class ASPMC:
    def __init__(self, program: Program, artifact: Path, *, timeout: float | None = None, cache_mb: int | None = None, targets=None, unfold=False, compiler='sharpsat', fixed_seed=None):
        import aspmc
        from aspmc.programs.problogprogram import ProblogProgram
        self.program = program
        self.fixed_seed = fixed_seed
        if fixed_seed is not None and not 0 <= fixed_seed < 1 << len(program.boundary):
            raise Unsupported('fixed seed outside interface')
        self.targets = list(range(len(program.boundary))) if targets is None else list(targets)
        if unfold:
            program = unfold_private(program)
        artifact = artifact.resolve()
        artifact.mkdir(parents=True, exist_ok=True)
        text, names = source_text(program, evidence_declarations=False)
        (artifact / 'source.pl').write_text(text)
        started = time.perf_counter()
        self.compiled = ProblogProgram(text, [])
        print(json.dumps({'stage': 'aspmc_grounded', 'atoms': len(self.compiled._nameMap),
                          'seconds': time.perf_counter() - started}), flush=True)
        self.compiled.tpUnfold()
        print(json.dumps({'stage': 'aspmc_unfolded', 'atoms': len(self.compiled._nameMap),
                          'seconds': time.perf_counter() - started}), flush=True)
        self.compiled.td_guided_both_clark_completion()
        cnf = self.compiled.get_cnf()
        if fixed_seed is not None:
            named = {name: var for var, name in self.compiled._nameMap.items()}
            cnf.clauses += [[named[f'seed{i}'] if fixed_seed >> i & 1 else -named[f'seed{i}']]
                           for i in range(len(program.boundary))]
        print(json.dumps({'stage': 'aspmc_cnf', 'variables': cnf.nr_vars, 'clauses': len(cnf.clauses),
                          'seconds': time.perf_counter() - started}), flush=True)
        self.variable_count = cnf.nr_vars
        cnf_path = artifact / 'program.cnf'
        with cnf_path.open('wb') as stream:
            cnf.write_kc_cnf(stream)
        self.nnf = artifact / 'program.cnf.nnf'
        if compiler == 'sharpsat':
            executable = Path(aspmc.__file__).parent / 'external/sharpsat-td/bin/sharpSAT'
            command = [str(executable), '-dDNNF', '-decot', '1', '-decow', '100',
                       '-tmpdir', str(artifact), str(cnf_path), '-dDNNF_out', str(self.nnf)]
            if cache_mb is not None:
                command[1:1] = ['-cs', str(cache_mb)]
        elif compiler == 'd4':
            executable = Path(aspmc.__file__).parent / 'external/d4/d4_static'
            command = [str(executable), str(cnf_path), '-dDNNF', f'-out={self.nnf}', '-smooth']
        else:
            raise Unsupported('unknown ASPMC compiler')
        with (artifact / 'compiler.log').open('wb') as output:
            subprocess.run(command, cwd=executable.parent, stdout=output, stderr=subprocess.STDOUT,
                           timeout=timeout, check=True)
        self.compile_seconds = time.perf_counter() - started
        self.graph, self.root = (read_d4 if compiler == 'd4' else read_ddnnf)(self.nnf)
        self.graph, roots = self.graph.pruned([self.root])
        self.root = roots[0]
        self.native_circuit = native_cached_circuit(self.graph, self.variable_count)
        self.native_root = self.root
        variable_map = {name: var for var, name in self.compiled._nameMap.items()}
        chance = list(program.shared) + [a for c in program.components for a in c.choices]
        self.variables = {name: variable_map[names[name]] for name in chance}
        self.variables.update({f'@seed{i}': variable_map[f'seed{i}'] for i in range(len(program.boundary))})
        self.query_vars = [variable_map[names[program.boundary[i]]] for i in self.targets]
        self.lanes = len(self.query_vars) + 1
        self.weights = {literal: np.ones(self.lanes) for i in range(1, self.variable_count + 1) for literal in (i, -i)}
        for lane, var in enumerate(self.query_vars, 1):
            self.weights[-var][lane] = 0.0

    def rebalance(self):
        self.graph, roots = self.graph.rebalanced([self.root])
        self.root = roots[0]

    def set_state(self, states, shared, seed, changed=None, *, include_shared=True, include_seed=True, evaluation='incremental'):
        if self.fixed_seed is not None and seed != self.fixed_seed:
            raise Unsupported('compiled for a different fixed seed')
        raw = choice_weights(self.program, states, shared, seed, changed,
                             include_shared=include_shared, include_seed=include_seed)
        updates = {}
        for name, pair in raw.items():
            var = self.variables[name]
            for literal, value in zip((var, -var), pair):
                self.weights[literal] = np.full(self.lanes, value)
                updates[literal] = self.weights[literal]
        if evaluation == 'native':
            return self.native()
        if changed is None or not self.graph.initialized:
            self.graph.full(self.weights)
        else:
            self.graph.update(updates)
        return self.results()

    def results(self):
        values = self.graph.values[self.root]
        return None if values[0] == 0 else list(values[1:] / values[0])

    def full_graph(self):
        self.graph.full(self.weights)
        return self.results()

    def native(self):
        weights = [self.weights[literal] for i in range(1, self.variable_count + 1) for literal in (i, -i)]
        self.native_circuit.wmc(weights)
        result = self.native_circuit.nodes[self.native_root].weight
        return None if result[0] == 0 else list(result[1:] / result[0])
