"""Reproducible local/global-change workloads for closure-response inference."""
from __future__ import annotations

import argparse
from decimal import Decimal
from fractions import Fraction
import gzip
import hashlib
import json
import os
from pathlib import Path
import pickle
import random
import resource
import time

from closure_response import Component, Engine, LocalState, Prepared, Program, Rule
from closure_response_baselines import ASPMC, ProbLogSDD, CompiledArithmeticCircuit
from closure_response_ablations import DirectEngine, DirectPrepared


def probabilities(rng: random.Random, count: int, choices: int = 4):
    activation = min(Fraction(7, 8), rng.choice([Fraction(1, 2), Fraction(2), Fraction(8)]) *
                     rng.choice([Fraction(5, 8), Fraction(7, 8), Fraction(9, 8), Fraction(11, 8)]) / count)
    return (activation,) + tuple(rng.choice([Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)]) for _ in range(choices - 1))


def workload(count: int, width: int, generator_seed: int, depth: int = 8):
    if width < 2 or count < 1 or depth < 2:
        raise ValueError('workload requires width >= 2, components >= 1, depth >= 2')
    rng = random.Random(generator_seed)
    boundary = tuple(f'b{i}' for i in range(width))
    components, states = [], []
    for i in range(count):
        choices = tuple(f'm{i}_c{j}' for j in range(4))
        private = tuple(f'm{i}_p{j}' for j in range(depth))
        ports = rng.sample(boundary, len(boundary))
        a, b, c = ports[0], ports[1], ports[2 % width]
        rules = [Rule(private[0], (a, choices[0])), Rule(private[1], (private[0], choices[1]))]
        rules.extend(Rule(private[j + 1], (private[j],)) for j in range(1, depth - 1))
        rules.extend((Rule(private[0], (private[-1],)), Rule(b, (private[-1],)),
                      Rule(c, (b, choices[0], choices[2])), Rule(a, (c, choices[0], choices[3])),
                      Rule(c, (a, b, choices[0], choices[3]))))
        for port in ports[3:]:
            rules.extend((Rule(port, (b, c, choices[0], choices[2])), Rule(a, (port, choices[0], choices[3]))))
        components.append(Component(f'm{i}', choices, private, tuple(rules)))
        states.append(LocalState.make(probabilities(rng, count)))
    return Program(boundary, tuple(components)), states


def update_trace(initial, count, steps, changed_count, generator_seed, global_churn=False):
    rng = random.Random(100003 * generator_seed + changed_count)
    states = list(initial)
    evidence_bank = rng.sample(range(count), min(8, count))
    trace = []
    digest = hashlib.sha256()
    for step in range(steps):
        evidence_step = not global_churn and step % 5 == 4
        pool = evidence_bank if evidence_step else range(count)
        selected = list(range(count)) if global_churn else rng.sample(list(pool), min(changed_count, len(pool)))
        changed = {}
        for index in selected:
            previous = states[index]
            if evidence_step:
                evidence = list(previous.evidence)
                evidence[rng.randrange(len(evidence))] = rng.choice([None, True, False])
                state = LocalState.make(previous.probabilities, evidence)
            else:
                state = LocalState.make(probabilities(rng, count), previous.evidence)
            states[index] = state
            changed[index] = state
            digest.update(repr((step, index, state)).encode())
        trace.append(changed)
    return trace, digest.hexdigest()


def cpu_time():
    own = time.process_time()
    children = resource.getrusage(resource.RUSAGE_CHILDREN)
    return own + children.ru_utime + children.ru_stime


def answer_record(answer):
    if answer.enclosure is None:
        return {'answer': None, 'fallback': answer.fallback}
    return {'answer': [str(answer.enclosure.lo), str(answer.enclosure.hi)],
            'cancellation': [str(answer.cancellation.lo), str(answer.cancellation.hi)],
            'fallback': answer.fallback, 'exact': answer.exact is not None}


def write_output(path: Path, rows):
    with gzip.open(path, 'wt', encoding='utf8') as output:
        for row in rows:
            output.write(json.dumps(row, separators=(',', ':')) + '\n')


def closure_run(program, initial, trace, seed, targets, mode, output, timeout=None):
    queries = [(1 << source, target) for source in range(len(program.boundary))
               for target in range(len(program.boundary)) if source != target]
    before, cpu = time.perf_counter(), cpu_time()
    prepared = DirectPrepared(program) if mode == 'direct' else Prepared(program, queries)
    engine = DirectEngine(prepared, initial) if mode == 'direct' else Engine(prepared, initial)
    first = [engine.query(seed, target) for target in targets]
    preparation = time.perf_counter() - before
    preparation_cpu = cpu_time() - cpu
    compiled_bytes = len(pickle.dumps(prepared, protocol=5))
    cache_bytes = len(pickle.dumps(engine.tree.values, protocol=5))
    engine.ops.operations = engine.tree.visits = 0
    rows = []
    before, cpu = time.perf_counter(), cpu_time()
    for step, changed in enumerate(trace):
        if timeout is not None and time.perf_counter() - before > timeout:
            break
        if mode == 'closure_full':
            states = list(engine.states)
            for index, state in changed.items():
                states[index] = state
            old_ops, old_visits, old_fallbacks = engine.ops.operations, engine.tree.visits, engine.fallbacks
            old_exact = engine.exact_ops.operations
            engine = Engine(prepared, states)
            engine.ops.operations += old_ops
            engine.tree.visits += old_visits
            engine.fallbacks += old_fallbacks
            engine.exact_ops.operations += old_exact
        else:
            engine.update(changed)
        rows.append([answer_record(engine.query(seed, target)) for target in targets])
    elapsed, elapsed_cpu = time.perf_counter() - before, cpu_time() - cpu
    write_output(output / f'{mode}.jsonl.gz', rows)
    return {'mode': mode, 'complete': len(rows) == len(trace), 'updates_completed': len(rows),
            'preparation_wall_s': preparation, 'preparation_cpu_s': preparation_cpu,
            'update_wall_s': elapsed, 'update_cpu_s': elapsed_cpu,
            'total_wall_s': preparation + elapsed, 'total_cpu_s': preparation_cpu + elapsed_cpu,
            'compiled_structure_bytes': compiled_bytes, 'cache_bytes_initial': cache_bytes,
            'retained_rows': len(prepared.families) if mode != 'direct' else None,
            'convolution_products': engine.convolution.products if mode == 'direct' else None,
            'interval_operations': engine.ops.operations,
            'rational_operations': engine.exact_ops.operations, 'product_tree_visits': engine.tree.visits,
            'fallbacks': engine.fallbacks, 'first': [answer_record(a) for a in first],
            'output': f'{mode}.jsonl.gz'}


def incumbent_run(backend, initial, shared, trace, seed, mode, output, preparation, preparation_cpu, timeout=None):
    before, cpu = time.perf_counter(), cpu_time()
    evaluation = 'native' if mode.endswith('_native') else 'incremental'
    states = list(initial)
    first = backend.set_state(states, shared, seed, evaluation=evaluation)
    initialization, initialization_cpu = time.perf_counter() - before, cpu_time() - cpu
    backend.graph.visits = backend.graph.arithmetic = 0
    rows = []
    before, cpu = time.perf_counter(), cpu_time()
    for changed in trace:
        if timeout is not None and time.perf_counter() - before > timeout:
            break
        for index, state in changed.items():
            states[index] = state
        result = backend.set_state(states, shared, seed, changed,
                                   include_shared=False, include_seed=False, evaluation=evaluation)
        rows.append(None if result is None else [float(x) for x in result])
    elapsed, elapsed_cpu = time.perf_counter() - before, cpu_time() - cpu
    write_output(output / f'{mode}.jsonl.gz', rows)
    structure = (backend.graph.gates, backend.roots if hasattr(backend, 'roots') else [backend.root], backend.variables)
    return {'mode': mode, 'complete': len(rows) == len(trace), 'updates_completed': len(rows),
            'preparation_wall_s': preparation + initialization,
            'preparation_cpu_s': preparation_cpu + initialization_cpu,
            'update_wall_s': elapsed, 'update_cpu_s': elapsed_cpu,
            'total_wall_s': preparation + initialization + elapsed,
            'total_cpu_s': preparation_cpu + initialization_cpu + elapsed_cpu,
            'arithmetic_export_bytes': len(pickle.dumps(structure, protocol=5)),
            'cache_bytes_final': len(pickle.dumps(backend.graph.values, protocol=5)),
            'arithmetic_nodes': len(backend.graph.gates),
            'node_visits': None if evaluation == 'native' else backend.graph.visits,
            'arithmetic_operations': None if evaluation == 'native' else backend.graph.arithmetic,
            'first': None if first is None else [float(x) for x in first], 'output': f'{mode}.jsonl.gz'}


def compare_outputs(reference: Path, candidate: Path):
    count = 0
    with gzip.open(reference, 'rt') as left, gzip.open(candidate, 'rt') as right:
        while True:
            a, b = left.readline(), right.readline()
            if not a and not b:
                break
            if not a or not b:
                raise AssertionError('different update counts')
            expected, actual = json.loads(a), json.loads(b)
            if all(item['answer'] is None for item in expected):
                if actual is not None:
                    raise AssertionError(('impossible evidence', count, actual))
            else:
                if actual is None or len(actual) != len(expected):
                    raise AssertionError(('missing answer', count, actual))
                for index, (item, value) in enumerate(zip(expected, actual)):
                    if not isinstance(value, (int, float)) or not __import__('math').isfinite(value):
                        raise AssertionError(('nonfinite answer', count, index, value))
                    lo, hi = (Fraction(Decimal(x)) for x in item['answer'])
                    point = Fraction(value)
                    error = max(abs(point - lo), abs(point - hi))
                    if error > Fraction(1, 10**12) or (lo > 0 and error > Fraction(1, 10**10) * lo):
                        raise AssertionError(('accuracy disagreement', count, index, item, value))
            count += 1
    return count


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--system', choices=['closure', 'closure_full', 'direct', 'problog', 'problog_forward', 'problog_grouped', 'problog_unfold', 'aspmc', 'aspmc_unfold', 'aspmc_d4_fixed'], required=True)
    parser.add_argument('--components', type=int, required=True)
    parser.add_argument('--width', type=int, default=3)
    parser.add_argument('--generator-seed', type=int, default=7)
    parser.add_argument('--updates', type=int, default=10000)
    parser.add_argument('--changed', type=int, default=1)
    parser.add_argument('--global-churn', action='store_true')
    parser.add_argument('--depth', type=int, default=8)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache-mb', type=int)
    parser.add_argument('--compile-timeout', type=float)
    parser.add_argument('--mode-timeout', type=float)
    parser.add_argument('--diagnostic-updates', type=int, default=0)
    parser.add_argument('--compiled-library', type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    program, initial = workload(args.components, args.width, args.generator_seed, args.depth)
    trace, trace_hash = update_trace(initial, args.components, args.updates, args.changed,
                                    args.generator_seed, args.global_churn)
    seed_index = {7: 0, 19: 1, 43: 2}.get(args.generator_seed, args.generator_seed % args.width) % args.width
    seed = 1 << seed_index
    targets = [i for i in range(args.width) if i != seed_index]
    metadata = {'system': args.system, 'components': args.components, 'width': args.width,
                'generator_seed': args.generator_seed, 'updates': args.updates, 'changed': args.changed,
                'global_churn': args.global_churn, 'depth': args.depth, 'seed_mask': seed, 'targets': targets,
                'trace_sha256': trace_hash, 'source_sha256': hashlib.sha256(repr(program).encode()).hexdigest(),
                'initial_state_sha256': hashlib.sha256(repr(initial).encode()).hexdigest(),
                'implementation_sha256': {name: hashlib.sha256((Path(__file__).parent / name).read_bytes()).hexdigest()
                    for name in ['closure_response.py', 'closure_response_ablations.py', 'closure_response_baselines.py', 'run_closure_response.py', 'closure_response_dag.cpp']},
                'results': [], 'status': 'preparing'}
    if args.compiled_library:
        metadata['compiled_library_sha256'] = hashlib.sha256(args.compiled_library.read_bytes()).hexdigest()
    def save():
        metadata['self_peak_rss_bytes'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
        metadata['child_peak_rss_bytes'] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * 1024
        (output / f'{args.system}-result.json').write_text(json.dumps(metadata, indent=2) + '\n')
    save()
    print(json.dumps({'stage': 'preparing', 'system': args.system, 'components': args.components}), flush=True)
    if args.system.startswith('closure') or args.system == 'direct':
        metadata['results'].append(closure_run(program, initial, trace, seed, targets, args.system, output, args.mode_timeout))
    else:
        before, cpu = time.perf_counter(), cpu_time()
        backend = (ProbLogSDD(program, output / 'compiled', targets=targets,
                             forward=args.system in ('problog_forward', 'problog_grouped', 'problog_unfold'),
                             grouped=args.system in ('problog_grouped', 'problog_unfold'),
                             unfold=args.system.endswith('_unfold'), timeout=args.compile_timeout) if args.system.startswith('problog') else
                   ASPMC(program, output / 'compiled', targets=targets,
                         timeout=args.compile_timeout, cache_mb=args.cache_mb,
                         unfold=args.system.endswith('_unfold') or args.system == 'aspmc_d4_fixed',
                         compiler='d4' if args.system == 'aspmc_d4_fixed' else 'sharpsat',
                         fixed_seed=seed if args.system == 'aspmc_d4_fixed' else None))
        preparation, preparation_cpu = time.perf_counter() - before, cpu_time() - cpu
        shared = LocalState.make([])
        print(json.dumps({'stage': 'compiled', 'seconds': preparation, 'nodes': len(backend.graph.gates)}), flush=True)
        original_graph = backend.graph
        original_roots = list(backend.roots) if hasattr(backend, 'roots') else [backend.root]
        suffixes = ['compiled_incremental', 'compiled_balanced', 'native'] if args.compiled_library else ['native', 'incremental', 'balanced']
        if args.compiled_library and args.diagnostic_updates:
            suffixes += ['incremental', 'balanced']
        for suffix in suffixes:
            extra = extra_cpu = 0
            backend.graph = original_graph
            if hasattr(backend, 'roots'):
                backend.roots = list(original_roots)
            else:
                backend.root = original_roots[0]
            if suffix.endswith('balanced'):
                start, start_cpu = time.perf_counter(), cpu_time()
                backend.rebalance()
                extra, extra_cpu = time.perf_counter() - start, cpu_time() - start_cpu
            if suffix.startswith('compiled_'):
                start, start_cpu = time.perf_counter(), cpu_time()
                backend.graph = CompiledArithmeticCircuit(backend.graph, getattr(backend, 'lanes', 1), args.compiled_library)
                extra += time.perf_counter() - start
                extra_cpu += cpu_time() - start_cpu
            mode = args.system + '_' + suffix
            selected_trace = (trace[:args.diagnostic_updates] if args.compiled_library and suffix in ['incremental', 'balanced'] else trace)
            result = incumbent_run(backend, initial, shared, selected_trace, seed, mode, output,
                                   preparation + extra, preparation_cpu + extra_cpu, args.mode_timeout)
            metadata['results'].append(result)
            metadata['status'] = mode + '_finished'
            save()
            print(json.dumps({'stage': mode, 'update_seconds': result['update_wall_s']}), flush=True)
    metadata['status'] = 'finished'
    save()
    print(json.dumps({'stage': 'finished', 'result': str(output / f'{args.system}-result.json')}), flush=True)


if __name__ == '__main__':
    main()
