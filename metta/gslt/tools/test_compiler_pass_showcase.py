#!/usr/bin/env python3
"""Run Datalog demand slicing and CHR constant folding inside one MeTTa program.

The CHR matcher is prepared at build time. Runtime uses the compiled
Datalog provider and its Lean runtime libraries, with no Lean or SWI
subprocess. Souffle and SWI independently check the example.
This qualifies a prepared CHR instance, not a general CHR source compiler.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--cetta', type=Path, required=True)
    parser.add_argument('--souffle', type=Path, required=True)
    parser.add_argument('--swipl', type=Path, default=Path(shutil.which('swipl') or 'swipl'))
    parser.add_argument('--timeout', type=float, default=600)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / 'metta/gslt', repo / 'lean/mettapedia'
    source = gslt / 'examples/compiler_passes'
    engine = args.cetta.resolve(strict=True)
    souffle = args.souffle.resolve(strict=True)
    swipl = args.swipl.resolve(strict=True)
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=False)
    engine_root = next((p for p in [engine.parent, engine.parent.parent]
                        if (p / 'tools/library_spelling.py').is_file()), None)
    assert engine_root is not None, 'the CeTTa source tools must accompany this build'
    sys.path.insert(0, str(engine_root / 'tools'))
    from library_spelling import read_forms, Symbol

    timings = {}
    def run(label, command, cwd=work):
        started = time.monotonic()
        result = subprocess.run(list(map(str, command)), cwd=cwd, capture_output=True,
                                timeout=args.timeout)
        timings[label] = time.monotonic() - started
        (work / (label + '.out')).write_bytes(result.stdout)
        (work / (label + '.err')).write_bytes(result.stderr)
        assert result.returncode == 0, (label, result.returncode, result.stdout[-1200:], result.stderr[-1600:])
        return result

    generator = gslt / 'tools/generate_compiler_pass_showcase.lean'
    targets = re.findall(r'^import (Mettapedia\.[A-Za-z0-9_.]+)$', generator.read_text(), re.M)
    run('build', ['lake', '--wfail', 'build', *targets], lean)
    run('generate', ['lake', 'env', 'lean', '-DwarningAsError=true', '--run', generator,
                     source / 'program.metta', work], lean)
    fixture = json.loads((work / 'input.json').read_text())
    common = (gslt / 'tools/test_gslt_complete.sh').read_text()
    library_names = re.search(r'^libraries=\((.*?)^\)', common, re.M | re.S).group(1).split()
    libraries = [gslt / 'lib' / (name + '.metta') for name in library_names]
    libraries += [gslt / 'lib/gslt_integer.metta', gslt / 'lib/gslt_chr.metta']
    runtime = '\n'.join(p.read_text() for p in libraries)
    workload = work / 'run.metta'
    workload.write_text(runtime + '\n' + (work / 'prepared.metta').read_text() + '\n' +
                        (source / 'program.metta').read_text() + '\n' + (source / 'run.metta').read_text())
    shutil.copyfile(source / 'demand.dl', work / 'demand.dl')
    native = run('cetta', [engine, '--lang', 'petta', '--profile', 'extended', '--quiet',
                            '--run-contract', workload])
    diagnostics = re.sub(rb'run: status 0; queries [0-9]+; unsettled 0\n', b'', native.stderr)
    assert not diagnostics, diagnostics
    lines = native.stdout.decode().splitlines()
    def observation(head):
        rows = [line for line in lines if line.startswith('(' + head + ' ')]
        assert len(rows) == 1, (head, lines[-8:])
        return read_forms(rows[0])[0]
    demanded = [json.loads(value) for value in observation('DemandedNodes')[1]]
    expected_needed = {'out', 'future', 'copy', 'double', 'sum', 'a', 'b', 'bias', 'dynamic'}
    assert set(demanded) == expected_needed and len(demanded) == len(expected_needed), demanded
    assert str(observation('ExactResume')[1]).lower() == 'true'
    result = observation('SpecializedProgram')
    assert result[1] == Symbol('ChrComplete'), result[:2]
    def value(token):
        if isinstance(token, Symbol):
            assert re.fullmatch(r'-?[0-9]+', token), token
            return int(token)
        return json.loads(token)
    actual = Counter(tuple([str(row[0]), *map(value, row[1:])]) for row in result[2])
    assert result[3] == [Symbol('HistoryEntries'), Symbol('8')], result[3]

    facts = work / 'facts'; facts.mkdir()
    out = work / 'souffle'; out.mkdir()
    for relation in ['Add', 'Output']:
        rows = [row[1:] for row in fixture['source'] if row[0] == relation]
        (facts / (relation + '.facts')).write_text(''.join('\t'.join(row) + '\n' for row in rows))
    run('souffle', [souffle, '-j', '1', '-F', facts, '-D', out, work / 'demand.dl'])
    reference_needed = {row[0] for row in csv.reader((out / 'Need.csv').read_text().splitlines(), delimiter='\t')}
    assert reference_needed == set(demanded)
    def term(value):
        if isinstance(value, int):
            return str(value)
        if isinstance(value, list):
            return '[' + ','.join(term(v) for v in value) + ']'
        assert re.fullmatch(r'[a-z][a-z_]*', value), value
        return value
    reference = run('swi', [swipl, '-q', '-s', source / 'constant_fold.pl', '-g',
                           'compiler_pass_reference:run(' + term(sorted(demanded)) + ',' +
                           term(fixture['seeds']) + '),halt.'])
    expected = Counter(map(tuple, json.loads(reference.stdout)))
    assert actual == expected, (actual, expected)
    assert actual['constant', 'out', 15] == 1
    assert actual['constant', 'copy', 7] == 2 and actual['seen', 'copy'] == 2
    assert actual['add', 'future', 'dynamic', 'a'] == 1
    assert not any('dead_a' in row or 'dead_b' in row for row in actual)
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    pinned = [engine, souffle, swipl, generator, Path(__file__), *libraries,
              *source.glob('*'), workload, work / 'prepared.metta']
    record = {'passed': True, 'needed': sorted(demanded),
              'constant_result': 15, 'duplicate_results': 2, 'propagation_history_entries': 8,
              'unknown_operation_retained': True, 'dead_cycle_excluded': True,
              'exact_resume': True, 'souffle_agrees': True, 'swi_chr_bag_agrees': True,
              'runtime': 'both passes execute as one MeTTa program; no runtime Lean or SWI call',
              'scope': 'prepared ground CHR instance; general CHR source/controller correspondence remains open',
              'seconds': timings,
              'inputs': {str(p): digest(p) for p in pinned if p.is_file()}}
    (work / 'qualification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({key: record[key] for key in ['passed', 'needed', 'constant_result', 'duplicate_results', 'exact_resume']}))


if __name__ == '__main__':
    main()
