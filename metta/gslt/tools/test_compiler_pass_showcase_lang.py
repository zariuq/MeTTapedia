#!/usr/bin/env python3
"""Run Datalog demand slicing and CHR constant folding through the public lang library.

The workload imports only lang: both passes are ordinary source programs
loaded with (lang:load Datalog) and (lang:load CHR). Runtime launches no
Lean, Souffle or SWI process; this test runs both references afterwards.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
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
    parser.add_argument('--timeout', type=float, default=900)
    args = parser.parse_args()
    gslt = Path(__file__).resolve().parents[1]
    source = gslt / 'examples/compiler_passes'
    engine = args.cetta.resolve(strict=True)
    souffle = args.souffle.resolve(strict=True)
    swipl = args.swipl.resolve(strict=True)
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=False)
    engine_root = next(p for p in [engine.parent, engine.parent.parent] if (p / 'tools/library_spelling.py').is_file())
    sys.path.insert(0, str(engine_root / 'tools'))
    from library_spelling import read_forms

    timings = {}

    def run(label, command, cwd=work):
        started = time.monotonic()
        result = subprocess.run(list(map(str, command)), cwd=cwd, capture_output=True, timeout=args.timeout)
        timings[label] = time.monotonic() - started
        (work / (label + '.out')).write_bytes(result.stdout)
        (work / (label + '.err')).write_bytes(result.stderr)
        assert result.returncode == 0, (label, result.returncode, result.stdout[-1500:], result.stderr[-1500:])
        return result

    for name in ['demand.dl', 'constant_fold.chr']:
        shutil.copyfile(source / name, work / name)
    workload = work / 'run.metta'
    workload.write_text((source / 'program.metta').read_text() + '\n' + (source / 'run_lang.metta').read_text())
    native = run('cetta', [engine, '--lang', 'petta', '--profile', 'extended', workload])
    lines = native.stdout.decode().splitlines()

    def observation(head):
        rows = [line for line in lines if line.startswith('(' + head + ' ')]
        assert len(rows) == 1, (head, lines[-8:])
        return read_forms(rows[0])[0]

    demanded = [json.loads(value) for value in observation('DemandedNodes')[1]]
    expected_needed = {'out', 'future', 'copy', 'double', 'sum', 'a', 'b', 'bias', 'dynamic'}
    assert set(demanded) == expected_needed and len(demanded) == len(expected_needed), demanded
    assert str(observation('PrivateAgrees')[1]).lower() == 'true'
    assert str(observation('ResumedAgrees')[1]).lower() == 'true'

    def value(token):
        # C0 accepts both host string and symbol spellings of guest atoms.
        # Surviving host occurrences keep their original string form.
        if str(token).startswith('"'):
            return json.loads(str(token))
        return int(token) if str(token).lstrip('-').isdigit() else str(token)
    heads = {'constant', 'add', 'input', 'seen'}
    rows = [row for row in observation('SpecializedProgram')[1] if isinstance(row, list) and str(row[0]) in heads]
    actual = Counter(tuple([str(row[0]), *map(value, row[1:])]) for row in rows)
    assert any(str(row[0]) == 'input' and str(row[1]) == '"dynamic"' for row in rows), rows
    resumed_rows = [row for row in observation('ResumedSpace')[1] if isinstance(row, list) and str(row[0]) in heads]
    assert Counter(tuple([str(row[0]), *map(value, row[1:])]) for row in resumed_rows) == actual

    program_rows = [form for form in read_forms((source / 'program.metta').read_text()) if isinstance(form, list)]
    facts = work / 'facts'; facts.mkdir()
    out = work / 'souffle'; out.mkdir()
    for relation in ['Add', 'Output']:
        relation_rows = [[json.loads(field) for field in row[1:]] for row in program_rows if str(row[0]) == relation]
        (facts / (relation + '.facts')).write_text(''.join('\t'.join(r) + '\n' for r in relation_rows))
    run('souffle', [souffle, '-j', '1', '-F', facts, '-D', out, work / 'demand.dl'])
    reference_needed = {row[0] for row in csv.reader((out / 'Need.csv').read_text().splitlines(), delimiter='\t')}
    assert reference_needed == set(demanded)

    seeds = []
    for row in program_rows:
        head = str(row[0])
        fields = [json.loads(field) if str(field).startswith('"') else int(str(field)) for field in row[1:]]
        if head == 'Add':
            seeds.append([fields[0], 'add', *fields])
        elif head == 'Constant':
            seeds.append([fields[0], 'constant', *fields])
        elif head == 'Input':
            seeds.append([fields[0], 'input', *fields])

    def term(item):
        if isinstance(item, int):
            return str(item)
        if isinstance(item, list):
            return '[' + ','.join(term(v) for v in item) + ']'
        assert item.replace('_', '').isalnum() and item[0].islower(), item
        return item
    reference = run('swi', [swipl, '-q', '-s', source / 'constant_fold.pl', '-g',
                           'compiler_pass_reference:run(' + term(sorted(demanded)) + ',' + term(seeds) + '),halt.'])
    expected = Counter(map(tuple, json.loads(reference.stdout)))
    assert actual == expected, (actual, expected)
    assert actual['constant', 'out', 15] == 1
    assert actual['constant', 'copy', 7] == 2 and actual['seen', 'copy'] == 2
    assert actual['add', 'future', 'dynamic', 'a'] == 1
    assert not any('dead_a' in row or 'dead_b' in row for row in actual)
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    record = {'passed': True, 'needed': sorted(demanded), 'final_multiset': sorted(map(list, actual.elements())),
              'private_eval_agrees': True, 'resumed_run_agrees': True, 'souffle_agrees': True, 'swi_chr_bag_agrees': True,
              'public_path': 'workload imports lang only; ordinary Datalog and CHR sources',
              'seconds': timings,
              'inputs': {str(p): digest(p) for p in [engine, souffle, swipl, Path(__file__), *source.glob('*')] if p.is_file()}}
    (work / 'qualification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({key: record[key] for key in ['passed', 'needed', 'private_eval_agrees', 'resumed_run_agrees']}))


if __name__ == '__main__':
    main()
