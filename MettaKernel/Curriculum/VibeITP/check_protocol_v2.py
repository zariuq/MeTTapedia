#!/usr/bin/env python3
"""Compare Lean-exported protocol fixtures with the selected external C checker.

This is an oracle driver, not a native-implementation refinement proof. A
nonzero exit alone never establishes the expected refusal: its diagnostic must
also match. Zero exit with an unsatisfied challenge is not full acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def matches_result(entry, returncode, output):
    if any(marker in output for marker in (
            'ERROR: AddressSanitizer', 'LeakSanitizer:', 'runtime error:')):
        return False
    expected = entry['expected']
    if expected == 'refused':
        return returncode > 0 and entry['diagnostic'] is not None and entry['diagnostic'] in output
    if expected not in ('success', 'incomplete'):
        raise ValueError(f"unsupported oracle outcome: {expected}")
    counts = entry['challenges']
    if any(type(counts[key]) is not int or counts[key] < 0 for key in ('setup', 'proof', 'remaining')):
        raise ValueError('challenge counts must be nonnegative integers')
    total = counts['setup'] + counts['proof']
    remaining = counts['remaining']
    if remaining > total:
        raise ValueError('remaining challenges exceed registrations')
    successes = re.findall(r'^Success! All (\d+) challenges proved!', output, re.MULTILINE)
    partial = re.findall(r'^Remaining unproven challenges\. Proved (\d+) / (\d+) challenges\.',
                         output, re.MULTILINE)
    if expected == 'success':
        return (returncode == 0 and total > 0 and remaining == 0 and
                successes == [str(total)] and not partial)
    if total == 0:
        return (returncode == 0 and not successes and not partial and
                'Successfully processed axioms, definitions & proofs.' in output)
    return (returncode == 0 and remaining > 0 and not successes and
            partial == [(str(total - remaining), str(total))])


def qualify(checker, directory, results_directory, timeout=None):
    checker = checker.resolve()
    directory = directory.resolve()
    results_directory = results_directory.resolve()
    results_directory.mkdir(parents=True, exist_ok=True)
    manifest = directory / 'manifest.json'
    entries = json.loads(manifest.read_text())
    results = []
    for entry in entries:
        setup = [directory / name for name in entry['setup']]
        proofs = [directory / name for name in entry['proofs']]
        command = [str(checker), *map(str, setup)]
        if proofs:
            command += ['--proofs', *map(str, proofs)]
        started = time.monotonic()
        run = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
        seconds = time.monotonic() - started
        output = run.stdout + run.stderr
        (results_directory / (entry['name'] + '.log')).write_text(output)
        expected = entry['expected']
        passed = matches_result(entry, run.returncode, output)
        result = {'name': entry['name'], 'expected': expected, 'exit': run.returncode,
                  'passed': passed, 'seconds': seconds,
                  'inputs': {path.name: sha(path) for path in setup + proofs}}
        results.append(result)
        print(entry['name'], 'passed' if passed else 'FAILED', flush=True)
    receipt = {'checker_sha256': sha(checker), 'manifest_sha256': sha(manifest),
               'cases': results, 'passed': all(row['passed'] for row in results),
               'native_refinement_proved': False}
    (results_directory / 'native-results.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return receipt['passed']


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checker', type=Path)
    parser.add_argument('fixtures', type=Path)
    parser.add_argument('results', type=Path)
    parser.add_argument('--timeout', type=float)
    args = parser.parse_args()
    raise SystemExit(0 if qualify(args.checker, args.fixtures, args.results, args.timeout) else 1)
