#!/usr/bin/env python3
"""Check that every headline theorem in `scripts/headline_witnesses.toml` is witnessed.

A theorem whose hypotheses can never hold together is true and useless. The manifest
lists headline theorems with a *witness*: a declaration that applies the theorem with
every hypothesis argument closed, directly or through the proof of a theorem it applies
(see `scripts/headline_witness_scan.lean` for the exact criterion). It also lists
*refutations*: negative controls whose conclusion is that a hypothesis combination never
holds. It also acknowledges theorems that are *vacuous* on purpose (a control showing that a
test passes vacuously, a fixture with an impossible premise), each with its reason.

Checks:

* static (always): every entry has its fields; the named modules exist; the theorem and
  the witness are declared there; the witness module imports the theorem module,
  directly or transitively. An entry without a witness fails.
* `--lean`: additionally builds the witness modules (`lake build`) and runs the Lean scan
  in `verify` mode, which confirms from the compiled declarations that each witness applies
  its theorem with closed hypothesis arguments.
* `--papers DIR`: additionally lists the theorems cited in `DIR/*.tex` (`\\leanname`,
  `\\nolinkurl`, `\\code`, `\\texttt`) that the manifest does not list. This is a report,
  not a failure.
* `--audit PREFIX --out FILE`: runs the Lean scan in `audit` mode over every module under
  `PREFIX` whose olean, and the oleans of its import closure, are current; writes one row per
  theorem to `FILE` and prints the counts. It fails when a theorem is flagged `ex-falso`
  (its proof derives `False` from its own hypotheses, so it is vacuous) and the manifest does
  not acknowledge it under `[[vacuous]]`. The other flags are for review.

Usage, from the Lean package root:

    python3 scripts/check_headline_witnesses.py
    python3 scripts/check_headline_witnesses.py --lean
    python3 scripts/check_headline_witnesses.py --papers ../../papers
    python3 scripts/check_headline_witnesses.py --audit Mettapedia.Logic.HOL --out hol.tsv
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / 'scripts' / 'headline_witnesses.toml'
SCAN = ROOT / 'scripts' / 'headline_witness_scan.lean'
WORK = ROOT / '.lake' / 'headline-witnesses'

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|example)\s+([^\s:({\[]+)')
NAMESPACE = re.compile(r'^\s*namespace\s+(\S+)')
SECTION = re.compile(r'^\s*(?:(?:noncomputable|public)\s+)*section(?:\s+(\S+))?\s*$|^\s*mutual\s*$')
END = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+([\w.]+)', re.M)


def module_path(module: str) -> Path:
    return ROOT / (module.replace('.', '/') + '.lean')


def declared_names(path: Path) -> set[str]:
    """Full names of the declarations of a file, tracking `namespace`, `section`, `mutual`
    and the `end` that closes each."""
    names: set[str] = set()
    stack: list[list[str]] = []
    depth = 0
    for line in path.read_text(encoding='utf-8').splitlines():
        if depth:
            depth = max(0, depth + line.count('/-') - line.count('-/'))
            continue
        if line.lstrip().startswith('/-'):
            depth = max(0, line.count('/-') - line.count('-/'))
            continue
        if m := NAMESPACE.match(line):
            stack.append(m.group(1).split('.'))
        elif SECTION.match(line):
            stack.append([])
        elif END.match(line):
            if stack:
                stack.pop()
        elif m := DECL.match(line):
            name = m.group(1).rstrip('.')  # `name.{u}` declares universe parameters
            if name.startswith('_root_.'):
                names.add(name[len('_root_.'):])
            else:
                names.add('.'.join([part for parts in stack for part in parts] + [name]))
    return names


def imports_transitively(start: str, goal: str) -> bool:
    seen, todo = set(), [start]
    while todo:
        module = todo.pop()
        if module == goal:
            return True
        if module in seen:
            continue
        seen.add(module)
        path = module_path(module)
        if path.exists():
            head = path.read_text(encoding='utf-8').split('\n/-', 1)[0]
            todo.extend(IMPORT.findall(head))
    return False


def static_check(manifest: dict) -> list[str]:
    errors: list[str] = []
    cache: dict[str, set[str]] = {}

    def has(module: str, name: str) -> bool:
        if module not in cache:
            cache[module] = declared_names(module_path(module))
        return name in cache[module]

    for kind in ('witness', 'refutation', 'vacuous'):
        for entry in manifest.get(kind, []):
            label = entry.get('theorem', '<missing theorem>')
            fields = {'witness': ('theorem', 'theorem_module', 'witness', 'witness_module'),
                      'refutation': ('theorem', 'theorem_module'),
                      'vacuous': ('theorem', 'theorem_module', 'reason')}[kind]
            missing = [f for f in fields if not entry.get(f)]
            if missing:
                errors.append(f'{label}: missing {", ".join(missing)}')
                continue
            modules = [entry['theorem_module']] + \
                ([entry['witness_module']] if kind == 'witness' else [])
            absent = [m for m in modules if not module_path(m).exists()]
            if absent:
                errors.append(f'{label}: no module {", ".join(absent)}')
                continue
            if not has(entry['theorem_module'], entry['theorem']):
                errors.append(f'{label}: not declared in {entry["theorem_module"]}')
            if kind == 'witness':
                if not has(entry['witness_module'], entry['witness']):
                    errors.append(f'{label}: witness {entry["witness"]} not declared in '
                                  f'{entry["witness_module"]}')
                if not imports_transitively(entry['witness_module'], entry['theorem_module']):
                    errors.append(f'{label}: {entry["witness_module"]} does not import '
                                  f'{entry["theorem_module"]}')
    return errors


def lean_check(manifest: dict) -> list[str]:
    entries = manifest.get('witness', []) + manifest.get('refutation', [])
    WORK.mkdir(parents=True, exist_ok=True)
    modules = sorted({e.get('witness_module') or e['theorem_module'] for e in entries})
    (WORK / 'imports.txt').write_text('\n'.join(modules) + '\n', encoding='utf-8')
    pairs = [f"{e['theorem']}\t{e.get('witness', e['theorem'])}" for e in entries]
    (WORK / 'pairs.tsv').write_text('\n'.join(pairs) + '\n', encoding='utf-8')
    out = WORK / 'verify.tsv'
    out.unlink(missing_ok=True)
    build = subprocess.run(['lake', 'build', *modules], cwd=ROOT, capture_output=True, text=True)
    if build.returncode != 0:
        return [f'building the witness modules failed:\n{build.stdout[-4000:]}\n{build.stderr[-4000:]}']
    run = subprocess.run(
        ['lake', 'env', 'lean', '--run', str(SCAN), 'verify',
         '--imports-file', str(WORK / 'imports.txt'),
         '--pairs-file', str(WORK / 'pairs.tsv'), '--out', str(out)],
        cwd=ROOT, capture_output=True, text=True)
    if not out.exists():
        return [f'Lean scan failed:\n{run.stdout}\n{run.stderr}']
    errors = []
    refutations = {e['theorem'] for e in manifest.get('refutation', [])}
    for line in out.read_text(encoding='utf-8').splitlines()[1:]:
        result, theorem, witness = line.split('\t')
        accepted = {'refutation', 'no-hypotheses'} if theorem in refutations \
            else {'ok', 'no-hypotheses'}
        if result not in accepted:
            errors.append(f'{theorem}: {result} (witness {witness})')
    return errors


def importable_modules(prefix: str) -> list[str]:
    """Modules under `prefix` whose oleans, and those of their import closure, are current."""
    olean_root = ROOT / '.lake' / 'build' / 'lib' / 'lean'
    known: dict[str, bool] = {}

    def fresh(module: str) -> bool:
        source = module_path(module)
        olean = olean_root / (module.replace('.', '/') + '.olean')
        return source.exists() and olean.exists() and \
            olean.stat().st_mtime >= source.stat().st_mtime

    imports_cache: dict[str, list[str]] = {}

    def deps(m: str) -> list[str]:
        if m not in imports_cache:
            path = module_path(m)
            head = path.read_text(encoding='utf-8').split('\n/-', 1)[0] if path.exists() else ''
            imports_cache[m] = [i for i in IMPORT.findall(head) if i.startswith('Mettapedia')]
        return imports_cache[m]

    def ok(module: str) -> bool:
        stack, order, seen = [module], [], set()
        while stack:
            m = stack.pop()
            if m in known or m in seen:
                continue
            seen.add(m)
            order.append(m)
            stack.extend(deps(m))
        for m in reversed(order):
            if m not in known:
                known[m] = fresh(m) and all(known.get(d, fresh(d)) for d in deps(m))
        return known[module]

    base = ROOT / prefix.replace('.', '/')
    files = sorted(set(base.rglob('*.lean')) | ({base.with_suffix('.lean')}
                                                 if base.with_suffix('.lean').exists() else set()))
    modules = ['.'.join(f.relative_to(ROOT).with_suffix('').parts) for f in files]
    return [m for m in modules if ok(m)]


def audit(prefix: str, out: Path, acknowledged: set[str]) -> int:
    WORK.mkdir(parents=True, exist_ok=True)
    modules = importable_modules(prefix)
    imports = WORK / 'audit-imports.txt'
    imports.write_text('\n'.join(modules) + '\n', encoding='utf-8')
    run = subprocess.run(
        ['lake', 'env', 'lean', '--run', str(SCAN), 'audit', '--imports-file', str(imports),
         '--module-prefix', prefix, '--out', str(out)],
        cwd=ROOT, capture_output=True, text=True)
    print(run.stdout.strip())
    if run.returncode != 0 or not out.exists():
        print(run.stderr.strip()[-4000:])
        return 1
    vacuous = [line.split('\t')[1] for line in out.read_text(encoding='utf-8').splitlines()[1:]
               if 'ex-falso' in line.split('\t')[-1]]
    unacknowledged = [name for name in vacuous if name not in acknowledged]
    print(f'{len(modules)} modules; {len(vacuous)} theorems derive False from their hypotheses, '
          f'{len(unacknowledged)} of them not acknowledged under [[vacuous]]')
    for name in vacuous:
        print(f"  {'VACUOUS' if name in unacknowledged else 'acknowledged'} {name}")
    return 1 if unacknowledged else 0


PAPER_MACRO = re.compile(r'\\(?:leanname|nolinkurl|code|texttt)\{((?:[^{}]|\{[^{}]*\})*)\}')


def paper_report(manifest: dict, papers: Path) -> None:
    listed = {e['theorem'].split('.')[-1] for kind in ('witness', 'refutation')
              for e in manifest.get(kind, [])}
    cited: dict[str, set[str]] = {}
    for tex in sorted(papers.glob('*.tex')):
        for arg in PAPER_MACRO.findall(tex.read_text(encoding='utf-8', errors='replace')):
            arg = arg.replace('\\_', '_')
            for token in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", arg):
                token = token.strip('.')
                if '_' in token and '/' not in token and not token.endswith('.lean'):
                    cited.setdefault(token.split('.')[-1], set()).add(tex.name)
    unlisted = sorted(set(cited) - listed)
    print(f'{len(cited)} names cited in papers; {len(unlisted)} not in the manifest')
    for name in unlisted:
        print(f'  {name}\t{", ".join(sorted(cited[name]))}')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--lean', action='store_true', help='verify witnesses with Lean')
    parser.add_argument('--papers', type=Path, help='report paper citations not listed')
    parser.add_argument('--manifest', type=Path, default=MANIFEST)
    parser.add_argument('--audit', metavar='PREFIX', help='audit the theorems under PREFIX')
    parser.add_argument('--out', type=Path, help='output of --audit')
    args = parser.parse_args()
    if args.audit:
        if not args.out:
            parser.error('--audit needs --out')
        manifest = tomllib.loads(args.manifest.read_text(encoding='utf-8'))
        return audit(args.audit, args.out.resolve(),
                     {e['theorem'] for e in manifest.get('vacuous', [])})
    manifest = tomllib.loads(args.manifest.read_text(encoding='utf-8'))
    errors = static_check(manifest)
    if args.lean and not errors:
        errors += lean_check(manifest)
    n = sum(len(manifest.get(k, [])) for k in ('witness', 'refutation', 'vacuous'))
    for error in errors:
        print(f'FAIL {error}')
    print(f'{n} entries; {len(errors)} failures')
    if args.papers:
        paper_report(manifest, args.papers)
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
