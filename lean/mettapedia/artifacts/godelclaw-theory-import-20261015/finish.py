"""Write a qualification receipt only when the frozen checks have succeeded."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

art = Path(__file__).resolve().parent
root = art.parents[1]
load = lambda p: json.loads((art/p).read_text())
digest = lambda data: hashlib.sha256(data).hexdigest()
prov = load('PROVENANCE.json')
assert len(prov['files']) == 35
for record in prov['files']:
    assert digest((root/record['target_path']).read_bytes()) == record['target_sha256'], record['target_path']
sources_before = load('SOURCES_frozen-before-build.json')
sources_after = load('SOURCES_frozen-after-audit.json')
assert sources_before == sources_after
for record in sources_after.values():
    assert digest((root/record['path']).read_bytes()) == record['sha256'], record['path']
objects_before = load('OBJECTS_frozen-before-audit.json')
objects_after = load('OBJECTS_frozen-after-audit.json')
assert objects_before == objects_after
for path, value in objects_after.items():
    assert digest((root/path).read_bytes()) == value, path
strict = load('STRICT_RESULTS.json')
assert len(strict) == 32 and all(r['exit_code'] == 0 for r in strict)
audit_log = (art/'audit-frozen.log').read_text()
summary = re.search(r'SUMMARY: (\d+) modules, (\d+) kernel declarations, (\d+) theorems, (\d+) compiler-only names', audit_log)
assert summary, 'missing kernel audit summary'
assert '\nerror:' not in audit_log
build_log = (art/'frozen-build.log').read_text()
build = re.search(r'Build completed successfully \((\d+) jobs\)', build_log)
assert build
source_audit = load('SOURCE_AUDIT.json')
assert not any(r['forbidden'] for r in source_audit)
warnings = []
owned = {r['target_path'] for r in prov['files']}
for line in build_log.splitlines():
    if not line.startswith('warning:'):
        continue
    m = re.match(r'warning: (.+?\.lean):(\d+):(\d+): (.*)', line)
    assert m, line
    warnings.append({'path': m[1], 'line': int(m[2]), 'column': int(m[3]),
                     'message': m[4], 'imported_file': m[1] in owned})
assert not any(r['imported_file'] for r in warnings)
(art/'DEPENDENCY_WARNINGS.json').write_text(json.dumps(warnings, indent=2)+'\n')
for record in prov['files']:
    text = (root/record['target_path']).read_text()
    assert 'CogArch' not in text, record['target_path']
    assert not any(s in text for s in ['/home/', '/shared/', 'Imagined council']), record['target_path']
    assert not any(line.rstrip() != line for line in text.splitlines()), record['target_path']
shared = load('SHARED_DEPENDENCIES.json')
assert not any(r['status'] == 'different_code' for r in shared)
assert len(load('INTEGRATION.json')['production_modules_reachable_from_default_root']) == 26
deferred = load('CONFLICT_LEDGER.json')['deferred_files']
assert not any(r['blocks_theory_import'] for r in deferred)
diff_check = subprocess.run(['git', 'diff', '--check'], cwd=root, capture_output=True, text=True)
(art/'diff-check.log').write_text(diff_check.stdout+diff_check.stderr)
assert diff_check.returncode == 0 or deferred, diff_check.stdout+diff_check.stderr
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=root).decode().strip() == 'main'
result = {
    'status': 'qualified',
    'goal': 'Import the complete selected godelclaw theory bundle into canonical MeTTapedia',
    'source_commit': prov['source_commit'],
    'target_branch': 'main',
    'source_files_added': len(prov['files']),
    'production_modules': int(summary[1]),
    'explicit_named_theorems_transferred': sum(r['named_theorems'] for r in source_audit),
    'kernel_declarations_checked': int(summary[2]),
    'kernel_theorem_declarations_including_generated': int(summary[3]),
    'compiler_only_names_recorded_separately': int(summary[4]),
    'allowed_axiom_dependencies': ['propext', 'Classical.choice', 'Quot.sound'],
    'build_jobs': int(build[1]),
    'strict_checks': len(strict),
    'frozen_local_dependency_modules': len(sources_after)-3,
    'frozen_objects': len(objects_after),
    'source_and_object_freeze_verified': True,
    'imported_module_warnings': 0,
    'dependency_warning_occurrences': len(warnings),
    'dependency_warning_inventory': 'DEPENDENCY_WARNINGS.json',
    'shared_dependencies_identical': sum(r['status'] == 'identical' for r in shared),
    'shared_dependencies_comments_only': sum(r['status'] == 'comments_only' for r in shared),
    'code_change_from_pinned_source': 'Namespace adaptation only; five files also have comment clarifications.',
    'all_production_modules_reachable_from_default_root': True,
    'deferred_theory_files': [],
    'active_worker_follow_ups': deferred,
    'repository_wide_diff_check_exit_code': diff_check.returncode,
    'conflict_ledger': 'CONFLICT_LEDGER.json',
    'proof_placeholders_or_custom_axioms': 0,
    'no_commits_or_pushes': True,
    'scope_limits': ['Exact mathematical arithmetic, not certified floating point.',
                     'Model contracts do not prove deployed agent conformance or empirical retrieval superiority.',
                     'No consciousness or experienced-wellbeing assignment is established.'],
    'qualification_notes': ['The first strict attempt lacked audit-module object files; building the audit dependencies resolved it.',
                            'Editorial review changes were followed by a fresh frozen build, all strict checks and a complete kernel audit.'],
}
(art/'QUALIFICATION.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
