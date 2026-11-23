"""Check normal import reachability and preserve the starting concurrent edits."""
import importlib.util
import difflib
import json
import subprocess
from pathlib import Path

art = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('qualify', art/'qualify.py')
qualify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(qualify)
root = qualify.ROOT
baseline = json.loads((art/'BASELINE.json').read_text())
insertions = {
    'Mettapedia.lean': [
        'import Mettapedia.ProbabilityTheory.MarkovChain\n',
        'import Mettapedia.Algorithms.Retrieval\n',
        'import Mettapedia.Logic.MarkovLogicLocalQueryApproximation\n',
        'import Mettapedia.PLN.Bridges.CognitiveArchitecture\n'],
    'Mettapedia/CognitiveArchitecture/Main.lean': [
        'import Mettapedia.CognitiveArchitecture.Attention\n',
        'import Mettapedia.CognitiveArchitecture.Memory\n'],
    'Mettapedia/PLN/Bridges.lean': [
        'import Mettapedia.PLN.Bridges.CognitiveArchitecture\n'],
}
overlaps = []
for path, added in insertions.items():
    current = (root/path).read_text()
    for line in added:
        assert current.count(line) == 1, (path, line)
        current = current.replace(line, '', 1)
    assert current == baseline[path]['text'], f'concurrent change needs review: {path}'
    overlaps.append({'path': path, 'disposition': 'additive import insertion; starting content preserved exactly',
                     'deferred': False})
for path in ['lake-manifest.json', 'lean-toolchain']:
    assert qualify.digest((root/path).read_bytes()) == baseline[path]['sha256'], path
old_lake = baseline['lakefile.lean']['text']
new_lake = (root/'lakefile.lean').read_text()
assert [l for l in old_lake.splitlines() if l.startswith('require ')] == [
    l for l in new_lake.splitlines() if l.startswith('require ')]
concurrent = []
if old_lake != new_lake:
    concurrent.append({'path': 'lakefile.lean', 'worker': 'main:14 Co VibeITP / native-kernel-restructure',
                       'worker_evidence': 'Read-only pane capture shows rho native checker and candidate/comparison extraction in progress.',
                       'disposition': 'Preserved untouched; executable target reorganization is independent of the imported library modules.',
                       'diff': ''.join(difflib.unified_diff(old_lake.splitlines(True), new_lake.splitlines(True)))})
owned = set(json.loads((art/'TARGETS.json').read_text()))
eligible = owned | {'Mettapedia', 'Mettapedia.CognitiveArchitecture.Main', 'Mettapedia.PLN.Bridges'}
pending = ['Mettapedia']
visited = set()
while pending:
    module = pending.pop()
    if module in visited or module not in eligible:
        continue
    visited.add(module)
    pending.extend(qualify.imports((root/(module.replace('.', '/')+'.lean')).read_text()))
assert owned <= visited, sorted(owned-visited)
for module in owned:
    assert not any(dep.endswith('.Audit') or dep.endswith('QueryAudit')
                   for dep in qualify.imports((root/(module.replace('.', '/')+'.lean')).read_text())), module
qualify.write('INTEGRATION.json', {'production_modules_reachable_from_default_root': sorted(owned),
                                 'audit_modules_excluded_from_production_imports': True,
                                 'preserved_overlaps': overlaps,
                                 'dependency_pins_unchanged': True,
                                 'concurrent_configuration_edits': concurrent})
diff_check = subprocess.run(['git', 'diff', '--check'], cwd=root, capture_output=True, text=True)
(art/'diff-check.log').write_text(diff_check.stdout+diff_check.stderr)
deferred = []
if diff_check.returncode:
    diagnostic = diff_check.stdout+diff_check.stderr
    expected = 'lean/mettapedia/Mettapedia/Languages/MeTTa/PrimeCandidates/DeclarationBased/FirstClassGSLT.lean:2039: new blank line at EOF.\n'
    assert diagnostic == expected, diagnostic
    deferred.append({
        'path': 'Mettapedia/Languages/MeTTa/PrimeCandidates/DeclarationBased/FirstClassGSLT.lean',
        'worker': 'main:15 CC FM',
        'worker_evidence': 'Read-only pane capture records an active +8/-348 update of FirstClassGSLT.lean.',
        'category': 'formatting follow-up outside the imported theory bundle',
        'diagnostic': diagnostic.strip(),
        'disposition': 'Left untouched for the active worker; remove the trailing blank line and rerun the owner scoped check.',
        'blocks_theory_import': False,
    })
qualify.write('CONFLICT_LEDGER.json', {
    'scope': 'Pinned attention, memory, retrieval, Markov, PLN bridges and DLR theory transfer',
    'deferred_files': deferred,
    'reason': 'No significant conflicts occurred. Existing concurrent edits were retained by additive integration.',
    'overlap_review': overlaps,
    'preserved_active_worker_edits': concurrent})
print('All', len(owned), 'production modules reachable; no theory conflicts;', len(deferred), 'active-worker formatting follow-ups')
