from pathlib import Path
import hashlib, json, re, sys
root = Path(__file__).resolve().parents[2]
art = Path(__file__).resolve().parent
roots = [
'Mettapedia.CategoryTheory.PartialSections',
'Mettapedia.Logic.Propositions.ComponentBases',
'Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalContent',
'Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalRealization',
'Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalScrutability',
'Mettapedia.CognitiveArchitecture.Consciousness',
'Mettapedia.CognitiveArchitecture.Main',
'Mettapedia.Logic.Propositions',
]
visited, stack = set(), list(roots)
while stack:
    module = stack.pop()
    if module in visited:
        continue
    visited.add(module)
    path = root / (module.replace('.', '/') + '.lean')
    if not path.is_file():
        raise SystemExit('missing local module: ' + module)
    source = re.sub(r'/\-[\s\S]*?\-/', '', path.read_text())
    for line in source.splitlines():
        match = re.match(r'\s*(?:public\s+)?import\s+(.*)', line.split('--')[0])
        if match:
            stack.extend(name for name in match.group(1).split() if name.startswith('Mettapedia.'))
paths = [name.replace('.', '/') + '.lean' for name in sorted(visited)]
paths += ['lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'lakefile.toml']
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
record = {path: digest(root / path) for path in paths if (root / path).is_file()}
label = sys.argv[1]
(art / ('SOURCES_' + label + '.json')).write_text(json.dumps(record, indent=2) + '\n')
print('frozen', len(visited), 'local source modules,', len(record), 'files')
if len(sys.argv) > 2:
    prior = json.loads((art / ('SOURCES_' + sys.argv[2] + '.json')).read_text())
    changed = [path for path in sorted(set(prior) | set(record)) if prior.get(path) != record.get(path)]
    (art / ('SOURCE_CHANGES_' + sys.argv[2] + '_to_' + label + '.json')).write_text(json.dumps(changed, indent=2) + '\n')
    print('changed', len(changed))
    for path in changed:
        print(path)
    raise SystemExit(bool(changed))
