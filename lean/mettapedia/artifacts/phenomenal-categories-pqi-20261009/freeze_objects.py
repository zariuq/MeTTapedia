from pathlib import Path
import hashlib, json, sys
root = Path(__file__).resolve().parents[2]
art = Path(__file__).resolve().parent
sources = json.loads((art / 'SOURCES_after-refined-build.json').read_text())
record = {}
missing = []
for path in sources:
    if not path.startswith('Mettapedia/') or not path.endswith('.lean'):
        continue
    base = root / '.lake/build/lib/lean' / path.removesuffix('.lean')
    objects = sorted(base.parent.glob(base.name + '.olean*'))
    if not objects:
        missing.append(path)
    for obj in objects:
        record[str(obj.relative_to(root))] = hashlib.sha256(obj.read_bytes()).hexdigest()
label = sys.argv[1]
(art / ('OBJECTS_' + label + '.json')).write_text(json.dumps(record, indent=2) + '\n')
print('frozen', len(record), 'compiled object files; missing modules', len(missing))
if missing:
    print(missing)
    raise SystemExit(1)
if len(sys.argv) > 2:
    prior = json.loads((art / ('OBJECTS_' + sys.argv[2] + '.json')).read_text())
    changed = [path for path in sorted(set(prior) | set(record)) if prior.get(path) != record.get(path)]
    (art / ('OBJECT_CHANGES_' + sys.argv[2] + '_to_' + label + '.json')).write_text(json.dumps(changed, indent=2) + '\n')
    print('changed', len(changed))
    for path in changed:print(path)
    raise SystemExit(bool(changed))
