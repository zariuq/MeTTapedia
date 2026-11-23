"""Check every transferred Lean file and the two integration umbrellas strictly."""
from pathlib import Path
import json
import subprocess
import time

art = Path(__file__).resolve().parent
root = art.parents[1]
files = [r['target_path'] for r in json.loads((art/'PROVENANCE.json').read_text())['files']
         if r['target_path'].endswith('.lean')]
files += ['Mettapedia/CognitiveArchitecture/Main.lean', 'Mettapedia/PLN/Bridges.lean']
records = []
for file in files:
    started = time.monotonic()
    log = art / ('strict-' + file.replace('/', '_') + '.log')
    with log.open('w') as output:
        proc = subprocess.run(['nice', '-n', '19', 'lake', 'env', 'lean', '-M', '24576',
                               '-DwarningAsError=true', file], cwd=root,
                              stdout=output, stderr=subprocess.STDOUT)
    record = {'path': file, 'exit_code': proc.returncode,
              'seconds': round(time.monotonic() - started, 3), 'log': log.name}
    records.append(record)
    (art/'STRICT_RESULTS.json').write_text(json.dumps(records, indent=2) + '\n')
    print('PASS' if proc.returncode == 0 else 'FAIL', file, flush=True)
    if proc.returncode:
        print(log.read_text(), flush=True)
        raise SystemExit(proc.returncode)
print('Strict checks passed:', len(records), flush=True)
