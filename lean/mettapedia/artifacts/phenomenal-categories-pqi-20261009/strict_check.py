from pathlib import Path
import json, subprocess, time
root = Path(__file__).resolve().parents[2]
art = Path(__file__).resolve().parent
modules = ['Mettapedia.CategoryTheory.PartialSections', 'Mettapedia.Logic.Propositions.ComponentBases', 'Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalContent', 'Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalRealization', 'Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalScrutability', 'Mettapedia.CognitiveArchitecture.Consciousness', 'Mettapedia.CognitiveArchitecture.Main', 'Mettapedia.Logic.Propositions']
results = []
for module in modules:
    path = module.replace('.', '/') + '.lean'
    started = time.monotonic()
    with (art / (module.split('.')[-1] + '-strict.log')).open('w') as log:
        result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', path], cwd=root, stdout=log, stderr=subprocess.STDOUT)
    results.append({'module': module, 'exit_code': result.returncode, 'seconds': round(time.monotonic() - started, 2)})
    print(module, 'exit', result.returncode, flush=True)
(art / 'STRICT_RESULTS.json').write_text(json.dumps(results, indent=2) + '\n')
raise SystemExit(0 if all(result['exit_code'] == 0 for result in results) else 1)
