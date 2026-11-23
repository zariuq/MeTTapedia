from pathlib import Path
import hashlib, json, re, subprocess
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
modules=json.loads((OUT/'modules.json').read_text())
def uncomment(text):
    output=[]; pos=0; depth=0; string=False
    while pos < len(text):
        if depth:
            if text.startswith('/-',pos): depth+=1; output.extend('  '); pos+=2
            elif text.startswith('-/',pos): depth-=1; output.extend('  '); pos+=2
            else: output.append('\n' if text[pos]=='\n' else ' '); pos+=1
        elif string:
            if text[pos]=='\\': output.extend('  '); pos+=2
            elif text[pos]=='"': string=False; output.append(' '); pos+=1
            else: output.append('\n' if text[pos]=='\n' else ' '); pos+=1
        elif text.startswith('/-',pos): depth=1; output.extend('  '); pos+=2
        elif text.startswith('--',pos):
            end=text.find('\n',pos)
            if end<0: output.extend(' '*(len(text)-pos)); break
            output.extend(' '*(end-pos)); pos=end
        elif text[pos]=='"': string=True; output.append(' '); pos+=1
        else: output.append(text[pos]); pos+=1
    return ''.join(output)
rows=[]; added=0; total=0
for module in modules:
    path=ROOT/(module.replace('.', '/')+'.lean')
    raw=path.read_text(); code=uncomment(raw)
    bad=[{'token':m[0], 'line':code[:m.start()].count('\n')+1} for m in re.finditer(r"\b(?:sorry|axiom|native_decide|theorem_wanted)\b|\badmit(?![\w?!'])",code)]
    names=set(re.findall(r'\b(?:theorem|lemma)\s+([^\s(:{]+)',code))
    rel=path.relative_to(ROOT)
    old=subprocess.run(['git','show','HEAD:lean/mettapedia/'+str(rel)],cwd=ROOT,text=True,capture_output=True)
    baseline=set(re.findall(r'\b(?:theorem|lemma)\s+([^\s(:{]+)',uncomment(old.stdout))) if old.returncode==0 else set()
    new=sorted(names-baseline); added+=len(new); total+=len(names)
    trailing=[i for i,line in enumerate(raw.splitlines(),1) if line.rstrip()!=line]
    row={'module':module,'path':str(rel),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'lines':len(raw.splitlines()),'named_theorems':len(names),'added_named_theorems':new,'forbidden_code_tokens':bad,'trailing_whitespace':trailing}
    rows.append(row)
    if bad or trailing: raise RuntimeError(f'Source hygiene failure: {module}: {bad}, trailing {trailing}')
result={'modules':rows,'module_count':len(rows),'distinct_bare_theorem_names_total':total,'new_distinct_bare_theorem_names':added,'count_method':'Lower bound: theorem and lemma bare spellings per file; equal names in different namespaces count once; excludes generated kernel theorem names','baseline':'Git HEAD; selected existing source files were clean at intake'}
(OUT/'SOURCE_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print('SOURCE SUMMARY',len(rows),'modules;',added,'new distinct theorem spellings (lower bound);',total,'total distinct theorem spellings; no forbidden proof tokens or trailing whitespace')
