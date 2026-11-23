from pathlib import Path
import re, json
root=Path(__file__).resolve().parents[2]
art=Path(__file__).resolve().parent
modules=['Mettapedia.CategoryTheory.PartialSections','Mettapedia.Logic.Propositions.ComponentBases','Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalContent','Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalRealization','Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalScrutability']
records=[]
for module in modules:
    path=root/(module.replace('.','/')+'.lean')
    source=path.read_text()
    depth=0
    stripped=[]
    index=0
    while index<len(source):
        if source[index:index+2]=='/-':
            depth+=1;index+=2;continue
        if depth and source[index:index+2]=='-/':
            depth-=1;index+=2;continue
        if depth:
            if source[index]=='\n':stripped.append('\n')
            index+=1;continue
        if source[index:index+2]=='--':
            end=source.find('\n',index)
            if end<0:break
            index=end;continue
        stripped.append(source[index]);index+=1
    code=''.join(stripped)
    forbidden=[]
    for line_no,line in enumerate(code.splitlines(),1):
        if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|partial)\b|_wanted',line):
            forbidden.append({'line':line_no,'code':line.strip()})
    records.append({'module':module,'lines':len(source.splitlines()),'named_theorems':len(re.findall(r'^theorem\s+\S+',code,re.M)),'source_declarations':len(re.findall(r'^(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|theorem|instance)\b',code,re.M)),'forbidden':forbidden})
(art/'SOURCE_AUDIT.json').write_text(json.dumps(records,indent=2)+'\n')
print('implementation modules',len(records),'named theorems',sum(item['named_theorems']for item in records),'forbidden occurrences',sum(len(item['forbidden'])for item in records))
for record in records:
    if record['forbidden']:print(record)
raise SystemExit(any(record['forbidden'] for record in records))
