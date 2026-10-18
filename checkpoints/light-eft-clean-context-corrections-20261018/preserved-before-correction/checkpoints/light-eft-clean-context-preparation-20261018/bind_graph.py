"""Bind import edges to frozen Git source bytes; read-only Git, never Lean.

The accepted rows-pilot already records the complete project import relation.
Derive it again from every hash-verified frozen source, compare all 486 entries,
and require every project edge to precede its importer. No empty-edge fallback.
"""
from pathlib import Path
import hashlib,json,re,subprocess

A=Path(__file__).resolve().parent
ROOT=A.parents[1]
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
AUTH='checkpoints/light-eft-linked-rows-pilot-20261017/evidence/affected-closure.json'
def sha(b):return hashlib.sha256(b).hexdigest()

def verify():
    original=json.loads((A/'preserved-draft-before-resume/frozen-graph.json').read_text())
    names={r['module'] for r in original}
    assert len(original)==len(names)==486
    authoritative=json.loads((ROOT/AUTH).read_text())['imports']
    assert set(authoritative)==names
    requests=''.join(SOURCE+':'+r['path']+'\n' for r in original).encode()
    raw=subprocess.run(['git','cat-file','--batch'],input=requests,stdout=subprocess.PIPE,check=True,cwd=ROOT).stdout
    cursor=0;seen=set();bound=[];evidence=[]
    for row in original:
        end=raw.index(b'\n',cursor);header=raw[cursor:end].decode().split()
        assert len(header)==3 and header[1]=='blob',header
        size=int(header[2]);start=end+1;data=raw[start:start+size];cursor=start+size+1
        assert raw[cursor-1:cursor]==b'\n'
        assert sha(data)==row['sha256']==sha((ROOT/row['path']).read_bytes()),row['module']
        # Match the accepted parser and fail closed on other import syntax.
        text=data.decode();imports=[];lines=[]
        for i,line in enumerate(text.splitlines(),1):
            if re.search(r'\bimport\s',line):
                assert line.startswith('import '),(row['module'],i,line)
                tokens=line[7:].split('--',1)[0].split()
                assert tokens and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*",t) for t in tokens)
                imports.extend(tokens);lines.append({'line':i,'text':line})
        project=[m for m in imports if m in names]
        assert all(m in names for m in imports if m=='LightEFTSpanners' or m.startswith(('LightEFTSpanners.','LightSpanners.')))
        assert project==authoritative[row['module']],row['module']
        assert len(project)==len(set(project)) and set(project).issubset(seen),row['module']
        seen.add(row['module']);bound.append(dict(row,project_imports=project))
        evidence.append({'module':row['module'],'path':row['path'],'git_blob':header[0],'source_sha256':sha(data),'import_lines':lines,'project_imports':project})
    assert cursor==len(raw) and bound[-1]['module']=='LightEFTSpanners'
    # Aggregate's transitive project closure must cover every ordinary module.
    edges={r['module']:r['project_imports'] for r in bound};todo=['LightEFTSpanners'];closure=set()
    while todo:
        n=todo.pop()
        if n in closure:continue
        closure.add(n);todo.extend(edges[n])
    assert closure==names
    return bound,{'source_commit':SOURCE,'derivation':'hash-verified Git source import lines, cross-checked against accepted affected-closure imports','authoritative_path':AUTH,'authoritative_sha256':sha((ROOT/AUTH).read_bytes()),'rows':evidence,'nodes':486,'project_edges':sum(len(r['project_imports']) for r in bound),'all_source_hashes_match':True,'topological_closure':True,'aggregate_transitive_closure':486,'compiler_invocations':0}

if __name__=='__main__':
    graph,evidence=verify()
    (A/'frozen-graph.json').write_text(json.dumps(graph,indent=2)+'\n')
    (A/'graph-binding.json').write_text(json.dumps(evidence,indent=2)+'\n')
    plan=json.loads((A/'PLAN.json').read_text())
    plan['frozen_graph_sha256']=sha((A/'frozen-graph.json').read_bytes())
    plan['graph_binding_sha256']=sha((A/'graph-binding.json').read_bytes())
    plan['versioncheck']={'planned_count':1,'separate_from_1457_stages':True,'argv':['<fresh_toolchain>/bin/lean','--version'],'status':'PLANNED_NOT_EXECUTED','future_requirement':'separate locked source-bound owned execution receipt; not counted as compile/resolve/replay/audit'}
    (A/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
    print(json.dumps({k:v for k,v in evidence.items() if k!='rows'},indent=2))
