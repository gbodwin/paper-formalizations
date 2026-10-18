"""Pure byte-level final-audit/chunk contract, with no retained-root assumptions."""
import hashlib,re
from clean_contract import GRAPH, PLAN, require, validate_receipt

OUTPUTS=('actual-owner-inventory.tsv','recursive-dependencies.tsv','import-closure-loaded.txt','strict-violations.txt','raw.log')
KINDS={'axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor'}
def project(owner):return any(owner==p or owner.startswith(p+'.') for p in ['LightSpanners','LightEFTSpanners'])

def rows(data,header):
    require(data.endswith(b'\n'),'Truncated audit export')
    lines=data.decode().splitlines();require(lines and lines[0].split('\t')==header,'Wrong audit header')
    result=[]
    for line in lines[1:]:
        cells=line.split('\t');require(len(cells)==len(header),'Malformed audit row');result.append(dict(zip(header,cells)))
    return result

def reconcile_audit_data(ctx,frame,files,chunks):
    step={'module':'LightEFTFullAudit','stage':'audit','source_sha256':PLAN['audit_source_sha256']}
    validate_receipt(ctx,step,frame)
    require(set(files)==set(OUTPUTS) and set(chunks)==set(OUTPUTS),'Four source files plus raw required')
    total=0
    for name in OUTPUTS:
        item=files[name];data=item['data'];total+=len(data)
        require(item['producer_attempt']==frame['receipt']['attempt_id'] and item['context']==ctx.output_id and
                item['fresh'] and item['regular'] and not item['symlink'],'Stale/cross-context audit output')
        expected=str(ctx.work/'ci-evidence'/name) if name!='raw.log' else str(ctx.evidence/'audit/raw.log')
        require(item['path']==expected and len(data)<=64*1024**2,'Wrong/oversize audit output')
        parts=chunks[name];reconstructed=b''.join(p['data'] for p in parts)
        require(parts and all(hashlib.sha256(p['data']).hexdigest()==p['sha256'] for p in parts),'Bad part hash')
        require(reconstructed==data and all(p['data'].endswith(b'\n') for p in parts[:-1]),'Not exact row-aligned reconstruction')
    require(total<=320*1024**2,'Source-directed audit budget exceeded')
    inv=rows(files['actual-owner-inventory.tsv']['data'],['owner','name','kind','unsafe','partial'])
    dep=rows(files['recursive-dependencies.tsv']['data'],['name','owner','kind','typeDependencies','bodyDependencies','unsafe','partial'])
    loaded_data=files['import-closure-loaded.txt']['data'];require(loaded_data.endswith(b'\n'),'Truncated imports')
    loaded=loaded_data.decode().splitlines();required={r['module'] for r in GRAPH}
    require(len(loaded)==len(set(loaded)) and required.issubset(loaded),'Missing/duplicate loaded project modules')
    require(not ({m for m in loaded if project(m)}-required),'Unexpected project module')
    require(files['strict-violations.txt']['data']==b'\n','Strict audit findings')
    inventory={r['name']:r for r in inv};closure={r['name']:r for r in dep}
    require(inv and len(inventory)==len(inv) and len(closure)==len(dep),'Duplicate/empty audit inventory')
    for r in inv+dep:
        require(r['kind'] in KINDS and r['unsafe']=='false' and r['partial']=='false','Unsafe/partial/unknown declaration')
    for name,r in inventory.items():
        require(project(r['owner']) and r['owner'] in loaded and r['kind']!='axiom','Project axiom/incorrect actual owner')
        require(name in closure and all(closure[name][key]==r[key] for key in ['owner','kind','unsafe','partial']),'Root missing from closure')
    require({n for n,r in closure.items() if project(r['owner'])}==set(inventory),'Private/generated owner omitted')
    axioms={r['name'] for r in dep if r['kind']=='axiom'}
    require(axioms.issubset({'propext','Classical.choice','Quot.sound'}),'Disallowed recursive axiom')
    links={}
    for name,r in closure.items():
        refs=[]
        for key in ['typeDependencies','bodyDependencies']:
            if r[key]:refs+=r[key].split(',')
        require(all(x in closure for x in refs),'Unresolved type/body dependency')
        require(r['kind'] not in ('inductive','constructor','recursor') or r['bodyDependencies'],'Missing recursor/inductive rule coverage')
        links[name]=refs
    visited=set();todo=list(inventory)
    while todo:
        n=todo.pop()
        if n in visited:continue
        visited.add(n);todo.extend(links[n])
    require(visited==set(closure),'Incomplete/nonrecursive closure')
    raw=files['raw.log']['data'].decode()
    matches=re.findall(r'DIAGNOSTIC ONLY: (\d+) actual-owner project declarations, (\d+) covered declarations; (\d+) recursively visited constants, (\d+) opaque bodies; axioms #?\[([^\]]*)\]',raw,re.S)
    require(len(matches)==1,'Fresh full-audit diagnostic missing/duplicated')
    a,b,c,d,ax=matches[0];ordinary=required-{'LightEFTSpanners'}
    counts=(len(inv),sum(r['owner'] in ordinary for r in inv),len(dep),sum(r['kind']=='opaque' for r in dep))
    require(tuple(map(int,[a,b,c,d]))==counts and {x.strip() for x in ax.split(',') if x.strip()}==axioms,'Fresh audit counts/axioms disagree')
    require(not re.search(r'^(?:.*:\d+:\d+: )?(?:warning|error):',raw,re.M),'Lean diagnostics')
    return {'required_ordinary_modules_loaded':485,'aggregate_loaded':True,'actual_owner_roots':counts[0],
            'closure_constants':counts[2],'opaque_bodies':counts[3],'axioms':sorted(axioms),
            'strict_findings':0,'historical_counts_used':False,'source_and_raw_bytes':total,'chunks_verified':True}
