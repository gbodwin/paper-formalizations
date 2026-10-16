"""Sequential immutable-candidate verification. No Lake build and no CI trigger."""
from pathlib import Path
import csv,hashlib,json,os,re,subprocess,sys,traceback,time
from SequentialLean import run_locked
BASE=Path(__file__).resolve().parents[2]
CHECK=Path(__file__).resolve().parent
E=CHECK/'evidence';E.mkdir(exist_ok=True)
P=BASE/'An Alternate Proof of Near-Optimal Light Spanners'
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux')
PACKAGES=Path('/workspace/paper-formalizations/.lake/packages')
SHA='90b270f5442b3ebe50bd41a45f501b2277380d71'
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,d):(E/n).write_text(json.dumps(d,indent=2)+'\n')
def run(label,args,submitted=None):
    raw=run_locked(label,args,BASE,E,env=os.environ.copy(),submitted_sources=submitted)
    print(label,'PASS',flush=True)
    return raw

def main():
    assert not (BASE/'.lake/build').exists(),'Require fresh project outputs'
    manifest=json.loads((P/'verification/main-result-source-hashes.json').read_text())
    assert len(manifest['files'])==65
    for p,h in manifest['files'].items():assert hashfile(BASE/p)==h,p
    write('candidate-manifest-reconciliation.json',{'candidate_commit':SHA,'files':manifest['files'],'matched':65,
          'verification_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=BASE,text=True).strip()})
    processes=subprocess.check_output(['ps','-eo','pid,comm'],text=True)
    assert not [x for x in processes.splitlines() if x.split()[-1] in {'lean','leanchecker','lake'}]
    write('initial-resources.json',{'processes':processes,'disk':subprocess.check_output(['df','-h','/workspace'],text=True),
          'memory':subprocess.check_output(['free','-h'],text=True),'memory_limit':Path('/sys/fs/cgroup/memory.max').read_text(),'cpu_max':Path('/sys/fs/cgroup/cpu.max').read_text()})
    assert hashfile(Path('/workspace/toolchains/lean.tar.zst'))=='caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b'
    assert hashfile(BASE/'lake-manifest.json')=='615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f'
    packages=json.loads((BASE/'lake-manifest.json').read_text())['packages'];assert len(packages)==9
    for p in packages:
        d=PACKAGES/p['name'];assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip()==p['rev']
        assert not subprocess.check_output(['git','status','--porcelain'],cwd=d).strip()
    write('pins.json',packages)
    os.environ['LEAN_PATH']=os.pathsep.join(map(str,[BASE/'.lake/build/lib/lean']+[PACKAGES/p['name']/'.lake/build/lib/lean' for p in packages]+[TOOL/'lib/lean']))
    os.environ['LEAN_SRC_PATH']=os.pathsep.join(map(str,[P]+[PACKAGES/p['name'] for p in packages]+[TOOL/'src/lean']))
    ver=run('official-lean-version',[str(TOOL/'bin/lean'),'--version'],[BASE/'lean-toolchain'])
    assert '4.34.0' in ver and '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b' in ver
    write('toolchain-hashes.json',{n:hashfile(TOOL/'bin'/n) for n in ['lean','leanchecker','lake']})
    modules={'LightSpanners.'+f.stem:f for f in (P/'LightSpanners').glob('*.lean')}
    assert len(modules)==59
    imports=re.compile(r'^(?:(?:public|meta)\s+)*import\s+([\w.]+)',re.M)
    assert set(imports.findall((P/'LightSpanners.lean').read_text()))==set(modules)
    modules['LightSpanners']=P/'LightSpanners.lean';order=[];seen=set();visiting=set()
    def visit(n):
        if n in seen:return
        assert n not in visiting;visiting.add(n)
        for m in imports.findall(modules[n].read_text()):
            if m in modules:visit(m)
            else:assert m.startswith(('Mathlib.','Lean.','Batteries.','Std.','Init.')),m
        visiting.remove(n);seen.add(n);order.append(n)
    visit('LightSpanners');assert len(order)==60
    write('module-inventory.json',{'compile_order':order,'replays':[n for n in order if n!='LightSpanners'],
          'source_hashes':{n:hashfile(modules[n]) for n in order},'project_outputs_initially_empty':True,'dependency_cache':'reused existing official pinned dependency outputs; no old LightSpanners outputs in search path'})
    baseline={}
    for f in (P/'verification').glob('*.txt'):
        for line in f.read_text().splitlines():
            m=re.match(r'^warning: (.*\.lean:\d+:\d+): (.*)$',line)
            if m:baseline.setdefault(m[1]+': warning: '+m[2],[]).append(str(f.relative_to(BASE)))
    warning_rows=[]
    for n in order:
        out=BASE/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        args=[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','--root='+str(P),'-o',str(out),str(modules[n])]
        if n=='LightSpanners':args.insert(3,'-DwarningAsError=true')
        raw=run('compile-'+n,args)
        assert not re.search(r'^.+:\d+:\d+: error:',raw,re.M)
        for line in re.findall(r'^.+:\d+:\d+: warning:.*$',raw,re.M):
            normalized=line.replace(str(BASE)+'/', '')
            warning_rows.append({'module':n,'header':normalized,'historical_header_matches':baseline.get(normalized,[]),
                 'classification':'inherited diagnostic header' if normalized in baseline else 'fresh warning requiring classification'})
        write('warning-classification.json',warning_rows)
    objects=sorted((BASE/'.lake/build/lib/lean').rglob('*.olean'))
    assert len(objects)==60
    write('object-hashes.json',[{'path':str(p.relative_to(BASE)),'sha256':hashfile(p)} for p in objects])
    for n in order:
        if n=='LightSpanners':continue
        raw=run('replay-'+n,[str(TOOL/'bin/leanchecker'),'-v',n],[modules[n]])
        assert raw.strip()=='replaying '+n
    for name,src in [('all-declarations-audit',P/'verification/AllDeclarationsAudit.lean'),
                     ('selected-axioms',P/'verification/SelectedAxioms.lean'),('recursive-audit',CHECK/'RecursiveAudit.lean')]:
        raw=run(name,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(src)])
        print(raw[-600:],flush=True)
    rows=list(csv.DictReader((E/'recursive-dependencies.tsv').open(),delimiter='\t'))
    roots=list(csv.DictReader((E/'actual-owner-inventory.tsv').open(),delimiter='\t'))
    assert {r['owner'] for r in roots}==set(order)-{'LightSpanners'}
    assert {r['name'] for r in rows if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
    export=E/'audit-export';export.mkdir();data=(E/'recursive-dependencies.tsv').read_bytes();parts=[];chunk=b''
    def flush(d):
        name=f'part-{len(parts):03d}.tsv';(export/name).write_bytes(d);parts.append({'path':name,'bytes':len(d),'sha256':hashlib.sha256(d).hexdigest()})
    for row in data.splitlines(keepends=True):
        if chunk and len(chunk)+len(row)>200000:flush(chunk);chunk=b''
        chunk+=row
    if chunk:flush(chunk)
    (export/'manifest.json').write_text(json.dumps({'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'parts':parts,'reconstruction':'Concatenate listed parts as bytes, without separators.'},indent=2)+'\n')
    assert b''.join((export/p['path']).read_bytes() for p in parts)==data
    commands=[json.loads(l) for l in (E/'commands.jsonl').read_text().splitlines()]
    assert len({c['attempt_id'] for c in commands})==len(commands)
    assert len({(c['lock_device'],c['lock_inode']) for c in commands})==1
    for prev,cur in zip(commands,commands[1:]):assert prev['end_monotonic_ns']<=cur['lock_acquired_monotonic_ns']<=cur['start_monotonic_ns']
    for c in commands:
        assert c['child_reaped'] and c['exit']==0 and c['submitted_sources']
        folder=E/'attempts'/c['attempt_id'];assert json.loads((folder/'receipt.json').read_text())==c
        for src in c['submitted_sources']:
            assert hashfile(folder/(src['sha256']+'.lean'))==src['sha256']==hashfile(Path(src['path']))
    for p,h in manifest['files'].items():assert hashfile(BASE/p)==h
    assert not subprocess.check_output(['git','diff',SHA,'--',str(P)],cwd=BASE).strip()
    result={'PASS':True,'tested_candidate':SHA,'commands':len(commands),'compilations':60,'individual_replays':59,'audits':3,
      'roots':len(roots),'recursive_constants':len(rows),'opaque_bodies':sum(r['kind']=='opaque' for r in rows),
      'warnings':len(warning_rows),'unmatched_warning_headers':sum(not w['historical_header_matches'] for w in warning_rows),'audit_chunks':len(parts),
      'source_bound_receipts_verified':True,'one_lock_inode':True,'unique_ids':True,'nonoverlap':True,'children_reaped':True}
    write('result.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':
    try:main()
    except BaseException:
        (E/'failure.txt').write_text(traceback.format_exc());raise
    finally:
        write('evidence-sha256.json',[{'path':str(p.relative_to(E)),'bytes':p.stat().st_size,'sha256':hashfile(p)} for p in sorted(E.rglob('*')) if p.is_file() and p.name!='evidence-sha256.json'])
