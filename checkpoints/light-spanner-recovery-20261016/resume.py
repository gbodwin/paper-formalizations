"""Resume only kernel replays/audits after the preserved PATH setup failure."""
from verify import *
import shutil

def resume():
    os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH']
    assert Path(shutil.which('lean')).resolve()==TOOL/'bin/lean'
    previous=json.loads((E/'attempts/12a6b6d7843c4c0c9c89ec10282e63cf/receipt.json').read_text())
    for k,v in previous['lean_environment'].items():os.environ[k]=v
    write('resume-environment.json',{'PATH':os.environ['PATH'],'lean':shutil.which('lean'),
          'reason':'Official leanchecker invokes lean by name; initial PATH lacked the official bin directory.',
          'proof_source_changes':False,'rebuild_required':False})
    manifest=json.loads((P/'verification/main-result-source-hashes.json').read_text())
    for p,h in manifest['files'].items():assert hashfile(BASE/p)==h
    for r in json.loads((E/'object-hashes.json').read_text()):assert hashfile(BASE/r['path'])==r['sha256']
    inv=json.loads((E/'module-inventory.json').read_text());order=inv['compile_order']
    modules={n:P/Path(*n.split('.')).with_suffix('.lean') for n in order}
    warning_rows=json.loads((E/'warning-classification.json').read_text())
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
        assert c['child_reaped'] and c['submitted_sources']
        assert c['exit']==0 or c['attempt_id']=='12a6b6d7843c4c0c9c89ec10282e63cf'
        folder=E/'attempts'/c['attempt_id'];assert json.loads((folder/'receipt.json').read_text())==c
        for src in c['submitted_sources']:
            assert hashfile(folder/(src['sha256']+'.lean'))==src['sha256']==hashfile(Path(src['path']))
    for p,h in manifest['files'].items():assert hashfile(BASE/p)==h
    assert not subprocess.check_output(['git','diff',SHA,'--',str(P)],cwd=BASE).strip()
    result={'PASS':True,'tested_candidate':SHA,'commands':len(commands),'failed_attempts':sum(c['exit']!=0 for c in commands),'compilations':60,'individual_replays':59,'audits':3,
      'roots':len(roots),'recursive_constants':len(rows),'opaque_bodies':sum(r['kind']=='opaque' for r in rows),
      'warnings':len(warning_rows),'unmatched_warning_headers':sum(not w['historical_header_matches'] for w in warning_rows),'audit_chunks':len(parts),
      'source_bound_receipts_verified':True,'one_lock_inode':True,'unique_ids':True,'nonoverlap':True,'children_reaped':True}
    write('result.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':
    try:resume()
    except BaseException:
        (E/'resume-failure.txt').write_text(traceback.format_exc());raise
    finally:
        write('evidence-sha256.json',[{'path':str(p.relative_to(E)),'bytes':p.stat().st_size,'sha256':hashfile(p)} for p in sorted(E.rglob('*')) if p.is_file() and p.name!='evidence-sha256.json'])
