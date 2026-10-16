"""Exact-source CI gate. Every compiler/checker process is awaited before the next."""
from pathlib import Path
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import traceback
import tomllib
import urllib.request
import shutil
from SequentialLean import run_locked

BASE = Path(__file__).resolve().parents[1]
SOURCE = BASE / 'source'
EVIDENCE = BASE / 'evidence'
SHA = '90b270f5442b3ebe50bd41a45f501b2277380d71'
CHECKPOINT = 'checkpoints/light-spanner-recovery-20261016'
EVIDENCE.mkdir(exist_ok=True)

def write(name, obj):
    (EVIDENCE / name).write_text(json.dumps(obj, indent=2) + '\n')

def run(label, args, cwd=SOURCE):
    # No Lake launcher around a compiler: direct official executables inherit the lock FD.
    if args[:3]==['lake','env','lean']:args=['lean']+args[3:]
    if args[:3]==['lake','env','leanchecker']:args=['leanchecker']+args[3:]
    if args[0] in {'lean','leanchecker','lake'}:args=[str(Path(shutil.which(args[0])).resolve())]+args[1:]
    submitted=[SOURCE/'lean-toolchain'] if args[-1]=='--version' else None
    if Path(args[0]).name=='leanchecker':
        suffix=Path(*args[-1].split('.')).with_suffix('.lean')
        submitted=[p for p in SOURCE.rglob(suffix.name) if str(p).endswith(str(suffix))]
        assert len(submitted)==1, 'Checker source must resolve uniquely'
    raw=run_locked(label,args,cwd,EVIDENCE,env=os.environ.copy(),submitted_sources=submitted)
    print(label,'exit',0,flush=True)
    return raw

def file_hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def preflight():
    # Repository-wide read avoids launching Lean while another workflow is queued/running.
    repository = os.environ['GITHUB_REPOSITORY']
    own = int(os.environ['GITHUB_RUN_ID'])
    processes=subprocess.check_output(['ps','-eo','pid,comm'],text=True)
    write('runner-resources.json', {'processes':processes,'disk':subprocess.check_output(['df','-h'],text=True),'ram':subprocess.check_output(['free','-h'],text=True)})
    assert not [line for line in processes.splitlines() if line.split()[-1] in {'lean','leanchecker','lake'}]
    active = []
    for status in ['queued', 'in_progress', 'waiting', 'pending', 'requested']:
        page = 1
        while True:
            url = f'https://api.github.com/repos/{repository}/actions/runs?status={status}&per_page=100&page={page}'
            req = urllib.request.Request(url, headers={'Authorization': 'Bearer '+os.environ['GH_TOKEN'],
                                                      'Accept': 'application/vnd.github+json'})
            with urllib.request.urlopen(req, timeout=30) as response:
                runs = json.load(response)['workflow_runs']
            active.extend({'id': r['id'], 'name': r['name'], 'status': r['status'], 'sha': r['head_sha']}
                          for r in runs if r['id'] != own)
            if len(runs) < 100:
                break
            page += 1
    write('preflight.json', {'current_run': own, 'other_active_runs': active})
    if active:
        raise RuntimeError('Other workflows active: coordinate single-worker slot before retry')

def verify():
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=SOURCE, text=True).strip() == SHA
    assert not (SOURCE/'.lake').exists(), 'Require fresh project outputs and dependency checkout'
    source_files = subprocess.check_output(['git','ls-files','-z'],cwd=SOURCE).decode().split('\0')[:-1]
    original_hashes = {name: file_hash(SOURCE/name) for name in source_files}
    def verify_sources():
        assert all(file_hash(SOURCE/name)==digest for name,digest in original_hashes.items())
        assert not subprocess.check_output(['git','diff','HEAD','--'],cwd=SOURCE).strip()
    verify_sources()
    write('source-receipt.json', {'source_commit': SHA, 'ci_commit': os.environ['GITHUB_SHA'],
                                'tracked_file_sha256': original_hashes})
    assert (SOURCE/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0'
    official_bin=Path(shutil.which('lean')).resolve().parent
    os.environ['PATH']=str(official_bin)+os.pathsep+os.environ['PATH']
    assert Path(shutil.which('leanchecker')).resolve().parent==official_bin
    write('official-path.json',{'PATH':os.environ['PATH'],'bin':str(official_bin)})
    version = run('lean-version', ['lean', '--version'])
    assert '4.34.0' in version and '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b' in version
    run('lake-version', ['lake', '--version'])
    packages = json.loads((SOURCE/'lake-manifest.json').read_text())['packages']
    assert len(packages) == 9
    assert file_hash(SOURCE/'lake-manifest.json') == '615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f'
    assert next(p['rev'] for p in packages if p['name']=='mathlib') == '5ed2965256430c3649e86755f9576b54eca72435'
    for p in packages:
        dest = SOURCE/'.lake/packages'/p['name']
        run('clone-'+p['name'], ['git', 'clone', '--no-checkout', p['url'], str(dest)])
        run('checkout-'+p['name'], ['git', 'checkout', '--detach', p['rev']], dest)
        assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=dest,text=True).strip() == p['rev']
    write('dependency-pins.json', packages)
    sysroot=Path(shutil.which('lean')).resolve().parent.parent
    package_roots=[SOURCE/'.lake/packages'/p['name'] for p in packages]
    os.environ['LEAN_PATH']=os.pathsep.join(map(str,[SOURCE/'.lake/build/lib/lean']+
        [p/'.lake/build/lib/lean' for p in package_roots]+[sysroot/'lib/lean']))
    os.environ['LEAN_SRC_PATH']=os.pathsep.join(map(str,package_roots+[sysroot/'src/lean']))
    write('explicit-lean-paths.json', {k:os.environ[k] for k in ['LEAN_PATH','LEAN_SRC_PATH']})
    # Bootstrap the official cache program one source file at a time, avoiding Lake's parallel build scheduler.
    mathlib = SOURCE/'.lake/packages/mathlib'
    batteries = SOURCE/'.lake/packages/batteries'
    cache_modules = {'.'.join(p.relative_to(mathlib).with_suffix('').parts): (p,mathlib)
                     for p in (mathlib/'Cache').rglob('*.lean')}
    cache_modules.update({'.'.join(p.relative_to(batteries).with_suffix('').parts): (p,batteries)
                          for p in (batteries/'Batteries').rglob('*.lean')})
    imports = re.compile(r'^(?:(?:public|meta)\s+)*import\s+([\w.]+)', re.M)
    def topo(modules, root):
        order=[]; seen=set(); visiting=set()
        def visit(n):
            if n in seen:return
            assert n not in visiting, 'Import cycle'
            visiting.add(n)
            for m in imports.findall(modules[n][0].read_text()):
                if m in modules:visit(m)
                else:assert m.startswith(('Lean','Init','Lake','Std')), 'Unresolved import '+m
            visiting.remove(n);seen.add(n);order.append(n)
        visit(root);return order
    for n in topo(cache_modules,'Cache.Main'):
        if n=='Cache.Main':continue
        src, root=cache_modules[n];out=root/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean')
        out.parent.mkdir(parents=True,exist_ok=True)
        run('cache-bootstrap-'+n,['lake','env','lean','-j1','--root='+str(root),'-o',str(out),str(src)])
    run('official-cache-get',['lake','env','lean','-j1','--run',str(mathlib/'Cache/Main.lean'),'get'])
    # Check every dependency remains at its recorded revision and no tracked source was changed.
    for p in packages:
        dest=SOURCE/'.lake/packages'/p['name']
        assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=dest,text=True).strip()==p['rev']
        assert not subprocess.check_output(['git','status','--porcelain'],cwd=dest).strip()
    verify_sources()
    paper=SOURCE/'An Alternate Proof of Near-Optimal Light Spanners'
    manifest=json.loads((paper/'verification/main-result-source-hashes.json').read_text())
    assert len(manifest['files'])==65
    for p,h in manifest['files'].items():assert file_hash(SOURCE/p)==h,p
    write('candidate-65-file-manifest.json',manifest)
    modules={'LightSpanners.'+p.stem:(p,paper) for p in (paper/'LightSpanners').glob('*.lean')}
    assert len(modules)==59
    aggregate=imports.findall((paper/'LightSpanners.lean').read_text())
    assert len(aggregate)==59 and set(aggregate)==set(modules)
    modules['LightSpanners']=(paper/'LightSpanners.lean',paper)
    order=[];seen=set();visiting=set()
    def visit(n):
        if n in seen:return
        assert n not in visiting;visiting.add(n)
        for m in imports.findall(modules[n][0].read_text()):
            if m in modules:visit(m)
            else:assert m.startswith(('Mathlib.','Lean.','Batteries.','Std.','Init.')),m
        visiting.remove(n);seen.add(n);order.append(n)
    visit('LightSpanners');assert len(order)==60
    leaves=[n for n in order if n!='LightSpanners']
    write('source-module-inventory.json',{'compile_order':order,'leaf_replays':leaves,
          'source_hashes':{n:file_hash(modules[n][0]) for n in order}})
    old_warnings=json.loads((BASE/CHECKPOINT/'evidence/warning-classification.json').read_text())
    inherited={r['module'] for r in old_warnings};assert len(inherited)==9 and len(old_warnings)==22
    warnings=[]
    for n in order:
        src,root=modules[n];out=SOURCE/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean')
        out.parent.mkdir(parents=True,exist_ok=True)
        strict=n not in inherited
        args=['lean','-j1','-DautoImplicit=false']
        if strict:args+=['-DwarningAsError=true']
        raw=run('compile-'+n,args+['--root='+str(root),'-o',str(out),str(src)])
        if strict:assert not raw.strip(), 'Unexpected strict-module diagnostic: '+n
        else:
            baseline=BASE/CHECKPOINT/'evidence'/('compile-'+n+'.log')
            old=baseline.read_text().replace('/workspace/light-spanner-verification',str(SOURCE))
            assert raw==old,'Changed diagnostic body, not just count: '+n
            warnings.append({'module':n,'headers':len(re.findall(r'^.+:\d+:\d+: warning:',raw,re.M)),
               'baseline_path':str(baseline.relative_to(BASE)),'baseline_sha256':file_hash(baseline),
               'normalization':'Only /workspace/light-spanner-verification replaced by exact SOURCE checkout root',
               'classification':'exact normalized full diagnostic match'})
    assert sum(r['headers'] for r in warnings)==22
    write('warning-classification.json',warnings)
    objects=sorted((SOURCE/'.lake/build/lib/lean').rglob('*.olean'));assert len(objects)==60
    write('object-hashes.json',[{'path':str(p.relative_to(SOURCE)),'sha256':file_hash(p)} for p in objects])
    names=['.'.join(p.relative_to(SOURCE/'.lake/build/lib/lean').with_suffix('').parts) for p in objects]
    for n in leaves:
        assert [m for m in names if m==n or m.startswith(n+'.')]==[n]
        raw=run('checker-'+n,['leanchecker','-v',n]);assert raw.strip()=='replaying '+n
    for label,src in [('all-declarations-audit',paper/'verification/AllDeclarationsAudit.lean'),
                      ('selected-axioms',paper/'verification/SelectedAxioms.lean'),
                      ('recursive-audit',BASE/'checkpoints/light-spanner-ci-20261016/RecursiveAudit.lean')]:
        raw=run(label,['lean','-j1','-DautoImplicit=false','-DwarningAsError=true',str(src)])
        print(raw[-800:],flush=True)
    roots=list(csv.DictReader((EVIDENCE/'actual-owner-inventory.tsv').open(),delimiter='\t'))
    rows=list(csv.DictReader((EVIDENCE/'recursive-dependencies.tsv').open(),delimiter='\t'))
    assert len(roots)==795 and {r['owner'] for r in roots}==set(leaves)
    assert len(rows)==22323 and {r['name'] for r in rows if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
    export=EVIDENCE/'audit-export';export.mkdir();data=(EVIDENCE/'recursive-dependencies.tsv').read_bytes();parts=[];chunk=b''
    def flush(d):
        name=f'part-{len(parts):03d}.tsv';(export/name).write_bytes(d)
        parts.append({'path':name,'bytes':len(d),'sha256':hashlib.sha256(d).hexdigest()})
    for row in data.splitlines(keepends=True):
        if chunk and len(chunk)+len(row)>200000:flush(chunk);chunk=b''
        chunk+=row
    if chunk:flush(chunk)
    assert b''.join((export/p['path']).read_bytes() for p in parts)==data
    (export/'manifest.json').write_text(json.dumps({'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),
        'parts':parts,'reconstruction':'Concatenate parts in listed order as bytes without separators.'},indent=2)+'\n')
    commands=[json.loads(x) for x in (EVIDENCE/'commands.jsonl').read_text().splitlines()]
    assert len({r['attempt_id'] for r in commands})==len(commands)
    assert len({(r['lock_device'],r['lock_inode']) for r in commands})==1
    for a,b in zip(commands,commands[1:]):assert a['end_monotonic_ns']<=b['lock_acquired_monotonic_ns']<=b['start_monotonic_ns']
    for r in commands:
        assert r['child_reaped'] and r['exit']==0 and r['child_pid']
        folder=EVIDENCE/'attempts'/r['attempt_id'];assert json.loads((folder/'receipt.json').read_text())==r
        for s in r['submitted_sources']:
            assert file_hash(folder/(s['sha256']+'.lean'))==s['sha256']==file_hash(Path(s['path']))
        if Path(r['argv'][0]).name in {'lean','leanchecker','lake'}:assert r['submitted_sources']
    verify_sources()
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=SOURCE).strip()
    write('toolchain-executable-hashes.json',{n:file_hash(Path(shutil.which(n)).resolve()) for n in ['lean','leanchecker','lake']})
    write('result.json',{'PASS':True,'tested_source':SHA,'trigger_commit':os.environ['GITHUB_SHA'],
          'commands':len(commands),'builds':60,'leaf_replays':59,'audits':3,'strict_builds':51,
          'exact_diagnostic_baselines':9,'warning_headers':22,'roots':795,'recursive_constants':len(rows),
          'opaque_bodies':sum(r['kind']=='opaque' for r in rows),'audit_chunks':len(parts),
          'source_bound_receipts_verified':True,'one_lock_inode':True,'unique_ids':True,'nonoverlap':True,'all_children_reaped':True,
          'scope':'Connected finite simple graphs, positive actual-edge weights, every epsilon>0 and k>=1; no publication or whole-paper acceptance'})
    print((EVIDENCE/'result.json').read_text(),flush=True)

if __name__=='__main__':
    try:{'preflight':preflight,'verify':verify}[sys.argv[1]]()
    except BaseException:
        (EVIDENCE/'failure.txt').write_text(traceback.format_exc());raise
    finally:
        write('evidence-sha256.json',[{'path':str(p.relative_to(EVIDENCE)),'bytes':p.stat().st_size,'sha256':file_hash(p)}
          for p in sorted(EVIDENCE.rglob('*')) if p.is_file() and p.name!='evidence-sha256.json'])
