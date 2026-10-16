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
SHA = '58116f153e48e57a055767cabfd1bc89f622214d'
CHECKPOINT = 'checkpoints/conditional-plus6-preserved-20261015'
EVIDENCE.mkdir(exist_ok=True)

def write(name, obj):
    (EVIDENCE / name).write_text(json.dumps(obj, indent=2) + '\n')

def run(label, args, cwd=SOURCE):
    # No Lake launcher around a compiler: direct official executables inherit the lock FD.
    if args[:3]==['lake','env','lean']:args=['lean']+args[3:]
    if args[:3]==['lake','env','leanchecker']:args=['leanchecker']+args[3:]
    if args[0] in {'lean','leanchecker','lake'}:args=[str(Path(shutil.which(args[0])).resolve())]+args[1:]
    submitted=None
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
    modules={}
    for lib in tomllib.loads((SOURCE/'lakefile.toml').read_text())['lean_lib']:
        root=SOURCE/lib['srcDir']
        for src in root.rglob('*.lean'):
            if 'verification' in src.relative_to(root).parts:continue
            modules['.'.join(src.relative_to(root).with_suffix('').parts)]=(src,root)
    # Mathlib/package imports are already cached; treat them as external here.
    order=[];seen=set()
    def visit(n):
        if n in seen:return
        seen.add(n)
        for m in imports.findall(modules[n][0].read_text()):
            if m in modules:visit(m)
        order.append(n)
    visit('SlackSparsification.DirectedPreserver')
    expected={'LinearDistancePreservers.ConsistentTiebreaking','SlackSparsification.Hitting',
              'SlackSparsification.ParameterBounds','SlackSparsification.PlusFourParameters',
              'SlackSparsification.Amplification'}|{'SlackSparsification.'+n for n in
              ['DirectedBasics','DirectedTrees','DirectedExact','DirectedComplete','DirectedPreserver']}
    assert set(order)==expected and len(order)==10
    write('source-module-inventory.json', {'compile_order':order,'leaf_replays':order,
          'audit_entry_point':'verification/DirectedPreserverAudit.lean',
          'note':'Five directed modules plus five imported support modules; no aggregate or reachability draft.'})
    warnings=[]
    for n in order:
        src,root=modules[n];out=SOURCE/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean')
        out.parent.mkdir(parents=True,exist_ok=True)
        strict=n.startswith('SlackSparsification.Directed')
        args=['lake','env','lean','-j1','-DautoImplicit=false']
        if strict:args+=['-DwarningAsError=true']
        raw=run('compile-'+n,args+['--root='+str(root),'-o',str(out),str(src)])
        if strict:assert not raw.strip(), 'Unexplained strict compiler output'
        else:
            # Require exact previously reviewed diagnostics after normalizing only source root paths.
            if n=='LinearDistancePreservers.ConsistentTiebreaking':
                old=(BASE/'checkpoints/directed-preservers-20261016/evidence/attempt-002.log').read_text()
                old=old.replace('/workspace/plus-six-evidence-publish',str(SOURCE))
            else:
                old=(BASE/CHECKPOINT/'normal-toolchain-evidence'/('compile-'+n+'.log')).read_text()
                old=old.replace('/workspace/plus-six-verification/checkpoint/candidate',str(SOURCE))
            assert raw==old, 'Changed/unexplained inherited diagnostic: '+n
            warnings.append({'module':n,'count':len(re.findall(r'^.+:\d+:\d+: warning:', raw, re.MULTILINE)),'classification':'exact inherited baseline'})
    assert sum(r['count'] for r in warnings)==13
    write('warning-classification.json',warnings)
    objects=list((SOURCE/'.lake/build/lib/lean').rglob('*.olean'))
    write('object-hashes.json',[{'path':str(p.relative_to(SOURCE)),'sha256':file_hash(p)} for p in objects])
    names=['.'.join(p.relative_to(SOURCE/'.lake/build/lib/lean').with_suffix('').parts) for p in objects]
    for n in order:
        if n=='SlackSparsification':continue
        assert [m for m in names if m==n or m.startswith(n+'.')]==[n]
        raw=run('checker-'+n,['lake','env','leanchecker','-v',n])
        assert raw.strip()=='replaying '+n
    (SOURCE/'checkpoints/directed-preservers-20261016/evidence').mkdir(exist_ok=True)
    raw=run('recursive-audit',['lake','env','lean','-j1','-DautoImplicit=false','-DwarningAsError=true',
                            'A Note on Distance-Preserving Graph Sparsification/verification/DirectedPreserverAudit.lean'])
    assert '119 actual-owner project declarations, 82 new declarations; 18093 recursively visited constants, 14 opaque bodies' in raw
    audit_dir=SOURCE/'checkpoints/directed-preservers-20261016/evidence'
    for name in ['actual-owner-inventory.tsv','recursive-dependencies.tsv','import-closure-loaded.txt']:
        (EVIDENCE/name).write_bytes((audit_dir/name).read_bytes())
        (audit_dir/name).unlink()
    audit_dir.rmdir()
    rows=list(csv.DictReader((EVIDENCE/'recursive-dependencies.tsv').open(),delimiter='\t'))
    assert len(rows)==18093 and {r['name'] for r in rows if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
    verify_sources()
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=SOURCE).strip()
    commands=[json.loads(x) for x in (EVIDENCE/'commands.jsonl').read_text().splitlines()]
    assert len({r['attempt_id'] for r in commands})==len(commands)
    for previous,current in zip(commands,commands[1:]):
        assert previous['end_monotonic_ns']<=current['lock_acquired_monotonic_ns']<=current['start_monotonic_ns']
    assert all(r['child_reaped'] and r['exit']==0 and r['child_pid'] and r['lock_inode'] for r in commands)
    assert len({(r['lock_device'],r['lock_inode']) for r in commands})==1
    write('lock-reconciliation.json', {'PASS':True,'attempts':len(commands),'unique_ids':True,
          'one_lock_inode':True,'nonoverlapping_intervals':True,'all_children_reaped':True})
    write('result.json',{'result':'PASS','tested_source':SHA,'ci_commit':os.environ['GITHUB_SHA'],
                        'scope':'Finite nonnegative real weights, loopless directed input arcs; no signed weights, parallel edges or runtime claim',
                        'inherited':5,'inherited_warnings':13,'strict_directed':5,'leaf_replays':10})

if __name__=='__main__':
    try:
        {'preflight':preflight,'verify':verify}[sys.argv[1]]()
    except BaseException:
        (EVIDENCE/'failure.txt').write_text(traceback.format_exc())
        raise
    finally:
        write('evidence-sha256.json',[{'path':str(p.relative_to(EVIDENCE)),'sha256':file_hash(p)}
                                     for p in sorted(EVIDENCE.rglob('*')) if p.is_file() and p.name!='evidence-sha256.json'])
