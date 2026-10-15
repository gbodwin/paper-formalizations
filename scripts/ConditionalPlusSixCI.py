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
import tomllib
import urllib.request

BASE = Path(__file__).resolve().parents[1]
SOURCE = BASE / 'source'
EVIDENCE = BASE / 'evidence'
SHA = 'd0f9ee2364bf4a5aaa7e0ca4da48216e42bbc63e'
CHECKPOINT = 'checkpoints/conditional-plus6-preserved-20261015'
EVIDENCE.mkdir(exist_ok=True)

def write(name, obj):
    (EVIDENCE / name).write_text(json.dumps(obj, indent=2) + '\n')

def run(label, args, cwd=SOURCE):
    start = time.monotonic()
    # Stream unmodified stdout/stderr to a retained log; never start a second process here.
    with (EVIDENCE / (label + '.log')).open('w') as log:
        result = subprocess.run(args, cwd=cwd, stdout=log, stderr=subprocess.STDOUT)
    with (EVIDENCE / 'commands.jsonl').open('a') as log:
        log.write(json.dumps({'label': label, 'argv': args, 'cwd': str(cwd),
                             'exit': result.returncode, 'seconds': time.monotonic()-start})+'\n')
    print(label, 'exit', result.returncode, flush=True)
    if result.returncode:
        print((EVIDENCE / (label+'.log')).read_text(), flush=True)
        raise RuntimeError('Failed: ' + label)
    return (EVIDENCE / (label+'.log')).read_text()

def file_hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def preflight():
    # Repository-wide read avoids launching Lean while another workflow is queued/running.
    repository = os.environ['GITHUB_REPOSITORY']
    own = int(os.environ['GITHUB_RUN_ID'])
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
    manifest = json.loads((SOURCE/CHECKPOINT/'SOURCE_TRANSFER_MANIFEST.json').read_text())
    assert len(manifest['candidate_source_files']) == 165
    def verify_sources():
        for item in manifest['candidate_source_files']:
            data = (SOURCE/item['path']).read_bytes()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
            assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == item['git_blob']
    verify_sources()
    write('source-receipt.json', {'source_commit': SHA, 'ci_commit': os.environ['GITHUB_SHA'],
                                'manifest': manifest})
    assert (SOURCE/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0'
    version = run('lean-version', ['lean', '--version'])
    assert '4.34.0' in version and '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b' in version
    run('lake-version', ['lake', '--version'])
    packages = json.loads((SOURCE/'lake-manifest.json').read_text())['packages']
    assert len(packages) == 9
    for p in packages:
        dest = SOURCE/'.lake/packages'/p['name']
        run('clone-'+p['name'], ['git', 'clone', '--no-checkout', p['url'], str(dest)])
        run('checkout-'+p['name'], ['git', 'checkout', '--detach', p['rev']], dest)
        assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=dest,text=True).strip() == p['rev']
    write('dependency-pins.json', packages)
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
    visit('SlackSparsification')
    expected=json.loads((BASE/CHECKPOINT/'normal-toolchain-evidence/order.json').read_text())
    assert order==[x['module'] for x in expected] and len(order)==28
    warnings=[]
    expected_warnings=json.loads((BASE/CHECKPOINT/'normal-toolchain-evidence/inherited-warnings.json').read_text())
    for n in order:
        src,root=modules[n];out=SOURCE/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean')
        out.parent.mkdir(parents=True,exist_ok=True)
        strict=n=='SlackSparsification' or n.startswith('SlackSparsification.PlusSix')
        args=['lake','env','lean','-j1','-DautoImplicit=false']
        if strict:args+=['-DwarningAsError=true']
        raw=run('compile-'+n,args+['--root='+str(root),'-o',str(out),str(src)])
        if strict:assert not raw.strip(), 'Unexplained strict compiler output'
        else:
            # Require exact previously reviewed diagnostics after normalizing only source root paths.
            old=(BASE/CHECKPOINT/'normal-toolchain-evidence'/('compile-'+n+'.log')).read_text()
            old=old.replace('/workspace/plus-six-verification/checkpoint/candidate',str(SOURCE))
            assert raw==old, 'Changed/unexplained inherited diagnostic: '+n
    write('warning-classification.json',expected_warnings)
    objects=list((SOURCE/'.lake/build/lib/lean').rglob('*.olean'))
    write('object-hashes.json',[{'path':str(p.relative_to(SOURCE)),'sha256':file_hash(p)} for p in objects])
    names=['.'.join(p.relative_to(SOURCE/'.lake/build/lib/lean').with_suffix('').parts) for p in objects]
    for n in order:
        if n=='SlackSparsification':continue
        assert [m for m in names if m==n or m.startswith(n+'.')]==[n]
        raw=run('checker-'+n,['lake','env','leanchecker','-v',n])
        assert raw.strip()=='replaying '+n
    raw=run('recursive-audit',['lake','env','lean','-j1','-DautoImplicit=false','-DwarningAsError=true',
                            'A Note on Distance-Preserving Graph Sparsification/verification/PlusSixAudit.lean'])
    assert '241 actual-owner project declarations, 16 new declarations; 19215 recursively visited constants, 14 opaque bodies' in raw
    rows=list(csv.DictReader((EVIDENCE/'recursive-dependencies.tsv').open(),delimiter='\t'))
    assert len(rows)==19215 and {r['name'] for r in rows if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
    verify_sources()
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=SOURCE).strip()
    write('result.json',{'result':'PASS','tested_source':SHA,'ci_commit':os.environ['GITHUB_SHA'],
                        'scope':'Conditional reduction only: UniformSubsetPlusTwo G C and C > 0',
                        'inherited':23,'strict_new':4,'strict_aggregate':1,'leaf_replays':27})

if __name__=='__main__':
    try:
        {'preflight':preflight,'verify':verify}[sys.argv[1]]()
    finally:
        write('evidence-sha256.json',[{'path':str(p.relative_to(EVIDENCE)),'sha256':file_hash(p)}
                                     for p in sorted(EVIDENCE.rglob('*')) if p.is_file() and p.name!='evidence-sha256.json'])
