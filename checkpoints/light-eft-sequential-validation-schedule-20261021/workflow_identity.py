"""Read-only exact caller/job binding. No native child, lease or admission."""
from pathlib import Path
import hashlib, importlib.util, json, os, subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SPEC=ROOT/'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci-spec.json'

def require(ok,message):
    if not ok: raise ValueError(message)

def git_bytes(path):
    return subprocess.check_output(['git','show','HEAD:'+str(path.relative_to(ROOT))],cwd=ROOT)

def replay_launch_controls(script,workflow):
    # Reviewed 5998c2fd proposal: the startup contract includes the defining
    # runner shell, script entry and inner shell, not merely a later $- test.
    require(hashlib.sha256(script).hexdigest()==
            '9a5cb113fd7c4dc223e7f96fba6558ecde076ba533d71e6980b08d62cce5dd70',
            'Reviewed privileged replay script differs')
    name=b'      - name: Replay every project module through the Lean kernel\n'
    step=(name+b'        shell: /bin/bash --noprofile --norc -p -e -o pipefail {0}\n'
          b'        run: /bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh\n')
    require(workflow.count(name)==1 and workflow.count(step)==1,
            'Inseparable privileged replay workflow/script contract differs')

def exact_controls():
    require(SPEC.read_bytes()==git_bytes(SPEC),'Scheduling specification differs from HEAD')
    spec=json.loads(SPEC.read_text())
    rows={r['path']:r for r in spec['engine_files']}
    paths=['.github/workflows/lean.yml','.github/workflows/light-eft-fair-bit-focused.yml','scripts/KernelCheck.sh',
           str((HERE/'workflow_identity.py').relative_to(ROOT)),str((HERE/'acceptance.py').relative_to(ROOT)),
           'checkpoints/light-eft-canonical-output-adapter-20261020/ci_policy.py']
    result={};contents={}
    for rel in paths:
        p=ROOT/rel
        require(not any(q.is_symlink() for q in [p,*p.parents]),'Symlink scheduling control')
        raw=p.read_bytes();row=dict(path=rel,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        require(rows.get(rel)==row and raw==git_bytes(p),'Scheduling control binding differs: '+rel)
        result[rel]=row;contents[rel]=raw
    replay_launch_controls(contents['scripts/KernelCheck.sh'],contents['.github/workflows/lean.yml'])
    return result

def identity(env,head):
    path=ROOT/'checkpoints/light-eft-canonical-output-adapter-20261020/ci_policy.py'
    s=importlib.util.spec_from_file_location('_exact_schedule_policy',path)
    module=importlib.util.module_from_spec(s);s.loader.exec_module(module)
    return module.ci_identity(env,head)

def head():return subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()

def main():
    env=dict(os.environ)
    controls=exact_controls();ci=identity(env,head())
    require(env.get('LIGHTEFT_VALIDATION_ROLE')=='focused' and not os.path.lexists(ROOT/'.lake'),
            'Focused setup requires an absent .lake tree; no inherited repository build cache')
    print(json.dumps(dict(status='EXACT_WORKFLOW_SOURCE_BINDING_ONLY',CI_identity=ci,controls=controls)))

if __name__=='__main__':main()
