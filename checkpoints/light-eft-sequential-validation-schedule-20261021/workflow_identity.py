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

def replay_launch_controls(script,workflow,helper):
    # Preserve the original actual launcher primitives; the old full-job loop
    # remains source-bound but is no longer the workflow's replay entrypoint.
    require(hashlib.sha256(script).hexdigest()==
            'b7dac23e6300e3c34d6192887f52d6f780b2bef9720f43b94d4c0f1b3116d77d',
            'Original privileged replay script differs')
    require(hashlib.sha256(helper).hexdigest()==
            '2bcbe3ba3a4154d61ff01a19b0dfc615a6b50f64b3eb09020765a299af7fe4be',
            'Original launcher observation primitives differ')
    path=ROOT/'checkpoints/light-eft-global-replay-batches-20261026/route_status.py'
    raw=path.read_bytes();row=dict(path=str(path.relative_to(ROOT)),bytes=len(raw),
                                 sha256=hashlib.sha256(raw).hexdigest())
    rows={r['path']:r for r in json.loads(SPEC.read_text())['engine_files']}
    require(not any(p.is_symlink() for p in [path,*path.parents]) and
            rows.get(row['path'])==row and raw==git_bytes(path),'New route controller not source-bound')
    spec=importlib.util.spec_from_file_location('_exact_serial_route_controls',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    module.controls()  # Every exact caller/launcher byte is bound in all5specs.
    require(workflow.count(b'  replay1:\n')==1 and workflow.count(b'  replay2:\n')==1 and
            workflow.count(b'  replay3:\n')==1 and
            b'    needs: [check, replay1, replay2, replay3]\n' in workflow and
            b'    needs: [check, replay1, replay2, replay3, focused]\n' in workflow,
            'Serial coverage/fresh focused conjunction differs')

def exact_controls():
    require(SPEC.read_bytes()==git_bytes(SPEC),'Scheduling specification differs from HEAD')
    spec=json.loads(SPEC.read_text())
    rows={r['path']:r for r in spec['engine_files']}
    paths=['.github/workflows/lean.yml','.github/workflows/light-eft-fair-bit-focused.yml','scripts/KernelCheck.sh',
           'checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py',
           str((HERE/'workflow_identity.py').relative_to(ROOT)),str((HERE/'acceptance.py').relative_to(ROOT)),
           'checkpoints/light-eft-canonical-output-adapter-20261020/ci_policy.py']
    result={};contents={}
    for rel in paths:
        p=ROOT/rel
        require(not any(q.is_symlink() for q in [p,*p.parents]),'Symlink scheduling control')
        raw=p.read_bytes();row=dict(path=rel,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        require(rows.get(rel)==row and raw==git_bytes(p),'Scheduling control binding differs: '+rel)
        result[rel]=row;contents[rel]=raw
    replay_launch_controls(contents['scripts/KernelCheck.sh'],contents['.github/workflows/lean.yml'],
                           contents['checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py'])
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
