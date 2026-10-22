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
    # Reviewed adeaa012 admission: bootstrap precedes the privileged launcher;
    # helper/script/loop bytes are an inseparable exact-source contract.
    require(hashlib.sha256(script).hexdigest()==
            'b7dac23e6300e3c34d6192887f52d6f780b2bef9720f43b94d4c0f1b3116d77d',
            'Reviewed privileged replay script differs')
    require(hashlib.sha256(helper).hexdigest()==
            '72f33cd3676552f902cc7361ae805186971bbdf07e1f3fcc13a45a81b3797425',
            'Reviewed replay admission helper differs')
    parts=script.split(b"-c '\n")
    require(len(parts)==2,'Replay loop boundary differs')
    loop=parts[1].split(b"'\n    ;;",1)[0]
    require(hashlib.sha256(loop).hexdigest()==
            '53717997a6a67054021e6b82a61113676e62b2f2ed134868ffd622eb86874bbb',
            'Reviewed before-first-checker loop differs')
    for line in [b"SCRIPT_SHA = 'b7dac23e6300e3c34d6192887f52d6f780b2bef9720f43b94d4c0f1b3116d77d'\n",
                 b"LOOP_SHA = '53717997a6a67054021e6b82a61113676e62b2f2ed134868ffd622eb86874bbb'\n"]:
        require(helper.count(line)==1,'Mutual helper/script/loop pin differs')
    env=(b'        env:\n'
         b'          LIGHTEFT_JOB_WORKFLOW_REF: ${{ job.workflow_ref }}\n'
         b'          LIGHTEFT_JOB_WORKFLOW_SHA: ${{ job.workflow_sha }}\n'
         b'          LIGHTEFT_JOB_WORKFLOW_PATH: ${{ job.workflow_file_path }}\n'
         b'          LIGHTEFT_JOB_WORKFLOW_REPOSITORY: ${{ job.workflow_repository }}\n')
    boot_name=b'      - name: Observe replay launcher admission on this runner\n'
    boot=(boot_name+b'        shell: /usr/bin/python3 -I -B {0}\n'+env+
          b'        run: |\n'
          b'          import runpy, sys\n'
          b"          sys.argv = ['checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py', 'bootstrap']\n"
          b"          runpy.run_path('checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py', run_name='__main__')\n")
    name=b'      - name: Replay every project module through the Lean kernel\n'
    step=(name+env+b'        shell: /bin/bash --noprofile --norc -p -e -o pipefail {0}\n'
          b'        run: /bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh\n')
    require(workflow.count(name)==1 and workflow.count(boot_name)==1 and workflow.count(boot+step)==1,
            'Adjacent same-job bootstrap/privileged replay contract differs')
    upload=b'      - name: Preserve complete staged-gate evidence including failures\n'
    require(workflow.count(upload)==1,'Full evidence upload differs')
    block=workflow.split(upload,1)[1].split(b'  focused:\n',1)[0]
    path=b'            ${{ runner.temp }}/light-eft-replay-admission-${{ github.run_id }}-${{ github.run_attempt }}\n'
    require(workflow.count(path)==1 and path in block and block.startswith(b'        if: always()\n'),
            'Always-uploaded replay admission evidence path differs')

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
