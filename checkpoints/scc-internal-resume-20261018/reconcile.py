"""Reconcile preserved SCC evidence without invoking Lean or changing proofs."""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
prior = ROOT / 'checkpoints/scc-internal-reconciliation-20261018/reconcile.py'
text = prior.read_text()
text = text.replace('HERE = Path(__file__).resolve().parent', 'HERE = Path(' + repr(str(HERE)) + ')')
start = text.index("with lock.open('r') as f:")
end = text.index('active=[]', start)
text = text[:start] + "lock_observation = dict(path=str(lock), exists=lock.exists(), historical_device=33, historical_inode=3849)\nif lock.exists():\n    with lock.open('r') as f:\n        fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)\n        st=os.fstat(f.fileno())\n        lock_observation.update(device=st.st_dev,inode=st.st_ino,free=True)\n        fcntl.flock(f,fcntl.LOCK_UN)\nelse:\n    lock_observation['note']='Absent in this session; historical inode continuity is not asserted. No compiler invoked and no lock created.'\n" + text[end:]
text = text.replace('lock=dict(path=str(lock),device=st.st_dev,inode=st.st_ino,free=True)', 'lock=lock_observation')
text = text[:text.index('print(json.dumps(')] + "assert all(r['matches'] for r in current_bindings)\nprint(json.dumps({k:result[k] for k in ['observed_utc','tested_source','manifest_entries','chunks','roots','recursive_closure','axioms','lock','active_compilers','disk_free_bytes','mem_available_kib','fresh_compiler_invocations']},indent=2))\n"
exec(compile(text,str(prior),'exec'),{'__file__':str(prior)})
