"""Explicit future reviewed authority. Construction is read-only; never an auto-run."""
from pathlib import Path
import hashlib,json,os,subprocess,time
from contracts import require,ProductionDisabled
HERE=Path(__file__).resolve().parent
def known_released_lock():return json.loads((HERE/'released-lock.json').read_text())
def facts():
 return dict(owner_pid=os.getpid(),owner_start_ticks=Path('/proc/self/stat').read_text().rsplit(')',1)[1].split()[19],
  boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
  namespaces={n:os.readlink('/proc/self/ns/'+n) for n in ['pid','mnt','cgroup']},
  directory_identity=[Path('/tmp').stat().st_dev,Path('/tmp').stat().st_ino])
def check_document(document,commit,current=None,now=None):
 current=facts() if current is None else current;now=time.monotonic_ns() if now is None else now
 require(document.get('approved_wrapper_commit')==commit,'Review/coordinator commit differs')
 for key in ['exclusive_worker','reviewer_idle','allow_new_epoch']:require(document.get(key) is True,'Missing explicit coordinated '+key)
 require(document.get('same_directory')=='/tmp','Wrong common directory')
 require(isinstance(document.get('coordination_reference'),str) and bool(document['coordination_reference']),'Missing external coordination reference')
 require(document.get('facts')==current,'Fresh owner/boot/namespace/directory incarnation differs')
 known=known_released_lock()
 require(document.get('allow_released_lock_reuse') is True and document.get('released_lock_identity')==known['identity'],'Missing/wrong exact released-lock reuse coordination')
 issued=document.get('issued_ns');require(type(issued) is int and 0<=now-issued<60*10**9,'Stale/future coordinated ownership document')
class ReviewedAuthority:
 def __init__(self,commit,document):
  if not document:raise ProductionDisabled('No independent implementation review and fresh coordination supplied')
  from scope import reviewed_wrapper,APPROVED,FROZEN
  from probability_plan import exact_adapter_commit
  exact_adapter_commit(commit)
  self.bindings=reviewed_wrapper(commit);self.commit=commit;self.document=document
  self.released_lock=known_released_lock()
  ref=self.released_lock['receipt'];root=HERE.parents[1];path=root/ref['path']
  blob=subprocess.check_output(['git','show',ref['commit']+':'+ref['path']],cwd=root)
  body=path.read_bytes();require(body==blob and len(body)==ref['bytes'] and hashlib.sha256(body).hexdigest()==ref['sha256'],'Known released-lock receipt differs')
  prior=json.loads(body)
  require(prior['state']=='released' and prior.get('kernel_echild') and {k:prior[k] for k in ['path','device','inode','directory_identity']}==self.released_lock['identity'],'Known lock was not the exact released ECHILD-verified inode')
  require(prior['epoch']==self.released_lock['released_epoch'],'Released ownership epoch differs')
  self.check_live()
 def check_live(self):check_document(self.document,self.commit)
