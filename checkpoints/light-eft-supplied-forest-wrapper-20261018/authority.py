"""Explicit future reviewed authority. Construction is read-only; never an auto-run."""
from pathlib import Path
import os,time
from contracts import require,ProductionDisabled
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
 issued=document.get('issued_ns');require(type(issued) is int and 0<=now-issued<60*10**9,'Stale/future coordinated ownership document')
class ReviewedAuthority:
 def __init__(self,commit,document):
  if not document:raise ProductionDisabled('No independent implementation review and fresh coordination supplied')
  from scope import reviewed_wrapper,APPROVED,FROZEN
  require(commit not in [APPROVED,FROZEN],'Preparation/frozen source is not a wrapper review')
  self.bindings=reviewed_wrapper(commit);self.commit=commit;self.document=document
  self.check_live()
 def check_live(self):check_document(self.document,self.commit)
