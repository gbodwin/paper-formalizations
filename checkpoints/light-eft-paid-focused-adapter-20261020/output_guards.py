"""Scoped live metadata checks; completed hashes remain in the post-wait hooks."""
from pathlib import Path
import errno,os,stat
from contracts import signature,require,Rejected,SUFFIXES,EXPORTS,TARGET
OBJECT_BOUND=16*1024**2

def metadata(s):
 return dict(device=s.st_dev,inode=s.st_ino,bytes=s.st_size,mode=s.st_mode,
             links=s.st_nlink,uid=s.st_uid,gid=s.st_gid,mtime_ns=s.st_mtime_ns,ctime_ns=s.st_ctime_ns)

class LiveOutputRejected(Rejected):
 def __init__(self,message,path,s=None,stat_error=None):
  observed=dict(s) if isinstance(s,dict) else metadata(s) if s is not None else None
  self.observation=dict(path=str(path),stat=observed,stat_error=stat_error)
  super().__init__(message+': '+str(path))

def check(ok,message,path,s=None):
 if not ok:raise LiveOutputRejected(message,path,s)

def observe(path):
 try:return Path(path).lstat()
 except OSError as exc:raise LiveOutputRejected('Live output stat failed',path,stat_error=repr(exc)) from exc

def directory(path):
 s=observe(path);check(stat.S_ISDIR(s.st_mode),'Non-directory/symlink output ancestor',path,s);return s

def directory_key(s):return (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid)

def object_file(path,s):
 check(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'Nonregular/linked live output',path,s)
 check(0<=s.st_size<=OBJECT_BOUND,'Live object size exceeds ordinary FSIZE',path,s)

def renamed_temporary(path,target,entry_inode,parent_device,events):
 # Only an enumerated exact authorized temporary may disappear. A surviving
 # regular destination must have that very directory-entry inode and device.
 s=observe(target);object_file(target,s)
 check((s.st_dev,s.st_ino)==(parent_device,entry_inode),'Missing temporary lacks matching atomic-rename destination',target,s)
 try:current=Path(path).lstat()
 except FileNotFoundError as exc:
  if exc.errno!=errno.ENOENT:raise LiveOutputRejected('Temporary absence is not ENOENT',path,stat_error=repr(exc)) from exc
 except OSError as exc:raise LiveOutputRejected('Temporary absence check failed',path,stat_error=repr(exc)) from exc
 else:raise LiveOutputRejected('Temporary reappeared during atomic-rename check',path,current)
 events.append(dict(temporary=str(path),destination=str(target),enumerated_inode=entry_inode,
                    parent_device=parent_device,destination_stat=metadata(s)))
 return s

def live_tree(root,allowed,temporary=None,events=None):
 root=Path(root);events=[] if events is None else events
 ancestors={p:directory(p) for p in root.absolute().parents}
 allowed=set(map(str,allowed));dirs={str(parent) for f in allowed for parent in Path(f).parents if root in parent.parents}
 files={}
 def walk(parent):
  before=directory(parent)
  try:entries=os.scandir(parent)
  except OSError as exc:raise LiveOutputRejected('Live output enumeration failed',parent,before,repr(exc)) from exc
  with entries:
   for entry in entries:
    p=Path(entry.path)
    try:inode=entry.inode()
    except OSError as exc:raise LiveOutputRejected('Live output entry inode failed',p,stat_error=repr(exc)) from exc
    try:s=p.lstat()
    except FileNotFoundError as exc:
     if exc.errno!=errno.ENOENT or temporary is None or p!=temporary[0]:
      raise LiveOutputRejected('Enumerated live output disappeared',p,stat_error=repr(exc)) from exc
     s=renamed_temporary(p,temporary[1],inode,before.st_dev,events)
     files[str(temporary[1])]=metadata(s);continue
    except OSError as exc:raise LiveOutputRejected('Live output stat failed',p,stat_error=repr(exc)) from exc
    if stat.S_ISDIR(s.st_mode):
     check(str(p) in dirs,'Unexpected live output directory',p,s);walk(p);continue
    check(str(p) in allowed,'Unexpected live output path',p,s)
    check(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'Nonregular/linked live output',p,s)
    # A legitimate file can grow while being written; content is checked later.
    files[str(p)]=metadata(s)
  after=directory(parent)
  check(directory_key(before)==directory_key(after),'Live output directory identity changed',parent,after)
 walk(root)
 for parent,before in ancestors.items():
  after=directory(parent)
  check(directory_key(before)==directory_key(after),'Output ancestor identity changed',parent,after)
 return files

def live_objects(root,target,complete,temporary_pid=None,events=None,completed=()):
 base=str(target)[:-len('.olean')];allowed={base+s for s in SUFFIXES}|set(completed);temporary=None
 if temporary_pid is not None:
  require(not complete and type(temporary_pid) is int and temporary_pid>0,'Invalid live compile temporary authority')
  temporary=(Path(str(target)+'.tmp.'+str(temporary_pid)),Path(target));allowed.add(str(temporary[0]))
 files=live_tree(root,allowed,temporary,events)
 if complete:check(str(target) in files,'Missing completed target',target)
 for path,row in files.items():
  check(0<=row['bytes']<=OBJECT_BOUND,'Live object size exceeds ordinary FSIZE',path,row)
 return files

def live_audit(root):
 root=Path(root);files=live_tree(root,{str(root/n) for n in EXPORTS})
 for path,row in files.items():
  check(0<=row['bytes']<=64*1024**2,'Live audit file size budget',path,row)
 check(sum(r['bytes'] for r in files.values())<=320*1024**2,'Live audit total size budget',root,observe(root))
 return files

def live_empty_generated(root,target):
 # The existing first-package selection model needs its precreated namespace
 # directories. Permit only that scaffold and reject every generated file.
 root,target=Path(root),Path(target)
 require(target.is_relative_to(root) and target!=root,'Admission target outside generated root')
 files=live_tree(root,{str(target)})
 if files:
  path=next(iter(files));raise LiveOutputRejected('Admission generated-output tree is not empty',path,files[path])
 return files

def live_absent_resolution(work):
 path=Path(work)/'resolution.json'
 try:s=path.lstat()
 except FileNotFoundError as exc:
  if exc.errno==errno.ENOENT:return
  raise LiveOutputRejected('Admission resolution absence check failed',path,stat_error=repr(exc)) from exc
 except OSError as exc:raise LiveOutputRejected('Admission resolution absence check failed',path,stat_error=repr(exc)) from exc
 raise LiveOutputRejected('Admission resolution output appeared',path,s)

def live_admission_outputs(record,spec):
 from ci_handoff_contract import CONTRACT
 contract=spec['admission_only']
 require(isinstance(contract,dict) and set(contract)=={'module','object'},'Invalid admission-only output contract')
 module,path=contract['module'],contract['object']
 require(module in CONTRACT['replay_order'] and record.get('context_admission_module')==module,'Unreviewed admission module')
 require(record.get('stage')==spec.get('stage')=='replay','Admission-only contract outside replay')
 argv=record.get('argv',[])
 require(len(argv)==3 and Path(argv[0]).name=='leanchecker' and argv[1:]==['-v',module],'Wrong admission-only checker command')
 require(record.get('context_qualification')==CONTRACT['context_qualification'],'Admission context qualification differs')
 selection=record.get('context_admission_selection',{})
 require(selection.get('target')==module and selection.get('object')==path and
         list(map(tuple,selection.get('prefix_matches',[])))==[(module,path)],'Admission singleton binding differs')
 dependency=record.get('effective_dependencies',{}).get(module,{})
 protected=spec['protected'].get(path,{})
 require(dependency.get('path')==path and protected.get('path')==path and
         all(k in protected and protected[k]==dependency.get(k) for k in ['bytes','sha256','identity']),
         'Admission object is not a protected effective input')
 root=Path(spec['objects']);target=Path(spec['target'])
 require(root==Path(record['working_directory'])/'objects' and
         target==root/Path(*TARGET.split('.')).with_suffix('.olean'),'Admission generated-output scope differs')
 live_absent_resolution(record['working_directory'])
 return live_empty_generated(root,target)

def compile_temporary_pid(record,preexec,terminal):
 if (preexec or terminal or record.get('stage')!='compile' or record['output_guard_spec']['stage']!='compile'
     or record.get('state')!='exec-authorized' or record.get('kernel_limits_verified') is not True
     or record.get('preexec_binding_verified') is not True or record.get('direct_reaped')
     or 'exit' in record or record.get('terminal_confirmation')):return None
 pid=record.get('child_pid');first=record.get('child_identity',{});handshake=record.get('handshake',{})
 if type(pid) is not int or pid<=0 or type(first.get('start_ticks')) is not int or first['start_ticks']<=0:return None
 expected=dict(pid=pid,ppid=record.get('supervisor_pid'),sid=pid,pgid=pid)
 if type(expected['ppid']) is not int or expected['ppid']<=0:return None
 if any(first.get(k)!=v or handshake.get(k)!=v for k,v in expected.items()):return None
 if type(record.get('preexec_verified_ns')) is not int or record['preexec_verified_ns']<=0:return None
 return pid

def runtime_errors(record,preexec=False,terminal=False):
 errors=[]
 try:
  spec=record['output_guard_spec']
  focused_contract(record,spec)
  fd=record['lock']['fd'];a=os.fstat(fd);b=observe(record['lock']['path'])
  check(stat.S_ISREG(b.st_mode) and a.st_nlink==1 and (a.st_dev,a.st_ino)==(record['lock']['device'],record['lock']['inode'])==(b.st_dev,b.st_ino),'Live lock FD/path changed',record['lock']['path'],b)
  # Already completed object/resolution/input bindings remain independently immutable.
  for p,row in spec['protected'].items():
   s=observe(p);check(signature(s)==row['identity'],'Live protected object/resolution/input changed',p,s)
  pid=compile_temporary_pid(record,preexec,terminal)
  events=[]
  if spec['focused']['mode']=='fixtures':live_tree(spec['objects'],set(spec['focused']['completed']))
  else:live_objects(spec['objects'],spec['target'],spec['stage']!='compile',pid,events,spec['focused']['completed'])
  if events:record.setdefault('output_guard_atomic_renames',[]).extend(events)
  if spec['stage']=='audit':live_audit(spec['audit'])
  else:
   files=live_audit(spec['audit'])
   if files:
    path=next(iter(files));raise LiveOutputRejected('Audit exports appeared outside audit stage',path,files[path])
 except LiveOutputRejected as e:
  detail=dict(error=repr(e),**e.observation,stage=record.get('stage'),preexec=preexec,terminal=terminal)
  record['output_guard_rejection']=detail;errors.append(detail)
 except Exception as e:errors.append(repr(e))
 return errors

# The accepted single-target path above is extended only by this finite ledger.
def focused_contract(record,spec):
 from finite_contract import CONTRACT
 require('admission_only' not in spec,'Admission-only authority is not a focused compile mode')
 f=spec['focused'];modules=CONTRACT['modules'];module=f['module'];mode=f['mode']
 require(mode in ['module','fixtures'] and record.get('focused_module')==module,'Focused module/mode differs')
 require(record['stage']==spec['stage'],'Focused stage differs')
 if mode=='fixtures':
  require(module=='PaidFlagFixtures' and spec['stage']=='compile' and '-o' not in record['argv'],'Invalid fixture authority')
  old=modules;target_module=modules[-1]
 else:
  require(module in modules,'Unreviewed focused target')
  old=modules[:modules.index(module)];target_module=module
 require(f['completed_modules']==old,'Missing/reordered prior completed module')
 work=Path(f['work']);root=work/'objects'
 target=root/Path(*target_module.split('.')).with_suffix('.olean')
 require(Path(spec['objects'])==root and Path(spec['target'])==target,'Shared object root/target differs')
 expected_cwd=work/'audit'/module.rsplit('.',1)[-1] if spec['stage']=='audit' else work
 require(Path(record['working_directory'])==expected_cwd,'Focused cwd differs')
 expected={str(root/Path(*m.split('.')))+s for m in old for s in SUFFIXES}
 completed=set(f['completed']);require(completed<=expected,'Foreign completed output')
 require(all(str(root/Path(*m.split('.')).with_suffix('.olean')) in completed for m in old),'Missing prior object ledger')
 require(all(p in spec['protected'] and spec['protected'][p]['path']==p for p in completed),'Prior output is not protected')
 for folder,names,current in [
  (work/'resolution',{str(work/'resolution'/(m.rsplit('.',1)[-1]+'.json')) for m in modules},
   {str(work/'resolution'/(module.rsplit('.',1)[-1]+'.json'))} if mode=='module' and spec['stage']=='resolve' else set()),
  (work/'audit',{str(work/'audit'/m.rsplit('.',1)[-1]/'ci-evidence'/n) for m in [*modules,'PaidFlagFixtures'] for n in EXPORTS},
   {str(work/'audit'/module.rsplit('.',1)[-1]/'ci-evidence'/n) for n in EXPORTS} if spec['stage']=='audit' else set())]:
  key='completed_resolution' if folder.name=='resolution' else 'completed_audit'
  frozen=set(f[key]);require(frozen<=names and all(p in spec['protected'] for p in frozen),'Unprotected/foreign completed nonobject output')
  files=live_tree(folder,names)
  for p,row in files.items():
   check(p in frozen|current,'Output outside its producing focused stage',p,row)
   check(row['bytes']<=(64 if folder.name=='audit' else 16)*1024**2,'Focused nonobject file budget',p,row)
  if folder.name=='audit':
   for m in [*modules,'PaidFlagFixtures']:
    prefix=str(work/'audit'/m.rsplit('.',1)[-1]/'ci-evidence')+'/'
    check(sum(row['bytes'] for p,row in files.items() if p.startswith(prefix))<=320*1024**2,'Focused audit total budget',folder)
 require({p.name for p in work.iterdir()}=={'objects','resolution','audit'},'Unexpected work output sibling')
