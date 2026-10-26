"""Scoped live metadata checks; completed hashes remain in the post-wait hooks."""
from pathlib import Path
import errno,os,stat,json,hashlib
import path_config as namespace_paths
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

def live_objects(root,target,complete,temporary_pid=None,events=None):
 base=str(target)[:-len('.olean')];allowed={base+s for s in SUFFIXES};temporary=None
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

def live_metadata_outputs(record,spec):
 # Qualification-specific actual JSON output; no production mode is changed.
 e=os.environ;meta=spec['metadata_only'];identity=meta['identity']
 require(record.get('synthetic_fixture') is False and
         record.get('native_qualification')=='NATIVE_HEADER_PROBE_MAIN_567_PROFILE_ONLY' and
         record.get('stage')==spec.get('stage')=='resolve', 'Wrong genuine metadata resource class')
 require(e.get('GITHUB_ACTIONS')=='true' and
         e.get('GITHUB_REPOSITORY')=='gbodwin/paper-formalizations' and
         e.get('GITHUB_REF')=='refs/heads/light-eft-spanners-checkpoints' and
         e.get('GITHUB_EVENT_NAME')=='push' and
         e.get('LIGHTEFT_HANDOFF_PURPOSE')=='reacquisition_qualification' and
         e.get('LIGHTEFT_REACQUISITION_ROLE') in ['producer','consumer'] and
         e.get('GITHUB_JOB')=={'producer':'native_probe_main','consumer':'native_reacquisition_consumer'}.get(e.get('LIGHTEFT_REACQUISITION_ROLE')) and
         e.get('GITHUB_WORKFLOW')=='LightEFT probe main profile qualification',
         'Wrong actual metadata qualification identity')
 require(set(meta)=={'identity','program','request','output','ordered_targets_sha256','namespace_witness'} and
         set(identity)=={'GITHUB_REPOSITORY','GITHUB_SHA','GITHUB_REF','GITHUB_RUN_ID',
             'GITHUB_RUN_ATTEMPT','GITHUB_JOB','GITHUB_WORKFLOW','GITHUB_WORKFLOW_SHA',
             'GITHUB_WORKFLOW_REF','LEAN_NUM_THREADS','LIGHTEFT_JOB_WORKFLOW_REPOSITORY',
             'LIGHTEFT_JOB_WORKFLOW_PATH','LIGHTEFT_JOB_WORKFLOW_SHA','LIGHTEFT_JOB_WORKFLOW_REF','LIGHTEFT_REACQUISITION_ROLE'} and
         all(e.get(k)==v for k,v in identity.items()) and
         record.get('source_commit')==record.get('wrapper_commit')==identity.get('GITHUB_SHA') and
         identity.get('LIGHTEFT_JOB_WORKFLOW_SHA')==identity.get('GITHUB_SHA') and
         identity.get('LIGHTEFT_JOB_WORKFLOW_PATH')=='.github/workflows/light-eft-probe-main-qualification.yml' and
         meta['ordered_targets_sha256']=='aacaaa23315dda4923b1407fc1336bffc7feb541c392e5eb1fbd1e6de6a1ccda',
         'Metadata actual source/workflow/target binding differs')
 work=Path(record['working_directory']);program=Path(meta['program'])
 require(work.is_absolute() and work.resolve(strict=True)==work and
         record.get('planned_command',{}).get('cwd')==str(work),'Changed actual metadata cwd')
 witness_path=Path(meta['namespace_witness'])
 require(witness_path==work.parent/'path-encoding.json' and str(witness_path) in spec['protected'] and
         Path(namespace_paths.__file__).resolve(strict=True)==Path(__file__).resolve(strict=True).with_name('path_config.py') and
         str(Path(namespace_paths.__file__).resolve(strict=True)) in spec['protected'],
         'Unbound namespace witness or qualification helper')
 try:
  data=witness_path.read_bytes()
  require(len(data)<=65536 and hashlib.sha256(data).hexdigest()==spec['protected'][str(witness_path)]['sha256'],
          'Namespace witness bytes changed')
  witness=json.loads(data)
  require(witness['schema']=='SAME_CWD_PATH_SPELLINGS_V2_ABSENCE' and witness['cwd']==str(work),
          'Namespace witness schema/cwd differs')
  namespace_paths.verify_namespace(witness['object_entries'],work)
  namespace_paths.verify_namespace(witness['source_entries'],work)
 except BaseException as error:
  raise LiveOutputRejected('Live namespace directory/absence preservation failed',witness_path,
                           stat_error=repr(error)) from error
 request=work/'request.json';output=work/'graph'/'headers.json'
 require(Path(meta['request'])==request and Path(meta['output'])==output and
         Path(spec['objects'])==work/'objects' and Path(spec['audit'])==work/'empty-audit',
         'Metadata namespace differs')
 require(str(program) in spec['protected'] and str(request) in spec['protected'] and
         spec['protected'][str(program)]['sha256']=='715aa2055684da6eff491bf4de5d6646275d62c3197ce4d00d5072c9bb794567',
         'Unbound production metadata program/request')
 argv=record.get('argv',[])
 require(len(argv)==10 and Path(argv[0]).name=='lean' and
         argv[1:7]==['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true','--run'] and
         argv[7:]==[str(program),'request.json','graph/headers.json'] and
         (work/argv[8]).resolve(strict=True)==request and
         (work/argv[9]).resolve(strict=False)==output, 'Changed actual metadata command')
 files=live_tree(output.parent,{str(output)})
 for path,row in files.items():
  check(0<=row['bytes']<=OBJECT_BOUND,'Live metadata JSON size budget',path,row)
 require(not live_tree(spec['objects'],set()), 'Metadata child generated compiler objects')
 require(not live_audit(spec['audit']), 'Metadata child generated audit exports')
 return files


def runtime_errors(record,preexec=False,terminal=False):
 errors=[]
 try:
  spec=record['output_guard_spec']
  fd=record['lock']['fd'];a=os.fstat(fd);b=observe(record['lock']['path'])
  check(stat.S_ISREG(b.st_mode) and a.st_nlink==1 and (a.st_dev,a.st_ino)==(record['lock']['device'],record['lock']['inode'])==(b.st_dev,b.st_ino),'Live lock FD/path changed',record['lock']['path'],b)
  # Already completed object/resolution/input bindings remain independently immutable.
  for p,row in spec['protected'].items():
   s=observe(p);check(signature(s)==row['identity'],'Live protected object/resolution/input changed',p,s)
  pid=compile_temporary_pid(record,preexec,terminal)
  events=[]
  if 'metadata_only' in spec:live_metadata_outputs(record,spec)
  elif 'admission_only' in spec:live_admission_outputs(record,spec)
  else:live_objects(spec['objects'],spec['target'],spec['stage']!='compile',pid,events)
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
