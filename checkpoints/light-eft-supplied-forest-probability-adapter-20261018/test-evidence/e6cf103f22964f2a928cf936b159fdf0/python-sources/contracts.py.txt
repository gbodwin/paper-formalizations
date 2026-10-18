"""Narrow scoped filesystem, object-selection and output contracts; no process launch."""
from pathlib import Path
import hashlib,json,os,re,stat
TARGET='LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability'
THEOREM='LightEFTSpanners.SampledGreedy.polynomial_supplied_forest_package_failure_probability'
STAGES=('compile','resolve','replay','audit')
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig')
EXPORTS=('actual-owner-inventory.tsv','recursive-dependencies.tsv','import-closure-loaded.txt','strict-violations.txt')
class Rejected(RuntimeError):pass
class ProductionDisabled(Rejected):pass
def require(ok,message):
 if not ok:raise Rejected(message)
def sha(b):return hashlib.sha256(b).hexdigest()
def signature(s):return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def regular(path):
 p=Path(path)
 for parent in p.absolute().parents:require(not parent.is_symlink(),'Symlink parent: '+str(parent))
 fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
 with os.fdopen(fd,'rb') as f:
  a=os.fstat(f.fileno());require(stat.S_ISREG(a.st_mode) and a.st_nlink==1,'Nonregular/multilink input')
  b=f.read();z=os.fstat(f.fileno())
  require(signature(a)==signature(z)==signature(p.lstat()),'Input changed while reading')
  return dict(path=str(p),bytes=len(b),sha256=sha(b),identity=signature(z)),b
def bind(path,expected=None):
 r,b=regular(path)
 if expected:
  require(r['sha256']==expected['sha256'],'Input hash drift: '+str(path))
  if 'bytes' in expected:require(r['bytes']==expected['bytes'],'Input length drift')
 return r
def save(path,data):
 p=Path(path);tmp=p.with_suffix(p.suffix+'.tmp')
 with tmp.open('w') as f:json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
 os.replace(tmp,p)
def tree(root):
 root=Path(root);require(root.is_dir() and not root.is_symlink(),'Missing/symlink root')
 result={}
 for p in root.rglob('*'):
  require(not p.is_symlink(),'Symlink in output tree')
  if p.is_file():result[str(p)]=bind(p)
  else:require(p.is_dir(),'Nonregular tree entry')
 return result
def unchanged(rows):
 for p,row in rows.items():require(bind(p)==row,'Bound input identity/content changed: '+p)
def project(m):return any(m==p or m.startswith(p+'.') for p in ['LightSpanners','LightEFTSpanners','LightEFTSuppliedForestStage','LightEFTSuppliedForestProbabilityStage'])
def effective(roots,expected,target_object,compiled,predicted=False):
 """Inspect each physical search root, independent of the official resolver result."""
 roots=list(map(Path,roots))
 require(len(roots)==len(set(map(str,roots))),'Duplicate configured search root')
 if predicted:require(not compiled and not roots[0].exists() and not roots[0].is_symlink(),'Predicted output root must be absent')
 physical_roots=roots[1:] if predicted else roots
 require(all(r.is_dir() and not r.is_symlink() for r in physical_roots),'Invalid search root')
 expected=dict(expected)
 for module,row in expected.items():
  suffix=Path(*module.split('.')).with_suffix('.olean')
  matches=[r/suffix for r in physical_roots if (r/suffix).exists() or (r/suffix).is_symlink()]
  require(len(matches)==1 and str(matches[0])==row['path'],'Shadow/missing/wrong effective dependency: '+module)
  bind(matches[0],row)
 matches=[];all_modules={}
 for r in physical_roots:
  prefix=r/Path(*TARGET.split('.'))
  if prefix.exists():require(not any(prefix.rglob('*')),'Target-prefix sibling directory')
  parent=prefix.parent
  if parent.exists():
   for candidate in parent.glob(prefix.name+'.*'):
    allowed={str(target_object)[:-len('.olean')]+s for s in SUFFIXES} if compiled else set()
    require(str(candidate) in allowed,'Target sidecar shadow or prefix sibling')
  for p in r.rglob('*.olean'):
   module='.'.join(p.relative_to(r).with_suffix('').parts)
   require(module not in all_modules,'Shadow copy of effective module: '+module);all_modules[module]=str(p)
   if module==TARGET or module.startswith(TARGET+'.'):matches.append((module,str(p)))
 wanted=[(TARGET,str(target_object))] if compiled else []
 require(sorted(matches)==wanted,'New target shadow/prefix sibling/missing object')
 if compiled:bind(target_object)
 from package_selection import validate
 return validate(roots,all_modules,target_object,compiled,predicted)
def resolution(path,roots,target_object):
 r,b=regular(path);j=json.loads(b)
 require(j.get('target')==TARGET and j.get('count')==1 and j.get('resolved')==[{'module':TARGET,'object':str(target_object)}],'Official resolution mismatch')
 # initSearchPath may append the already specified sysroot; duplicates of this
 # exact root do not authorize a second physical file or any extra search root.
 sp=j.get('search_path')
 require(isinstance(sp,list) and list(dict.fromkeys(sp))==list(map(str,roots)),'Official effective search path mismatch')
 return r
def object_outputs(root,target_object,complete):
 files=tree(root);base=str(target_object)[:-len('.olean')]
 allowed={base+s for s in SUFFIXES}
 require(set(files)<=allowed,'Unexpected new object/prefix sibling')
 if complete:require(str(target_object) in files,'Missing compiled new object')
 return files
def outputs(root,complete=False):
 root=Path(root);files=tree(root)
 require(set(files)<=set(str(root/n) for n in EXPORTS),'Unexpected audit output')
 if complete:require(set(files)==set(str(root/n) for n in EXPORTS),'Incomplete audit exports')
 require(all(r['bytes']<=64*1024**2 for r in files.values()) and sum(r['bytes'] for r in files.values())<=320*1024**2,'Audit file/total budget')
 return files
def warning_lines(raw):
 return re.findall(r'^(?:.*:\d+:\d+: )?(?:warning|error):.*$',raw,re.M)
