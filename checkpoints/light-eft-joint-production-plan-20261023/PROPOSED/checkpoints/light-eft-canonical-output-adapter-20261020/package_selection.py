"""Model pinned Lean SearchPath.findWithExt for ext=olean, plus strict checks.

Selection uses the first top-level package marker, never a missing-leaf fallback.
Predicted layout overlays only the planned target directory/object; no writes.
"""
from pathlib import Path
import stat
from contracts import require,TARGET
def exists(path):return Path(path).exists() or Path(path).is_symlink()
def _selected_root(roots,package,predicted_dirs=(),predicted_files=()):
 dirs=set(map(str,predicted_dirs));files=set(map(str,predicted_files))
 for root in map(Path,roots):
  directory=root/package;marker=root/(package+'.olean')
  for p in [directory,marker]:
   if exists(p):require(not p.is_symlink(),'Symlink package marker')
  # Lean checks directory first OR root .olean pathExists, then constructs the
  # entire leaf path. It does not continue if that leaf is absent.
  if str(directory) in dirs or directory.is_dir() or str(marker) in files or marker.exists():
   return root
 return None
def selected_path(roots,module,predicted_dirs=(),predicted_files=()):
 parts=module.split('.');require(parts and all(parts),'Invalid package/module name')
 root=_selected_root(roots,parts[0],predicted_dirs,predicted_files)
 return None if root is None else root/Path(*parts).with_suffix('.olean')
def validate(roots,physical_modules,target,compiled,predicted=False):
 roots=list(map(Path,roots));target=Path(target);dirs=[];files=[]
 if predicted:
  require(not compiled and target.is_relative_to(roots[0]),'Invalid predicted target layout')
  dirs=[roots[0]/TARGET.split('.')[0]];files=[target]
 expected={m:Path(p) for m,p in physical_modules.items()}
 require(TARGET not in expected or expected[TARGET]==target,'Physical target differs')
 expected[TARGET]=target
 selected={};package_roots={}
 for module,path in expected.items():
  parts=module.split('.');require(parts and all(parts),'Invalid package/module name')
  package=parts[0]
  # Only this validation call's immutable package-marker decision is reused.
  # Every module/path/leaf comparison below still runs; no audit/checker result
  # or content verification is cached, and no state survives this call.
  if package not in package_roots:
   package_roots[package]=_selected_root(roots,package,dirs,files)
  root=package_roots[package]
  actual=None if root is None else root/Path(*parts).with_suffix('.olean')
  require(actual==path,'Package selection masks/wrong root: '+module+' -> '+str(actual)+'; expected '+str(path))
  if module!=TARGET or compiled:
   require(path.is_file() and not path.is_symlink(),'Selected package leaf missing/nonregular: '+module)
  selected[module]=str(actual)
 # The input/no-writer contract is still required. Revisit every used package
 # before return; persistent selection/symlink changes fail closed.
 for package,root in package_roots.items():
  require(_selected_root(roots,package,dirs,files)==root,'Package marker selection changed during validation')
 return {'model':'Lean SearchPath.findWithExt olean; first top-level marker; no leaf fallback','predicted':predicted,'selected':selected}
