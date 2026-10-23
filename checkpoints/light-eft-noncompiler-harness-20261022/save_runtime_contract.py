"""Fail-closed, in-child stdlib identity/semantics admission; never run at source review.
Reference AST pins alone do not attest a hosted interpreter. No alternate profile.
"""
import ast,builtins,hashlib,inspect,json,math,os,sys,types
from pathlib import Path

def need(ok,why):
 if not ok:raise RuntimeError('Save runtime contract: '+why)

def normal(node):
 if isinstance(node,ast.AST):
  fields=[]
  for key,value in ast.iter_fields(node):
   if key=='type_params' and not value:continue
   if key=='body' and isinstance(value,list) and value and isinstance(value[0],ast.Expr) and isinstance(value[0].value,ast.Constant) and isinstance(value[0].value.value,str):value=value[1:]
   fields.append((key,normal(value)))
  return type(node).__name__,tuple(fields)
 if isinstance(node,list):return tuple(normal(x) for x in node)
 return node

def sha(data):return hashlib.sha256(data).hexdigest()

def code_signature(c):
 def const(x):
  if isinstance(x,types.CodeType):return code_signature(x)
  if isinstance(x,tuple):return ('tuple',tuple(const(y) for y in x))
  return type(x).__name__,repr(x)
 return tuple((name,const(getattr(c,name))) for name in (
  'co_argcount','co_posonlyargcount','co_kwonlyargcount','co_nlocals','co_stacksize',
  'co_flags','co_code','co_consts','co_names','co_varnames','co_filename','co_name',
  'co_qualname','co_firstlineno','co_linetable','co_exceptiontable','co_freevars','co_cellvars'))

def codes(c):
 yield c
 for x in c.co_consts:
  if isinstance(x,types.CodeType):yield from codes(x)

class Contract:
 def __init__(self,pins,root,contracts,source_bytes):
  self.pins=pins;self.root=root;self.contracts=contracts;self.source_bytes=source_bytes
  self.first=self.capture(save_sources=True)
 def capture(self,save_sources=False):
  import _json
  encoder=json.encoder
  need(sys.implementation.name=='cpython' and list(sys.version_info[:2]) in self.pins['accepted_cpython_minors'],'unreviewed interpreter')
  need(sys.flags.isolated==1 and sys.dont_write_bytecode and sys.flags.optimize==0,'interpreter flags')
  need(inspect.isfunction(json.dump) and json.JSONEncoder is encoder.JSONEncoder and type(encoder.JSONEncoder) is type,'dump/encoder linkage')
  need(encoder.JSONEncoder.__bases__==(object,),'encoder bases')
  for module in (json,encoder):
   need(module.__dict__.get('__builtins__') is vars(builtins),'stdlib builtins authority')
   for name in ('ValueError','TypeError','dict','float','id','int','isinstance','list','str','tuple','object','super'):
    need(name not in module.__dict__,'shadowed stdlib builtin '+name)
  sources={};asts={};compiled={};total=self.source_bytes
  for label,module in [('json',json),('encoder',encoder)]:
   path=Path(module.__file__).resolve()
   need(path.suffix=='.py','stdlib source unavailable')
   row,data=self.contracts.regular(path)
   need(row['bytes']<=65536,'stdlib source length')
   total+=len(data);sources[label]=dict(path=str(path),bytes=len(data),sha256=sha(data))
   asts[label]=ast.parse(data,filename=str(path))
   # Compile for code comparison ONLY; never execute the stdlib source again.
   compiled[label]={c.co_qualname:c for c in codes(compile(data,str(path),'exec',dont_inherit=True,optimize=0))}
   if save_sources:
    fd=os.open(self.root/(label+'.py'),os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
    with os.fdopen(fd,'wb') as f:f.write(data);f.flush();os.fsync(f.fileno())
  need(total<=2*1024**2,'actual stdlib text exceeds existing source cap')
  nodes={n.name:n for n in asts['json'].body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
  enodes={n.name:n for n in asts['encoder'].body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
  fingerprints={key:sha(repr(normal(node)).encode()) for key,node in [('dump',nodes['dump']),('JSONEncoder',enodes['JSONEncoder']),('_make_iterencode',enodes['_make_iterencode'])]}
  need(any(fingerprints==p['components'] for p in self.pins['profiles']),'actual semantic AST differs from reviewed profile')
  functions=[('json',json.dump),('encoder',encoder._make_iterencode)]
  functions += [('encoder',getattr(encoder.JSONEncoder,n)) for n in ['__init__','default','encode','iterencode']]
  identities=[]
  for label,fn in functions:
   module=json if label=='json' else encoder
   need(inspect.isfunction(fn) and fn.__globals__ is module.__dict__,'function globals')
   need(fn.__qualname__ in compiled[label] and code_signature(fn.__code__)==code_signature(compiled[label][fn.__qualname__]),'loaded code not equal to actual source: '+fn.__qualname__)
   need(fn.__closure__ is None,'unexpected stdlib closure')
   identities.append([fn.__qualname__,id(fn),id(fn.__code__)])
  defaults=dict(skipkeys=False,ensure_ascii=True,check_circular=True,allow_nan=True,sort_keys=False,indent=None,separators=None,default=None)
  def exact_defaults(actual,wanted):
   return type(actual) is dict and actual.keys()==wanted.keys() and all(actual[k] is v for k,v in wanted.items())
  need(exact_defaults(json.dump.__kwdefaults__,dict(defaults,cls=None)) and json.dump.__defaults__ is None,'dump defaults')
  need(exact_defaults(encoder.JSONEncoder.__init__.__kwdefaults__,defaults),'encoder defaults')
  need(type(encoder.JSONEncoder.iterencode.__defaults__) is tuple and len(encoder.JSONEncoder.iterencode.__defaults__)==1 and encoder.JSONEncoder.iterencode.__defaults__[0] is False,'iterencode defaults')
  need(encoder._make_iterencode.__defaults__==(ValueError,dict,float,id,int,isinstance,list,str,tuple,int.__repr__),'iterator builtin bindings')
  need(json.dump.__globals__['JSONEncoder'] is encoder.JSONEncoder,'dump class global')
  need(encoder.encode_basestring_ascii is _json.encode_basestring_ascii and isinstance(_json.encode_basestring_ascii,types.BuiltinFunctionType),'string encoder binding')
  need(encoder.JSONEncoder.item_separator==', ' and encoder.JSONEncoder.key_separator==': ' and math.isinf(encoder.INFINITY) and encoder.INFINITY>0,'encoder constants')
  # The reviewed AST has these exact class attributes and four methods.
  need(set(vars(encoder.JSONEncoder))=={'__module__','__doc__','item_separator','key_separator','__init__','default','encode','iterencode','__dict__','__weakref__'},'encoder class additions')
  extension=Path(_json.__file__).resolve() if getattr(_json,'__file__',None) else Path(sys.executable).resolve()
  erow,_=self.contracts.regular(extension)
  xrow,_=self.contracts.regular(Path(sys.executable).resolve())
  return dict(interpreter=sys.version,implementation=sys.implementation.name,cache_tag=sys.implementation.cache_tag,
   executable=dict(path=str(Path(sys.executable).resolve()),binding=xrow),source_text=sources,
   extension=dict(path=str(extension),binding=erow),semantic_AST=fingerprints,identities=identities,
   source_bytes_including_actual_stdlib=total,scope='Loaded Python code equals actual source and pinned AST; same actual C string encoder, not a CPython binary semantics proof')
 def finish(self):
  need(self.capture()==self.first,'stdlib/interpreter contract changed during trials')
  # IDs remain private implementation evidence, not portable identities.
  return self.first
