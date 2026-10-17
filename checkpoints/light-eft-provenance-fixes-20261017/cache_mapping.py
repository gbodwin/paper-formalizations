"""Unreviewed Python-only cache mapping candidate. No Lean/runtime/FFI execution.
Hash rules translated from pinned Lean lean.h/hash.cpp and mathlib Cache/Hashing.lean.
Only simple ASCII module identifiers are supported; unsupported headers refuse.
This prepares an independently reviewable map; it does not enable the gate.
"""
from pathlib import Path
import hashlib,json,re,sys
M=0xc6a4a7935bd1e995
MASK=(1<<64)-1
CACHE_ROOTS=set('Mathlib Batteries BatteriesRecycling Aesop Cli ImportGraph LeanSearchClient Plausible Qq ProofWidgets Archive Counterexamples Wanted MathlibTest Requests OpenAIClient Reap Canonical Duper Auto PremiseSelection Hammer'.split())

def mix(h,k):
    k=(k*M)&MASK;k^=k>>47;k^=M
    return ((h^k)*M)&MASK

def hash_list(values):
    h=7
    for value in values:h=mix(h,value)
    return h

def string_hash(text):
    data=text.encode('utf-8');h=(11^(len(data)*M))&MASK
    for i in range(0,len(data)//8*8,8):
        k=(int.from_bytes(data[i:i+8],'little')*M)&MASK;k^=k>>47;k=(k*M)&MASK
        h=((h^k)*M)&MASK
    tail=data[len(data)//8*8:]
    if tail:h=((h^int.from_bytes(tail,'little'))*M)&MASK
    h^=h>>47;h=(h*M)&MASK;h^=h>>47
    return h

def canonical_hash(data):return string_hash(data.decode('utf-8').replace('\r\n','\n'))

def lean_char_is_whitespace(c):
    """Pinned Init/Data/Char/Basic.lean: exactly these four characters."""
    return c in (' ', '\t', '\r', '\n')

def imports(text):
    if text.startswith('\ufeff'):raise ValueError('Unsupported BOM header')
    pos=0;result=[]
    def whitespace():
        nonlocal pos
        while pos<len(text):
            if text[pos]=='\t':raise ValueError('Tab in module header')
            if lean_char_is_whitespace(text[pos]):pos+=1;continue
            # Restricted ASCII header dialect: refuse unsupported controls and
            # non-ASCII token-boundary characters, never treat them as spacing.
            # Comment contents are consumed below and are not token boundaries.
            if ord(text[pos]) < 32 or ord(text[pos]) >= 127:
                raise ValueError('Unsupported header boundary U+%04X' % ord(text[pos]))
            if text.startswith('--',pos):
                end=text.find('\n',pos);pos=len(text) if end<0 else end+1;continue
            if text.startswith('/-',pos) and not text.startswith(('/--','/-!'),pos):
                pos+=2;level=1
                while level:
                    if pos>=len(text):raise ValueError('Unterminated comment')
                    if text.startswith('/-',pos):level+=1;pos+=2
                    elif text.startswith('-/',pos):level-=1;pos+=2
                    else:pos+=1
                continue
            break
    def keyword(word):
        nonlocal pos
        if text.startswith(word,pos):pos+=len(word);whitespace();return True
        return False
    whitespace();module=keyword('module');keyword('prelude')
    while True:
        begin=pos;public=keyword('public');meta=keyword('meta')
        if not keyword('import'):pos=begin;break
        all_=keyword('all')
        if (public or meta or all_) and not module:raise ValueError('Modifier without module')
        found=re.match(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*",text[pos:])
        if not found:raise ValueError('Unsupported module identifier')
        name=found[0];pos+=len(name)
        if pos<len(text) and (ord(text[pos])>127 or text[pos] in '.«»'):
            raise ValueError('Unsupported module identifier continuation')
        result.append(name);whitespace()
    return result

def derive(repo,packages):
    repo=Path(repo);packages=Path(packages)
    pins=json.loads((repo/'lake-manifest.json').read_text())['packages']
    bases=[(p['name'],packages/p['name']) for p in pins]
    mathlib=packages/'mathlib';root_files=['lakefile.lean','lean-toolchain','lake-manifest.json']
    roots=[dict(path=str(mathlib/n),sha256=hashlib.sha256((mathlib/n).read_bytes()).hexdigest(),canonical_hash=f'{canonical_hash((mathlib/n).read_bytes()):016x}') for n in root_files]
    root=hash_list([5]+[int(x['canonical_hash'],16) for x in roots]);rows={};visiting=set()
    def visit(name):
        if name in rows:return int(rows[name]['cache_key'],16)
        if name in visiting:raise ValueError('Dependency cycle '+name)
        visiting.add(name);relative=Path(*name.split('.')).with_suffix('.lean')
        candidates=[(pkg,base/relative) for pkg,base in bases if (base/relative).is_file()]
        if len(candidates)!=1:raise ValueError('Missing/ambiguous dependency '+name)
        pkg,path=candidates[0];raw=path.read_bytes();deps=[n for n in imports(raw.decode('utf-8')) if n.split('.')[0] in CACHE_ROOTS]
        dep_hashes=[visit(n) for n in deps]
        path_hash=hash_list(string_hash(c) for c in relative.parts)
        key=hash_list([root,path_hash,canonical_hash(raw),*dep_hashes])
        rows[name]=dict(module=name,package=pkg,path=str(path),source_sha256=hashlib.sha256(raw).hexdigest(),imports=deps,import_keys=[f'{h:016x}' for h in dep_hashes],path_hash=f'{path_hash:016x}',content_hash=f'{canonical_hash(raw):016x}',cache_key=f'{key:016x}',official_url=f'https://cache.mathlib.org/mathlib4-master/f/{key:016x}.ltar')
        visiting.remove(name);return key
    plan=json.loads((repo/'checkpoints/light-eft-clean-gate-preparation-20261017/source-plan.json').read_text())
    project=set(row['module'] for row in plan['modules']);direct=set()
    for row in plan['modules']:
        raw=(repo/row['path']).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=row['sha256']:raise ValueError('Frozen project source changed')
        for name in imports(raw.decode('utf-8')):
            if name in project:continue
            if name.split('.')[0] in CACHE_ROOTS:direct.add(name)
            elif name.split('.')[0] not in ['Init','Lean','Std']:raise ValueError('Unmapped project import '+name)
    for name in sorted(direct):visit(name)
    return dict(status='UNREVIEWED_PYTHON_MAPPING_NO_EXTRACTION',source=plan['source'],root_generation=5,root_files=roots,root_hash=f'{root:016x}',direct_dependency_roots=sorted(direct),pins={p['name']:p['rev'] for p in pins},modules=list(rows.values()),lean_executions=0)

if __name__=='__main__':
    result=derive(sys.argv[1],sys.argv[2]);Path(sys.argv[3]).write_text(json.dumps(result,indent=2)+'\n')
    print('Prepared dependency mapping:',len(result['modules']),'root',result['root_hash'])
