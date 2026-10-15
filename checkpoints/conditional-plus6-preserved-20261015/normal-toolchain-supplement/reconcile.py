from pathlib import Path
import hashlib,json,csv,io
here=Path(__file__).resolve().parent; old=here.parent/'normal-toolchain-evidence'; data=(old/'recursive-dependencies.tsv').read_bytes(); lines=data.splitlines(keepends=True)
chunks=here/'dependency-chunks'; chunks.mkdir(exist_ok=True)
manifest=[]; start=0
# Raw contiguous line blocks: only chunk 1 has the original header. Concatenation is byte exact.
for i in range(0,len(lines),400):
 b=b''.join(lines[i:i+400]); name=f'part-{len(manifest)+1:03}.tsv'; (chunks/name).write_bytes(b)
 manifest.append({'path':'dependency-chunks/'+name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'first_original_line':i+1,'last_original_line':i+len(b.splitlines()),'data_rows':len(b.splitlines())-(1 if i==0 else 0),'has_header':i==0})
rebuilt=b''.join((here/m['path']).read_bytes() for m in manifest); assert rebuilt==data
rows=list(csv.DictReader(io.StringIO(data.decode()),delimiter='\t')); inv=list(csv.DictReader((old/'actual-owner-inventory.tsv').open(),delimiter='\t'))
byname={r['name']:r for r in rows}; assert len(byname)==len(rows)==19215
rootnames={r['name'] for r in inv}; assert len(rootnames)==len(inv)==241
assert rootnames<=byname.keys()
root_owner_mismatch=[n for n in rootnames if byname[n]['owner']!=next(r['owner'] for r in inv if r['name']==n)];assert not root_owner_mismatch
opaque=[r for r in rows if r['kind']=='opaque'];assert len(opaque)==14
edges={n:set(filter(None,(r['typeDependencies']+','+r['bodyDependencies']).split(','))) for n,r in byname.items()}
missing=sorted(set().union(*edges.values())-byname.keys());assert not missing
seen=set();todo=list(rootnames)
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(edges[n]-seen)
assert seen==set(byname)
summary={'original_path':'../normal-toolchain-evidence/recursive-dependencies.tsv','original_bytes':len(data),'original_sha256':hashlib.sha256(data).hexdigest(),'original_lines_including_header':len(lines),'data_rows':len(rows),'unique_names':len(byname),'inventory_roots':len(rootnames),'roots_present':len(rootnames & byname.keys()),'root_owner_mismatches':root_owner_mismatch,'opaque_rows':len(opaque),'opaque_with_nonempty_body_dependencies':sum(bool(r['bodyDependencies']) for r in opaque),'missing_dependency_names':missing,'reachable_from_roots':len(seen),'unreachable_rows':0,'byte_exact_reconstruction':True,'chunks':manifest}
(here/'dependency-manifest.json').write_text(json.dumps(summary,indent=2)+'\n')
with (here/'opaque-body-coverage.tsv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=rows[0].keys(),delimiter='\t');w.writeheader();w.writerows(opaque)
(here/'root-reconciliation.tsv').write_text('name\towner\tpresent_in_recursive_rows\n'+''.join(f"{r['name']}\t{r['owner']}\ttrue\n" for r in inv))
print(json.dumps({k:v for k,v in summary.items() if k!='chunks'},indent=2)); print('chunks',len(manifest))
