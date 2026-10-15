from pathlib import Path
import hashlib,json,tarfile,subprocess,os,datetime,urllib.request
here=Path(__file__).resolve().parent;root=Path('/workspace/toolchains');installed=root/'lean-4.34.0-linux';archive=root/'lean.tar.zst'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1048576):h.update(b)
 return h.hexdigest()
def runtime():
 result={'timestamp_utc':now(),'relevant_environment':{k:os.environ.get(k) for k in ['LD_PRELOAD','LD_LIBRARY_PATH','LEAN_SYSROOT','LEAN_PATH']},'elan_toolchain_link':os.readlink('/workspace/toolchains/elan/toolchains/leanprover--lean4---v4.34.0'),'processes':subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True),'binaries':{}}
 for n in ['lean','lake','leanchecker']:
  p=installed/'bin'/n;result['binaries'][n]={'path':str(p),'sha256':digest(p)}
 for n in ['lean','lake']:
  p=subprocess.run([str(installed/'bin'/n),'--version'],text=True,capture_output=True);result[n+'_version']={'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
 return result
start=now();pre=runtime();(here/'runtime-pre.json').write_text(json.dumps(pre,indent=2)+'\n')
archive_hash=digest(archive);(here/'archive-identity.json').write_text(json.dumps({'path':str(archive),'bytes':archive.stat().st_size,'sha256':archive_hash,'recorded_download_url':'https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-linux.tar.zst','provenance':'Saved prepare-paper-environment.sh downloads this official GitHub release asset to this path; retained archive used in the original setup. Independently querying official release metadata below.'},indent=2)+'\n')
# Read-only provenance query; failure is retained and never silently treated as authentication.
try:
 req=urllib.request.Request('https://api.github.com/repos/leanprover/lean4/releases/tags/v4.34.0',headers={'User-Agent':'Codex-toolchain-verification','Accept':'application/vnd.github+json'})
 with urllib.request.urlopen(req,timeout=30) as response:raw=response.read()
 (here/'official-release-metadata.json').write_bytes(raw)
 obj=json.loads(raw);asset=next(a for a in obj['assets'] if a['name']=='lean-4.34.0-linux.tar.zst')
 provenance={'query_time_utc':now(),'asset_id':asset['id'],'name':asset['name'],'size':asset['size'],'browser_download_url':asset['browser_download_url'],'official_digest':asset.get('digest'),'local_sha256':archive_hash,'size_match':asset['size']==archive.stat().st_size,'digest_match':asset.get('digest')=='sha256:'+archive_hash}
except Exception as e:provenance={'query_time_utc':now(),'error':str(e),'official_digest_verified':False}
(here/'archive-provenance-result.json').write_text(json.dumps(provenance,indent=2)+'\n')
expected=set();mismatch=[];regular=0;links=0
p=subprocess.Popen(['zstd','-dc',str(archive)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
with (here/'toolchain-file-comparison.tsv').open('w') as log:
 log.write('path\tkind\tarchive_bytes\tinstalled_bytes\tarchive_sha256_or_link\tinstalled_sha256_or_link\tresult\n')
 with tarfile.open(fileobj=p.stdout,mode='r|') as t:
  for m in t:
   rel=Path(m.name);assert not rel.is_absolute() and '..' not in rel.parts
   q=root/rel; expected.add(str(q));
   if m.isfile():
    regular+=1;h=hashlib.sha256();f=t.extractfile(m)
    while b:=f.read(1048576):h.update(b)
    a=h.hexdigest();b=digest(q) if q.is_file() and not q.is_symlink() else 'MISSING_OR_WRONG_TYPE';sz=q.stat().st_size if q.exists() else -1;ok=a==b and m.size==sz
    log.write(f'{m.name}\tregular\t{m.size}\t{sz}\t{a}\t{b}\t'+('MATCH' if ok else 'MISMATCH')+'\n')
    if not ok:mismatch.append(m.name)
   elif m.issym():
    links+=1;b=os.readlink(q) if q.is_symlink() else 'MISSING_OR_WRONG_TYPE';ok=b==m.linkname;log.write(f'{m.name}\tsymlink\t0\t0\t{m.linkname}\t{b}\t'+('MATCH' if ok else 'MISMATCH')+'\n')
    if not ok:mismatch.append(m.name)
   elif m.isdir():
    if not q.is_dir():mismatch.append(m.name)
   else: mismatch.append('UNHANDLED_ARCHIVE_ENTRY:'+m.name)
err=p.stderr.read().decode();rc=p.wait();extras=[str(q) for q in installed.rglob('*') if str(q) not in expected];post=runtime();(here/'runtime-post.json').write_text(json.dumps(post,indent=2)+'\n')
result={'started_utc':start,'finished_utc':now(),'new_comparison_not_original_receipt':True,'regular_files_compared':regular,'symlinks_compared':links,'mismatches':mismatch,'extra_installed_paths':extras,'zstd_exit':rc,'zstd_stderr':err,'archive_sha256_before':archive_hash,'archive_sha256_after':digest(archive),'runtime_binary_hashes_unchanged':pre['binaries']==post['binaries'],'official_asset_metadata':provenance,'result':'PASS' if regular==17738 and not mismatch and not extras and rc==0 and pre['binaries']==post['binaries'] else 'FAIL'}
(here/'toolchain-comparison-result.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2),flush=True)
raise SystemExit(0 if result['result']=='PASS' else 1)
