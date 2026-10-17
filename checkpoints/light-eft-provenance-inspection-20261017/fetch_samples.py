"""Read-only HTTPS provenance samples. Downloads bytes; never extracts or executes."""
from pathlib import Path
import datetime,hashlib,json,ssl,urllib.request

BASE=Path(__file__).resolve().parent
ctx=ssl.create_default_context()

def fetch(url,path):
    receipt=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),hostname_verification=ctx.check_hostname,certificate_verification='CERT_REQUIRED',executed=False,extracted=False)
    try:
        with urllib.request.urlopen(url,context=ctx,timeout=30) as response:
            receipt.update(final_url=response.geturl(),status=response.status,headers=dict(response.headers))
            if not receipt['final_url'].startswith('https://'):raise RuntimeError('HTTPS required')
            try:receipt['peer_certificate_sha256']=hashlib.sha256(response.fp.raw._sock.getpeercert(binary_form=True)).hexdigest()
            except AttributeError:receipt['peer_certificate_sha256']=None
            with path.open('xb') as output:
                while chunk:=response.read(1024*1024):output.write(chunk)
        receipt.update(bytes=path.stat().st_size,sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    except Exception as exc:receipt['error']=repr(exc)
    return receipt

if __name__=='__main__':
    mapping=json.loads((BASE/'evidence/dependency-map.json').read_text())
    selected=[]
    for package in ['aesop','mathlib','Qq']:
        selected.append(next(row for row in mapping['modules'] if row['package']==package))
    target=BASE/'evidence/https-samples';target.mkdir(exist_ok=True)
    receipts=[]
    for row in selected:
        result=fetch(row['official_url'],target/(row['cache_key']+'.ltar'))
        result.update(module=row['module'],source_sha256=row['source_sha256'],cache_key=row['cache_key'])
        receipts.append(result);print(json.dumps(result),flush=True)
        (BASE/'evidence/https-sample-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
        if 'error' in result:break
