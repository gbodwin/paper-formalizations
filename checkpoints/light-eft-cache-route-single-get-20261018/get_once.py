"""One ordinary unchanged urllib GET. No redirect, retry, alternate route or extraction."""
from pathlib import Path
import datetime, hashlib, json, os, signal, ssl, stat, sys, time, traceback, urllib.error, urllib.request, uuid

A=Path(__file__).resolve().parent
R=A.parents[1]
URL='https://cache.mathlib.org/mathlib4-master/f/35a94f3f050967bd.ltar'
READ_LIMIT=1024**2
SOCKET_TIMEOUT=30
WALL_LIMIT=45


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs):return None


def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    # Match the prior ordinary urllib request identity, default ProxyHandler,
    # HTTPSHandler and trust store. No proxy/header/TLS environment is changed.
    ctx=ssl.create_default_context()
    assert ctx.check_hostname and ctx.verify_mode==ssl.CERT_REQUIRED
    opener=urllib.request.build_opener(NoRedirect,urllib.request.HTTPSHandler(context=ctx))
    assert opener.addheaders==[('User-agent','Python-urllib/3.12')]
    with (A/'request-invocation-claimed.json').open('x') as f:
        json.dump({'utc':utc(),'url':URL,'one_GET_attempt_only':True,'no_retry':True},f)
    folder=A/'attempts'/uuid.uuid4().hex;folder.mkdir(parents=True,exist_ok=False)
    receipt={'attempt_id':folder.name,'created_utc':utc(),'started_ns':time.monotonic_ns(),
        'pid':os.getpid(),'source_sha256':sha(Path(__file__)),'url':URL,'method':'GET',
        'request_headers':opener.addheaders,'route':'unchanged urllib default environment proxy handling; no custom transport',
        'handler_classes':[type(h).__name__ for h in opener.handlers],
        'hostname_verification':ctx.check_hostname,'certificate_verification':'CERT_REQUIRED',
        'TLS_context':'ssl.create_default_context; existing trust store/environment unchanged',
        'socket_timeout_seconds':SOCKET_TIMEOUT,'overall_wall_limit_seconds':WALL_LIMIT,
        'response_body_accept_limit':READ_LIMIT,'maximum_retained_body_bytes':READ_LIMIT+1,
        'overflow_detection':'Retain at most one overflow byte, then stop incomplete',
        'redirects_followed':False,'automatic_retries':0,
        'open_invocations':0,'request_attempted':False,'response_complete':False,
        'candidate_compared':False,'extracted':False,'archive_executed':False,
        'Lean_build_checker_or_audit_invocations':0,'response_representation':'HTTP library entity body; ordered parsed headers and HTTPMessage serialization, not wire packet capture'}
    path=folder/'receipt.json'
    def save():path.write_text(json.dumps(receipt,indent=2)+'\n')
    save()
    def expired(sig,frame):raise TimeoutError('One-request overall45second wall bound reached')
    old=signal.signal(signal.SIGALRM,expired)
    received=0;digest=hashlib.sha256();eof=False;framing_ok=True;limit_hit=False
    try:
        receipt.update(request_started_utc=utc(),request_started_ns=time.monotonic_ns(),
                       request_attempted=True,open_invocations=1)
        save();signal.setitimer(signal.ITIMER_REAL,WALL_LIMIT)
        try:response=opener.open(URL,timeout=SOCKET_TIMEOUT)
        except urllib.error.HTTPError as error:response=error
        with response:
            receipt.update(status=response.status,reason=str(response.reason),final_url=response.geturl(),
                ordered_response_headers=list(response.headers.raw_items()))
            header_bytes=response.headers.as_bytes()
            (folder/'response-headers.bin').write_bytes(header_bytes)
            receipt.update(headers_bytes=len(header_bytes),headers_sha256=hashlib.sha256(header_bytes).hexdigest())
            # This matches the previous helper's best-effort interface exactly.
            # Failure is retained; no extra connection or transport is attempted.
            try:
                sock=response.fp.raw._sock
                receipt['peer_certificate_sha256']=hashlib.sha256(sock.getpeercert(binary_form=True)).hexdigest()
                receipt['peer_certificate']=sock.getpeercert();receipt['transport_peer']=sock.getpeername()
            except Exception as error:receipt['peer_capture_limitation']=repr(error)
            lengths=response.headers.get_all('Content-Length',[])
            receipt['content_length_headers']=lengths
            declared=[]
            try:
                for value in lengths:
                    for item in value.split(','):
                        if not item.strip().isdecimal():raise ValueError('Invalid Content-Length')
                        declared.append(int(item.strip()))
                if len(set(declared))>1:raise ValueError('Conflicting Content-Length headers')
            except ValueError as error:
                framing_ok=False;receipt['framing_limitation']=repr(error)
            transfer=response.headers.get_all('Transfer-Encoding',[])
            receipt['transfer_encoding_headers']=transfer
            if transfer and declared:
                framing_ok=False;receipt['framing_limitation']='Both Transfer-Encoding and Content-Length present; fail closed'
            receipt['declared_body_bytes']=declared[0] if declared else None
            save()
            with (folder/'response-body.bin').open('xb') as output:
                while received<=READ_LIMIT:
                    chunk=response.read(min(64*1024,READ_LIMIT+1-received))
                    if not chunk:eof=True;break
                    output.write(chunk);digest.update(chunk);received+=len(chunk)
                    if received>READ_LIMIT:limit_hit=True;break
                output.flush();os.fsync(output.fileno())
            receipt['observed_EOF']=eof
            if declared and received!=declared[0]:
                framing_ok=False;receipt['framing_limitation']='Actual response bytes differ from declared Content-Length'
            receipt['response_complete']=bool(eof and framing_ok and not limit_hit)
            receipt['completeness_basis']='Observed library EOF, no read failure/limit, and matching Content-Length when supplied'
    except BaseException as error:
        receipt['transport_or_read_error']=repr(error)
        (folder/'transport-error.log').write_text(traceback.format_exc())
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,old)
        receipt.update(body_bytes=received,body_sha256=digest.hexdigest(),body_limit_exceeded=limit_hit,
                       response_finished_utc=utc(),response_finished_ns=time.monotonic_ns())
        body=folder/'response-body.bin';receipt['body_file_present']=body.exists()
        if body.exists():
            receipt['body_bytes']=body.stat().st_size;receipt['body_sha256']=sha(body)
            if receipt['body_bytes']!=received:
                receipt['response_complete']=False;receipt['retained_body_limitation']='Retained file length differs from successfully read/written byte count'
        else:
            receipt['body_bytes']=None;receipt['body_sha256']=None
        save()
    # Stop on any denial/redirect/incomplete response. Only this one complete
    # successful response may trigger comparison against the bound candidate.
    status=receipt.get('status')
    if status is not None and 300<=status<400:receipt['outcome']='REDIRECT_STOPPED'
    elif status is not None and not 200<=status<300:receipt['outcome']='HTTP_DENIAL_OR_FAILURE_STOPPED'
    elif not receipt['response_complete']:receipt['outcome']='TRANSPORT_OR_INCOMPLETE_RESPONSE_STOPPED'
    elif receipt.get('final_url')!=URL:receipt['outcome']='UNEXPECTED_FINAL_URL_STOPPED'
    else:
        try:
            binding=json.loads((A/'bound-candidate.json').read_text());authority=binding['authority']
            source=R/authority['repository_path']
            if source.stat().st_size!=authority['bytes'] or sha(source)!=authority['sha256']:
                raise RuntimeError('Bound candidate inventory authority changed')
            row=binding['archive'];candidate=Path(row['local_archive'])
            if row['official_url']!=URL or row['cache_key']!='35a94f3f050967bd':raise RuntimeError('Candidate scope differs')
            fd=os.open(candidate,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
            with os.fdopen(fd,'rb') as stream:
                before=os.fstat(stream.fileno())
                if not stat.S_ISREG(before.st_mode):raise RuntimeError('Bound candidate is not a regular file')
                data=stream.read();after=os.fstat(stream.fileno())
            signature=lambda s:[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
            if signature(before)!=signature(after):raise RuntimeError('Candidate changed during read')
            value=hashlib.sha256(data).hexdigest()
            if len(data)!=row['bytes'] or value!=row['sha256']:raise RuntimeError('Local candidate differs from bound inventory')
            receipt.update(candidate_compared=True,candidate_bytes=len(data),candidate_sha256=value,
                candidate_identity=signature(after),response_matches_bound_candidate=data==(folder/'response-body.bin').read_bytes())
            receipt['outcome']='ONE_ARCHIVE_RETRIEVABLE_AND_MATCHING' if receipt['response_matches_bound_candidate'] else 'SUCCESSFUL_RESPONSE_CANDIDATE_MISMATCH_STOPPED'
        except Exception as error:
            receipt['candidate_comparison_error']=repr(error);receipt['outcome']='CANDIDATE_COMPARISON_REFUSED_STOPPED'
    receipt.update(ended_utc=utc(),ended_ns=time.monotonic_ns(),retrieval_scope='One archive only; no extraction or wider authentication')
    save();print(json.dumps(receipt,indent=2))
    return 0 if receipt['outcome']=='ONE_ARCHIVE_RETRIEVABLE_AND_MATCHING' else 1


if __name__=='__main__':raise SystemExit(main())
