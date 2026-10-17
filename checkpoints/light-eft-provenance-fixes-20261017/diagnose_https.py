"""One ordinary same-URL request, unchanged default urllib identity/proxy/TLS.
No redirects followed, no alternate hosts or retries; capture error response bytes.
"""
from pathlib import Path
import datetime,hashlib,json,ssl,urllib.request,urllib.error
BASE=Path(__file__).resolve().parent/'evidence'
URL='https://cache.mathlib.org/mathlib4-master/f/35a94f3f050967bd.ltar'
class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs):return None
ctx=ssl.create_default_context()
opener=urllib.request.build_opener(NoRedirect,urllib.request.HTTPSHandler(context=ctx))
r={'url':URL,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'request_headers':opener.addheaders,'route':'unchanged urllib default environment proxy handling; no custom transport','hostname_verification':ctx.check_hostname,'certificate_verification':'CERT_REQUIRED','redirects_followed':False,'attempts':1,'executed':False,'extracted':False}
try:
    try:response=opener.open(URL,timeout=30)
    except urllib.error.HTTPError as error:response=error
    with response:
        r.update(status=response.status,reason=str(response.reason),final_url=response.geturl(),response_origin_url=response.geturl(),headers=list(response.headers.raw_items()))
        try:
            sock=response.fp.raw._sock
            r['peer_certificate_sha256']=hashlib.sha256(sock.getpeercert(binary_form=True)).hexdigest()
            r['peer_certificate']=sock.getpeercert()
            r['transport_peer']=sock.getpeername()
        except (AttributeError,OSError) as error:r['peer_capture_error']=repr(error)
        body=response.read()
        (BASE/'https-response-body.bin').write_bytes(body)
        headers=response.headers.as_bytes();(BASE/'https-response-headers.bin').write_bytes(headers)
        r.update(body_bytes=len(body),body_sha256=hashlib.sha256(body).hexdigest(),headers_sha256=hashlib.sha256(headers).hexdigest(),headers_representation='HTTPMessage serialization; raw ordered header name/value pairs also retained, not wire packet capture')
except Exception as error:r['error']=repr(error)
(BASE/'https-diagnostic-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
