"""Offline bounded bridge diagnostics; never establishes child/audit acceptance."""
import json,re,sys
from port import PHASES
PREFIX='BRIDGE-AUDIT-TIMING: '
MAX_CLOCK=2**64-1
MAX_BYTES=sum(len(f'{PREFIX}phase={p} mono-ms-mod64={MAX_CLOCK}\n'.encode()) for p in PHASES)
BOUND=2048
assert MAX_BYTES<=BOUND
def summarize(raw):
    found=[];bytes_seen=0
    for line in raw.splitlines(keepends=True):
        if not line.startswith(PREFIX):continue
        match=re.fullmatch(r'BRIDGE-AUDIT-TIMING: phase=([a-z-]+) mono-ms-mod64=([0-9]{1,20})\n',line)
        if match is None:raise ValueError('Malformed/truncated bridge timing marker')
        phase,number=match.groups();clock=int(number)
        if clock>MAX_CLOCK or len(found)>=len(PHASES) or phase!=PHASES[len(found)]:
            raise ValueError('Unknown/duplicate/reordered/oversize bridge timing marker')
        bytes_seen+=len(line.encode())
        if bytes_seen>BOUND:raise ValueError('Bridge timing marker byte budget exceeded')
        found.append((phase,clock))
    decreases=any(a[1]>b[1] for a,b in zip(found,found[1:]))
    intervals=[dict(after=a[0],before=b[0],elapsed_ms=None if decreases else b[1]-a[1]) for a,b in zip(found,found[1:])]
    last=found[-1][0] if found else None;next_phase=PHASES[len(found)] if len(found)<len(PHASES) else None
    return dict(diagnostic_only=True,audit_acceptance_established=False,marker_count=len(found),
        complete_marker_sequence=len(found)==len(PHASES),last_phase=last,next_phase=next_phase,
        open_interval=('startup/imports/first run_cmd elaboration before frontend-ready' if not found else
          f'after {last}; before {next_phase}' if next_phase else 'after strict-checks-complete; final PASS/exit/cleanup still require receipts'),
        clock_status='decreased; wrap or inconsistent log: elapsed unverified' if decreases else 'nondecreasing observed modulo2^64 milliseconds',
        intervals=intervals,marker_bytes=bytes_seen,max_additional_marker_bytes=MAX_BYTES,
        interpretation='Includes scheduling/GC/IO/marker and elaboration overhead; not CPU attribution or bottleneck proof')
if __name__=='__main__':
    from pathlib import Path
    if len(sys.argv)!=2:raise SystemExit('Expected one existing bridge raw log; no execution route')
    print(json.dumps(summarize(Path(sys.argv[1]).read_text()),indent=2))
