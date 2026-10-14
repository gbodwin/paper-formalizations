"""Static draft checks only; does not invoke Lean or establish Lean validity."""
from pathlib import Path
import hashlib, json, re, subprocess
ROOT = Path(__file__).resolve().parent
BASE = Path('/workspace/shared/flow-published722-recovered-20261014T0012Z')
PAPER = BASE/'Improved Upper Bounds for the Directed Flow-Cut Gap'
files = sorted((ROOT/'DirectedFlowCutGap').glob('*.lean'))
assert len(files) == 9
for p in files:
    text = p.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|native_decide)\b', text), p
    assert text.count('namespace DirectedFlowCutGap.FinalDispatch\n') == 1
    assert text.rstrip().endswith('end DirectedFlowCutGap.FinalDispatch')
    for module in re.findall(r'^import (DirectedFlowCutGap\.\S+)', text, re.M):
        rel = Path(*module.split('.')).with_suffix('.lean')
        assert (ROOT/rel).is_file() or (PAPER/rel).is_file(), (p,module)
prog=(ROOT/'DirectedFlowCutGap/FinalDispatchProgram.lean').read_text()
assert 'match pc.val-13264 with' in prog
assert 'match pc.val with' not in prog
parts=[(0,10760),(10760,12900),(12900,12944),(12944,13264),(13264,13320)]
assert [b-a for a,b in parts] == [10760,2140,44,320,56]
assert all(parts[i][1] == parts[i+1][0] for i in range(len(parts)-1))
controllers={int(i):op for i,op in re.findall(r'^  \| (\d+) => (.+)$',prog,re.M)}
assert set(controllers)=={6,7,8,9,10,11,36,37,38,39,40,41,42,43,44,45,46,47,54}
assert controllers[54]=='.call 13300 13319 .r3'
assert controllers[39]=='.branch .r3 13306 13304 13304 13319'
assert controllers[44]=='.branch .r3 13305 13319 13319 13309'
assert controllers[43]=='.call 13262 13308 .r3'
assert controllers[45]=='.call 10758 13310 .r3'
assert controllers[47]=='.make .r3 (.pair .r0 .r3) 13305'
assert 55 not in controllers
# Check tracked baseline bytes, without touching its checkout.
subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=BASE,check=True)
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=BASE,text=True).strip()
assert commit=='ea1dfba989c89eb8ceed693cdad42ba8d96584f5'
report={
 'status':'NEW_UNVERIFIED_DRAFT_STATIC_CHECKS_ONLY',
 'baseline_commit':commit,
 'lean_invoked':False,
 'compiler_pass_claimed':False,
 'physical_fixture_claimed':False,
 'baseline_tracked_diff':'empty',
 'module_count':len(files),
 'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
 'checks':['import source existence','placeholder/unsafe token scan','namespace balance',
           'disjoint complete label partition','key controller and branch slots','baseline tracked bytes'],
}
(ROOT/'static-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
