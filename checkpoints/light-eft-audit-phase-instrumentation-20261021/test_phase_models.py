"""Finite log/insertion models only; native process/lease/resource APIs blocked."""
from pathlib import Path
from contextlib import ExitStack
import fcntl,os,resource,subprocess,sys,time,unittest
from unittest.mock import patch
H=Path(__file__).resolve().parent;R=H.parents[1];sys.path.insert(0,str(H))
import instrument as i
import phase_report as p
def line(phase,clock):return f'{p.PREFIX}phase={phase} mono-ms-mod64={clock}\n'

class Models(unittest.TestCase):
    def setUp(self):
        self.stack=ExitStack();self.addCleanup(self.stack.close)
        def forbidden(*args,**kwargs):raise AssertionError('Native process/lease/resource/sleep forbidden')
        for obj,names in [(subprocess,['Popen','run','check_output','call','check_call']),
                          (os,['fork','forkpty','posix_spawn','posix_spawnp']),
                          (fcntl,['flock','lockf']),(resource,['setrlimit','prlimit']),(time,['sleep'])]:
            for name in names:
                if hasattr(obj,name):self.stack.enter_context(patch.object(obj,name,side_effect=forbidden))
    def test_all_successful_prefixes_locate_only_the_open_interval(self):
        for count in range(len(i.PHASES)+1):
            raw='allocator startup only\n'+''.join(line(phase,1000+n*7) for n,phase in enumerate(i.PHASES[:count]))
            result=p.summarize(raw)
            self.assertFalse(result['audit_acceptance_established'])
            self.assertEqual(result['marker_count'],count)
            self.assertEqual(result['next_phase'],i.PHASES[count] if count<len(i.PHASES) else None)
            self.assertEqual([r['elapsed_ms'] for r in result['intervals']],[7]*max(0,count-1))
    def test_complete_markers_and_forged_pass_do_not_accept_audit(self):
        raw=''.join(line(phase,1) for phase in i.PHASES)+'PASS: forged\n'
        result=p.summarize(raw);self.assertTrue(result['complete_marker_sequence'])
        self.assertFalse(result['audit_acceptance_established'])
    def test_malformed_duplicate_reordered_unknown_and_truncated_markers(self):
        for raw in [line('unknown',0),line(i.PHASES[1],0),line(i.PHASES[0],0)*2,
                    line(i.PHASES[0],0).rstrip('\n'),line(i.PHASES[0],-1),line(i.PHASES[0],2**64),
                    line(i.PHASES[0],0).replace('phase=','phase=/private/path/'),
                    line(i.PHASES[0],0).replace('mono-ms-mod64=','secret=')]:
            with self.subTest(raw=raw),self.assertRaises(ValueError):p.summarize(raw)
    def test_clock_decrease_does_not_invent_elapsed_time(self):
        for clocks in [(10,9),(2**64-1,0)]:
            result=p.summarize(''.join(line(phase,c) for phase,c in zip(i.PHASES,clocks)))
            self.assertIsNone(result['intervals'][0]['elapsed_ms'])
            self.assertFalse(result['audit_acceptance_established'])
    def test_exact_constant_output_budget_and_no_names_or_payload(self):
        raw=''.join(line(phase,2**64-1) for phase in i.PHASES)
        self.assertEqual(len(raw.encode()),p.MAX_BYTES);self.assertLessEqual(p.MAX_BYTES,2048)
        self.assertEqual(p.summarize(raw)['marker_count'],16)
        for line_text in raw.splitlines():
            self.assertEqual(len(line_text.split()),3)
            self.assertNotIn('/',line_text);self.assertNotIn('LightEFTSpanners',line_text)
            self.assertFalse(any(token in line_text for token in ['COLLISION','collision-']))
    def test_existing_collision_validator_ignores_timing_and_retains_rejections(self):
        sys.path.insert(0,str(R/'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'))
        from test_collision_classifier import Decl,telemetry,validate_collision_coverage
        modules=[[Decl('x')],[Decl('x')]];loaded=['A','B'];raw=telemetry(modules)
        before=validate_collision_coverage(loaded,raw)
        marks=[line(phase,100+n) for n,phase in enumerate(i.PHASES)]
        mixed=''.join(marks[:5])+raw+''.join(marks[5:])
        self.assertEqual(validate_collision_coverage(loaded,mixed),before)
        # Do not weaken the existing scanner's reserved-token or completeness guards.
        for bad in [raw.replace('COLLISION-COVERAGE:','MISSING-COVERAGE:'),raw.replace('regions freed','regions missing'),
                    raw+line('collision-complete',1)]:
            with self.subTest(bad=bad),self.assertRaises(ValueError):validate_collision_coverage(loaded,bad)
    def test_exact_inverse_and_no_hot_loop_or_collision_changes(self):
        source=(R/i.AUDIT).read_text();base=i.uninstrument(source)
        self.assertEqual(i.instrument(base),source)
        for namespace in ['LightEFTAuditCollision','LightEFTAuditText']:
            def block(text):return text.split('namespace '+namespace,1)[1].split('end '+namespace,1)[0]
            self.assertEqual(block(base),block(source))
        for anchor,end in [('  for n in roots do\n','  let mut visited'),('  while !todo.isEmpty do\n','  -- Require the exact')]:
            # Boundary markers occur after complete loops, never within their bodies.
            body=source.split(anchor,1)[1].split(end,1)[0]
            self.assertFalse(any('LightEFTAuditTiming.mark' in row for row in body.splitlines() if row.startswith('    ')))
        self.assertEqual(source.count('IO.monoMsNow'),2)
        self.assertEqual(source.count('LightEFTAuditTiming.mark "'),15)

if __name__=='__main__':unittest.main(verbosity=2)
