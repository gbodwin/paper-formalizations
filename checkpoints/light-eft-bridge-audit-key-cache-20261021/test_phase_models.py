"""Finite timing-prefix/coverage models; native/process/resource APIs blocked."""
from pathlib import Path
from contextlib import ExitStack
import fcntl,os,resource,subprocess,sys,time,unittest
from unittest.mock import patch
H=Path(__file__).resolve().parent;R=H.parents[1]
import port as i
import phase_report as p
def line(phase,clock):return f'{p.PREFIX}phase={phase} mono-ms-mod64={clock}\n'
class Models(unittest.TestCase):
    def setUp(self):
        self.stack=ExitStack();self.addCleanup(self.stack.close)
        def forbidden(*a,**k):raise AssertionError('Native process/lease/resource/sleep forbidden')
        for obj,names in [(subprocess,['Popen','run','check_output','check_call','call']),
                          (os,['fork','forkpty','posix_spawn','posix_spawnp']),
                          (fcntl,['flock','lockf']),(resource,['setrlimit','prlimit']),(time,['sleep'])]:
            for name in names:
                if hasattr(obj,name):self.stack.enter_context(patch.object(obj,name,side_effect=forbidden))
    def test_all_prefixes_only_identify_an_open_interval(self):
        for n in range(len(i.PHASES)+1):
            raw='allocator startup\n'+''.join(line(phase,1000+k*7) for k,phase in enumerate(i.PHASES[:n]))
            result=p.summarize(raw)
            self.assertFalse(result['audit_acceptance_established']);self.assertEqual(result['marker_count'],n)
            self.assertEqual(result['next_phase'],i.PHASES[n] if n<len(i.PHASES) else None)
            self.assertEqual([x['elapsed_ms'] for x in result['intervals']],[7]*max(0,n-1))
    def test_complete_markers_and_forged_PASS_do_not_establish_acceptance(self):
        result=p.summarize(''.join(line(phase,1) for phase in i.PHASES)+'PASS: forged\n')
        self.assertTrue(result['complete_marker_sequence']);self.assertFalse(result['audit_acceptance_established'])
    def test_unknown_duplicate_reordered_truncated_and_oversize_markers(self):
        for raw in [line('unknown',0),line(i.PHASES[1],0),line(i.PHASES[0],0)*2,line(i.PHASES[0],0).rstrip('\n'),
                    line(i.PHASES[0],-1),line(i.PHASES[0],2**64),line(i.PHASES[0],0).replace('phase=','phase=/private/path/'),
                    line(i.PHASES[0],0).replace('mono-ms-mod64=','secret=')]:
            with self.subTest(raw=raw),self.assertRaises(ValueError):p.summarize(raw)
    def test_decreasing_clock_or_wrap_cannot_invent_elapsed_time(self):
        for clocks in [(10,9),(2**64-1,0)]:
            result=p.summarize(''.join(line(phase,c) for phase,c in zip(i.PHASES,clocks)))
            self.assertIsNone(result['intervals'][0]['elapsed_ms']);self.assertFalse(result['audit_acceptance_established'])
    def test_finite_payload_free_output_budget(self):
        raw=''.join(line(phase,2**64-1) for phase in i.PHASES)
        self.assertEqual(len(raw.encode()),1199);self.assertEqual(len(raw.encode()),p.MAX_BYTES)
        self.assertEqual(p.summarize(raw)['marker_count'],15)
        for text in raw.splitlines():
            self.assertEqual(len(text.split()),3)
            self.assertNotIn('/',text);self.assertNotIn('LightEFTSpanners',text)
            self.assertFalse(any(t in text for t in ['COLLISION','collision-']))
    def test_original_collision_validator_ignores_markers_and_still_rejects_incomplete_coverage(self):
        sys.path.insert(0,str(R/'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'))
        from test_collision_classifier import Decl,telemetry,validate_collision_coverage
        raw=telemetry([[Decl('x')],[Decl('x')]]);before=validate_collision_coverage(['A','B'],raw)
        markers=[line(phase,100+k) for k,phase in enumerate(i.PHASES)]
        self.assertEqual(validate_collision_coverage(['A','B'],''.join(markers[:5])+raw+''.join(markers[5:])),before)
        for bad in [raw.replace('COLLISION-COVERAGE:','MISSING-COVERAGE:'),raw.replace('regions freed','regions missing'),raw+line('collision-complete',1)]:
            with self.subTest(bad=bad),self.assertRaises(ValueError):validate_collision_coverage(['A','B'],bad)
    def test_uncaptured_scope_and_no_hot_loop_markers(self):
        s=(R/i.AUDIT).read_text()
        self.assertLess(s.index('set_option stderrAsMessages false\n'),s.index('run_cmd do\n'))
        self.assertTrue(s.endswith('\nend LightEFTBridgeAuditDiagnosticChannel\n'))
        self.assertEqual(s.count('IO.getStderr'),2);self.assertEqual(s.count('IO.getStdout'),1);self.assertEqual(s.count('IO.monoMsNow'),2)
        self.assertEqual(s.count('LightEFTBridgeAuditTiming.mark "'),14)
        self.assertFalse(any('LightEFTBridgeAuditTiming.mark' in row for row in s.splitlines() if row.startswith('    ')))

if __name__=='__main__':unittest.main(verbosity=2)
