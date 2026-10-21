"""Pinned stream-capture/order models and actual launcher AST; never runs Lean."""
from pathlib import Path
from contextlib import ExitStack
import fcntl,os,resource,subprocess,sys,time,unittest
from unittest.mock import patch
H=Path(__file__).resolve().parent;R=H.parents[1];sys.path.insert(0,str(H))
from check_delivery_source import repair,unrepair,validate_delivery,launcher_contract
from instrument import AUDIT,CHANNEL_SCOPE,CHANNEL_END,PHASES
from phase_report import MAX_BYTES,summarize

class BufferStream:
    def __init__(self):self.data=''
    def put(self,text):self.data+=text
    def flush(self):pass  # Pinned IO.FS.Stream.ofBuffer.flush = pure ().

class HandleStream:
    def __init__(self,raw):self.pending='';self.raw=raw
    def put(self,text):self.pending+=text
    def flush(self):self.raw.append(self.pending);self.pending=''

def command(option_at_entry,channel,late_option=None,completed=False):
    # Language.Lean.doElab reads scope.opts before entering the command.
    raw=[];buffer=BufferStream();stderr=buffer if option_at_entry else HandleStream(raw)
    stdout=buffer
    option_during_body=option_at_entry if late_option is None else late_option
    stream=stdout if channel=='stdout' else stderr
    marker='AUDIT-TIMING: phase=frontend-ready mono-ms-mod64=1\n'
    stream.put(marker);stream.flush()
    before_return=''.join(raw)
    if completed:raw.append(buffer.data)
    # Otherwise command termination/timeout loses its unreported buffer.
    return before_return,''.join(raw),option_during_body

class Models(unittest.TestCase):
    def setUp(self):
        self.stack=ExitStack();self.addCleanup(self.stack.close)
        def forbidden(*a,**k):raise AssertionError('Native process/lease/resource/sleep forbidden')
        for obj,names in [(subprocess,['Popen','run','check_output','call','check_call']),
                          (os,['fork','forkpty','posix_spawn','posix_spawnp']),
                          (fcntl,['flock','lockf']),(resource,['setrlimit','prlimit']),(time,['sleep'])]:
            for name in names:
                if hasattr(obj,name):self.stack.enter_context(patch.object(obj,name,side_effect=forbidden))
    def test_stdout_is_captured_even_with_stderr_option_false(self):
        for option in [True,False]:
            before,after,_=command(option,'stdout',completed=False)
            self.assertEqual((before,after),('',''))
            before,after,_=command(option,'stdout',completed=True)
            self.assertEqual(before,'');self.assertIn('AUDIT-TIMING:',after)
    def test_default_stderr_is_captured_and_late_option_is_too_late(self):
        for late in [None,False]:
            before,after,_=command(True,'stderr',late_option=late,completed=False)
            self.assertEqual((before,after),('',''))
    def test_standalone_false_makes_flush_survive_command_termination(self):
        for completed in [True,False]:
            before,after,_=command(False,'stderr',completed=completed)
            self.assertIn('AUDIT-TIMING:',before);self.assertEqual(before,after)
    def test_section_restores_true_or_false_caller_option(self):
        for caller in [True,False]:
            scopes=[dict(stderrAsMessages=caller)]
            scopes.append(dict(scopes[-1]));scopes[-1]['stderrAsMessages']=False
            before,_,_=command(scopes[-1]['stderrAsMessages'],'stderr')
            self.assertIn('AUDIT-TIMING:',before)
            scopes.pop();self.assertEqual(scopes[-1]['stderrAsMessages'],caller)
    def test_exact_repair_and_invalid_scope_or_channel_rejected(self):
        new=(R/AUDIT).read_text();old=unrepair(new);validate_delivery(new,old)
        self.assertEqual(repair(old),new)
        for bad in [new.replace(CHANNEL_SCOPE,''),new.removesuffix(CHANNEL_END),
                    new.replace('stderrAsMessages false','stderrAsMessages true'),
                    new.replace('IO.getStderr','IO.getStdout',1),new.replace('IO.getStdout','IO.getStderr'),
                    new.replace('set_option stderrAsMessages false\n','set_option stderrAsMessages false in\n'),
                    new.replace(CHANNEL_END,'\nset_option stderrAsMessages true\n')]:
            with self.subTest(bad=bad[:120]),self.assertRaises(AssertionError):validate_delivery(bad,old)
    def test_actual_launcher_merge_and_exec_preservation(self):
        e=R/'checkpoints/light-eft-joint-flag-assignment-corrected-adapter-20261018'
        runner=(e/'child_runner.py').read_text();pilot=(e/'pilot_child.py').read_text()
        launcher_contract(runner,pilot)
        for bad in [runner.replace('stderr=subprocess.STDOUT','stderr=subprocess.PIPE'),
                    runner.replace('stdout=log','stdout=subprocess.PIPE')]:
            with self.assertRaises(AssertionError):launcher_contract(bad,pilot)
        with self.assertRaises(AssertionError):launcher_contract(runner,pilot+'\nos.dup2(1,2)\n')
    def test_all_merged_markers_stay_bounded_and_non_authoritative(self):
        raw=''.join(f'AUDIT-TIMING: phase={p} mono-ms-mod64={2**64-1}\n' for p in PHASES)
        self.assertEqual(len(raw.encode()),MAX_BYTES);self.assertEqual(MAX_BYTES,1176)
        result=summarize(raw);self.assertFalse(result['audit_acceptance_established'])
        self.assertEqual(result['marker_count'],16)

if __name__=='__main__':unittest.main(verbosity=2)
