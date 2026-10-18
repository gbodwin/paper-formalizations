"""Synthetic data producer only. Never invokes a compiler, checker or another tool."""
from pathlib import Path
import json,os,sys,time
stage,config=sys.argv[1:]
j=json.loads(Path(config).read_text())
time.sleep(.12)
if j.get('fail_stage')==stage:print('synthetic deliberate failure');raise SystemExit(7)
if j.get('descendant_stage')==stage:
 pid=os.fork()
 if pid==0:time.sleep(3);os._exit(0)
 time.sleep(3)
if stage=='compile':Path(j['object']).write_bytes(b'SYNTHETIC FIXTURE DATA, NOT A LEAN OBJECT\n')
if stage=='resolve':Path(j['resolution']).write_text(json.dumps({'target':j['target'],'count':1,'resolved':[{'module':j['target'],'object':j['object']}],'search_path':j['roots']}))
if stage=='replay':print('replaying '+j['target'])
if stage=='audit':
 out=Path(j['audit'])
 for name,text in j['audit_files'].items():(out/name).write_text(text)
 print(j['audit_raw'])
