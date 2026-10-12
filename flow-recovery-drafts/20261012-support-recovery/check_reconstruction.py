from pathlib import Path
import os,sys,subprocess,json,hashlib,time
p=Path(__file__).parent;lib=p/'lib';logs=p/'logs';env=os.environ.copy();env['LEAN_PATH']=str(lib)+':'+str(p/'parent-lib')+':'+env['FORMALIZATION_DEP_LEAN_PATH'];env['LEAN_NUM_THREADS']='1'
names=sys.argv[1:] or ['SupportRecoveryProgram','SupportSearchData','SupportSearchAccounts','SupportRecoveryCalls','SupportSearchInvariants','SupportEdgeComparison','SupportEdgeMembership','SupportAdjacencyTest','SupportCodeLookup','SupportPredecessorPrefix','SupportPredecessorScan','SupportVisitAllocation','SupportVisitDecision','SupportVertexVisit','SupportForwardPass','SupportRoundInitial','SupportRounds','SupportSearchExecution','SupportSearchLowerMachine']
for n in names:
 src=p/'src/DirectedFlowCutGap'/f'{n}.lean';out=lib/'DirectedFlowCutGap'/f'{n}.olean';h=hashlib.sha256(src.read_bytes()).hexdigest();attempt=1+len(list(logs.glob(n+'.attempt-*.log')));log=logs/f'{n}.attempt-{attempt}.log';print('STRICT',n,flush=True);start=time.monotonic()
 with log.open('w') as f:r=subprocess.run(['lean','-j1','-DautoImplicit=false','-DwarningAsError=true','-o',str(out),str(src.relative_to(p/'src'))],cwd=p/'src',env=env,stdout=f,stderr=subprocess.STDOUT)
 result={'source':n,'sha256':h,'returncode':r.returncode,'elapsed':time.monotonic()-start,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'scope':'Fresh strict check of reconstructed source; not an original-byte recovery claim or full checkpoint verification'};log.with_suffix('.result.json').write_text(json.dumps(result,indent=2)+'\n')
 if r.returncode:print(log.read_text(),flush=True);sys.exit(r.returncode)
 print('STRICT_PASS',n,flush=True)
