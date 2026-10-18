import threading,json,sys
event=threading.Event()
workers=[threading.Thread(target=event.wait) for _ in range(3)]
for worker in workers:worker.start()
print(json.dumps([threading.get_native_id()]+[worker.native_id for worker in workers]),flush=True)
sys.stdin.readline()
event.set()
for worker in workers:worker.join()
