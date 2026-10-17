import time,os,signal
time.sleep(.12)
os.kill(os.getpid(),signal.SIGTERM)
