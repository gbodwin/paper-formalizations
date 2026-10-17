import time,os,signal
time.sleep(.25)
os.kill(os.getpid(),signal.SIGTERM)
