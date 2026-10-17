import ctypes,time,os
libc=ctypes.CDLL(None)
libc.pthread_create.argtypes=[ctypes.POINTER(ctypes.c_ulong),ctypes.c_void_p,ctypes.c_void_p,ctypes.c_void_p]
libc.pthread_create.restype=ctypes.c_int
workers=[]
for seconds in [1, 3]:
    handle=ctypes.c_ulong()
    result=libc.pthread_create(ctypes.byref(handle),None,ctypes.cast(libc.sleep,ctypes.c_void_p),ctypes.c_void_p(seconds))
    if result:os._exit(90)
    workers.append(handle)
time.sleep(.25)
libc.pthread_exit.argtypes=[ctypes.c_void_p]
libc.pthread_exit.restype=None
libc.pthread_exit(None)
os._exit(91)
