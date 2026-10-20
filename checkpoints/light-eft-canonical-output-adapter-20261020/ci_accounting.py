"""Fresh CI full-hierarchy accounting; no Codex namespace or inode transplant.

Uses the existing initial-cgroup-namespace discovery. Unknown/truncated views
refuse. Pure normalization is separately testable without any kernel probes.
"""
from pathlib import Path
import os, time, datetime

FILES = ('memory.max','memory.current','memory.stat','memory.events',
         'cgroup.procs','pids.current','pids.max','pids.events')

def normalize(snapshot, rows, identities):
    if snapshot.get('discovery_error') or not snapshot.get('initial_namespace_verified'):
        raise ValueError('Full initial cgroup hierarchy not verified')
    if len(rows) != len(snapshot['ancestors']) or len(identities) != len(rows):
        raise ValueError('Incomplete ancestor accounting')
    if len({r['path'] for r in rows})!=len(rows):raise ValueError('Duplicate accounting ancestor')
    if type(snapshot['system_available']) is not int or snapshot['system_available']<0:raise ValueError('Bad host accounting')
    for expected, row in zip(snapshot['ancestors'], rows, strict=True):
        if row['path'] != expected['directory'] or row['limit'] != expected['max']:
            raise ValueError('Ancestor path/limit differs')
        if type(row['current']) is not int or row['current'] < 0:
            raise ValueError('Bad current memory observation')
        for k in ('anon','file','kernel'):
            if type(row['memory_stat'][k]) is not int or row['memory_stat'][k] < 0:
                raise ValueError('Bad memory.stat')
        if set(row['oom']) != {'oom','oom_kill','oom_group_kill'}:
            raise ValueError('Incomplete OOM counters')
        if row['limit'] != 'max' and int(row['limit']) <= 0:
            raise ValueError('Bad finite limit')
        if row['pids_max'] != 'max' and int(row['pids_max']) <= 0:
            raise ValueError('Bad PID limit')
    finite = [int(r['limit'])-r['current'] for r in rows if r['limit']!='max']
    # With the full initial hierarchy proven unlimited, MemAvailable is the
    # remaining conservative physical admission floor, not an invented cgroup cap.
    headroom = min(finite) if finite else snapshot['system_available']
    return dict(namespace=snapshot['namespace_inode'], membership=snapshot['membership'],
                mountinfo=snapshot['mountinfo_raw'], identities=identities, nodes=rows,
                headroom=headroom, system_available=snapshot['system_available'],
                qualification='FRESH_CI_FULL_INITIAL_CGROUP_HIERARCHY; no historical/local inode continuity',
                explicit_unlimited=not finite, collection_errors=[])

class CIAccounting:
    def __init__(self, memory_snapshot):
        self.memory_snapshot=memory_snapshot; self.expected=None; self.last_partial=None

    def sample(self):
        started=time.monotonic_ns(); rows=[]; ids=[]
        state=dict(sample_started_ns=started, nodes=rows, identities=ids, collection_errors=[])
        self.last_partial=state
        try:
            s=self.memory_snapshot()
            state['discovery_snapshot']=s
            if s.get('discovery_error'):raise ValueError(s['discovery_error'])
            for a in s['ancestors']:
                p=Path(a['directory']); raw={}; ident={}
                for parent in [p,*p.parents]:
                    if parent.is_symlink():raise ValueError('Symlink accounting parent')
                d=os.open(p,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
                try:
                    st=os.fstat(d);ident['directory']=[st.st_dev,st.st_ino]
                    for name in FILES:
                        f=os.open(name,os.O_RDONLY|os.O_NOFOLLOW,dir_fd=d)
                        try:
                            st=os.fstat(f);info=Path(f'/proc/self/fdinfo/{f}').read_text()
                            mount=next(x.split()[1] for x in info.splitlines() if x.startswith('mnt_id:'))
                            if mount!=s['selected_mount']['id']:raise ValueError('Accounting file overmount')
                            ident[name]=[st.st_dev,st.st_ino,mount];raw[name]=os.read(f,65536).decode()
                        finally:os.close(f)
                finally:os.close(d)
                pairs=lambda k:{x:int(y) for x,y in (line.split() for line in raw[k].splitlines())}
                events=pairs('memory.events')
                rows.append(dict(path=str(p),limit=raw['memory.max'].strip(),current=int(raw['memory.current']),
                    memory_stat=pairs('memory.stat'),memory_stat_raw=raw['memory.stat'],memory_events=events,
                    oom={k:events[k] for k in ['oom','oom_kill','oom_group_kill']},
                    pids_current=int(raw['pids.current']),pids_max=raw['pids.max'].strip(),pids_events=pairs('pids.events')))
                ids.append(ident)
            state=normalize(s,rows,ids)
            state['discovery_snapshot']=s
            stable={k:state[k] for k in ['namespace','membership','mountinfo','identities']}
            stable['limits']=[(r['limit'],r['pids_max']) for r in rows]
            if self.expected is None:self.expected=stable
            elif self.expected!=stable:raise ValueError('CI accounting identity/limit drift')
            if Path('/proc/self/cgroup').read_text()!=s['cgroup_membership_raw'] or Path('/proc/self/mountinfo').read_text()!=s['mountinfo_raw']:
                raise ValueError('CI membership/mount layout changed')
            state.update(sample_started_ns=started,sample_finished_ns=time.monotonic_ns(),sample_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
            return state
        except BaseException as e:
            state['collection_errors'].append(dict(operation='fresh CI accounting',error=repr(e)))
            state['sample_finished_ns']=time.monotonic_ns();self.last_partial=state
            # The reviewed collector retains this partial state, then refuses.
            e.partial=state
            raise
