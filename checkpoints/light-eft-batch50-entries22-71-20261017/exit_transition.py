"""Whole-process identity tracking; only owned waitid can confirm completion."""
from pathlib import Path
import datetime,os,time
import decision_telemetry as telemetry
PF_EXITING=0x4
TRANSITION_NS=1_000_000_000

def probe(child):
    row = {'pid_requested': child.pid, 'started_ns': time.monotonic_ns(),
           'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'options': ['WEXITED', 'WNOHANG', 'WNOWAIT'], 'terminal': False}
    try:
        info = os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
        if info is not None:
            row.update(pid=info.si_pid, uid=info.si_uid, code=info.si_code,
                       status=info.si_status, signo=info.si_signo)
            if info.si_pid != child.pid or info.si_code not in (os.CLD_EXITED, os.CLD_KILLED, os.CLD_DUMPED):
                raise RuntimeError('Unexpected owned waitid result')
            row['terminal'] = True
    except Exception as exc:
        row['error'] = repr(exc)
    row['finished_ns'] = time.monotonic_ns()
    return row


def no_mm(row):
    return bool((row.get('stat_flags', 0) & PF_EXITING or row.get('state') in ('Z', 'X'))
                and row.get('stat_vsize_bytes') == 0 and row.get('stat_rss_pages') == 0
                and row.get('rss') in (None, 0) and row.get('vm') in (None, 0))


def is_gone(tid):
    try:
        os.stat('/proc/%d' % tid)
        return False
    except FileNotFoundError:
        return True


def assess(child, decision, record, before_probe, descendants):
    status = {'probes': [before_probe], 'terminal_confirmed': False, 'allow_missing_memory': False,
              'completion_rule': 'owned waitid terminal confirmation, never leader state alone'}
    decision['exit_lifecycle'] = status
    decision['process_memory'] = {'rss': None, 'vm': None, 'source_tid': None}
    decision['observed_process_memory'] = {'rss': None, 'vm': None, 'source_tid': None}
    leader = decision.get('child') or {}
    catalog = record.setdefault('tid_catalog', {})
    errors = []
    now = time.monotonic_ns()
    wall_deadline = record['runtime_wall_started_ns'] + int(record['deadline_seconds'] * 1_000_000_000)
    if now >= wall_deadline:
        errors.append('Child wall deadline')
    terminal = before_probe if before_probe.get('terminal') else None
    if before_probe.get('error'):
        errors.append('Owned waitid failed: ' + before_probe['error'])

    def again():
        nonlocal terminal
        row = probe(child)
        status['probes'].append(row)
        if row.get('error'):
            errors.append('Owned waitid failed: ' + row['error'])
        if row.get('terminal'):
            terminal = row

    def identity(row, tid):
        expected = {'pid': tid, 'stat_pid': tid, 'status_pid': tid, 'tgid': child.pid,
                    'ppid': os.getpid(), 'sid': child.pid, 'pgid': child.pid}
        previous = catalog.get(str(tid))
        first = record.get('child_identity') if tid == child.pid else None
        if previous:
            expected['start_ticks'] = previous['start_ticks']
        elif first:
            expected['start_ticks'] = first['start_ticks']
        if not isinstance(row.get('start_ticks'), int) or any(row.get(k) != v for k, v in expected.items()):
            errors.append('TID identity/Tgid/start-time/ownership mismatch: ' + str(tid))
            return False
        if previous is None:
            previous = {'tid': tid, 'tgid': child.pid, 'start_ticks': row['start_ticks'],
                        'first_seen_ns': now, 'first_seen_utc': decision['sample_utc']}
            catalog[str(tid)] = previous
        previous.update(last_seen_ns=time.monotonic_ns(), last_state=row.get('state'))
        return True

    def grace(entry):
        if 'teardown_deadline_ns' not in entry:
            entry.update(teardown_started_ns=now, teardown_deadline_ns=min(now + TRANSITION_NS, wall_deadline))
        if time.monotonic_ns() >= entry['teardown_deadline_ns']:
            errors.append('Non-resetting thread teardown grace expired: ' + str(entry['tid']))

    def group_grace():
        g = record.get('process_teardown')
        if g is None:
            g = {'started_ns': now, 'deadline_ns': min(now + TRANSITION_NS, wall_deadline),
                 'first_sample_utc': decision['sample_utc'], 'state': 'awaiting-whole-process-confirmation'}
            record['process_teardown'] = g
        status['teardown_deadline_ns'] = g['deadline_ns']
        if time.monotonic_ns() >= g['deadline_ns']:
            errors.append('Non-resetting whole-process teardown grace expired')

    leader_ok = identity(leader, child.pid)
    rows = descendants()
    status['descendants'] = rows
    if any(row['pid'] != child.pid for row in rows):
        record['unexpected_descendants'] = rows
        errors.append('Unexpected process descendant')
    threads = [leader]
    valid = [leader] if leader_ok else []
    if terminal is None:
        discovered = set()
        try:
            discovered = {int(p.name) for p in Path('/proc/%d/task' % child.pid).iterdir() if p.name.isdecimal()}
            status['task_census_tids'] = sorted(discovered)
            record['last_task_census'] = {'sample_utc': decision['sample_utc'], 'tids': sorted(discovered)}
        except (FileNotFoundError, PermissionError) as exc:
            status['task_census_unavailable'] = repr(exc)
        retained = {int(k) for k, v in catalog.items() if not v.get('positively_gone')}
        tids = sorted((discovered | retained) - {child.pid})
        for tid in tids:
            # /proc/TID remains directly addressable even if PID/task vanishes.
            row = telemetry.capture_child(tid)
            row['proc_read_path'] = '/proc/%d' % tid
            threads.append(row)
            if row.get('collection_errors') and is_gone(tid):
                entry = catalog.get(str(tid))
                if entry:
                    entry.update(positively_gone=True, gone_confirmed_ns=time.monotonic_ns())
                    row['known_tid_positively_gone'] = True
                else:
                    row['vanished_from_owned_census_before_identity_capture'] = True
                continue
            if identity(row, tid):
                valid.append(row)
        if status.get('task_census_unavailable') and leader.get('stat_threads', 0) > len(catalog):
            errors.append('Unobservable thread census exceeds retained identity catalog')
        if leader.get('collection_errors') or no_mm(leader) or any(no_mm(row) for row in valid):
            again()
    status['threads'] = threads
    # Raw rows remain in threads/decision.child, with rereads nested under the
    # original row. All policy classification uses this separate effective map.
    effective = {row['pid']: row for row in valid}
    live = {}
    observed = []

    def classify(row):
        tid = row['pid']
        effective[tid] = row
        live.pop(tid, None)
        if isinstance(row.get('rss'), int) and isinstance(row.get('vm'), int):
            observed.append(row)
        only_memory_errors = all(x.get('operation') in ('VmRSS', 'VmSize') and x.get('error') == 'Missing required live value'
                                 for x in row.get('collection_errors', []))
        if not only_memory_errors:
            errors.append('Thread collection/identity error: ' + str(tid) + ' ' + repr(row['collection_errors']))
            return
        if no_mm(row):
            if terminal is None:
                grace(catalog[str(tid)])
                if tid == child.pid:
                    group_grace()
            row['positively_exiting_no_mm'] = True
        elif row.get('rss') is None or row.get('vm') is None:
            errors.append('Missing memory telemetry for still-live TID ' + str(tid))
        else:
            if catalog[str(tid)].get('teardown_started_ns') is not None:
                errors.append('Previously exiting TID regained unconfirmed memory: ' + str(tid))
            live[tid] = row

    for row in valid:
        classify(row)
    selected = None
    if terminal is None:
        for row in sorted(list(live.values()), key=lambda x: x['rss'], reverse=True):
            tid = row['pid']
            try:
                st = os.stat('/proc/%d/fd/%d' % (tid, record['lock']['fd']))
                if [st.st_dev, st.st_ino] != [record['lock']['device'], record['lock']['inode']]:
                    errors.append('Live TID inherited lock identity mismatch: ' + str(tid))
                    continue
                selected = row
                status['live_lock_verification'] = {'tid': tid, 'device': st.st_dev, 'inode': st.st_ino}
                break
            except (FileNotFoundError, PermissionError) as exc:
                row['fd_unavailable'] = repr(exc)
                again()
                if terminal is not None:
                    break
                fresh = telemetry.capture_child(tid)
                row['fd_transition_reread'] = fresh
                # The old candidate is never used again, even if validation of
                # its replacement fails. Such failure remains a hard error.
                effective.pop(tid, None)
                live.pop(tid, None)
                if fresh.get('collection_errors') and is_gone(tid) and tid != child.pid:
                    catalog[str(tid)].update(positively_gone=True, gone_confirmed_ns=time.monotonic_ns())
                    fresh['known_tid_positively_gone'] = True
                    continue
                if not identity(fresh, tid):
                    continue
                classify(fresh)
                if tid == child.pid:
                    leader = fresh
                if no_mm(fresh):
                    continue
                errors.append('Inherited lock unavailable for still-live TID ' + str(tid))
    if observed:
        row = max(observed, key=lambda x: x['rss'])
        decision['observed_process_memory'] = {'rss': row['rss'], 'vm': row['vm'], 'source_tid': row['pid'],
                                                'tgid': row['tgid'], 'start_ticks': row['start_ticks'], 'aggregation': 'one shared-mm sample; never summed'}
    valid = list(effective.values())
    status['effective_classifications'] = {str(row['pid']): {'state': row.get('state'), 'no_mm': no_mm(row),
        'rss': row.get('rss'), 'vm': row.get('vm'), 'start_ticks': row.get('start_ticks')} for row in valid}
    if terminal is not None:
        g = record.get('process_teardown')
        if g and terminal['finished_ns'] > g['deadline_ns']:
            errors.append('Whole-process confirmation exceeded fixed teardown deadline')
        if not errors:
            status.update(terminal_confirmed=True, allow_missing_memory=True, confirmation=terminal,
                          fd_check='No live FD requirement after owned whole-process confirmation')
            record['terminal_confirmation'] = terminal
            for entry in catalog.values():
                entry['whole_process_terminal_confirmed_ns'] = terminal['finished_ns']
            if g:
                g.update(state='kernel-confirmed', confirmed_ns=terminal['finished_ns'])
    else:
        if selected is not None:
            decision['process_memory'] = {'rss': selected['rss'], 'vm': selected['vm'], 'source_tid': selected['pid'],
                                          'tgid': selected['tgid'], 'start_ticks': selected['start_ticks'],
                                          'aggregation': 'single identity-checked shared-address-space sample; never summed'}
            status['using_live_sibling_memory'] = selected['pid'] != child.pid
        elif valid and all(no_mm(row) for row in valid):
            group_grace()
        else:
            errors.append('No identity-checked live shared-mm telemetry or bounded exiting-only group')
        if leader_ok and no_mm(leader) and not errors:
            status['allow_missing_memory'] = True
        if record.get('process_teardown'):
            group_grace()  # Fixed deadline is checked again, never reset.
            status['teardown_pending'] = True
    for error in errors:
        decision['collection_errors'].append({'operation': 'whole-process supervision', 'error': error})
