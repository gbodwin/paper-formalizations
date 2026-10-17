"""Owned-child terminal observation only; waitid never reaps the child."""
import datetime
import os
import time

PF_EXITING = 0x4
TRANSITION_NS = 1_000_000_000


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


def assess(child, decision, record, before_probe, descendants):
    """Keep raw/null telemetry; grant no unconfirmed general missing-data exemption."""
    status = {'probes': [before_probe], 'terminal_confirmed': False,
              'allow_missing_memory': False}
    decision['exit_lifecycle'] = status
    errors = []
    current = decision.get('child') or {}
    first = record.get('child_identity')
    expected = {'pid': child.pid, 'ppid': os.getpid(), 'sid': child.pid, 'pgid': child.pid}
    if first is not None:
        expected['start_ticks'] = first['start_ticks']
    status['expected_identity'] = expected
    if not isinstance(current.get('start_ticks'), int) or any(current.get(k) != v for k, v in expected.items()):
        errors.append('Owned child identity mismatch or unavailable')
    rows = descendants()
    status['descendants'] = rows
    if any(x['pid'] != child.pid for x in rows):
        record['unexpected_descendants'] = rows
        errors.append('Unexpected process descendant')
    now = time.monotonic_ns()
    wall_deadline = record['runtime_wall_started_ns'] + int(record['deadline_seconds'] * 1_000_000_000)
    if now >= wall_deadline:
        errors.append('Child wall deadline')
    terminal = before_probe if before_probe.get('terminal') else None
    if before_probe.get('error'):
        errors.append('Owned waitid failed: ' + before_probe['error'])
    memory_errors = [x for x in current.get('collection_errors', []) if x.get('operation') in ('VmRSS', 'VmSize')]

    def again():
        nonlocal terminal
        observation = probe(child)
        status['probes'].append(observation)
        if observation.get('error'):
            errors.append('Owned waitid failed: ' + observation['error'])
        if observation.get('terminal'):
            terminal = observation

    if memory_errors and terminal is None:
        again()
    fd_closed = False
    if terminal is None:
        try:
            stat = os.stat('/proc/%s/fd/%s' % (child.pid, record['lock']['fd']))
            status['child_lock_identity'] = [stat.st_dev, stat.st_ino]
            if [stat.st_dev, stat.st_ino] != [record['lock']['device'], record['lock']['inode']]:
                errors.append('Child lock descriptor identity mismatch')
        except (FileNotFoundError, PermissionError) as exc:
            fd_closed = True
            status['child_lock_fd_unavailable'] = repr(exc)
            again()
        except Exception as exc:
            errors.append('Child lock descriptor check failed: ' + repr(exc))
    else:
        status['fd_check'] = 'Not required after owned kernel terminal confirmation'
    transition = record.get('exit_transition')
    if terminal is not None:
        if transition is not None and terminal['finished_ns'] > transition['deadline_ns']:
            errors.append('Exit transition confirmation exceeded one-second deadline')
        if not errors:
            status.update(terminal_confirmed=True, allow_missing_memory=True, confirmation=terminal)
            record['terminal_confirmation'] = terminal
            if transition is not None:
                transition.update(state='kernel-confirmed', confirmed_ns=terminal['finished_ns'])
    else:
        only_memory_errors = all(x.get('operation') in ('VmRSS', 'VmSize') and
                                 x.get('error') == 'Missing required live value'
                                 for x in current.get('collection_errors', []))
        candidate = bool(memory_errors) and only_memory_errors and not errors and (
            current.get('stat_flags', 0) & PF_EXITING and current.get('stat_threads') == 1
            and current.get('status_threads') == 1 and current.get('stat_vsize_bytes') == 0
            and current.get('stat_rss_pages') == 0)
        status['exact_transition_candidate'] = bool(candidate)
        if candidate:
            if transition is None:
                transition = {'started_ns': now, 'deadline_ns': min(now + TRANSITION_NS, wall_deadline),
                              'state': 'awaiting-kernel-confirmation', 'identity': expected,
                              'first_sample_utc': decision['sample_utc']}
                record['exit_transition'] = transition
            if time.monotonic_ns() >= transition['deadline_ns']:
                errors.append('Exit transition confirmation timeout')
            else:
                status.update(transition_pending=True, allow_missing_memory=True,
                              transition_deadline_ns=transition['deadline_ns'])
        elif transition is not None:
            errors.append('Unconfirmed exit transition no longer matches exact predicate')
        if fd_closed and not candidate:
            errors.append('Unconfirmed live child lock FD disappeared')
    for error in errors:
        decision['collection_errors'].append({'operation': 'exit supervision', 'error': error})
