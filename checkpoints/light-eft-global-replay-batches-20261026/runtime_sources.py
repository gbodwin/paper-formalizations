"""SOURCE ONLY: nine exact package source checkouts, never package build caches.

Future ordinary setup operation. No command in this source has been invoked.
Failed Git operations and partial checkouts are retained, never cleaned/retried.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    if not (sys.flags.isolated and sys.dont_write_bytecode):
        raise ValueError('Require Python -I -B')
    path = HERE / 'route_status.py'
    raw = path.read_bytes()
    actual = subprocess.run(['git', 'show', 'HEAD:' + path.relative_to(ROOT).as_posix()],
                            cwd=ROOT, capture_output=True, check=True, timeout=10).stdout
    if raw != actual or any(p.is_symlink() for p in [path, *path.parents]):
        raise ValueError('Route controller differs from actual Git source')
    spec = importlib.util.spec_from_file_location('_bound_source_setup_status', path)
    route = importlib.util.module_from_spec(spec); spec.loader.exec_module(route)
    bound = route.controls(); ci = route.identity('global_replay'); cl = route.contract()
    require = route.require
    require(not os.path.lexists(ROOT / '.lake'), 'Fresh source setup requires absent .lake')
    require((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0',
            'Wrong ordinary toolchain source')
    manifest = route.read(ROOT / 'lake-manifest.json')
    packages = manifest['packages']
    require(manifest['packagesDir'] == '.lake/packages' and len(packages) == 9 and
            {p['name']: p['rev'] for p in packages} == cl.PINS, 'Exact nine pins differ')
    require(len({p['name'] for p in packages}) == 9 and all(p['type'] == 'git' and
            p['subDir'] is None and p['url'].startswith('https://github.com/') and
            not any(x in p['url'] for x in ['@', '?', '#', '\n', '\r']) for p in packages),
            'Unreviewed package source transport')
    parent = Path(os.environ['RUNNER_TEMP']).resolve(strict=True)
    report = parent / ('light-eft-replay-source-setup-' + ci['run_id'] + '-' + ci['run_attempt'])
    report.mkdir(mode=0o700, exist_ok=False)
    result = dict(status='FAILED_SOURCE_SETUP_ONLY', CI_identity=ci, controls=bound,
                  packages=[], compiled_cache_restored=False, proof_acceptance=False)

    def command(argv, cwd, label):
        # Newly owned public-package repositories only. No hooks execute and no
        # credential/security configuration is changed. Do not broaden on error.
        command_argv = ['git', '-c', 'core.hooksPath=/dev/null', '-c', 'core.fsmonitor=false', *argv]
        began = time.monotonic_ns()
        metadata = dict(argv=command_argv, cwd=str(cwd), phase=label,
                        timeout_seconds=600, started_ns=began)
        cl.create(report / (label + '-start.json'), route.encoded(metadata))
        try:
            p = subprocess.run(command_argv, cwd=cwd, capture_output=True, timeout=600)
        except (subprocess.TimeoutExpired, OSError) as error:
            # TimeoutExpired retains partial captured bytes; a launch failure
            # may have no stream. Preserve the distinction without retrying.
            out = getattr(error, 'stdout', None)
            err = getattr(error, 'stderr', None)
            for suffix, value in [('stdout', out), ('stderr', err)]:
                raw = value.encode() if isinstance(value, str) else (value or b'')
                cl.create(report / (label + '.' + suffix), raw)
            cl.create(report / (label + '.json'), route.encoded(dict(metadata,
                      ended_ns=time.monotonic_ns(), returncode=None,
                      timed_out=isinstance(error, subprocess.TimeoutExpired),
                      launch_failed=isinstance(error, OSError), error=repr(error),
                      partial_stdout_available=out is not None,
                      partial_stderr_available=err is not None,
                      operation_failed=True, no_retry=True)))
            raise
        cl.create(report / (label + '.stdout'), p.stdout)
        cl.create(report / (label + '.stderr'), p.stderr)
        cl.create(report / (label + '.json'), route.encoded(dict(metadata,
                  ended_ns=time.monotonic_ns(), returncode=p.returncode,
                  timed_out=False, launch_failed=False, operation_failed=p.returncode != 0)))
        require(p.returncode == 0, 'Package setup failed: ' + label)
        return p.stdout

    try:
        (ROOT / '.lake').mkdir(mode=0o700)
        base = ROOT / '.lake/packages'; base.mkdir(mode=0o700)
        for p in packages:
            name = p['name']; dest = base / name
            require(name in cl.PINS and not os.path.lexists(dest), 'Package destination exists')
            dest.mkdir(mode=0o700)
            command(['init', '--quiet'], dest, name + '-init')
            command(['remote', 'add', 'origin', p['url']], dest, name + '-origin')
            command(['fetch', '--no-tags', '--depth=1', 'origin', p['rev']], dest, name + '-fetch')
            fetched = command(['rev-parse', 'FETCH_HEAD'], dest, name + '-fetched').decode().strip()
            require(fetched == cl.PINS[name], 'Exact package fetch differs')
            command(['checkout', '--detach', '--quiet', fetched], dest, name + '-checkout')
            require(command(['rev-parse', 'HEAD'], dest, name + '-head').decode().strip() == fetched and
                    not command(['status', '--porcelain', '--untracked-files=all'], dest, name + '-status'),
                    'Package checkout not exact and clean')
            require(not os.path.lexists(dest / '.lake'), 'Source checkout supplies a package build/cache tree')
            result['packages'].append(dict(name=name, revision=fetched, url=p['url']))
        require(route.controls() == bound and route.identity('global_replay') == ci,
                'Source/identity changed during ordinary setup')
        result['status'] = 'EXACT_PACKAGE_SOURCES_ONLY_NOT_COMPILED_INPUT_ACCEPTANCE'
    except BaseException as error:
        result['failure'] = repr(error)
        result['partial_source_checkouts_preserved'] = True
        raise
    finally:
        cl.create(report / 'result.json', route.encoded(result))


if __name__ == '__main__':
    main()
