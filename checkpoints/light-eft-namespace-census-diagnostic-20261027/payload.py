"""Actual fresh filesystem census only; no compiler, subprocess or proof result."""
from pathlib import Path
import hashlib
import json
import os
import resource
import stat
import sys
import types

HERE = Path(__file__).resolve().parent
HARNESS = HERE.parents[1]
TESTED = HARNESS.parent
SOURCE = '2bc06c4aca8ba1e0d48e4e4a879f93944a17d4db'
CONTRACT = 'checkpoints/light-eft-global-replay-batches-20261026/closure_contract.py'
MAX_RESULT = 1024 ** 2


def require(ok, text):
    if not ok:
        raise RuntimeError(text)


def read_file(path, bound):
    for parent in [path, *path.parents]:
        require(not parent.is_symlink(), 'Symlink diagnostic input')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1 and
                before.st_size <= bound, 'Unsafe diagnostic input')
        raw = stream.read(bound + 1)
        after = os.fstat(stream.fileno()); named = path.lstat()
        signature = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_nlink,
                               s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        require(len(raw) <= bound and signature(before) == signature(after) ==
                signature(named), 'Diagnostic input changed')
        return raw


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate diagnostic key')
        result[key] = value
    return result


def authenticate():
    raw = read_file(HERE / 'bindings.json', MAX_RESULT)
    require(hashlib.sha256(raw).hexdigest() == os.environ['CENSUS_BINDINGS_SHA'],
            'Child source manifest differs')
    manifest = json.loads(raw, object_pairs_hook=unique)
    require(manifest['tested_source'] == SOURCE and
            0 < len(manifest['files']) <= 80 and
            sum(row['bytes'] for row in manifest['files']) <= 2 * 1024 ** 2,
            'Diagnostic source budget differs')
    require(len({(row['origin'], row['path']) for row in manifest['files']}) ==
            len(manifest['files']), 'Duplicate source binding')
    observed = {}
    for row in manifest['files']:
        require(row['origin'] in ['tested', 'harness'] and
                not Path(row['path']).is_absolute() and
                '..' not in Path(row['path']).parts, 'Unsafe bound source path')
        base = TESTED if row['origin'] == 'tested' else HARNESS
        data = read_file(base / row['path'], row['bytes'])
        require(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() ==
                row['sha256'], 'Child source bytes differ')
        observed[(row['origin'], row['path'])] = data
    require(read_file(TESTED / '.git/HEAD', 256).decode().strip() == SOURCE and
            read_file(HARNESS / '.git/HEAD', 256).decode().strip() ==
            os.environ['CENSUS_HARNESS_SHA'], 'Detached dual-source identity differs')
    return observed


def main(work):
    require(work.is_absolute() and work.is_dir() and not work.is_symlink() and
            Path.cwd() == work, 'Wrong census working directory')
    require(os.environ['CENSUS_TESTED_SOURCE'] == SOURCE, 'Wrong tested source')
    fd = int(os.environ['LIGHTEFT_DIAGNOSTIC_LOCK_FD'])
    held = os.fstat(fd)
    lock = Path(os.environ['LIGHTEFT_DIAGNOSTIC_LOCK_PATH'])
    named = lock.lstat()
    require(stat.S_ISREG(held.st_mode) and stat.S_ISREG(named.st_mode) and
            (held.st_dev, held.st_ino) == (named.st_dev, named.st_ino) and
            held.st_nlink == named.st_nlink == 1 and held.st_uid == os.getuid() and
            stat.S_IMODE(held.st_mode) == 0o600, 'Inherited CI lease differs')
    require(os.getsid(0) == os.getpid() and os.getpgid(0) == os.getpid(),
            'Isolated census session required')
    for name, value in [('RLIMIT_AS', 12884901888), ('RLIMIT_CPU', 60),
                        ('RLIMIT_FSIZE', 16 * 1024 ** 2), ('RLIMIT_CORE', 0)]:
        require(resource.getrlimit(getattr(resource, name)) == (value, value),
                'Census kernel limit differs: ' + name)
    state = dict(scope='ACTUAL_FRESH_NAMESPACE_CENSUS_ONLY',
                 tested_source=SOURCE, harness_source=os.environ['CENSUS_HARNESS_SHA'],
                 bindings_sha256=os.environ['CENSUS_BINDINGS_SHA'],
                 observer_completed=False, production_acceptance=False,
                 replay_invoked=False, checker_invocations=0,
                 historical_consumer_reconstruction=False,
                 inherited_lease=dict(path=str(lock), fd=fd, device=held.st_dev,
                                      inode=held.st_ino))
    try:
        source = authenticate()
        cache = work / 'absent-python-cache'
        require(not os.path.lexists(cache), 'Child cache prefix already exists')
        sys.pycache_prefix = str(cache)
        cl = types.ModuleType('_exact_tested_namespace_contract')
        cl.__file__ = str(TESTED / CONTRACT)
        exec(compile(source[('tested', CONTRACT)], cl.__file__, 'exec'), cl.__dict__)
        # Same root expansion/classification as tested runtime(), without its
        # Git subprocesses. Parent authenticates runtime/pins before and after.
        tool = Path(os.environ['LEAN_SYSROOT']).resolve(strict=True)
        require(Path(os.environ['LAKE']).resolve(strict=True) == tool / 'bin/lake',
                'Actual captured Lake differs')
        tools = {name: cl.digest(tool / 'bin' / name)
                 for name in ['lean', 'leanchecker', 'lake']}
        require(all(tools[name]['sha256'] == sha for name, sha in cl.TOOLS.items()),
                'Pinned tool bytes differ')
        raw = os.environ.get('LEAN_PATH', '')
        require(raw and all(raw.split(':')), 'Absent/empty Lake search root')
        roots = [Path(p).resolve() for p in raw.split(':')] + [tool / 'lib/lean']
        allowed = {'project': TESTED / '.lake/build/lib/lean',
                   'toolchain': tool / 'lib/lean'}
        allowed.update({'package:' + name: TESTED / '.lake/packages' / name /
                        '.lake/build/lib/lean' for name in cl.PINS})
        kinds = []
        for root in roots:
            matches = [kind for kind, path in allowed.items() if root == path.resolve()]
            require(len(matches) == 1, 'Unreviewed census search root')
            kinds.append(matches[0])
        state.update(actual_tools=tools, ordered_roots=list(map(str, roots)),
                     root_kinds=kinds, public_lean_path=raw,
                     namespace_before=cl.package_namespace(roots, kinds))
        authenticate()
        state['namespace_after'] = cl.package_namespace(roots, kinds)
        require(state['namespace_after'] == state['namespace_before'] and
                {name: cl.digest(tool / 'bin' / name) for name in tools} == tools,
                'Namespace/tool inputs changed during census')
        state['observer_completed'] = True
    except BaseException as error:
        state['failure'] = repr(error)
        raise
    finally:
        raw = (json.dumps(state, sort_keys=True, separators=(',', ':')) + '\n').encode()
        require(len(raw) <= MAX_RESULT, 'Complete census result exceeds unchanged1MiB bound')
        out = os.open(work / 'result.json', os.O_WRONLY | os.O_CREAT | os.O_EXCL |
                      os.O_NOFOLLOW, 0o600)
        with os.fdopen(out, 'wb') as stream:
            stream.write(raw); stream.flush(); os.fsync(stream.fileno())
    print('ACTUAL_FRESH_NAMESPACE_CENSUS_COMPLETE_NOT_ACCEPTANCE')


if __name__ == '__main__':
    require(sys.flags.isolated and sys.dont_write_bytecode and
            len(sys.argv) == 3 and sys.argv[1] == '--child',
            'Exact isolated Python census invocation required')
    main(Path(sys.argv[2]))
