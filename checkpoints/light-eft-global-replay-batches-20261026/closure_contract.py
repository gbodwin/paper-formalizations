"""UNEXECUTED source draft: finite same-run object handoff, not CI acceptance.

No workflow is wired to this module. Export refuses unless these new controls
are Git-exact and bound by every existing specification. HeaderProbe is run
only by export on a genuine producer; caller-supplied/synthetic graphs are not
an export API. Import executes no supplied code and emits no replay marker.
Transport, actual fresh launcher admission and final batch receipts remain
separate reviewed integration obligations. Nothing in this file has run.
"""
from pathlib import Path, PurePosixPath
import errno
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SPECS = ('light-eft-paid-focused-adapter-20261020',
         'light-eft-joint-flag-ci-extension-revision-20261019',
         'light-eft-canonical-output-adapter-20261020',
         'light-eft-paid-joint-bridge-ci-adapter-20261020',
         'light-eft-fair-bit-batch-ci-adapter-20261021')
PINS = {'mathlib': '5ed2965256430c3649e86755f9576b54eca72435',
        'plausible': '118aa17ee84656b8bd727fef7c458ee8c833385c',
        'LeanSearchClient': 'ddf04cf3949fa556442341e87d47f9f6e6074707',
        'importGraph': 'e928b72544873815af278d38681b31c0293588e3',
        'proofwidgets': '106ff4fafc74ef4ac99d81dbf3ab399118f497a5',
        'aesop': '355695d523e41d0554926416cba2a2b3544fbbc9',
        'Qq': '6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259',
        'batteries': 'f2effa3d803fda822b1f97b806c47cf2adfbcbc2',
        'Cli': 'e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204'}
TOOLS = {'lean': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
         'leanchecker': 'ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'}
QUALIFICATION = ('Newly observed same-run bytes; no authenticated cache/build '
                 'provenance and no historical or cross-job proof acceptance')
CHUNK = 64 * 1024
PART = 4 * 1024 * 1024
JSON_LIMIT = 16 * 1024 * 1024
# Explicit proposed transfer bound, not a claim about platform capacity. An
# actual closure above this bound must be reported and reviewed, never omitted.
PAYLOAD_LIMIT = 1024 * 1024 * 1024
CONTROL_NAMES = ('closure_contract.py', 'HeaderProbe.lean', 'targets.json',
                 'strict_download.cjs', 'package.json', 'package-lock.json', 'qualification_adapter.py')
SUFFIXES = ('', '.server', '.private', '.ir.sig', '.ir')
ACQUISITION_POLICY = dict(
    schema='PROJECT_TRANSFER_PINNED_DEPENDENCIES_EXACT_PRODUCER_BYTES_V1',
    project='project_transfer', package='package_reacquire_exact_producer_bytes',
    toolchain='toolchain_reverify', total_transfer_limit_bytes=PAYLOAD_LIMIT,
    ordinary_acquisition_is_not_cache_provenance=True)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def no_duplicates(pairs):
    result = {}
    for k, v in pairs:
        require(k not in result, 'Duplicate JSON key: ' + k)
        result[k] = v
    return result


def read_json(path):
    p = Path(path)
    require(p.is_file() and not p.is_symlink() and p.stat().st_size <= JSON_LIMIT,
            'Unsafe/oversized JSON: ' + str(p))
    return json.loads(p.read_bytes(), object_pairs_hook=no_duplicates)


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def signature(s):
    return (s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size,
            s.st_mtime_ns, s.st_ctime_ns)


def digest(path):
    p = Path(path)
    fd = os.open(p, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd)
        require(stat.S_ISREG(before.st_mode), 'Not a regular file: ' + str(p))
        h = hashlib.sha256()
        while data := os.read(fd, CHUNK):
            h.update(data)
        require(signature(before) == signature(os.fstat(fd)) ==
                signature(p.lstat()), 'File changed while hashing: ' + str(p))
        return dict(bytes=before.st_size, sha256=h.hexdigest())
    finally:
        os.close(fd)


def git(*args, cwd=ROOT):
    return subprocess.run(['git', *args], cwd=cwd, check=True,
                          capture_output=True, timeout=10).stdout


def controls():
    paths = [HERE / n for n in CONTROL_NAMES]
    rows = {}
    for p in paths:
        rel = p.relative_to(ROOT).as_posix()
        require(not p.is_symlink() and p.read_bytes() == git('show', 'HEAD:' + rel),
                'Control differs from exact Git source: ' + rel)
        rows[rel] = dict(path=rel, **digest(p))
    for name in SPECS:
        p = ROOT / 'checkpoints' / name / 'ci-spec.json'
        require(p.read_bytes() == git('show', 'HEAD:' + p.relative_to(ROOT).as_posix()),
                'Specification differs from Git')
        bound = {r['path']: r for r in read_json(p)['engine_files']}
        require(all(bound.get(k) == v for k, v in rows.items()),
                'New handoff controls are not bound in all five specifications')
    return rows


def identity(role):
    e = dict(os.environ)
    head = git('rev-parse', 'HEAD').decode().strip()
    require(e.get('GITHUB_ACTIONS') == 'true' and
            e.get('GITHUB_REPOSITORY') == 'gbodwin/paper-formalizations', 'Not project CI')
    require(re.fullmatch('[0-9a-f]{40}', head) and e.get('GITHUB_SHA') == head and
            e.get('LIGHTEFT_EXPECTED_SOURCE') == head, 'Exact event/source differs')
    require(all(e.get(k, '').isdecimal() and int(e[k]) > 0
                for k in ['GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']), 'Invalid run/attempt')
    paths = {'full': '.github/workflows/lean.yml',
             'global_replay': '.github/workflows/light-eft-global-replay.yml'}
    require(role in paths and e.get('LIGHTEFT_VALIDATION_ROLE') == role and
            e.get('GITHUB_JOB') == 'check' and e.get('LEAN_NUM_THREADS') == '1',
            'Wrong actual role/job/worker setting')
    ref = e.get('GITHUB_REF', '')
    require(e.get('GITHUB_EVENT_NAME') in ['push', 'pull_request', 'workflow_dispatch'] and
            ref != 'refs/heads/light-eft-spanners-checkpoints', 'Wrong trigger/ref')
    require(e.get('GITHUB_WORKFLOW') == 'Lean' and e.get('GITHUB_WORKFLOW_SHA') == head and
            e.get('GITHUB_WORKFLOW_REF') == 'gbodwin/paper-formalizations/.github/workflows/lean.yml@' + ref,
            'Caller workflow differs')
    require(e.get('LIGHTEFT_JOB_WORKFLOW_REPOSITORY') == e['GITHUB_REPOSITORY'] and
            e.get('LIGHTEFT_JOB_WORKFLOW_PATH') == paths[role] and
            e.get('LIGHTEFT_JOB_WORKFLOW_SHA') == head and
            e.get('LIGHTEFT_JOB_WORKFLOW_REF') in
            [e['GITHUB_REPOSITORY'] + '/' + paths[role] + '@' + ref,
             e['GITHUB_REPOSITORY'] + '/' + paths[role] + '@' + head],
            'Actual job workflow differs')
    return {k: e[k] for k in ['GITHUB_REPOSITORY', 'GITHUB_SHA', 'GITHUB_REF',
                              'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_JOB',
                              'LIGHTEFT_VALIDATION_ROLE']}


def runtime():
    tool = Path(os.environ['LEAN_SYSROOT']).resolve(strict=True)
    require(Path(os.environ['LAKE']).resolve(strict=True) == tool / 'bin/lake',
            'Not the actual admitted Lake environment')
    tools = {n: digest(tool / 'bin' / n) for n in ['lean', 'leanchecker', 'lake']}
    require(all(tools[n]['sha256'] == h for n, h in TOOLS.items()), 'Pinned tool differs')
    require((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0',
            'Toolchain contract differs')
    for name, rev in PINS.items():
        p = ROOT / '.lake/packages' / name
        no_symlink_parents(p)
        require(git('rev-parse', 'HEAD', cwd=p).decode().strip() == rev and
                not git('status', '--porcelain', '--untracked-files=no', cwd=p),
                'Package source pin/cleanliness differs: ' + name)
    raw = os.environ.get('LEAN_PATH', '')
    require(raw and all(raw.split(':')), 'Absent/empty Lake search root')
    paths = [Path(p).resolve() for p in raw.split(':')] + [tool / 'lib/lean']
    kinds = []
    allowed = {'project': ROOT / '.lake/build/lib/lean', 'toolchain': tool / 'lib/lean'}
    allowed.update({'package:' + n: ROOT / '.lake/packages' / n / '.lake/build/lib/lean'
                    for n in PINS})
    for path in paths:
        found = [k for k, v in allowed.items() if path == v.resolve()]
        require(len(found) == 1, 'Unreviewed search root: ' + str(path))
        kinds.append(found[0])
    return tool, tools, paths, kinds


def module_path(name):
    require(isinstance(name, str) and name and not any(c in name for c in '/\\\0\r\n'),
            'Unsafe module name')
    parts = name.split('.')
    require(all(p and p not in ['.', '..'] for p in parts), 'Empty module component')
    return PurePosixPath(*parts).as_posix() + '.olean'


def targets():
    plan = read_json(HERE / 'targets.json')
    require(plan['target_count'] == 567 and len(plan['batches']) == 3 and
            [x['count'] for x in plan['batches']] == [189, 189, 189], 'Target partition differs')
    rows = [r for batch in plan['batches'] for r in batch['targets']]
    names = [r['module'] for r in rows]
    require(len(names) == len(set(names)) == 567 and
            hashlib.sha256(('\n'.join(names) + '\n').encode()).hexdigest() ==
            'aacaaa23315dda4923b1407fc1336bffc7feb541c392e5eb1fbd1e6de6a1ccda',
            'Original ordered target coverage differs')
    for i, batch in enumerate(plan['batches']):
        part = names[i * 189:(i + 1) * 189]
        require(batch['batch'] == i + 1 and batch['offset'] == i * 189 and
                len(batch['targets']) == 189 and
                batch['ordered_module_sha256'] == hashlib.sha256(('\n'.join(part) + '\n').encode()).hexdigest(),
                'Exact contiguous batch descriptor differs')
    for row in rows:
        require(git('rev-parse', 'HEAD:' + row['path']).decode().strip() == row['git_blob_oid'],
                'Target source OID differs: ' + row['path'])
    return names


def validate_graph(graph, names):
    require(graph['schema'] == 'LEAN_4_34_SERIALIZED_HEADER_GRAPH_V1', 'Wrong header schema')
    require(graph['target_count'] == len(names) and len(names) in [189, 567], 'Probe scope differs')
    nodes = graph['nodes']
    require(0 < len(nodes) <= 32768 and len(graph['census']) <= 200000, 'Graph bound exceeded')
    by_name = {n['module']: n for n in nodes}
    require(len(by_name) == len(nodes), 'Duplicate module header')
    for row in graph['census']:
        require(set(row) == {'module', 'file'} and type(row['file']) is str and Path(row['file']).is_absolute(),
                'Invalid object-name census row')
        module_path(row['module'])
    require([x['target'] for x in graph['expansions']] == names, 'Target order differs')
    census_names = {x['module'] for x in graph['census']}
    seeds = set()
    for row in graph['expansions']:
        expected = {n for n in census_names if n == row['target'] or n.startswith(row['target'] + '.')}
        require(expected and len(row['modules']) == len(set(row['modules'])) and
                set(row['modules']) == expected, 'Checker prefix expansion differs')
        seeds.update(expected)
    reached = set()
    pending = list(seeds)
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        require(name in by_name, 'Missing actual import header: ' + name)
        module_path(name)
        n = by_name[name]
        require(set(n) == {'module', 'file', 'source', 'is_module', 'imports', 'header_parts'},
                'Unknown/missing header fields')
        require(type(n['is_module']) is bool, 'Invalid module-system flag')
        headers = n['header_parts']
        require(isinstance(headers, list) and [p['suffix'] for p in headers] in
                [[''], ['', '.server'], ['', '.server', '.private']], 'Invalid companion header prefix')
        require(all(set(p) == {'suffix', 'is_module', 'imports'} and
                    p['is_module'] is n['is_module'] and p['imports'] == n['imports']
                    for p in headers), 'Compiled companion import headers disagree')
        reached.add(name)
        for imp in n['imports']:
            require(set(imp) == {'module', 'is_exported', 'is_meta', 'import_all'} and
                    all(type(imp[k]) is bool for k in ['is_exported', 'is_meta', 'import_all']),
                    'Invalid actual import descriptor')
            module_path(imp['module'])
            pending.append(imp['module'])
    require(reached == set(by_name), 'Extraneous/unreachable object graph')
    # The genuine import relation is a DAG. Detect malformed cyclic cache data
    # without relying on Python recursion or treating visited nodes as proof.
    state = {}
    for start in by_name:
        if state.get(start) == 2:
            continue
        state[start] = 1; stack = [(start, iter(i['module'] for i in by_name[start]['imports']))]
        while stack:
            name, edges = stack[-1]
            child = next(edges, None)
            if child is None:
                state[name] = 2; stack.pop(); continue
            require(state.get(child) != 1, 'Cyclic serialized import graph')
            if state.get(child) != 2:
                state[child] = 1
                stack.append((child, iter(i['module'] for i in by_name[child]['imports'])))
    return by_name, seeds


def chosen_root(name, roots):
    prefix = name.split('.')[0]
    for i, root in enumerate(roots):
        if (root / prefix).is_dir() or (root / (prefix + '.olean')).exists():
            return i
    raise ValueError('No original prefix root for ' + name)


def source_binding(path, tool):
    p = Path(path).resolve(strict=True)
    bases = [('toolchain', tool / 'src/lean')]
    bases += [('package:' + n, ROOT / '.lake/packages' / n) for n in PINS]
    bases += [('project', ROOT)]
    for kind, base in bases:
        if p.is_relative_to(base.resolve()):
            rel = p.relative_to(base.resolve()).as_posix()
            row = dict(kind=kind, path=rel, **digest(p))
            if kind != 'toolchain':
                raw = git('show', 'HEAD:' + rel, cwd=base)
                require(len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256'],
                        'Source differs from pinned Git bytes: ' + str(p))
                row['git_blob_oid'] = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            return row
    raise ValueError('Source outside exact project/package/toolchain roots: ' + str(p))


def create(path, raw):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'wb') as f:
        f.write(raw)
        f.flush()
        os.fsync(f.fileno())


def part_path(base, suffix):
    return base.with_suffix(suffix) if suffix.startswith('.ir') else Path(str(base) + suffix)


def observation(path):
    p = Path(path)
    before = signature(p.lstat())
    row = digest(p)
    require(before == signature(p.lstat()), 'Snapshot changed: ' + str(p))
    return dict(identity=list(before), **row)


def snapshot(paths):
    return {str(p): observation(p) for p in sorted(set(map(Path, paths)), key=str)}


def write_snapshot(folder, values):
    folder.mkdir(mode=0o700, exist_ok=False)
    rows = sorted(values.items()); index = []; whole = hashlib.sha256()
    for key, value in rows:
        whole.update(encoded([key, value]))
    for offset in range(0, len(rows), 64):
        name = 'chunk-%05d.json' % (offset // 64)
        raw = encoded(rows[offset:offset + 64])
        require(len(raw) <= PART, 'Snapshot metadata chunk exceeds bound')
        create(folder / name, raw)
        index.append(dict(path=name, count=len(rows[offset:offset + 64]), **digest(folder / name)))
    result = dict(count=len(rows), ordered_records_sha256=whole.hexdigest(), chunks=index)
    create(folder / 'index.json', encoded(result))
    return result


def prefixes(roots):
    result = []
    for root in roots:
        if not root.exists():
            result.append([])
            continue
        require(root.is_dir() and not root.is_symlink(), 'Unsafe search root')
        names = []
        for p in root.iterdir():
            if p.is_dir():
                names.append(p.name)
            elif p.name.endswith('.olean'):
                names.append(p.name[:-6])
        result.append(sorted(set(names)))
    return result


def chosen_prefix(name, claims):
    prefix = name.split('.')[0]
    for i, row in enumerate(claims):
        if prefix in row:
            return i
    raise ValueError('Missing effective namespace prefix: ' + name)


def selection(graph, selected_names):
    by_name = {n['module']: n for n in graph['nodes']}
    expansions = [r for r in graph['expansions'] if r['target'] in set(selected_names)]
    require([r['target'] for r in expansions] == selected_names, 'Selected target order differs')
    seeds = {n for r in expansions for n in r['modules']}
    reached = set(); pending = list(seeds)
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        require(name in by_name, 'Missing selected dependency: ' + name)
        reached.add(name)
        pending.extend(i['module'] for i in by_name[name]['imports'])
    imported = {i['module'] for n in reached for i in by_name[n]['imports']}
    return reached, seeds, imported, expansions


def required_suffixes(name, node, available, seeds, imported):
    require(set(available) == set(SUFFIXES) and available[''] is not None,
            'Incomplete explicit companion availability')
    result = ['']
    if name in imported and node['is_module']:
        require(available['.server'] is not None and available['.private'] is not None,
                'Module-system import requires server/private: ' + name)
        result += ['.server', '.private']
    elif name in seeds and available['.server'] is not None:
        result += ['.server']
        if available['.private'] is not None:
            result += ['.private']
    if name in imported and available['.ir.sig'] is not None:
        require(available['.ir'] is not None, 'IR signature without IR: ' + name)
        result += ['.ir.sig', '.ir']
    return result


def acquisition(kind):
    require(kind in {'project', 'toolchain', *('package:' + n for n in PINS)},
            'Unknown object acquisition owner')
    return ACQUISITION_POLICY['package' if kind.startswith('package:') else kind]


def package_namespace(roots, kinds):
    """Finite root/absence and prefix observation, under external no-writer scope.

    Directory timestamps are not a lease or hostile-writer proof. An absent
    root retains its first missing suffix and existing ancestor identity; no
    mkdir, error-to-absence conversion or dropping of semantic slots occurs.
    """
    result = []
    def directory_identity(path):
        s = path.lstat()
        require(stat.S_ISDIR(s.st_mode), 'Unsafe package namespace ancestor')
        return [s.st_dev, s.st_ino, s.st_uid, s.st_gid,
                stat.S_IMODE(s.st_mode), s.st_nlink]
    for index, (root, kind) in enumerate(zip(roots, kinds, strict=True)):
        if not kind.startswith('package:'):
            continue
        require(root.is_absolute(), 'Relative package namespace root')
        no_symlink_parents(root)
        current = root; suffix = []
        while True:
            try:
                observed = directory_identity(current)
                break
            except FileNotFoundError as error:
                require(error.errno == errno.ENOENT and current != current.parent,
                        'Package namespace absence is not ENOENT')
                suffix.insert(0, current.name); current = current.parent
        row = dict(root=index, kind=kind, anchor=str(current),
                   anchor_identity=observed, missing_suffix=suffix,
                   state='absent' if suffix else 'directory',
                   prefixes=prefixes([root])[0])
        # Reobserve the first missing component, or the actual present root.
        if suffix:
            try:
                (current / suffix[0]).lstat()
            except FileNotFoundError as error:
                require(error.errno == errno.ENOENT, 'Package namespace absence changed')
            else:
                raise ValueError('Absent package namespace appeared during observation')
        require(directory_identity(current) == observed, 'Package namespace identity changed')
        result.append(row)
    return result


def package_census(graph, kinds):
    """Compare native package-name observations across relocated exact roots.

    Sorting removes filesystem enumeration order only. Duplicate census rows
    and duplicate search-root slots remain represented; no object bytes gain
    trust from being named here.
    """
    paths = graph['search_path']
    require(len(paths) == len(kinds), 'Package census search-root slots differ')
    roots = [PurePosixPath(p) for p in paths]
    require(all(type(p) is str and r.is_absolute() and p == r.as_posix() and
                '..' not in r.parts for p, r in zip(paths, roots, strict=True)),
            'Noncanonical native package census root')
    result = []
    for row in graph['census']:
        path = PurePosixPath(row['file'])
        for index, (root, kind) in enumerate(zip(roots, kinds, strict=True)):
            if kind.startswith('package:') and path.is_relative_to(root):
                relative = path.relative_to(root).as_posix()
                require(relative == module_path(row['module']),
                        'Package census module/file mapping differs')
                result.append([index, row['module'], relative])
    return sorted(result)


def reacquired_package_paths(manifest, nodes, roots, kinds):
    """Verify ALL producer-declared package families, never cache provenance.

    Required companions remain explicit manifest rows. The complete five-slot
    availability observation also rejects missing/extra optional companions
    which could change a native read set. No package file is installed here.
    """
    paths = []
    for name in sorted(nodes):
        obj = manifest['objects'][name]
        if not kinds[obj['root']].startswith('package:'):
            continue
        base = roots[obj['root']] / obj['relative']; actual = {}
        for suffix in SUFFIXES:
            path = part_path(base, suffix); no_symlink_parents(path)
            try:
                path.lstat()
            except FileNotFoundError as error:
                require(error.errno == errno.ENOENT, 'Package companion absence is not ENOENT')
                actual[suffix] = None
            else:
                actual[suffix] = digest(path)
            if actual[suffix] is not None:
                paths.append(path)
        require(actual == obj['available'],
                'Reacquired package companion presence/bytes differ: ' + name)
    return sorted(set(paths), key=str)


def run_probe(folder, names, tool, ci):
    folder.mkdir(mode=0o700, exist_ok=False)
    request = folder / 'request.json'; output = folder / 'headers.json'
    create(request, encoded(dict(targets=names)))
    command = [str(tool / 'bin/lean'), '--run', str(HERE / 'HeaderProbe.lean'), str(request), str(output)]
    began = time.monotonic_ns(); result = None; failure = None; failure_exit = None; timed_out = False
    try:
        with (folder / 'stdout.log').open('xb') as out, (folder / 'stderr.log').open('xb') as err:
            result = subprocess.run(command, cwd=ROOT, check=True, stdout=out, stderr=err, timeout=90)
        require(all((folder / n).stat().st_size <= JSON_LIMIT for n in ['stdout.log', 'stderr.log']),
                'Metadata logs exceed bound; complete bytes retained')
        graph = read_json(output)
        validate_graph(graph, names)
        return graph
    except BaseException as error:
        failure = repr(error)
        failure_exit = getattr(error, 'returncode', None)
        timed_out = isinstance(error, subprocess.TimeoutExpired)
        raise
    finally:
        record = dict(schema='ACTUAL_METADATA_CAPTURE_V1', command=command, CI_identity=ci,
                      started_ns=began, ended_ns=time.monotonic_ns(),
                      exit=failure_exit if result is None else result.returncode, failure=failure,
                      timed_out=timed_out,
                      subprocess_run_manages_only_owned_direct_child=True,
                      no_global_reap_or_kernel_acceptance_claim=True)
        record['files'] = {n: digest(folder / n) for n in ['request.json', 'headers.json', 'stdout.log', 'stderr.log']
                           if (folder / n).is_file()}
        create(folder / 'capture.json', encoded(record))


def graph_fingerprint(graph):
    value = dict(graph)
    value['census'] = sorted(graph['census'], key=lambda r: (r['module'], r['file']))
    value['nodes'] = sorted(graph['nodes'], key=lambda r: r['module'])
    value['expansions'] = [dict(target=r['target'], modules=sorted(r['modules']))
                           for r in graph['expansions']]
    return hashlib.sha256(encoded(value)).hexdigest()


def inventory(graph, names, tool, roots, kinds):
    nodes, _ = validate_graph(graph, names)
    claims = prefixes(roots)
    objects = {}; sources = {}; paths = [HERE / n for n in CONTROL_NAMES]
    paths += [tool / 'bin' / n for n in ['lean', 'leanchecker', 'lake']]
    for name, node in sorted(nodes.items()):
        index = chosen_prefix(name, claims); relative = module_path(name)
        base = roots[index] / relative
        require(base.resolve(strict=True) == Path(node['file']).resolve(strict=True),
                'Serialized header did not use the effective namespace root')
        availability = {}
        for suffix in SUFFIXES:
            p = part_path(base, suffix)
            # lexists distinguishes a dangling symlink from a genuine absence.
            availability[suffix] = digest(p) if os.path.lexists(p) else None
            if availability[suffix] is not None:
                paths.append(p)
        expected_headers = ['']
        if availability['.server'] is not None:
            expected_headers.append('.server')
            if availability['.private'] is not None:
                expected_headers.append('.private')
        require([p['suffix'] for p in node['header_parts']] == expected_headers,
                'Header capture/companion presence changed')
        objects[name] = dict(root=index, relative=relative, available=availability)
        sources[name] = source_binding(node['source'], tool)
        paths.append(Path(node['source']).resolve(strict=True))
    reached, seeds, imported, _ = selection(graph, names)
    for name in reached:
        required_suffixes(name, nodes[name], objects[name]['available'], seeds, imported)
    return objects, sources, claims, paths


def source_path(row, tool):
    kind = row['kind']
    require(kind in {'project', 'toolchain', *('package:' + n for n in PINS)},
            'Unknown source owner')
    base = tool / 'src/lean' if kind == 'toolchain' else ROOT if kind == 'project' else ROOT / '.lake/packages' / kind[8:]
    return base / safe_relative(row['path'])


def copy_parts(path, bundle, index, expected):
    require(observation(path) == expected, 'Object changed before copying')
    row = []; copied = 0; whole = hashlib.sha256()
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        require(list(signature(os.fstat(fd))) == expected['identity'], 'Opened object identity differs')
        while copied < expected['bytes']:
            rel = 'parts/f%06d-p%06d.bin' % (index, len(row))
            part_fd = os.open(bundle / rel, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
            h = hashlib.sha256(); count = 0
            with os.fdopen(part_fd, 'wb') as stream:
                while count < min(PART, expected['bytes'] - copied):
                    data = os.read(fd, min(CHUNK, PART - count, expected['bytes'] - copied - count))
                    require(data, 'Object truncated during export')
                    stream.write(data); h.update(data); whole.update(data); count += len(data)
                stream.flush(); os.fsync(stream.fileno())
            row.append(dict(path=rel, bytes=count, sha256=h.hexdigest())); copied += count
        require(not os.read(fd, 1) and whole.hexdigest() == expected['sha256'] and
                list(signature(os.fstat(fd))) == expected['identity'], 'Object changed during copying')
    finally:
        os.close(fd)
    require(observation(path) == expected, 'Object changed after copying')
    return row


def seal_manifest(bundle, manifest):
    """Hash-index complete metadata; never split the total payload allowance.

    The graph remains one bounded JSON object. Objects/sources/file rows retain
    all fields, list order and duplicate file rows in fixed <=64-record chunks.
    Only their location changes; one same-run producer output binds the index.
    """
    directory = bundle / 'metadata'; directory.mkdir(mode=0o700, exist_ok=False)
    metadata = {}; metadata_bytes = 0; records_written = 0; sequence = 0
    attempts = bundle.parent / 'metadata-attempts'; attempts.mkdir(mode=0o700, exist_ok=False)
    def attempted(phase, details):
        nonlocal sequence
        sequence += 1
        record = dict(schema='EXACT_METADATA_SERIALIZATION_ATTEMPT_V1',
                      status='PARTIAL_ATTEMPT_NOT_SEALED_OR_ACCEPTED', phase=phase,
                      sequence=sequence, metadata_records_committed=records_written,
                      project_payload_bytes=manifest['payload_bytes'],
                      metadata_committed_bytes=metadata_bytes,
                      index_bytes=None, index_sha256=None, exact_complete_total_bytes=None,
                      unknown_fields='Index and complete total not yet computed',
                      total_limit_bytes=PAYLOAD_LIMIT, per_JSON_limit_bytes=JSON_LIMIT,
                      record_limit_bytes=PART, **details)
        raw = encoded(record)
        require(len(raw) <= PART, 'Bounded metadata attempt evidence exceeds part allowance')
        create(attempts / ('attempt-%05d.json' % sequence), raw)
    def put(name, value, ceiling):
        nonlocal metadata_bytes, records_written
        raw = encoded(value)
        attempted('record-before-ceilings', dict(
                  record_name='metadata/' + name, attempted_encoded_bytes=len(raw),
                  attempted_encoded_sha256=hashlib.sha256(raw).hexdigest(),
                  attempted_record_limit_bytes=ceiling,
                  metadata_bytes_if_written=metadata_bytes + len(raw),
                  total_lower_bound_without_index=manifest['payload_bytes'] + metadata_bytes + len(raw)))
        require(len(raw) <= ceiling, 'Metadata record exceeds unchanged bound: ' + name)
        require(metadata_bytes + len(raw) + manifest['payload_bytes'] <= PAYLOAD_LIMIT,
                'Metadata plus project payload exceeds unchanged total transfer allowance')
        path = directory / name; create(path, raw); row = dict(path='metadata/' + name, **digest(path))
        metadata_bytes += len(raw); records_written += 1
        return row
    metadata['graph'] = put('graph.json', manifest['graph'], JSON_LIMIT)
    for field, maximum in [('objects', 32768), ('sources', 32768), ('files', 5 * 32768)]:
        value = manifest[field]
        rows = value if field == 'files' else sorted(value.items())
        attempted('collection-before-count-ceiling', dict(
                  collection=field, observed_count=len(rows), maximum_count=maximum,
                  attempted_encoded_bytes=None, attempted_encoded_sha256=None,
                  encoding_status='Not encoded; count is checked before bounded chunks'))
        require(0 < len(rows) <= maximum, 'Metadata collection count exceeds graph bound')
        chunks = []
        for offset in range(0, len(rows), 64):
            chunk = rows[offset:offset + 64]
            row = put('%s-%05d.json' % (field, offset // 64), chunk, PART)
            chunks.append(dict(count=len(chunk), **row))
        metadata[field] = dict(count=len(rows), chunks=chunks)
    index = {k: v for k, v in manifest.items() if k not in metadata}
    index.update(schema='LIGHT_SAME_RUN_REPLAY_HANDOFF_V3_INDEXED_METADATA',
                 metadata=metadata, metadata_bytes=metadata_bytes)
    raw = encoded(index)
    profile = dict(schema='EXACT_PROJECT_AND_METADATA_TRANSFER_PROFILE_V1',
                   status='COMPLETE_SERIALIZED_COUNTS_BEFORE_FINAL_CEILINGS',
                   project_payload_bytes=manifest['payload_bytes'], metadata_bytes=metadata_bytes,
                   index_bytes=len(raw), total_bytes=manifest['payload_bytes'] + metadata_bytes + len(raw),
                   total_limit_bytes=PAYLOAD_LIMIT, per_JSON_limit_bytes=JSON_LIMIT,
                   index_sha256=hashlib.sha256(raw).hexdigest(),
                   required_companions=len(manifest['files']), acquisition_policy=ACQUISITION_POLICY)
    # Refusal evidence lives outside the bundle; no failed export is promoted.
    create(bundle.parent / 'transfer-profile.json', encoded(profile))
    require(len(raw) <= JSON_LIMIT and profile['total_bytes'] <= PAYLOAD_LIMIT,
            'Indexed metadata/project handoff exceeds unchanged total or JSON allowance')
    create(bundle / 'manifest.json', raw)
    return dict(manifest_sha256=profile['index_sha256'],
                total_transfer_bytes=profile['total_bytes'], metadata_bytes=metadata_bytes)


def load_manifest(bundle, expected_sha):
    """Authenticate index and every metadata byte before reconstructing rows."""
    path = bundle / 'manifest.json'; no_symlink_parents(path); index_before = observation(path)
    require(index_before['sha256'] == expected_sha, 'Manifest index digest differs')
    index = read_json(path)
    require(observation(path) == index_before and set(index) == {
            'schema', 'producer', 'controls', 'tools', 'packages', 'root_kinds',
            'prefix_claims', 'payload_bytes', 'qualification', 'snapshot', 'captures',
            'acquisition_policy', 'metadata', 'metadata_bytes'} and
            index['schema'] == 'LIGHT_SAME_RUN_REPLAY_HANDOFF_V3_INDEXED_METADATA' and
            type(index['payload_bytes']) is int and 0 < index['payload_bytes'] <= PAYLOAD_LIMIT and
            type(index['metadata_bytes']) is int and 0 < index['metadata_bytes'] <= PAYLOAD_LIMIT,
            'Unknown/oversized indexed handoff fields')
    records = index['metadata']
    require(type(records) is dict and set(records) == {'graph', 'objects', 'sources', 'files'},
            'Incomplete metadata collection index')
    paths = [path]; seen = set(); metadata_bytes = 0
    def get(row, name, ceiling):
        nonlocal metadata_bytes
        require(type(row) is dict and set(row) == {'path', 'bytes', 'sha256'} and
                row['path'] == 'metadata/' + name and row['path'] not in seen,
                'Metadata path/duplicate differs from fixed index')
        binding({k: row[k] for k in ['bytes', 'sha256']})
        require(row['bytes'] <= ceiling, 'Indexed metadata record exceeds finite bound')
        p = bundle / row['path']; no_symlink_parents(p); before = observation(p)
        require({k: before[k] for k in ['bytes', 'sha256']} ==
                {k: row[k] for k in ['bytes', 'sha256']}, 'Authenticated metadata bytes differ')
        metadata_bytes += row['bytes']
        require(metadata_bytes + index['payload_bytes'] + index_before['bytes'] <= PAYLOAD_LIMIT,
                'Metadata/project bytes exceed unchanged total transfer allowance')
        value = read_json(p)
        require(observation(p) == before, 'Metadata changed while decoding')
        seen.add(row['path']); paths.append(p)
        return value
    values = {'graph': get(records['graph'], 'graph.json', JSON_LIMIT)}
    for field, maximum in [('objects', 32768), ('sources', 32768), ('files', 5 * 32768)]:
        record = records[field]
        require(type(record) is dict and set(record) == {'count', 'chunks'} and
                type(record['count']) is int and 0 < record['count'] <= maximum and
                type(record['chunks']) is list and len(record['chunks']) ==
                (record['count'] + 63) // 64, 'Metadata collection index count differs')
        rows = []
        for number, chunk in enumerate(record['chunks']):
            require(type(chunk) is dict and set(chunk) == {'path', 'count', 'bytes', 'sha256'} and
                    type(chunk['count']) is int and chunk['count'] ==
                    min(64, record['count'] - len(rows)), 'Metadata chunk count/order differs')
            row = {k: chunk[k] for k in ['path', 'bytes', 'sha256']}
            part = get(row, '%s-%05d.json' % (field, number), PART)
            require(type(part) is list and len(part) == chunk['count'], 'Metadata chunk rows differ')
            rows.extend(part)
        require(len(rows) == record['count'], 'Metadata collection incomplete')
        if field == 'files':
            values[field] = rows  # Keep every list ordinal; never deduplicate.
        else:
            require(all(type(row) is list and len(row) == 2 and type(row[0]) is str for row in rows),
                    'Metadata mapping row differs')
            keys = [row[0] for row in rows]
            require(keys == sorted(set(keys)), 'Metadata mapping duplicate/order differs')
            values[field] = dict(rows)
    directory = bundle / 'metadata'; no_symlink_parents(directory)
    require(directory.is_dir(), 'Missing metadata directory')
    actual = set()
    for p in directory.iterdir():
        s = p.lstat()
        require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1 and not p.is_symlink(),
                'Unsafe/unlisted metadata entry')
        actual.add('metadata/' + p.name)
        require(len(actual) <= 1 + (32768 + 63) // 64 * 2 + (5 * 32768 + 63) // 64,
                'Metadata directory entry bound exceeded')
    require(actual == seen and metadata_bytes == index['metadata_bytes'] and
            observation(path) == index_before, 'Hidden/missing/changed indexed metadata')
    manifest = {k: v for k, v in index.items() if k not in ['metadata', 'metadata_bytes']}
    manifest.update(schema='LIGHT_SAME_RUN_REPLAY_HANDOFF_V3', **values)
    return manifest, paths, metadata_bytes + index_before['bytes']


def export_body(destination, ci, bound, names, tool, tools, roots, kinds):
    capture = destination / 'capture'; capture.mkdir(mode=0o700)
    bundle = destination / 'bundle'; bundle.mkdir(mode=0o700)
    (bundle / 'parts').mkdir(mode=0o700)
    graph = run_probe(capture / 'discovery', names, tool, ci)
    require([str(p.resolve()) for p in map(Path, graph['search_path'])] == list(map(str, roots)),
            'Probe and actual Lake root ordering differ')
    nodes, _ = validate_graph(graph, names)
    objects, sources, claims, input_paths = inventory(graph, names, tool, roots, kinds)
    before = snapshot(input_paths)
    before_index = write_snapshot(capture / 'inputs-before', before)
    confirmed = run_probe(capture / 'confirmed', names, tool, ci)
    require(graph_fingerprint(confirmed) == graph_fingerprint(graph), 'Headers/namespace census changed across snapshot')
    require(snapshot(input_paths) == before and prefixes(roots) == claims, 'Inputs changed across header capture')
    _, seeds, imported, _ = selection(graph, names)
    files = []; payload_bytes = 0
    for name, node in sorted(nodes.items()):
        obj = objects[name]; index = obj['root']; base = roots[index] / obj['relative']
        for suffix in required_suffixes(name, node, obj['available'], seeds, imported):
            path = part_path(base, suffix); binding = obj['available'][suffix]
            require(observation(path) == before[str(path)], 'Object changed before sealing')
            row = dict(module=name, suffix=suffix, root=index,
                       relative=path.relative_to(roots[index]).as_posix(),
                       acquisition=acquisition(kinds[index]),
                       transfer=kinds[index] == 'project', chunks=[], **binding)
            if row['transfer']:
                require(payload_bytes + binding['bytes'] <= PAYLOAD_LIMIT,
                        'Exact required closure exceeds proposed transfer bound: ' + str(path))
                row['chunks'] = copy_parts(path, bundle, len(files), before[str(path)])
                payload_bytes += binding['bytes']
            files.append(row)
    sealed = run_probe(capture / 'sealed', names, tool, ci)
    require(graph_fingerprint(sealed) == graph_fingerprint(graph), 'Headers/census changed during payload sealing')
    final_objects, final_sources, final_claims, final_paths = inventory(sealed, names, tool, roots, kinds)
    require(final_objects == objects and final_sources == sources and final_claims == claims and
            set(map(str, final_paths)) == set(map(str, input_paths)),
            'Companion presence/absence/source census changed during sealing')
    require(snapshot(input_paths) == before and prefixes(roots) == claims and
            identity('full') == ci and controls() == bound and runtime()[1:] == (tools, roots, kinds),
            'No-writer snapshot/source/runtime correlation failed')
    after_index = write_snapshot(capture / 'inputs-after', snapshot(input_paths))
    require(before_index['ordered_records_sha256'] == after_index['ordered_records_sha256'],
            'Sealed snapshot correlation differs')
    manifest = dict(schema='LIGHT_SAME_RUN_REPLAY_HANDOFF_V3', producer=ci, controls=bound,
                    acquisition_policy=ACQUISITION_POLICY,
                    tools=tools, packages=PINS, root_kinds=kinds, graph=graph, sources=sources,
                    objects=objects, prefix_claims=claims, files=files, payload_bytes=payload_bytes,
                    qualification=QUALIFICATION, snapshot=dict(before=before_index, after=after_index,
                    observed_inputs_unchanged=True, graph_sha256=graph_fingerprint(graph),
                    external_no_writer_required=True, hostile_writer_absence_not_proved=True),
                    captures=[read_json(capture / n / 'capture.json') for n in ['discovery', 'confirmed', 'sealed']])
    index_binding = seal_manifest(bundle, manifest)
    summary = dict(**index_binding, payload_bytes=payload_bytes,
                   target_count=567, object_module_count=len(nodes), producer=ci)
    create(destination / 'export-summary.json', encoded(summary))
    return summary


def export_handoff(destination):
    ci = identity('full')
    bound = controls()  # Current unmodified five specs deliberately refuse.
    names = targets(); tool, tools, roots, kinds = runtime()
    destination = Path(destination)
    require(destination.parent.resolve() == Path(os.environ['RUNNER_TEMP']).resolve(),
            'Export must be a fresh direct runner-temp child')
    no_symlink_parents(destination)
    destination.mkdir(mode=0o700, exist_ok=False)
    state = dict(status='FAILED_NOT_REPLAY_ACCEPTANCE', CI_identity=ci, accepted=False,
                 replay_invoked=False, partial_data_preserved=True, qualification=QUALIFICATION)
    try:
        summary = export_body(destination, ci, bound, names, tool, tools, roots, kinds)
        state.update(status='SEALED_OBJECT_HANDOFF_ONLY', summary=summary)
        return summary
    except BaseException as error:
        state['failure'] = repr(error)
        raise
    finally:
        create(destination / 'export-result.json', encoded(state))


def safe_relative(value):
    require(type(value) is str and value and not any(ord(c) < 32 or ord(c) == 127 for c in value),
            'Invalid relative path text')
    p = PurePosixPath(value)
    require(value == p.as_posix() and not p.is_absolute() and
            '\\' not in value and all(x not in ['', '.', '..'] for x in p.parts),
            'Unsafe relative payload path')
    return p


def binding(row, allow_empty=False):
    require(type(row) is dict and set(row) == {'bytes', 'sha256'} and
            type(row['bytes']) is int and row['bytes'] >= (0 if allow_empty else 1) and
            type(row['sha256']) is str and re.fullmatch('[0-9a-f]{64}', row['sha256']),
            'Invalid compiled-file binding')
    return row


def artifact_digest(value):
    require(type(value) is str, 'Missing artifact digest')
    value = value.removeprefix('sha256:')
    require(re.fullmatch('[0-9a-f]{64}', value), 'Invalid artifact digest')
    return value


def no_symlink_parents(path):
    p = Path(path)
    require(not p.is_symlink() and all(not q.is_symlink() for q in p.parents),
            'Symlink data path/parent: ' + str(p))


def transport(ci, bound, purpose='production'):
    e = os.environ
    require(purpose in ['production', 'reacquisition_qualification'], 'Unknown transport purpose')
    qualification = purpose == 'reacquisition_qualification'
    if qualification:
        require(e.get('LIGHTEFT_HANDOFF_PURPOSE') == purpose and
                e.get('LIGHTEFT_REACQUISITION_ROLE') == 'consumer' and
                e.get('GITHUB_JOB') == 'native_reacquisition_consumer' and
                e.get('GITHUB_WORKFLOW') == 'LightEFT probe main profile qualification' and
                e.get('GITHUB_REF') == 'refs/heads/light-eft-spanners-checkpoints' and
                e.get('LIGHTEFT_JOB_WORKFLOW_PATH') == '.github/workflows/light-eft-probe-main-qualification.yml' and
                e.get('LIGHTEFT_JOB_WORKFLOW_SHA') == ci['GITHUB_SHA'],
                'Wrong actual qualification transport context')
    require(all(e.get(k) == ci[v] for k, v in
                [('LIGHTEFT_HANDOFF_PRODUCER_SHA', 'GITHUB_SHA'),
                 ('LIGHTEFT_HANDOFF_PRODUCER_RUN_ID', 'GITHUB_RUN_ID'),
                 ('LIGHTEFT_HANDOFF_PRODUCER_RUN_ATTEMPT', 'GITHUB_RUN_ATTEMPT')]),
            'Producer outputs are not the current source/run/attempt')
    text_id = e.get('LIGHTEFT_HANDOFF_ARTIFACT_ID', '')
    require(re.fullmatch('[1-9][0-9]*', text_id) and int(text_id) <= 2**53 - 1,
            'Invalid exact same-run artifact ID')
    expected_digest = artifact_digest(e.get('LIGHTEFT_HANDOFF_ARTIFACT_DIGEST'))
    manifest_sha = e.get('LIGHTEFT_HANDOFF_MANIFEST_SHA256', '')
    require(re.fullmatch('[0-9a-f]{64}', manifest_sha), 'Missing producer manifest output')
    parent = Path(e['RUNNER_TEMP']).resolve(strict=True)
    prefix = 'light-eft-handoff-qualification-' if qualification else 'light-eft-handoff-'
    home = parent / (prefix + ci['GITHUB_RUN_ID'] + '-' + ci['GITHUB_RUN_ATTEMPT'] + '-' + text_id)
    path = home / 'transport.json'
    require(e.get('LIGHTEFT_HANDOFF_TRANSPORT_RECORD') == str(path), 'Not the fixed actual transport record')
    no_symlink_parents(path)
    s = home.lstat(); f = path.lstat()
    require(stat.S_ISDIR(s.st_mode) and s.st_uid == os.getuid() and stat.S_IMODE(s.st_mode) == 0o700 and
            stat.S_ISREG(f.st_mode) and f.st_uid == os.getuid() and f.st_nlink == 1 and
            stat.S_IMODE(f.st_mode) == 0o600, 'Unsafe actual transport record/domain')
    saved = observation(path); row = read_json(path)
    require(row['schema'] == 'LIGHT_ACTUAL_SDK_TRANSPORT_V1' and
            row['source_commit'] == ci['GITHUB_SHA'] and row['repository'] == ci['GITHUB_REPOSITORY'] and
            row['run_id'] == ci['GITHUB_RUN_ID'] and row['run_attempt'] == ci['GITHUB_RUN_ATTEMPT'],
            'Actual transport context differs')
    require(type(row['artifact_id']) is int and row['artifact_id'] == int(text_id) and
            row.get('purpose') == purpose and
            row['artifact_name'] == ('light-eft-reacquisition-handoff-' if qualification else 'light-eft-replay-handoff-') + ci['GITHUB_RUN_ID'] + '-' + ci['GITHUB_RUN_ATTEMPT'] and
            type(row['artifact_bytes']) is int and row['artifact_bytes'] > 0 and
            row['artifact_digest'] == expected_digest and row['manifest_sha256'] == manifest_sha,
            'Actual SDK metadata differs from producer outputs')
    require(row['current_run_client'] is True and row['findBy_used'] is False and
            row['compressed_digest_verified'] is True and row['digest_mismatch'] is False and
            row['sdk_version'] == '2.3.2' and row['source_controls'] == bound,
            'Transport is not the exact strict current-run source-bound SDK capture')
    require(row['loaded_code_unchanged'] is True and type(row['loaded_code']) is dict and
            0 < len(row['loaded_code']) <= 8192 and row['sdk_entry'] in row['loaded_code'] and
            row['sdk_entry'].startswith('node_modules/@actions/artifact/') and
            row['dependency_qualification'] == 'Pinned lockfile CI installation; not authenticated build/cache provenance',
            'Actual local SDK capture is incomplete')
    dependency_root = ROOT / '.lake' / ('light-eft-qualification-sdk-' + ci['GITHUB_RUN_ID'] + '-' + ci['GITHUB_RUN_ATTEMPT']) if qualification else HERE
    require(row.get('dependency_root') == str(dependency_root), 'SDK dependency domain differs')
    no_symlink_parents(dependency_root)
    if qualification:
        ds = dependency_root.lstat()
        require(stat.S_ISDIR(ds.st_mode) and ds.st_uid == os.getuid() and stat.S_IMODE(ds.st_mode) == 0o700,
                'Unsafe qualification SDK domain')
        for filename in ['package.json', 'package-lock.json']:
            require(digest(dependency_root / filename) == digest(HERE / filename), 'Qualification SDK lock bytes differ')
    for rel, value in row['loaded_code'].items():
        safe_relative(rel)
        require(rel.startswith('node_modules/'), 'SDK code path outside dependency tree')
        binding(value, allow_empty=True); p = dependency_root / rel; no_symlink_parents(p)
        require(digest(p) == value, 'Loaded SDK code changed after transport')
    bundle = home / 'bundle'
    no_symlink_parents(bundle)
    require(row['destination'] == str(bundle.resolve(strict=True)) and observation(path) == saved,
            'Actual download destination/record changed')
    return bundle, path, saved, row


def companion_relative(module, suffix):
    p = PurePosixPath(module_path(module))
    return p.with_suffix(suffix).as_posix() if suffix.startswith('.ir') else p.as_posix() + suffix


def expected_file_set(manifest, nodes, all_names, kinds):
    objects = manifest['objects']; claims = manifest['prefix_claims']
    require(set(objects) == set(nodes) and len(claims) == len(kinds), 'Incomplete object/prefix census')
    require(all(type(row) is list and all(type(n) is str for n in row) and row == sorted(set(row))
                for row in claims), 'Invalid namespace-prefix observation')
    _, seeds, imported, _ = selection(manifest['graph'], all_names)
    expected = {}
    for name, node in sorted(nodes.items()):
        obj = objects[name]
        require(set(obj) == {'root', 'relative', 'available'} and type(obj['root']) is int and
                0 <= obj['root'] < len(kinds) and obj['root'] == chosen_prefix(name, claims) and
                obj['relative'] == module_path(name) and set(obj['available']) == set(SUFFIXES),
                'Object owner/effective namespace/relative path differs')
        for value in obj['available'].values():
            if value is not None:
                binding(value)
        expected_headers = ['']
        if obj['available']['.server'] is not None:
            expected_headers += ['.server']
            if obj['available']['.private'] is not None:
                expected_headers += ['.private']
        require([r['suffix'] for r in node['header_parts']] == expected_headers,
                'Header/explicit companion census differs')
        for suffix in required_suffixes(name, node, obj['available'], seeds, imported):
            expected[(name, suffix)] = dict(root=obj['root'], relative=companion_relative(name, suffix),
                                          acquisition=acquisition(kinds[obj['root']]),
                                          transfer=kinds[obj['root']] == 'project',
                                          **binding(obj['available'][suffix]))
    return expected


def bundle_entries(bundle, expected_parts, extra_entries=()):
    no_symlink_parents(bundle)
    require(extra_entries in [(), ('qualification-attestation.json',)], 'Unknown finite bundle extension')
    require(bundle.is_dir() and {p.name for p in bundle.iterdir()} ==
            {'manifest.json', 'parts', 'metadata', *extra_entries},
            'Unknown/missing top-level bundle entries')
    directory = bundle / 'parts'
    require(directory.is_dir() and not directory.is_symlink(), 'Unsafe parts directory')
    actual = set()
    for p in directory.iterdir():
        s = p.lstat()
        require(stat.S_ISREG(s.st_mode) and not p.is_symlink() and s.st_nlink == 1 and
                re.fullmatch('f[0-9]{6}-p[0-9]{6}\\.bin', p.name), 'Unsafe/unexpected part entry')
        actual.add('parts/' + p.name)
        require(len(actual) <= 200000, 'Part-name census exceeds bound')
    require(actual == expected_parts, 'Unlisted/missing payload part')


def verify_files(bundle, manifest, expected, metadata_paths, metadata_bytes, extra_entries=()):
    rows = manifest['files']; require(type(rows) is list and len(rows) == len(expected), 'Required companion count differs')
    by_key = {}; all_parts = set(); paths = list(metadata_paths); total = 0
    for index, row in enumerate(rows):
        require(set(row) == {'module', 'suffix', 'root', 'relative', 'acquisition',
                            'transfer', 'chunks', 'bytes', 'sha256'},
                'Unknown/missing object stream fields')
        key = (row['module'], row['suffix'])
        require(key in expected and key not in by_key, 'Unexpected/duplicate required companion')
        require(type(row['root']) is int and type(row['transfer']) is bool and
                {k: row[k] for k in expected[key]} == expected[key], 'Required companion binding differs')
        safe_relative(row['relative']); binding({k: row[k] for k in ['bytes', 'sha256']})
        require(type(row['chunks']) is list and (row['transfer'] or not row['chunks']), 'Invalid transfer chunk list')
        copied = 0; whole = hashlib.sha256()
        for number, part in enumerate(row['chunks']):
            require(set(part) == {'path', 'bytes', 'sha256'} and
                    part['path'] == 'parts/f%06d-p%06d.bin' % (index, number) and
                    part['path'] not in all_parts, 'Part identity/order differs')
            binding({k: part[k] for k in ['bytes', 'sha256']})
            require(part['bytes'] == min(PART, row['bytes'] - copied) and part['bytes'] > 0,
                    'Part length/complete stream differs')
            path = bundle / safe_relative(part['path']); no_symlink_parents(path)
            require(digest(path) == {k: part[k] for k in ['bytes', 'sha256']}, 'Part content differs')
            with path.open('rb') as stream:
                while data := stream.read(CHUNK):
                    whole.update(data)
            paths.append(path); all_parts.add(part['path']); copied += part['bytes']; total += part['bytes']
            require(total + metadata_bytes <= PAYLOAD_LIMIT,
                    'Decoded project/metadata payload exceeds unchanged total transfer bound')
        require(copied == (row['bytes'] if row['transfer'] else 0) and
                (not row['transfer'] or whole.hexdigest() == row['sha256']), 'Whole object stream differs')
        by_key[key] = row
    require(set(by_key) == set(expected) and total == manifest['payload_bytes'] and
            total + metadata_bytes <= PAYLOAD_LIMIT, 'Hidden required object omission/total budget differs')
    bundle_entries(bundle, all_parts, extra_entries)
    return by_key, paths


def selected_batch(all_names):
    text = os.environ.get('LIGHTEFT_REPLAY_BATCH', '')
    require(text in ['1', '2', '3'], 'Not a source-bound replay batch')
    number = int(text)
    return number, all_names[(number - 1) * 189:number * 189]


def verify_sources(manifest, nodes, tool):
    require(set(manifest['sources']) == set(nodes), 'Incomplete source closure')
    paths = []
    for name, row in manifest['sources'].items():
        kind = row['kind']
        expected_keys = {'kind', 'path', 'bytes', 'sha256'}
        if kind != 'toolchain':
            expected_keys.add('git_blob_oid')
        require(set(row) == expected_keys and row['path'].endswith('.lean'), 'Invalid source binding')
        binding({k: row[k] for k in ['bytes', 'sha256']}, allow_empty=True)
        path = source_path(row, tool); no_symlink_parents(path)
        require(digest(path) == {k: row[k] for k in ['bytes', 'sha256']}, 'Source closure bytes differ')
        # Reuse the same source-to-owner classification and Git-byte check on
        # this fresh checkout; do not trust a payload's claimed source owner.
        require(source_binding(path, tool) == row, 'Fresh source/Git/owner binding differs')
        paths.append(path)
    return paths


def capture_facts(manifest, producer, graph):
    captures = manifest['captures']
    require(len(captures) == 3 and all(c['schema'] == 'ACTUAL_METADATA_CAPTURE_V1' and
            c['CI_identity'] == producer and c['exit'] == 0 and c['failure'] is None and
            type(c['started_ns']) is int and type(c['ended_ns']) is int and
            c['started_ns'] < c['ended_ns'] for c in captures), 'Incomplete actual producer capture chain')
    require(all(a['ended_ns'] < b['started_ns'] for a, b in zip(captures, captures[1:])),
            'Producer metadata captures were not serial')
    evidence = manifest['snapshot']
    require(evidence['observed_inputs_unchanged'] is True and
            evidence['external_no_writer_required'] is True and
            evidence['hostile_writer_absence_not_proved'] is True and
            evidence['graph_sha256'] == graph_fingerprint(graph) and
            evidence['before']['count'] == evidence['after']['count'] and
            evidence['before']['ordered_records_sha256'] == evidence['after']['ordered_records_sha256'],
            'Producer source/no-writer snapshot correlation differs')


def verify_restored_graph(actual, original, selected_names, nodes, sources, objects, roots, tool):
    observed, _ = validate_graph(actual, selected_names)
    needed, _, _, expansions = selection(original, selected_names)
    require(set(observed) == needed and
            [(r['target'], set(r['modules'])) for r in actual['expansions']] ==
            [(r['target'], set(r['modules'])) for r in expansions],
            'Restored checker prefix expansion/import closure differs')
    require([str(Path(p).resolve()) for p in actual['search_path']] == list(map(str, roots)),
            'Restored probe and actual admitted Lake root order differ')
    for name, row in observed.items():
        expected = nodes[name]; obj = objects[name]
        require(row['is_module'] is expected['is_module'] and row['imports'] == expected['imports'],
                'Restored compiled import/header flags differ: ' + name)
        require(chosen_root(name, roots) == obj['root'] and
                Path(row['file']).resolve(strict=True) ==
                (roots[obj['root']] / obj['relative']).resolve(strict=True),
                'Restored effective namespace resolution differs: ' + name)
        require(Path(row['source']).resolve(strict=True) == source_path(sources[name], tool).resolve(strict=True),
                'Restored actual Lean source resolution differs: ' + name)


def actual_companions(needed, objects, roots):
    values = {}; paths = []
    for name in sorted(needed):
        obj = objects[name]; base = roots[obj['root']] / obj['relative']
        values[name] = {}
        for suffix in SUFFIXES:
            path = part_path(base, suffix)
            values[name][suffix] = digest(path) if os.path.lexists(path) else None
            if values[name][suffix] is not None:
                paths.append(path)
    return values, paths


def restore_project_rows(bundle, selected_rows, roots, before, progress, report):
    """Create-only project stream restore, shared without changing read trust."""
    for row in selected_rows:
        if not row['transfer']:
            continue
        dest = roots[row['root']] / safe_relative(row['relative'])
        no_symlink_parents(dest)
        dest.parent.mkdir(parents=True, exist_ok=True)
        no_symlink_parents(dest.parent)
        fd = os.open(dest, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        whole = hashlib.sha256()
        with os.fdopen(fd, 'wb') as output:
            for part in row['chunks']:
                p = bundle / part['path']
                require(observation(p) == before[str(p)], 'Authenticated part changed before use')
                with p.open('rb') as stream:
                    while data := stream.read(CHUNK):
                        output.write(data); whole.update(data)
                require(observation(p) == before[str(p)], 'Authenticated part changed during use')
            output.flush(); os.fsync(output.fileno())
        require(whole.hexdigest() == row['sha256'] and digest(dest) ==
                {k: row[k] for k in ['bytes', 'sha256']}, 'Restored object differs')
        progress.append(dict(module=row['module'], suffix=row['suffix'], destination=str(dest), **digest(dest)))
        if len(progress) % 64 == 0:
            create(report / ('progress-%05d.json' % (len(progress) // 64)), encoded(progress[-64:]))


def restore_body(bundle, report, ci, bound, tool, tools, roots, kinds, names, selected_names,
                 transport_path, transport_state, transport_row, progress):
    expected_sha = os.environ['LIGHTEFT_HANDOFF_MANIFEST_SHA256']
    manifest, metadata_paths, metadata_bytes = load_manifest(bundle, expected_sha)
    require(set(manifest) == {'schema', 'producer', 'controls', 'tools', 'packages', 'root_kinds',
            'graph', 'sources', 'objects', 'prefix_claims', 'files', 'payload_bytes',
            'qualification', 'snapshot', 'captures', 'acquisition_policy'},
            'Unknown/missing V3 manifest fields')
    require(manifest['schema'] == 'LIGHT_SAME_RUN_REPLAY_HANDOFF_V3' and
            manifest['acquisition_policy'] == ACQUISITION_POLICY and
            manifest['producer'] == {**ci, 'LIGHTEFT_VALIDATION_ROLE': 'full'} and
            manifest['controls'] == bound and manifest['packages'] == PINS and
            manifest['tools'] == tools and manifest['root_kinds'] == kinds and
            manifest['qualification'] == QUALIFICATION and type(manifest['payload_bytes']) is int and
            0 < manifest['payload_bytes'] <= PAYLOAD_LIMIT, 'Producer/run/attempt/source/runtime differs')
    graph = manifest['graph']; nodes, _ = validate_graph(graph, names)
    capture_facts(manifest, manifest['producer'], graph)
    expected_files = expected_file_set(manifest, nodes, names, kinds)
    by_key, part_paths = verify_files(bundle, manifest, expected_files, metadata_paths, metadata_bytes)
    source_paths = verify_sources(manifest, nodes, tool)
    needed, seeds, imported, _ = selection(graph, selected_names)
    selected_keys = {(name, suffix) for name in needed for suffix in
                     required_suffixes(name, nodes[name], manifest['objects'][name]['available'], seeds, imported)}
    require(selected_keys <= set(by_key), 'Batch required companion omitted from full handoff')
    selected_rows = [row for key, row in by_key.items() if key in selected_keys]
    package_namespace_before = package_namespace(roots, kinds)
    require(all(row['prefixes'] == manifest['prefix_claims'][row['root']]
                for row in package_namespace_before),
            'Reacquired package namespace prefixes differ from producer')
    package_paths = reacquired_package_paths(manifest, nodes, roots, kinds)
    require(package_namespace(roots, kinds) == package_namespace_before,
            'Package namespace changed during producer-byte validation')
    selected_destinations = []; in_place = []
    # Preflight the complete batch before the first compiled-object write.
    for row in selected_rows:
        dest = roots[row['root']] / safe_relative(row['relative']); no_symlink_parents(dest)
        require(row['relative'] == companion_relative(row['module'], row['suffix']), 'Destination is not its module companion')
        require(dest not in selected_destinations, 'Aliased/duplicate consumer destination')
        selected_destinations.append(dest)
        if row['transfer']:
            require(not os.path.lexists(dest), 'Existing compiled object is not overwritten: ' + str(dest))
        else:
            require(digest(dest) == {k: row[k] for k in ['bytes', 'sha256']},
                    'Fresh dependency object differs from producer: ' + str(dest))
            in_place.append(dest)
    stable_paths = part_paths + source_paths + in_place + package_paths + [transport_path]
    stable_paths += [HERE / n for n in CONTROL_NAMES] + [tool / 'bin' / n for n in ['lean', 'leanchecker', 'lake']]
    require(observation(transport_path) == transport_state, 'Transport record changed before restoration')
    before = snapshot(stable_paths); before_index = write_snapshot(report / 'inputs-before', before)
    restore_project_rows(bundle, selected_rows, roots, before, progress, report)
    actual_available, actual_paths = actual_companions(needed, manifest['objects'], roots)
    for name in needed:
        require(required_suffixes(name, nodes[name], actual_available[name], seeds, imported) ==
                required_suffixes(name, nodes[name], manifest['objects'][name]['available'], seeds, imported),
                'Fresh companion presence changes the native loader read set: ' + name)
    restored_before = snapshot(actual_paths)
    actual = run_probe(report / 'restored-header-probe', selected_names, tool, ci)
    verify_restored_graph(actual, graph, selected_names, nodes, manifest['sources'],
                          manifest['objects'], roots, tool)
    require(package_census(actual, kinds) == package_census(graph, kinds),
            'Reacquired package native object-name census differs from producer')
    # Re-derive the required set and verify actual observed presence at its
    # effective root. Native loader prefix semantics are checked by the probe.
    for row in selected_rows:
        dest = roots[row['root']] / safe_relative(row['relative'])
        require(digest(dest) == {k: row[k] for k in ['bytes', 'sha256']}, 'Required companion changed after probe')
    confirmed = run_probe(report / 'confirmed-restored-header-probe', selected_names, tool, ci)
    require(graph_fingerprint(confirmed) == graph_fingerprint(actual), 'Restored headers/census changed during validation')
    available_after, paths_after = actual_companions(needed, manifest['objects'], roots)
    require(available_after == actual_available and set(map(str, paths_after)) == set(map(str, actual_paths)) and
            snapshot(actual_paths) == restored_before and snapshot(stable_paths) == before and
            reacquired_package_paths(manifest, nodes, roots, kinds) == package_paths and
            package_namespace(roots, kinds) == package_namespace_before and
            observation(transport_path) == transport_state and identity('global_replay') == ci and
            controls() == bound and runtime()[1:] == (tools, roots, kinds),
            'Restored/source/transport/runtime snapshot correlation failed')
    after_index = write_snapshot(report / 'inputs-after', snapshot(stable_paths))
    write_snapshot(report / 'restored-inputs', restored_before)
    require(before_index['ordered_records_sha256'] == after_index['ordered_records_sha256'],
            'Consumer input snapshot digest differs')
    create(report / 'restored-objects.json', encoded(progress))
    return dict(status='BATCH_OBJECTS_AND_METADATA_ONLY_NOT_REPLAY_ACCEPTANCE', CI_identity=ci,
                producer=manifest['producer'], manifest_sha256=expected_sha,
                transport_record=dict(path=str(transport_path), **digest(transport_path)),
                artifact_id=transport_row['artifact_id'], artifact_digest=transport_row['artifact_digest'],
                whole_target_count=567, batch_target_count=len(selected_names),
                ordered_batch_targets_sha256=hashlib.sha256(('\n'.join(selected_names) + '\n').encode()).hexdigest(),
                object_module_count=len(needed), transferred_companions=len(progress),
                verified_in_place_toolchain_companions=sum(
                    kinds[row['root']] == 'toolchain' for row in selected_rows),
                producer_authenticated_required_package_companions=sum(
                    row['acquisition'] == ACQUISITION_POLICY['package'] for row in by_key.values()),
                verified_available_package_files=len(package_paths),
                package_namespace=package_namespace_before,
                acquisition_policy=ACQUISITION_POLICY,
                authenticated_metadata_bytes=metadata_bytes,
                total_transfer_bytes=manifest['payload_bytes'] + metadata_bytes,
                snapshots=dict(before=before_index, after=after_index),
                observed_inputs_unchanged=True, external_no_writer_required=True,
                hostile_writer_absence_not_proved=True, qualification=QUALIFICATION)


def restore_handoff():
    ci = identity('global_replay'); bound = controls(); names = targets()
    tool, tools, roots, kinds = runtime(); number, selected_names = selected_batch(names)
    parent = Path(os.environ['RUNNER_TEMP']).resolve(strict=True)
    report = parent / ('light-eft-replay-restore-' + ci['GITHUB_RUN_ID'] + '-' + ci['GITHUB_RUN_ATTEMPT'] + '-' + str(number))
    no_symlink_parents(report)
    report.mkdir(mode=0o700, exist_ok=False)
    state = dict(status='FAILED_NOT_REPLAY_ACCEPTANCE', CI_identity=ci, batch=number,
                 accepted=False, replay_invoked=False, existing_files_never_overwritten=True)
    progress = []
    try:
        # No caller-chosen payload or receipt path. This record can only follow
        # the source-bound strict SDK operation in the same fresh owned domain.
        bundle, path, saved, row = transport(ci, bound)
        state.update(restore_body(bundle, report, ci, bound, tool, tools, roots, kinds,
                                  names, selected_names, path, saved, row, progress))
        return state
    except BaseException as error:
        state['failure'] = repr(error)
        state['partial_objects_preserved'] = True
        raise
    finally:
        create(report / 'restored-progress.json', encoded(progress))
        create(report / 'result.json', encoded(state))


def main():
    # Execute the main source file directly under a fresh isolated control-cache
    # prefix. This is an invocation contract, not evidence that it has run.
    require(sys.flags.isolated and sys.dont_write_bytecode, 'Require Python -I -B')
    role = os.environ.get('LIGHTEFT_VALIDATION_ROLE', '')
    slot = os.environ.get('LIGHTEFT_REPLAY_BATCH', 'producer')
    require(role in ['full', 'global_replay'] and
            ((role == 'full' and slot == 'producer') or (role == 'global_replay' and slot in ['1', '2', '3'])),
            'Wrong fixed metadata role/batch')
    ci = identity(role)
    prefix = Path(os.environ['RUNNER_TEMP']) / ('light-eft-handoff-control-cache-' +
             ci['GITHUB_RUN_ID'] + '-' + ci['GITHUB_RUN_ATTEMPT'] + '-' + role + '-' + slot)
    require(sys.pycache_prefix == str(prefix) and not os.path.lexists(prefix),
            'Fresh absent explicit -X pycache_prefix required')
    require(len(sys.argv) == 2 and sys.argv[1] in ['export', 'restore'], 'Finite metadata mode required')
    if sys.argv[1] == 'export':
        require(role == 'full', 'Export is producer-only')
        destination = Path(os.environ['RUNNER_TEMP']) / ('light-eft-replay-export-' +
                      ci['GITHUB_RUN_ID'] + '-' + ci['GITHUB_RUN_ATTEMPT'])
        summary = export_handoff(destination)
        outputs = {'handoff_manifest_sha256': summary['manifest_sha256'],
                   'handoff_producer_sha': ci['GITHUB_SHA'],
                   'handoff_producer_run_id': ci['GITHUB_RUN_ID'],
                   'handoff_producer_run_attempt': ci['GITHUB_RUN_ATTEMPT']}
        with open(os.environ['GITHUB_OUTPUT'], 'a') as stream:
            for key, value in outputs.items():
                stream.write(key + '=' + value + '\n')
        print(json.dumps(dict(status='OBJECT_HANDOFF_SEALED_NOT_KERNEL_ACCEPTANCE', **summary)))
    else:
        require(role == 'global_replay', 'Restore is replay-job-only')
        state = restore_handoff()
        print(json.dumps({k: state[k] for k in ['status', 'artifact_id', 'batch_target_count',
                                               'ordered_batch_targets_sha256']}))


if __name__ == '__main__':
    main()
