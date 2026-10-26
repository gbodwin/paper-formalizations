"""Lossless spellings under the unchanged native cwd; no process invocation.

Raw native graph/config evidence stays separate from canonical views. No path,
namespace entry, duplicate, source, input or native guard is omitted here.
"""
from pathlib import Path
import hashlib
import errno
import json
import os
import stat
from contracts import require, signature


def cwd_identity(work):
    require(work.is_absolute() and work.resolve(strict=True) == work and
            not any(p.is_symlink() for p in [work, *work.parents]),
            'Native cwd is not its actual absolute nonsymlink directory')
    s = work.lstat()
    require(stat.S_ISDIR(s.st_mode), 'Native cwd is not a directory')
    return signature(s)


def under_cwd(text, work, strict=True):
    require(isinstance(text, str) and text and not any(c in text for c in '\0\r\n'),
            'Invalid path spelling')
    p = Path(text)
    return (p if p.is_absolute() else work / p).resolve(strict=strict)


def _directory_identity(s):
    return [s.st_dev, s.st_ino, stat.S_IMODE(s.st_mode), s.st_uid, s.st_gid]


def _full_identity(s):
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns,
            stat.S_IMODE(s.st_mode), s.st_uid, s.st_gid, s.st_nlink]


def _directory(path, seen):
    s = path.lstat()  # No symlink following; permission/type errors are not absence.
    require(stat.S_ISDIR(s.st_mode), 'Symlink or nondirectory namespace ancestor')
    value = _directory_identity(s); key = str(path)
    require(key not in seen or seen[key] == value, 'Namespace ancestor identity changed')
    seen[key] = value
    require(len(seen) <= 256, 'Namespace ancestor count exceeds finite witness bound')
    return s


def _members(anchor):
    before = anchor.lstat(); rows = []; size = 0
    with os.scandir(anchor) as directory:
        for entry in directory:
            require(len(rows) < 4096, 'Absence anchor membership exceeds finite bound')
            row = [entry.name, _full_identity(entry.stat(follow_symlinks=False))]
            size += len(json.dumps(row).encode())
            require(size <= 65536, 'Absence anchor membership exceeds64KiB')
            rows.append(row)
    after = anchor.lstat()
    require(stat.S_ISDIR(before.st_mode) and _full_identity(before) == _full_identity(after),
            'Absence anchor changed during membership observation')
    raw = json.dumps(sorted(rows), separators=(',', ':')).encode()
    return dict(count=len(rows), sha256=hashlib.sha256(raw).hexdigest())


def _walk(text, work, seen):
    """Resolve only real directory components; preserve the first ENOENT suffix.

    Parent traversal must happen while its operand exists. No lexical collapse
    across a missing component, symlink traversal or error-to-absence conversion.
    """
    require(isinstance(text, str) and text and not text.startswith('//') and
            not any(c in text for c in '\0\r\n:'), 'Invalid namespace path spelling')
    parts = text.split('/')
    if text.startswith('/'):
        parts = parts[1:]
    else:
        parts = list(work.parts[1:]) + parts
    require(0 < len(parts) <= 256 and all(parts), 'Unsafe namespace path components')
    current = Path('/'); _directory(current, seen)
    for index, component in enumerate(parts):
        if component == '.':
            _directory(current, seen); continue
        if component == '..':
            current = current.parent; _directory(current, seen); continue
        candidate = current / component
        try:
            observed = candidate.lstat()
        except FileNotFoundError as missing:
            require(missing.errno == errno.ENOENT, 'Namespace absence is not ENOENT')
            suffix = parts[index:]
            require(all(x not in ('', '.', '..') for x in suffix),
                    'Parent traversal after a missing namespace component')
            before = _directory(current, seen)
            membership = _members(current)
            after = _directory(current, seen)
            require(_full_identity(before) == _full_identity(after),
                    'Absence anchor changed during observation')
            # Recheck the FIRST missing child, not merely the final unresolved leaf.
            try:
                candidate.lstat()
            except FileNotFoundError as missing:
                require(missing.errno == errno.ENOENT, 'Namespace recheck absence is not ENOENT')
            else:
                raise RuntimeError('Missing namespace component appeared during observation')
            return dict(state='absent', absolute=str(current.joinpath(*suffix)),
                        anchor=str(current), missing_suffix=suffix,
                        anchor_identity=_full_identity(after), anchor_membership=membership)
        require(stat.S_ISDIR(observed.st_mode), 'Symlink or nondirectory namespace component')
        current = candidate
        require(_directory_identity(_directory(current, seen)) == _directory_identity(observed),
                'Namespace component changed while traversing')
    return dict(state='directory', absolute=str(current),
                identity=_full_identity(_directory(current, seen)))


def _check_ancestors(ancestors):
    current = {}
    for name, expected in ancestors.items():
        require(Path(name).is_absolute(), 'Nonabsolute witnessed ancestor')
        require(_directory_identity(_directory(Path(name), current)) == expected,
                'Witnessed namespace ancestor changed')


def spell_entries(entries, work, kind, encoded_count, native_tail=(), absent_allowed=(),
                  original_spellings=None):
    before = cwd_identity(work)
    require(kind in ('LEAN_PATH', 'LEAN_SRC_PATH') and
            0 < encoded_count <= len(entries) <= 80 and
            len(native_tail) == len(entries) - encoded_count, 'Namespace witness shape differs')
    allowed = sorted(set(map(str, absent_allowed)))
    require((not allowed or kind == 'LEAN_PATH') and
            set(allowed).issubset(set(map(str, entries))), 'Unadmitted absent namespace root')
    originals = list(map(str, entries)) if original_spellings is None else original_spellings
    require(len(originals) == len(entries), 'Original namespace slot coverage differs')
    roots = {}; ancestors = {}; slots = []; encoded = []
    for index, absolute in enumerate(entries):
        require(absolute.is_absolute(), 'Nonabsolute original namespace directory')
        state = _walk(str(absolute), work, ancestors)
        require(state['absolute'] == str(absolute) and
                (state['state'] == 'directory' or str(absolute) in allowed),
                'Unadmitted absent or noncanonical namespace root')
        require(str(absolute) not in roots or roots[str(absolute)] == state,
                'Duplicate namespace root changed state')
        roots[str(absolute)] = state
        relative = os.path.relpath(absolute, work)
        spelling = min([str(absolute), relative], key=lambda s: len(json.dumps(s).encode()))
        reported = spelling if index < encoded_count else native_tail[index - encoded_count]
        require(_walk(originals[index], work, ancestors) == state and
                _walk(spelling, work, ancestors) == state and
                _walk(reported, work, ancestors) == state, 'Namespace spellings are not equivalent')
        slots.append(dict(kind=kind, index=index, absolute=str(absolute), spelling=spelling,
                          encoded=index < encoded_count, reported=reported, original=originals[index]))
        if index < encoded_count:
            encoded.append(spelling)
    witness = dict(schema='ORDERED_NAMESPACE_ABSENCE_WITNESS_V1', kind=kind,
                   encoded_count=encoded_count, slots=slots, roots=roots,
                   ancestors=ancestors, absent_allowed=allowed)
    verify_namespace(witness, work)
    require(cwd_identity(work) == before, 'Native cwd changed during encoding')
    return ':'.join(encoded), witness


def verify_namespace(witness, work):
    cwd_identity(work)
    require(isinstance(witness, dict) and set(witness) == {'schema', 'kind', 'encoded_count',
            'slots', 'roots', 'ancestors', 'absent_allowed'} and
            witness['schema'] == 'ORDERED_NAMESPACE_ABSENCE_WITNESS_V1' and
            witness['kind'] in ('LEAN_PATH', 'LEAN_SRC_PATH'), 'Namespace witness schema differs')
    slots = witness['slots']; roots = witness['roots']; ancestors = witness['ancestors']
    count = witness['encoded_count']; allowed = witness['absent_allowed']
    require(isinstance(slots, list) and 0 < count <= len(slots) <= 80 and
            isinstance(roots, dict) and set(roots) == {x['absolute'] for x in slots} and
            isinstance(ancestors, dict) and 0 < len(ancestors) <= 256 and
            allowed == sorted(set(allowed)) and set(allowed).issubset(roots) and
            (not allowed or witness['kind'] == 'LEAN_PATH'), 'Namespace witness coverage differs')
    _check_ancestors(ancestors)
    observed = {}; cached = {}
    for index, row in enumerate(slots):
        require(set(row) == {'kind', 'index', 'absolute', 'spelling', 'encoded', 'reported', 'original'} and
                row['kind'] == witness['kind'] and row['index'] == index and
                row['encoded'] is (index < count), 'Ordered namespace slot differs')
        expected = roots[row['absolute']]
        require(expected['absolute'] == row['absolute'] and
                (expected['state'] == 'directory' or
                 (expected['state'] == 'absent' and row['absolute'] in allowed)),
                'Absent namespace root lacks explicit admission')
        for text in (row['absolute'], row['original'], row['spelling'], row['reported']):
            if text not in cached:
                cached[text] = _walk(text, work, observed)
            require(cached[text] == expected, 'Namespace directory/absence state changed')
    require(all(name in ancestors and ancestors[name] == value for name, value in observed.items()),
            'Namespace traversal escaped witnessed ancestors')
    _check_ancestors(ancestors)


def verify_entries(encoded, originals, work, witness):
    verify_namespace(witness, work)
    count = witness['encoded_count']; slots = witness['slots'][:count]
    require(isinstance(encoded, str) and encoded and all(encoded.split(':')) and
            encoded.split(':') == [r['spelling'] for r in slots] and
            list(map(str, originals)) == [r['absolute'] for r in slots],
            'Encoded namespace count/order/duplicates or original paths differ')


def verify_reported(entries, witness, work):
    verify_namespace(witness, work)
    require(isinstance(entries, list) and len(entries) == len(witness['slots']),
            'Reported namespace count differs')
    observed = {}; cached = {}
    for text, slot in zip(entries, witness['slots']):
        if text not in cached:
            cached[text] = _walk(text, work, observed)
        require(cached[text] == witness['roots'][slot['absolute']],
                'Reported namespace slot/order/absence differs')
    require(all(name in witness['ancestors'] and witness['ancestors'][name] == value
                for name, value in observed.items()), 'Reported namespace used an unwitnessed ancestor')
    verify_namespace(witness, work)


def physical_roots(witness, work):
    verify_namespace(witness, work)
    return list(dict.fromkeys(Path(row['absolute']) for row in witness['slots']
                              if witness['roots'][row['absolute']]['state'] == 'directory'))


def verify_arguments(plan, work, program, request, output):
    cwd_identity(work)
    require(plan['cwd'] == str(work) and plan['argv'][6:] ==
            ['--run', str(program), 'request.json', 'graph/headers.json'],
            'Exact relative request/output argument spelling differs')
    require(request == work / 'request.json' and output == work / 'graph/headers.json' and
            under_cwd('request.json', work) == request and
            under_cwd('graph/headers.json', work, strict=False) == output and
            output.parent.resolve(strict=True) == work / 'graph',
            'Argument spelling names another absolute protected input/output')


def config_bytes(plan):
    # Exactly the unchanged canonical child_runner's key order/default encoder.
    return json.dumps({'argv': plan['argv'], 'env': plan['env'], 'stage': plan['stage']}).encode()


def preserve_attempt(plan, folder, create, save):
    data = config_bytes(plan)
    prefix = data[:65536]
    path = folder / 'attempted-native-config.json'
    create(path, prefix)
    record = dict(schema='NATIVE_CONFIG_ATTEMPT_BYTES_V1', bytes=len(data),
        sha256=hashlib.sha256(data).hexdigest(), stored_bytes=len(prefix),
        complete=len(data) == len(prefix), evidence_file=str(path),
        bound=4096, default_serialization_unchanged=True,
        audit_only_never_a_child_configuration_input=True,
        public_plan_fields_only=True)
    save(folder / 'attempted-native-config-receipt.json', record)
    # Both exact total byte count and digest are persisted BEFORE the unchanged floor.
    require(len(data) <= 4096, 'Existing native launcher configuration bound exceeded')
    require(record['complete'], 'Accepted configuration evidence incomplete')
    return data, [path, folder / 'attempted-native-config-receipt.json']


def canonical_graph(raw, work, roots, source_roots, protected, object_witness, source_witness):
    """Retain raw output; change only path spellings in this in-memory view.

    Every returned file resolves under the actual child cwd to a real pre-exec
    protected regular input with the same identity. Existing header/prefix/Git/
    companion checks still consume the complete resulting graph afterwards.
    """
    cwd_identity(work)
    require(isinstance(raw, dict) and set(raw) == {'schema', 'target_count',
            'search_path', 'source_search_path', 'census', 'expansions', 'nodes',
            'regions_retained'}, 'Unexpected raw graph schema fields')
    require(isinstance(raw['census'], list) and len(raw['census']) <= 200000 and
            isinstance(raw['nodes'], list) and 0 < len(raw['nodes']) <= 32768,
            'Raw graph count bound exceeded')
    require([r['absolute'] for r in object_witness['slots']] == list(map(str, roots)) and
            [r['absolute'] for r in source_witness['slots']] == list(map(str, source_roots)),
            'Witnessed complete effective namespaces differ')
    verify_reported(raw['search_path'], object_witness, work)
    verify_reported(raw['source_search_path'], source_witness, work)
    memo = {}; mapping_hash = hashlib.sha256(); occurrences = 0
    def file_path(text):
        nonlocal occurrences
        require(isinstance(text, str), 'Nonstring graph file')
        if text not in memo:
            actual = under_cwd(text, work)
            key = str(actual)
            require(key in protected and not protected[key].get('metadata_only'),
                    'Graph path escaped the actual protected inputs')
            s = actual.lstat()
            require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1 and
                    signature(s) == protected[key]['identity'], 'Graph file identity drift')
            memo[text] = key
        result = memo[text]; occurrences += 1
        mapping_hash.update((json.dumps([text, result]) + '\n').encode())
        return result
    result = dict(raw)
    result['search_path'] = list(map(str, roots))
    result['source_search_path'] = list(map(str, source_roots))
    result['census'] = []
    for row in raw['census']:
        require(isinstance(row, dict) and set(row) == {'module', 'file'}, 'Unknown census row')
        copy = dict(row); copy['file'] = file_path(row['file']); result['census'].append(copy)
    result['nodes'] = []
    for row in raw['nodes']:
        require(isinstance(row, dict) and set(row) == {'module', 'file', 'source',
                'is_module', 'imports', 'header_parts'}, 'Unknown native header fields')
        copy = dict(row); copy['file'] = file_path(row['file']); copy['source'] = file_path(row['source'])
        result['nodes'].append(copy)
    # No imports, flags, expansions, node/module order or duplicate census rows change.
    digest = hashlib.sha256(); size = 0
    for part in json.JSONEncoder(sort_keys=True).iterencode(result):
        data = part.encode(); size += len(data); digest.update(data)
    report = dict(schema='RAW_GRAPH_CANONICAL_PATH_VIEW_V1',
        canonical_view_bytes=size, canonical_view_sha256=digest.hexdigest(),
        path_occurrences=occurrences, unique_spellings=len(memo),
        path_mapping_sha256=mapping_hash.hexdigest(),
        raw_graph_preserved=True, only_path_spellings_changed=True,
        no_native_input_shift=True)
    verify_namespace(object_witness, work); verify_namespace(source_witness, work)
    return result, report
