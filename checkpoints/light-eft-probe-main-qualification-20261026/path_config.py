"""Lossless spellings under the unchanged native cwd; no process invocation.

Raw native graph/config evidence stays separate from canonical views. No path,
namespace entry, duplicate, source, input or native guard is omitted here.
"""
from pathlib import Path
import hashlib
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


def spell_entries(entries, work, kind):
    before = cwd_identity(work)
    spellings = []; witness = []
    for index, absolute in enumerate(entries):
        require(absolute.is_absolute() and absolute.resolve(strict=True) == absolute and
                absolute.is_dir(), 'Noncanonical original namespace directory')
        original = signature(absolute.stat())
        relative = os.path.relpath(absolute, work)
        # Default JSON escaping is retained. Equal cost chooses the original absolute form.
        spelling = min([str(absolute), relative], key=lambda s: len(json.dumps(s).encode()))
        require(':' not in spelling and ':' not in str(absolute), 'Unrepresentable path separator')
        actual = under_cwd(spelling, work)
        require(actual == absolute and signature(actual.stat()) == original ==
                signature(absolute.stat()), 'Encoded namespace directory changed identity')
        spellings.append(spelling)
        witness.append(dict(kind=kind, index=index, absolute=str(absolute),
            spelling=spelling, canonical=str(actual), directory_identity=original))
    require(cwd_identity(work) == before, 'Native cwd changed during encoding')
    return ':'.join(spellings), witness


def verify_entries(encoded, originals, work):
    require(isinstance(encoded, str) and encoded and all(encoded.split(':')),
            'Empty encoded namespace entry')
    entries = encoded.split(':')
    require(len(entries) == len(originals), 'Encoded namespace count/order differs')
    for spelling, original in zip(entries, originals):
        require(under_cwd(spelling, work) == original and
                signature(under_cwd(spelling, work).stat()) == signature(original.stat()),
                'Encoded namespace no longer names the same real directory')


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


def canonical_graph(raw, work, roots, source_roots, protected):
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
    require(isinstance(raw['search_path'], list) and
            len(raw['search_path']) == len(roots) and
            [str(under_cwd(x, work)) for x in raw['search_path']] == list(map(str, roots)),
            'Raw effective object namespace differs in order or physical entry')
    require(isinstance(raw['source_search_path'], list) and
            len(raw['source_search_path']) == len(source_roots) and
            [str(under_cwd(x, work)) for x in raw['source_search_path']] == list(map(str, source_roots)),
            'Raw source namespace differs in order or physical entry')
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
    return result, report
