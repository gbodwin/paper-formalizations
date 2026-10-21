"""Read-only exact membership/identity seals for completed producer evidence."""
from pathlib import Path
import stat
from contracts import bind, require, signature

def shape(root):
    root = Path(root)
    nodes = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        require(stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode), 'Nonregular prior tree member: ' + str(p))
        require(not stat.S_ISREG(s.st_mode) or s.st_nlink == 1, 'Linked prior file: ' + str(p))
        nodes[str(p)] = dict(kind='directory' if stat.S_ISDIR(s.st_mode) else 'file',
                            identity=signature(s), mode=s.st_mode, uid=s.st_uid,
                            gid=s.st_gid, links=s.st_nlink)
    for path, row in nodes.items():
        if row['kind'] == 'directory':
            require(signature(Path(path).lstat()) == row['identity'], 'Prior directory changed during collection')
    return nodes

def capture(roots):
    return {str(root): shape(root) for root in roots}

def verify(trees):
    require(isinstance(trees, dict) and len(trees) == 3, 'Exactly three producer evidence trees required')
    for root, before in trees.items():
        require(shape(root) == before, 'Prior evidence membership/identity changed: ' + root)

def expected_roots(work, identity):
    temp = Path(work).parent.parent
    suffix = identity['GITHUB_RUN_ID'] + '-' + identity['GITHUB_RUN_ATTEMPT']
    require(identity['GITHUB_RUN_ID'].isdecimal() and identity['GITHUB_RUN_ATTEMPT'].isdecimal(), 'Bad producer run identity')
    return [temp / ('light-eft-paid-focused-' + suffix), temp / ('light-eft-staged-' + suffix),
            temp / ('light-eft-paid-joint-bridge-' + suffix)]

def contract(record, spec):
    trees = spec['prior_trees']
    require(set(trees) == set(map(str, expected_roots(spec['focused']['work'], record['CI_identity']))), 'Wrong producer tree roots')
    for root, nodes in trees.items():
        require(root in nodes and nodes[root]['kind'] == 'directory', 'Missing producer root identity')
        for path, row in nodes.items():
            require(Path(path).is_relative_to(root), 'Prior member outside producer root')
            if row['kind'] == 'file':
                protected = spec['protected'].get(path, {})
                require(protected.get('path') == path and protected.get('identity') == row['identity'], 'Prior evidence file is not protected')
    verify(trees)
