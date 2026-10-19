"""Strict complete-line collision telemetry validation; no runtime launch.

Restores the reviewed fail-closed behavior. The previous exact private validator
source is not locally available, so this explicit candidate requires review and
is not represented as a byte-identical recovery of that unavailable file.
"""
import re

def require(ok,message):
    if not ok:raise ValueError(message)

START=re.compile(r'AUDIT-PHASE: collision-start modules=([0-9]+)',re.ASCII)
MODULE=re.compile(r'COLLISION-MODULE: ([0-9]+) ([0-9]+) parts, ([0-9]+) constNames, ([0-9]+) extraConstNames, ([0-9]+) regions freed',re.ASCII)
COVERAGE=re.compile(r'COLLISION-COVERAGE: ([0-9]+) modules, ([0-9]+) declarations/extra-name claims, ([0-9]+) parts read, ([0-9]+) regions freed, ([0-9]+) peak owned regions, ([0-9]+) independent keys, ([0-9]+) constNames, ([0-9]+) extraConstNames, ([0-9]+) same-module repetitions, ([0-9]+) cross-module collisions',re.ASCII)

def validate_collision_coverage(loaded,raw):
    require(isinstance(raw,str) and raw.endswith('\n'),'Truncated collision log')
    require(loaded and all(isinstance(x,str) and x for x in loaded) and len(set(loaded))==len(loaded),'Empty/duplicate loaded module names')
    events=[]
    for position,line in enumerate(raw.splitlines()):
        # Inspect EVERY marker-bearing line. Prefix/suffix junk, malformed extra
        # reports, indentation and incomplete/unknown phases cannot disappear
        # from a findall result. Both patterns and whole lines must match.
        if not any(token in line for token in ('COLLISION','collision-')):continue
        for kind,pattern in [('start',START),('module',MODULE),('coverage',COVERAGE)]:
            match=pattern.fullmatch(line)
            if match:
                events.append((kind,tuple(map(int,match.groups())),position));break
        else:raise ValueError('Malformed/unknown collision telemetry line '+str(position+1))
    n=len(loaded)
    require([x[0] for x in events]==['start']+['module']*n+['coverage'],'Missing/duplicate/out-of-order collision telemetry')
    require(events[0][1]==(n,),'Collision start module scope differs')
    rows=[x[1] for x in events[1:-1]]
    require([x[0] for x in rows]==list(range(n)),'Missing/repeated/out-of-order module index')
    require(all(x[1] in (1,3) and x[1]==x[4] for x in rows),'Required parts/owned release mismatch')
    count,claims,parts,freed,peak,keys,consts,extras,repetitions,collisions=events[-1][1]
    require(count==n,'Collision summary module scope differs')
    require(parts==freed==sum(x[1] for x in rows) and peak==max(x[1] for x in rows)<=3,'Owned region totals differ')
    require(consts==sum(x[2] for x in rows) and extras==sum(x[3] for x in rows) and claims==consts+extras,'Name claim totals differ')
    require(collisions==0 and 0<=repetitions<=claims and keys==claims-repetitions,'Collision/independent-key accounting differs')
    return dict(imported_modules=count,constNames=consts,extraConstNames=extras,claims=claims,
                owned_parts_read=parts,owned_regions_freed=freed,peak_owned_regions=peak,
                independent_keys=keys,same_module_repetitions=repetitions,cross_module_collisions=0,
                strict_complete_lines=True)
