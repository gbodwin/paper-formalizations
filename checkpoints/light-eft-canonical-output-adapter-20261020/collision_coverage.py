"""Fail-closed raw-part and selected-declaration collision classification."""
import re

def require(ok,message):
    if not ok:raise ValueError(message)

HEX=r'((?:[0-9a-f]{2})+)'
PATTERNS=[
 ('start',re.compile(r'AUDIT-PHASE: collision-start modules=([0-9]+)',re.ASCII)),
 ('claim',re.compile(r'COLLISION-CLAIM: ([0-9]+) key='+HEX+r' prior=([0-9]+) owner=([0-9]+) class=(auxiliary-ownership|constant-name-metadata)',re.ASCII)),
 ('decl',re.compile(r'COLLISION-DECL: ([0-9]+) key='+HEX+r' prior=([0-9]+) owner=([0-9]+) result=(compatible-update|compatible-retain|incompatible)',re.ASCII)),
 ('unclassified',re.compile(r'COLLISION-UNCLASSIFIED: ([0-9]+) owner=([0-9]+) scope=(raw-shape|raw-name|effective-shape|effective-name|location|module-count)',re.ASCII)),
 ('module',re.compile(r'COLLISION-MODULE: ([0-9]+) ([0-9]+) parts, ([0-9]+) constNames, ([0-9]+) extraConstNames, ([0-9]+) regions freed',re.ASCII)),
 ('actual',re.compile(r'COLLISION-ACTUAL: ([0-9]+) ([0-9]+) declarations, ([0-9]+) constNames, ([0-9]+) duplicates, ([0-9]+) compatible, ([0-9]+) incompatible, ([0-9]+) unclassified',re.ASCII)),
 ('coverage',re.compile(r'COLLISION-COVERAGE: ([0-9]+) modules, ([0-9]+) declarations/extra-name claims, ([0-9]+) parts read, ([0-9]+) regions freed, ([0-9]+) peak owned regions, ([0-9]+) independent keys, ([0-9]+) constNames, ([0-9]+) extraConstNames, ([0-9]+) same-module repetitions, ([0-9]+) cross-module collisions',re.ASCII)),
 ('classification',re.compile(r'COLLISION-CLASSIFICATION: ([0-9]+) constant-name metadata overlaps, ([0-9]+) auxiliary ownership overlaps, ([0-9]+) effective declarations, ([0-9]+) effective constNames, ([0-9]+) duplicate declarations, ([0-9]+) compatible, ([0-9]+) incompatible, ([0-9]+) unclassified, ([0-9]+) effective keys',re.ASCII)),
]

def validate_collision_coverage(loaded,raw):
    require(isinstance(raw,str) and raw.endswith('\n'),'Truncated collision log')
    require(loaded and all(isinstance(x,str) and x for x in loaded) and len(set(loaded))==len(loaded),'Empty/duplicate loaded module names')
    events=[]
    for position,line in enumerate(raw.splitlines()):
        if not any(token in line for token in ('COLLISION','collision-')):continue
        for kind,pattern in PATTERNS:
            match=pattern.fullmatch(line)
            if match:
                events.append((kind,match.groups(),position));break
        else:raise ValueError('Malformed/unknown collision telemetry line '+str(position+1))
    n=len(loaded)
    require(len(events)>=2*n+3 and events[0][:2]==('start',(str(n),)),'Missing/wrong collision start')
    require([x[0] for x in events[-2:]]==['coverage','classification'],'Missing final collision summaries')
    cursor=1;rows=[];actual=[];claims=[];declarations=[];unclassified=[]
    for owner in range(n):
        local_decl=[];local_unclassified=[]
        while cursor<len(events)-2 and events[cursor][0] in {'claim','decl','unclassified'}:
            kind,values,_=events[cursor];cursor+=1
            if kind=='unclassified':
                seq,who=int(values[0]),int(values[1])
                require(seq==len(unclassified) and who==owner,'Unclassified sequence/owner differs')
                unclassified.append(values);local_unclassified.append(values)
            else:
                seq,key,prior,who,result=values
                seq,prior,who=int(seq),int(prior),int(who)
                require(who==owner and 0<=prior<=owner,'Collision event owner differs')
                if kind=='claim':
                    require(prior<owner and seq==len(claims),'Raw overlap sequence/prior differs')
                    claims.append((key,prior,who,result))
                else:
                    require(seq==len(declarations),'Declaration collision sequence differs')
                    declarations.append((key,prior,who,result));local_decl.append(result)
        require(cursor+1<len(events)-2 and events[cursor][0]=='module' and events[cursor+1][0]=='actual','Missing/ordered module/actual pair')
        row=tuple(map(int,events[cursor][1]));typed=tuple(map(int,events[cursor+1][1]));cursor+=2
        require(row[0]==typed[0]==owner,'Missing/repeated/out-of-order module index')
        require(row[1] in (1,3) and row[1]==row[4],'Required parts/owned release mismatch')
        require(typed[1]==typed[2] and typed[1]<=row[2],'Selected declaration/name/part coverage differs')
        require(typed[3]==len(local_decl) and typed[4]==sum(x.startswith('compatible-') for x in local_decl)
                and typed[5]==local_decl.count('incompatible') and typed[6]==len(local_unclassified),'Per-module classification totals differ')
        rows.append(row);actual.append(typed)
    require(cursor==len(events)-2,'Extra/missing/out-of-order collision events')
    count,total,parts,freed,peak,keys,consts,extras,repetitions,cross=map(int,events[-2][1])
    metadata,auxiliary,effective,names,dups,compatible,incompatible,unknown,effective_keys=map(int,events[-1][1])
    require(count==n and parts==freed==sum(x[1] for x in rows)
            and peak==max(x[1] for x in rows)<=3,'Owned region/module totals differ')
    require(consts==sum(x[2] for x in rows) and extras==sum(x[3] for x in rows) and total==consts+extras,'Raw claim totals differ')
    require(cross==len(claims) and 0<=repetitions<=total and keys==total-repetitions-cross,'Raw key/overlap accounting differs')
    require(metadata==sum(x[3]=='constant-name-metadata' for x in claims)
            and auxiliary==sum(x[3]=='auxiliary-ownership' for x in claims)
            and metadata+auxiliary==cross,'Raw findings not completely classified')
    require((effective,names,dups,compatible,incompatible,unknown)==tuple(sum(x[i] for x in actual) for i in range(1,7)),'Selected declaration totals differ')
    require(dups==len(declarations)==compatible+incompatible and unknown==len(unclassified)
            and effective_keys==effective-dups,'Declaration classification/key totals differ')
    require(incompatible==unknown==0,'Incompatible or unclassified collision finding')
    return dict(imported_modules=n,constNames=consts,extraConstNames=extras,claims=total,
                owned_parts_read=parts,owned_regions_freed=freed,peak_owned_regions=peak,
                independent_keys=keys,same_module_repetitions=repetitions,cross_module_collisions=cross,
                constant_name_metadata_overlaps=metadata,auxiliary_ownership_overlaps=auxiliary,
                effective_declarations=effective,duplicate_declarations=dups,
                compatible_duplicates=compatible,incompatible_duplicates=0,unclassified_findings=0,
                effective_keys=effective_keys,strict_complete_lines=True)
