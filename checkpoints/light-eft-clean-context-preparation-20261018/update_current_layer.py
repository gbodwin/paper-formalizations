"""Prepare the authorized dated repository evidence index; no mathematical edits."""
from pathlib import Path
import hashlib,json

A=Path(__file__).resolve().parent;ROOT=A.parents[1]
PAPER=ROOT/'Light Edge Fault Tolerant Graph Spanners'
def sha(b):return hashlib.sha256(b).hexdigest()
def bind(p):
    b=p.read_bytes();return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':sha(b)}

def main():
    old=A/'preserved-index-before-update';old.mkdir(exist_ok=True)
    paths=['verification/statement-map.json','README.md','PROOF_COVERAGE.md']
    for name in paths:
        dest=old/name;dest.parent.mkdir(parents=True,exist_ok=True)
        if not dest.exists():dest.write_bytes((PAPER/name).read_bytes())
    catalog=json.loads((A/'chain-evidence-index.json').read_text())
    current={'as_of_utc_date':'2026-10-18','mathematical_source_commit':catalog['source_commit'],
        'scope':'Reviewed incremental exact-source evidence; reconciliation only, not a clean authenticated build or new execution',
        'ordinary_modules':485,'qualified_compile_resolve_singleton_replay_chains':485,
        'aggregate':{'module':'LightEFTSpanners','compile':True,'resolve':False,'replay':False},
        'ordinary_evidence_binding_commit':catalog['review_authority']['ordinary_final_binding_commit'],
        'chain_index':bind(A/'chain-evidence-index.json'),'full_audit':catalog['full_audit'],
        'latest_access_evidence':{'binding_commit':'0769579d242f5c8bcd75f2f6333bb57b8d8fc97b','report':'checkpoints/light-eft-cache-route-single-get-20261018/REPORT.md','outcome':'Exactly one unchanged-route official-cache GET returned HTTP403 / error code1010; no archive authentication. No further probe or workaround and no specific user-side setting established.'},
        'historical_coverage_policy':'Original pilot reports and original current_native_coverage dictionaries are preserved as historical; 57/56 partial counts do not describe the current frozen source.',
        'disabled_preparation_packet':str(A.relative_to(ROOT)),
        'remaining_separate':catalog['remaining']}
    index=PAPER/'verification/current-exact-source-evidence-20261018.json'
    index.write_text(json.dumps(current,indent=2)+'\n')
    original=json.loads((old/'verification/statement-map.json').read_text());updated=json.loads(json.dumps(original));changed=[]
    for i,row in enumerate(updated):
        if 'current_native_coverage' not in row:continue
        historical=row['current_native_coverage']
        assert 'historical_native_coverage' not in row
        row['historical_native_coverage']={'qualification':'Verbatim original metadata, historical as of 2026-10-18; includes superseded 57/56 partial counts','original_current_native_coverage':historical}
        row['current_native_coverage']={'as_of_utc_date':'2026-10-18','source':catalog['source_commit'],
            'evidence':catalog['review_authority']['ordinary_final_binding_commit'],'report':'../PROOF_COVERAGE.md',
            'scope':historical['scope'],'exact_source_evidence_index':'current-exact-source-evidence-20261018.json',
            'aggregate_validation':'485 reviewed incremental compile/exact-resolution/singleton-replay chains, plus aggregate compilation only. Full audit c7f33d7e has zero unsafe/partial/project-axiom findings. See dated evidence index for all links and review limits.',
            'qualification':'No authenticated clean rebuild or exact CI is established. Mathematical statement status, Theorem34 replacement scaling, runtime-model scope, website completion and whole-paper acceptance remain separate.',
            'historical_partial_counts':'Original 57/56-partial pilot metadata is preserved verbatim in historical_native_coverage; it is not current-source validation.'}
        changed.append({'row_index':i,'statement':row.get('number',row.get('statement',row.get('id')))})
    assert len(changed)==5
    (PAPER/'verification/statement-map.json').write_text(json.dumps(updated,indent=2)+'\n')
    prefix='''# Current exact-source evidence — 2026-10-18

Frozen mathematical source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. The reviewed incremental evidence covers **485 ordinary compile / exact-resolution / singleton-replay chains**, with the aggregate compiled separately. Full-audit binding `c7f33d7ece117ddc7d20e4f7a5dad2f870e9d41f` records **8,950 project roots, 60,369 closure constants and zero unsafe/partial/project-axiom findings**, using only the three standard axioms. This dated layer reconciles existing evidence; no new Lean execution occurred.

See the [dated exact-source index](verification/current-exact-source-evidence-20261018.json), [all 485 chain links](../checkpoints/light-eft-clean-context-preparation-20261018/chain-evidence-index.json), and [disabled clean-context preparation report](../checkpoints/light-eft-clean-context-preparation-20261018/REPORT.md). Review retains the limitation that the parent's connector could not retrieve the entire 30 MB canonical inventory; matching 83,032-binding preservation receipts and manifest review remain recorded.

This is incremental validation. Authenticated clean toolchain/dependency/extractor validation, reviewed production clean execution, exact coordinated CI, Theorem 34 replacement scaling, runtime-model scope, website completion and whole-paper acceptance remain pending. The unchanged official-cache route most recently returned HTTP 403 / code 1010; no specific user-side setting or workaround has been established. The new preparation remains production-disabled and runs no Lean child.

All original sections below are preserved **historical pilot reports**, including headings that originally said “Current” and the old 57/56-partial results. They do not supersede this dated layer.

---

'''
    for name in ['README.md','PROOF_COVERAGE.md']:(PAPER/name).write_bytes(prefix.encode()+(old/name).read_bytes())
    evidence={'changed_coverage_rows':changed,'other_statement_fields_unchanged':True,'historical_originals':[bind(old/name) for name in paths],'current_index':bind(index),'no_mathematical_source_or_website_edits':True}
    for before,after in zip(original,updated):
        assert {k:v for k,v in before.items() if k!='current_native_coverage'}=={k:v for k,v in after.items() if k not in ['current_native_coverage','historical_native_coverage']}
    (A/'current-layer-reconciliation.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps(evidence,indent=2))

if __name__=='__main__':main()
