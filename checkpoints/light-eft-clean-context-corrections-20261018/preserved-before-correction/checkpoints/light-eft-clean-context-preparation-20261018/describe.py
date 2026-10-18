"""Permanently describe-only preparation entrypoint. No execution approval exists here."""
import json, sys
from clean_contract import PLAN, CleanContext, schedule, disabled_production


def main(argv=None):
    argv=sys.argv[1:] if argv is None else argv
    if argv not in ([],['--describe']):return disabled_production(argv)
    print(json.dumps({'status':'DISABLED_PREPARATION_ONLY','production_enabled':False,
        'planned_stages':len(schedule()),'schedule_counts':PLAN['schedule_counts'],
        'separate_planned_versioncheck':PLAN['versioncheck'],
        'reviewed_artifact_authority':None,'initial_project_object_ledger':{},
        'initial_resolution_ledger':{},'cache_advice_scopes':[],
        'execution_message':'No argument, missing/forged approval, descriptor or override enables production in this packet',
        'bounded_accounting':PLAN['bounded_accounting']},indent=2))
    return 0


if __name__=='__main__':raise SystemExit(main())
