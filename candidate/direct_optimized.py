"""Strong Direct control with the same annotation-allocation optimization.

All factor/row/pair checks still run, with full failure collection and the same
preflight and expression evaluator. This is not a reduced-output baseline.
"""
import itertools


def explicit_audit(spec,rows,deps,core,direct):
    index=direct.preflight(spec,rows,core)
    trace=[];annotations={}
    def check(identity,result,dependencies):
        key=tuple(dependencies)
        annotation=annotations.get(key)
        if annotation is None:
            annotation=list(key);annotations[key]=annotation
        trace.append({'id':identity,'passed':bool(result),'dependencies':annotation})
    for (block,cell),row in sorted(index.items()):
        for factor,level in spec['cells'][cell].items():
            check(f'{block}/{cell}/FACTOR_{factor}',row[factor]==level,(factor,))
        for law in spec['laws']:
            try:result=bool(core.evaluate(law['expr'],row))
            except (KeyError,TypeError,ValueError,ZeroDivisionError,OverflowError):result=False
            check(f'{block}/{cell}/{law["id"]}',result,deps[law['id']])
    for block in spec['blocks']:
        for ca,cb in itertools.combinations(spec['cells'],2):
            a,b=index[block,ca],index[block,cb]
            for field,rule in sorted(spec['fields'].items()):
                fixed=rule['role']=='context'
                if rule['role']=='controlled':
                    fixed=not any(spec['cells'][ca][f]!=spec['cells'][cb][f] for f in rule['causes'])
                if fixed:check(f'{block}/{ca}:{cb}/FIXED_{field}',a[field]==b[field],(field,))
    failures=[t['id'] for t in trace if not t['passed']]
    return dict(comparison='REJECT' if failures else 'PASS',failures=failures,
                contract_sha256=core.digest(spec),records_sha256=core.digest(rows),
                evaluated=len(trace),reused=0,predicates=len(trace),trace=trace,
                assurance=spec['assurance'],effect_permission=not failures,
                mechanism='NOT_QUERIED' if not failures else 'NOT_EVALUATED_AFTER_REJECT')
