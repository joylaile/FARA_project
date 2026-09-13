"""Generic same-information Direct adapter; no FARA compile/plan access.

The baseline may export the same inspectable representation. Shared schema
validation/dependency extraction is available, and charged, to this baseline.
"""
import copy
import itertools


def export(spec, direct, core):
    dependencies = direct.explicit_declaration(spec, core)
    snapshot = copy.deepcopy(spec)
    rows = [dict(id=law['id'], expr=law['expr'], dependencies=dependencies[law['id']])
            for law in snapshot['laws']]
    pairs = []
    for left, right in itertools.combinations(snapshot['cells'], 2):
        changed = {f for f in snapshot['factors']
                   if snapshot['cells'][left][f] != snapshot['cells'][right][f]}
        fixed, allowed = [], []
        for field, rule in snapshot['fields'].items():
            if rule['role'] == 'context':
                fixed.append(field)
            elif rule['role'] == 'controlled':
                (allowed if changed.intersection(rule['causes']) else fixed).append(field)
        pairs.append(dict(a=left, b=right, factors=sorted(changed),
                          fixed=sorted(fixed), allowed=sorted(allowed)))
    return dict(spec=snapshot, rows=rows, pairs=pairs, contract_sha256=core.digest(spec))
