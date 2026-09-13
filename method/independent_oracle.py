"""Finite valid-schema test oracle: no imports of FARA or Direct modules.

Not an independent hardware oracle or a proof over arbitrary JSON programs.
Its truth table generates expected scope, dependency, and all-check outputs.
"""
import itertools
import operator


def fields(node):
    if 'field' in node:
        return {node['field']}
    if 'const' in node:
        return set()
    found = set()
    for child in next(iter(node.values())):
        found.update(fields(child))
    return found


def value(node, row):
    if 'field' in node:
        return row[node['field']]
    if 'const' in node:
        return node['const']
    operation, nodes = next(iter(node.items()))
    args = [value(child, row) for child in nodes]
    unary = {'sum': sum, 'len': len, 'all_zero': lambda xs: not any(x != 0 for x in xs)}
    binary = {'eq': operator.eq, 'ne': operator.ne, 'gt': operator.gt, 'ge': operator.ge,
              'add': operator.add, 'sub': operator.sub, 'mul': operator.mul,
              'div': operator.truediv, 'get': operator.getitem,
              'and': lambda a,b: bool(a and b), 'or': lambda a,b: bool(a or b)}
    return unary[operation](*args) if operation in unary else binary[operation](*args)


def permission_rows(spec):
    answer = []
    names = list(spec['cells'])
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            a, b = names[i], names[j]
            changed = [f for f in spec['factors'] if spec['cells'][a][f] != spec['cells'][b][f]]
            fixed, allowed = [], []
            for field in sorted(spec['fields']):
                rule = spec['fields'][field]
                if rule['role'] == 'context':
                    fixed.append(field)
                if rule['role'] == 'controlled':
                    same = all(spec['cells'][a][f] == spec['cells'][b][f] for f in rule['causes'])
                    (fixed if same else allowed).append(field)
            answer.append(dict(a=a, b=b, factors=sorted(changed), fixed=fixed, allowed=allowed))
    return answer


def schema_inventory(spec):
    return dict(pairs=permission_rows(spec),
                rows=[dict(id=law['id'], expr=law['expr'], dependencies=sorted(fields(law['expr'])))
                      for law in spec['laws']])


def checks(spec, records):
    out = []
    for row in sorted(records, key=lambda r: (r['block'],r['cell'])):
        start = str(row['block'])+'/'+row['cell']+'/'
        for factor, expected in spec['cells'][row['cell']].items():
            out.append(dict(id=start+'FACTOR_'+factor, passed=row[factor]==expected, dependencies=[factor]))
        for law in spec['laws']:
            try:
                result = bool(value(law['expr'], row))
            except (KeyError, TypeError, ValueError, ZeroDivisionError, OverflowError):
                result = False
            out.append(dict(id=start+str(law['id']), passed=result, dependencies=sorted(fields(law['expr']))))
    index = {(r['block'],r['cell']):r for r in records}
    for block in spec['blocks']:
        for pair in permission_rows(spec):
            a, b = index[block,pair['a']], index[block,pair['b']]
            for field in pair['fixed']:
                out.append(dict(id=str(block)+'/'+pair['a']+':'+pair['b']+'/FIXED_'+field,
                                passed=a[field]==b[field], dependencies=[field]))
    return out
