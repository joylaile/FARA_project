"""Finite, pure record-contract compiler. No arbitrary eval or hardware proof.

The cache is process-local and trusted. It stores predicate results, never effects
or recommendations. Author declarations and source decoders remain outside it.
"""
import hashlib
import itertools
import json
import math


OPS = {'eq': 2, 'ne': 2, 'gt': 2, 'ge': 2, 'add': 2, 'sub': 2,
       'mul': 2, 'div': 2, 'sum': 1, 'len': 1, 'all_zero': 1,
       'get': 2, 'and': 2, 'or': 2}
ROLES = {'context', 'controlled', 'response', 'evidence'}


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     allow_nan=False).encode()).hexdigest()


def require(condition, code):
    if not condition:
        raise ValueError(code)


def expression(node, fields):
    require(isinstance(node, dict) and len(node) == 1, 'EXPRESSION_SCHEMA')
    op, args = next(iter(node.items()))
    if op == 'const':
        digest(args)
        return set()
    if op == 'field':
        require(args in fields, 'UNKNOWN_FIELD_REFERENCE')
        return {args}
    require(op in OPS and isinstance(args, list) and len(args) == OPS[op],
            'EXPRESSION_OPERATOR')
    return set().union(*(expression(a, fields) for a in args))


def evaluate(node, row):
    op, args = next(iter(node.items()))
    if op == 'const':
        return args
    if op == 'field':
        return row[args]
    a = [evaluate(n, row) for n in args]
    if op == 'eq': return a[0] == a[1]
    if op == 'ne': return a[0] != a[1]
    if op == 'gt': return a[0] > a[1]
    if op == 'ge': return a[0] >= a[1]
    if op == 'add': return a[0] + a[1]
    if op == 'sub': return a[0] - a[1]
    if op == 'mul': return a[0] * a[1]
    if op == 'div': return a[0] / a[1]
    if op == 'sum': return sum(a[0])
    if op == 'len': return len(a[0])
    if op == 'all_zero': return all(x == 0 for x in a[0])
    if op == 'get': return a[0][a[1]]
    if op == 'and': return bool(a[0] and a[1])
    if op == 'or': return bool(a[0] or a[1])
    raise ValueError('UNKNOWN_OPERATOR')


def compile_contract(spec):
    require(set(spec) == {'version', 'task', 'fields', 'factors', 'cells', 'blocks',
                          'laws', 'assurance'}, 'CONTRACT_SCHEMA')
    require(spec['version'] == 1 and spec['assurance'] == 'AUTHOR_DECLARED_NOT_PROVED',
            'ASSURANCE_SCOPE')
    fields, factors = spec['fields'], spec['factors']
    require(fields and factors and spec['cells'] and spec['blocks'], 'EMPTY_DESIGN')
    require({'block', 'cell'} <= set(fields), 'MISSING_DESIGN_FIELDS')
    require(len(spec['blocks']) == len(set(spec['blocks'])), 'DUPLICATE_BLOCK')
    for name, rule in fields.items():
        require(set(rule) == {'role', 'type', 'causes'} and rule['role'] in ROLES,
                'FIELD_SCHEMA')
        require(rule['type'] in {'int', 'number', 'str', 'list', 'dict'}, 'FIELD_TYPE')
        require(set(rule['causes']) <= set(factors), 'UNKNOWN_FACTOR')
        require(rule['role'] == 'controlled' or not rule['causes'], 'ILLEGAL_FOOTPRINT')
        require(rule['role'] != 'controlled' or bool(rule['causes']), 'UNBOUND_CONTROLLED_FIELD')
    for f, levels in factors.items():
        require(f in fields and fields[f]['role'] == 'controlled' and
                set(fields[f]['causes']) == {f}, 'FACTOR_FIELD')
        require(len(levels) >= 2 and len(levels) == len(set(levels)), 'FACTOR_LEVELS')
    for label, levels in spec['cells'].items():
        require(set(levels) == set(factors) and
                all(levels[f] in factors[f] for f in factors), 'CELL_LEVELS')
    states = [tuple(c[f] for f in factors) for c in spec['cells'].values()]
    require(len(states) == len(set(states)) and
            set(states) == set(itertools.product(*factors.values())), 'FACTORIAL_COVERAGE')
    plans, names = [], set()
    for law in spec['laws']:
        require(set(law) == {'id', 'expr'} and law['id'] not in names, 'LAW_SCHEMA')
        names.add(law['id'])
        deps = expression(law['expr'], fields)
        plans.append(dict(id=law['id'], expr=law['expr'], dependencies=sorted(deps)))
    pairs = []
    for a, b in itertools.combinations(spec['cells'], 2):
        delta = {f for f in factors if spec['cells'][a][f] != spec['cells'][b][f]}
        fixed = sorted(k for k, v in fields.items() if v['role'] == 'context' or
                       (v['role'] == 'controlled' and not delta.intersection(v['causes'])))
        allowed = sorted(k for k, v in fields.items() if v['role'] == 'controlled'
                         and delta.intersection(v['causes']))
        pairs.append(dict(a=a, b=b, factors=sorted(delta), fixed=fixed, allowed=allowed))
    return dict(spec=spec, rows=plans, pairs=pairs, contract_sha256=digest(spec))


def type_ok(value, kind):
    if kind == 'int': return type(value) is int
    if kind == 'number': return type(value) in (int, float) and math.isfinite(value)
    if kind == 'str': return isinstance(value, str)
    if kind == 'list': return isinstance(value, list)
    if kind == 'dict': return isinstance(value, dict)
    return False


def audit(plan, rows, cache=None, cache_scope='projection'):
    """Full inventory is checked every time; only pure predicate work is reused."""
    spec = plan['spec']
    require(cache_scope in {'projection', 'record'}, 'CACHE_SCOPE')
    require(plan == compile_contract(spec), 'PLAN_INTEGRITY')
    require(len(rows) == len(spec['blocks'])*len(spec['cells']), 'RECORD_COVERAGE')
    index = {}
    for row in rows:
        require(set(row) == set(spec['fields']), 'RECORD_FIELDS')
        require(all(type_ok(row[k], v['type']) for k, v in spec['fields'].items()), 'RECORD_TYPES')
        digest(row)  # Reject non-JSON and nested nonfinite values before cache lookup.
        key = (row['block'], row['cell'])
        require(key[0] in spec['blocks'] and key[1] in spec['cells'], 'RECORD_LABEL')
        require(key not in index, 'DUPLICATE_RECORD')
        index[key] = row
    trace, evaluated, reused = [], 0, 0
    def check(identity, expr, projected, thunk, full):
        nonlocal evaluated, reused
        key = digest({'interpreter': 1, 'scope': cache_scope, 'expr': expr,
                      'inputs': projected if cache_scope == 'projection' else full})
        hit = cache is not None and key in cache
        if hit:
            result = cache[key]
            reused += 1
        else:
            try:
                result = bool(thunk())
            except (KeyError, TypeError, ValueError, ZeroDivisionError, OverflowError):
                result = False
            if cache is not None: cache[key] = result
            evaluated += 1
        trace.append(dict(id=identity, passed=result, key=key, reused=hit,
                          dependencies=sorted(projected)))
    for (block, cell), row in sorted(index.items()):
        for f, level in spec['cells'][cell].items():
            check(f'{block}/{cell}/FACTOR_{f}', {'eq': [f, level]}, {f: row[f]},
                  lambda r=row, f=f, v=level: r[f] == v, row)
        for law in plan['rows']:
            projection = {k: row[k] for k in law['dependencies']}
            check(f'{block}/{cell}/{law["id"]}', law['expr'], projection,
                  lambda law=law, row=row: evaluate(law['expr'], row), row)
    for block in spec['blocks']:
        for pair in plan['pairs']:
            a, b = index[block, pair['a']], index[block, pair['b']]
            for field in pair['fixed']:
                check(f'{block}/{pair["a"]}:{pair["b"]}/FIXED_{field}', {'equal_pair': field},
                      {field: [a[field], b[field]]}, lambda a=a,b=b,k=field: a[k] == b[k], [a,b])
    failures = [t['id'] for t in trace if not t['passed']]
    return dict(comparison='REJECT' if failures else 'PASS', failures=failures,
                contract_sha256=plan['contract_sha256'], records_sha256=digest(rows),
                evaluated=evaluated, reused=reused, predicates=len(trace), trace=trace,
                assurance=spec['assurance'], effect_permission=not failures,
                mechanism='NOT_QUERIED' if not failures else 'NOT_EVALUATED_AFTER_REJECT')
