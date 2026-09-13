"""Exact-key evaluator with an owned compiled-plan boundary.

No new contract semantics or evidence permissions are introduced. The JSON AST,
cache key bytes, predicate identities/order and complete verdict match Phase94.
Compilation validates the declaration and owns a defensive deep snapshot. An
opaque engine-created plan can be audited without recompiling it; a dictionary
plan from outside this process still requires full reconstruction/equality.

This is a trusted in-process API, not a security boundary against arbitrary
Python reflection or malicious mutation of a caller-supplied Boolean cache.
Imported PASS JSON is never accepted as a compiled plan. No global caches exist.
"""
from collections.abc import Mapping
import copy
import hashlib
import itertools
import json
import math

OPS = {'eq': 2, 'ne': 2, 'gt': 2, 'ge': 2, 'add': 2, 'sub': 2,
       'mul': 2, 'div': 2, 'sum': 1, 'len': 1, 'all_zero': 1,
       'get': 2, 'and': 2, 'or': 2}
ROLES = {'context', 'controlled', 'response', 'evidence'}
_TOKEN = object()
_JSON = json.JSONEncoder(sort_keys=True, separators=(',', ':'), allow_nan=False)
_SUFFIX = {'projection': b',"interpreter":1,"scope":"projection"}',
           'record': b',"interpreter":1,"scope":"record"}'}


def _bytes(value):
    return _JSON.encode(value).encode('utf-8')


def digest(value):
    return hashlib.sha256(_bytes(value)).hexdigest()


def _clone(value):
    """Defensive JSON-tree copy; preserve tuple constants and unusual subclasses."""
    kind = type(value)
    if kind in (str, int, float, bool, type(None)):
        return value
    if kind is dict:
        return {_clone(key): _clone(item) for key, item in value.items()}
    if kind is list:
        return [_clone(item) for item in value]
    if kind is tuple:
        return tuple(_clone(item) for item in value)
    return copy.deepcopy(value)


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
    require(op in OPS and isinstance(args, list) and len(args) == OPS[op], 'EXPRESSION_OPERATOR')
    return set().union(*(expression(a, fields) for a in args))


def evaluate(node, row):
    op, args = next(iter(node.items()))
    if op == 'const': return args
    if op == 'field': return row[args]
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


def _validated_view(spec):
    """Unchanged declaration gates and order from the frozen compiler."""
    require(set(spec) == {'version', 'task', 'fields', 'factors', 'cells', 'blocks',
                          'laws', 'assurance'}, 'CONTRACT_SCHEMA')
    require(spec['version'] == 1 and spec['assurance'] == 'AUTHOR_DECLARED_NOT_PROVED', 'ASSURANCE_SCOPE')
    fields, factors = spec['fields'], spec['factors']
    require(fields and factors and spec['cells'] and spec['blocks'], 'EMPTY_DESIGN')
    require({'block', 'cell'} <= set(fields), 'MISSING_DESIGN_FIELDS')
    require(len(spec['blocks']) == len(set(spec['blocks'])), 'DUPLICATE_BLOCK')
    for _, rule in fields.items():
        require(set(rule) == {'role', 'type', 'causes'} and rule['role'] in ROLES, 'FIELD_SCHEMA')
        require(rule['type'] in {'int', 'number', 'str', 'list', 'dict'}, 'FIELD_TYPE')
        require(set(rule['causes']) <= set(factors), 'UNKNOWN_FACTOR')
        require(rule['role'] == 'controlled' or not rule['causes'], 'ILLEGAL_FOOTPRINT')
        require(rule['role'] != 'controlled' or bool(rule['causes']), 'UNBOUND_CONTROLLED_FIELD')
    for f, levels in factors.items():
        require(f in fields and fields[f]['role'] == 'controlled' and set(fields[f]['causes']) == {f}, 'FACTOR_FIELD')
        require(len(levels) >= 2 and len(levels) == len(set(levels)), 'FACTOR_LEVELS')
    for _, levels in spec['cells'].items():
        require(set(levels) == set(factors) and all(levels[f] in factors[f] for f in factors), 'CELL_LEVELS')
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
        allowed = sorted(k for k, v in fields.items() if v['role'] == 'controlled' and delta.intersection(v['causes']))
        pairs.append(dict(a=a, b=b, factors=sorted(delta), fixed=fixed, allowed=allowed))
    return dict(spec=spec, rows=plans, pairs=pairs, contract_sha256=digest(spec))


class CompiledPlan(Mapping):
    """Opaque owned state; exported fields are independent defensive copies.

    Use plan_view(plan) when a JSON-serializable plan is required. Indexing keeps
    existing assurance/spec inspection compatible, without exposing live state.
    """
    __slots__ = ('_owned_state',)

    def __init__(self, view, token=None):
        if token is not _TOKEN:
            raise ValueError('ENGINE_CREATED_PLAN_REQUIRED')
        owned = _clone(view)
        spec = owned['spec']
        quoted_fields = {field: _bytes(field) + b':' for field in spec['fields']}
        laws = []
        for law in owned['rows']:
            deps = tuple(law['dependencies'])
            names = tuple(quoted_fields[k] for k in deps)
            prefix = b'{"expr":' + _bytes(law['expr']) + b',"inputs":'
            laws.append((law['id'], deps, names, prefix, law['expr']))
        factors = {}
        for cell, levels in spec['cells'].items():
            factors[cell] = tuple((f, level, quoted_fields[f],
                b'{"expr":' + _bytes({'eq': [f, level]}) + b',"inputs":') for f, level in levels.items())
        pair_fields = {field: (field, quoted_fields[field],
            b'{"expr":' + _bytes({'equal_pair': field}) + b',"inputs":')
            for field in {field for pair in owned['pairs'] for field in pair['fixed']}}
        pairs = []
        for pair in owned['pairs']:
            checks = tuple(pair_fields[field] for field in pair['fixed'])
            pairs.append((pair['a'], pair['b'], checks))
        used_fields = tuple(sorted(set(spec['factors']) | set(pair_fields) |
                                   {field for law in owned['rows'] for field in law['dependencies']}))
        state = (_TOKEN, owned, tuple((k, rule['type']) for k, rule in spec['fields'].items()),
                 frozenset(spec['fields']), frozenset(spec['blocks']), frozenset(spec['cells']),
                 tuple(laws), factors, tuple(pairs), used_fields)
        object.__setattr__(self, '_owned_state', state)

    def __setattr__(self, name, value):
        raise TypeError('CompiledPlan is immutable through its public API')

    def __delattr__(self, name):
        raise TypeError('CompiledPlan is immutable through its public API')

    def __getattribute__(self, name):
        if name == '_owned_state':
            raise AttributeError('CompiledPlan state is private; use plan_view')
        return object.__getattribute__(self, name)

    def __getitem__(self, key):
        return _clone(_state(self)[1][key])

    def __iter__(self):
        return iter(('spec', 'rows', 'pairs', 'contract_sha256'))

    def __len__(self):
        return 4

    def __repr__(self):
        return f"CompiledPlan({self['contract_sha256']})"


def _state(plan):
    require(type(plan) is CompiledPlan, 'PLAN_INTEGRITY')
    try:
        result = object.__getattribute__(plan, '_owned_state')
    except AttributeError:
        raise ValueError('PLAN_INTEGRITY') from None
    require(isinstance(result, tuple) and len(result) == 10 and result[0] is _TOKEN, 'PLAN_INTEGRITY')
    return result


def plan_view(plan):
    """Return a JSON-ready defensive view, exactly the frozen plan schema."""
    return _clone(_state(plan)[1])


def compile_contract(spec):
    return CompiledPlan(_validated_view(spec), _TOKEN)


def type_ok(value, kind):
    if kind == 'int': return type(value) is int
    if kind == 'number': return type(value) in (int, float) and math.isfinite(value)
    if kind == 'str': return isinstance(value, str)
    if kind == 'list': return isinstance(value, list)
    if kind == 'dict': return isinstance(value, dict)
    return False


def audit(plan, rows, cache=None, cache_scope='projection'):
    """Complete inventory and output on every call; only exact Boolean reuse.

    Serializer fragments and key hashes are memoized ONLY during this call.
    Complete record canonical serialization validates nested JSON values before
    any cache lookup; the same bytes reconstruct the unchanged records SHA-256.
    """
    # Preserve imported-plan integrity: only native opaque plans avoid a rebuild.
    if type(plan) is CompiledPlan:
        state = _state(plan)
    else:
        spec = plan['spec']
        require(cache_scope in ('projection', 'record'), 'CACHE_SCOPE')
        rebuilt = compile_contract(spec)
        require(plan == plan_view(rebuilt), 'PLAN_INTEGRITY')
        state = _state(rebuilt)
    require(cache_scope in ('projection', 'record'), 'CACHE_SCOPE')
    _, view, typed_fields, field_names, block_names, cell_names, laws, factors, pairs, used_fields = state
    spec = view['spec']
    require(len(rows) == len(spec['blocks']) * len(spec['cells']), 'RECORD_COVERAGE')
    index, row_bytes, serialized_in_order = {}, {}, []
    for row in rows:
        require(set(row) == field_names, 'RECORD_FIELDS')
        require(all(type_ok(row[k], kind) for k, kind in typed_fields), 'RECORD_TYPES')
        serialized = _bytes(row)  # Same rejection of non-JSON/nested nonfinite values.
        key = (row['block'], row['cell'])
        require(key[0] in block_names and key[1] in cell_names, 'RECORD_LABEL')
        require(key not in index, 'DUPLICATE_RECORD')
        index[key], row_bytes[key] = row, serialized
        serialized_in_order.append(serialized)
    trace, evaluated, reused = [], 0, 0
    fragments = {}
    scalar_fragments, key_hashes = {}, {}
    suffix = _SUFFIX[cache_scope]
    if cache_scope == 'projection':
        for record_key, row in index.items():
            by_field = {}
            for field in used_fields:
                value = row[field]
                kind = type(value)
                if kind in (int, str, bool, type(None)):
                    scalar_key = (kind, value)
                elif kind is float:
                    # Float equality merges signed zeros; repr preserves key bytes.
                    scalar_key = (float, repr(value))
                else:
                    scalar_key = None
                if scalar_key is not None and scalar_key in scalar_fragments:
                    encoded = scalar_fragments[scalar_key]
                else:
                    encoded = _bytes(value)
                    if scalar_key is not None:
                        scalar_fragments[scalar_key] = encoded
                by_field[field] = encoded
            fragments[record_key] = by_field

    def check(identity, prefix, input_bytes, deps, opcode, left, right):
        nonlocal evaluated, reused
        address = (prefix, input_bytes)
        key = key_hashes.get(address)
        if key is None:
            key = hashlib.sha256(prefix + input_bytes + suffix).hexdigest()
            key_hashes[address] = key
        hit = cache is not None and key in cache
        if hit:
            result = cache[key]
            reused += 1
        else:
            try:
                result = bool(evaluate(left, right) if opcode else left == right)
            except (KeyError, TypeError, ValueError, ZeroDivisionError, OverflowError):
                result = False
            if cache is not None:
                cache[key] = result
            evaluated += 1
        trace.append(dict(id=identity, passed=result, key=key, reused=hit, dependencies=list(deps)))

    for key, row in sorted(index.items()):
        block, cell = key
        identity_prefix = f'{block}/{cell}/'
        full = row_bytes[key]
        values = fragments.get(key)
        for factor, level, name, prefix in factors[cell]:
            inputs = (b'{' + name + values[factor] + b'}') if cache_scope == 'projection' else full
            check(identity_prefix + 'FACTOR_' + factor, prefix, inputs, (factor,),
                  0, row[factor], level)
        for name, deps, quoted, prefix, expr in laws:
            if cache_scope == 'projection':
                if len(deps) == 1:
                    inputs = b'{' + quoted[0] + values[deps[0]] + b'}'
                elif len(deps) == 2:
                    inputs = b'{' + quoted[0] + values[deps[0]] + b',' + quoted[1] + values[deps[1]] + b'}'
                else:
                    inputs = b'{' + b','.join(part + values[field] for part, field in zip(quoted, deps)) + b'}'
            else:
                inputs = full
            check(identity_prefix + str(name), prefix, inputs, deps, 1, expr, row)
    for block in spec['blocks']:
        for left, right, checks in pairs:
            ka, kb = (block, left), (block, right)
            a, b = index[ka], index[kb]
            full = b'[' + row_bytes[ka] + b',' + row_bytes[kb] + b']' if cache_scope == 'record' else None
            identity_prefix = f'{block}/{left}:{right}/FIXED_'
            fa, fb = fragments.get(ka), fragments.get(kb)
            for field, quoted, prefix in checks:
                inputs = (b'{' + quoted + b'[' + fa[field] + b',' + fb[field] + b']}') if cache_scope == 'projection' else full
                check(identity_prefix + field, prefix, inputs, (field,),
                      0, a[field], b[field])
    failures = [t['id'] for t in trace if not t['passed']]
    records_sha = hashlib.sha256(b'[' + b','.join(serialized_in_order) + b']').hexdigest()
    return dict(comparison='REJECT' if failures else 'PASS', failures=failures,
                contract_sha256=view['contract_sha256'], records_sha256=records_sha,
                evaluated=evaluated, reused=reused, predicates=len(trace), trace=trace,
                assurance=spec['assurance'], effect_permission=not failures,
                mechanism='NOT_QUERIED' if not failures else 'NOT_EVALUATED_AFTER_REJECT')
