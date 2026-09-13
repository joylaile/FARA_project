"""Derive a bounded assurance report; an identity is not hardware provenance.

The default is a standalone, fresh verification boundary. ``verify=False`` is
only for a trusted in-process checker that has just completed every predicate;
the benchmark applies that same boundary to all three checkers. It must not be
used to import an untrusted JSON verdict as proof. Neither mode certifies the
author's oracle, factor footprints, physical source, or external delivery.
"""
from contract_compiler import audit, compile_contract, digest, type_ok

LEVELS = ('REJECTED', 'RECORDED_FIELDS_ONLY', 'RECORDED_IDENTITIES_CHECKED')
IDENTITIES = {'ELF': 'elf', 'bitstream': 'bitstream', 'input_slice': 'sample_offset'}


def _binding(expr, field):
    """Recognize only explicit equality bindings, not mere field occurrence."""
    if not isinstance(expr, dict) or set(expr) != {'eq'}:
        return None
    left, right = expr['eq']
    if right == {'field': field}:
        left, right = right, left
    if left != {'field': field}:
        return None
    if field == 'bitstream' and set(right) == {'const'} and isinstance(right['const'], str) and right['const'].strip():
        return 'author_registered_constant'
    if field == 'elf' and set(right) == {'get'}:
        mapping, key = right['get']
        if (set(mapping) == {'const'} and isinstance(mapping['const'], dict) and mapping['const']
                and all(isinstance(value, str) and value.strip() for value in mapping['const'].values())
                and key == {'field': 'cell'}):
            return 'author_registered_per_cell_mapping'
    expected = {'mul': [{'sub': [{'field': 'block'}, {'const': 1}]}, {'const': 3}]}
    if field == 'sample_offset' and right == expected:
        return 'author_declared_three_sample_block_slice'
    return None


def assess(spec, records, comparison, requested_level=None, *, verify=True):
    """Return coverage/ceiling, refusing unsupported requested promotion.

``comparison`` supplies comparison, failures, and predicates from the checker.
Full-audit SHA fields, when supplied, must bind these same inputs. The checked
identity level means agreement with a registered author declaration, not an
independent hash of the executable loaded on the physical board.
"""
    plan = compile_contract(spec)
    if not isinstance(comparison, dict):
        raise ValueError('ASSURANCE_REQUIRES_COMPLETE_VERDICT')
    required = {'comparison', 'failures', 'predicates'}
    if not required <= set(comparison) or not isinstance(comparison['failures'], list):
        raise ValueError('ASSURANCE_REQUIRES_COMPLETE_VERDICT')
    if comparison['comparison'] not in ('PASS', 'REJECT'):
        raise ValueError('ASSURANCE_VERDICT_STATUS')
    if comparison['comparison'] != ('REJECT' if comparison['failures'] else 'PASS'):
        raise ValueError('ASSURANCE_VERDICT_CONTRADICTION')
    # Cheap structural checks remain charged even at the trusted fast boundary.
    # An empty list or a forged predicate count must not imply full coverage.
    expected_pairs = len(spec['blocks']) * sum(len(pair['fixed']) for pair in plan['pairs'])
    expected_count = len(spec['blocks']) * len(spec['cells']) * (len(spec['factors']) + len(plan['rows'])) + expected_pairs
    if comparison['predicates'] != expected_count:
        raise ValueError('ASSURANCE_PREDICATE_COVERAGE')
    if len(records) != len(spec['blocks']) * len(spec['cells']):
        raise ValueError('ASSURANCE_RECORD_COVERAGE')
    seen = set()
    for row in records:
        if set(row) != set(spec['fields']) or not all(type_ok(row[k], rule['type']) for k, rule in spec['fields'].items()):
            raise ValueError('ASSURANCE_RECORD_SCHEMA')
        key = row['block'], row['cell']
        if key in seen or key[0] not in spec['blocks'] or key[1] not in spec['cells']:
            raise ValueError('ASSURANCE_RECORD_DESIGN')
        seen.add(key)
    for field, actual in [('contract_sha256', digest(spec)), ('records_sha256', digest(records))]:
        if field in comparison and comparison[field] != actual:
            raise ValueError('ASSURANCE_INPUT_BINDING')
    if verify:
        fresh = audit(plan, records)
        if any(comparison[key] != fresh[key] for key in required):
            raise ValueError('ASSURANCE_VERDICT_MISMATCH')
    bindings = {}
    for label, field in IDENTITIES.items():
        bindings[label] = [dict(law_id=law['id'], binding=_binding(law['expr'], field))
                           for law in plan['rows'] if field in spec['fields'] and _binding(law['expr'], field)]
    failures = set(comparison['failures'])
    per_row = []
    for row in sorted(records, key=lambda r: (r['block'], r['cell'])):
        prefix = f'{row["block"]}/{row["cell"]}/'
        checked, missing = {}, []
        for label, field in IDENTITIES.items():
            valid = [binding for binding in bindings[label]
                     if prefix + binding['law_id'] not in failures]
            if field in row and valid:
                checked[label] = dict(field=field, value=row[field], checks=valid)
            else:
                missing.append(label)
        per_row.append(dict(block=row['block'], cell=row['cell'], checked_identities=checked,
                            missing_identity_fields=missing))
    missing = sorted({x for row in per_row for x in row['missing_identity_fields']})
    derived = ('REJECTED' if failures else
               'RECORDED_FIELDS_ONLY' if missing else 'RECORDED_IDENTITIES_CHECKED')
    promotion = (requested_level is not None and
                 (requested_level not in LEVELS or LEVELS.index(requested_level) > LEVELS.index(derived)))
    return dict(
        comparison=comparison['comparison'], level=derived, result_assurance_ceiling=derived,
        requested_level=requested_level,
        request_status='REFUSED_ASSURANCE_PROMOTION' if promotion else 'WITHIN_DERIVED_CEILING',
        output_permission=not failures and not promotion,
        missing_identity_fields=missing, per_row=per_row,
        law_coverage=[dict(id=law['id'], dependencies=law['dependencies']) for law in plan['rows']],
        checked_scope='Recorded values agree with compiled predicates and registered author declarations.',
        validation_boundary=('fresh_standalone_full_verification' if verify else
                             'trusted_in_process_complete_checker_output'),
        author_assertions=['factor_footprint_completeness', 'law_and_oracle_adequacy',
                           'source_decoder_correctness', 'physical_record_origin'],
        not_established=['independent_hardware_rebuild', 'new_hardware_acquisition',
                         'loaded_binary_attestation', 'external_artifact_delivery'],
        source_hash_scope='raw_sha256 is recorded metadata here; this function does not open or hash source files.',
        input_binding=dict(contract_sha256=digest(spec), records_sha256=digest(records)))
