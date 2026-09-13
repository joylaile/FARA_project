"""Same-information revision workflow: complete diagnostics and end-to-end cost.

Every revised row after archive_00 is a labelled SOFTWARE FIXTURE, not a new
board observation. The baseline has the same complete declaration and law AST.
It directly validates the declaration and enumerates every comparison without
a compiled pair plan. The common assurance reporter does compile its coverage
plan in every arm, and that cost is charged. All three arms share pure arithmetic and typed preflight
semantics, not comparison generation. This is not an independent oracle proof.
"""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import importlib.util
import itertools
import json
import math
import platform
import statistics
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECKERS = ("explicit_full", "compiled_record", "compiled_projection")
STAGES = ("input_serialization_ns", "input_parse_ns", "declaration_prepare_ns",
          "validation_predicates_ns", "effect_recomputation_ns",
          "assurance_diagnostic_serialization_ns")


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      allow_nan=False).encode("utf-8")


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False)
                    + "\n", encoding="utf-8")


def cpu_model():
    if sys.platform == "win32":
        try:
            import winreg
            with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,
                                r"HARDWARE\DESCRIPTION\System\CentralProcessor\0") as key:
                return winreg.QueryValueEx(key, "ProcessorNameString")[0].strip()
        except OSError:
            pass
    return platform.processor()


def resolve_source(path):
    path = path.resolve()
    if not (path / "frozen/evidence/independent_same_information.py").exists():
        path = path / "submission/FARA_phase94_method_release"
    if not (path / "frozen/evidence/independent_same_information.py").is_file():
        raise ValueError("PHASE94_SOURCE_PACKAGE_REQUIRED")
    return path


def explicit_declaration(spec, core):
    """Same closed schema; no compiled pair plan and no compile_contract call.

    Dependency extraction is charged because both output formats disclose it.
    This follows the frozen interpreter's declaration checks literally. It is
    a same-information reference implementation, not a separately proved DSL.
    """
    require = core.require
    require(set(spec) == {"version", "task", "fields", "factors", "cells", "blocks",
                          "laws", "assurance"}, "CONTRACT_SCHEMA")
    require(spec["version"] == 1 and spec["assurance"] == "AUTHOR_DECLARED_NOT_PROVED",
            "ASSURANCE_SCOPE")
    fields, factors = spec["fields"], spec["factors"]
    require(fields and factors and spec["cells"] and spec["blocks"], "EMPTY_DESIGN")
    require({"block", "cell"} <= set(fields), "MISSING_DESIGN_FIELDS")
    require(len(spec["blocks"]) == len(set(spec["blocks"])), "DUPLICATE_BLOCK")
    for _, rule in fields.items():
        require(set(rule) == {"role", "type", "causes"} and rule["role"] in core.ROLES,
                "FIELD_SCHEMA")
        require(rule["type"] in {"int", "number", "str", "list", "dict"}, "FIELD_TYPE")
        require(set(rule["causes"]) <= set(factors), "UNKNOWN_FACTOR")
        require(rule["role"] == "controlled" or not rule["causes"], "ILLEGAL_FOOTPRINT")
        require(rule["role"] != "controlled" or bool(rule["causes"]), "UNBOUND_CONTROLLED_FIELD")
    for f, levels in factors.items():
        require(f in fields and fields[f]["role"] == "controlled" and
                set(fields[f]["causes"]) == {f}, "FACTOR_FIELD")
        require(len(levels) >= 2 and len(levels) == len(set(levels)), "FACTOR_LEVELS")
    for _, levels in spec["cells"].items():
        require(set(levels) == set(factors) and
                all(levels[f] in factors[f] for f in factors), "CELL_LEVELS")
    states = [tuple(c[f] for f in factors) for c in spec["cells"].values()]
    require(len(states) == len(set(states)) and
            set(states) == set(itertools.product(*factors.values())), "FACTORIAL_COVERAGE")
    deps, names = {}, set()
    for law in spec["laws"]:
        require(set(law) == {"id", "expr"} and law["id"] not in names, "LAW_SCHEMA")
        names.add(law["id"])
        deps[law["id"]] = sorted(core.expression(law["expr"], fields))
    return deps


def preflight(spec, rows, core):
    """Literal full inventory/type gate from the frozen compiler audit."""
    core.require(len(rows) == len(spec["blocks"]) * len(spec["cells"]), "RECORD_COVERAGE")
    index = {}
    for row in rows:
        core.require(set(row) == set(spec["fields"]), "RECORD_FIELDS")
        core.require(all(core.type_ok(row[k], v["type"]) for k, v in spec["fields"].items()),
                     "RECORD_TYPES")
        core.digest(row)
        key = (row["block"], row["cell"])
        core.require(key[0] in spec["blocks"] and key[1] in spec["cells"], "RECORD_LABEL")
        core.require(key not in index, "DUPLICATE_RECORD")
        index[key] = row
    return index


def explicit_audit(spec, rows, deps, core):
    """All checks and all failures; direct factor/role loops, not a pair plan."""
    index = preflight(spec, rows, core)
    trace = []

    def check(identity, result, dependencies):
        trace.append(dict(id=identity, passed=bool(result), dependencies=dependencies))

    for (block, cell), row in sorted(index.items()):
        for factor, level in spec["cells"][cell].items():
            check(f"{block}/{cell}/FACTOR_{factor}", row[factor] == level, [factor])
        for law in spec["laws"]:
            try:
                result = bool(core.evaluate(law["expr"], row))
            except (KeyError, TypeError, ValueError, ZeroDivisionError, OverflowError):
                result = False
            check(f"{block}/{cell}/{law['id']}", result, deps[law["id"]])
    for block in spec["blocks"]:
        for ca, cb in itertools.combinations(spec["cells"], 2):
            a, b = index[block, ca], index[block, cb]
            for field, rule in sorted(spec["fields"].items()):
                fixed = rule["role"] == "context"
                if rule["role"] == "controlled":
                    fixed = not any(spec["cells"][ca][f] != spec["cells"][cb][f]
                                    for f in rule["causes"])
                if fixed:
                    check(f"{block}/{ca}:{cb}/FIXED_{field}", a[field] == b[field], [field])
    failures = [t["id"] for t in trace if not t["passed"]]
    return dict(comparison="REJECT" if failures else "PASS", failures=failures,
                contract_sha256=core.digest(spec), records_sha256=core.digest(rows),
                evaluated=len(trace), reused=0, predicates=len(trace), trace=trace,
                assurance=spec["assurance"], effect_permission=not failures,
                mechanism="NOT_QUERIED" if not failures else "NOT_EVALUATED_AFTER_REJECT")


def effects(spec, rows, estimator):
    """Every PASS recomputes all ten paired effects and confidence intervals."""
    if len(spec["blocks"]) != 8 or set(spec["factors"]) != {"W", "T"}:
        raise ValueError("BENCHMARK_EFFECT_SCOPE_REQUIRES_EIGHT_WT_BLOCKS")
    paired = {b: {} for b in spec["blocks"]}
    for row in rows:
        paired[row["block"]][row["cell"]] = dict(
            total_ms=row["milliseconds"],
            buckets_ms=[x / row["hz"] * 1000 / row["samples"] for x in row["buckets"]],
            order="software revision fixture; not acquisition order",
            sample_offset=row["sample_offset"])
    values, blocks = estimator.contrasts(paired)
    return dict(summary=values, paired_blocks=blocks,
                scope="eight archived blocks or explicitly synthetic revisions; no new acquisition")


def diagnostic(result, effect, spec, rows, assurance_module, input_valid):
    if assurance_module is not None and input_valid:
        assurance = assurance_module.assess(spec, rows, result, verify=False)
    else:
        assurance = dict(level="REJECTED", output_permission=False,
                         reason="schema gate did not permit assurance assessment")
    return dict(comparison=result["comparison"], failures=result["failures"],
                predicates=result["predicates"],
                checks=[{k: row[k] for k in ("id", "passed", "dependencies")} for row in result["trace"]],
                contract_sha256=result["contract_sha256"], records_sha256=result["records_sha256"],
                effect_permission=result["effect_permission"], effect=effect,
                mechanism=result["mechanism"], assurance=assurance)


def one_step(checker, document, cache, core, estimator, assurance_module):
    """Time from caller's in-memory document through serialized complete output.

    Input fixture construction and disk IO are outside the boundary for all arms.
    Compilation includes actual frozen plan construction. audit additionally
    validates its plan internally; this implementation cost is deliberately paid.
    """
    times, result, parsed, input_valid = {}, None, None, False
    start = time.perf_counter_ns()
    payload = encoded(document)
    now = time.perf_counter_ns(); times[STAGES[0]] = now - start
    parsed = json.loads(payload)
    stamp = time.perf_counter_ns(); times[STAGES[1]] = stamp - now
    spec, rows = parsed["spec"], parsed["records"]
    try:
        prepared = explicit_declaration(spec, core) if checker == "explicit_full" else core.compile_contract(spec)
        now = time.perf_counter_ns(); times[STAGES[2]] = now - stamp
        result = (explicit_audit(spec, rows, prepared, core) if checker == "explicit_full" else
                  core.audit(prepared, rows, cache, "record" if checker == "compiled_record" else "projection"))
        input_valid = True
        stamp = time.perf_counter_ns(); times[STAGES[3]] = stamp - now
    except (KeyError, TypeError, ValueError) as error:
        now = time.perf_counter_ns()
        if STAGES[2] not in times:
            times[STAGES[2]] = now - stamp
            times[STAGES[3]] = 0
        else:
            times[STAGES[3]] = now - (stamp + times[STAGES[2]])
        stamp = now
        result = dict(comparison="REJECT", failures=["STRUCTURE/" + str(error)],
                      predicates=0, trace=[], evaluated=0, reused=0,
                      contract_sha256=core.digest(spec), records_sha256=core.digest(rows),
                      effect_permission=False, mechanism="NOT_EVALUATED_AFTER_REJECT")
    effect = effects(spec, rows, estimator) if result["effect_permission"] else None
    now = time.perf_counter_ns(); times[STAGES[4]] = now - stamp
    output = diagnostic(result, effect, spec, rows, assurance_module, input_valid)
    blob = encoded(output)
    stamp = time.perf_counter_ns(); times[STAGES[5]] = stamp - now
    times["total_ns"] = stamp - start
    assert sum(times[k] for k in STAGES) == times["total_ns"]
    return dict(diagnostic=output, diagnostic_sha256=hashlib.sha256(blob).hexdigest(),
                output_bytes=len(blob), evaluated=result["evaluated"], reused=result["reused"],
                times=times, cache_entries=len(cache) if cache is not None else 0,
                predicate_trace=result["trace"])


def make_sequence(spec, records, source_hashes):
    """Predeclared cumulative revisions, not selected after measuring runtimes."""
    spec, rows = copy.deepcopy(spec), copy.deepcopy(records)
    steps = []

    def add(name, kind, explanation, status="PASS"):
        steps.append(dict(id=name, kind=kind, explanation=explanation, expected=status,
                          spec=copy.deepcopy(spec), records=copy.deepcopy(rows)))

    def law(identity):
        return next(x for x in spec["laws"] if x["id"] == identity)

    add("00_archive", "archive", "Unmodified normalized archived MobileNet W/T records.")
    add("01_unchanged", "legal_revision", "Resubmit unchanged declaration and records.")
    rows[0]["ticks"] += 100
    rows[0]["buckets"][0] += 100
    rows[0]["milliseconds"] = rows[0]["ticks"] / rows[0]["hz"] * 1000 / rows[0]["samples"]
    add("02_response", "legal_revision", "Matched ticks/bucket/unit revision; arithmetic is consistent but synthetic.")
    law("T_HITS")["expr"]["eq"][1]["mul"][1]["const"] -= 1
    for row in rows:
        if row["T"]:
            row["t_hits"] -= 1
            row["t_rebuilds"] += 1
    add("03_oracle_matched", "legal_revision", "Change declared T-hit oracle and all corresponding T-on counter records together.")
    spec["fields"]["completed"]["role"] = "context"
    add("04_role_strengthened", "legal_revision", "Evidence completed becomes context, adding all within-block equality obligations.")
    spec["fields"]["t_hits"]["causes"] = ["W", "T"]
    add("05_footprint_revised", "legal_revision", "Author changes t_hits footprint from T to W,T; generated equality set must change.")
    swapped = [r for r in rows if r["cell"] == "request_only" and r["block"] in (1, 2)]
    for row in swapped:
        row["block"] = 3 - row["block"]
        row["sample_offset"] = 3 * (row["block"] - 1)
    add("06_pairing_revised", "legal_revision", "Synthetic re-pairing swaps W records of blocks 1/2 with matched declared input offsets; source truth is not proved.")
    rows.reverse()
    add("07_record_order", "legal_revision", "Reverse record serialization order, keeping declared pairing unchanged.")
    law("COUNT_h2c")["expr"]["eq"][1]["const"] += 16
    add("08_oracle_unmatched", "invalid_fixture", "Change H2C oracle without changing records; every COUNT_h2c must be reported.", "REJECT")
    for row in rows:
        row["h2c"] += 16
    add("09_oracle_recovered", "legal_revision", "Update all H2C records to the revised declared oracle; no new physical traffic claim.")
    good = copy.deepcopy(rows)
    rows[0]["errors"][0] = 1
    rows[0]["completed"] -= 1
    rows[0]["h2c"] += 16
    add("10_multi_failure", "invalid_fixture", "Concurrent error-word/completion/count errors and newly generated pair inconsistencies; collect all diagnostics.", "REJECT")
    rows = copy.deepcopy(good)
    add("11_recovered", "legal_revision", "Recover all three values; prior cached failures must not leak into recovered output.")
    rows[0]["undeclared"] = 1
    add("12_unknown_record_field", "invalid_fixture", "Undeclared field must be rejected before predicate/effect evaluation.", "REJECT")
    rows = copy.deepcopy(good)
    add("13_schema_recovered", "legal_revision", "Remove undeclared field and recover valid inventory.")
    previous = copy.deepcopy(law("COUNT_h2c")["expr"])
    law("COUNT_h2c")["expr"]["eq"][0]["field"] = "missing_oracle_input"
    add("14_unknown_dependency", "invalid_fixture", "Law references nonexistent field; no compiled plan/effects are permitted.", "REJECT")
    law("COUNT_h2c")["expr"] = previous
    add("15_declaration_recovered", "legal_revision", "Restore law dependency and recover all checks/effects.")
    return dict(version=1, declaration="Fixed before timing; deterministic synthetic revision fixtures except step 00.",
                source_hashes=source_hashes, new_hardware_samples=0, steps=steps)


def delta(old, new):
    if old is None:
        return dict(declaration_fields="all", record_fields="all", pairing_changed=True)
    changed_spec = [k for k in sorted(set(old["spec"]) | set(new["spec"]))
                    if old["spec"].get(k) != new["spec"].get(k)]
    before = {(r["block"], r["cell"]): r for r in old["records"]}
    after = {(r["block"], r["cell"]): r for r in new["records"]}
    changes = []
    for key in sorted(set(before) | set(after)):
        a, b = before.get(key, {}), after.get(key, {})
        fields = [f for f in sorted(set(a) | set(b)) if a.get(f) != b.get(f)]
        if fields:
            changes.append(dict(record=f"{key[0]}/{key[1]}", fields=fields))
    return dict(declaration_fields=changed_spec, record_fields=changes,
                pairing_changed=old["spec"]["blocks"] != new["spec"]["blocks"] or
                    any(x["fields"] and "raw_sha256" in x["fields"] for x in changes),
                serialized_order_changed=[(r["block"], r["cell"]) for r in old["records"]] !=
                                         [(r["block"], r["cell"]) for r in new["records"]])


def summarize(observations, steps, repetitions):
    summary = {}
    for mode in ("cold_workflow", "repeated_workflow"):
        summary[mode] = {}
        for checker in CHECKERS:
            selected = [r for r in observations if r["mode"] == mode and r["checker"] == checker]
            totals = [sum(r["times"]["total_ns"] for r in selected if r["repetition"] == rep) / 1e6
                      for rep in range(repetitions)]
            stage_ms = {key.removesuffix("_ns"): statistics.fmean(
                sum(r["times"][key] for r in selected if r["repetition"] == rep) / 1e6
                for rep in range(repetitions)) for key in STAGES}
            summary[mode][checker] = dict(mean_workflow_ms=statistics.fmean(totals),
                median_workflow_ms=statistics.median(totals), min_workflow_ms=min(totals),
                max_workflow_ms=max(totals), stdev_workflow_ms=statistics.stdev(totals),
                raw_workflow_ms=totals, mean_stage_ms=stage_ms,
                evaluated_per_workflow=sum(r["evaluated"] for r in selected) // repetitions,
                reused_per_workflow=sum(r["reused"] for r in selected) // repetitions)
        base = summary[mode]["explicit_full"]["mean_workflow_ms"]
        for checker in CHECKERS:
            summary[mode][checker]["mean_cost_relative_to_explicit_full"] = summary[mode][checker]["mean_workflow_ms"] / base
    return summary


def run(source, output, sequence_path, repetitions, assurance_path=None):
    if repetitions < 12 or repetitions % 6:
        raise ValueError("AT_LEAST_TWELVE_REPETITIONS_MULTIPLE_OF_SIX_REQUIRED")
    source = resolve_source(source)
    if output.exists() and any(output.iterdir()):
        raise ValueError("FRESH_BENCHMARK_OUTPUT_REQUIRED")
    output.mkdir(parents=True, exist_ok=True)
    run_started = datetime.now(timezone.utc).isoformat()
    implementations = {"revision_benchmark.py": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       "assurance.py": hashlib.sha256(assurance_path.read_bytes()).hexdigest()}
    core = load_module("benchmark_frozen_core", source / "method/contract_compiler.py")
    sys.modules["contract_compiler"] = core
    estimator = load_module("benchmark_frozen_estimator", source / "frozen/evidence/independent_same_information.py")
    assurance_module = load_module("benchmark_assurance", assurance_path) if assurance_path else None
    if assurance_path is None:
        raise ValueError("ASSURANCE_MODULE_REQUIRED_FOR_COMPLETE_OUTPUT")
    spec, records = read(source / "data/mobilenet_spec.json"), read(source / "data/mobilenet_records.json")
    sources = {p: hashlib.sha256((source / p).read_bytes()).hexdigest() for p in
               ("method/contract_compiler.py", "data/mobilenet_spec.json", "data/mobilenet_records.json",
                "frozen/evidence/independent_same_information.py")}
    generated = make_sequence(spec, records, sources)
    if sequence_path.exists():
        if read(sequence_path) != generated:
            raise ValueError("FROZEN_SEQUENCE_DIFFERENCE")
    else:
        write(sequence_path, generated)
    sequence_sha = hashlib.sha256(sequence_path.read_bytes()).hexdigest()
    steps, observations, trace = generated["steps"], [], []
    expected_diagnostics = {}
    permutations = list(itertools.permutations(CHECKERS))
    for rep in range(repetitions):
        order = permutations[rep % 6]
        caches = {c: (None if c == "explicit_full" else {}) for c in CHECKERS}
        for mode in ("cold_workflow", "repeated_workflow"):
            for checker in order:
                prior_keys, prior = set(), None
                for step in steps:
                    result = one_step(checker, dict(spec=step["spec"], records=step["records"]),
                                      caches[checker], core, estimator, assurance_module)
                    diag = result["diagnostic"]
                    if diag["comparison"] != step["expected"]:
                        raise ValueError("EXPECTED_STATUS_" + step["id"] + "_" + checker)
                    if step["id"] not in expected_diagnostics:
                        expected_diagnostics[step["id"]] = result["diagnostic_sha256"]
                    elif expected_diagnostics[step["id"]] != result["diagnostic_sha256"]:
                        raise ValueError("COMPLETE_DIAGNOSTIC_DISAGREEMENT_" + step["id"] + "_" + checker)
                    row = dict(repetition=rep, mode=mode, checker=checker, checker_order=list(order),
                               step=step["id"], status=diag["comparison"],
                               diagnostic_sha256=result["diagnostic_sha256"], output_bytes=result["output_bytes"],
                               evaluated=result["evaluated"], reused=result["reused"],
                               cache_entries=result["cache_entries"], times=result["times"])
                    observations.append(row)
                    if rep == 0 and mode == "cold_workflow":
                        keys = {t["key"] for t in result["predicate_trace"] if "key" in t}
                        try:
                            plan = core.compile_contract(step["spec"])
                        except (ValueError, KeyError, TypeError) as error:
                            plan = dict(rejected=str(error))
                        trace.append(dict(step=step["id"], kind=step["kind"], checker=checker,
                            explanation=step["explanation"], revision_delta=delta(prior, step),
                            declaration=step["spec"], compiled_plan=plan,
                            invalidated_old_keys=sorted(prior_keys - keys), new_predicate_keys=sorted(keys - prior_keys),
                            cache_semantics="Old entries are retained but unreachable unless expression and typed inputs match again; effects never cached.",
                            evaluated=result["evaluated"], reused=result["reused"],
                            complete_diagnostic=diag, predicate_cache_trace=result["predicate_trace"],
                            times=row["times"]))
                        prior_keys, prior = keys, step
        print(f"revision benchmark repetition {rep + 1}/{repetitions}", flush=True)
    summary = summarize(observations, steps, repetitions)
    for step in steps:
        canonical = next(t["complete_diagnostic"] for t in trace if t["step"] == step["id"])
        if canonical["comparison"] == "REJECT" and canonical["effect"] is not None:
            raise ValueError("EFFECT_ESCAPED_REJECTION")
    results = dict(status="PASS", experiment="Same-information full-cost software revision workflow",
        run_started_utc=run_started, implementation_files=implementations,
        scientific_output_agreement=True, diagnostic_comparisons=len(observations),
        source_files=sources, sequence_sha256=sequence_sha, steps=len(steps), repetitions=repetitions,
        timing_observations=len(observations), new_hardware_samples=0,
        original_independent_board_blocks=8, mutation_rows_are_new_independent_samples=False,
        paired_effects_recomputed_on_every_pass=True, disk_and_network_io_timed=False,
        input_and_output_json_serialization_timed=True, assurance_timed=True,
        include_actual_frozen_plan_integrity_recompile=True,
        shared_assurance_compilation_charged_to_all_arms=True,
        process_startup_imports_and_fixture_construction_timed=False,
        expanded_debug_trace_generation_and_archive_export_timed=False,
        cross_checker_equivalence_comparison_timed=False,
        cache_lifetime="New empty caches each cold workflow; second full workflow reuses first workflow cache. Both passes are charged and reported.",
        output_contract="Byte-identical canonical diagnostics, all predicate results/dependencies, complete failure list and all ten paired effects with intervals.",
        inference_boundary="Runtime observations are local software timings, not independent board trials or evidence of compiler superiority.",
        system=dict(python=sys.version, platform=platform.platform(), machine=platform.machine(), cpu_model=cpu_model(),
                    processor=platform.processor(), clock=time.get_clock_info("perf_counter")._asdict()
                    if hasattr(time.get_clock_info("perf_counter"), "_asdict") else
                    dict(implementation=time.get_clock_info("perf_counter").implementation,
                         resolution=time.get_clock_info("perf_counter").resolution)),
        checker_order="All six permutations repeated equally; same order for cold and repeated phases.",
        summary=summary,
        step_results=[dict(id=s["id"], kind=s["kind"], expected=s["expected"],
                           diagnostic_sha256=expected_diagnostics[s["id"]],
                           checkers={c: dict(evaluated=next(t["evaluated"] for t in trace if t["step"] == s["id"] and t["checker"] == c),
                                            reused=next(t["reused"] for t in trace if t["step"] == s["id"] and t["checker"] == c)) for c in CHECKERS},
                           failures=next(t["complete_diagnostic"]["failures"] for t in trace if t["step"] == s["id"])) for s in steps])
    by_step = {t["step"]: t["complete_diagnostic"] for t in trace if t["checker"] == "explicit_full"}
    original = by_step["00_archive"]["effect"]["summary"]
    legacy = read(source / "data/mobilenet_legacy_effects.json")
    checked = 0
    for key in legacy:
        for actual, expected in zip([original[key]["estimate"], *original[key]["ci95"]],
                                    [legacy[key]["estimate"], *legacy[key]["ci95"]]):
            if not math.isclose(actual, expected, rel_tol=1e-10, abs_tol=1e-9):
                raise ValueError("ORIGINAL_BOARD_EFFECT_CHANGED_" + key)
            checked += 1
    if by_step["02_response"]["effect"] == by_step["01_unchanged"]["effect"]:
        raise ValueError("RESPONSE_EFFECT_NOT_RECOMPUTED")
    if by_step["06_pairing_revised"]["effect"]["paired_blocks"] == by_step["05_footprint_revised"]["effect"]["paired_blocks"]:
        raise ValueError("PAIR_PARTNERS_DID_NOT_CHANGE_EFFECT_RECORD")
    if by_step["07_record_order"]["effect"] != by_step["06_pairing_revised"]["effect"]:
        raise ValueError("SERIALIZATION_ORDER_CHANGED_EFFECT")
    if by_step["08_oracle_unmatched"]["failures"] != [
            f"{b}/{c}/COUNT_h2c" for b in sorted(spec["blocks"]) for c in sorted(spec["cells"])]:
        raise ValueError("COMPLETE_ORACLE_REFUSALS_NOT_REPORTED")
    results["unchanged_legacy_estimates_and_ci_endpoints_checked"] = checked
    signature = dict(status="PASS", sequence_sha256=sequence_sha, source_files=sources,
        implementation_files=implementations,
        unchanged_legacy_estimates_and_ci_endpoints_checked=checked,
        step_results=results["step_results"],
        counts={mode: {checker: {key: summary[mode][checker][key] for key in
                ("evaluated_per_workflow", "reused_per_workflow")} for checker in CHECKERS}
                for mode in ("cold_workflow", "repeated_workflow")},
        response_effect_recomputed=True, pairing_effect_recomputed=True,
        record_order_does_not_change_effect=True,
        complete_oracle_refusals_checked=True,
        note="Deterministic signature excludes timestamps, platform and all timings; compare this file on replay.")
    if implementations != {"revision_benchmark.py": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                           "assurance.py": hashlib.sha256(assurance_path.read_bytes()).hexdigest()}:
        raise ValueError("IMPLEMENTATION_CHANGED_DURING_BENCHMARK")
    write(output / "revision_benchmark_observations.json", observations)
    write(output / "revision_benchmark_trace.json", trace)
    write(output / "revision_benchmark_summary.json", results)
    write(output / "revision_benchmark_signature.json", signature)
    print("PHASE95_REVISION_BENCHMARK=PASS", flush=True)
    print(json.dumps(summary, indent=2))
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT / "frozen94")
    parser.add_argument("--out", type=Path, default=ROOT / "results")
    parser.add_argument("--sequence", type=Path, default=ROOT / "data/revision_sequence.json")
    parser.add_argument("--assurance", type=Path, default=ROOT / "method/assurance.py")
    parser.add_argument("--repetitions", type=int, default=18)
    args = parser.parse_args()
    run(args.source_root, args.out, args.sequence, args.repetitions, args.assurance)
