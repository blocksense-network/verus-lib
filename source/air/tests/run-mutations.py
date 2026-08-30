#!/usr/bin/env python3
"""Mutation harness for the counterexample checks in tests/counterexample.rs.

Every check in that file claims to detect something. This script proves it: for
each mutation it patches one line of the product, re-runs the suite, and requires
that the **named** test fails -- not merely that the run went red. A mutation
killed by a different test than the one written for it is reported as a
MISDIRECTED kill and counts as a failure of this harness, because it means the
check that was supposed to catch it does not.

Mutations that no check can kill are listed in DECLARED_SURVIVORS with the reason
at the line. They are still run, and it is an error if one of them turns out to be
killable after all -- a survivor that starts dying means the reason recorded for
it has gone stale.

Per Testing/Verification-Harness-Traps.md: the verdict is taken from the parsed
per-test result lines, never from the exit code alone, and a run that produces no
result lines at all is a harness failure rather than a kill.

Usage:  ./run-mutations.py            (from source/air, with z3 on PATH)
"""

import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

AIR = Path(__file__).resolve().parent.parent
SOURCE = AIR.parent

MODEL = "src/model.rs"
SMT = "src/smt_verify.rs"


@dataclass
class Mutation:
    id: str
    path: str
    find: str
    replace: str
    killer: str
    why: str = ""


MUTATIONS = [
    Mutation(
        "M1", MODEL,
        "        self.defs = defs;",
        "        self.defs = HashMap::new();",
        "c3_model_values_are_the_values_the_failing_execution_computes",
    ),
    Mutation(
        "M2", MODEL,
        "            value: (*def.body).clone(),",
        '            value: constant.to_string(),',
        "c3_model_values_are_the_values_the_failing_execution_computes",
    ),
    Mutation(
        "M3", MODEL,
        "                let constant = crate::var_to_const::rename_var(name, *version);",
        "                let constant = crate::var_to_const::rename_var(name, 0);",
        "c3_model_values_are_the_values_the_failing_execution_computes",
    ),
    Mutation(
        "M4", MODEL,
        "    REPORT_COUNTEREXAMPLE.load(Ordering::SeqCst)",
        "    true",
        "c1_control_no_counterexample_is_reported_when_reporting_is_off",
    ),
    Mutation(
        "M5", MODEL,
        "        !self.parameters.is_empty() || self.snapshots.iter().any(|s| !s.bindings.is_empty())",
        "        true",
        "c8_a_counterexample_with_no_bindings_is_not_populated",
    ),
    Mutation(
        "M6", MODEL,
        "        snapshot\n            .iter()",
        "        snapshot\n            .iter()\n            .take(0)",
        "c3_model_values_are_the_values_the_failing_execution_computes",
    ),
    Mutation(
        "M7", MODEL,
        "    let json = note.strip_prefix(COUNTEREXAMPLE_NOTE_PREFIX)?;",
        "    let json = note.strip_prefix(COUNTEREXAMPLE_NOTE_PREFIX).unwrap_or(note);",
        "c9_only_a_counterexample_note_decodes_as_one",
    ),
    Mutation(
        "M8", MODEL,
        "        self.parameters.keys().filter_map(|name| self.binding(name, name)).collect()",
        "        self.parameters.keys().take(0).filter_map(|name| self.binding(name, name)).collect()",
        "c3_model_values_are_the_values_the_failing_execution_computes",
    ),
    Mutation(
        "M9", MODEL,
        "        ids.sort();\n        ids",
        "        ids.sort();\n        ids.reverse();\n        ids",
        "c10_snapshots_are_emitted_in_a_stable_order_and_carry_the_solver_s_sorts",
    ),
    Mutation(
        "M10", MODEL,
        "            typ: typ_to_smt_name(&def.ret),",
        '            typ: "Int".to_string(),',
        "c10_snapshots_are_emitted_in_a_stable_order_and_carry_the_solver_s_sorts",
    ),
    Mutation(
        "M11", MODEL,
        "            constant: constant.to_string(),",
        "            constant: (**variable).clone(),",
        "c3_model_values_are_the_values_the_failing_execution_computes",
    ),
    Mutation(
        "M12", SMT,
        "    air_model.set_defs(model_defs.clone());",
        "    // mutated: model defs not handed to the model",
        "c3_model_values_are_the_values_the_failing_execution_computes",
    ),
    Mutation(
        "M13", SMT,
        "        let level = crate::messages::MessageLevel::Note;",
        "        let level = crate::messages::MessageLevel::Warning;",
        "c2_one_counterexample_is_reported_for_the_invalid_query",
    ),
]

# Mutations that are deliberately not expected to die, each with the reason.
DECLARED_SURVIVORS = [
    Mutation(
        "S1", SMT,
        "        cx.assert_id =\n"
        "            discovered_assert_id.as_ref().and_then(|id| id.as_ref()).map(|id| (**id).clone());",
        "        cx.assert_id = None;",
        killer="",
        why="AIR's textual grammar has no form that attaches an assert-id to an "
            "assertion (parser.rs builds StmtX::Assert with None), so no query "
            "expressible in these checks carries one. The field is exercised only "
            "through its JSON round trip in C9. Covering it needs a caller that "
            "builds the AST directly -- rust_verify does, and Venir goes through "
            "rust_verify, so this is covered at the next level up rather than here.",
    ),
]

TEST_LINE = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored)")


@dataclass
class RunResult:
    rc: int
    passed: list = field(default_factory=list)
    failed: list = field(default_factory=list)

    @property
    def total(self):
        return len(self.passed) + len(self.failed)


def run_suite() -> RunResult:
    proc = subprocess.run(
        ["cargo", "test", "-p", "air", "--test", "counterexample", "--", "--nocapture"],
        cwd=SOURCE, capture_output=True, text=True, timeout=900,
    )
    out = proc.stdout + proc.stderr
    res = RunResult(rc=proc.returncode)
    for line in out.splitlines():
        m = TEST_LINE.match(line.strip())
        if m:
            (res.passed if m.group(2) == "ok" else res.failed).append(m.group(1))
    if res.total == 0:
        # A compile error, a missing solver, or a harness that never started.
        # This is not a kill; report it verbatim so the reason is visible.
        print("---- suite produced no test result lines; last 40 lines follow ----")
        print("\n".join(out.splitlines()[-40:]))
    return res


def apply(mut: Mutation) -> str:
    path = AIR / mut.path
    original = path.read_text()
    if original.count(mut.find) != 1:
        raise SystemExit(
            f"{mut.id}: pattern occurs {original.count(mut.find)} times in {mut.path}, "
            f"expected exactly 1. The mutation table has drifted from the source."
        )
    path.write_text(original.replace(mut.find, mut.replace))
    return original


def restore(mut: Mutation, original: str):
    (AIR / mut.path).write_text(original)


def main() -> int:
    print("== control ==")
    control = run_suite()
    if control.failed or control.total == 0:
        print(f"CONTROL IS NOT GREEN: rc={control.rc} failed={control.failed} total={control.total}")
        return 1
    baseline = sorted(control.passed)
    print(f"control: rc={control.rc}, {len(baseline)} tests, 0 failures")
    print(f"tests: {', '.join(baseline)}\n")

    rows = []
    problems = 0

    for mut in MUTATIONS:
        original = apply(mut)
        try:
            res = run_suite()
        finally:
            restore(mut, original)
        if res.total == 0:
            verdict, note = "HARNESS-ERROR", "suite produced no results"
            problems += 1
        elif not res.failed:
            verdict, note = "SURVIVED", "no check noticed"
            problems += 1
        elif mut.killer in res.failed:
            others = [f for f in res.failed if f != mut.killer]
            verdict = "killed"
            note = mut.killer + (f" (+{len(others)} more)" if others else "")
        else:
            verdict, note = "MISDIRECTED", f"died in {', '.join(res.failed)} but not {mut.killer}"
            problems += 1
        rows.append((mut.id, mut.path, verdict, note))
        print(f"{mut.id:<4} {verdict:<14} {note}")

    print()
    for mut in DECLARED_SURVIVORS:
        original = apply(mut)
        try:
            res = run_suite()
        finally:
            restore(mut, original)
        if res.total == 0:
            verdict, note = "HARNESS-ERROR", "suite produced no results"
            problems += 1
        elif res.failed:
            verdict = "NO-LONGER-A-SURVIVOR"
            note = f"now killed by {', '.join(res.failed)}; the recorded reason is stale"
            problems += 1
        else:
            verdict, note = "survived (declared)", mut.why
        rows.append((mut.id, mut.path, verdict, note))
        print(f"{mut.id:<4} {verdict:<14} {note}")

    print()
    killed = sum(1 for r in rows if r[2] == "killed")
    declared = sum(1 for r in rows if r[2].startswith("survived (declared)"))
    print(f"{killed} killed, {declared} declared survivors, {problems} problems")
    return 0 if problems == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
