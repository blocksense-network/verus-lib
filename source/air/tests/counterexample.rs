//! Integration checks for the counterexample model AIR now reports.
//!
//! Every check in this file drives a **real solver**. There is no fixture and no
//! recorded transcript: `run_query` starts z3, sends a query, and reads what came
//! back. A check that cannot reach z3 **fails**; it does not skip. A skipped check
//! and a passing check are indistinguishable in a summary line, which is the
//! failure mode `Testing/Verification-Harness-Traps.md` records as "a harness
//! reporting a state it did not reach".
//!
//! The load-bearing property is C3/C5: a counterexample that is *wrong* is worse
//! than no counterexample, so it is not enough to observe that a model-shaped
//! object arrived. C3 compares every value against the value the failing
//! execution computes, worked out in Rust without asking the solver. C5 hands the
//! model to a **second, independent** z3 process together with the program's
//! semantics transcribed by hand, and asks whether the model really is an
//! execution that violates the obligation. C6 is C5's mutation arm and lives in
//! the suite rather than in the mutation harness, because "one wrong value is
//! rejected" is a property of the product, not of the tests.

use air::ast::CommandX;
use air::context::{Context, SmtSolver, ValidityResult};
use air::messages::{AirMessage, ArcDynMessage, Diagnostics, MessageLevel};
use air::model::{self, Counterexample, ModelBinding};
use std::io::Write;
use std::sync::{Mutex, MutexGuard, OnceLock};

// ---------------------------------------------------------------------------
// harness
// ---------------------------------------------------------------------------

/// `air::model::set_report_counterexample` is process-wide, and `cargo test` runs
/// these in parallel threads. Every check takes this lock for its whole run, so
/// no check can observe a neighbour's setting.
fn reporting_lock() -> MutexGuard<'static, ()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    match LOCK.get_or_init(|| Mutex::new(())).lock() {
        Ok(g) => g,
        Err(poisoned) => poisoned.into_inner(),
    }
}

#[derive(Default)]
struct Capture {
    notes: Mutex<Vec<String>>,
    others: Mutex<Vec<(MessageLevel, String)>>,
}

impl Diagnostics for Capture {
    fn report_as(&self, msg: &ArcDynMessage, level: MessageLevel) {
        let msg =
            msg.downcast_ref::<AirMessage>().expect("air's own reporter only ever sees AirMessage");
        match level {
            MessageLevel::Note => self.notes.lock().unwrap().push(msg.note.clone()),
            other => self.others.lock().unwrap().push((other, msg.note.clone())),
        }
    }
    fn report(&self, msg: &ArcDynMessage) {
        let level = msg.downcast_ref::<AirMessage>().unwrap().level;
        self.report_as(msg, level)
    }
    fn report_now(&self, msg: &ArcDynMessage) {
        self.report(msg)
    }
    fn report_as_now(&self, msg: &ArcDynMessage, level: MessageLevel) {
        self.report_as(msg, level)
    }
}

struct RunOutcome {
    /// One entry per note the solver run emitted that parsed as a counterexample.
    counterexamples: Vec<Counterexample>,
    /// Notes that were *not* counterexamples, kept so a check can say so.
    other_notes: Vec<String>,
    invalid_queries: usize,
    valid_queries: usize,
}

/// Parse `src` as AIR, run it against a real z3, and collect what the reporter saw.
fn run_query(src: &str, report_counterexamples: bool) -> RunOutcome {
    require_z3();
    let message_interface = std::sync::Arc::new(air::messages::AirMessageInterface {});
    let capture = Capture::default();

    let mut bytes: Vec<u8> = Vec::new();
    bytes.push(b'(');
    bytes.extend_from_slice(src.as_bytes());
    bytes.push(b')');
    let mut parser = sise::Parser::new(&bytes);
    let node = sise::read_into_tree(&mut parser).expect("test query is well-formed s-expression");
    let nodes = match node {
        sise::Node::List(nodes) => nodes,
        sise::Node::Atom(_) => panic!("test query is not a list"),
    };
    let commands = air::parser::Parser::new(message_interface.clone())
        .nodes_to_commands(&nodes)
        .expect("test query parses as AIR");

    model::set_report_counterexample(report_counterexamples);
    let mut ctx = Context::new(message_interface.clone(), SmtSolver::Z3);
    ctx.set_z3_param("air_recommended_options", "true");

    let mut invalid_queries = 0;
    let mut valid_queries = 0;
    for command in commands.iter() {
        let result = ctx.command(&*message_interface, &capture, command, Default::default());
        match result {
            ValidityResult::Valid(..) => {
                if matches!(**command, CommandX::CheckValid(..)) {
                    valid_queries += 1;
                }
            }
            ValidityResult::Invalid(..) => invalid_queries += 1,
            other => panic!("unexpected solver outcome: {:?}", other),
        }
        if matches!(**command, CommandX::CheckValid(..)) {
            ctx.finish_query();
        }
    }
    model::set_report_counterexample(false);

    let notes = capture.notes.lock().unwrap().clone();
    let mut counterexamples = Vec::new();
    let mut other_notes = Vec::new();
    for note in notes {
        match model::counterexample_from_note(&note) {
            Some(cx) => counterexamples.push(cx),
            None => other_notes.push(note),
        }
    }
    RunOutcome { counterexamples, other_notes, invalid_queries, valid_queries }
}

/// A missing solver is a failure, not a skip.
fn require_z3() {
    let exe = std::env::var("VERUS_Z3_PATH").unwrap_or_else(|_| "z3".to_string());
    let out = std::process::Command::new(&exe).arg("--version").output();
    match out {
        Ok(o) if o.status.success() => {}
        Ok(o) => panic!("`{} --version` exited {:?}; these checks need a solver", exe, o.status),
        Err(e) => panic!(
            "cannot start `{}`: {e}. These checks drive a real solver and do not skip without one; \
             run them with z3 on PATH or VERUS_Z3_PATH set.",
            exe
        ),
    }
}

/// Ask a **second, independent** z3 -- a fresh process, given a script this test
/// wrote -- whether `script` is satisfiable. Returns the verbatim verdict.
fn ask_fresh_solver(script: &str) -> String {
    require_z3();
    let exe = std::env::var("VERUS_Z3_PATH").unwrap_or_else(|_| "z3".to_string());
    let dir = std::env::temp_dir();
    let path = dir.join(format!(
        "air-cx-check-{}-{:?}.smt2",
        std::process::id(),
        std::thread::current().id()
    ));
    let mut f = std::fs::File::create(&path).expect("scratch file");
    f.write_all(script.as_bytes()).expect("write scratch file");
    drop(f);
    let out = std::process::Command::new(&exe)
        .arg("-smt2")
        .arg(&path)
        .output()
        .expect("second solver runs");
    let _ = std::fs::remove_file(&path);
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

fn binding<'a>(bindings: &'a [ModelBinding], variable: &str) -> Option<&'a ModelBinding> {
    bindings.iter().find(|b| b.variable == variable)
}

fn snapshot<'a>(cx: &'a Counterexample, id: &str) -> &'a [ModelBinding] {
    cx.snapshots
        .iter()
        .find(|s| s.snapshot_id == id)
        .unwrap_or_else(|| panic!("counterexample has no snapshot {}: {:?}", id, cx))
        .bindings
        .as_slice()
}

/// Counted assertions. Each check prints how many it made, so a check that
/// silently stopped asserting is visible in the output rather than green.
struct Counted {
    name: &'static str,
    n: usize,
}
impl Counted {
    fn new(name: &'static str) -> Counted {
        Counted { name, n: 0 }
    }
    fn eq<T: std::fmt::Debug + PartialEq>(&mut self, what: &str, actual: T, expected: T) {
        self.n += 1;
        assert_eq!(actual, expected, "[{}] {}", self.name, what);
    }
    fn that(&mut self, what: &str, cond: bool) {
        self.n += 1;
        assert!(cond, "[{}] {}", self.name, what);
    }
    fn done(self, expected: usize) {
        assert_eq!(
            self.n, expected,
            "[{}] made {} assertions, expected {}",
            self.name, self.n, expected
        );
        println!("[{}] {} assertions", self.name, self.n);
    }
}

// ---------------------------------------------------------------------------
// the programs under test
// ---------------------------------------------------------------------------

/// A failing query whose failing execution is **unique**: `n` is pinned, and both
/// assignments are deterministic, so there is exactly one assignment of values
/// that reaches the assertion, and the solver has no freedom to invent another.
/// That is what makes C3 a correspondence check rather than a shape check.
const STRAIGHT_LINE: &str = r#"
(check-valid
  (declare-const n Int)
  (declare-var a Int)
  (declare-var b Int)
  (block
    (assume (= n 42))
    (assign a (+ n 1))
    (snapshot after_a)
    (assign b (* a 2))
    (snapshot after_b)
    (assert (< b 0))
  )
)
"#;

/// The same idea with a branch: `n` is pinned to 7, so only the `then` arm is
/// feasible, and the value at `after` says which arm the model took.
const BRANCHING: &str = r#"
(check-valid
  (declare-const n Int)
  (declare-var a Int)
  (block
    (assume (= n 7))
    (switch
      (block (assume (> n 5)) (assign a 100))
      (block (assume (not (> n 5))) (assign a 200)))
    (snapshot after)
    (assert (= a 200))
  )
)
"#;

const VALID: &str = r#"
(check-valid
  (declare-const n Int)
  (declare-var a Int)
  (block
    (assume (= n 42))
    (assign a (+ n 1))
    (snapshot after_a)
    (assert (= a 43))
  )
)
"#;

/// No parameters and no snapshots: the solver still finds the query invalid, but
/// there is nothing to step through.
const NOTHING_TO_SHOW: &str = r#"
(check-valid
  (block
    (assert false)
  )
)
"#;

// The values the failing execution of STRAIGHT_LINE computes, worked out here
// rather than read back out of the solver.
const EXPECTED_N: i64 = 42;
const EXPECTED_A: i64 = EXPECTED_N + 1;
const EXPECTED_B: i64 = EXPECTED_A * 2;

// ---------------------------------------------------------------------------
// C1 -- control arm: reporting off
// ---------------------------------------------------------------------------

#[test]
fn c1_control_no_counterexample_is_reported_when_reporting_is_off() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C1");
    let run = run_query(STRAIGHT_LINE, false);

    c.eq("the query is still invalid", run.invalid_queries, 1);
    c.eq("no counterexample note was emitted", run.counterexamples.len(), 0);
    c.eq("and no note of any kind was emitted", run.other_notes.len(), 0);
    c.done(3);
}

// ---------------------------------------------------------------------------
// C2 -- one counterexample per invalid query, and none for a valid one
// ---------------------------------------------------------------------------

#[test]
fn c2_one_counterexample_is_reported_for_the_invalid_query() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C2");
    let run = run_query(STRAIGHT_LINE, true);

    c.eq("the query is invalid", run.invalid_queries, 1);
    c.eq("exactly one counterexample", run.counterexamples.len(), 1);
    c.eq("and no note that was not one", run.other_notes.len(), 0);
    c.that("the counterexample carries values", run.counterexamples[0].is_populated());
    c.done(4);
}

#[test]
fn c7_control_a_valid_query_reports_no_counterexample() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C7");
    let run = run_query(VALID, true);

    c.eq("the query verifies", run.valid_queries, 1);
    c.eq("nothing was invalid", run.invalid_queries, 0);
    c.eq("no counterexample was reported", run.counterexamples.len(), 0);
    c.done(3);
}

// ---------------------------------------------------------------------------
// C3 -- the correspondence: the model *is* the failing execution
// ---------------------------------------------------------------------------

#[test]
fn c3_model_values_are_the_values_the_failing_execution_computes() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C3");
    let run = run_query(STRAIGHT_LINE, true);
    c.eq("exactly one counterexample", run.counterexamples.len(), 1);
    let cx = &run.counterexamples[0];

    // The parameter the execution starts from.
    let n = binding(&cx.parameters, "n").expect("model binds the parameter n");
    c.eq("n is the pinned input", n.value.as_str(), EXPECTED_N.to_string().as_str());
    c.eq("n is an Int", n.typ.as_str(), "Int");
    c.eq("n was read under its own name", n.constant.as_str(), "n");

    // After the first assignment.
    let after_a = snapshot(cx, "after_a");
    let a1 = binding(after_a, "a").expect("model binds a at after_a");
    c.eq("a is n + 1", a1.value.as_str(), EXPECTED_A.to_string().as_str());
    c.that(
        "a was read under a renamed constant, not under its source name",
        a1.constant != a1.variable && a1.constant.starts_with("a@"),
    );

    // After the second assignment: a is unchanged and b is derived from it.
    let after_b = snapshot(cx, "after_b");
    let a2 = binding(after_b, "a").expect("model binds a at after_b");
    let b2 = binding(after_b, "b").expect("model binds b at after_b");
    c.eq("a is unchanged at the second point", a2.value.as_str(), a1.value.as_str());
    c.eq("b is a * 2", b2.value.as_str(), EXPECTED_B.to_string().as_str());

    // The obligation `(< b 0)` is what failed, and the model is why.
    c.that("the model violates the obligation", b2.value.parse::<i64>().unwrap() >= 0);

    // The two program points are distinguishable: b's constant differs between
    // them, so the counterexample really is positioned rather than flat.
    let b1 = binding(after_a, "b");
    c.that(
        "b at the two points is not the same constant",
        b1.map(|b| b.constant.as_str()) != Some(b2.constant.as_str()),
    );

    c.done(10);
}

// ---------------------------------------------------------------------------
// C4 -- the path the model forced
// ---------------------------------------------------------------------------

#[test]
fn c4_the_model_shows_which_branch_it_took() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C4");
    let run = run_query(BRANCHING, true);
    c.eq("exactly one counterexample", run.counterexamples.len(), 1);
    let cx = &run.counterexamples[0];

    let n = binding(&cx.parameters, "n").expect("model binds n");
    c.eq("n is 7, so only the then-arm is reachable", n.value.as_str(), "7");

    let after = snapshot(cx, "after");
    let a = binding(after, "a").expect("model binds a after the branch");
    c.eq("a holds the then-arm's value", a.value.as_str(), "100");
    c.that("a does not hold the else-arm's value", a.value != "200");
    c.done(4);
}

// ---------------------------------------------------------------------------
// C5/C6 -- an independent solver agrees, and disagrees when one value is wrong
// ---------------------------------------------------------------------------

/// Transcribe STRAIGHT_LINE's semantics by hand and pin the model's values on
/// top of it. `sat` means: these values are an execution of this program that
/// violates the obligation. Nothing in `air` participates in this judgement.
fn independent_check_script(n: &str, a: &str, b: &str) -> String {
    format!(
        "(declare-const n Int)\n\
         (declare-const a Int)\n\
         (declare-const b Int)\n\
         ; the model's claim\n\
         (assert (= n {n}))\n\
         (assert (= a {a}))\n\
         (assert (= b {b}))\n\
         ; the program, transcribed here and not taken from air\n\
         (assert (= n 42))\n\
         (assert (= a (+ n 1)))\n\
         (assert (= b (* a 2)))\n\
         ; and the obligation is violated\n\
         (assert (not (< b 0)))\n\
         (check-sat)\n"
    )
}

fn straight_line_values() -> (String, String, String) {
    let run = run_query(STRAIGHT_LINE, true);
    assert_eq!(run.counterexamples.len(), 1, "expected one counterexample");
    let cx = &run.counterexamples[0];
    let n = binding(&cx.parameters, "n").expect("n").value.clone();
    let after_b = snapshot(cx, "after_b");
    let a = binding(after_b, "a").expect("a").value.clone();
    let b = binding(after_b, "b").expect("b").value.clone();
    (n, a, b)
}

#[test]
fn c5_an_independent_solver_confirms_the_model_is_a_violating_execution() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C5");
    let (n, a, b) = straight_line_values();

    let verdict = ask_fresh_solver(&independent_check_script(&n, &a, &b));
    c.eq("the second solver accepts the model", verdict.as_str(), "sat");
    c.done(1);
}

#[test]
fn c6_mutation_arm_one_wrong_value_is_rejected_by_the_independent_solver() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C6");
    let (n, a, b) = straight_line_values();

    // Establish the control first, in this same arm, so a "rejects everything"
    // oracle cannot pass this check.
    c.eq(
        "control: the unperturbed model is accepted",
        ask_fresh_solver(&independent_check_script(&n, &a, &b)).as_str(),
        "sat",
    );

    let bump = |v: &str| (v.parse::<i64>().expect("integer model value") + 1).to_string();
    c.eq(
        "a wrong n is rejected",
        ask_fresh_solver(&independent_check_script(&bump(&n), &a, &b)).as_str(),
        "unsat",
    );
    c.eq(
        "a wrong a is rejected",
        ask_fresh_solver(&independent_check_script(&n, &bump(&a), &b)).as_str(),
        "unsat",
    );
    c.eq(
        "a wrong b is rejected",
        ask_fresh_solver(&independent_check_script(&n, &a, &bump(&b))).as_str(),
        "unsat",
    );
    c.done(4);
}

// ---------------------------------------------------------------------------
// C8 -- a model-shaped object that carries nothing is not steppable
// ---------------------------------------------------------------------------

#[test]
fn c8_a_counterexample_with_no_bindings_is_not_populated() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C8");
    let run = run_query(NOTHING_TO_SHOW, true);

    c.eq("the query is invalid", run.invalid_queries, 1);
    c.eq("a counterexample was still reported", run.counterexamples.len(), 1);
    let cx = &run.counterexamples[0];
    c.eq("it binds no parameters", cx.parameters.len(), 0);
    c.that("it binds nothing anywhere", cx.snapshots.iter().all(|s| s.bindings.is_empty()));
    c.that("so it does not read as populated", !cx.is_populated());

    // and the contrast, in the same arm
    let populated = run_query(STRAIGHT_LINE, true);
    c.that("while the straight-line one does", populated.counterexamples[0].is_populated());
    c.done(6);
}

// ---------------------------------------------------------------------------
// C10 -- the emitted order is stable, and sorts are the solver's own
// ---------------------------------------------------------------------------

/// Snapshots are reached as `zeta` then `alpha`, so program order and sorted
/// order disagree and the check can tell which one was emitted -- a sorted list
/// would be deterministic and would step the program backwards. `flag` is a Bool
/// so that the sort a binding reports is not always `Int`.
const ORDERING: &str = r#"
(check-valid
  (declare-const n Int)
  (declare-var a Int)
  (declare-var flag Bool)
  (block
    (assume (= n 3))
    (assign a n)
    (assign flag (> n 0))
    (snapshot zeta)
    (assign a (+ a 1))
    (snapshot alpha)
    (assert (= a 0))
  )
)
"#;

#[test]
fn c10_snapshots_are_emitted_in_program_order_and_carry_the_solver_s_sorts() {
    let _lock = reporting_lock();
    let mut c = Counted::new("C10");
    let run = run_query(ORDERING, true);
    c.eq("exactly one counterexample", run.counterexamples.len(), 1);
    let cx = &run.counterexamples[0];

    let ids: Vec<&str> = cx.snapshots.iter().map(|s| s.snapshot_id.as_str()).collect();
    c.eq("snapshots come out in program order, not sorted", ids, vec!["zeta", "alpha"]);

    let zeta = snapshot(cx, "zeta");
    let alpha = snapshot(cx, "alpha");
    c.eq("a is n at the first point", binding(zeta, "a").expect("a@zeta").value.as_str(), "3");
    c.eq("a is n + 1 at the second", binding(alpha, "a").expect("a@alpha").value.as_str(), "4");

    let flag = binding(zeta, "flag").expect("flag@zeta");
    c.eq("a Bool reports the Bool sort", flag.typ.as_str(), "Bool");
    c.eq("and the value the solver gave it", flag.value.as_str(), "true");
    c.eq("while an Int reports Int", binding(zeta, "a").unwrap().typ.as_str(), "Int");
    c.done(7);
}

// ---------------------------------------------------------------------------
// C9 -- the note boundary
// ---------------------------------------------------------------------------

#[test]
fn c9_only_a_counterexample_note_decodes_as_one() {
    let mut c = Counted::new("C9");
    let cx = Counterexample {
        parameters: vec![ModelBinding {
            variable: "x".into(),
            constant: "x".into(),
            value: "1".into(),
            typ: "Int".into(),
        }],
        snapshots: vec![],
        assert_id: Some(vec![3, 1, 4]),
    };
    let note = model::counterexample_note(&cx);
    // The same JSON with the prefix removed: a note that is *shaped* like a
    // counterexample but was not announced as one must not decode. The prefix is
    // the whole discriminator, so a decoder that fell back to "try parsing it
    // anyway" would adopt any JSON note that crossed this boundary.
    let unannounced = note
        .strip_prefix(model::COUNTEREXAMPLE_NOTE_PREFIX)
        .expect("the note we just wrote carries the prefix")
        .to_string();
    c.eq("a counterexample note round-trips", model::counterexample_from_note(&note), Some(cx));

    for other in [
        "",
        "Verification results:: 0 verified, 1 errors",
        "air-counterexample-model",
        "air-counterexample-model not json",
        " air-counterexample-model {}",
        unannounced.as_str(),
    ] {
        c.eq(
            &format!("{other:?} is not a counterexample"),
            model::counterexample_from_note(other),
            None,
        );
    }
    c.done(7);
}
