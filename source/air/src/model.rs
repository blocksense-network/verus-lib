//! Provides an AIR-level interface to the model returned by the SMT solver
//! when it reaches a SAT conclusion

use crate::ast::{Binders, Decl, DeclX, Ident, Snapshots, Typ, TypX};
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// For now, expressions are just strings, but we can later change this to a more detailed enum
pub type ModelExpr = Arc<String>;

/// Represent (define-fun f (...parameters...) return-type body) from SMT model
/// (This includes constants, which have an empty parameter list.)
pub type ModelDef = Arc<ModelDefX>;
pub type ModelDefs = Arc<Vec<ModelDef>>;
#[derive(Debug)]
pub struct ModelDefX {
    pub name: Ident,
    pub params: Binders<Typ>,
    pub ret: Typ,
    pub body: ModelExpr,
}

/// Render an AIR sort the way the SMT-LIB text spells it, so that a consumer
/// outside this crate can read a value without depending on `TypX`.
pub fn typ_to_smt_name(typ: &Typ) -> String {
    match &**typ {
        TypX::Bool => "Bool".to_string(),
        TypX::Int => "Int".to_string(),
        TypX::Fun => "Fun".to_string(),
        TypX::Named(x) => (**x).clone(),
        TypX::BitVec(n) => format!("(_ BitVec {})", n),
    }
}

/// One variable's assignment in a counterexample.
///
/// `variable` is the name the AIR query declared; `constant` is the Z3-level
/// constant that `var_to_const` renamed it to at this program point, and is the
/// name under which the assignment appears in the solver's `(get-model)`
/// response. Keeping both is what lets a consumer check that a value was read
/// out of the model under the name the query actually asked about.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModelBinding {
    pub variable: String,
    pub constant: String,
    /// The solver's assignment, verbatim from the body of its `(define-fun ...)`.
    pub value: String,
    /// The sort the solver gave the constant.
    pub typ: String,
}

/// The assignments in force at one recorded program point.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModelSnapshot {
    pub snapshot_id: String,
    pub bindings: Vec<ModelBinding>,
}

/// A concrete counterexample: every value the solver committed to, positioned at
/// the program points the query recorded snapshots for.
///
/// This is assembled from data the solver already returns. It requires no second
/// query, no live solver process and no `rustc` -- see [`Model::counterexample`].
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counterexample {
    /// Values for query parameters, which have no snapshot of their own.
    pub parameters: Vec<ModelBinding>,
    /// Values per recorded program point, in snapshot-declaration order.
    pub snapshots: Vec<ModelSnapshot>,
    /// The identifier of the assertion the solver found violated, when the query
    /// carried one. This is what ties a counterexample to the obligation it is a
    /// counterexample *to*; a consumer that cannot match it must not claim the
    /// two belong together.
    #[serde(default)]
    pub assert_id: Option<Vec<u64>>,
}

impl Counterexample {
    /// True when the solver committed to at least one value. A counterexample
    /// with no bindings carries no more information than the located obligation
    /// that came with it, and a consumer must not offer to step through it.
    pub fn is_populated(&self) -> bool {
        !self.parameters.is_empty() || self.snapshots.iter().any(|s| !s.bindings.is_empty())
    }
}

#[derive(Clone, Debug)]
/// AIR-level model of a concrete counterexample
pub struct Model {
    /// Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    /// Generated when converting mutable variables to Z3-level constants.
    id_snapshots: Snapshots,
    /// The parameters of the function, in declaration order, with their sorts
    parameters: IndexMap<Ident, Typ>,
    /// The solver's `(get-model)` response, keyed by the constant each
    /// `define-fun` defines. Empty until [`Model::set_defs`] is called, which
    /// `smt_get_model` does as soon as it has parsed the response.
    defs: HashMap<Ident, ModelDef>,
}

impl Model {
    /// Returns an (unpopulated) AIR model object.  Must call [build()] to fully populate.
    /// # Arguments
    /// * `model` - The model that Z3 returns
    /// * `snapshots` - Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    pub fn new(snapshots: Snapshots, params: Vec<Decl>) -> Model {
        // println!("Creating a new model with {} snapshots", snapshots.len());
        // for (sid, snapshot) in &snapshots {
        //     println!("{:?}", sid);
        //     for (name, num) in snapshot {
        //         println!("{:?} {}", name, num);
        //     }
        // }

        let mut parameters = IndexMap::new();
        for param in params {
            if let DeclX::Const(name, typ) = &*param {
                parameters.insert(name.clone(), typ.clone());
            }
        }

        Model { id_snapshots: snapshots, parameters, defs: HashMap::new() }
    }

    /// Record the solver's `(get-model)` response against this model.
    ///
    /// Without this the model maps variables to Z3 constant *names* and to
    /// nothing else, which is what it did before: the response was parsed,
    /// consulted for the failing label, and dropped.
    pub fn set_defs(&mut self, defs: HashMap<Ident, ModelDef>) {
        self.defs = defs;
    }

    pub fn translate_variable(&self, sid: &Ident, name: &Ident) -> Option<String> {
        // look for variable in the snapshot first
        let id_snapshot = &self.id_snapshots.get(sid)?;
        if let Some(var_label) = id_snapshot.get(name) {
            return Some(crate::var_to_const::rename_var(name, *var_label));
        }
        // then look in the parameter list
        if self.parameters.contains_key(name) {
            return Some((**name).clone());
        }
        None
    }

    fn binding(&self, variable: &Ident, constant: &str) -> Option<ModelBinding> {
        let def = self.defs.get(&constant.to_string())?;
        Some(ModelBinding {
            variable: (**variable).clone(),
            constant: constant.to_string(),
            value: (*def.body).clone(),
            typ: typ_to_smt_name(&def.ret),
        })
    }

    /// Snapshot ids **in program order** -- the order `var_to_const` reached the
    /// `snapshot` statements while walking the query. This is what makes the
    /// counterexample steppable: a consumer can walk these points in this order
    /// and be walking the path the model forced. Sorting them instead would be
    /// deterministic and wrong, which is worse.
    ///
    /// What this order does *not* carry is source positions. The snapshot-to-span
    /// map is built in `vir`/`rust_verify` (`SnapPos`), not here, so a consumer
    /// that wants to put a value next to a line has to supply that mapping
    /// itself.
    pub fn snapshot_ids(&self) -> Vec<Ident> {
        self.id_snapshots.keys().cloned().collect()
    }

    /// The assignments in force at one program point, in the order the query
    /// declared the variables.
    pub fn bindings_at(&self, sid: &Ident) -> Vec<ModelBinding> {
        let Some(snapshot) = self.id_snapshots.get(sid) else {
            return Vec::new();
        };
        snapshot
            .iter()
            .filter_map(|(name, version)| {
                let constant = crate::var_to_const::rename_var(name, *version);
                self.binding(name, &constant)
            })
            .collect()
    }

    /// The assignments the solver gave the query's parameters, in declaration
    /// order. Parameters are not renamed, so they carry no snapshot.
    pub fn parameter_bindings(&self) -> Vec<ModelBinding> {
        self.parameters.keys().filter_map(|name| self.binding(name, name)).collect()
    }

    /// Assemble the whole counterexample.
    pub fn counterexample(&self) -> Counterexample {
        Counterexample {
            parameters: self.parameter_bindings(),
            snapshots: self
                .snapshot_ids()
                .into_iter()
                .map(|sid| ModelSnapshot {
                    snapshot_id: (*sid).clone(),
                    bindings: self.bindings_at(&sid),
                })
                .collect(),
            assert_id: None,
        }
    }
}

/// Prefix on the note of the diagnostic that carries a counterexample.
///
/// The counterexample travels as an ordinary `Note` rather than as a new message
/// type because `ArcDynMessage` is `Arc<dyn Any>` and every consumer downcasts it
/// to the one type it knows: introducing a second type would panic every
/// `Diagnostics` implementation that is not looking for it, including the one
/// `rust_verify` uses to talk to `rustc`.
pub const COUNTEREXAMPLE_NOTE_PREFIX: &str = "air-counterexample-model ";

/// Off by default. `air` reports counterexample models only when a caller has
/// asked for them, because the note it emits is machine-readable JSON that would
/// otherwise appear in ordinary human-facing verifier output.
static REPORT_COUNTEREXAMPLE: AtomicBool = AtomicBool::new(false);

pub fn set_report_counterexample(enabled: bool) {
    REPORT_COUNTEREXAMPLE.store(enabled, Ordering::SeqCst);
}

pub fn report_counterexample_enabled() -> bool {
    REPORT_COUNTEREXAMPLE.load(Ordering::SeqCst)
}

/// Render a counterexample as the note text of the diagnostic that carries it.
pub fn counterexample_note(cx: &Counterexample) -> String {
    format!(
        "{}{}",
        COUNTEREXAMPLE_NOTE_PREFIX,
        serde_json::to_string(cx).expect("counterexample is serializable")
    )
}

/// Recover a counterexample from a note produced by [`counterexample_note`].
/// Returns `None` for any note that is not one, which is every other note.
pub fn counterexample_from_note(note: &str) -> Option<Counterexample> {
    let json = note.strip_prefix(COUNTEREXAMPLE_NOTE_PREFIX)?;
    serde_json::from_str(json).ok()
}
