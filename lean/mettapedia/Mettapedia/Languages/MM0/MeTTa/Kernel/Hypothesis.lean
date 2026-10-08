import Mettapedia.Languages.MM0.MeTTa.Data.VectorAccess
import Mettapedia.Languages.MM0.MeTTa.Data.Data
import Mettapedia.Languages.MM0.Kernel.ProofSharing

/-!
# The hypothesis branch of the retained MM0 checker

These paths execute the actual pinned proof equation. A hypothesis witness
reads the supplied hypotheses directly and returns a completed absence when
its index is missing. The branch neither searches for evidence nor changes
the theory or the source store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Hypothesis

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom applySubst_nil)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open Store (natural)
open ListAccess (listValue optionValue)

/-- The service supplies inline hypotheses during declaration admission and
uses a saved vector while checking chronological shared proofs. -/
inductive Storage where
  | inline
  | vector
  deriving DecidableEq

/-- The input value used by the existing source data-access function. -/
def value (storage : Storage) (handle : NamedSpaces.Handle) (values : List Atom) : Atom :=
  match storage with
  | .inline => listValue values
  | .vector => VectorAccess.vectorValue handle values.length

/-- Inline input is the supplied list itself. Vector input requires an actual
physical representation in the source store. -/
inductive Ready : Storage → NamedSpaces.Handle → List Atom → State → Prop where
  | inline {handle values state} : Ready .inline handle values state
  | vector {handle values state} (represented : Store.Represents state handle (Store.enumerate values)) :
      Ready .vector handle values state

theorem Ready.vector_represents {storage : Storage} {handle : NamedSpaces.Handle}
    {values : List Atom} {state : State} (ready : Ready storage handle values state)
    (mode : storage = .vector) : Store.Represents state handle (Store.enumerate values) := by
  cases ready with
  | inline => cases mode
  | vector represented => exact represented

theorem Ready.after_reads {storage : Storage} {handle : NamedSpaces.Handle}
    {values : List Atom} {before after : State} (ready : Ready storage handle values before)
    (same : after.read handle = before.read handle) : Ready storage handle values after := by
  cases ready with
  | inline => exact .inline
  | vector represented =>
      apply Ready.vector
      change after.read handle = some (Store.rows (Store.enumerate values))
      rw [same]
      exact represented

/-- Both admitted input layouts execute through the retained `mm0:data-at`;
missing positions return `None` without reading any other store. -/
theorem data_at_returns (bindings : Subst) (state : State) (storage : Storage)
    (handle : NamedSpaces.Handle) (values : List Atom) (index : Nat) (hypothesesName indexName : String)
    (ready : Ready storage handle values state)
    (capturedHypotheses : applySubst bindings (.var hypothesesName) = value storage handle values)
    (capturedIndex : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:data-at", .var hypothesesName, .var indexName]) state (optionValue (values[index]?)) := by
  cases ready with
  | inline =>
      exact ListAccess.data_at_list_returns bindings state values index hypothesesName indexName
        capturedHypotheses capturedIndex
  | vector represented =>
      have computed := VectorAccess.vector_returns bindings state handle (Store.rows (Store.enumerate values))
        values.length index hypothesesName indexName represented capturedHypotheses capturedIndex
      by_cases bounded : index < values.length
      · simpa [bounded, Store.query_dense_prefix, List.getElem?_eq_getElem bounded,
          VectorAccess.queryAnswer, optionValue] using computed
      · simpa [bounded, List.getElem?_eq_none (by omega : values.length ≤ index), optionValue] using computed

def witness (index : Nat) : Atom :=
  .expression [.symbol "MM0:L", .expression [.symbol "MM0:Hyp", natural index]]

private def environmentFor (table definitions theorems context hypotheses : Atom)
    (index : Nat) : Subst :=
  [("witness", witness index), ("hypotheses", hypotheses),
    ("context", context), ("theorems", theorems), ("definitions", definitions), ("table", table)]

private def environment (table definitions theorems context : Atom)
    (hypotheses : List Atom) (index : Nat) : Subst :=
  environmentFor table definitions theorems context (listValue hypotheses) index

theorem proof_clause_for (table definitions theorems context hypotheses : Atom) (index : Nat) :
    clauses program "mm0:proof"
      [table, definitions, theorems, context, hypotheses, witness index] =
      [.evaluate (environmentFor table definitions theorems context hypotheses index) proofEquation.body] := by
  rw [clauses_use_only_the_named_equations, proof_equation_is_unique]
  simp [proof_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environmentFor]

theorem proof_clause (table definitions theorems context : Atom)
    (hypotheses : List Atom) (index : Nat) :
    clauses program "mm0:proof"
      [table, definitions, theorems, context, listValue hypotheses, witness index] =
      [.evaluate (environment table definitions theorems context hypotheses index) proofEquation.body] :=
  proof_clause_for table definitions theorems context (listValue hypotheses) index

private def cases : SpaceSemantics.Cases :=
  match proofEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def hypBody : Atom := (cases[0]'(by decide)).2

private theorem body_is_case :
    proofEquation.body = .expression [.symbol "case", .var "witness",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by
  decide

private theorem cases_head :
    cases = (.expression [.symbol "MM0:L", .expression [.symbol "MM0:Hyp", .var "index"]],
      hypBody) :: cases.tail := by
  decide

private theorem hyp_body_shape :
    hypBody = .expression [.symbol "mm0:data-at", .var "hypotheses", .var "index"] := by
  decide

theorem proof_body_returns_from_read (state : State)
    (table definitions theorems context hypotheses : Atom) (index : Nat) (answer : Atom)
    (read : PureReturns program
      [("index", natural index), ("witness", witness index), ("hypotheses", hypotheses),
        ("context", context), ("theorems", theorems), ("definitions", definitions), ("table", table)]
      state (.expression [.symbol "mm0:data-at", .var "hypotheses", .var "index"]) state answer) :
    PureReturns program [("witness", witness index), ("hypotheses", hypotheses),
      ("context", context), ("theorems", theorems), ("definitions", definitions), ("table", table)]
      state proofEquation.body state answer := by
  let bindings := environmentFor table definitions theorems context hypotheses index
  let bound := ("index", natural index) :: bindings
  rw [body_is_case]
  apply case_returns program bindings bound state state state (.var "witness")
    (witness index) hypBody _ _ cases (read_cases_encoded cases)
  · simpa [bindings, environmentFor, applySubst, Subst.lookup] using
      variable_returns program bindings state "witness"
  · have matched : SpaceSemantics.matchValue bindings
        (.expression [.symbol "MM0:L", .expression [.symbol "MM0:Hyp", .var "index"]])
        (witness index) = some bound := by
      simp [bindings, bound, environmentFor, witness, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    rw [cases_head, SpaceSemantics.selectCase, matched]
  · simpa only [hyp_body_shape, bound, bindings, environmentFor] using read

theorem proof_body_returns (state : State) (table definitions theorems context : Atom)
    (hypotheses : List Atom) (index : Nat) :
    PureReturns program (environment table definitions theorems context hypotheses index)
      state proofEquation.body state (optionValue (hypotheses[index]?)) := by
  apply proof_body_returns_from_read
  let bound := ("index", natural index) :: environment table definitions theorems context hypotheses index
  change PureReturns program bound state _ state _
  apply ListAccess.data_at_list_returns bound state hypotheses index "hypotheses" "index"
  · simp [bound, environment, environmentFor, applySubst, Subst.lookup]
  · simp [bound, applySubst, Subst.lookup]

private theorem proof_returns_from_body (state : State)
    (table definitions theorems context hypotheses : Atom) (index : Nat) (answer : Atom)
    (body : PureReturns program (environmentFor table definitions theorems context hypotheses index)
      state proofEquation.body state answer) :
    PureReturns program [] state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        hypotheses, witness index]) state answer := by
  apply raw_call_returns program [] state state "mm0:proof" _ _ (by decide)
    _ _ (by decide)
  · intro position bounded
    have bound : position < 6 := bounded
    have positions : position = 0 ∨ position = 1 ∨ position = 2 ∨
        position = 3 ∨ position = 4 ∨ position = 5 := by omega
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.map, applySubst_nil]
    exact authored_function_arguments_return program []
      (environmentFor table definitions theorems context hypotheses index) state state "mm0:proof"
      [table, definitions, theorems, context, hypotheses, witness index] 6
      proofEquation.body _ (by decide) (by decide)
      (proof_clause_for table definitions theorems context hypotheses index) body

theorem proof_returns (state : State) (table definitions theorems context : Atom)
    (hypotheses : List Atom) (index : Nat) :
    PureReturns program [] state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        listValue hypotheses, witness index]) state (optionValue (hypotheses[index]?)) :=
  proof_returns_from_body state table definitions theorems context (listValue hypotheses) index _
    (proof_body_returns state table definitions theorems context hypotheses index)

theorem saved_hypothesis_returns (state : State) (table definitions theorems context : Atom)
    (handle : NamedSpaces.Handle) (rows : List Atom) (size index : Nat)
    (represented : state.read handle = some rows) :
    PureReturns program [] state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        VectorAccess.vectorValue handle size, witness index]) state
      (if index < size then VectorAccess.queryAnswer (Store.indexedQuery rows index)
        else .symbol "None") := by
  apply proof_returns_from_body
  apply proof_body_returns_from_read
  let bound := ("index", natural index) :: environmentFor table definitions theorems context
    (VectorAccess.vectorValue handle size) index
  change PureReturns program bound state _ state _
  apply VectorAccess.vector_returns bound state handle rows size index "hypotheses" "index" represented
  · simp [bound, environmentFor, applySubst, Subst.lookup]
  · simp [bound, applySubst, Subst.lookup]

theorem dense_saved_hypothesis_returns (state : State) (table definitions theorems context : Atom)
    (handle : NamedSpaces.Handle) (hypotheses : List Atom) (index : Nat)
    (represented : Store.Represents state handle (Store.enumerate hypotheses)) :
    PureReturns program [] state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        VectorAccess.vectorValue handle hypotheses.length, witness index]) state
      (optionValue (hypotheses[index]?)) := by
  have computed := saved_hypothesis_returns state table definitions theorems context handle
    (Store.rows (Store.enumerate hypotheses)) hypotheses.length index represented
  by_cases bounded : index < hypotheses.length
  · simpa [bounded, Store.query_dense_prefix, List.getElem?_eq_getElem bounded,
      VectorAccess.queryAnswer, optionValue] using computed
  · simpa [bounded, List.getElem?_eq_none (by omega : hypotheses.length ≤ index),
      optionValue] using computed

theorem proof_has_sufficient_fuel (state : State) (table definitions theorems context : Atom)
    (hypotheses : List Atom) (index : Nat) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        listValue hypotheses, witness index]) =
      .complete state [optionValue (hypotheses[index]?)] [] [] :=
  pure_returns_has_sufficient_fuel program [] state state _ _
    (proof_returns state table definitions theorems context hypotheses index)

/-- The source computation agrees with the independent kernel on every
hypothesis request. The other signature components are not read by this branch. -/
theorem proof_matches_kernel (state : State) (table definitions theorems context : Atom)
    (signature : Kernel.TermSignature) (kernelDefinitions : Kernel.Definition.Signature)
    (kernelTheorems : Kernel.TheoremSignature) (kernelContext : Kernel.Context)
    (hypotheses : List Kernel.Preterm) (index : Nat) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        listValue (hypotheses.map Data.preterm), witness index]) =
      .complete state [optionValue ((Kernel.ProofWitness.proof? signature kernelDefinitions
        kernelTheorems kernelContext hypotheses (.hyp index)).map Data.preterm)] [] [] := by
  simpa [Kernel.ProofWitness.proof?, List.getElem?_map] using
    proof_has_sufficient_fuel state table definitions theorems context (hypotheses.map Data.preterm) index

theorem checks_iff_source_accepts (state : State) (table definitions theorems context : Atom)
    (signature : Kernel.TermSignature) (kernelDefinitions : Kernel.Definition.Signature)
    (kernelTheorems : Kernel.TheoremSignature) (kernelContext : Kernel.Context)
    (hypotheses : List Kernel.Preterm) (index : Nat) (claim : Kernel.Preterm) :
    Kernel.ProofWitness.Checks signature kernelDefinitions kernelTheorems kernelContext
        hypotheses (.hyp index) claim ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
          listValue (hypotheses.map Data.preterm), witness index]) =
        .complete state [optionValue (some (Data.preterm claim))] [] [] := by
  rw [← Kernel.ProofWitness.proof_eq_some_iff]
  constructor
  · intro accepted
    simpa [accepted] using proof_matches_kernel state table definitions theorems context
      signature kernelDefinitions kernelTheorems kernelContext hypotheses index
  · rintro ⟨fuel, accepted⟩
    obtain ⟨referenceFuel, completed⟩ := proof_matches_kernel state table definitions theorems context
      signature kernelDefinitions kernelTheorems kernelContext hypotheses index
    have unique := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] []
      completed accepted
    have equal := List.singleton_inj.mp unique.2.1
    exact Data.optional_preterm_injective equal

theorem checks_iff_saved_hypothesis_accepts (state : State) (table definitions theorems context : Atom)
    (handle : NamedSpaces.Handle) (signature : Kernel.TermSignature)
    (kernelDefinitions : Kernel.Definition.Signature) (kernelTheorems : Kernel.TheoremSignature)
    (kernelContext : Kernel.Context) (hypotheses : List Kernel.Preterm) (index : Nat) (claim : Kernel.Preterm)
    (represented : Store.Represents state handle (Store.enumerate (hypotheses.map Data.preterm))) :
    Kernel.ProofWitness.Checks signature kernelDefinitions kernelTheorems kernelContext
        hypotheses (.hyp index) claim ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
          VectorAccess.vectorValue handle hypotheses.length, witness index]) =
        .complete state [optionValue (some (Data.preterm claim))] [] [] := by
  have path := dense_saved_hypothesis_returns state table definitions theorems context handle
    (hypotheses.map Data.preterm) index represented
  have returns : ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        VectorAccess.vectorValue handle hypotheses.length, witness index]) =
      .complete state [optionValue ((hypotheses[index]?).map Data.preterm)] [] [] := by
    simpa [evaluate, start, List.getElem?_map] using pure_returns_has_sufficient_fuel program [] state state _ _ path
  rw [← Kernel.ProofWitness.proof_eq_some_iff, Kernel.ProofWitness.proof?]
  constructor
  · intro accepted
    simpa [accepted] using returns
  · rintro ⟨fuel, accepted⟩
    obtain ⟨referenceFuel, completed⟩ := returns
    have unique := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] []
      completed accepted
    exact Data.optional_preterm_injective (List.singleton_inj.mp unique.2.1)

/-- A read of a saved conclusion is justified in the original scope only
when those saved facts were checked there. The driver must establish that
premise before publishing; storage and successful lookup cannot establish it. -/
theorem authorized_saved_hypothesis_is_sound (state : State)
    (table definitions theorems context : Atom) (handle : NamedSpaces.Handle)
    (signature : Kernel.TermSignature) (kernelDefinitions : Kernel.Definition.Signature)
    (kernelTheorems : Kernel.TheoremSignature) (kernelContext : Kernel.Context)
    (hypotheses saved : List Kernel.Preterm) (index : Nat) (claim : Kernel.Preterm)
    (represented : Store.Represents state handle
      (Store.enumerate ((hypotheses ++ saved).map Data.preterm)))
    (checked : ∀ fact ∈ saved,
      Kernel.Derives signature kernelDefinitions kernelTheorems kernelContext hypotheses fact)
    (accepted : ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        VectorAccess.vectorValue handle (hypotheses ++ saved).length, witness index]) =
      .complete state [optionValue (some (Data.preterm claim))] [] []) :
    Kernel.Derives signature kernelDefinitions kernelTheorems kernelContext hypotheses claim := by
  have witnessed := (checks_iff_saved_hypothesis_accepts state table definitions theorems context
    handle signature kernelDefinitions kernelTheorems kernelContext (hypotheses ++ saved) index claim
    represented).mpr accepted
  exact Kernel.ProofWitness.Checks.reuse_checked checked witnessed

theorem absent_hypothesis_returns_none (state : State) (table definitions theorems context : Atom)
    (hypotheses : List Atom) (index : Nat) (absent : hypotheses.length ≤ index) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:proof", table, definitions, theorems, context,
        listValue hypotheses, witness index]) = .complete state [.symbol "None"] [] [] := by
  simpa [List.getElem?_eq_none absent, optionValue] using
    proof_has_sufficient_fuel state table definitions theorems context hypotheses index

end Mettapedia.Languages.MM0.MeTTa.Hypothesis
