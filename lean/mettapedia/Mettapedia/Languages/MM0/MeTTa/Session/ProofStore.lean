import Mettapedia.Languages.MM0.MeTTa.Kernel.Proof
import Mettapedia.Languages.MM0.MeTTa.Data.VectorPublication

/-!
# Checked publication in the MM0 proof store

The private vector contains original hypotheses followed by conclusions of
chronologically checked initializers. Publication retains the actual witness
and preserves its original logical scope; it does not expand a proof tree.

The shared-entry driver's control flow is a separate source correspondence.
These contracts join its proof call, native publication and logical prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ProofStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open NamedSpaces (Handle)
open Kernel (Preterm ProofWitness Context)
open TableAccess (tableValue)
open Presentation.ComputationalTyping (signatureOf)

def extend (tables : Proof.Tables) (expression : Preterm) : Proof.Tables :=
  { tables with values := tables.values ++ [expression] }

/-- Publication also needs the proof vector to be distinct from the declaration
tables and an explicitly selected vector input. Proof checking also accepts
inline hypotheses, but native publication requires the vector layout. -/
structure Independent (tables : Proof.Tables) : Prop where
  terms : tables.terms ≠ tables.hypotheses
  definitions : tables.definitions ≠ tables.hypotheses
  theorems : tables.theorems ≠ tables.hypotheses
  vector : tables.storage = .vector

/-- Extending the checked logical prefix changes neither store ownership nor
the selected physical input layout. -/
theorem Independent.after_extend {tables : Proof.Tables} (independent : Independent tables)
    (expression : Preterm) : Independent (extend tables expression) :=
  ⟨independent.terms, independent.definitions, independent.theorems, independent.vector⟩

/-- Literal admission input cannot be used as the private publication vector. -/
theorem inline_not_independent (tables : Proof.Tables) (mode : tables.storage = .inline) :
    ¬ Independent tables := by
  intro independent
  have vector := independent.vector
  rw [mode] at vector
  cases vector

structure Authorized (tables : Proof.Tables) (context : Context)
    (original : List Preterm) (saved : List (Preterm × ProofWitness)) : Prop where
  values : tables.values = original ++ saved.map Prod.fst
  initializers : Kernel.SavedWitnessesChecked (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
    (Proof.theoremSignature tables.declarations) context original saved

theorem authorized_empty (tables : Proof.Tables) (context : Context) :
    Authorized tables context tables.values [] := ⟨by simp, .nil⟩

theorem Authorized.record {tables : Proof.Tables} {context : Context}
    {original : List Preterm} {saved : List (Preterm × ProofWitness)}
    (authorized : Authorized tables context original saved) {witness : ProofWitness} {expression : Preterm}
    (checked : ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values witness expression) :
    Authorized (extend tables expression) context original (saved ++ [(expression, witness)]) := by
  refine ⟨?_, ?_⟩
  · simp [extend, authorized.values, List.append_assoc]
  · apply Kernel.SavedWitnessesChecked.record authorized.initializers
    simpa only [← authorized.values] using (ProofWitness.check_iff _ _ _ _ _ _ _).mpr checked

theorem Authorized.root_sound {tables : Proof.Tables} {context : Context}
    {original : List Preterm} {saved : List (Preterm × ProofWitness)}
    (authorized : Authorized tables context original saved) {witness : ProofWitness} {claim : Preterm}
    (checked : ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values witness claim) :
    Kernel.Derives (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context original claim := by
  apply authorized.initializers.root_sound
  simpa only [← authorized.values] using (ProofWitness.check_iff _ _ _ _ _ _ _).mpr checked

theorem ready_after_publication {tables : Proof.Tables} {before after : State} {expression : Preterm}
    (ready : Proof.Ready tables before) (independent : Independent tables)
    (inserted : Effects.insert before tables.hypotheses
      (Store.row (tables.values.length, Data.preterm expression)) = some after) :
    Proof.Ready (extend tables expression) after := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change after.read tables.terms = _
    rw [Effects.insert_read_other inserted independent.terms]
    exact ready.terms
  · change after.read tables.definitions = _
    rw [Effects.insert_read_other inserted independent.definitions]
    exact ready.definitions
  · change after.read tables.theorems = _
    rw [Effects.insert_read_other inserted independent.theorems]
    exact ready.theorems
  · have published := VectorPublication.publication_preserves_dense_prefix
      (ready.vector_hypotheses independent.vector) (by simpa only [List.length_map] using inserted)
    change Hypothesis.Ready tables.storage tables.hypotheses _ after
    rw [independent.vector]
    apply Hypothesis.Ready.vector
    simpa only [extend, List.map_append, List.map_cons, List.map_nil] using published
  · change InferenceCache.Ready (signatureOf tables.entries) (tableValue tables.terms) tables.cache after
    unfold InferenceCache.Ready
    rw [Effects.insert_preserves_cells inserted]
    rw [Effects.insert_read_other inserted (Ne.symm tables.separateHypotheses)]
    exact ready.cache

/-- The actual native vector operation publishes one row, and changes no other
space or cell. Authorization is supplied by the preceding proof check. -/
theorem publication_returns (tables : Proof.Tables) (expression : Preterm) (before : State)
    (ready : Proof.Ready tables before) (independent : Independent tables) :
    ∃ after,
      (∀ bindings vectorName expressionName,
        applySubst bindings (.var vectorName) = Proof.hypothesesValue tables →
        applySubst bindings (.var expressionName) = Data.preterm expression →
        PureReturns program bindings before (.expression [.symbol "mm0:vector-snoc", .var vectorName, .var expressionName]) after
          (Proof.hypothesesValue (extend tables expression))) ∧
      Proof.Ready (extend tables expression) after ∧
      (∀ other, other ≠ tables.hypotheses → after.read other = before.read other) ∧ after.cells = before.cells := by
  obtain ⟨after, inserted⟩ := Effects.insert_exists_of_read_some (ready.vector_hypotheses independent.vector)
    (Store.row (tables.values.length, Data.preterm expression))
  refine ⟨after, ?_, ready_after_publication ready independent inserted,
    fun _ different => Effects.insert_read_other inserted different,
    Effects.insert_preserves_cells inserted⟩
  intro bindings vectorName expressionName capturedVector capturedExpression
  rw [Proof.hypothesesValue_vector tables independent.vector] at capturedVector
  have nextMode : (extend tables expression).storage = .vector := independent.vector
  rw [Proof.hypothesesValue_vector (extend tables expression) nextMode]
  simpa only [extend, List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using
    VectorPublication.publication_returns bindings before after tables.hypotheses tables.values.length (Data.preterm expression)
      vectorName expressionName inserted capturedVector capturedExpression

/-- Checking and publishing the submitted initializer retains a chronological
justification in the original scope. The runtime stores just its conclusion. -/
theorem check_and_publish (tables : Proof.Tables) (context : Context) (original : List Preterm)
    (saved : List (Preterm × ProofWitness)) (witness : ProofWitness) (expression : Preterm) (before : State)
    (ready : Proof.Ready tables before) (independent : Independent tables)
    (authorized : Authorized tables context original saved)
    (checked : ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values witness expression) :
    ∃ middle after,
      Proof.Call tables context witness before middle (some expression) ∧
      (∀ bindings vectorName expressionName,
        applySubst bindings (.var vectorName) = Proof.hypothesesValue tables →
        applySubst bindings (.var expressionName) = Data.preterm expression →
        PureReturns program bindings middle (.expression [.symbol "mm0:vector-snoc", .var vectorName, .var expressionName]) after
          (Proof.hypothesesValue (extend tables expression))) ∧
      Proof.Ready (extend tables expression) after ∧
      Authorized (extend tables expression) context original (saved ++ [(expression, witness)]) ∧
      (∀ other, other ≠ tables.cache → other ≠ tables.hypotheses → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨middle, _, proofReturned, readyMiddle, frame⟩ := Proof.returns tables context witness before ready
  obtain ⟨after, published, readyAfter, otherAfter, cellsAfter⟩ := publication_returns tables expression middle readyMiddle independent
  refine ⟨middle, after, ?_, published, readyAfter, authorized.record checked, ?_, cellsAfter.trans frame.cells⟩
  · simpa only [checked.eval] using proofReturned
  · intro other notCache notVector
    rw [otherAfter other notVector, frame.other other notCache]

/-- A proof store aliased with the term table cannot preserve that frozen
snapshot after publication. Separation is needed even when both are empty. -/
theorem aliased_publication_changes_terms {tables : Proof.Tables} {before after : State} {expression : Preterm}
    (ready : Proof.Ready tables before) (aliased : tables.terms = tables.hypotheses)
    (inserted : Effects.insert before tables.hypotheses
      (Store.row (tables.values.length, Data.preterm expression)) = some after) :
    after.read tables.terms ≠ some (TableAccess.declarationRows tables.entries) := by
  obtain ⟨rows, readBefore, readAfter⟩ := Effects.insert_reads_back inserted
  have sameBefore : rows = TableAccess.declarationRows tables.entries := by
    have termRead := ready.terms
    rw [aliased, readBefore] at termRead
    exact Option.some.inj termRead
  intro unchanged
  rw [aliased, readAfter] at unchanged
  have same := Option.some.inj unchanged
  have lengths := congrArg List.length same
  simp only [List.length_append, List.length_cons, List.length_nil, sameBefore] at lengths
  omega

end Mettapedia.Languages.MM0.MeTTa.ProofStore
