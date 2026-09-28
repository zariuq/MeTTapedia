import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Context-indexed rho communication

The closed COMM substitution replaces the received name, but has no binder
elimination for names in an enclosing context. This operation eliminates the
received binder: indices outside it move down, and an open payload moves under
each intervening input binder. Literal quotations remain opaque.

The result is a raw pattern. Admitting an open payload as a newly constructed
name requires a separate contextual-name representation; `NQuote` alone is a
literal and cannot supply that representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt)

/-- The name of a received payload uses rho's quote/drop name equation.
This only forms a name; it does not add a free operational Drop step. -/
def contextualNameOfPayload : Pattern → Pattern
  | .apply "PDrop" [name] => semanticNormalizeName name
  | payload => .apply "NQuote" [payload]

/-- Constructing a name from a payload agrees with the authored name
equation, including a payload which is itself a drop. -/
theorem contextualNameOfPayload_equiv (payload : Pattern) :
    NameEquiv (contextualNameOfPayload payload)
      (.apply "NQuote" [payload]) := by
  unfold contextualNameOfPayload
  split
  · rename_i name
    exact NameEquiv.trans _ _ _
      (semanticNormalizeName_sound name)
      (NameEquiv.symm _ _ (NameEquiv.quote_drop name))
  · exact NameEquiv.refl _

/-- A payload already closed to surrounding binders keeps an admitted name
when moved under more binders. The second premise is the precise nameability
condition, which matters for malformed raw patterns. -/
theorem contextualNameOfPayload_closed_lift_safe
    (payload : Pattern) (depth : Nat)
    (payloadSafe : binderSafeAt "NQuote" 0 payload = true)
    (nameSafe : binderSafeAt "NQuote" 0
      (contextualNameOfPayload payload) = true) :
    binderSafeAt "NQuote" depth
      (contextualNameOfPayload (liftBVars 0 depth payload)) = true := by
  have wellScoped :=
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedAt_of_binderSafeAt
      "NQuote" payloadSafe
  have unchanged :=
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
      (cutoff := 0) (shift := depth) wellScoped
  rw [unchanged]
  exact Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt_mono
    "NQuote" nameSafe (Nat.zero_le depth)

/-- A dropped ambient name is a dynamic payload whose name remains open and
scoped after insertion beneath any number of input binders. -/
theorem contextualNameOfOpenDrop_lift (index shift : Nat) :
    contextualNameOfPayload
        (liftBVars 0 shift (.apply "PDrop" [.bvar index])) =
      .bvar (index + shift) := by
  rfl

theorem contextualNameOfOpenDrop_lift_safe
    (ambient index shift : Nat) (inScope : index < ambient) :
    binderSafeAt "NQuote" (ambient + shift)
      (contextualNameOfPayload
        (liftBVars 0 shift (.apply "PDrop" [.bvar index]))) = true := by
  rw [contextualNameOfOpenDrop_lift]
  simp only [binderSafeAt, decide_eq_true_eq]
  omega

/-- Eliminate the received binder from a name. The Boolean records whether
the whole normalized name was the received name. -/
def contextualNameSubstMark (depth : Nat) (payload : Pattern)
    (name : Pattern) : Pattern × Bool :=
  let normalized := semanticNormalizeName name
  match normalized with
  | .bvar index =>
      if index < depth then (.bvar index, false)
      else if index = depth then
        (contextualNameOfPayload (liftBVars 0 depth payload), true)
      else (.bvar (index - 1), false)
  | other => (other, false)

/-- Name projection of contextual communication substitution. -/
def contextualNameSubst (depth : Nat) (payload name : Pattern) : Pattern :=
  (contextualNameSubstMark depth payload name).1

mutual
  /-- Context-indexed semantic COMM substitution. The `depth` nearest binders
are retained; the next binder is the one eliminated by communication. -/
  def contextualProcSubst (depth : Nat) (payload : Pattern) : Pattern → Pattern
    | .bvar index =>
        if index < depth then .bvar index
        else if index = depth then
          contextualNameOfPayload (liftBVars 0 depth payload)
        else .bvar (index - 1)
    | .fvar name => .fvar name
    | .apply "NQuote" [code] => .apply "NQuote" [code]
    | .apply "PDrop" [name] =>
        let (name', matched) := contextualNameSubstMark depth payload name
        if matched then liftBVars 0 depth payload
        else .apply "PDrop" [name']
    | .apply "POutput" [name, continuation] =>
        .apply "POutput"
          [contextualNameSubst depth payload name,
           contextualProcSubst depth payload continuation]
    | .apply "PInput" [name, .lambda none body] =>
        .apply "PInput"
          [contextualNameSubst depth payload name,
           .lambda none (contextualProcSubst (depth + 1) payload body)]
    | .lambda name body =>
        .lambda name (contextualProcSubst (depth + 1) payload body)
    | .multiLambda arity names body =>
        .multiLambda arity names (contextualProcSubst (depth + arity) payload body)
    | .subst body replacement =>
        .subst (contextualProcSubst (depth + 1) payload body)
          (contextualProcSubst depth payload replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (contextualProcSubstList depth payload elements) rest
    | other => other

  def contextualProcSubstList (depth : Nat) (payload : Pattern) :
      List Pattern → List Pattern
    | [] => []
    | head :: tail =>
        contextualProcSubst depth payload head ::
          contextualProcSubstList depth payload tail
end

/-- The payload is normalized once, as in strict-core COMM. -/
def contextualCommRepresentative (body payload : Pattern) : Pattern :=
  contextualProcSubst 0 (semanticNormalizeProc payload) body

/-- Under any number of inner binders, the received name is replaced as a
whole by the name of the appropriately lifted payload. -/
theorem contextualNameSubstMark_bound (depth : Nat) (payload : Pattern) :
    contextualNameSubstMark depth payload (.bvar depth) =
      (contextualNameOfPayload (liftBVars 0 depth payload), true) := by
  simp [contextualNameSubstMark, semanticNormalizeName]

/-- Names bound by an inner input are untouched by elimination of an outer
receive binder. -/
theorem contextualNameSubst_inner (depth index : Nat) (payload : Pattern)
    (inner : index < depth) :
    contextualNameSubst depth payload (.bvar index) = .bvar index := by
  simp [contextualNameSubst, contextualNameSubstMark,
    semanticNormalizeName, inner]

/-- A drop of the received name executes its payload, lifted beneath the
inner binders. This is distinct from firing an independent Drop rule. -/
theorem contextualProcSubst_bound_drop (depth : Nat) (payload : Pattern) :
    contextualProcSubst depth payload (.apply "PDrop" [.bvar depth]) =
      liftBVars 0 depth payload := by
  simp [contextualProcSubst, contextualNameSubstMark,
    semanticNormalizeName]

/-- An enclosing name moves down one index when the receive binder leaves
scope, while the inner binders remain untouched. -/
theorem contextualNameSubst_ambient (depth index : Nat) (payload : Pattern) :
    contextualNameSubst depth payload (.bvar (depth + 1 + index)) =
      .bvar (depth + index) := by
  simp [contextualNameSubst, contextualNameSubstMark,
    semanticNormalizeName, show ¬ depth + 1 + index < depth by omega,
    show depth + 1 + index ≠ depth by omega]

/-- The old closed operation leaves this enclosing name at index one. The
context-indexed operation removes the receive binder and reindexes it. -/
theorem ambient_name_reindexed (payload : Pattern) :
    contextualCommRepresentative
      (.apply "POutput" [.bvar 1, .apply "PZero" []]) payload =
        .apply "POutput" [.bvar 0, .apply "PZero" []] := by
  rfl

/-- The same reindexing works beneath a second input binder. -/
theorem ambient_name_reindexed_beneath_input (payload : Pattern) :
    contextualCommRepresentative
      (.apply "PInput"
        [.fvar "channel", .lambda none
          (.apply "POutput" [.bvar 2, .apply "PZero" []])]) payload =
        .apply "PInput"
          [.fvar "channel", .lambda none
            (.apply "POutput" [.bvar 1, .apply "PZero" []])] := by
  rfl

/-- A matched drop executes the received payload as part of COMM. -/
theorem bound_drop_contextual_comm (payload : Pattern) :
    contextualCommRepresentative (.apply "PDrop" [.bvar 0]) payload =
      semanticNormalizeProc payload := by
  simp [contextualCommRepresentative, contextualProcSubst,
    contextualNameSubstMark, semanticNormalizeName,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

/-- Other literal quoted names are unchanged by communication. -/
theorem literal_quote_contextual_comm (code payload : Pattern) :
    contextualCommRepresentative (.apply "NQuote" [code]) payload =
      .apply "NQuote" [code] := by
  rfl

/-- A free drop stays inert in strict-core COMM. -/
theorem free_drop_contextual_comm (name : String) (payload : Pattern) :
    contextualCommRepresentative (.apply "PDrop" [.fvar name]) payload =
      .apply "PDrop" [.fvar name] := by
  rfl

/-- An open ambient name sent as a dropped payload is still the ambient
name after receiving it. This needs the name equation and binder removal
together. -/
theorem received_open_name_reindexed :
    contextualCommRepresentative
        (.apply "POutput" [.bvar 0, .apply "PZero" []])
        (.apply "PDrop" [.bvar 0]) =
      .apply "POutput" [.bvar 0, .apply "PZero" []] := by
  rfl

/-- The same received name survives one more input binder, shifted under
that binder while retaining the outer ambient reference. -/
theorem received_open_name_beneath_input :
    contextualCommRepresentative
        (.apply "PInput"
          [.fvar "channel", .lambda none
            (.apply "POutput" [.bvar 1, .apply "PZero" []])])
        (.apply "PDrop" [.bvar 0]) =
      .apply "PInput"
        [.fvar "channel", .lambda none
          (.apply "POutput" [.bvar 1, .apply "PZero" []])] := by
  rfl

/-- The quote/drop name equation repairs this admitted open-name case:
both inputs and the contextual result are scoped, whereas closed COMM's
unresolved literal quote is not scoped at the result context. -/
theorem received_open_name_scope_comparison :
    let body : Pattern :=
      .apply "POutput" [.bvar 0, .apply "PZero" []]
    let payload : Pattern := .apply "PDrop" [.bvar 0]
    binderSafeAt "NQuote" 2 body = true ∧
      binderSafeAt "NQuote" 1 payload = true ∧
      binderSafeAt "NQuote" 1
        (contextualCommRepresentative body payload) = true ∧
      binderSafeAt "NQuote" 1
        (semanticCommSubst body payload) = false := by
  decide

/-- An arbitrary open process cannot be reclassified as a literal quote.
The general translation still needs a distinct contextual name constructor
or a source elaboration that closes the code before forming that name. -/
theorem open_payload_requires_contextual_name :
    let payload : Pattern :=
      .apply "POutput" [.bvar 0, .apply "PZero" []]
    binderSafeAt "NQuote" 1 payload = true ∧
      binderSafeAt "NQuote" 1 (contextualNameOfPayload payload) = false := by
  decide

/-- The contextual operation agrees with the existing COMM result on a
received drop, the closed principal example. -/
theorem bound_drop_agrees_with_closed_comm (payload : Pattern) :
    contextualCommRepresentative (.apply "PDrop" [.bvar 0]) payload =
      semanticCommSubst (.apply "PDrop" [.bvar 0]) payload := by
  rw [bound_drop_contextual_comm, semanticCommSubst_collapses_bound_drop]

/-- On the closed output-channel schema, contextual construction and the
existing COMM result agree modulo the authored name equation. The targets
may have different raw representatives when the payload is a drop. -/
theorem contextual_output_channel_agrees_with_closed_comm
    (payload : Pattern) :
    StructuralCongruence
      (contextualCommRepresentative
        (.apply "POutput" [.bvar 0, .apply "PZero" []]) payload)
      (semanticCommSubst
        (.apply "POutput" [.bvar 0, .apply "PZero" []]) payload) := by
  simp only [contextualCommRepresentative, contextualProcSubst,
    contextualNameSubst, contextualNameSubstMark,
    semanticCommSubst, semanticSubstProc, semanticSubstName,
    semanticSubstNameMark, semanticNormalizeName,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
  change StructuralCongruence
    (.apply "POutput"
      [contextualNameOfPayload (semanticNormalizeProc payload),
        .apply "PZero" []])
    (.apply "POutput"
      [.apply "NQuote" [semanticNormalizeProc payload],
        .apply "PZero" []])
  refine StructuralCongruence.apply_cong "POutput" _ _ rfl ?_
  intro index leftValid rightValid
  have small : index < 2 := by simpa using leftValid
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with atZero | atOne
  · subst index
    simpa using nameEquiv_implies_struct
      (contextualNameOfPayload_equiv (semanticNormalizeProc payload))
  · subst index
    simpa using StructuralCongruence.refl (.apply "PZero" [])

/-- Reindexing is necessary even when the payload itself is closed. -/
theorem closed_comm_misses_ambient_reindexing :
    contextualCommRepresentative
        (.apply "POutput" [.bvar 1, .apply "PZero" []])
        (.apply "PZero" []) ≠
      semanticCommSubst
        (.apply "POutput" [.bvar 1, .apply "PZero" []])
        (.apply "PZero" []) := by
  decide

#print axioms ambient_name_reindexed
#print axioms contextualNameOfPayload_equiv
#print axioms contextualNameOfPayload_closed_lift_safe
#print axioms contextualNameOfOpenDrop_lift_safe
#print axioms contextualProcSubst_bound_drop
#print axioms contextualNameSubst_inner
#print axioms contextualNameSubst_ambient
#print axioms bound_drop_agrees_with_closed_comm
#print axioms contextual_output_channel_agrees_with_closed_comm
#print axioms closed_comm_misses_ambient_reindexing
#print axioms received_open_name_beneath_input
#print axioms received_open_name_scope_comparison
#print axioms open_payload_requires_contextual_name

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
