import Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntaxLaws
import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternMeaningLaws
import Mettapedia.Languages.MeTTa.PeTTa.Unifying

/-!
# The checked selector graph and protected return of a generic fact

The whole emitted equation fixes both the selector and its quoted echo. The
selector's native constructor graph is exactly instantiation of the source
head. The actual source machine returns that same value from the echo under
the selected bindings, without activating constructor names in the result.

Realizing computed-let selection, fresh clause activation and answer ordering
are separate obligations. The passive-pattern machine is not silently given
a different binding rule by this module.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open GeneratedPeTTaDataPattern (ConstructorGraph)

/-- Lexically different scalar spellings may read to the same typed head.
Two reader failures are never evidence of equal source meaning. -/
def readbacksAgree (source rendered : SExpr) : Bool :=
  match SpaceSemantics.readRawExpression source, SpaceSemantics.readRawExpression rendered with
  | .ok first, .ok second => decide (first = second)
  | _, _ => false

/-- Check the complete native equation and read its proposed echo back
against the independently supplied source head. -/
def checkSource (source emitted : SExpr) : Bool :=
  match bodyParts? emitted with
  | some (_, echo) => check echo emitted && readbacksAgree source echo
  | none => false

theorem readbacksAgree_iff (source rendered : SExpr) :
    readbacksAgree source rendered = true ↔
      ∃ atom, SpaceSemantics.readRawExpression source = .ok atom ∧
        SpaceSemantics.readRawExpression rendered = .ok atom := by
  unfold readbacksAgree
  cases firstRead : SpaceSemantics.readRawExpression source <;>
    cases secondRead : SpaceSemantics.readRawExpression rendered <;> simp [eq_comm]

theorem checked_body_parts {head emitted : SExpr} (checked : check head emitted = true) :
    bodyParts? emitted = some (GeneratedPeTTaDataPattern.encode head, head) := by
  obtain ⟨relation, arguments, slot, rfl, _, rfl⟩ := checked_equation checked
  rfl

theorem checked_parts_exact {head emitted selector echo : SExpr}
    (checked : check head emitted = true) (parts : bodyParts? emitted = some (selector, echo)) :
    selector = GeneratedPeTTaDataPattern.encode head ∧ echo = head := by
  have same := Option.some.inj (parts.symm.trans (checked_body_parts checked))
  exact Prod.mk.inj same

theorem checkSource_iff (source emitted : SExpr) :
    checkSource source emitted = true ↔
      ∃ head, check head emitted = true ∧
        ∃ atom, SpaceSemantics.readRawExpression source = .ok atom ∧
          SpaceSemantics.readRawExpression head = .ok atom := by
  constructor
  · intro checked
    unfold checkSource at checked
    cases parts : bodyParts? emitted with
    | none => simp [parts] at checked
    | some pair =>
        obtain ⟨selector, echo⟩ := pair
        simp only [parts, Bool.and_eq_true] at checked
        exact ⟨echo, checked.1, (readbacksAgree_iff source echo).1 checked.2⟩
  · rintro ⟨head, checked, atom, sourceRead, headRead⟩
    unfold checkSource
    rw [checked_body_parts checked]
    exact Bool.and_eq_true_iff.mpr ⟨checked, (readbacksAgree_iff source head).2 ⟨atom, sourceRead, headRead⟩⟩

/-- This is the actual selector extracted from the checked equation, not a
replacement pattern supplied by the proof. -/
theorem checked_selector_graph_iff {head emitted selector echo : SExpr}
    (checked : check head emitted = true) (parts : bodyParts? emitted = some (selector, echo))
    (bindings : Subst) (before after : State) (value : Atom) :
    ConstructorGraph bindings before selector after value ↔
      ∃ atom, SpaceSemantics.readRawExpression head = .ok atom ∧
        after = before ∧ value = applySubst bindings atom := by
  rw [(checked_parts_exact checked parts).1]
  exact GeneratedPeTTaDataPattern.graph_encode_iff bindings before after head value

theorem checked_source_selector_graph {source emitted selector echo : SExpr}
    (checked : checkSource source emitted = true) (parts : bodyParts? emitted = some (selector, echo)) :
    ∃ atom, SpaceSemantics.readRawExpression source = .ok atom ∧
      ∀ (bindings : Subst) (before after : State) (value : Atom),
        ConstructorGraph bindings before selector after value ↔
          after = before ∧ value = applySubst bindings atom := by
  obtain ⟨head, syntaxChecked, atom, sourceRead, headRead⟩ := (checkSource_iff source emitted).1 checked
  refine ⟨atom, sourceRead, ?_⟩
  intro bindings before after value
  rw [checked_selector_graph_iff syntaxChecked parts]
  simp only [headRead, Except.ok.injEq]
  constructor
  · rintro ⟨other, rfl, pureWorld, instantiated⟩
    exact ⟨pureWorld, instantiated⟩
  · intro result
    exact ⟨atom, rfl, result⟩

/-- Once the selector graph holds, the protected echo returns its selected
value in the existing source machine, over arbitrary saved caller frames.
The equation's computed-let selector is still a separate realization step. -/
theorem checked_echo_step {head emitted selector echo : SExpr} {atom value : Atom}
    (checked : check head emitted = true) (parts : bodyParts? emitted = some (selector, echo))
    (read : SpaceSemantics.readRawExpression head = .ok atom)
    (bindings : Subst) (before after : State)
    (graph : ConstructorGraph bindings before selector after value)
    (registry : SpaceSemantics.Program) (base : Unifying.Configuration) :
    SpaceSemantics.readRawExpression (.list [.atom "quote", echo]) =
        .ok (.expression [.symbol "quote", atom]) ∧
      Unifying.step registry
        {base with state := after, control := .evaluate bindings (.expression [.symbol "quote", atom])} =
        some {base with state := before, control := .returned [⟨value, bindings⟩]} := by
  obtain ⟨decoded, decodedRead, pureWorld, instantiated⟩ :=
    (checked_selector_graph_iff checked parts bindings before after value).1 graph
  have same : decoded = atom := Except.ok.inj (decodedRead.symm.trans read)
  subst decoded
  subst after
  subst value
  constructor
  · rw [(checked_parts_exact checked parts).2]
    have quoteRead : SpaceSemantics.readToken "quote" = .ok (.symbol "quote") := by decide +kernel
    simp [SpaceSemantics.readRawExpression, SpaceSemantics.readRawExpressions,
      quoteRead, read, bind, Except.bind, pure, Except.pure]
  · rfl

#print axioms checked_parts_exact
#print axioms checkSource_iff
#print axioms checked_selector_graph_iff
#print axioms checked_source_selector_graph
#print axioms checked_echo_step

end Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax
