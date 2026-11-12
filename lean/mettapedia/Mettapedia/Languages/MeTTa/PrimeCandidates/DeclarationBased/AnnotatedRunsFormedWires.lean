import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AnnotatedRunsFormedJoined

/-!
# The projection, certified for every wire

The result check of the projection is a run of the occurs-checked unifier on the compiled run's
final store. That store mentions the wire only through its quoted data, a closed transform term
that is not a variable. The unifier's eight steps do not inspect it (`projection_unifier`), so
the check accepts for every wire at fuel eight (`projection_checked_every_wire`), and the
certifying joined theorem holds for every wire (`projection_joined_every_wire`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
namespace Wires

open Mettapedia.Logic.LP
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation (Tm)
open Presentation.FormationSensitiveContextual (Context TypeOver Term TotalTerm QTerm empty)
open Presentation.StructuralConversionCode (Certificate Code)
open AnnotatedRuns
open Projection

/-! ## Quoted closed values -/

/-- A quoted value mentions only the context's variables. -/
theorem occursIn_quoteValue {Head : Type} (canonical : Presentation.DeclName → Bool) :
    ∀ {n : Nat} (t : Tm Head n) {p : Pattern}, quoteValue canonical t = some p →
      ∀ v, n ≤ v → p.occursIn v = false
  | _, .var index, p, quoted, v, outside => by
      simp only [quoteValue, Option.some.injEq] at quoted
      subst quoted
      have differ : v ≠ index.val := by omega
      simp [Term.occursIn, differ]
  | _, .const name, p, quoted, v, _ => by
      unfold quoteValue at quoted
      split at quoted
      · cases quoted
        rfl
      · cases quoted
  | _, .app function argument, p, quoted, v, outside => by
      cases hf : quoteValue canonical function with
      | none => simp [quoteValue, hf] at quoted
      | some f =>
          cases ha : quoteValue canonical argument with
          | none => simp [quoteValue, hf, ha] at quoted
          | some a =>
              simp only [quoteValue, hf, ha, Option.bind_some, Option.map_some,
                Option.some.injEq] at quoted
              subst quoted
              have first := occursIn_quoteValue canonical function hf v outside
              have second := occursIn_quoteValue canonical argument ha v outside
              simp only [ap, Term.occursIn, List.any_eq_false]
              intro x _
              split <;> simp [first, second]
  | _, .pair first second, p, quoted, v, outside => by
      cases hf : quoteValue canonical first with
      | none => simp [quoteValue, hf] at quoted
      | some f =>
          cases hs : quoteValue canonical second with
          | none => simp [quoteValue, hf, hs] at quoted
          | some s =>
              simp only [quoteValue, hf, hs, Option.bind_some, Option.map_some,
                Option.some.injEq] at quoted
              subst quoted
              have firstClosed := occursIn_quoteValue canonical first hf v outside
              have secondClosed := occursIn_quoteValue canonical second hs v outside
              simp only [pairP, Term.occursIn, List.any_eq_false]
              intro x _
              split <;> simp [firstClosed, secondClosed]
  | _, .head _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .pi _ _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .sigma _ _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .id _ _ _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .lam _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .fst _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .snd _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .refl _, p, quoted, _, _ => by simp [quoteValue] at quoted

theorem payload_occurs (wire : NativeWireData.Wire) (v : Nat) :
    (payloadPattern wire).occursIn v = false :=
  occursIn_quoteValue holCanonical _ (quote_payload wire) v (Nat.zero_le v)

/-- A closed quoted value is not a variable. -/
theorem payload_not_variable (wire : NativeWireData.Wire) (w : Nat) :
    payloadPattern wire ≠ .var w := by
  intro same
  have occurs := payload_occurs wire w
  rw [same] at occurs
  simp [Term.occursIn] at occurs

/-- The quoted HOL sequence singleton, written out. -/
def holExplicit : Pattern :=
  ap (ap (ap (.const NativeIndexedFamilies.Intrinsic.consName) (.const `HOLUniformList.sequence))
    (.const `HOLUniformList.nil))
    (ap (.const NativeIndexedFamilies.Intrinsic.nilName) (.const `HOLUniformList.sequence))

theorem holPattern_eq : holPattern = holExplicit := by
  decide +kernel

theorem holExplicit_occurs (v : Nat) : holExplicit.occursIn v = false := by
  rw [← holPattern_eq]
  exact occursIn_quoteValue holCanonical _ quote_hol v (Nat.zero_le v)

/-! ## The unifier on the projection's store -/

theorem ofFn_evaluate {α : Type} (f : Fin (signature.functionArity Symbol.evaluate) → α) :
    List.ofFn f = [f ⟨0, by decide⟩, f ⟨1, by decide⟩] := rfl

theorem ofFn_pair {α : Type} (f : Fin (signature.functionArity Symbol.pair) → α) :
    List.ofFn f = [f ⟨0, by decide⟩, f ⟨1, by decide⟩] := rfl

theorem ofFn_second {α : Type} (f : Fin (signature.functionArity Symbol.second) → α) :
    List.ofFn f = [f ⟨0, by decide⟩] := rfl

/-- **The unifier's eight steps on the projection's store do not inspect the payload.** For every
closed payload that is not a variable, the unifier answers, giving the result variable `0` and
the projected variable `2` the payload and `1` the HOL sequence. -/
theorem holExplicit_eq_app : holExplicit =
    .app .application fun i =>
      if i.val = 0 then
        ap (ap (.const NativeIndexedFamilies.Intrinsic.consName) (.const `HOLUniformList.sequence))
          (.const `HOLUniformList.nil)
      else ap (.const NativeIndexedFamilies.Intrinsic.nilName) (.const `HOLUniformList.sequence) :=
  rfl

/-- **The unifier's eight steps on the projection's store do not inspect the payload.** For every
closed payload that is not a variable, the unifier answers, giving the result variable `0` and
the projected variable `2` the payload and `1` the HOL sequence. -/
theorem projection_unifier_values (b : Pattern) (closed : ∀ v, b.occursIn v = false)
    (fixed : ∀ σ : Subst signature, σ.applyTerm b = b) (notVariable : ∀ w, b ≠ .var w) :
    (unifyFuel 8 [(evaluate (secondP (pairP (.var 1) (.var 2))) (.var 3),
        evaluate (secondP (pairP holExplicit b)) (.var 0)), (.var 3, .var 2)]).map
      (fun θ => (θ 0, θ 1, θ 2)) = some (b, holExplicit, b) := by
  have holFixed : ∀ σ : Subst signature, σ.applyTerm holExplicit = holExplicit := by
    intro σ
    rw [← holPattern_eq]
    exact hol_closed σ
  have holOccurs := holExplicit_occurs
  rw [holExplicit_eq_app] at holFixed holOccurs ⊢
  cases b with
  | var w => exact absurd rfl (notVariable w)
  | const c =>
      simp [unifyFuel, evaluate, secondP, pairP, finPairsToList, List.finRange, ofFn_evaluate,
        ofFn_pair, ofFn_second, Subst.applyEqs, Subst.applyTerm_var, holFixed, holOccurs, fixed,
        closed, Subst.comp, Subst.single]
  | app f ts =>
      simp [unifyFuel, evaluate, secondP, pairP, finPairsToList, List.finRange, ofFn_evaluate,
        ofFn_pair, ofFn_second, Subst.applyEqs, Subst.applyTerm_var, holFixed, holOccurs, fixed,
        closed, Subst.comp, Subst.single]

theorem projection_unifier (b : Pattern) (closed : ∀ v, b.occursIn v = false)
    (fixed : ∀ σ : Subst signature, σ.applyTerm b = b)
    (notVariable : ∀ w, b ≠ .var w) :
    ∃ θ, unifyFuel 8 [(evaluate (secondP (pairP (.var 1) (.var 2))) (.var 3),
        evaluate (secondP (pairP holPattern b)) (.var 0)), (.var 3, .var 2)] = some θ ∧
      θ 0 = b ∧ θ 1 = holPattern ∧ θ 2 = b := by
  have values := projection_unifier_values b closed fixed notVariable
  rw [← holPattern_eq] at values
  cases unified : unifyFuel 8 [(evaluate (secondP (pairP (.var 1) (.var 2))) (.var 3),
      evaluate (secondP (pairP holPattern b)) (.var 0)), (.var 3, .var 2)] with
  | none => rw [unified] at values; cases values
  | some θ =>
      rw [unified] at values
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at values
      exact ⟨θ, rfl, values.1, values.2.1, values.2.2⟩

/-- The projection's final store, for every wire. -/
theorem wire_store (wire : NativeWireData.Wire) :
    (follow (programLabel (program wire)) start [projectionFiring]).equations =
      [(evaluate (secondP (pairP (.var 1) (.var 2))) (.var 3),
        evaluate (secondP (pairP holPattern (payloadPattern wire))) (.var 0)), (.var 3, .var 2)] :=
  projection_store _ 1 2 3 0

/-- **The projection's result check, for every wire**, at fuel eight. -/
theorem projection_checked_every_wire (wire : NativeWireData.Wire) :
    checkResult holCanonical 8 (follow (programLabel (program wire)) start [projectionFiring]).equations
      0 (NativeWireData.encode (n := 0) wire) = true := by
  obtain ⟨θ, unified, result, _, _⟩ :=
    projection_unifier (payloadPattern wire) (payload_occurs wire) (payload_closed wire)
      (payload_not_variable wire)
  rw [wire_store]
  unfold checkResult
  rw [unified]
  simp [result, payload_readback, fixesContext]

/-- **The certifying joined theorem for the projection, for every wire**: the compiler reads the
source, the compiled run executes, the checker accepts at fuel eight, and the run's own
certificate converts the source to the wire's value. -/
theorem projection_joined_every_wire (wire : NativeWireData.Wire) :
    CertifiedConclusion holDecoder holDiscipline projectionProgram holRootAction (empty rules)
      (projectionSource wire) (programLabel (program wire)) 0 unitConfiguration
      [projectionStep 1 2 3 0] [] 8 0 (NativeWireData.encode wire) := by
  obtain ⟨θ, unified, _, first, second⟩ :=
    projection_unifier (payloadPattern wire) (payload_occurs wire) (payload_closed wire)
      (payload_not_variable wire)
  have hol : (denote projectionProgram.operations holPattern :
      Option (Tm Presentation.Tower.Head (empty rules).arity)) =
      some Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility.holSequenceSingleton :=
    denote_quoteValue _ holCanonical _ quote_hol
  have pay : (denote projectionProgram.operations (payloadPattern wire) :
      Option (Tm Presentation.Tower.Head (empty rules).arity)) = some (NativeWireData.encode wire) :=
    denote_quoteValue _ holCanonical _ (quote_payload wire)
  have executes : Executable action (programLabel (program wire)) start [projectionFiring] := by
    have compiled := (projection_square wire).2.1
    rw [projectionFiringAt_compiled] at compiled
    exact compiled
  refine formed_certified_execution holDiscipline projectionProgram holRootAction
    (compile_source wire) rfl ?_ ?_ ?_ dataTypeOver (valueTerm wire) rfl (Certificate.refl _)
  · rw [Consumers.projection_run]
    exact separated_alone executes
  · rw [Consumers.projection_run]
    exact projection_checked_every_wire wire
  · unfold runCertificate
    rw [Consumers.projection_run, wire_store, unified]
    simp [certify, stepCertificate, collect, bridge, projectionStep, projectionRule,
      CompiledRule.isOutput, CompiledRule.outputIndex, Subst.comp, varRenaming, projectionRename,
      first, second, hol, pay]

#print axioms occursIn_quoteValue
#print axioms payload_occurs
#print axioms payload_not_variable
#print axioms holPattern_eq
#print axioms projection_unifier_values
#print axioms projection_unifier
#print axioms projection_checked_every_wire
#print axioms projection_joined_every_wire

end Wires
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
