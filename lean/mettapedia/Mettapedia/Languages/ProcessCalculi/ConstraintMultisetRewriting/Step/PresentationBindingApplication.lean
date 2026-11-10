import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationBindingHeads
import Mettapedia.GSLT.LanguageDef.RuleBindingABT

/-! # Contextual source application through transform binding trees

The implementation uses the common scoped graft on transform terms. Its
argument spine retains both declared dependencies and the ambient tail.
Preservation and reflection include all source scope and arity refusals.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.GSLT.LanguageDef
open SignatureIndexedABT

def spine (ambient depth : Nat) (arguments : List Pattern) : List Payloads.Term :=
  arguments.map lowerPattern ++ (List.range ambient).map (fun index => .idx (depth + index))

theorem spine_transport (ambient depth : Nat) (arguments : List Pattern) :
    spine ambient depth arguments =
      (RuleBindingABT.spine ambient depth arguments).map (mapHeads encodeHead) := by
  simp only [spine, RuleBindingABT.spine, List.map_append, List.map_map, Function.comp_def,
    mapHeads]
  rfl

theorem spine_scoped (ambient depth : Nat) (arguments : List Pattern)
    (scopeOK : arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) = true) :
    ∀ term ∈ spine ambient depth arguments, Term.supportedAt (depth + ambient) term = true := by
  intro term member
  rcases List.mem_append.mp member with given | retained
  · obtain ⟨argument, argumentPresent, rfl⟩ := List.mem_map.mp given
    rw [lowerPattern_scope]
    exact List.all_eq_true.mp scopeOK argument argumentPresent
  · obtain ⟨index, inside, rfl⟩ := List.mem_map.mp retained
    have bound := List.mem_range.mp inside
    simp only [Term.supportedAt, decide_eq_true_eq]
    omega

theorem spine_length (ambient depth : Nat) (arguments : List Pattern) :
    (spine ambient depth arguments).length = arguments.length + ambient := by
  simp [spine]

/-- The common graft checks arity and body support once. The scoped argument
spine proves output support, so no second traversal of the result is needed. -/
def instantiateContextual? (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) : Option Payloads.Term := do
  if value.ambient != ambient then none else
  if !((arguments.map lowerPattern).all (fun argument => Term.supportedAt (depth + ambient) argument)) then
    none
  else
    ScopedApplication.graft (value.dependencies.length + ambient)
      (spine ambient depth arguments) (lowerPattern value.body)

theorem instantiateContextual_transport (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) :
    instantiateContextual? value ambient depth arguments =
      (RuleBindingABT.instantiateLowered? value ambient depth arguments).map (mapHeads encodeHead) := by
  unfold instantiateContextual? RuleBindingABT.instantiateLowered?
  simp only [lowerPattern_scope, PatternABTCarrier.lower_scope, List.all_map, Function.comp_def]
  by_cases sameAmbient : value.ambient = ambient
  · by_cases count : arguments.length = value.dependencies.length
    · by_cases bodyScoped : value.body.isWellScopedAt (value.dependencies.length + ambient) = true
      · by_cases argsScoped : arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) = true
        · simp only [sameAmbient, count, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, bodyScoped, argsScoped]
          rw [spine_transport, lowerPattern, graft_mapHeads]
          cases result : ScopedApplication.graft (value.dependencies.length + ambient)
              (RuleBindingABT.spine ambient depth arguments) (PatternABTCarrier.lower value.body) with
          | none => rfl
          | some term =>
              have encoded : ScopedApplication.graft (value.dependencies.length + ambient)
                  (spine ambient depth arguments) (lowerPattern value.body) = some (mapHeads encodeHead term) := by
                rw [spine_transport, lowerPattern, graft_mapHeads, result]
                rfl
              have outputScoped := ScopedApplication.graft_supported (spine_scoped ambient depth arguments argsScoped) encoded
              rw [mapHeads_scope] at outputScoped
              change some (mapHeads encodeHead term) =
                (if Term.supportedAt (depth + ambient) term then some term else none).map (mapHeads encodeHead)
              rw [if_pos outputScoped]
              rfl
        · simp [sameAmbient, count, bodyScoped, argsScoped]
      · simp [sameAmbient, count, bodyScoped, ScopedApplication.graft, spine_length, lowerPattern_scope]
    · simp [sameAmbient, count, ScopedApplication.graft, spine_length, lowerPattern_scope]
  · simp [sameAmbient]

theorem instantiateContextual_exact (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) :
    instantiateContextual? value ambient depth arguments =
      (instantiateValue? value ambient depth arguments).map lowerPattern := by
  rw [instantiateContextual_transport, RuleBindingABT.instantiateLowered_exact, Option.map_map]
  rfl

theorem source_success_iff (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Payloads.Term) :
    instantiateContextual? value ambient depth arguments = some result ↔
      ∃ source, instantiateValue? value ambient depth arguments = some source ∧
        lowerPattern source = result := by
  rw [instantiateContextual_exact, Option.map_eq_some_iff]

theorem source_refusal_iff (value : ContextualValue) (ambient depth : Nat) (arguments : List Pattern) :
    instantiateContextual? value ambient depth arguments = none ↔
      instantiateValue? value ambient depth arguments = none := by
  rw [instantiateContextual_exact, Option.map_eq_none_iff]

theorem result_scoped (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) {result : Payloads.Term}
    (applied : instantiateContextual? value ambient depth arguments = some result) :
    Term.supportedAt (depth + ambient) result = true := by
  obtain ⟨source, success, rfl⟩ := (source_success_iff value ambient depth arguments result).mp applied
  rw [lowerPattern_scope]
  exact instantiateValue?_scoped value ambient depth arguments source success

namespace Controls

def nested : ContextualValue := RuleBindingABT.Controls.nested

theorem nested_application : instantiateContextual? nested 1 1 [.bvar 0] =
    some (lowerPattern (.lambda (some "other") (.apply "pair" [.bvar 1, .bvar 2]))) := by
  rw [instantiateContextual_transport]
  change (RuleBindingABT.instantiateLowered? RuleBindingABT.Controls.nested 1 1 [.bvar 0]).map _ = _
  rw [RuleBindingABT.Controls.lowering_preserves_capture_avoidance]
  rfl

theorem wrong_ambient_refused : instantiateContextual? RuleBindingABT.Controls.value 0 1 [.bvar 0] = none := by
  rw [instantiateContextual_transport, RuleBindingABT.Controls.wrong_ambient_refused]
  rfl

theorem escaped_argument_refused : instantiateContextual? RuleBindingABT.Controls.value 1 1 [.bvar 2] = none := by
  rw [instantiateContextual_transport, RuleBindingABT.Controls.escaped_argument_refused]
  rfl

theorem missing_dependency_refused : instantiateContextual? RuleBindingABT.Controls.value 1 1 [] = none := by
  rw [instantiateContextual_transport, RuleBindingABT.Controls.missing_parameter_refused]
  rfl

end Controls

#print axioms instantiateContextual_exact
#print axioms source_success_iff
#print axioms result_scoped
#print axioms Controls.nested_application

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Binding
