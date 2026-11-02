import Mettapedia.GSLT.LanguageDef.PatternABTCarrier
import Mettapedia.OSLF.MeTTaIL.RuleBinding
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualMatcher

/-!
# Authored contextual interfaces lower to the common graft

An authored value has a declared dependency prefix and a separate ambient
context. The native parameter scope contains both. Occurrence arguments fill
the prefix; the ambient tail is explicitly weakened past the local binders.
This preserves the source operation, including all scope and arity refusals.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RuleBindingABT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open SignatureIndexedABT
open InferenceSupportIndexedABTLowering (PatternABTHead)
open PatternABTCarrier
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

/-- The authored dependency arguments followed by the retained ambient context. -/
def spine (ambient depth : Nat) (arguments : List Pattern) : List (Term PatternABTHead) :=
  arguments.map lower ++ (List.range ambient).map (fun i => Term.idx (depth + i))

theorem spine_length (ambient depth : Nat) (arguments : List Pattern) :
    (spine ambient depth arguments).length = arguments.length + ambient := by simp [spine]

theorem spine_assignment {dependencies ambient depth : Nat} {arguments : List Pattern}
    (count : arguments.length = dependencies) (index : Nat) (inside : index < dependencies + ambient) :
    SignatureIndexedABT.ScopedApplication.argumentAt (spine ambient depth arguments) index =
      lower (occurrenceAssignment dependencies depth arguments index) := by
  unfold SignatureIndexedABT.ScopedApplication.argumentAt spine occurrenceAssignment
  by_cases parameter : index < dependencies
  · have available : index < arguments.length := by omega
    rw [if_pos parameter, List.getElem?_append_left (by simpa using available)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem available]
  · have after : (arguments.map lower).length ≤ index := by simp; omega
    have available : index - arguments.length < ambient := by omega
    have inRange : index - dependencies < (List.range ambient).length := by simpa [count] using available
    rw [if_neg parameter, List.getElem?_append_right after]
    simp [List.getElem?_eq_getElem inRange, count, lower, lowerRaw,
      InferenceSupportIndexedABTLowering.PatternABT.encode, toTerm, Pattern.eraseBinderMetadata]

/-- The native simultaneous graft is the source occurrence substitution after lowering. -/
theorem graft_lower (value : ContextualValue) (ambient depth : Nat) (arguments : List Pattern)
    (count : arguments.length = value.dependencies.length)
    (bodyScoped : value.body.isWellScopedAt (value.dependencies.length + ambient) = true) :
    SignatureIndexedABT.ScopedApplication.graft (value.dependencies.length + ambient)
      (spine ambient depth arguments) (lower value.body) =
        some (lower (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
          (occurrenceAssignment value.dependencies.length depth arguments) value.body)) := by
  unfold SignatureIndexedABT.ScopedApplication.graft
  rw [spine_length, count, lower_scope]
  simp only [bodyScoped, and_self, ↓reduceIte]
  rw [lower_substitute]
  congr 1
  apply Term.substituteMany_congr_scoped _ (lower value.body) (by rwa [lower_scope])
  intro index inside
  exact spine_assignment count index inside

/-- The compiled operation uses native support checks and the common ABT graft. -/
def instantiateLowered? (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) : Option (Term PatternABTHead) := do
  if value.ambient != ambient then none else
  if arguments.length != value.dependencies.length then none else
  if !(Term.supportedAt (value.dependencies.length + ambient) (lower value.body)) then none else
  if !((arguments.map lower).all (fun argument => Term.supportedAt (depth + ambient) argument)) then none else
  let result ← SignatureIndexedABT.ScopedApplication.graft (value.dependencies.length + ambient)
    (spine ambient depth arguments) (lower value.body)
  if Term.supportedAt (depth + ambient) result then some result else none

/-- Exact preservation and reflection of successful results and every source refusal. -/
theorem instantiateLowered_exact (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) :
    instantiateLowered? value ambient depth arguments =
      (instantiateValue? value ambient depth arguments).map lower := by
  unfold instantiateLowered? instantiateValue?
  simp only [lower_scope, List.all_map, Function.comp_def]
  by_cases sameAmbient : value.ambient = ambient
  · by_cases count : arguments.length = value.dependencies.length
    · by_cases bodyScoped : value.body.isWellScopedAt (value.dependencies.length + ambient) = true
      · have grafted := graft_lower value ambient depth arguments count bodyScoped
        simp [sameAmbient, count, bodyScoped, grafted, lower_scope]
        split_ifs <;> rfl
      · simp [sameAmbient, count, bodyScoped]
    · simp [sameAmbient, count]
  · simp [sameAmbient]

/-- Obtain occurrence metadata from the existing rule binding specification and source path. -/
def lowerOccurrence? (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (name : String) (site : RulePatternSite) (path : List Nat) :
    Option (ContextualPatterns.Occurrence PatternABTHead String) := do
  let dependencies ← dependencies? spec name
  let arguments ← arguments? rule spec name site path
  let depth ← occurrenceDepthAtSite? rule site path
  if arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) then
    some ⟨name, dependencies.length + ambient, spine ambient depth arguments⟩
  else none

/-- Lowering retains the declared dependency arity and the complete ambient tail. -/
theorem lowerOccurrence_interface {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {name : String} {site : RulePatternSite} {path : List Nat}
    {occurrence : ContextualPatterns.Occurrence PatternABTHead String}
    (compiled : lowerOccurrence? rule spec ambient name site path = some occurrence) :
    ∃ dependencies arguments depth,
      dependencies? spec name = some dependencies ∧
      arguments? rule spec name site path = some arguments ∧
      occurrenceDepthAtSite? rule site path = some depth ∧
      arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) = true ∧
      occurrence = ⟨name, dependencies.length + ambient, spine ambient depth arguments⟩ := by
  unfold lowerOccurrence? at compiled
  cases hd : dependencies? spec name with
  | none => simp [hd] at compiled
  | some dependencies =>
    cases ha : arguments? rule spec name site path with
    | none => simp [hd, ha] at compiled
    | some arguments =>
      cases hx : occurrenceDepthAtSite? rule site path with
      | none => simp [hd, ha, hx] at compiled
      | some depth =>
        simp only [hd, ha, hx] at compiled
        change (if arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) = true then
          some (⟨name, dependencies.length + ambient, spine ambient depth arguments⟩ :
            ContextualPatterns.Occurrence PatternABTHead String) else none) = some occurrence at compiled
        by_cases valid : arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) = true
        · have same : (⟨name, dependencies.length + ambient, spine ambient depth arguments⟩ :
            ContextualPatterns.Occurrence PatternABTHead String) = occurrence := by
            rw [if_pos valid] at compiled
            exact Option.some.inj compiled
          exact ⟨dependencies, arguments, depth, rfl, rfl, rfl, valid, same.symm⟩
        · rw [if_neg valid] at compiled
          cases compiled

namespace Controls

def spec : RuleBindingSpec :=
  ⟨[("B", [.base "Expr"])], [⟨"B", .left, [0], [.bvar 0]⟩]⟩

def rule : RewriteRule :=
  { name := "inspect", typeContext := [("B", .base "Expr")], premises := [],
    left := .lambda (some "x") (.fvar "B"), right := .fvar "B", bindings := some spec }

theorem authored_occurrence_keeps_ambient_tail :
    lowerOccurrence? rule spec 1 "B" .left [0] =
      some ⟨"B", 2, [.idx 0, .idx 1]⟩ := by
  change some (⟨"B", 2, [lower (.bvar 0), .idx 1]⟩ :
    ContextualPatterns.Occurrence PatternABTHead String) = _
  simp [lower, lowerRaw, Pattern.eraseBinderMetadata,
    InferenceSupportIndexedABTLowering.PatternABT.encode, toTerm]

theorem invented_occurrence_refused : lowerOccurrence? rule spec 1 "missing" .left [0] = none := by decide

theorem wrong_source_path_refused : lowerOccurrence? rule spec 1 "B" .left [1] = none := by decide

def value : ContextualValue := ⟨[.base "Expr"], 1,
  .apply "pair" [.bvar 0, .bvar 1]⟩

theorem dependency_and_ambient_both_survive :
    instantiateLowered? value 1 1 [.bvar 0] =
      some (lower (.apply "pair" [.bvar 0, .bvar 1])) := by
  rw [instantiateLowered_exact]
  rfl

theorem wrong_ambient_refused : instantiateLowered? value 0 1 [.bvar 0] = none := by
  rw [instantiateLowered_exact]
  rfl

theorem escaped_argument_refused : instantiateLowered? value 1 1 [.bvar 2] = none := by
  rw [instantiateLowered_exact]
  rfl

theorem missing_parameter_refused : instantiateLowered? value 1 1 [] = none := by
  rw [instantiateLowered_exact]
  rfl

def nested : ContextualValue := ⟨[.base "Expr"], 1,
  .lambda (some "same") (.apply "pair" [.bvar 1, .bvar 2])⟩

theorem lowering_preserves_capture_avoidance :
    instantiateLowered? nested 1 1 [.bvar 0] =
      some (lower (.lambda (some "other") (.apply "pair" [.bvar 1, .bvar 2]))) := by
  rw [instantiateLowered_exact]
  simp [instantiateValue?, nested, occurrenceAssignment,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt, lower, Pattern.eraseBinderMetadata]

end Controls
end Mettapedia.GSLT.LanguageDef.RuleBindingABT
