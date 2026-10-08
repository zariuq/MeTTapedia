import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicSchema
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.NativeSyntax

/-!
# Annotation-preserving matching of open equation schemas

The matcher reconstructs an assignment from a written left side and a subject.
Repeated slots require equality of the whole written term, including lambda
domains. Assignment extension never replaces
a bound slot. Left sides do not enter binders; right sides may use the entire
scoped grammar and instantiate by capture-avoiding substitution.

Matching is separate from priority, declaration admission and normalization.
It does not identify a failed match with a permanently false equation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableWrittenSchemaMatching

variable {Head : Type}

abbrev Assignment (Head : Type) (slots ambient : Nat) :=
  Fin slots → Option (ATm Head ambient)

def Extends {slots ambient : Nat} (first second : Assignment Head slots ambient) : Prop :=
  ∀ index value, first index = some value → second index = some value

def Realizes {slots ambient : Nat} (assignment : Assignment Head slots ambient)
    (substitution : ATm.ASub Head slots ambient) : Prop :=
  ∀ index value, assignment index = some value → substitution index = value

theorem Extends.refl {slots ambient : Nat} (assignment : Assignment Head slots ambient) :
    Extends assignment assignment := fun _ _ bound => bound

theorem Extends.trans {slots ambient : Nat} {first middle last : Assignment Head slots ambient}
    (initial : Extends first middle) (final : Extends middle last) : Extends first last :=
  fun index value bound => final index value (initial index value bound)

theorem Realizes.of_extends {slots ambient : Nat}
    {first second : Assignment Head slots ambient} {substitution : ATm.ASub Head slots ambient}
    (realized : Realizes second substitution) (extended : Extends first second) :
    Realizes first substitution :=
  fun index value bound => realized index value (extended index value bound)

/-- Exact source equality is decided through the independently scoped raw
encoding; its injectivity supplies the proof, including written domains. -/
instance writtenDecidableEq [DecidableEq Head] {ambient : Nat} :
    DecidableEq (ATm Head ambient) := fun first second =>
  decidable_of_iff (NativeSyntax.encode first = NativeSyntax.encode second)
    ⟨fun same => NativeSyntax.encode_injective same, congrArg NativeSyntax.encode⟩

variable [DecidableEq Head]

def bindSlot {slots ambient : Nat} (assignment : Assignment Head slots ambient)
    (index : Fin slots) (value : ATm Head ambient) : Option (Assignment Head slots ambient) :=
  match assignment index with
  | none => some (Function.update assignment index (some value))
  | some prior => if value = prior then some assignment else none

theorem bindSlot_sound {slots ambient : Nat} {assignment updated : Assignment Head slots ambient}
    {index : Fin slots} {value : ATm Head ambient}
    (bound : bindSlot assignment index value = some updated) :
    Extends assignment updated ∧ updated index = some value := by
  cases prior : assignment index with
  | none =>
      simp only [bindSlot, prior] at bound
      cases bound
      refine ⟨?_, Function.update_self ..⟩
      intro other term old
      by_cases same : other = index
      · subst other
        rw [prior] at old
        cases old
      · rw [Function.update_of_ne same]
        exact old
  | some term =>
      simp only [bindSlot, prior] at bound
      split at bound
      · rename_i same
        cases bound
        exact ⟨Extends.refl _, same ▸ prior⟩
      · cases bound

theorem bindSlot_complete {slots ambient : Nat} {assignment : Assignment Head slots ambient}
    {substitution : ATm.ASub Head slots ambient} (realized : Realizes assignment substitution)
    (index : Fin slots) :
    ∃ updated, bindSlot assignment index (substitution index) = some updated ∧
      Realizes updated substitution := by
  cases prior : assignment index with
  | none =>
      refine ⟨Function.update assignment index (some (substitution index)), ?_, ?_⟩
      · simp only [bindSlot, prior]
      · intro other value bound
        by_cases same : other = index
        · subst other
          rw [Function.update_self] at bound
          exact Option.some.inj bound
        · rw [Function.update_of_ne same] at bound
          exact realized other value bound
  | some term =>
      have same := realized index term prior
      refine ⟨assignment, ?_, realized⟩
      simp only [bindSlot, prior]
      exact if_pos same

/-- The admitted left-side grammar. Binder formation is not pattern matching. -/
def supported {slots : Nat} : ATm Head slots → Bool
  | .var _ | .const _ | .head _ => true
  | .app function argument => supported function && supported argument
  | .refl subject => supported subject
  | _ => false

/-- Match in source order, retaining the same slot at every occurrence. -/
def run {slots ambient : Nat} : ATm Head slots → ATm Head ambient →
    Assignment Head slots ambient → Option (Assignment Head slots ambient)
  | .var index, subject, assignment => bindSlot assignment index subject
  | .const name, .const candidate, assignment =>
      if candidate = name then some assignment else none
  | .head head, .head candidate, assignment =>
      if candidate = head then some assignment else none
  | .app function argument, .app actualFunction actualArgument, assignment => do
      let updated ← run function actualFunction assignment
      run argument actualArgument updated
  | .refl subject, .refl actual, assignment => run subject actual assignment
  | _, _, _ => none

/-- A successful match preserves previous slots and reconstructs an exact
instance for every total assignment extending the returned one. -/
theorem run_sound {slots ambient : Nat} (pattern : ATm Head slots) :
    ∀ {subject : ATm Head ambient} {assignment updated : Assignment Head slots ambient},
      run pattern subject assignment = some updated →
      Extends assignment updated ∧
        ∀ substitution, Realizes updated substitution →
          ATm.subst substitution pattern = subject := by
  induction pattern with
  | var index =>
      intro subject assignment updated matched
      obtain ⟨extended, bound⟩ := bindSlot_sound matched
      exact ⟨extended, fun substitution realized => realized index subject bound⟩
  | const name =>
      intro subject assignment updated matched
      cases subject <;> simp only [run] at matched <;> try cases matched
      split at matched
      · rename_i same
        cases matched
        exact ⟨Extends.refl _, fun _ _ => by subst same; rfl⟩
      · cases matched
  | head head =>
      intro subject assignment updated matched
      cases subject <;> simp only [run] at matched <;> try cases matched
      split at matched
      · rename_i same
        cases matched
        exact ⟨Extends.refl _, fun _ _ => by subst same; rfl⟩
      · cases matched
  | app function argument functionIH argumentIH =>
      intro subject assignment updated matched
      cases subject <;> simp only [run] at matched <;> try cases matched
      rename_i actualFunction actualArgument
      cases first : run function actualFunction assignment with
      | none => simp only [first] at matched; cases matched
      | some middle =>
          simp only [first] at matched
          obtain ⟨initial, functionInstance⟩ := functionIH first
          obtain ⟨final, argumentInstance⟩ := argumentIH matched
          refine ⟨initial.trans final, fun substitution realized => ?_⟩
          exact congrArg₂ ATm.app
            (functionInstance substitution (realized.of_extends final))
            (argumentInstance substitution realized)
  | refl subject ih =>
      intro actual assignment updated matched
      cases actual <;> simp only [run] at matched <;> try cases matched
      obtain ⟨extended, instanceOf⟩ := ih matched
      exact ⟨extended, fun substitution realized => congrArg ATm.refl (instanceOf substitution realized)⟩
  | pi _ _ | sigma _ _ | id _ _ _ | lamBare _ | lamTyped _ _ | pair _ _ | fst _ | snd _ =>
      intro subject assignment updated matched
      cases subject <;> cases matched

/-- Every instance of a supported left side can be matched; repeated
occurrences keep their assigned values. No choice principle is used. -/
theorem run_complete {slots ambient : Nat} (pattern : ATm Head slots) :
    supported pattern = true →
    ∀ {assignment : Assignment Head slots ambient} (substitution : ATm.ASub Head slots ambient),
      Realizes assignment substitution →
      ∃ updated, run pattern (ATm.subst substitution pattern) assignment = some updated ∧
        Realizes updated substitution := by
  induction pattern with
  | var index =>
      intro _ assignment substitution realized
      exact bindSlot_complete realized index
  | const name | head name =>
      intro _ assignment substitution realized
      exact ⟨assignment, by simp only [ATm.subst, run, ite_true], realized⟩
  | app function argument functionIH argumentIH =>
      intro grammar assignment substitution realized
      have both : supported function = true ∧ supported argument = true := by
        simpa only [supported, Bool.and_eq_true] using grammar
      obtain ⟨functionGrammar, argumentGrammar⟩ := both
      obtain ⟨middle, first, realizedMiddle⟩ := functionIH functionGrammar substitution realized
      obtain ⟨updated, second, realizedUpdated⟩ := argumentIH argumentGrammar substitution realizedMiddle
      refine ⟨updated, ?_, realizedUpdated⟩
      simp only [ATm.subst, run, first]
      exact second
  | refl subject ih =>
      intro grammar assignment substitution realized
      exact ih grammar substitution realized
  | pi _ _ | sigma _ _ | id _ _ _ | lamBare _ | lamTyped _ _ | pair _ _ | fst _ | snd _ =>
      intro grammar
      cases grammar

def materialize {slots ambient : Nat} (assignment : Assignment Head slots ambient) :
    ATm.ASub Head slots ambient := fun index => (assignment index).getD (.const .anonymous)

omit [DecidableEq Head] in
theorem materialize_realizes {slots ambient : Nat} (assignment : Assignment Head slots ambient) :
    Realizes assignment (materialize assignment) := by
  intro index value bound
  simp only [materialize, bound, Option.getD_some]

/-- The total substitution reconstructed from a successful empty-store match. -/
def reconstruct {slots ambient : Nat} (pattern : ATm Head slots) (subject : ATm Head ambient) :
    Option (ATm.ASub Head slots ambient) := (run pattern subject (fun _ => none)).map materialize

theorem reconstruct_sound {slots ambient : Nat} {pattern : ATm Head slots}
    {subject : ATm Head ambient} {substitution : ATm.ASub Head slots ambient}
    (matched : reconstruct pattern subject = some substitution) :
    ATm.subst substitution pattern = subject := by
  unfold reconstruct at matched
  cases computed : run pattern subject (fun _ => none) with
  | none => simp only [computed, Option.map_none] at matched; cases matched
  | some updated =>
      simp only [computed, Option.map_some, Option.some.injEq] at matched
      subst substitution
      exact (run_sound pattern computed).2 _ (materialize_realizes updated)

/-- The executable matcher recognizes exactly the substitution instances of
the supported grammar. Unused slots need not agree with a proposed witness. -/
theorem reconstruct_exists_iff {slots ambient : Nat} {pattern : ATm Head slots}
    (grammar : supported pattern = true) (subject : ATm Head ambient) :
    (∃ substitution, reconstruct pattern subject = some substitution) ↔
      ∃ substitution : ATm.ASub Head slots ambient, ATm.subst substitution pattern = subject := by
  constructor
  · rintro ⟨substitution, matched⟩
    exact ⟨substitution, reconstruct_sound matched⟩
  · rintro ⟨substitution, rfl⟩
    obtain ⟨updated, matched, _⟩ := run_complete pattern grammar substitution
      (assignment := fun _ => none) (fun _ _ impossible => by cases impossible)
    exact ⟨materialize updated, by simp only [reconstruct, matched, Option.map_some]⟩

/-- All free source occurrences, including occurrences in written domains.
The tracked index moves past a binder; its bound index is not a schema slot. -/
def variableMultiplicity {ambient : Nat} (index : Fin ambient) : ATm Head ambient → Nat
  | .var candidate => if candidate = index then 1 else 0
  | .const _ | .head _ => 0
  | .pi domain body | .sigma domain body | .lamTyped domain body =>
      variableMultiplicity index domain + variableMultiplicity index.succ body
  | .lamBare body => variableMultiplicity index.succ body
  | .id carrier left right => variableMultiplicity index carrier +
      variableMultiplicity index left + variableMultiplicity index right
  | .app function argument | .pair function argument =>
      variableMultiplicity index function + variableMultiplicity index argument
  | .fst inner | .snd inner | .refl inner => variableMultiplicity index inner

/-- Every slot actually written on a matched left side has a retained value. -/
theorem run_assigned {slots ambient : Nat} (pattern : ATm Head slots) :
    ∀ {subject : ATm Head ambient} {assignment updated : Assignment Head slots ambient},
      run pattern subject assignment = some updated →
      ∀ index, 0 < variableMultiplicity index pattern →
        ∃ value, updated index = some value := by
  induction pattern with
  | var slot =>
      intro subject assignment updated matched index occurs
      by_cases same : slot = index
      · subst slot
        exact ⟨subject, (bindSlot_sound matched).2⟩
      · simp only [variableMultiplicity, if_neg same] at occurs
        exact (Nat.not_lt_zero 0 occurs).elim
  | const _ | head _ =>
      intro subject assignment updated matched index occurs
      simp only [variableMultiplicity] at occurs
      exact (Nat.not_lt_zero 0 occurs).elim
  | app function argument functionIH argumentIH =>
      intro subject assignment updated matched index occurs
      cases subject <;> simp only [run] at matched <;> try cases matched
      rename_i actualFunction actualArgument
      cases first : run function actualFunction assignment with
      | none => simp only [first] at matched; cases matched
      | some middle =>
          simp only [first] at matched
          simp only [variableMultiplicity] at occurs
          by_cases inFunction : 0 < variableMultiplicity index function
          · obtain ⟨value, bound⟩ := functionIH first index inFunction
            exact ⟨value, (run_sound argument matched).1 index value bound⟩
          · have absent : variableMultiplicity index function = 0 :=
              Nat.eq_zero_of_not_pos inFunction
            rw [absent, Nat.zero_add] at occurs
            exact argumentIH matched index occurs
  | refl subject ih =>
      intro actual assignment updated matched index occurs
      cases actual <;> simp only [run] at matched <;> try cases matched
      exact ih matched index occurs
  | pi _ _ | sigma _ _ | id _ _ _ | lamBare _ | lamTyped _ _ | pair _ _ | fst _ | snd _ =>
      intro subject assignment updated matched
      cases subject <;> cases matched

/-- Right-side slots must be supplied by the actual match. -/
def RightAssigned {slots ambient : Nat} (rhs : ATm Head slots)
    (assignment : Assignment Head slots ambient) : Prop :=
  ∀ index, 0 < variableMultiplicity index rhs → (assignment index).isSome = true

instance {slots ambient : Nat} (rhs : ATm Head slots)
    (assignment : Assignment Head slots ambient) : Decidable (RightAssigned rhs assignment) :=
  inferInstanceAs (Decidable (∀ index : Fin slots,
    0 < variableMultiplicity index rhs → (assignment index).isSome = true))

/-- The usual right-variable coverage law discharges right-side assignment
from successful matching; it is not additional execution input. -/
theorem rightAssigned_of_covered {slots ambient : Nat} {left right : ATm Head slots}
    {subject : ATm Head ambient} {assignment updated : Assignment Head slots ambient}
    (covered : ∀ index, 0 < variableMultiplicity index right →
      0 < variableMultiplicity index left)
    (matched : run left subject assignment = some updated) : RightAssigned right updated := by
  intro index occurs
  obtain ⟨value, bound⟩ := run_assigned left matched index (covered index occurs)
  simp only [bound, Option.isSome_some]

end TypedEquality.Normalization.ExecutableWrittenSchemaMatching
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
