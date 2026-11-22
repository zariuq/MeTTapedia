import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentProgramExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# Dependent schema applications in the cumulative tower

The schema opens a type `A`, a value `x : A`, and `g : Ground`, then constrains
`x : A` to equal `g : Ground`. Its take/read/make multiplicities are arbitrary.
The comparison uses actual tower judgments and actual dependent-step states.
Solutions remain symbolic; a model context containing `g` is not a closed
inhabitant of Ground.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.Controls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTwins DependentFull
open DependentFull.Controls (setting smallUniverse groundType ground_typed ground point)

abbrev levels : LevelModel Tower.rules Nat := setting.levels

abbrev typeContext (Γ : Context Tower.rules) := extend Γ (smallUniverse Γ)

def valueType (Γ : Context Tower.rules) : TypeOver (typeContext Γ) :=
  ⟨.var 0, .sort Tower.zero, .sort _, Derivable.var 0⟩

abbrev valueContext (Γ : Context Tower.rules) := extend (typeContext Γ) (valueType Γ)
abbrev outputContext (Γ : Context Tower.rules) := extend (valueContext Γ) (groundType _)

def helpers (Γ : Context Tower.rules) : Helpers Γ :=
  .cons (smallUniverse Γ) (.cons (valueType Γ) (.cons (groundType _) (.nil _)))

def valueRow (Γ : Context Tower.rules) : TotalTerm (outputContext Γ) :=
  TotalTerm.reindex
    (⟨(valueType Γ).reindex (projectionHom (typeContext Γ) (valueType Γ)),
      newest (typeContext Γ) (valueType Γ)⟩ : TotalTerm (valueContext Γ))
    (projectionHom (valueContext Γ) (groundType _))

def groundRow (Γ : Context Tower.rules) : TotalTerm (outputContext Γ) :=
  ⟨(groundType (valueContext Γ)).reindex (projectionHom _ (groundType _)),
    newest (valueContext Γ) (groundType _)⟩

def pointValue : TotalTerm point := ⟨groundType point, ⟨.var 0, Derivable.var 0⟩⟩

def schema (Γ : Context Tower.rules) (takes reads makes : Nat) : Schema levels Nat Γ where
  helpers := helpers Γ
  takes := List.replicate takes (valueRow Γ)
  reads := List.replicate reads (valueRow Γ)
  makes := List.replicate makes (Make.ofRow (valueRow Γ))
  tells := [(valueRow Γ, groundRow Γ)]
  guards := []
  queries := []

def typeArgument {Γ : Context Tower.rules} (baseMap : point ⟶ Γ) :
    Term point ((smallUniverse Γ).reindex baseMap) := ⟨ground, ground_typed _⟩

def valueArgument {Γ : Context Tower.rules} (baseMap : point ⟶ Γ) :
    Term point ((valueType Γ).reindex (pair baseMap (typeArgument baseMap))) :=
  ⟨.var 0, Derivable.var 0⟩

def arguments {Γ : Context Tower.rules} (baseMap : point ⟶ Γ) :
    (helpers Γ).Arguments baseMap :=
  ⟨typeArgument baseMap, valueArgument baseMap, ⟨.var 0, Derivable.var 0⟩, PUnit.unit⟩

def model {Γ : Context Tower.rules} (baseMap : point ⟶ Γ) : point ⟶ outputContext Γ :=
  (helpers Γ).instantiate baseMap (arguments baseMap)

theorem value_in_model {Γ : Context Tower.rules} (baseMap : point ⟶ Γ) :
    (valueRow Γ).reindex (model baseMap) = pointValue :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem ground_in_model {Γ : Context Tower.rules} (baseMap : point ⟶ Γ) :
    (groundRow Γ).reindex (model baseMap) = pointValue :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- All present resources have the stated value in this actual solution. -/
structure Represents (state : State Tower.rules Nat) (baseMap : point ⟶ state.frame) : Prop where
  knowledge : (frames levels).Models baseMap state.knowledge
  rows : ∀ occurrence ∈ state.present, (state.label occurrence).reindex baseMap = pointValue

theorem matches_replicated {state : State Tower.rules Nat} (baseMap : point ⟶ state.frame)
    (represented : Represents state baseMap) (takes reads makes count : Nat)
    (selected : List Nat) (present : ∀ occurrence ∈ selected, occurrence ∈ state.present) :
    (schema state.frame takes reads makes).MatchesAt baseMap (arguments baseMap)
      (List.replicate count (valueRow state.frame)) selected := by
  intro pattern occurrence member
  have pairMembers := List.of_mem_zip member
  have patternEq : pattern = valueRow state.frame := List.eq_of_mem_replicate pairMembers.1
  subst pattern
  change (frames levels).E
    ((valueRow state.frame).reindex (model baseMap)) ((state.label occurrence).reindex baseMap)
  rw [value_in_model, represented.rows occurrence (present occurrence pairMembers.2)]
  exact ((frames levels).equivalence point).refl _

theorem models_arguments {state : State Tower.rules Nat} (baseMap : point ⟶ state.frame)
    (represented : Represents state baseMap) (takes reads makes : Nat)
    (pick : Pick (schema state.frame takes reads makes))
    (taken : ∀ occurrence ∈ pick.1.taken, occurrence ∈ state.present)
    (read : ∀ occurrence ∈ pick.1.read, occurrence ∈ state.present) :
    (schema state.frame takes reads makes).ModelsAt pick baseMap (arguments baseMap) := by
  refine ⟨represented.knowledge,
    matches_replicated baseMap represented takes reads makes takes pick.1.taken taken,
    matches_replicated baseMap represented takes reads makes reads pick.1.read read, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change (frames levels).E
    ((valueRow state.frame).reindex (model baseMap))
    ((groundRow state.frame).reindex (model baseMap))
  rw [value_in_model, ground_in_model]
  exact ((frames levels).equivalence point).refl _

/-- A nontrivial family of source applications, for arbitrary numbers of
consumed, borrowed and produced occurrences. -/
theorem admitted {state : State Tower.rules Nat} (baseMap : point ⟶ state.frame)
    (represented : Represents state baseMap) (takes reads makes : Nat)
    (pick : Pick (schema state.frame takes reads makes))
    (distinctTaken : pick.1.taken.Nodup) (distinctMade : pick.1.fresh.Nodup)
    (takeCount : takes = pick.1.taken.length) (readCount : reads = pick.1.read.length)
    (available : (schema state.frame takes reads makes).Present pick) :
    (schema state.frame takes reads makes).Admits pick := by
  refine ⟨⟨distinctTaken, distinctMade, ?_, ?_, ?_⟩, available,
    ⟨point, baseMap, arguments baseMap,
      models_arguments baseMap represented takes reads makes pick available.1 available.2.1⟩, ?_⟩
  · change (List.replicate takes (valueRow state.frame)).length = pick.1.taken.length
    rw [List.length_replicate]
    exact takeCount
  · change (List.replicate reads (valueRow state.frame)).length = pick.1.read.length
    rw [List.length_replicate]
    exact readCount
  · intro made member
    have same := List.eq_of_mem_replicate member
    subst made
    exact Make.ofRow_wellTyped _
  · intro Δ substitution args _
    exact ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩

theorem represented_after {state : State Tower.rules Nat} (baseMap : point ⟶ state.frame)
    (represented : Represents state baseMap) (takes reads makes : Nat)
    (pick : Pick (schema state.frame takes reads makes))
    (accepted : (schema state.frame takes reads makes).Admits pick) :
    Represents ((schema state.frame takes reads makes).publish pick accepted.1) (model baseMap) := by
  let template := schema state.frame takes reads makes
  let firing := template.compile pick
  have nativeAccepted : firing.Admits := (template.compile_admits_iff pick).mpr accepted
  refine ⟨?_, ?_⟩
  · change (frames levels).Models
      (template.helpers.instantiate baseMap (arguments baseMap)) (template.information pick)
    rw [← template.compile_information pick]
    exact (template.compile_information_iff pick baseMap (arguments baseMap)).mpr
      (models_arguments baseMap represented takes reads makes pick
        accepted.2.1.1 accepted.2.1.2.1)
  · intro occurrence present
    by_cases fresh : occurrence ∈ pick.1.fresh
    · have made : occurrence ∈ firing.made := by rwa [template.compile_made pick]
      obtain ⟨⟨identity, output⟩, member, _, row⟩ := firing.label_after_of_mem nativeAccepted made
      have outputEq : output = Make.ofRow (valueRow state.frame) :=
        List.eq_of_mem_replicate (List.of_mem_zip member).2
      subst output
      change (template.publish pick accepted.1).label occurrence = valueRow state.frame at row
      rw [row]
      exact value_in_model baseMap
    · have notMade : occurrence ∉ firing.made := by rwa [template.compile_made pick]
      have row := firing.label_after_of_not_mem nativeAccepted notMade
      change (template.publish pick accepted.1).label occurrence =
        (state.label occurrence).reindex (helpers state.frame).weaken at row
      rw [row]
      change ((state.label occurrence).reindex (helpers state.frame).weaken).reindex
        ((helpers state.frame).instantiate baseMap (arguments baseMap)) = pointValue
      rw [(helpers state.frame).instantiate_old_value]
      apply represented.rows occurrence
      change occurrence ∈ (state.present \ pick.1.taken.toFinset) ∪ pick.1.fresh.toFinset at present
      rcases Finset.mem_union.mp present with old | new
      · exact (Finset.mem_sdiff.mp old).1
      · exact False.elim (fresh (List.mem_toFinset.mp new))

def start : State Tower.rules Nat := ⟨point, [], {0}, fun _ => pointValue⟩

theorem start_represents : Represents start (𝟙 point) := by
  refine ⟨Frames.models_nil _, ?_⟩
  intro occurrence _
  exact ContextualDependentEta.reindex_id _

def table : Program levels Nat := fun Γ =>
  [schema Γ 0 1 1, schema Γ 0 1 1, schema Γ 1 1 1]

def first : Candidate table start where
  ruleIndex := ⟨0, by decide⟩
  pick := ⟨⟨[], [0], [7]⟩, rfl⟩

theorem first_admitted : first.schema.Admits first.pick := by
  apply admitted (𝟙 point) start_represents 0 1 1
  · exact List.nodup_nil
  · exact List.nodup_singleton _
  · rfl
  · rfl
  · simp [Schema.Present, first, start]

def middle : State Tower.rules Nat := first.schema.publish first.pick first_admitted.1

theorem middle_represents : Represents middle (model (𝟙 point)) :=
  represented_after (state := start) (𝟙 point) start_represents 0 1 1 first.pick first_admitted

theorem middle_present : middle.present = {0, 7} := by
  change ({0} \ ([] : List Nat).toFinset) ∪ ([7] : List Nat).toFinset = _
  decide

def second : Candidate table middle where
  ruleIndex := ⟨2, by decide⟩
  pick := ⟨⟨[7], [0], [8]⟩, rfl⟩

theorem second_admitted : second.schema.Admits second.pick := by
  apply admitted (state := middle) (model (𝟙 point)) middle_represents 1 1 1
  · exact List.nodup_singleton _
  · exact List.nodup_singleton _
  · rfl
  · rfl
  · change (∀ occurrence ∈ ([7] : List Nat), occurrence ∈ middle.present) ∧
      (∀ occurrence ∈ ([0] : List Nat), occurrence ∈ middle.present) ∧
      (∀ occurrence ∈ ([7] : List Nat), occurrence ∉ ([0] : List Nat)) ∧
      ∀ occurrence ∈ ([8] : List Nat), occurrence ∉ middle.present
    rw [middle_present]
    decide

def allow : {state : State Tower.rules Nat} → Candidate table state → Prop := fun _ => True

def twoSteps : table.Execution allow start :=
  .cons first first_admitted True.intro
    (.cons second second_admitted True.intro
      (.nil (second.schema.publish second.pick second_admitted.1)))

theorem two_steps_keep_and_replace_resources : twoSteps.last.present = {0, 8} := by decide

theorem two_steps_retain_rule_indices :
    twoSteps.toRun.word.map (fun event => event.2.ruleIndex.val) = [0, 2] := by
  rw [Program.Execution.toRun_word]
  rfl

def alternative : Candidate table start where
  ruleIndex := ⟨1, by decide⟩
  pick := ⟨⟨[], [0], [7]⟩, rfl⟩

theorem raw_effects_agree : first.compile = alternative.compile := rfl

theorem candidate_origins_are_distinct : first ≠ alternative := by
  intro same
  have impossible := congrArg (fun candidate => candidate.ruleIndex.val) same
  change (0 : Nat) = 1 at impossible
  cases impossible

theorem denied_permission_refuses :
    ¬ (table.toStep (fun _ => False)).Admits first := by
  intro accepted
  exact ((table.admits_iff (fun _ => False) first).mp accepted).2

theorem output_arity_is_checked :
    validateChoice (schema point 0 1 1) (⟨[], [0], []⟩ : Choice Nat) = none := rfl

def reusedOutput : Candidate table middle where
  ruleIndex := ⟨0, by decide⟩
  pick := ⟨⟨[], [0], [7]⟩, rfl⟩

theorem existing_output_identity_refuses : ¬ reusedOutput.schema.Admits reusedOutput.pick := by
  intro accepted
  have absent := accepted.2.1.2.2.2 7 (List.mem_singleton_self _)
  exact absent (by decide)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.Controls
