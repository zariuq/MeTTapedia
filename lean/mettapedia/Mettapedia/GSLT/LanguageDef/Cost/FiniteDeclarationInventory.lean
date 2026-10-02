import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticTypingCore

/-!
# Exact declaration inventory for finite Cost profiles

The source cut computes the nonprincipal declaration inventory. Additional
continuation slots retain their authored positions; they do not create a
second constructor authority. The intrinsic Cost constructor and role types
are the existing ones. Materialization uses the finite profile's actual
parameter retyping, including every additional continuation position.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism

/-- Duplicate-freedom follows from source declaration validation, without
requiring a two-slot residual-coverage plan. -/
theorem continuationConstructors_nodup {theory : IGSLT}
    (cut : InteractionCutPresentation theory) : (continuationConstructors cut).Nodup := by
  unfold continuationConstructors
  apply List.Nodup.filter
  apply List.nodup_attach.mpr
  exact List.Nodup.of_map (fun constructor => constructor.label)
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      theory.presentation.presentation.language theory.presentation.presentation.valid)

namespace ContinuationDecorationProfile
variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Construct a finite profile with the exact authored nonprincipal
inventory. The slot arguments already carry their declaration, parameter
position, binder representation, and schema-occurrence evidence. -/
def withNonprincipalInventory
    (programAdditional : List (ContinuationDecorationSlot cut.program))
    (environmentAdditional : List (ContinuationDecorationSlot cut.environment)) :
    ContinuationDecorationProfile cut where
  programAdditional := programAdditional
  environmentAdditional := environmentAdditional
  constructorClosure := continuationConstructors cut

theorem withNonprincipalInventory_mem
    (programAdditional : List (ContinuationDecorationSlot cut.program))
    (environmentAdditional : List (ContinuationDecorationSlot cut.environment))
    (constructor : DeclaredConstructor theory.presentation.presentation) :
    constructor ∈ (withNonprincipalInventory programAdditional environmentAdditional).constructorClosure ↔
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor :=
  ContinuationRetypingPlan.mem_continuationConstructors_iff cut constructor

theorem withNonprincipalInventory_nodup
    (programAdditional : List (ContinuationDecorationSlot cut.program))
    (environmentAdditional : List (ContinuationDecorationSlot cut.environment)) :
    (withNonprincipalInventory programAdditional environmentAdditional).constructorClosure.Nodup :=
  continuationConstructors_nodup cut

/-- The old declaration-only profile is the zero-additional-slot case. -/
theorem ofRetypingPlan_eq_withNonprincipalInventory (plan : ContinuationRetypingPlan cut) :
    ofRetypingPlan plan = withNonprincipalInventory [] [] := rfl

/-- Select the actually present wrapped summand of the existing intrinsic
Cost namespace. Base and apparatus declarations are retained in full. -/
def IsDeclaredCostConstructor (profile : ContinuationDecorationProfile cut) :
    CostConstructor (DeclaredConstructor theory.presentation.presentation) → Prop
  | .base _ => True
  | .wrapped constructor => constructor ∈ profile.constructorClosure
  | .apparatus _ => True

abbrev DeclaredCostConstructor (profile : ContinuationDecorationProfile cut) :=
  { constructor : CostConstructor (DeclaredConstructor theory.presentation.presentation) //
      profile.IsDeclaredCostConstructor constructor }

def renderDeclaredCostConstructor (profile : ContinuationDecorationProfile cut) :
    profile.DeclaredCostConstructor → String :=
  fun constructor => CostConstructor.render (fun authored => authored.1.label) constructor.1

theorem renderDeclaredCostConstructor_injective (profile : ContinuationDecorationProfile cut) :
    Function.Injective profile.renderDeclaredCostConstructor := by
  intro left right same
  apply Subtype.ext
  exact CostConstructor.render_injective _
    (ContinuationRetypingPlan.authoredConstructorLabel_injective theory.presentation.presentation) same

/-- Role classification is by the exact authored principal declarations,
using the existing role type rather than a second role hierarchy. -/
def declaredCostConstructorRole (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) : CIGSLT.GeneratedCostConstructorRole :=
  match constructor.1 with
  | .base authored =>
      if authored = cut.program.constructor ∨ authored = cut.environment.constructor then
        .interactionPrincipal
      else .static .base
  | .wrapped _ => .static .wrapped
  | .apparatus kind => .apparatus kind

/-- Actual finite grammar-row interpretation. The base row uses all selected
slots, not only the two primary positions. -/
def materializeDeclaredCostConstructor (profile : ContinuationDecorationProfile cut) :
    profile.DeclaredCostConstructor → GrammarRule
  | ⟨.base authored, _⟩ => profile.baseConstructor authored.1
  | ⟨.wrapped authored, _⟩ => costWrappedConstructor (theory := theory) authored.1
  | ⟨.apparatus kind, _⟩ => kind.grammarRule theory.presentation.interactingSort.1.name

@[simp] theorem materializeDeclaredCostConstructor_label (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) :
    (profile.materializeDeclaredCostConstructor constructor).label =
      profile.renderDeclaredCostConstructor constructor := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base authored => rfl
  | wrapped authored => rfl
  | apparatus kind => cases kind <;> rfl

theorem materializeDeclaredCostConstructor_injective (profile : ContinuationDecorationProfile cut) :
    Function.Injective profile.materializeDeclaredCostConstructor := by
  intro left right same
  apply profile.renderDeclaredCostConstructor_injective
  rw [← profile.materializeDeclaredCostConstructor_label left,
    ← profile.materializeDeclaredCostConstructor_label right, same]

theorem materializeDeclaredCostConstructor_mem (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) :
    profile.materializeDeclaredCostConstructor constructor ∈ profile.costCoreLanguage.terms := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base authored =>
    exact List.mem_append_left _ (profile.baseConstructor_mem authored.1 authored.2)
  | wrapped authored =>
    exact List.mem_append_left _ (profile.wrappedConstructor_mem authored declared)
  | apparatus kind =>
    apply List.mem_append_right
    rw [costCoreConstructors_eq_typed]
    exact List.mem_map.mpr ⟨kind, by cases kind <;> simp [costCoreConstructorKinds], rfl⟩

/-- No generated row is omitted by intrinsic classification, including all
of the exact key, signature, stack, and funding apparatus. -/
theorem exists_declaredCostConstructor_of_mem (profile : ContinuationDecorationProfile cut)
    (rule : GrammarRule) (member : rule ∈ profile.costCoreLanguage.terms) :
    ∃ constructor : profile.DeclaredCostConstructor,
      profile.materializeDeclaredCostConstructor constructor = rule := by
  rcases List.mem_append.mp member with generated | apparatus
  · rcases List.mem_append.mp generated with base | wrapped
    · obtain ⟨authored, included, same⟩ := List.mem_map.mp base
      exact ⟨⟨.base ⟨authored, included⟩, trivial⟩, same⟩
    · obtain ⟨authored, included, same⟩ := List.mem_map.mp wrapped
      exact ⟨⟨.wrapped authored, included⟩, same⟩
  · rw [costCoreConstructors_eq_typed] at apparatus
    obtain ⟨kind, _, same⟩ := List.mem_map.mp apparatus
    exact ⟨⟨.apparatus kind, trivial⟩, same⟩

/-- Finite enumeration retaining exact source declaration identity. -/
def declaredCostConstructors (profile : ContinuationDecorationProfile cut) :
    List profile.DeclaredCostConstructor :=
  theory.presentation.presentation.language.terms.attach.map
      (fun constructor => (⟨.base constructor, trivial⟩ : profile.DeclaredCostConstructor)) ++
    profile.constructorClosure.attach.map
      (fun constructor => (⟨.wrapped constructor.1, constructor.2⟩ : profile.DeclaredCostConstructor)) ++
    costCoreConstructorKinds.map
      (fun kind => (⟨.apparatus kind, trivial⟩ : profile.DeclaredCostConstructor))

/-- Materialization recovers the exact ordered row list, not merely an
existentially equivalent signature. -/
theorem declaredCostConstructors_materialize (profile : ContinuationDecorationProfile cut) :
    profile.declaredCostConstructors.map profile.materializeDeclaredCostConstructor =
      profile.costCoreLanguage.terms := by
  change _ = (theory.presentation.presentation.language.terms.map profile.baseConstructor ++
    profile.constructorClosure.map (fun constructor => costWrappedConstructor (theory := theory) constructor.1)) ++
    costCoreConstructors theory.presentation.interactingSort.1.name
  unfold declaredCostConstructors
  rw [List.map_append, List.map_append, List.map_map, List.map_map, List.map_map]
  change (theory.presentation.presentation.language.terms.attach.map
      (fun constructor => profile.baseConstructor constructor.1) ++
    profile.constructorClosure.attach.map
      (fun constructor => costWrappedConstructor (theory := theory) constructor.1.1)) ++
    costCoreConstructorKinds.map (·.grammarRule theory.presentation.interactingSort.1.name) = _
  rw [List.attach_map_val,
    List.attach_map_val (l := profile.constructorClosure)
      (f := fun constructor => costWrappedConstructor (theory := theory) constructor.1),
    costCoreConstructors_eq_typed]

/-- Signature validation provides duplicate-freedom of the exact intrinsic
enumeration when the supplied profile has no duplicate wrapped rows. -/
theorem declaredCostConstructors_nodup (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) : profile.declaredCostConstructors.Nodup := by
  apply List.Nodup.of_map profile.materializeDeclaredCostConstructor
  rw [profile.declaredCostConstructors_materialize]
  exact List.Nodup.of_map (fun rule => rule.label)
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil _
      (profile.costCoreLanguage_validate noDuplicates))

theorem mem_declaredCostConstructors (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) :
    constructor ∈ profile.declaredCostConstructors := by
  have member := profile.materializeDeclaredCostConstructor_mem constructor
  rw [← profile.declaredCostConstructors_materialize] at member
  obtain ⟨other, included, same⟩ := List.mem_map.mp member
  have identical := profile.materializeDeclaredCostConstructor_injective same
  simpa only [identical] using included

/-- Declaration-aware executable lookup uses the existing finite-list
search, never a wire prefix as a substitute for source membership. -/
def decodeDeclaredCostConstructor (profile : ContinuationDecorationProfile cut) (name : String) :
    Option profile.DeclaredCostConstructor :=
  profile.declaredCostConstructors.find? (fun constructor =>
    profile.renderDeclaredCostConstructor constructor == name)

@[simp] theorem decodeDeclaredCostConstructor_render (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) :
    profile.decodeDeclaredCostConstructor (profile.renderDeclaredCostConstructor constructor) =
      some constructor := by
  unfold decodeDeclaredCostConstructor
  cases found : profile.declaredCostConstructors.find? (fun candidate =>
      profile.renderDeclaredCostConstructor candidate == profile.renderDeclaredCostConstructor constructor) with
  | none =>
    have missing := List.find?_eq_none.mp found constructor (profile.mem_declaredCostConstructors constructor)
    simp at missing
  | some candidate =>
    have equalNames := List.find?_some found
    have same := profile.renderDeclaredCostConstructor_injective (of_decide_eq_true equalNames)
    exact congrArg some same

theorem decodeDeclaredCostConstructor_eq_some_iff (profile : ContinuationDecorationProfile cut)
    (name : String) (constructor : profile.DeclaredCostConstructor) :
    profile.decodeDeclaredCostConstructor name = some constructor ↔
      profile.renderDeclaredCostConstructor constructor = name := by
  constructor
  · intro found
    have same : (profile.renderDeclaredCostConstructor constructor == name) = true :=
      List.find?_some (p := fun candidate : profile.DeclaredCostConstructor =>
        profile.renderDeclaredCostConstructor candidate == name) found
    exact of_decide_eq_true same
  · intro same
    rw [← same]
    exact profile.decodeDeclaredCostConstructor_render constructor

theorem decodeDeclaredCostConstructor_eq_none_iff (profile : ContinuationDecorationProfile cut)
    (name : String) : profile.decodeDeclaredCostConstructor name = none ↔
      ∀ constructor : profile.DeclaredCostConstructor,
        profile.renderDeclaredCostConstructor constructor ≠ name := by
  constructor
  · intro missing constructor same
    have found := (profile.decodeDeclaredCostConstructor_eq_some_iff name constructor).mpr same
    rw [missing] at found
    cases found
  · intro absent
    cases found : profile.decodeDeclaredCostConstructor name with
    | none => rfl
    | some constructor =>
      exact False.elim (absent constructor
        ((profile.decodeDeclaredCostConstructor_eq_some_iff name constructor).mp found))

/-- Exact nonprincipal closure is the extra declaration fact needed by the
existing region role discipline. It supplies a wrapped declaration for each
static base declaration and excludes both principals. -/
theorem declaredCostConstructorRole_base_static_iff
    (programAdditional : List (ContinuationDecorationSlot cut.program))
    (environmentAdditional : List (ContinuationDecorationSlot cut.environment))
    (authored : DeclaredConstructor theory.presentation.presentation) :
    (withNonprincipalInventory programAdditional environmentAdditional).declaredCostConstructorRole
      ⟨.base authored, trivial⟩ = .static .base ↔
      authored ∈ (withNonprincipalInventory programAdditional environmentAdditional).constructorClosure := by
  rw [withNonprincipalInventory_mem]
  simp [declaredCostConstructorRole, not_or]

/-- A certified static base row is uniformly typed; finite retyping of all
principal payload positions remains in the structural boundary instead. -/
theorem static_base_params
    (programAdditional : List (ContinuationDecorationSlot cut.program))
    (environmentAdditional : List (ContinuationDecorationSlot cut.environment))
    (authored : DeclaredConstructor theory.presentation.presentation)
    (static : (withNonprincipalInventory programAdditional environmentAdditional).declaredCostConstructorRole
      ⟨.base authored, trivial⟩ = .static .base) :
    ((withNonprincipalInventory programAdditional environmentAdditional).materializeDeclaredCostConstructor
      ⟨.base authored, trivial⟩).params = authored.1.params.map (mapTermParam costBaseStaticSymbols) := by
  have included := (declaredCostConstructorRole_base_static_iff programAdditional environmentAdditional authored).mp static
  have excluded := (withNonprincipalInventory_mem programAdditional environmentAdditional authored).mp included
  exact (withNonprincipalInventory programAdditional environmentAdditional).baseConstructor_params_eq_map_of_nonprincipal
    authored.1 (fun same => excluded.1 (Subtype.ext same))
      (fun same => excluded.2 (Subtype.ext same))

/-- Old and finite-profile intrinsic declaration carriers coincide exactly. -/
theorem ofRetypingPlan_IsDeclaredCostConstructor (source : CIGSLT)
    (constructor : source.GeneratedCostConstructor) :
    (ofRetypingPlan source.continuationRetyping).IsDeclaredCostConstructor constructor ↔
      source.IsDeclaredCostConstructor constructor := by
  cases constructor <;> rfl

def ofCIGSLTConstructor (source : CIGSLT) (constructor : source.DeclaredCostConstructor) :
    (ofRetypingPlan source.continuationRetyping).DeclaredCostConstructor :=
  ⟨constructor.1, (ofRetypingPlan_IsDeclaredCostConstructor source constructor.1).mpr constructor.2⟩

/-- The migration retains the entire intrinsic constructor, including its
authored declaration witness. Only proof-irrelevant membership is transported. -/
def cigsltConstructorEquiv (source : CIGSLT) :
    source.DeclaredCostConstructor ≃
      (ofRetypingPlan source.continuationRetyping).DeclaredCostConstructor where
  toFun := ofCIGSLTConstructor source
  invFun := fun constructor =>
    ⟨constructor.1, (ofRetypingPlan_IsDeclaredCostConstructor source constructor.1).mp constructor.2⟩
  left_inv := by intro constructor; cases constructor; rfl
  right_inv := by intro constructor; cases constructor; rfl

theorem ofRetypingPlan_declaredCostConstructorRole (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    (ofRetypingPlan source.continuationRetyping).declaredCostConstructorRole
        (ofCIGSLTConstructor source constructor) = source.declaredCostConstructorRole constructor := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor <;> rfl

theorem ofRetypingPlan_materializeDeclaredCostConstructor (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    (ofRetypingPlan source.continuationRetyping).materializeDeclaredCostConstructor
        (ofCIGSLTConstructor source constructor) =
      source.materializeDeclaredCostConstructor constructor := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base authored => exact ofRetypingPlan_baseConstructor _ _
  | wrapped authored => rfl
  | apparatus kind => rfl

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
