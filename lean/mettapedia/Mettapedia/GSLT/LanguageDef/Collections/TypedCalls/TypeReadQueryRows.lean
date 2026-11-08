import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryArguments

/-!
# Ordered signature rows under growing private coordinates

Argument inference may allocate while choosing a row's shared substitution.
The row's range and all remaining row variables stay protected through that
growth. Normalization must preserve resource closure, name support and the
coordinate action; resource closure alone does not imply the latter laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRows

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines.ReadOnlyQueryWorldRelation (Related)
open TypeDependencyAdmission TypeReadQueryWorlds
open RetainedTypePayloads (ExternalView)

structure Normalizers (first second : Atom → Atom) : Prop where
  safe : ∀ atom, resourceFree atom = true → resourceFree (first atom) = true
  support : ∀ atom, resourceFree atom = true → atomVariables (first atom) ⊆ atomVariables atom
  rename : ∀ (names : Equiv.Perm String) atom, resourceFree atom = true →
    second (renameAtom names atom) = renameAtom names (first atom)

theorem normalized_related {first second : Atom → Atom} (normalizers : Normalizers first second)
    {world : Coordinates} {left right : Atom} (related : AtomRelated world left right) :
    AtomRelated world (first left) (second right) := by
  refine ⟨normalizers.safe left related.1,
    fun _ member => related.2.1 (normalizers.support left related.1 member), ?_⟩
  rw [related.2.2]
  exact normalizers.rename world.names left related.1

theorem source_normalizer (external : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive)
    (supported : TypeNormalizationNames.ResultsSupported active primitive)
    (equivariant : TypeNormalizationNames.Equivariant active primitive) :
    Normalizers (InertTypeDependencies.normalize active (TypeNormalizationScope.observed external primitive))
      (InertTypeDependencies.normalize active (TypeNormalizationScope.observed external primitive)) :=
  ⟨TypeNormalizationScope.normalize_preserves active _ (TypeNormalizationScope.observed_closed active external primitive closed),
    TypeNormalizationNames.normalize_observed_support active primitive closed supported external,
    TypeNormalizationNames.normalize_observed_equivariant active primitive closed equivariant external⟩

theorem arrow_support (external : ExternalView) (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    {row : Atom} {formals : List Atom} {range : Atom}
    (selected : (TypeScopeMatcher.ops external normalize subtypes).arrow row = some (formals, range)) :
    atomListVariables formals ⊆ atomVariables row ∧ atomVariables range ⊆ atomVariables row := by
  simp only [TypeScopeMatcher.ops, Option.bind_eq_some_iff, Option.map_eq_some_iff] at selected
  obtain ⟨params, args, returned, result, same⟩ := selected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  unfold getFunctionArgTypes at args
  split at args <;> try contradiction
  split at args <;> try contradiction
  have paramsEq := Option.some.inj args
  rename_i ignored rest enough
  constructor
  · intro name member
    rw [← paramsEq] at member
    simp only [atomListVariables_eq_flatMap, List.mem_flatMap] at member
    obtain ⟨child, present, occurs⟩ := member
    change name ∈ [] ++ atomListVariables rest
    apply List.mem_append_right
    rw [atomListVariables_eq_flatMap]
    exact List.mem_flatMap.mpr ⟨child, List.mem_of_mem_dropLast present, occurs⟩
  · intro name member
    simp only [getFunctionRetType, if_pos enough] at result
    change name ∈ [] ++ atomListVariables rest
    apply List.mem_append_right
    rw [atomListVariables_eq_flatMap]
    exact List.mem_flatMap.mpr ⟨returned, List.mem_of_getLast? result, member⟩

theorem signature_related (external : ExternalView) (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    {world : Coordinates} {row other : Atom} (related : AtomRelated world row other)
    {formals : List Atom} {range : Atom}
    (selected : (TypeScopeMatcher.ops external normalize subtypes).arrow row = some (formals, range)) :
    TypesRelated world formals (formals.map (renameAtom world.names)) ∧
      AtomRelated world range (renameAtom world.names range) := by
  have safe := TypeScopeMatcher.arrow_resourceFree external normalize subtypes related.1 selected
  have support := arrow_support external normalize subtypes selected
  exact ⟨⟨safe.1, fun _ member => related.2.1 (support.1 member), rfl⟩,
    ⟨safe.2, fun _ member => related.2.1 (support.2 member), rfl⟩⟩

theorem rowsPlan (external : ExternalView) (firstNormalize secondNormalize : Atom → Atom)
    (normalizers : Normalizers firstNormalize secondNormalize)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (rows : List Atom) :
    ∀ (world : Coordinates) (otherRows values : List Atom),
      TypesRelated world rows otherRows → Fixed world (atomListVariables values) →
      Related viewWorlds TypeAnswers world
        (NativeTypeDemand.rowsPlan (TypeScopeMatcher.ops external firstNormalize firstSubtypes) values rows)
        (NativeTypeDemand.rowsPlan (TypeScopeMatcher.ops external secondNormalize secondSubtypes) values otherRows) := by
  induction rows with
  | nil =>
      intro world otherRows values related _
      rw [related.2.2]
      exact .pure (.ok ⟨rfl, by simp [atomListVariables], rfl⟩)
  | cons row rows ih =>
      intro world otherRows values related fixed
      have rowRelated := types_member related (List.mem_cons_self : row ∈ row :: rows)
      have tailRelated := types_tail related
      rw [related.2.2]
      simp only [List.map_cons, NativeTypeDemand.rowsPlan,
        TypeRowFreshening.arrow_rename external secondNormalize secondSubtypes world.names row]
      have arrowSame : (TypeScopeMatcher.ops external secondNormalize secondSubtypes).arrow row =
          (TypeScopeMatcher.ops external firstNormalize firstSubtypes).arrow row := rfl
      rw [arrowSame]
      cases chosen : (TypeScopeMatcher.ops external firstNormalize firstSubtypes).arrow row with
      | none => exact ih world _ values tailRelated fixed
      | some signature =>
          rcases signature with ⟨formals, range⟩
          have parts := signature_related external firstNormalize firstSubtypes rowRelated chosen
          simp only [Option.map_some, renameAtomList_eq_map]
          apply Mettapedia.Machines.ReadOnlyQueryWorldRelation.bind_related viewWorlds BindingAnswers TypeAnswers
          · exact TypeReadQueryArguments.argsPlan external firstNormalize secondNormalize firstSubtypes secondSubtypes
              formals world _ values Atom.var Atom.var parts.1 fixed (TypeReadQueryMatcher.initial world)
          · intro next grown firstAnswer secondAnswer answers
            cases answers with
            | error => exact .pure .error
            | ok selected =>
                cases selected with
                | none => exact ih next _ values (types_mono grown tailRelated) (fixed_mono grown fixed)
                | some states =>
                    have rangeRelated := atom_mono grown parts.2
                    have resultRelated := normalized_related normalizers
                      (TypeReadQueryMatcher.apply_related states rangeRelated)
                    apply Mettapedia.Machines.ReadOnlyQueryWorldRelation.map_related
                      viewWorlds TypeAnswers TypeAnswers
                    · exact ih next _ values (types_mono grown tailRelated) (fixed_mono grown fixed)
                    · intro last extended firstTail secondTail tails
                      cases tails with
                      | error => exact .error
                      | ok tailTypes => exact .ok (types_cons (atom_mono extended resultRelated) tailTypes)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRows
