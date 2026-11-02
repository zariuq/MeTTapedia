import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Typed

/-!
# The generators of restriction blocks between processes

Over any calculus with restriction: each generator of the static theory by its shape keeps the process sort, both
ways, for a source with no binder names (`generator_typed`), and between processes it is a chain through processes
(`generator_equiv`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm (hasCanonicalBinderMetadataList_iff)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Prenex

variable {language : LanguageDef} {block : Block} [laws : BlockSignature language block]

/-- The body of a restriction is a process under one more name. -/
theorem restriction_body {free : FreeTypeContext} {bound : List TypeExpr} {binder : Option String} {body : Pattern}
    {type : TypeExpr} (typed : HasType language free bound (.apply block.restrict [.lambda binder body]) type) :
    HasType language free (.base block.name :: bound) body (.base block.proc) :=
  (laws.restriction_typed typed).1


omit laws in
/-- **Strengthening a lifted process**: it does not use the variable it was lifted past. -/
theorem unlift_typed {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free (.base block.name :: bound) (liftBVars 0 1 pattern) type) :
    HasType language free bound pattern type := by
  rw [liftBVars_eq_rename] at typed
  have unused : ¬ FreeIn ([] : List TypeExpr).length (rename (shiftAbove 0 1) pattern) := by
    rw [freeIn_rename]
    rintro ⟨original, -, equal⟩
    simp [shiftAbove] at equal
  have dropped := drop_typed (inner := []) (outer := bound) typed unused
  rw [rename_comp] at dropped
  have identity : (dropIndex ([] : List TypeExpr).length ∘ shiftAbove 0 1) = id := by
    funext index
    simp [dropIndex, shiftAbove]
  rw [identity, rename_id] at dropped
  simpa using dropped

omit laws in
theorem lift_one {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType language free bound pattern (.base block.proc)) :
    HasType language free (.base block.name :: bound) (liftBVars 0 1 pattern) (.base block.proc) :=
  lift_typed (inner := []) (inserted := [.base block.name]) (outer := bound) typed

omit laws in
/-- The members of a bag are the selected one and the others. -/
theorem members_iff_selected {free : FreeTypeContext} {bound : List TypeExpr} {members : List Pattern}
    {selected : Nat} (inside : selected < members.length) :
    Members language block free bound members ↔
      HasType language free bound members[selected] (.base block.proc) ∧ Members language block free bound (members.eraseIdx selected) := by
  have permutation := perm_getElem_eraseIdx members selected inside
  constructor
  · intro all
    exact ⟨all _ (List.getElem_mem inside), fun element member => all element (List.mem_of_mem_eraseIdx member)⟩
  · rintro ⟨chosen, others⟩ element member
    rcases List.mem_cons.mp (permutation.mem_iff.mp member) with rfl | other
    · exact chosen
    · exact others element other

omit laws in
theorem swapInner_sorts {bound : List TypeExpr} (index : Nat) (sort : TypeExpr)
    (lookup : (TypeExpr.base block.name :: .base block.name :: bound)[index]? = some sort) :
    (TypeExpr.base block.name :: .base block.name :: bound)[swapInner index]? = some sort := by
  unfold swapInner
  rcases index with _ | _ | index <;> simpa using lookup

omit laws in
theorem swapped_typed {free : FreeTypeContext} {bound : List TypeExpr} {body : Pattern}
    (typed : HasType language free (.base block.name :: .base block.name :: bound) body (.base block.proc)) :
    HasType language free (.base block.name :: .base block.name :: bound) (rename swapInner body) (.base block.proc) :=
  rename_typed typed swapInner_sorts

omit laws in
theorem binder_none_of_canonical {binder : Option String} {body : Pattern}
    (canonical : (Pattern.apply block.restrict [.lambda binder body]).hasCanonicalBinderMetadata = true) : binder = none := by
  simp only [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Bool.and_true,
    Bool.and_eq_true, Option.isNone_iff_eq_none] at canonical
  exact canonical.1

omit laws in
theorem canonical_member {kind : CollType} {elements : List Pattern} {rest : Option String} {element : Pattern}
    (canonical : (Pattern.collection kind elements rest).hasCanonicalBinderMetadata = true) (member : element ∈ elements) :
    element.hasCanonicalBinderMetadata = true := by
  simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical
  exact canonical element member

omit laws in
theorem restriction_canonical {binder : Option String} {body : Pattern}
    (canonical : (Pattern.apply block.restrict [.lambda binder body]).hasCanonicalBinderMetadata = true) :
    body.hasCanonicalBinderMetadata = true := by
  simp only [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Bool.and_true,
    Bool.and_eq_true] at canonical
  exact canonical.2

/-- A bag law read from left to right keeps the process sort. -/
theorem derived_typed_forward {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (derived : DerivedInstance language source target) (typed : HasType language free bound source (.base block.proc)) :
    HasType language free bound target (.base block.proc) := by
  obtain ⟨bag, presented, category⟩ := laws.bag
  rw [← category] at typed ⊢
  exact presented.derived_hasType derived typed rfl

/-- A bag law read from right to left keeps the process sort. -/
theorem derived_typed_reverse {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (derived : DerivedInstance language source target) (typed : HasType language free bound target (.base block.proc)) :
    HasType language free bound source (.base block.proc) := by
  cases derived with
  | bagPerm _ _ permutation =>
      have members := members_of_bag typed
      exact bag_typed fun element member => members element (permutation.mem_iff.mp member)
  | setPerm declaration kindTyped _ =>
      exact ((laws.no_set_rule declaration) kindTyped).elim
  | setDedup declaration kindTyped =>
      exact ((laws.no_set_rule declaration) kindTyped).elim
  | flatten declaration _ _ =>
      obtain ⟨rfl, -⟩ := laws.algebra_shape declaration
      have members := members_of_bag typed
      apply bag_typed
      intro element member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inBefore | rfl | inAfter
      · exact members element (by simp [inBefore])
      · exact bag_typed fun inner member => members inner (by simp [member])
      · exact members element (by simp [inAfter])
  | singleton declaration _ _ =>
      obtain ⟨rfl, -⟩ := laws.algebra_shape declaration
      exact bag_typed fun element member => by
        rw [List.mem_singleton.mp member]
        exact typed
  | unitElim declaration unitIs _ =>
      obtain ⟨rfl, named⟩ := laws.algebra_shape declaration
      rw [unitIs, Option.some.injEq] at named
      subst named
      have members := members_of_bag typed
      apply bag_typed
      intro element member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inBefore | rfl | inAfter
      · exact members element (by simp [inBefore])
      · exact laws.unit_typed
      · exact members element (by simp [inAfter])
  | emptyUnit declaration _ _ =>
      obtain ⟨rfl, -⟩ := laws.algebra_shape declaration
      exact bag_typed Members.nil

/-- **Every law of the static theory keeps the process sort, both ways**, for a source with no binder names. -/
theorem generator_typed {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (generator : BlockGenerator language block source target) (canonical : source.hasCanonicalBinderMetadata = true) :
    HasType language free bound source (.base block.proc) ↔ HasType language free bound target (.base block.proc) := by
  cases generator with
  | nil binder =>
      cases binder_none_of_canonical canonical
      exact ⟨fun _ => laws.unit_typed, fun _ => restrict_typed laws.unit_typed⟩
  | nilReverse => exact ⟨fun _ => restrict_typed laws.unit_typed, fun _ => laws.unit_typed⟩
  | extrusion members selected binder body inside chosen =>
      have chosenCanonical := canonical_member canonical (List.getElem_mem inside)
      rw [chosen] at chosenCanonical
      cases binder_none_of_canonical chosenCanonical
      constructor
      · intro typed
        obtain ⟨chosenTyped, others⟩ := (members_iff_selected inside).mp (members_of_bag typed)
        rw [chosen] at chosenTyped
        apply restrict_typed
        apply bag_typed
        intro element member
        rcases List.mem_cons.mp member with rfl | lifted
        · exact restriction_body chosenTyped
        · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp lifted
          exact lift_one (others original originalMember)
      · intro typed
        have inner := members_of_bag (restriction_body typed)
        apply bag_typed
        refine (members_iff_selected inside).mpr ⟨?_, fun element member => ?_⟩
        · rw [chosen]
          exact restrict_typed (inner _ List.mem_cons_self)
        · exact unlift_typed (inner _ (List.mem_cons_of_mem _ (List.mem_map_of_mem member)))
  | extrusionReverse binder members selected originals inside othersEq =>
      cases binder_none_of_canonical canonical
      constructor
      · intro typed
        obtain ⟨chosenTyped, others⟩ := (members_iff_selected inside).mp (members_of_bag (restriction_body typed))
        apply bag_typed
        intro element member
        rcases List.mem_cons.mp member with rfl | original
        · exact restrict_typed chosenTyped
        · exact unlift_typed (others _ (by rw [othersEq]; exact List.mem_map_of_mem original))
      · intro typed
        have outer := members_of_bag typed
        apply restrict_typed
        apply bag_typed
        refine (members_iff_selected inside).mpr ⟨restriction_body (outer _ List.mem_cons_self), ?_⟩
        rw [othersEq]
        intro element member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact lift_one (outer original (List.mem_cons_of_mem _ originalMember))
  | exchange outerBinder innerBinder body =>
      cases binder_none_of_canonical canonical
      cases binder_none_of_canonical (restriction_canonical canonical)
      constructor
      · intro typed
        exact restrict_typed (restrict_typed (swapped_typed (restriction_body (restriction_body typed))))
      · intro typed
        have swapped := swapped_typed (restriction_body (restriction_body typed))
        rw [rename_swapInner_swapInner] at swapped
        exact restrict_typed (restrict_typed swapped)
  | emptyUnit label listed =>
      exact ⟨fun _ => restrict_typed laws.unit_typed, fun _ => laws.emptyMultiset_typed listed⟩
  | emptyUnitReverse label listed binder =>
      cases binder_none_of_canonical canonical
      exact ⟨fun _ => laws.emptyMultiset_typed listed, fun _ => restrict_typed laws.unit_typed⟩
  | derived derivedInstance =>
      exact ⟨fun typed => derived_typed_forward derivedInstance typed, derived_typed_reverse derivedInstance⟩


open Mettapedia.GSLT.LanguageDef.EquationSemantics (declaredInstanceAt_of_applyEquationAt)

/-- **Every law between processes is a chain through processes**, for a source with no binder names. -/
theorem generator_equiv {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (generator : BlockGenerator language block source target) (canonical : source.hasCanonicalBinderMetadata = true)
    (sourceTyped : HasType language free bound source (.base block.proc)) :
    ProcEquiv language block free bound source target := by
  have targetTyped := (generator_typed generator canonical).mp sourceTyped
  cases generator with
  | nil binder =>
      cases binder_none_of_canonical canonical
      exact restriction_nil_equivalent
  | nilReverse => exact .symm _ _ restriction_nil_equivalent
  | extrusion members selected binder body inside chosen =>
      have chosenCanonical := canonical_member canonical (List.getElem_mem inside)
      rw [chosen] at chosenCanonical
      cases binder_none_of_canonical chosenCanonical
      obtain ⟨chosenTyped, others⟩ := (members_iff_selected inside).mp (members_of_bag sourceTyped)
      rw [chosen] at chosenTyped
      have bodyScoped := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt (restriction_body chosenTyped)
      have othersScoped := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt
        (bag_typed (rest := none) others)
      have membersScoped := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt sourceTyped
      simp only [List.length_cons] at bodyScoped
      rw [Nat.add_comm] at bodyScoped
      exact SortedEquiv.ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length)
        laws.extrusion_mem rfl
        (declaredInstanceAt_of_applyEquationAt
          (extrusion_instance_at inside chosen bodyScoped othersScoped membersScoped))⟩ sourceTyped targetTyped
  | extrusionReverse binder members selected originals inside othersEq =>
      cases binder_none_of_canonical canonical
      have inner := restriction_body sourceTyped
      obtain ⟨chosenTyped, others⟩ := (members_iff_selected inside).mp (members_of_bag inner)
      have permutation := perm_getElem_eraseIdx members selected inside
      have middleMembers : Members language block free (.base block.name :: bound)
          (members[selected] :: members.eraseIdx selected) := Members.cons chosenTyped others
      have middleTyped := restrict_typed (bag_typed (rest := none) middleMembers)
      have reorder := restrict_fill (SortedEquiv.ofDerived
        (DerivedInstance.bagPerm_of_sorted ⟨free, .base block.name :: bound, bag_typed (members_of_bag inner)⟩
          permutation) (bag_typed (members_of_bag inner)) (bag_typed (rest := none) middleMembers))
      have outer := members_of_bag targetTyped
      have bodyScoped := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt
        (restriction_body (outer _ List.mem_cons_self))
      simp only [List.length_cons] at bodyScoped
      rw [Nat.add_comm] at bodyScoped
      have extruded := extrusion_instance (language := language) (block := block) (ambient := bound.length) bodyScoped
        (Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt (bag_typed (rest := none) outer.tail))
      rw [← othersEq] at extruded
      have extrude := SortedEquiv.ofInstance (sort := .base block.proc) ⟨0, .declared (orientation := .forward)
        (ambient := bound.length) laws.extrusion_mem rfl (declaredInstanceAt_of_applyEquationAt extruded)⟩
        targetTyped middleTyped
      exact .trans _ _ _ reorder (.symm _ _ extrude)
  | exchange outerBinder innerBinder body =>
      cases binder_none_of_canonical canonical
      cases binder_none_of_canonical (restriction_canonical canonical)
      exact exchange_equivalent (restriction_body (restriction_body sourceTyped))
  | emptyUnit label listed =>
      exact SortedEquiv.ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length)
        (laws.emptyUnit_mem listed) rfl (declaredInstanceAt_of_applyEquationAt emptyUnit_instance)⟩
        sourceTyped targetTyped
  | emptyUnitReverse label listed binder =>
      cases binder_none_of_canonical canonical
      exact .symm _ _ (SortedEquiv.ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length)
        (laws.emptyUnit_mem listed) rfl (declaredInstanceAt_of_applyEquationAt emptyUnit_instance)⟩
        targetTyped sourceTyped)
  | derived derivedInstance => exact SortedEquiv.ofDerived derivedInstance sourceTyped targetTyped

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
