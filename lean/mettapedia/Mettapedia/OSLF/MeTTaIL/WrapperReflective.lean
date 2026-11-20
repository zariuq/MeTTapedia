import Mettapedia.OSLF.MeTTaIL.WrapperMatching
import Mettapedia.OSLF.MeTTaIL.QuoteDropTyping

/-!
# Wrapper normal forms through reflective substitution

Reflective substitution tests the whole name modulo its declared equations.
The wrapper laws must therefore refer to that parallel collection and its
unit (`BinderWrapperCompatible`). They may change the retained spelling of
a miss, but not the binding decision. If a wrapper exposes an unmatched
index, scope ensures that index is already below the binder being removed.

Wrapper steps keep scope, binder metadata, object terms, substitution and index lifting; with the
quote-drop steps they form the forward chains `QWForward`, which keep well-sortedness
(`QWForward.openPatternWellSorted`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax CollectionLaws CanonicalBags ReflectiveSubstitution QuoteDrop
open Mettapedia.GSLT.LanguageDef.WellSorted
open Relation (ReflTransGen)

variable {laws : List Laws} {declaration : ReflectivePresentationDecl}

/-! ## Wrapper steps keep scope, binder metadata and object terms -/

theorem listAll_middle' {f : Pattern → Bool} {before after : List Pattern} {x y : Pattern} (same : f x = f y) :
    (before ++ x :: after).all f = (before ++ y :: after).all f := by
  simp [List.all_append, same]

theorem wellScopedList_middle (depth : Nat) {before after : List Pattern} {x y : Pattern}
    (same : x.isWellScopedAt depth = y.isWellScopedAt depth) :
    Pattern.isWellScopedListAt depth (before ++ x :: after) = Pattern.isWellScopedListAt depth (before ++ y :: after) := by
  induction before with
  | nil => simp [Pattern.isWellScopedListAt, same]
  | cons first rest ih => simp [Pattern.isWellScopedListAt, ih]

theorem WrapperStep.wellScoped {left right : Pattern} (step : WrapperStep laws left right) :
    ∀ depth, left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction step with
  | singleton _ => intro depth; simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | empty _ _ => intro depth; simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | apply _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact wellScopedList_middle depth (ih depth)
  | lambda _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact ih _
  | multiLambda _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact ih _
  | substBody _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | substReplacement _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | element _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact wellScopedList_middle depth (ih depth)

theorem WrapperStep.binderMetadata_eq {left right : Pattern} (step : WrapperStep laws left right) :
    left.hasCanonicalBinderMetadata = right.hasCanonicalBinderMetadata := by
  have listForm : ∀ items : List Pattern,
      Pattern.hasCanonicalBinderMetadataList items = items.all Pattern.hasCanonicalBinderMetadata := by
    intro items
    induction items with
    | nil => rfl
    | cons item rest ih => simp [Pattern.hasCanonicalBinderMetadataList, ih]
  induction step with
  | singleton _ => simp [Pattern.hasCanonicalBinderMetadata, listForm]
  | empty _ _ => simp [Pattern.hasCanonicalBinderMetadata, listForm]
  | apply _ ih => simp only [Pattern.hasCanonicalBinderMetadata, listForm]; exact listAll_middle' ih
  | lambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | multiLambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substBody _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substReplacement _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | element _ ih => simp only [Pattern.hasCanonicalBinderMetadata, listForm]; exact listAll_middle' ih

theorem WrapperStep.objectPattern_eq {left right : Pattern} (step : WrapperStep laws left right) :
    isObjectPattern left = isObjectPattern right := by
  induction step with
  | singleton _ => simp [isObjectPattern, isObjectPatternList_eq_all]
  | empty _ _ => simp [isObjectPattern, isObjectPatternList_eq_all]
  | apply _ ih => simp only [isObjectPattern, isObjectPatternList_eq_all]; exact listAll_middle' ih
  | lambda _ ih => simp only [isObjectPattern, ih]
  | multiLambda _ ih => simp only [isObjectPattern, ih]
  | substBody _ _ => simp only [isObjectPattern]
  | substReplacement _ _ => simp only [isObjectPattern]
  | element _ ih => simp only [isObjectPattern, isObjectPatternList_eq_all]; rw [listAll_middle' ih]

/-- **One wrapper step keeps well-sortedness** at a type without collections of a flattening kind. -/
theorem WrapperStep.openPatternWellSorted {language : LanguageDef} {free : FreeTypeContext}
    (admission : WrappersTyped laws language) {left right : Pattern} (step : WrapperStep laws left right)
    {bound : List TypeExpr} {type : TypeExpr} (noLaw : NoLawCollections laws type)
    (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  obtain ⟨typed, metadata, object, scope⟩ := sorted
  exact ⟨step.hasType admission object noLaw typed, step.binderMetadata_eq ▸ metadata, step.objectPattern_eq ▸ object,
    by unfold ScopeSafeAt at scope ⊢; rw [← step.wellScoped]; exact scope⟩

/-! ## Substitution and index lifting -/

theorem WrapperStep.substitute {left right : Pattern} (step : WrapperStep laws left right) :
    ∀ assignment : ContextSubstitution.Assignment,
      WrapperStep laws (ContextSubstitution.substitute assignment left) (ContextSubstitution.substitute assignment right) := by
  induction step with
  | singleton found =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_cons, List.map_nil]
    exact .singleton found
  | empty found unit =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_nil]
    exact .empty found unit
  | apply _ ih =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .apply (ih assignment)
  | lambda _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .lambda (ih _)
  | multiLambda _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .multiLambda (ih _)
  | substBody _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .substBody (ih _)
  | substReplacement _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .substReplacement (ih _)
  | element _ ih =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .element (ih assignment)

theorem WrapperStep.liftBVars {left right : Pattern} (step : WrapperStep laws left right) :
    ∀ cutoff shift, WrapperStep laws (Substitution.liftBVars cutoff shift left) (Substitution.liftBVars cutoff shift right) := by
  induction step with
  | singleton found =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_cons, List.map_nil]
    exact .singleton found
  | empty found unit =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_nil]
    exact .empty found unit
  | apply _ ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_append, List.map_cons]
    exact .apply (ih cutoff shift)
  | lambda _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .lambda (ih _ _)
  | multiLambda _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .multiLambda (ih _ _)
  | substBody _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .substBody (ih _ _)
  | substReplacement _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .substReplacement (ih _ _)
  | element _ ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_append, List.map_cons]
    exact .element (ih cutoff shift)

/-! ## Forward chains of quote-drop and wrapper steps -/

variable (laws declaration) in
/-- One quote-drop or wrapper step, left to right. -/
def QWStep (left right : Pattern) : Prop := QuoteDropStep declaration left right ∨ WrapperStep laws left right

variable (laws declaration) in
/-- A forward chain of quote-drop and wrapper steps. -/
abbrev QWForward (left right : Pattern) : Prop := ReflTransGen (QWStep laws declaration) left right

theorem QWForward.lift {f : Pattern → Pattern}
    (quoteLift : ∀ {a b : Pattern}, QuoteDropStep declaration a b → QuoteDropStep declaration (f a) (f b))
    (wrapperLift : ∀ {a b : Pattern}, WrapperStep laws a b → WrapperStep laws (f a) (f b)) {a b : Pattern}
    (forward : QWForward laws declaration a b) : QWForward laws declaration (f a) (f b) := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih =>
    rcases step with quoteDrop | wrapped
    · exact .tail ih (.inl (quoteLift quoteDrop))
    · exact .tail ih (.inr (wrapperLift wrapped))

theorem QWForward.ofQuoteDrop {a b : Pattern} (forward : QuoteDropForward declaration a b) :
    QWForward laws declaration a b := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.inl step)

theorem QWForward.ofWrapper {a b : Pattern} (forward : WrapperForward laws a b) : QWForward laws declaration a b := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.inr step)

theorem qwForward_pointwise (wrap : List Pattern → Pattern)
    (quoteLift : ∀ (before after : List Pattern) {a b : Pattern}, QuoteDropStep declaration a b →
      QuoteDropStep declaration (wrap (before ++ a :: after)) (wrap (before ++ b :: after)))
    (wrapperLift : ∀ (before after : List Pattern) {a b : Pattern}, WrapperStep laws a b →
      WrapperStep laws (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before : List Pattern) {items items' : List Pattern}, List.Forall₂ (QWForward laws declaration) items items' →
      QWForward laws declaration (wrap (before ++ items)) (wrap (before ++ items'))
  | _, [], [], .nil => .refl
  | before, item :: rest, item' :: _, .cons head tail => by
    have first : QWForward laws declaration (wrap (before ++ item :: rest)) (wrap (before ++ item' :: rest)) :=
      QWForward.lift (f := fun x => wrap (before ++ x :: rest)) (fun step => quoteLift before rest step)
        (fun step => wrapperLift before rest step) head
    have later := qwForward_pointwise wrap quoteLift wrapperLift (before ++ [item']) tail
    simp only [List.append_assoc, List.singleton_append] at later
    exact first.trans later

theorem qwForward_apply (label : String) {items items' : List Pattern}
    (each : List.Forall₂ (QWForward laws declaration) items items') :
    QWForward laws declaration (.apply label items) (.apply label items') := by
  simpa using qwForward_pointwise (fun items => .apply label items) (fun _ _ _ _ step => .apply step)
    (fun _ _ _ _ step => .apply step) [] each

theorem qwForward_collection (kind : CollType) (rest : Option String) {items items' : List Pattern}
    (each : List.Forall₂ (QWForward laws declaration) items items') :
    QWForward laws declaration (.collection kind items rest) (.collection kind items' rest) := by
  simpa using qwForward_pointwise (fun items => .collection kind items rest) (fun _ _ _ _ step => .element step)
    (fun _ _ _ _ step => .element step) [] each

theorem qwForward_lambda (binder : Option String) {body body' : Pattern} (forward : QWForward laws declaration body body') :
    QWForward laws declaration (.lambda binder body) (.lambda binder body') :=
  QWForward.lift (f := .lambda binder) (fun step => .lambda step) (fun step => .lambda step) forward

theorem qwForward_multiLambda (arity : Nat) (binders : List String) {body body' : Pattern}
    (forward : QWForward laws declaration body body') :
    QWForward laws declaration (.multiLambda arity binders body) (.multiLambda arity binders body') :=
  QWForward.lift (f := .multiLambda arity binders) (fun step => .multiLambda step) (fun step => .multiLambda step) forward

theorem qwForward_subst {body body' replacement replacement' : Pattern}
    (forwardBody : QWForward laws declaration body body')
    (forwardReplacement : QWForward laws declaration replacement replacement') :
    QWForward laws declaration (.subst body replacement) (.subst body' replacement') :=
  (QWForward.lift (f := fun x => .subst x replacement) (fun step => .substBody step) (fun step => .substBody step)
    forwardBody).trans
    (QWForward.lift (f := fun x => .subst body' x) (fun step => .substReplacement step)
      (fun step => .substReplacement step) forwardReplacement)

theorem QWForward.substitute {left right : Pattern} (forward : QWForward laws declaration left right)
    (assignment : ContextSubstitution.Assignment) :
    QWForward laws declaration (ContextSubstitution.substitute assignment left)
      (ContextSubstitution.substitute assignment right) :=
  QWForward.lift (f := ContextSubstitution.substitute assignment) (fun step => step.substitute assignment)
    (fun step => step.substitute assignment) forward

theorem QWForward.liftBVars {left right : Pattern} (forward : QWForward laws declaration left right)
    (cutoff shift : Nat) :
    QWForward laws declaration (Substitution.liftBVars cutoff shift left) (Substitution.liftBVars cutoff shift right) :=
  QWForward.lift (f := Substitution.liftBVars cutoff shift) (fun step => step.liftBVars cutoff shift)
    (fun step => step.liftBVars cutoff shift) forward

/-- **Substituting forward-related values gives forward-related results.** -/
theorem qwForward_substitute_assignment : ∀ (pattern : Pattern) {first second : ContextSubstitution.Assignment},
    (∀ index, QWForward laws declaration (first index) (second index)) →
    QWForward laws declaration (ContextSubstitution.substitute first pattern) (ContextSubstitution.substitute second pattern)
  | .bvar index, _, _, pointwise => by simp only [ContextSubstitution.substitute]; exact pointwise index
  | .fvar _, _, _, _ => by simp only [ContextSubstitution.substitute]; exact .refl
  | .apply label arguments, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply qwForward_apply
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact qwForward_substitute_assignment item pointwise
  | .lambda binder body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply qwForward_lambda
    apply qwForward_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl
    · exact QWForward.liftBVars (pointwise _) 0 1
  | .multiLambda arity binders body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply qwForward_multiLambda
    apply qwForward_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl
    · exact QWForward.liftBVars (pointwise _) 0 arity
  | .subst body replacement, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply qwForward_subst
    · apply qwForward_substitute_assignment body
      intro index
      unfold ContextSubstitution.lift
      split
      · exact .refl
      · exact QWForward.liftBVars (pointwise _) 0 1
    · exact qwForward_substitute_assignment replacement pointwise
  | .collection kind elements rest, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply qwForward_collection
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
    exact qwForward_substitute_assignment item pointwise
termination_by pattern => sizeOf pattern

/-- **Ordinary binder elimination maps forward chains to a forward chain.** -/
theorem instantiateBVar_qwForward {replacement replacement' body body' : Pattern}
    (forwardReplacement : QWForward laws declaration replacement replacement')
    (forwardBody : QWForward laws declaration body body') :
    QWForward laws declaration (Substitution.instantiateBVar replacement body)
      (Substitution.instantiateBVar replacement' body') := by
  rw [← ContextSubstitution.substitute_single_eq_instantiateBVar,
    ← ContextSubstitution.substitute_single_eq_instantiateBVar]
  refine (QWForward.substitute forwardBody _).trans (qwForward_substitute_assignment body' ?_)
  intro index
  cases index with
  | zero => exact forwardReplacement
  | succ => exact .refl

/-! ## Scope, indices and drops along forward chains -/

theorem QWStep.wellScoped {left right : Pattern} (step : QWStep laws declaration left right) (depth : Nat) :
    left.isWellScopedAt depth = right.isWellScopedAt depth := by
  rcases step with quoteDrop | wrapped
  · exact quoteDrop.wellScoped depth
  · exact wrapped.wellScoped depth

theorem QWForward.wellScoped {left right : Pattern} (forward : QWForward laws declaration left right) (depth : Nat) :
    left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction forward with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step.wellScoped depth)

theorem qwForward_bvar {index : Nat} {other : Pattern} (forward : QWForward laws declaration (.bvar index) other) :
    other = .bvar index := by
  induction forward with
  | refl => rfl
  | tail _ step ih =>
    subst ih
    rcases step with quoteDrop | wrapped
    · cases quoteDrop
    · cases wrapped

theorem qwStep_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) {name other : Pattern}
    (step : QWStep laws declaration (.apply declaration.dropConstructor [name]) other) :
    ∃ name', other = .apply declaration.dropConstructor [name'] ∧ QWStep laws declaration name name' := by
  rcases step with quoteDrop | wrapped
  · generalize source : Pattern.apply declaration.dropConstructor [name] = term at quoteDrop
    cases quoteDrop with
    | collapse inner =>
      simp only [Pattern.apply.injEq] at source
      exact absurd source.1 distinct
    | @apply label before after argument changed inner =>
      simp only [Pattern.apply.injEq] at source
      obtain ⟨rfl, same⟩ := source
      match before, after, same with
      | [], [], same =>
        simp only [List.nil_append, List.cons.injEq, and_true] at same
        subst same
        exact ⟨changed, rfl, .inl inner⟩
      | _ :: _, _, same => simp at same
      | [], _ :: _, same => simp at same
    | _ => cases source
  · generalize source : Pattern.apply declaration.dropConstructor [name] = term at wrapped
    cases wrapped with
    | @apply label before after argument changed inner =>
      simp only [Pattern.apply.injEq] at source
      obtain ⟨rfl, same⟩ := source
      match before, after, same with
      | [], [], same =>
        simp only [List.nil_append, List.cons.injEq, and_true] at same
        subst same
        exact ⟨changed, rfl, .inr inner⟩
      | _ :: _, _, same => simp at same
      | [], _ :: _, same => simp at same
    | _ => cases source

theorem qwForward_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) {name other : Pattern}
    (forward : QWForward laws declaration (.apply declaration.dropConstructor [name]) other) :
    ∃ name', other = .apply declaration.dropConstructor [name'] ∧ QWForward laws declaration name name' := by
  induction forward with
  | refl => exact ⟨name, rfl, .refl⟩
  | tail _ step ih =>
    obtain ⟨middle, rfl, before⟩ := ih
    obtain ⟨last, rfl, after⟩ := qwStep_drop distinct step
    exact ⟨last, rfl, before.tail after⟩

/-! ## Quote-drop normal forms along wrapper steps -/

/-- **The quote-drop test maps forward chains of the arguments to a forward chain.** -/
theorem finish_qwForward (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (label : String)
    {arguments arguments' : List Pattern} (each : List.Forall₂ (QWForward laws declaration) arguments arguments') :
    QWForward laws declaration (finishNormalizeReflectiveApply declaration label arguments)
      (finishNormalizeReflectiveApply declaration label arguments') := by
  by_cases quoted : label = declaration.quoteConstructor
  · subst quoted
    match arguments, arguments', each with
    | [], [], .nil => exact .refl
    | first :: second :: rest, first' :: second' :: rest', each =>
      rw [finish_long, finish_long]
      exact qwForward_apply _ each
    | [argument], [argument'], .cons head .nil =>
      by_cases shaped : ∃ name, argument = .apply declaration.dropConstructor [name]
      · obtain ⟨name, rfl⟩ := shaped
        obtain ⟨name', rfl, forwardName⟩ := qwForward_drop distinct head
        rw [finish_drop, finish_drop]
        simpa using forwardName
      · have notDrop : ∀ name, argument ≠ .apply declaration.dropConstructor [name] :=
          fun name same => shaped ⟨name, same⟩
        rw [finish_quote_plain notDrop]
        have quoted : QWForward laws declaration (.apply declaration.quoteConstructor [argument])
            (.apply declaration.quoteConstructor [argument']) := qwForward_apply _ (.cons head .nil)
        by_cases shaped' : ∃ name', argument' = .apply declaration.dropConstructor [name']
        · obtain ⟨name', rfl⟩ := shaped'
          rw [finish_drop]
          simp only [beq_self_eq_true, Bool.and_self, if_true]
          exact quoted.tail (.inl (.collapse name'))
        · rw [finish_quote_plain fun name same => shaped' ⟨name, same⟩]
          exact quoted
  · have notQuote : label ≠ declaration.quoteConstructor := quoted
    rw [finish_not_quote notQuote, finish_not_quote notQuote]
    exact qwForward_apply label each

/-- **A wrapper step moves the quote-drop normal form by a forward chain.** -/
theorem normal_qwForward (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) {left right : Pattern}
    (step : WrapperStep laws left right) :
    QWForward laws declaration (normal declaration left) (normal declaration right) := by
  induction step with
  | singleton found =>
    rw [normal_collection]
    simp only [List.map_cons, List.map_nil]
    exact .single (.inr (.singleton found))
  | @empty kind law label found unit =>
    rw [normal_collection, normal_apply, List.map_nil, finish_nil]
    exact .single (.inr (.empty found unit))
  | @apply label before after argument changed _ ih =>
    rw [normal_apply, normal_apply]
    apply finish_qwForward distinct
    simp only [List.map_append, List.map_cons]
    exact List.rel_append (List.forall₂_same.mpr fun _ _ => .refl) (.cons ih (List.forall₂_same.mpr fun _ _ => .refl))
  | lambda _ ih => rw [normal_lambda, normal_lambda]; exact qwForward_lambda _ ih
  | multiLambda _ ih => rw [normal_multiLambda, normal_multiLambda]; exact qwForward_multiLambda _ _ ih
  | substBody _ ih => rw [normal_subst, normal_subst]; exact qwForward_subst ih .refl
  | substReplacement _ ih => rw [normal_subst, normal_subst]; exact qwForward_subst .refl ih
  | element _ ih =>
    rw [normal_collection, normal_collection]
    apply qwForward_collection
    simp only [List.map_append, List.map_cons]
    exact List.rel_append (List.forall₂_same.mpr fun _ _ => .refl) (.cons ih (List.forall₂_same.mpr fun _ _ => .refl))

theorem normal_qwForward_of_forward (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (forward : WrapperForward laws left right) :
    QWForward laws declaration (normal declaration left) (normal declaration right) := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (normal_qwForward distinct step)

/-- A forward chain of quote-drop and wrapper steps moves the quote-drop normal form by a forward chain:
a quote-drop step keeps it. -/
theorem normal_qwForward_of_qwForward (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (forward : QWForward laws declaration left right) :
    QWForward laws declaration (normal declaration left) (normal declaration right) := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih =>
    rcases step with quoteDrop | wrapped
    · rw [← quoteDrop.normalize_eq distinct]; exact ih
    · exact ih.trans (normal_qwForward distinct wrapped)

/-! ## Reflective binder elimination -/

/-- A wrapper may expose a whole name only using the declared reflective
parallel composition. Unlike flattening, eliminating a wrapper of a
different kind can turn an opaque term into a binding reference. -/
def BinderWrapperCompatible (laws : List Laws) (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ {kind law}, lawFor laws kind = some law →
    kind = declaration.parallelCollection ∧
      ∀ {label}, law.unit = some label → label = declaration.parallelUnitConstructor

open BinderHead in
theorem WrapperStep.binderHead_eq (compatible : BinderWrapperCompatible laws declaration)
    {left right : Pattern} (step : WrapperStep laws left right) :
    ofPattern declaration left = ofPattern declaration right := by
  induction step with
  | singleton found => simp [ofPattern, ofList, (compatible found).1]
  | empty found unit =>
    simp [ofPattern, ofList, BinderHead.apply, rigid, (compatible found).1, (compatible found).2 unit]
  | apply inner ih => simp [ofPattern, ofList_eq_map, ih]
  | lambda inner ih => rfl
  | multiLambda inner ih => rfl
  | substBody inner ih => rfl
  | substReplacement inner ih => rfl
  | @element kind before after element changed rest inner ih =>
    cases rest with
    | some rest => rfl
    | none => simp [ofPattern, ofList_eq_map, ih]

open BinderHead in
/-- Removing a wrapper of the wrong kind or using a different empty value
really changes the binding head of some raw term. -/
theorem binderWrapperCompatible_iff :
    BinderWrapperCompatible laws declaration ↔
      ∀ {left right}, WrapperStep laws left right →
        ofPattern declaration left = ofPattern declaration right := by
  refine ⟨fun compatible {_ _} step => step.binderHead_eq compatible, ?_⟩
  intro preserves kind law found
  have parallel : kind = declaration.parallelCollection := by
    by_contra otherKind
    have different := preserves (WrapperStep.singleton (element := .bvar 0) found)
    simp [ofPattern, otherKind] at different
  refine ⟨parallel, ?_⟩
  intro label unit
  by_contra differentUnit
  have different := preserves (WrapperStep.empty found unit)
  simp [ofPattern, ofList, BinderHead.apply, rigid, parallel, differentUnit] at different

theorem QWForward.matchesBinder_eq
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (compatible : BinderWrapperCompatible laws declaration)
    {left right : Pattern} (forward : QWForward laws declaration left right) (depth : Nat) :
    matchesBinder declaration depth left = matchesBinder declaration depth right := by
  induction forward with
  | refl => rfl
  | tail _ step ih =>
    rw [ih]
    rcases step with quoteDrop | wrapper
    · unfold matchesBinder
      rw [quoteDrop.binderHead_eq distinct]
    · unfold matchesBinder
      rw [wrapper.binderHead_eq compatible]

open BinderHead in
theorem WrapperForward.binderHead_eq (compatible : BinderWrapperCompatible laws declaration)
    {left right : Pattern} (forward : WrapperForward laws left right) :
    ofPattern declaration left = ofPattern declaration right := by
  induction forward with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step.binderHead_eq compatible)

private theorem wrapperNormal_unary (label : String) (payload : Pattern) :
    wrapperNormal laws (.apply label [payload]) = .apply label [wrapperNormal laws payload] := by
  rw [wrapperNormal_apply]; rfl

/-- Removing wrappers acts member by member on the declared parallel
composition. -/
theorem parallelLeaves_wrapperNormal (compatible : BinderWrapperCompatible laws declaration)
    (pattern : Pattern) :
    parallelLeaves declaration (wrapperNormal laws pattern) =
      (parallelLeaves declaration pattern).map (wrapperNormal laws) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [wrapperNormal_bvar, parallelLeaves]
  | hfvar name => simp [wrapperNormal_fvar, parallelLeaves]
  | hlambda binder body ih => simp [wrapperNormal_lambda, parallelLeaves]
  | hmultiLambda arity binders body ih => simp [wrapperNormal_multiLambda, parallelLeaves]
  | hsubst body value ihBody ihValue => simp [wrapperNormal_subst, parallelLeaves]
  | happly label arguments ih =>
    cases arguments with
    | nil =>
      by_cases unit : label = declaration.parallelUnitConstructor <;>
        simp [parallelLeaves, unit, wrapperNormal_apply]
    | cons argument arguments => simp [parallelLeaves, wrapperNormal_apply]
  | hcollection kind elements rest ih =>
    have plain : parallelLeaves declaration (.collection kind (elements.map (wrapperNormal laws)) rest) =
        (parallelLeaves declaration (.collection kind elements rest)).map (wrapperNormal laws) := by
      by_cases parallel : kind = declaration.parallelCollection ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := parallel
        simp only [parallelLeaves, if_true, parallelLeavesList_eq_flatMap, List.flatMap_map,
          List.map_flatMap]
        exact List.flatMap_congr fun element member => ih element member
      · have same : wrapperNormal laws (.collection kind elements rest) =
            .collection kind (elements.map (wrapperNormal laws)) rest ∨
            ∃ law, lawFor laws kind = some law := by
          cases found : lawFor laws kind with
          | none => exact .inl (wrapperNormal_plain found _ _)
          | some law => exact .inr ⟨law, rfl⟩
        cases rest with
        | some rest =>
          simp only [parallelLeaves, List.map_cons, List.map_nil, List.cons.injEq, and_true]
          cases found : lawFor laws kind with
          | none => rw [wrapperNormal_plain found]
          | some law => rw [wrapperNormal_law found]; simp [wrapFinish]
        | none =>
          have notParallel : kind ≠ declaration.parallelCollection := fun h => parallel ⟨h, rfl⟩
          have noLaw : lawFor laws kind = none := by
            cases found : lawFor laws kind with
            | none => rfl
            | some law => exact absurd (compatible found).1 notParallel
          simp [parallelLeaves, notParallel, wrapperNormal_plain noLaw]
    cases found : lawFor laws kind with
    | none => rw [wrapperNormal_plain found]; exact plain
    | some law =>
      obtain ⟨parallel, unitLabel⟩ := compatible found
      subst parallel
      rw [wrapperNormal_law found]
      cases rest with
      | some rest => simpa [wrapFinish] using plain
      | none =>
        match elements, ih, plain with
        | [], _, _ =>
          cases unit : law.unit with
          | none => simp [wrapFinish, unit, parallelLeaves, parallelLeavesList]
          | some label =>
            rw [unitLabel unit] at unit
            simp [wrapFinish, unit, parallelLeaves, parallelLeavesList]
        | [element], ih, _ =>
          simp only [wrapFinish, List.map_cons, List.map_nil]
          rw [ih element (by simp)]
          simp [parallelLeaves, parallelLeavesList]
        | first :: second :: more, _, plain =>
          simpa [wrapFinish] using plain

private theorem exposedDrop?_wrapperNormal (compatible : BinderWrapperCompatible laws declaration)
    (pattern : Pattern) :
    exposedDrop? declaration (wrapperNormal laws pattern) =
      (exposedDrop? declaration pattern).map (wrapperNormal laws) := by
  have leaves := parallelLeaves_wrapperNormal compatible pattern
  cases exposed : exposedDrop? declaration pattern with
  | some name =>
    have shaped := ReflectiveCoherent.exposedDrop?_eq_some_iff.mp exposed
    rw [shaped] at leaves
    simp only [List.map_cons, List.map_nil, wrapperNormal_unary] at leaves
    exact ReflectiveCoherent.exposedDrop?_eq_some_iff.mpr leaves
  | none =>
    cases normalExposed : exposedDrop? declaration (wrapperNormal laws pattern) with
    | none => rfl
    | some name =>
      exfalso
      have shaped := ReflectiveCoherent.exposedDrop?_eq_some_iff.mp normalExposed
      rw [leaves] at shaped
      obtain ⟨member, memberLeaves, memberNormal⟩ := List.map_eq_singleton_iff.mp shaped
      have memberShape : ∃ argument, member = .apply declaration.dropConstructor [argument] := by
        cases member with
        | apply label arguments =>
          rw [wrapperNormal_apply] at memberNormal
          simp only [Pattern.apply.injEq, List.map_eq_singleton_iff] at memberNormal
          obtain ⟨rfl, argument, rfl, _⟩ := memberNormal
          exact ⟨argument, rfl⟩
        | collection kind elements rest =>
          exfalso
          have member' := ReflectiveCoherent.isMember_of_mem_parallelLeaves
            (declaration := declaration) (pattern := pattern) (by rw [memberLeaves]; exact List.mem_singleton_self _)
          cases found : lawFor laws kind with
          | none => rw [wrapperNormal_plain found] at memberNormal; cases memberNormal
          | some law =>
            obtain ⟨parallel, _⟩ := compatible found
            subst parallel
            rw [wrapperNormal_law found] at memberNormal
            unfold wrapFinish at memberNormal
            split at memberNormal
            · exact member'.2 _ rfl
            · exact member'.2 _ rfl
            · cases memberNormal
        | bvar index => rw [wrapperNormal_bvar] at memberNormal; cases memberNormal
        | fvar label => rw [wrapperNormal_fvar] at memberNormal; cases memberNormal
        | lambda binder body => rw [wrapperNormal_lambda] at memberNormal; cases memberNormal
        | multiLambda arity binders body => rw [wrapperNormal_multiLambda] at memberNormal; cases memberNormal
        | subst body value => rw [wrapperNormal_subst] at memberNormal; cases memberNormal
      obtain ⟨argument, rfl⟩ := memberShape
      have back := ReflectiveCoherent.exposedDrop?_eq_some_iff.mpr memberLeaves
      rw [exposed] at back
      cases back

/-- **Resolution commutes with removing wrappers** of the declared parallel
composition. -/
theorem resolveQuotes_wrapperNormal (compatible : BinderWrapperCompatible laws declaration)
    (pattern : Pattern) :
    resolveQuotes declaration (wrapperNormal laws pattern) =
      wrapperNormal laws (resolveQuotes declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [wrapperNormal_bvar, resolveQuotes]
  | hfvar name => simp [wrapperNormal_fvar, resolveQuotes]
  | hlambda binder body ih =>
    rw [wrapperNormal_lambda]; simp only [resolveQuotes]; rw [ih, wrapperNormal_lambda]
  | hmultiLambda arity binders body ih =>
    rw [wrapperNormal_multiLambda]; simp only [resolveQuotes]; rw [ih, wrapperNormal_multiLambda]
  | hsubst body value ihBody ihValue =>
    rw [wrapperNormal_subst]; simp only [resolveQuotes]; rw [ihBody, ihValue, wrapperNormal_subst]
  | hcollection kind elements rest ih =>
    have mapped : (elements.map (wrapperNormal laws)).map (resolveQuotes declaration) =
        (elements.map (resolveQuotes declaration)).map (wrapperNormal laws) := by
      simp only [List.map_map]
      exact List.map_congr_left fun p m => ih p m
    cases found : lawFor laws kind with
    | none =>
      rw [wrapperNormal_plain found]
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      rw [mapped, wrapperNormal_plain found]
    | some law =>
      rw [wrapperNormal_law found]
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      rw [wrapperNormal_law found]
      cases rest with
      | some rest => simp [wrapFinish, resolveQuotes, resolveQuotesList_eq_map, mapped]
      | none =>
        match elements, ih, mapped with
        | [], _, _ =>
          cases unit : law.unit with
          | none => simp [wrapFinish, unit, resolveQuotes, resolveQuotesList]
          | some label => simp [wrapFinish, unit, resolveQuotes, resolveQuotesList, finishResolveApply]
        | [element], ih, _ =>
          simp only [wrapFinish, List.map_cons, List.map_nil]
          exact ih element (by simp)
        | first :: second :: more, _, mapped =>
          simp only [wrapFinish, List.map_cons, resolveQuotes, resolveQuotesList_eq_map]
          simp only [List.map_cons] at mapped
          rw [mapped]
  | happly label arguments ih =>
    have mapped : (arguments.map (wrapperNormal laws)).map (resolveQuotes declaration) =
        (arguments.map (resolveQuotes declaration)).map (wrapperNormal laws) := by
      simp only [List.map_map]
      exact List.map_congr_left fun p m => ih p m
    rw [wrapperNormal_apply]
    simp only [resolveQuotes, resolveQuotesList_eq_map]
    rw [mapped]
    generalize arguments.map (resolveQuotes declaration) = resolved
    match resolved with
    | [] => simp [finishResolveApply, wrapperNormal_apply]
    | first :: second :: more => simp [finishResolveApply, wrapperNormal_apply]
    | [payload] =>
      simp only [List.map_cons, List.map_nil, finishResolveApply]
      split
      · rename_i quoted
        rw [exposedDrop?_wrapperNormal compatible]
        cases exposedDrop? declaration payload with
        | some name => rfl
        | none => simp [wrapperNormal_apply]
      · simp [wrapperNormal_apply]

/-- Structural elimination maps removal of wrappers in the body and a
forward chain of the received process to a forward chain. -/
private theorem substituteResolved_wrapper (compatible : BinderWrapperCompatible laws declaration)
    {process process' : Pattern} (forwardProcess : QWForward laws declaration process process') :
    ∀ (body : Pattern) (depth : Nat), QWForward laws declaration
      (substituteResolved declaration (fun level index => Substitution.instantiateBVarAt level
        (.apply declaration.quoteConstructor [process]) (.bvar index)) depth body)
      (substituteResolved declaration (fun level index => Substitution.instantiateBVarAt level
        (.apply declaration.quoteConstructor [process']) (.bvar index)) depth (wrapperNormal laws body)) := by
  have liftedReplacement : ∀ depth, QWForward laws declaration
      (Substitution.liftBVars 0 depth (.apply declaration.quoteConstructor [process]))
      (Substitution.liftBVars 0 depth (.apply declaration.quoteConstructor [process'])) := fun depth =>
    QWForward.liftBVars (qwForward_apply _ (.cons forwardProcess .nil)) 0 depth
  have atIndex : ∀ depth index, QWForward laws declaration
      (Substitution.instantiateBVarAt depth (.apply declaration.quoteConstructor [process]) (.bvar index))
      (Substitution.instantiateBVarAt depth (.apply declaration.quoteConstructor [process']) (.bvar index)) := by
    intro depth index
    unfold Substitution.instantiateBVarAt
    split
    · exact .refl
    · split
      · exact liftedReplacement depth
      · exact .refl
  have lifted : ∀ depth (inner : Pattern), Substitution.instantiateBVarAt depth
      (.apply declaration.quoteConstructor [inner]) (.bvar depth) =
      .apply declaration.quoteConstructor [Substitution.liftBVars 0 depth inner] := by
    intro depth inner
    simp [Substitution.instantiateBVarAt, Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
  have received : ∀ depth (constructor : String), QWForward laws declaration
      (receive declaration constructor (Substitution.instantiateBVarAt depth
        (.apply declaration.quoteConstructor [process]) (.bvar depth)))
      (receive declaration constructor (Substitution.instantiateBVarAt depth
        (.apply declaration.quoteConstructor [process']) (.bvar depth))) := by
    intro depth constructor
    rw [lifted, lifted]
    simp only [receive, if_true]
    exact QWForward.liftBVars forwardProcess 0 _
  intro body
  induction body using Pattern.inductionOn with
  | hbvar index => intro depth; rw [wrapperNormal_bvar]; exact atIndex depth index
  | hfvar name => intro depth; rw [wrapperNormal_fvar]; exact .refl
  | hlambda binder body ih =>
    intro depth; rw [wrapperNormal_lambda]; simp only [substituteResolved]
    exact qwForward_lambda _ (ih _)
  | hmultiLambda arity binders body ih =>
    intro depth; rw [wrapperNormal_multiLambda]; simp only [substituteResolved]
    exact qwForward_multiLambda _ _ (ih _)
  | hsubst body value ihBody ihValue =>
    intro depth; rw [wrapperNormal_subst]; simp only [substituteResolved]
    exact qwForward_subst (ihBody _) (ihValue _)
  | happly label arguments ih =>
    intro depth
    rw [wrapperNormal_apply]
    match arguments, ih with
    | [], _ => exact .refl
    | first :: second :: more, ih =>
      simp only [List.map_cons, substituteResolved, substituteResolvedList_eq_map]
      apply qwForward_apply
      refine .cons (ih first (by simp) depth) (.cons (ih second (by simp) depth) ?_)
      rw [List.map_map]
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact List.forall₂_same.mpr fun item member => ih item (by simp [member]) depth
    | [payload], ih =>
      simp only [List.map_cons, List.map_nil, substituteResolved]
      have decision : matchesBinder declaration depth payload =
          matchesBinder declaration depth (wrapperNormal laws payload) := by
        simp only [matchesBinder,
          WrapperForward.binderHead_eq compatible (to_wrapperNormal payload)]
      by_cases quoted : label = declaration.quoteConstructor
      · simp only [quoted, if_true]
        exact QWForward.ofWrapper (wrapperForward_apply _ (.cons (to_wrapperNormal payload) .nil))
      · by_cases dropped : label = declaration.dropConstructor
        · have notQuote : ¬ declaration.dropConstructor = declaration.quoteConstructor :=
            fun same => quoted (dropped.trans same)
          subst dropped
          by_cases hit : matchesBinder declaration depth payload = true
          · have hit' : matchesBinder declaration depth (wrapperNormal laws payload) = true := decision ▸ hit
            simp only [notQuote, if_false, if_true, hit, hit']
            exact received depth _
          · have hit' : ¬ matchesBinder declaration depth (wrapperNormal laws payload) = true := decision ▸ hit
            simp only [notQuote, if_false, if_true, hit, hit', Bool.false_eq_true]
            exact qwForward_apply _ (.cons (ih payload (by simp) depth) .nil)
        · simp only [quoted, dropped, if_false]
          exact qwForward_apply _ (.cons (ih payload (by simp) depth) .nil)
  | hcollection kind elements rest ih =>
    intro depth
    have mapped : QWForward laws declaration
        (.collection kind (elements.map (substituteResolved declaration (fun level index =>
          Substitution.instantiateBVarAt level (.apply declaration.quoteConstructor [process]) (.bvar index))
          depth)) rest)
        (.collection kind ((elements.map (wrapperNormal laws)).map (substituteResolved declaration
          (fun level index => Substitution.instantiateBVarAt level
            (.apply declaration.quoteConstructor [process']) (.bvar index)) depth)) rest) := by
      apply qwForward_collection
      rw [List.map_map]
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact List.forall₂_same.mpr fun item member => ih item member depth
    simp only [substituteResolved, substituteResolvedList_eq_map]
    cases found : lawFor laws kind with
    | none =>
      rw [wrapperNormal_plain found]
      simpa only [substituteResolved, substituteResolvedList_eq_map] using mapped
    | some law =>
      rw [wrapperNormal_law found]
      unfold wrapFinish
      split
      · rename_i item same
        obtain ⟨element, rfl, rfl⟩ : ∃ element, elements = [element] ∧ item = wrapperNormal laws element := by
          match elements, same with
          | [element], same => exact ⟨element, rfl, by simpa using same.symm⟩
        simp only [List.map_cons, List.map_nil] at mapped ⊢
        exact (ReflTransGen.single (.inr (.singleton found))).trans (ih element (by simp) depth)
      · rename_i same
        have empty : elements = [] := by simpa using same
        subst empty
        split
        · rename_i label unit
          simp only [List.map_nil, substituteResolved]
          exact .single (.inr (.empty found unit))
        · simp only [List.map_nil, substituteResolved, substituteResolvedList]
          exact .refl
      · simpa only [substituteResolved, substituteResolvedList_eq_map] using mapped

open ReflectiveInstantiation in
/-- **Reflective binder elimination maps the wrapper normal form of its body and a forward chain of its
quoted replacement to a forward chain**, when the original result is inScope. -/
theorem instantiate_wrapper (compatible : BinderWrapperCompatible laws declaration)
    {process process' : Pattern} (forwardProcess : QWForward laws declaration process process') (body : Pattern) :
    ∀ depth, (instantiate declaration depth (.apply declaration.quoteConstructor [process]) body).isWellScopedAt depth →
      QWForward laws declaration (instantiate declaration depth (.apply declaration.quoteConstructor [process]) body)
        (instantiate declaration depth (.apply declaration.quoteConstructor [process']) (wrapperNormal laws body)) := by
  intro depth _
  unfold instantiate
  rw [resolveQuotes_wrapperNormal compatible]
  exact substituteResolved_wrapper compatible forwardProcess _ depth

/-- **The reflective binder operation of a closed quote scope maps the wrapper normal form of its body
and a forward chain of its quoted replacement to a forward chain**, when the original result is closed. -/
theorem reflectiveOperation_wrapper (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (closedScope : declaration.quoteScope = .closed)
    (compatible : BinderWrapperCompatible laws declaration)
    {payload payload' : Pattern} (forwardPayload : QWForward laws declaration payload payload') (body : Pattern)
    (inScope : (ScopedRuleInstantiation.reflectiveOperation declaration (.apply declaration.quoteConstructor [payload])
      body).isWellScopedAt 0 = true) :
    QWForward laws declaration
      (ScopedRuleInstantiation.reflectiveOperation declaration (.apply declaration.quoteConstructor [payload]) body)
      (ScopedRuleInstantiation.reflectiveOperation declaration (.apply declaration.quoteConstructor [payload'])
        (wrapperNormal laws body)) := by
  unfold ScopedRuleInstantiation.reflectiveOperation at inScope ⊢
  simp only [normalizeReflectiveReplacement, beq_self_eq_true, if_true,
    ReflectiveInstantiation.instantiateDeclared_of_closed closedScope] at inScope ⊢
  exact instantiate_wrapper compatible (normal_qwForward_of_qwForward distinct forwardPayload) body 0 inScope

/-! ## Typing along forward chains -/

/-- **A forward chain of quote-drop and wrapper steps keeps well-sortedness** at a type without
collections of a flattening kind. -/
theorem QWForward.openPatternWellSorted {language : LanguageDef} {free : FreeTypeContext}
    (typedPresentation : QuoteDropTyped language declaration) (admission : WrappersTyped laws language)
    {left right : Pattern} (forward : QWForward laws declaration left right) {bound : List TypeExpr} {type : TypeExpr}
    (noLaw : NoLawCollections laws type) (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  induction forward with
  | refl => exact sorted
  | tail _ step ih =>
    rcases step with quoteDrop | wrapped
    · exact quoteDrop.openPatternWellSorted typedPresentation ih
    · exact wrapped.openPatternWellSorted admission noLaw ih

end Mettapedia.OSLF.MeTTaIL.Wrappers
