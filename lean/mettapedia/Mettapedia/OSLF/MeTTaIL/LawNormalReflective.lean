import Mettapedia.OSLF.MeTTaIL.LawNormalInstantiation
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

/-!
# Reflective substitution respects the collection laws

A law move rearranges a collection's elements; it never changes a constructor application, a
binder or an index. Hence law-equal terms have the same shape above their collections
(`LawSame.apply_inv`, `LawSame.bvar_inv`), the quote-drop normal form maps law-equal terms to
law-equal terms (`normalizeReflective_lawSame`). Reflective binder elimination also
respects the laws when the collection laws preserve its whole-name test
(`BinderLawCompatible`, `binderOperation_lawSame`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws ReflectiveSubstitution

variable {laws : List Laws}

/-! ## Law-equal terms have the same shape above their collections -/

theorem forall₂_lawSame_refl (items : List Pattern) : List.Forall₂ (LawSame laws) items items :=
  List.forall₂_same.mpr fun _ _ => .refl _

theorem forall₂_lawSame_symm : ∀ {left right : List Pattern}, List.Forall₂ (LawSame laws) left right →
    List.Forall₂ (LawSame laws) right left
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => .cons (.symm _ _ head) (forall₂_lawSame_symm tail)

theorem forall₂_lawSame_trans : ∀ {first second third : List Pattern}, List.Forall₂ (LawSame laws) first second →
    List.Forall₂ (LawSame laws) second third → List.Forall₂ (LawSame laws) first third
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons head tail, .cons head' tail' =>
    .cons (.trans _ _ _ head head') (forall₂_lawSame_trans tail tail')

theorem LawStep.apply_inv {label : String} {arguments : List Pattern} {other : Pattern}
    (step : LawStep laws (.apply label arguments) other) :
    ∃ arguments', other = .apply label arguments' ∧ List.Forall₂ (LawSame laws) arguments arguments' := by
  cases step with
  | apply inner =>
    exact ⟨_, rfl, List.rel_append (forall₂_lawSame_refl _) (.cons (.rel _ _ inner) (forall₂_lawSame_refl _))⟩

theorem LawStep.apply_inv' {label : String} {arguments : List Pattern} {other : Pattern}
    (step : LawStep laws other (.apply label arguments)) :
    ∃ arguments', other = .apply label arguments' ∧ List.Forall₂ (LawSame laws) arguments arguments' := by
  cases step with
  | apply inner =>
    exact ⟨_, rfl, List.rel_append (forall₂_lawSame_refl _) (.cons (.symm _ _ (.rel _ _ inner)) (forall₂_lawSame_refl _))⟩

/-- **Law-equal terms agree on a constructor application**, with pointwise law-equal arguments. -/
theorem LawSame.apply_inv {label : String} {arguments : List Pattern} {other : Pattern}
    (same : LawSame laws (.apply label arguments) other) :
    ∃ arguments', other = .apply label arguments' ∧ List.Forall₂ (LawSame laws) arguments arguments' := by
  have chain : Relation.ReflTransGen (Relation.SymmGen (LawStep laws)) (.apply label arguments) other := by
    rw [Relation.EqvGen.reflTransGen_symmGen]; exact same
  clear same
  induction chain with
  | refl => exact ⟨arguments, rfl, forall₂_lawSame_refl _⟩
  | tail _ step ih =>
    obtain ⟨middle, rfl, toMiddle⟩ := ih
    rcases step with forward | backward
    · obtain ⟨next, rfl, toNext⟩ := forward.apply_inv
      exact ⟨next, rfl, forall₂_lawSame_trans toMiddle toNext⟩
    · obtain ⟨next, rfl, toNext⟩ := backward.apply_inv'
      exact ⟨next, rfl, forall₂_lawSame_trans toMiddle toNext⟩

/-- Law-equal terms agree on an index. -/
theorem LawSame.bvar_inv {index : Nat} {other : Pattern} (same : LawSame laws (.bvar index) other) :
    other = .bvar index := by
  have chain : Relation.ReflTransGen (Relation.SymmGen (LawStep laws)) (.bvar index) other := by
    rw [Relation.EqvGen.reflTransGen_symmGen]; exact same
  clear same
  induction chain with
  | refl => rfl
  | tail _ step ih =>
    subst ih
    rcases step with forward | backward
    · cases forward
    · cases backward

/-! ## The quote-drop normal form -/

theorem normalizeReflectiveList_map (declaration : ReflectivePresentationDecl) :
    ∀ items : List Pattern, normalizeReflectiveList declaration items = items.map (normalizeReflective declaration)
  | [] => by rw [normalizeReflectiveList]; rfl
  | item :: rest => by rw [normalizeReflectiveList, normalizeReflectiveList_map declaration rest]; rfl

theorem finish_nil (declaration : ReflectivePresentationDecl) (label : String) :
    finishNormalizeReflectiveApply declaration label [] = .apply label [] := by
  unfold finishNormalizeReflectiveApply; split <;> rfl

theorem finish_long (declaration : ReflectivePresentationDecl) (label : String) (first second : Pattern)
    (rest : List Pattern) :
    finishNormalizeReflectiveApply declaration label (first :: second :: rest) = .apply label (first :: second :: rest) := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · rename_i same; simp at same
    · rfl
  · rfl

theorem finish_plain (declaration : ReflectivePresentationDecl) (label : String) {first : Pattern}
    (notShaped : ¬ ∃ drop name, first = .apply drop [name]) :
    finishNormalizeReflectiveApply declaration label [first] = .apply label [first] := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · rename_i drop name same
      simp only [List.cons.injEq, and_true] at same
      exact absurd ⟨drop, name, same⟩ notShaped
    · rfl
  · rfl

theorem finish_drop (declaration : ReflectivePresentationDecl) (label drop : String) (name : Pattern) :
    finishNormalizeReflectiveApply declaration label [.apply drop [name]] =
      if label == declaration.quoteConstructor && drop == declaration.dropConstructor then name
      else .apply label [.apply drop [name]] := by
  unfold finishNormalizeReflectiveApply
  by_cases quote : label == declaration.quoteConstructor <;> by_cases dropped : drop == declaration.dropConstructor <;>
    simp [quote, dropped]

/-- The quote-drop step at a constructor maps pointwise law-equal arguments to law-equal results. -/
theorem finishNormalizeReflectiveApply_lawSame (declaration : ReflectivePresentationDecl) (label : String)
    {arguments arguments' : List Pattern} (pointwise : List.Forall₂ (LawSame laws) arguments arguments') :
    LawSame laws (finishNormalizeReflectiveApply declaration label arguments)
      (finishNormalizeReflectiveApply declaration label arguments') := by
  cases pointwise with
  | nil => rw [finish_nil]; exact .refl _
  | @cons first first' rest rest' head tail =>
    cases tail with
    | @cons second second' more more' secondSame moreSame =>
      rw [finish_long, finish_long]
      exact lawSame_apply_congr _ (.cons head (.cons secondSame moreSame))
    | nil =>
      by_cases shaped : ∃ drop name, first = .apply drop [name]
      · obtain ⟨drop, name, rfl⟩ := shaped
        obtain ⟨arguments'', rfl, inner⟩ := head.apply_inv
        cases inner with
        | cons nameSame rest =>
          cases rest
          rw [finish_drop, finish_drop]
          split
          · exact nameSame
          · exact lawSame_apply_congr _ (.cons (lawSame_apply_congr _ (.cons nameSame .nil)) .nil)
      · have notShaped' : ¬ ∃ drop name, first' = .apply drop [name] := by
          rintro ⟨drop, name, rfl⟩
          obtain ⟨arguments'', rfl, inner⟩ := LawSame.apply_inv (Relation.EqvGen.symm _ _ head)
          cases inner with
          | cons _ rest => cases rest; exact shaped ⟨drop, _, rfl⟩
        rw [finish_plain declaration label shaped, finish_plain declaration label notShaped']
        exact lawSame_apply_congr _ (.cons head .nil)

/-- **The quote-drop normal form maps a law move to law-equal terms.** -/
theorem LawStep.normalizeReflective (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (step : LawStep laws left right) :
    LawSame laws (ReflectiveSubstitution.normalizeReflective declaration left)
      (ReflectiveSubstitution.normalizeReflective declaration right) := by
  induction step with
  | permute unordered permutation =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map]
    exact .rel _ _ (.permute unordered (permutation.map _))
  | members same =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map]
    exact .rel _ _ (.members (members_map same _))
  | flatten found =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map, List.map_append, List.map_cons]
    exact .rel _ _ (.flatten found)
  | @unit kind law label before after rest found unit =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map, List.map_append, List.map_cons,
      List.map_nil]
    rw [finish_nil]
    exact .rel _ _ (.unit found unit)
  | apply _ ih =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map, List.map_append, List.map_cons]
    exact finishNormalizeReflectiveApply_lawSame declaration _
      (List.rel_append (forall₂_lawSame_refl _) (.cons ih (forall₂_lawSame_refl _)))
  | lambda _ ih => simp only [ReflectiveSubstitution.normalizeReflective]; exact lawSame_lambda_congr _ ih
  | multiLambda _ ih => simp only [ReflectiveSubstitution.normalizeReflective]; exact lawSame_multiLambda_congr _ _ ih
  | substBody _ ih =>
    simp only [ReflectiveSubstitution.normalizeReflective]; exact lawSame_subst_congr ih (.refl _)
  | substReplacement _ ih =>
    simp only [ReflectiveSubstitution.normalizeReflective]; exact lawSame_subst_congr (.refl _) ih
  | element _ ih =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map, List.map_append, List.map_cons]
    exact lawSame_collection_congr _ _ (List.rel_append (forall₂_lawSame_refl _) (.cons ih (forall₂_lawSame_refl _)))

theorem normalizeReflective_lawSame (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (same : LawSame laws left right) :
    LawSame laws (ReflectiveSubstitution.normalizeReflective declaration left)
      (ReflectiveSubstitution.normalizeReflective declaration right) := by
  induction same with
  | rel _ _ step => exact step.normalizeReflective declaration
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-! ## Reflective binder elimination -/

open ReflectiveInstantiation in
/-- The drop case of reflective elimination: activate a substituted quote. -/
def dropResult (declaration : ReflectivePresentationDecl) (constructor : String) (name : Pattern) (matched : Bool) :
    Pattern :=
  match name, matched with
  | .apply quote [process], true => if quote == declaration.quoteConstructor then process else .apply constructor [name]
  | _, _ => .apply constructor [name]

open ReflectiveInstantiation in
theorem instantiateList_map' (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement : Pattern) :
    ∀ items : List Pattern, instantiateList declaration depth replacement items =
      items.map (instantiate declaration depth replacement)
  | _ => rfl

theorem dropResult_shaped (declaration : ReflectivePresentationDecl) (constructor quote : String) (process : Pattern) :
    dropResult declaration constructor (.apply quote [process]) true =
      if quote == declaration.quoteConstructor then process else .apply constructor [.apply quote [process]] := rfl

theorem dropResult_plain (declaration : ReflectivePresentationDecl) (constructor : String) {name : Pattern} {matched : Bool}
    (plain : (¬ ∃ quote process, name = .apply quote [process]) ∨ matched = false) :
    dropResult declaration constructor name matched = .apply constructor [name] := by
  unfold dropResult
  split
  · rename_i quote process
    rcases plain with notShaped | unmatched
    · exact absurd ⟨quote, process, rfl⟩ notShaped
    · cases unmatched
  · rfl

theorem dropResult_lawSame (declaration : ReflectivePresentationDecl) (constructor : String) {name name' : Pattern}
    (matched : Bool) (same : LawSame laws name name') :
    LawSame laws (dropResult declaration constructor name matched) (dropResult declaration constructor name' matched) := by
  cases matched with
  | false =>
    rw [dropResult_plain declaration constructor (.inr rfl), dropResult_plain declaration constructor (.inr rfl)]
    exact lawSame_apply_congr _ (.cons same .nil)
  | true =>
    by_cases shaped : ∃ quote process, name = .apply quote [process]
    · obtain ⟨quote, process, rfl⟩ := shaped
      obtain ⟨arguments, rfl, inner⟩ := same.apply_inv
      cases inner with
      | cons processSame rest =>
        cases rest
        rw [dropResult_shaped, dropResult_shaped]
        split
        · exact processSame
        · exact lawSame_apply_congr _ (.cons same .nil)
    · have shaped' : ¬ ∃ quote process, name' = .apply quote [process] := by
        rintro ⟨quote, process, rfl⟩
        obtain ⟨arguments, rfl, inner⟩ := LawSame.apply_inv (Relation.EqvGen.symm _ _ same)
        cases inner with
        | cons _ rest => cases rest; exact shaped ⟨quote, _, rfl⟩
      rw [dropResult_plain declaration constructor (.inl shaped), dropResult_plain declaration constructor (.inl shaped')]
      exact lawSame_apply_congr _ (.cons same .nil)

/-- The chosen collection laws may rearrange or flatten the reflective
parallel bag, but may not delete a different unit or contract multiplicities
as a set. Laws acting only on other collection kinds are unrestricted. -/
structure BinderLawCompatible (laws : List Laws) (declaration : ReflectivePresentationDecl) : Prop where
  notSet : declaration.parallelCollection ≠ .hashSet
  unit_eq : ∀ {law label}, lawFor laws declaration.parallelCollection = some law →
    law.unit = some label → label = declaration.parallelUnitConstructor

/-- Check only the presentation selected by the real rule; an ordinary
binder has no reflective collection dependency. -/
def BinderLawsFor (laws : List Laws) (profile : Reflection.ReflectionProfile) (rule : RewriteRule) : Prop :=
  ∀ declaration, substitutionPresentationForRule? profile rule = some declaration →
    BinderLawCompatible laws declaration

def checkBinderLawsFor (laws : List Laws) (profile : Reflection.ReflectionProfile) (rule : RewriteRule) : Bool :=
  match substitutionPresentationForRule? profile rule with
  | none => true
  | some declaration =>
      decide (declaration.parallelCollection ≠ .hashSet) &&
      match (lawFor laws declaration.parallelCollection).bind Laws.unit with
      | none => true
      | some label => label == declaration.parallelUnitConstructor

theorem checkBinderLawsFor_iff (laws : List Laws) (profile : Reflection.ReflectionProfile) (rule : RewriteRule) :
    checkBinderLawsFor laws profile rule = true ↔ BinderLawsFor laws profile rule := by
  unfold checkBinderLawsFor BinderLawsFor
  split
  · rename_i missing
    simp [missing]
  · rename_i declaration selected
    simp only [selected, Option.some.injEq, forall_eq', Bool.and_eq_true, decide_eq_true_eq]
    cases found : lawFor laws declaration.parallelCollection with
    | none =>
      simp only [Option.bind_none, and_true]
      exact ⟨fun notSet => ⟨notSet, by simp [found]⟩, fun compatible => compatible.notSet⟩
    | some law =>
      cases unit : law.unit with
      | none =>
        simp only [Option.bind_some, unit, and_true]
        refine ⟨fun notSet => ⟨notSet, ?_⟩, fun compatible => compatible.notSet⟩
        intro other label otherLaw otherUnit
        have equal := Option.some.inj (found.symm.trans otherLaw)
        subst other
        rw [unit] at otherUnit
        cases otherUnit
      | some label =>
        simp only [Option.bind_some, unit, beq_iff_eq]
        refine ⟨fun ⟨notSet, labelEq⟩ => ⟨notSet, ?_⟩,
          fun compatible => ⟨compatible.notSet, compatible.unit_eq found unit⟩⟩
        intro other name otherLaw otherUnit
        rw [found, Option.some.injEq] at otherLaw
        subst other
        exact (Option.some.inj (otherUnit.symm.trans unit)).trans labelEq

open BinderHead in
/-- Authorized collection moves cannot change the structural binder head. -/
theorem LawStep.binderHead_eq {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) {left right : Pattern}
    (step : LawStep laws left right) :
    ofPattern declaration left = ofPattern declaration right := by
  induction step with
  | @permute kind elements permuted rest _ permutation =>
    cases rest with
    | some rest => rfl
    | none =>
      by_cases parallel : kind = declaration.parallelCollection
      · simp only [ofPattern, parallel, if_true, ofList_eq_map]
        exact fold_perm (permutation.map _)
      · simp [ofPattern, parallel]
  | @members elements others rest _ =>
    cases rest with
    | some rest => rfl
    | none => simp [ofPattern, Ne.symm compatible.notSet]
  | @flatten kind law before inner after rest _ =>
    cases rest with
    | some rest => rfl
    | none =>
      by_cases parallel : kind = declaration.parallelCollection
      · simp only [ofPattern, parallel, if_true, ofList_eq_map, List.map_append,
          List.map_cons, List.foldr_cons, fold_append, join_assoc]
      · simp [ofPattern, parallel]
  | @unit kind law label before after rest found unit =>
    cases rest with
    | some rest => rfl
    | none =>
      by_cases parallel : kind = declaration.parallelCollection
      · subst kind
        have unitLabel := compatible.unit_eq found unit
        simp [ofPattern, ofList_eq_map, BinderHead.apply, rigid, unitLabel]
      · simp [ofPattern, parallel]
  | apply inner ih => simp [ofPattern, ofList_eq_map, ih]
  | lambda inner ih => rfl
  | multiLambda inner ih => rfl
  | substBody inner ih => rfl
  | substReplacement inner ih => rfl
  | @element kind before after element changed rest inner ih =>
    cases rest with
    | some rest => rfl
    | none => simp [ofPattern, ofList_eq_map, ih]

theorem LawSame.binderHead_eq {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) {left right : Pattern}
    (same : LawSame laws left right) :
    BinderHead.ofPattern declaration left = BinderHead.ofPattern declaration right := by
  induction same with
  | rel _ _ step => exact step.binderHead_eq compatible
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

open BinderHead in
/-- On the raw carrier the compatibility condition is exact. Repeating a
single index separates a set from a parallel bag; inserting a conflicting
unit beside that index separates the two notions of unit. -/
theorem binderLawCompatible_iff (laws : List Laws) (declaration : ReflectivePresentationDecl) :
    BinderLawCompatible laws declaration ↔
      ∀ {left right}, LawStep laws left right →
        ofPattern declaration left = ofPattern declaration right := by
  refine ⟨fun compatible {_ _} step => step.binderHead_eq compatible, ?_⟩
  intro preserves
  constructor
  · intro parallel
    have repeated : LawStep laws (.collection .hashSet [.bvar 0, .bvar 0] none)
        (.collection .hashSet [.bvar 0] none) := .members (by simp)
    have same := preserves repeated
    simp [ofPattern, ofList, parallel, join] at same
  · intro law label found unit
    by_contra different
    have dropped : LawStep laws
        (.collection declaration.parallelCollection [.apply label [], .bvar 0] none)
        (.collection declaration.parallelCollection [.bvar 0] none) :=
      .unit (before := []) (after := [.bvar 0]) found unit
    have same := preserves dropped
    simp [ofPattern, ofList, BinderHead.apply, rigid, join, different] at same

theorem instantiateBVarAt_lawSame_replacement {replacement replacement' : Pattern}
    (same : LawSame laws replacement replacement') (depth index : Nat) :
    LawSame laws (Substitution.instantiateBVarAt depth replacement (.bvar index))
      (Substitution.instantiateBVarAt depth replacement' (.bvar index)) := by
  unfold Substitution.instantiateBVarAt
  split
  · exact .refl _
  · split
    · exact LawSame.lift (fun step => step.liftBVars 0 depth) same
    · exact .refl _

/-! ### Resolution and structural elimination respect compatible laws -/

open ReflectiveCoherent in
private theorem single_members {declaration : ReflectivePresentationDecl} {left right : Pattern}
    (leftMember : IsMember declaration left) (rightMember : IsMember declaration right)
    (same : LawSame laws left right) :
    ∃ arranged, (parallelLeaves declaration left).Perm arranged ∧
      List.Forall₂ (LawSame laws) arranged (parallelLeaves declaration right) := by
  rw [parallelLeaves_of_isMember leftMember, parallelLeaves_of_isMember rightMember]
  exact ⟨_, .refl _, .cons same .nil⟩

private theorem parallelLeaves_collection {declaration : ReflectivePresentationDecl}
    (elements : List Pattern) :
    parallelLeaves declaration (.collection declaration.parallelCollection elements none) =
      elements.flatMap (parallelLeaves declaration) := by
  simp [parallelLeaves, parallelLeavesList_eq_flatMap]

open ReflectiveCoherent in
/-- A compatible law move changes the members of the declared parallel
composition only by a permutation and law-equal members. -/
theorem LawStep.parallelLeaves {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) {left right : Pattern}
    (step : LawStep laws left right) :
    ∃ arranged, (ReflectiveSubstitution.parallelLeaves declaration left).Perm arranged ∧
      List.Forall₂ (LawSame laws) arranged (ReflectiveSubstitution.parallelLeaves declaration right) := by
  have whole : LawSame laws left right := .rel _ _ step
  induction step with
  | @permute kind elements permuted rest unordered permutation =>
    by_cases parallel : kind = declaration.parallelCollection ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := parallel
      rw [parallelLeaves_collection, parallelLeaves_collection]
      exact ⟨_, permutation.flatMap_right _, forall₂_lawSame_refl _⟩
    · exact single_members ⟨by simp, fun _ same => by injection same with hk _ hr; exact parallel ⟨hk, hr⟩⟩
        ⟨by simp, fun _ same => by injection same with hk _ hr; exact parallel ⟨hk, hr⟩⟩ whole
  | @members elements others rest _ =>
    have different : CollType.hashSet ≠ declaration.parallelCollection := Ne.symm compatible.notSet
    exact single_members ⟨by simp, fun _ same => by injection same with hk; exact different hk⟩
      ⟨by simp, fun _ same => by injection same with hk; exact different hk⟩ whole
  | @flatten kind law before inner after rest found =>
    by_cases parallel : kind = declaration.parallelCollection ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := parallel
      refine ⟨_, List.Perm.of_eq ?_, forall₂_lawSame_refl _⟩
      simp [parallelLeaves_collection, List.flatMap_append]
    · exact single_members ⟨by simp, fun _ same => by injection same with hk _ hr; exact parallel ⟨hk, hr⟩⟩
        ⟨by simp, fun _ same => by injection same with hk _ hr; exact parallel ⟨hk, hr⟩⟩ whole
  | @unit kind law label before after rest found unit =>
    by_cases parallel : kind = declaration.parallelCollection ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := parallel
      have unitLabel := compatible.unit_eq found unit
      subst unitLabel
      refine ⟨_, List.Perm.of_eq ?_, forall₂_lawSame_refl _⟩
      rw [parallelLeaves_collection, parallelLeaves_collection, List.flatMap_append, List.flatMap_cons,
        List.flatMap_append]
      simp [ReflectiveSubstitution.parallelLeaves]
    · exact single_members ⟨by simp, fun _ same => by injection same with hk _ hr; exact parallel ⟨hk, hr⟩⟩
        ⟨by simp, fun _ same => by injection same with hk _ hr; exact parallel ⟨hk, hr⟩⟩ whole
  | @apply label before after argument changed _ _ =>
    exact single_members ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ whole
  | lambda _ _ => exact single_members ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ whole
  | multiLambda _ _ => exact single_members ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ whole
  | substBody _ _ => exact single_members ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ whole
  | substReplacement _ _ => exact single_members ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ whole
  | @element kind before after element changed rest inner ih =>
    by_cases parallel : kind = declaration.parallelCollection ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := parallel
      obtain ⟨arranged, permutation, related⟩ := ih (.rel _ _ inner)
      rw [parallelLeaves_collection, parallelLeaves_collection]
      simp only [List.flatMap_append, List.flatMap_cons]
      exact ⟨_, (permutation.append_right _).append_left _,
        List.rel_append (forall₂_lawSame_refl _) (List.rel_append related (forall₂_lawSame_refl _))⟩
    · exact single_members ⟨by simp, fun _ same => by injection same with hk _ hr; exact parallel ⟨hk, hr⟩⟩
        ⟨by simp, fun _ same => by injection same with hk _ hr; exact parallel ⟨hk, hr⟩⟩ whole

open ReflectiveCoherent in
private theorem exposedDrop?_step {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) {left right : Pattern}
    (step : LawStep laws left right) :
    (exposedDrop? declaration left = none ∧ exposedDrop? declaration right = none) ∨
      ∃ name name', exposedDrop? declaration left = some name ∧
        exposedDrop? declaration right = some name' ∧ LawSame laws name name' := by
  obtain ⟨arranged, permutation, related⟩ := step.parallelLeaves compatible
  cases leftExposed : exposedDrop? declaration left with
  | some name =>
    have leaves := exposedDrop?_eq_some_iff.mp leftExposed
    rw [leaves, List.singleton_perm] at permutation
    subst permutation
    obtain ⟨result, others, same, nilRel, rightLeaves⟩ := List.forall₂_cons_left_iff.mp related
    rw [List.forall₂_nil_left_iff] at nilRel
    subst nilRel
    obtain ⟨arguments, resultEq, inner⟩ := LawSame.apply_inv same
    obtain ⟨name', rest, nameSame, nilRest, argumentsEq⟩ := List.forall₂_cons_left_iff.mp inner
    rw [List.forall₂_nil_left_iff] at nilRest
    subst nilRest argumentsEq resultEq
    exact .inr ⟨name, name', rfl, exposedDrop?_eq_some_iff.mpr rightLeaves, nameSame⟩
  | none =>
    refine .inl ⟨rfl, ?_⟩
    cases rightExposed : exposedDrop? declaration right with
    | none => rfl
    | some name' =>
      exfalso
      have leaves := exposedDrop?_eq_some_iff.mp rightExposed
      rw [leaves] at related
      obtain ⟨member, others, same, nilRel, arrangedEq⟩ := List.forall₂_cons_right_iff.mp related
      rw [List.forall₂_nil_right_iff] at nilRel
      subst nilRel arrangedEq
      obtain ⟨arguments, memberEq, inner⟩ := LawSame.apply_inv (Relation.EqvGen.symm _ _ same)
      obtain ⟨name, rest, _, nilRest, argumentsEq⟩ := List.forall₂_cons_left_iff.mp inner
      rw [List.forall₂_nil_left_iff] at nilRest
      subst nilRest argumentsEq memberEq
      rw [List.perm_singleton] at permutation
      have exposed := exposedDrop?_eq_some_iff.mpr permutation
      rw [leftExposed] at exposed
      cases exposed

open ReflectiveCoherent in
/-- Law-equal terms expose a drop together, with law-equal names. -/
theorem LawSame.exposedDrop?_cases {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) {left right : Pattern}
    (same : LawSame laws left right) :
    (exposedDrop? declaration left = none ∧ exposedDrop? declaration right = none) ∨
      ∃ name name', exposedDrop? declaration left = some name ∧
        exposedDrop? declaration right = some name' ∧ LawSame laws name name' := by
  induction same with
  | rel _ _ step => exact exposedDrop?_step compatible step
  | refl term =>
    cases exposed : exposedDrop? declaration term with
    | none => exact .inl ⟨rfl, rfl⟩
    | some name => exact .inr ⟨name, name, rfl, rfl, .refl _⟩
  | symm _ _ _ ih =>
    rcases ih with ⟨first, second⟩ | ⟨name, name', first, second, same⟩
    · exact .inl ⟨second, first⟩
    · exact .inr ⟨name', name, second, first, .symm _ _ same⟩
  | trans _ _ _ _ _ first second =>
    rcases first with ⟨a, b⟩ | ⟨n, n', a, b, s⟩ <;> rcases second with ⟨c, d⟩ | ⟨m, m', c, d, t⟩
    · exact .inl ⟨a, d⟩
    · rw [b] at c; cases c
    · rw [b] at c; cases c
    · rw [b] at c
      cases c
      exact .inr ⟨n, m', a, d, .trans _ _ _ s t⟩

private theorem finishResolveApply_of_length_ne_one (declaration : ReflectivePresentationDecl)
    (label : String) {arguments : List Pattern} (notOne : arguments.length ≠ 1) :
    finishResolveApply declaration label arguments = .apply label arguments := by
  match arguments, notOne with
  | [], _ => rfl
  | _ :: _ :: _, _ => rfl

/-- **Resolution maps a compatible law move to law-equal results.** -/
theorem LawStep.resolveQuotes {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) {left right : Pattern}
    (step : LawStep laws left right) :
    LawSame laws (ReflectiveSubstitution.resolveQuotes declaration left)
      (ReflectiveSubstitution.resolveQuotes declaration right) := by
  induction step with
  | permute unordered permutation =>
    simp only [ReflectiveSubstitution.resolveQuotes, resolveQuotesList_eq_map]
    exact .rel _ _ (.permute unordered (permutation.map _))
  | members same =>
    simp only [ReflectiveSubstitution.resolveQuotes, resolveQuotesList_eq_map]
    exact .rel _ _ (.members (members_map same _))
  | flatten found =>
    simp only [ReflectiveSubstitution.resolveQuotes, resolveQuotesList_eq_map, List.map_append,
      List.map_cons]
    exact .rel _ _ (.flatten found)
  | unit found unit =>
    simp only [ReflectiveSubstitution.resolveQuotes, resolveQuotesList_eq_map, List.map_append,
      List.map_cons, resolveQuotesList, finishResolveApply]
    exact .rel _ _ (.unit found unit)
  | @apply label before after argument changed inner ih =>
    simp only [ReflectiveSubstitution.resolveQuotes, resolveQuotesList_eq_map, List.map_append,
      List.map_cons]
    by_cases single : before = [] ∧ after = []
    · obtain ⟨rfl, rfl⟩ := single
      simp only [List.map_nil, List.nil_append, finishResolveApply]
      by_cases quoted : label = declaration.quoteConstructor
      · simp only [quoted, if_true]
        rcases LawSame.exposedDrop?_cases compatible ih with ⟨none₁, none₂⟩ | ⟨name, name', some₁, some₂, same⟩
        · rw [none₁, none₂]
          exact lawSame_apply_congr _ (.cons ih .nil)
        · rw [some₁, some₂]
          exact same
      · simp only [quoted, if_false]
        exact lawSame_apply_congr _ (.cons ih .nil)
    · have notOne : (before.map (ReflectiveSubstitution.resolveQuotes declaration) ++
          ReflectiveSubstitution.resolveQuotes declaration argument ::
            after.map (ReflectiveSubstitution.resolveQuotes declaration)).length ≠ 1 := by
        intro one; apply single
        simp only [List.length_append, List.length_map, List.length_cons] at one
        exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
      have notOne' : (before.map (ReflectiveSubstitution.resolveQuotes declaration) ++
          ReflectiveSubstitution.resolveQuotes declaration changed ::
            after.map (ReflectiveSubstitution.resolveQuotes declaration)).length ≠ 1 := by
        simpa using notOne
      rw [finishResolveApply_of_length_ne_one declaration label notOne,
        finishResolveApply_of_length_ne_one declaration label notOne']
      exact lawSame_apply_congr _ (List.rel_append (forall₂_lawSame_refl _) (.cons ih
        (forall₂_lawSame_refl _)))
  | lambda _ ih =>
    simp only [ReflectiveSubstitution.resolveQuotes]; exact lawSame_lambda_congr _ ih
  | multiLambda _ ih =>
    simp only [ReflectiveSubstitution.resolveQuotes]; exact lawSame_multiLambda_congr _ _ ih
  | substBody _ ih =>
    simp only [ReflectiveSubstitution.resolveQuotes]; exact lawSame_subst_congr ih (.refl _)
  | substReplacement _ ih =>
    simp only [ReflectiveSubstitution.resolveQuotes]; exact lawSame_subst_congr (.refl _) ih
  | element _ ih =>
    simp only [ReflectiveSubstitution.resolveQuotes, resolveQuotesList_eq_map, List.map_append,
      List.map_cons]
    exact lawSame_collection_congr _ _ (List.rel_append (forall₂_lawSame_refl _) (.cons ih
      (forall₂_lawSame_refl _)))

private theorem substituteResolved_of_length_ne_one (declaration : ReflectivePresentationDecl)
    (atIndex : Nat → Nat → Pattern) (depth : Nat) (label : String) {arguments : List Pattern}
    (notOne : arguments.length ≠ 1) :
    substituteResolved declaration atIndex depth (.apply label arguments) =
      .apply label (arguments.map (substituteResolved declaration atIndex depth)) := by
  match arguments, notOne with
  | [], _ => rfl
  | _ :: _ :: _, _ => simp [substituteResolved, substituteResolvedList_eq_map]

/-- **Structural elimination maps a compatible law move to law-equal results.** -/
theorem LawStep.substituteResolved {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) (atIndex : Nat → Nat → Pattern)
    {left right : Pattern} (step : LawStep laws left right) :
    ∀ depth, LawSame laws (ReflectiveSubstitution.substituteResolved declaration atIndex depth left)
      (ReflectiveSubstitution.substituteResolved declaration atIndex depth right) := by
  induction step with
  | permute unordered permutation =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved, substituteResolvedList_eq_map]
    exact .rel _ _ (.permute unordered (permutation.map _))
  | members same =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved, substituteResolvedList_eq_map]
    exact .rel _ _ (.members (members_map same _))
  | flatten found =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved, substituteResolvedList_eq_map,
      List.map_append, List.map_cons]
    exact .rel _ _ (.flatten found)
  | unit found unit =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved, substituteResolvedList_eq_map,
      List.map_append, List.map_cons]
    exact .rel _ _ (.unit found unit)
  | @apply label before after argument changed inner ih =>
    intro depth
    by_cases single : before = [] ∧ after = []
    · obtain ⟨rfl, rfl⟩ := single
      simp only [List.nil_append]
      by_cases quoted : label = declaration.quoteConstructor
      · simp only [ReflectiveSubstitution.substituteResolved, quoted, if_true]
        exact .rel _ _ (.apply (before := []) (after := []) inner)
      · by_cases dropped : label = declaration.dropConstructor
        · have notQuote : ¬ declaration.dropConstructor = declaration.quoteConstructor :=
            fun same => quoted (dropped.trans same)
          have decision : matchesBinder declaration depth argument =
              matchesBinder declaration depth changed := by
            simp only [matchesBinder, inner.binderHead_eq compatible]
          by_cases hit : matchesBinder declaration depth changed = true
          · simp only [ReflectiveSubstitution.substituteResolved, dropped, notQuote, if_false, if_true,
              decision, hit]
            exact .refl _
          · simp only [ReflectiveSubstitution.substituteResolved, dropped, notQuote, if_false, if_true,
              decision, hit, Bool.false_eq_true]
            exact lawSame_apply_congr _ (.cons (ih depth) .nil)
        · simp only [ReflectiveSubstitution.substituteResolved, quoted, dropped, if_false]
          exact lawSame_apply_congr _ (.cons (ih depth) .nil)
    · have notOne : (before ++ argument :: after).length ≠ 1 := by
        intro one; apply single
        simp only [List.length_append, List.length_cons] at one
        exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
      have notOne' : (before ++ changed :: after).length ≠ 1 := by simpa using notOne
      rw [substituteResolved_of_length_ne_one declaration atIndex depth label notOne,
        substituteResolved_of_length_ne_one declaration atIndex depth label notOne']
      simp only [List.map_append, List.map_cons]
      exact lawSame_apply_congr _ (List.rel_append (forall₂_lawSame_refl _) (.cons (ih depth)
        (forall₂_lawSame_refl _)))
  | lambda _ ih =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved]
    exact lawSame_lambda_congr _ (ih _)
  | multiLambda _ ih =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved]
    exact lawSame_multiLambda_congr _ _ (ih _)
  | substBody _ ih =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved]
    exact lawSame_subst_congr (ih _) (.refl _)
  | substReplacement _ ih =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved]
    exact lawSame_subst_congr (.refl _) (ih _)
  | element _ ih =>
    intro depth
    simp only [ReflectiveSubstitution.substituteResolved, substituteResolvedList_eq_map,
      List.map_append, List.map_cons]
    exact lawSame_collection_congr _ _ (List.rel_append (forall₂_lawSame_refl _) (.cons (ih depth)
      (forall₂_lawSame_refl _)))

theorem substituteViewed_of_length_ne_one (declaration : ReflectivePresentationDecl)
    (insideQuote atIndex : Nat → Nat → Pattern) (depth : Nat) (label : String) {arguments : List Pattern}
    (notOne : arguments.length ≠ 1) :
    ReflectiveSubstitution.substituteViewed declaration insideQuote atIndex depth (.apply label arguments) =
      .apply label (arguments.map (ReflectiveSubstitution.substituteViewed declaration insideQuote atIndex depth)) := by
  match arguments, notOne with
  | [], _ => rfl
  | [_], notOne => exact absurd rfl notOne
  | first :: second :: rest, _ =>
      simp only [ReflectiveSubstitution.substituteViewed, ReflectiveSubstitution.substituteViewedList_eq_map]

theorem LawStep.substituteViewed {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) (insideQuote : Nat → Nat → Pattern)
    {left right : Pattern} (step : LawStep laws left right) :
    ∀ (atIndex : Nat → Nat → Pattern) depth,
      LawSame laws (ReflectiveSubstitution.substituteViewed declaration insideQuote atIndex depth left)
        (ReflectiveSubstitution.substituteViewed declaration insideQuote atIndex depth right) := by
  induction step with
  | permute unordered permutation =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed, ReflectiveSubstitution.substituteViewedList_eq_map]
    exact .rel _ _ (.permute unordered (permutation.map _))
  | members same =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed, ReflectiveSubstitution.substituteViewedList_eq_map]
    exact .rel _ _ (.members (members_map same _))
  | flatten found =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed, ReflectiveSubstitution.substituteViewedList_eq_map,
      List.map_append, List.map_cons]
    exact .rel _ _ (.flatten found)
  | unit found unit =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed, ReflectiveSubstitution.substituteViewedList_eq_map,
      List.map_append, List.map_cons]
    exact .rel _ _ (.unit found unit)
  | @apply label before after argument changed inner ih =>
    intro atIndex depth
    by_cases single : before = [] ∧ after = []
    · obtain ⟨rfl, rfl⟩ := single
      simp only [List.nil_append]
      by_cases quoted : label = declaration.quoteConstructor
      · simp only [ReflectiveSubstitution.substituteViewed, quoted, if_true]
        exact lawSame_apply_congr _ (.cons (ih insideQuote depth) .nil)
      · by_cases dropped : label = declaration.dropConstructor
        · have notQuote : ¬ declaration.dropConstructor = declaration.quoteConstructor :=
            fun same => quoted (dropped.trans same)
          have decision : matchesBinder declaration depth argument =
              matchesBinder declaration depth changed := by
            simp only [matchesBinder, inner.binderHead_eq compatible]
          by_cases hit : matchesBinder declaration depth changed = true
          · simp only [ReflectiveSubstitution.substituteViewed, dropped, notQuote, if_false, if_true,
              decision, hit]
            exact .refl _
          · simp only [ReflectiveSubstitution.substituteViewed, dropped, notQuote, if_false, if_true,
              decision, hit, Bool.false_eq_true]
            exact lawSame_apply_congr _ (.cons (ih atIndex depth) .nil)
        · simp only [ReflectiveSubstitution.substituteViewed, quoted, dropped, if_false]
          exact lawSame_apply_congr _ (.cons (ih atIndex depth) .nil)
    · have notOne : (before ++ argument :: after).length ≠ 1 := by
        intro one; apply single
        simp only [List.length_append, List.length_cons] at one
        exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
      have notOne' : (before ++ changed :: after).length ≠ 1 := by simpa using notOne
      rw [substituteViewed_of_length_ne_one declaration insideQuote atIndex depth label notOne,
        substituteViewed_of_length_ne_one declaration insideQuote atIndex depth label notOne']
      simp only [List.map_append, List.map_cons]
      exact lawSame_apply_congr _ (List.rel_append (forall₂_lawSame_refl _) (.cons (ih atIndex depth)
        (forall₂_lawSame_refl _)))
  | lambda _ ih =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed]
    exact lawSame_lambda_congr _ (ih _ _)
  | multiLambda _ ih =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed]
    exact lawSame_multiLambda_congr _ _ (ih _ _)
  | substBody _ ih =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed]
    exact lawSame_subst_congr (ih _ _) (.refl _)
  | substReplacement _ ih =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed]
    exact lawSame_subst_congr (.refl _) (ih _ _)
  | element _ ih =>
    intro atIndex depth
    simp only [ReflectiveSubstitution.substituteViewed, ReflectiveSubstitution.substituteViewedList_eq_map,
      List.map_append, List.map_cons]
    exact lawSame_collection_congr _ _ (List.rel_append (forall₂_lawSame_refl _) (.cons (ih atIndex depth)
      (forall₂_lawSame_refl _)))

theorem LawSame.substituteResolved {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) (atIndex : Nat → Nat → Pattern)
    {left right : Pattern} (same : LawSame laws left right) (depth : Nat) :
    LawSame laws (ReflectiveSubstitution.substituteResolved declaration atIndex depth left)
      (ReflectiveSubstitution.substituteResolved declaration atIndex depth right) := by
  induction same with
  | rel _ _ step => exact step.substituteResolved compatible atIndex depth
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem LawSame.substituteViewed {declaration : ReflectivePresentationDecl}
    (compatible : BinderLawCompatible laws declaration) (insideQuote atIndex : Nat → Nat → Pattern)
    {left right : Pattern} (same : LawSame laws left right) (depth : Nat) :
    LawSame laws (ReflectiveSubstitution.substituteViewed declaration insideQuote atIndex depth left)
      (ReflectiveSubstitution.substituteViewed declaration insideQuote atIndex depth right) := by
  induction same with
  | rel _ _ step => exact step.substituteViewed compatible insideQuote atIndex depth
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

open ReflectiveInstantiation in
/-- **Reflective elimination maps a law move in the body to law-equal results.** -/
theorem LawStep.instantiate (declaration : ReflectivePresentationDecl) {body body' : Pattern}
    (step : LawStep laws body body') (compatible : BinderLawCompatible laws declaration) :
      ∀ (depth : Nat) (replacement : Pattern),
      LawSame laws (ReflectiveInstantiation.instantiate declaration depth replacement body)
        (ReflectiveInstantiation.instantiate declaration depth replacement body') := by
  intro depth replacement
  exact LawSame.substituteResolved compatible _ (step.resolveQuotes compatible) depth

open ReflectiveCoherent in
theorem receive_lawSame (declaration : ReflectivePresentationDecl) (constructor : String)
    {name name' : Pattern} (same : LawSame laws name name') :
    LawSame laws (receive declaration constructor name) (receive declaration constructor name') := by
  have shapeEq : ∀ (n : Pattern), receive declaration constructor n = dropResult declaration constructor n true := by
    intro n
    unfold receive
    split
    · rename_i quote process
      rw [dropResult_shaped]
      by_cases quoted : quote = declaration.quoteConstructor <;> simp [quoted]
    · rename_i notShaped
      rw [dropResult_plain _ _ (.inl ?_)]
      rintro ⟨quote, process, rfl⟩
      exact notShaped quote process rfl
  rw [shapeEq, shapeEq]
  exact dropResult_lawSame declaration constructor true same

open ReflectiveInstantiation in
/-- **Reflective elimination maps law-equal replacements to law-equal results.** -/
theorem instantiate_replacement (declaration : ReflectivePresentationDecl) {replacement replacement' : Pattern}
    (same : LawSame laws replacement replacement') : ∀ (body : Pattern) (depth : Nat),
      LawSame laws (ReflectiveInstantiation.instantiate declaration depth replacement body)
        (ReflectiveInstantiation.instantiate declaration depth replacement' body) := by
  intro body depth
  unfold ReflectiveInstantiation.instantiate
  generalize ReflectiveSubstitution.resolveQuotes declaration body = resolved
  induction resolved using Pattern.inductionOn generalizing depth with
  | hbvar index => exact instantiateBVarAt_lawSame_replacement same depth index
  | hfvar name => exact .refl _
  | hlambda binder body ih =>
    simp only [ReflectiveSubstitution.substituteResolved]; exact lawSame_lambda_congr _ (ih _)
  | hmultiLambda arity binders body ih =>
    simp only [ReflectiveSubstitution.substituteResolved]; exact lawSame_multiLambda_congr _ _ (ih _)
  | hsubst body value ihBody ihValue =>
    simp only [ReflectiveSubstitution.substituteResolved]
    exact lawSame_subst_congr (ihBody _) (ihValue _)
  | hcollection kind elements rest ih =>
    simp only [ReflectiveSubstitution.substituteResolved, substituteResolvedList_eq_map]
    apply lawSame_collection_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr fun item member => ih item member depth
  | happly label arguments ih =>
    match arguments, ih with
    | [], _ => exact .refl _
    | first :: second :: rest, ih =>
      rw [substituteResolved_of_length_ne_one declaration _ depth label (by simp),
        substituteResolved_of_length_ne_one declaration _ depth label (by simp)]
      apply lawSame_apply_congr
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact List.forall₂_same.mpr fun item member => ih item member depth
    | [payload], ih =>
      simp only [ReflectiveSubstitution.substituteResolved]
      split
      · exact .refl _
      · split
        · split
          · exact receive_lawSame declaration label (instantiateBVarAt_lawSame_replacement same depth depth)
          · exact lawSame_apply_congr _ (.cons (ih payload (by simp) depth) .nil)
        · exact lawSame_apply_congr _ (.cons (ih payload (by simp) depth) .nil)

open ReflectiveInstantiation in
theorem nameMark_replacement (declaration : ReflectivePresentationDecl) (depth : Nat) {replacement replacement' : Pattern}
    (same : LawSame laws replacement replacement') (name : Pattern) :
    (nameMark declaration depth replacement name).2 = (nameMark declaration depth replacement' name).2 ∧
      LawSame laws (nameMark declaration depth replacement name).1 (nameMark declaration depth replacement' name).1 := by
  unfold nameMark
  split
  · exact ⟨rfl, instantiateBVarAt_lawSame_replacement same depth depth⟩
  · exact ⟨rfl, instantiate_replacement declaration same name depth⟩

theorem instantiate_lawSame (declaration : ReflectivePresentationDecl) (depth : Nat) {replacement replacement' body body' : Pattern}
    (compatible : BinderLawCompatible laws declaration)
    (sameReplacement : LawSame laws replacement replacement') (sameBody : LawSame laws body body') :
    LawSame laws (ReflectiveInstantiation.instantiate declaration depth replacement body)
      (ReflectiveInstantiation.instantiate declaration depth replacement' body') := by
  refine .trans _ _ _ ?_ (instantiate_replacement declaration sameReplacement body' depth)
  induction sameBody with
  | rel _ _ step => exact step.instantiate declaration compatible depth replacement
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem normalizeReflectiveReplacement_lawSame (declaration : ReflectivePresentationDecl) {replacement replacement' : Pattern}
    (same : LawSame laws replacement replacement') :
    LawSame laws (normalizeReflectiveReplacement declaration replacement)
      (normalizeReflectiveReplacement declaration replacement') := by
  by_cases shaped : ∃ constructor payload, replacement = .apply constructor [payload]
  · obtain ⟨constructor, payload, rfl⟩ := shaped
    obtain ⟨arguments, rfl, inner⟩ := same.apply_inv
    cases inner with
    | cons payloadSame rest =>
      cases rest
      unfold normalizeReflectiveReplacement
      by_cases quote : (constructor == declaration.quoteConstructor) = true
      · simp only [quote, if_true]
        exact lawSame_apply_congr _ (.cons (normalizeReflective_lawSame declaration payloadSame) .nil)
      · simp only [quote, Bool.false_eq_true, if_false]
        exact normalizeReflective_lawSame declaration same
  · have shaped' : ¬ ∃ constructor payload, replacement' = .apply constructor [payload] := by
      rintro ⟨constructor, payload, rfl⟩
      obtain ⟨arguments, rfl, inner⟩ := LawSame.apply_inv (Relation.EqvGen.symm _ _ same)
      cases inner with
      | cons _ rest => cases rest; exact shaped ⟨constructor, _, rfl⟩
    have plain : ∀ term : Pattern, (¬ ∃ constructor payload, term = .apply constructor [payload]) →
        normalizeReflectiveReplacement declaration term = ReflectiveSubstitution.normalizeReflective declaration term := by
      intro term notShaped
      unfold normalizeReflectiveReplacement
      split
      · rename_i constructor payload
        exact absurd ⟨constructor, payload, rfl⟩ notShaped
      · rfl
    rw [plain _ shaped, plain _ shaped']
    exact normalizeReflective_lawSame declaration same

/-- Law-equal actions give law-equal viewed substitutions. -/
theorem substituteViewed_actions_lawSame (declaration : ReflectivePresentationDecl)
    {insideQuote insideQuote' : Nat → Nat → Pattern}
    (insideSame : ∀ level index, LawSame laws (insideQuote level index) (insideQuote' level index)) :
    ∀ (body : Pattern) (atIndex atIndex' : Nat → Nat → Pattern),
      (∀ level index, LawSame laws (atIndex level index) (atIndex' level index)) → ∀ depth,
      LawSame laws (ReflectiveSubstitution.substituteViewed declaration insideQuote atIndex depth body)
        (ReflectiveSubstitution.substituteViewed declaration insideQuote' atIndex' depth body) := by
  intro body
  induction body using Pattern.inductionOn with
  | hbvar index => intro _ _ outsideSame depth; exact outsideSame depth index
  | hfvar name => intro _ _ _ _; exact .refl _
  | hlambda binder body ih =>
    intro atIndex atIndex' outsideSame depth
    simp only [ReflectiveSubstitution.substituteViewed]
    exact lawSame_lambda_congr _ (ih atIndex atIndex' outsideSame _)
  | hmultiLambda arity binders body ih =>
    intro atIndex atIndex' outsideSame depth
    simp only [ReflectiveSubstitution.substituteViewed]
    exact lawSame_multiLambda_congr _ _ (ih atIndex atIndex' outsideSame _)
  | hsubst body value ihBody ihValue =>
    intro atIndex atIndex' outsideSame depth
    simp only [ReflectiveSubstitution.substituteViewed]
    exact lawSame_subst_congr (ihBody atIndex atIndex' outsideSame _) (ihValue atIndex atIndex' outsideSame _)
  | hcollection kind elements rest ih =>
    intro atIndex atIndex' outsideSame depth
    simp only [ReflectiveSubstitution.substituteViewed, ReflectiveSubstitution.substituteViewedList_eq_map]
    apply lawSame_collection_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr fun item member => ih item member atIndex atIndex' outsideSame depth
  | happly label arguments ih =>
    intro atIndex atIndex' outsideSame depth
    match arguments, ih with
    | [], _ => exact .refl _
    | first :: second :: rest, ih =>
      rw [substituteViewed_of_length_ne_one declaration _ _ depth label (by simp),
        substituteViewed_of_length_ne_one declaration _ _ depth label (by simp)]
      apply lawSame_apply_congr
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact List.forall₂_same.mpr fun item member => ih item member atIndex atIndex' outsideSame depth
    | [payload], ih =>
      simp only [ReflectiveSubstitution.substituteViewed]
      split
      · exact lawSame_apply_congr _ (.cons (ih payload (by simp) insideQuote insideQuote' insideSame depth) .nil)
      · split
        · split
          · exact receive_lawSame declaration label (outsideSame depth depth)
          · exact lawSame_apply_congr _ (.cons (ih payload (by simp) atIndex atIndex' outsideSame depth) .nil)
        · exact lawSame_apply_congr _ (.cons (ih payload (by simp) atIndex atIndex' outsideSame depth) .nil)

open ReflectiveInstantiation in
/-- **Declared binder elimination respects the collection laws**, at every quote
scope. -/
theorem instantiateDeclared_lawSame (declaration : ReflectivePresentationDecl) (depth : Nat)
    {replacement replacement' body body' : Pattern}
    (compatible : BinderLawCompatible laws declaration)
    (sameReplacement : LawSame laws replacement replacement') (sameBody : LawSame laws body body') :
    LawSame laws (instantiateDeclared declaration depth replacement body)
      (instantiateDeclared declaration depth replacement' body') := by
  unfold instantiateDeclared
  cases scope : declaration.quoteScope with
  | closed => exact instantiate_lawSame declaration depth compatible sameReplacement sameBody
  | reaching view =>
    simp only [ReflectiveSubstitution.substituteScoped]
    have lowered : ∀ level index,
        LawSame laws (Substitution.instantiateBVarAt level replacement (.bvar index))
          (Substitution.instantiateBVarAt level replacement' (.bvar index)) :=
      fun level index => instantiateBVarAt_lawSame_replacement sameReplacement level index
    have insideSame : ∀ level index,
        LawSame laws (view.inside (fun level index => Substitution.instantiateBVarAt level replacement (.bvar index))
            level index)
          (view.inside (fun level index => Substitution.instantiateBVarAt level replacement' (.bvar index))
            level index) := by
      intro level index
      cases view with
      | apply => exact lowered level index
      | freeze frozen =>
          simp only [QuoteView.inside]
          split
          · exact .refl _
          · exact lowered level index
      | closure context =>
          simp only [QuoteView.inside]
          split
          · exact lawSame_apply_congr _ (.cons (lowered level level) .nil)
          · exact lowered level index
    refine .trans _ _ _ ?_ (substituteViewed_actions_lawSame declaration insideSame _ _ _ lowered depth)
    induction sameBody with
    | rel _ _ step =>
        exact LawSame.substituteViewed compatible _ _ (step.resolveQuotes compatible) depth
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- **Reflective binder elimination respects the collection laws.** -/
theorem reflectiveOperation_lawSame (declaration : ReflectivePresentationDecl) {replacement replacement' body body' : Pattern}
    (compatible : BinderLawCompatible laws declaration)
    (sameReplacement : LawSame laws replacement replacement') (sameBody : LawSame laws body body') :
    LawSame laws (ScopedRuleInstantiation.reflectiveOperation declaration replacement body)
      (ScopedRuleInstantiation.reflectiveOperation declaration replacement' body') :=
  instantiateDeclared_lawSame declaration 0 compatible
    (normalizeReflectiveReplacement_lawSame declaration sameReplacement) sameBody

/-- An ordinary binder respects collection laws. A selected reflective
binder needs compatibility at the rule's actual substitution declaration. -/
theorem binderOperation_lawSame (profile : Reflection.ReflectionProfile) (rule : RewriteRule)
    {replacement replacement' body body' : Pattern}
    (compatible : BinderLawsFor laws profile rule)
    (sameReplacement : LawSame laws replacement replacement') (sameBody : LawSame laws body body') :
    LawSame laws (ScopedReflectiveExecution.binderOperation profile rule replacement body)
      (ScopedReflectiveExecution.binderOperation profile rule replacement' body') := by
  unfold ScopedReflectiveExecution.binderOperation
  cases selected : substitutionPresentationForRule? profile rule with
  | none => exact instantiateBVar_lawSame sameReplacement sameBody
  | some declaration =>
    exact reflectiveOperation_lawSame declaration (compatible declaration selected) sameReplacement sameBody

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
