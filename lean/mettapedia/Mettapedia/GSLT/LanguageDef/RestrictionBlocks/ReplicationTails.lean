import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRawLaws

/-!
# Open tails, pending substitutions, and binding restrictions along a chain of laws

A raw match of a bag reads the members of a term and not its tail, so a law of replication read raw relates a term to
a bag with an open tail. The object reading of a term closes every open tail (`closeTails`); a term without pending
substitutions (`substFree`) reads as an object term (`isObject_closeTails`). Closing tails commutes with renaming and
with filling a context, and keeps the restrictions binding; a context keeps pending substitutions and binding
restrictions alike for fillings that have them alike and are not abstractions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)

/-! ## Closing open tails -/

mutual
  /-- **The object reading of a term**: every open collection tail closed. -/
  def closeTails : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => .apply label (closeTailsList arguments)
    | .lambda binder body => .lambda binder (closeTails body)
    | .multiLambda arity binders body => .multiLambda arity binders (closeTails body)
    | .subst body replacement => .subst (closeTails body) (closeTails replacement)
    | .collection kind elements _ => .collection kind (closeTailsList elements) none

  def closeTailsList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => closeTails pattern :: closeTailsList patterns
end

theorem closeTailsList_eq_map : ∀ (patterns : List Pattern), closeTailsList patterns = patterns.map closeTails
  | [] => rfl
  | pattern :: patterns => by simp [closeTailsList, closeTailsList_eq_map patterns]

mutual
  /-- Whether a term has no pending explicit substitution. -/
  def substFree : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply _ arguments => substFreeList arguments
    | .lambda _ body => substFree body
    | .multiLambda _ _ body => substFree body
    | .subst _ _ => false
    | .collection _ elements _ => substFreeList elements

  def substFreeList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => substFree pattern && substFreeList patterns
end

theorem substFreeList_eq_all : ∀ (patterns : List Pattern), substFreeList patterns = patterns.all substFree
  | [] => rfl
  | pattern :: patterns => by simp [substFreeList, substFreeList_eq_all patterns]

/-- **An object term is its own object reading.** -/
theorem closeTails_of_object (pattern : Pattern) : isObjectPattern pattern = true → closeTails pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | happly label arguments recurse =>
      intro object
      simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
      simp only [closeTails, closeTailsList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id arguments]
      exact List.map_congr_left fun argument member => recurse argument member (object argument member)
  | hlambda binder body recurse =>
      intro object
      simp only [closeTails, recurse (by simpa [isObjectPattern] using object)]
  | hmultiLambda arity binders body recurse =>
      intro object
      simp only [closeTails, recurse (by simpa [isObjectPattern] using object)]
  | hsubst body replacement _ _ =>
      intro object
      simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      intro object
      simp only [isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true] at object
      obtain ⟨closed, objects⟩ := object
      cases rest with
      | some name => simp at closed
      | none =>
          simp only [closeTails, closeTailsList_eq_map]
          congr 1
          conv_rhs => rw [← List.map_id elements]
          exact List.map_congr_left fun element member => recurse element member (objects element member)

/-- **The object reading of a term without pending substitutions is an object term.** -/
theorem isObject_closeTails (pattern : Pattern) : isObjectPattern (closeTails pattern) = substFree pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly label arguments recurse =>
      simp only [closeTails, closeTailsList_eq_map, isObjectPattern, isObjectPatternList_eq_all, substFree,
        substFreeList_eq_all, List.all_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp]
      exact forall₂_congr fun argument member => by rw [recurse argument member]
  | hlambda binder body recurse => simp only [closeTails, isObjectPattern, substFree, recurse]
  | hmultiLambda arity binders body recurse => simp only [closeTails, isObjectPattern, substFree, recurse]
  | hsubst body replacement _ _ => rfl
  | hcollection kind elements rest recurse =>
      simp only [closeTails, closeTailsList_eq_map, isObjectPattern, isObjectPatternList_eq_all, substFree,
        substFreeList_eq_all, List.all_map, Option.isNone_none, Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp]
      exact forall₂_congr fun element member => by rw [recurse element member]

/-- An object term has no pending substitution. -/
theorem substFree_of_object {pattern : Pattern} (object : isObjectPattern pattern = true) : substFree pattern = true := by
  rw [← isObject_closeTails, closeTails_of_object pattern object, object]

/-- **Closing tails commutes with renaming.** -/
theorem closeTails_rename (pattern : Pattern) : ∀ (relabel : Nat → Nat),
    closeTails (rename relabel pattern) = rename relabel (closeTails pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | happly label arguments recurse =>
      intro relabel
      simp only [rename_apply, closeTails, closeTailsList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => recurse argument member relabel
  | hlambda binder body recurse =>
      intro relabel
      simp only [rename_lambda, closeTails, recurse]
  | hmultiLambda arity binders body recurse =>
      intro relabel
      simp only [rename_multiLambda, closeTails, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro relabel
      simp only [rename_subst, closeTails, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro relabel
      simp only [rename_collection, closeTails, closeTailsList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member relabel

/-- Renaming keeps a term without pending substitutions. -/
theorem substFree_rename (pattern : Pattern) : ∀ (relabel : Nat → Nat),
    substFree (rename relabel pattern) = substFree pattern := by
  intro relabel
  rw [← isObject_closeTails, closeTails_rename, isObjectPattern_rename, isObject_closeTails]

/-- A term is an abstraction exactly when its object reading is. -/
theorem closeTails_notLambda {pattern : Pattern} (notLambda : ∀ binder body, pattern ≠ .lambda binder body) :
    ∀ binder body, closeTails pattern ≠ .lambda binder body := by
  intro binder body equal
  cases pattern with
  | lambda binder' body' => exact notLambda binder' body' rfl
  | _ => simp [closeTails] at equal

/-! ## Binding restrictions -/

/-- **Whether the restriction binds reads only whether a lone argument is an abstraction.** -/
theorem bindsAt_congr {base : Block} {label : String} {first second : List Pattern}
    (lengths : first.length = second.length)
    (lambdas : ∀ argument, first = [argument] → ∀ argument', second = [argument'] →
      ((∃ binder body, argument = .lambda binder body) ↔ ∃ binder body, argument' = .lambda binder body)) :
    bindsAt base label first = bindsAt base label second := by
  match first, second, lengths, lambdas with
  | [argument], [argument'], _, lambdas =>
      have same := lambdas argument rfl argument' rfl
      by_cases isLambda : ∃ binder body, argument = .lambda binder body
      · obtain ⟨binder, body, rfl⟩ := isLambda
        obtain ⟨binder', body', rfl⟩ := same.mp ⟨binder, body, rfl⟩
        rfl
      · have notLambda : ∀ binder body, argument ≠ .lambda binder body := fun binder body equal =>
          isLambda ⟨binder, body, equal⟩
        have notLambda' : ∀ binder body, argument' ≠ .lambda binder body := fun binder body equal =>
          isLambda (same.mpr ⟨binder, body, equal⟩)
        rw [bindsAt_single notLambda, bindsAt_single notLambda']
  | [], [], _, _ => rfl
  | first :: other :: rest, first' :: other' :: rest', _, _ =>
      rw [bindsAt_other (by simp), bindsAt_other (by simp)]

theorem rename_lambda_iff {relabel : Nat → Nat} {pattern : Pattern} :
    (∃ binder body, rename relabel pattern = .lambda binder body) ↔ ∃ binder body, pattern = .lambda binder body := by
  constructor
  · rintro ⟨binder, body, equal⟩
    by_contra notLambda
    push Not at notLambda
    exact rename_notLambda notLambda binder body equal
  · rintro ⟨binder, body, rfl⟩
    exact ⟨binder, _, rename_lambda relabel binder body⟩

theorem closeTails_lambda_iff {pattern : Pattern} :
    (∃ binder body, closeTails pattern = .lambda binder body) ↔ ∃ binder body, pattern = .lambda binder body := by
  constructor
  · rintro ⟨binder, body, equal⟩
    by_contra notLambda
    push Not at notLambda
    exact closeTails_notLambda notLambda binder body equal
  · rintro ⟨binder, body, rfl⟩
    exact ⟨binder, _, rfl⟩

/-- **Renaming keeps the restrictions binding.** -/
theorem restrictionsBind_rename (base : Block) (pattern : Pattern) : ∀ (relabel : Nat → Nat),
    restrictionsBind base (rename relabel pattern) = restrictionsBind base pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | happly label arguments recurse =>
      intro relabel
      simp only [rename_apply, restrictionsBind, restrictionsBindList_eq_all, List.all_map]
      congr 1
      · exact bindsAt_congr (by simp) fun argument equal argument' equal' => by
          obtain ⟨original, rfl, rfl⟩ := map_rename_eq_singleton equal
          simp only [List.cons.injEq, and_true] at equal'
          subst equal'
          exact rename_lambda_iff
      · apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, Function.comp]
        exact forall₂_congr fun argument member => by rw [recurse argument member relabel]
  | hlambda binder body recurse =>
      intro relabel
      simp only [rename_lambda, restrictionsBind, recurse]
  | hmultiLambda arity binders body recurse =>
      intro relabel
      simp only [rename_multiLambda, restrictionsBind, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro relabel
      simp only [rename_subst, restrictionsBind, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro relabel
      simp only [rename_collection, restrictionsBind, restrictionsBindList_eq_all, List.all_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp]
      exact forall₂_congr fun element member => by rw [recurse element member relabel]

/-- **Closing tails keeps the restrictions binding.** -/
theorem restrictionsBind_closeTails (base : Block) (pattern : Pattern) :
    restrictionsBind base (closeTails pattern) = restrictionsBind base pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly label arguments recurse =>
      simp only [closeTails, closeTailsList_eq_map, restrictionsBind, restrictionsBindList_eq_all, List.all_map]
      congr 1
      · exact bindsAt_congr (by simp) fun argument equal argument' equal' => by
          match arguments, equal with
          | [original], equal =>
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at equal equal'
              subst equal equal'
              exact closeTails_lambda_iff
      · apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, Function.comp]
        exact forall₂_congr fun argument member => by rw [recurse argument member]
  | hlambda binder body recurse => simp only [closeTails, restrictionsBind, recurse]
  | hmultiLambda arity binders body recurse => simp only [closeTails, restrictionsBind, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      simp only [closeTails, restrictionsBind, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      simp only [closeTails, closeTailsList_eq_map, restrictionsBind, restrictionsBindList_eq_all, List.all_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp]
      exact forall₂_congr fun element member => by rw [recurse element member]

/-! ## Contexts -/

/-- The object reading of a context: every open tail in it closed. -/
def closeContext : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply label before inner after =>
      .apply label (before.map closeTails) (closeContext inner) (after.map closeTails)
  | .lambda binder inner => .lambda binder (closeContext inner)
  | .multiLambda arity binders inner => .multiLambda arity binders (closeContext inner)
  | .substBody inner replacement => .substBody (closeContext inner) (closeTails replacement)
  | .substReplacement body inner => .substReplacement (closeTails body) (closeContext inner)
  | .collection kind before inner after _ =>
      .collection kind (before.map closeTails) (closeContext inner) (after.map closeTails) none

/-- **Closing tails commutes with filling a context.** -/
theorem closeTails_fill (context : OneHoleContext) (filling : Pattern) :
    closeTails (context.fill filling) = (closeContext context).fill (closeTails filling) := by
  induction context with
  | hole => rfl
  | apply label before inner after recurse =>
      simp only [OneHoleContext.fill, closeContext, closeTails, closeTailsList_eq_map, List.map_append, List.map_cons,
        recurse]
  | lambda binder inner recurse => simp only [OneHoleContext.fill, closeContext, closeTails, recurse]
  | multiLambda arity binders inner recurse => simp only [OneHoleContext.fill, closeContext, closeTails, recurse]
  | substBody inner replacement recurse => simp only [OneHoleContext.fill, closeContext, closeTails, recurse]
  | substReplacement body inner recurse => simp only [OneHoleContext.fill, closeContext, closeTails, recurse]
  | collection kind before inner after rest recurse =>
      simp only [OneHoleContext.fill, closeContext, closeTails, closeTailsList_eq_map, List.map_append, List.map_cons,
        recurse]

/-- **A context keeps fillings without pending substitutions alike.** -/
theorem substFree_fill (context : OneHoleContext) {first second : Pattern} (same : substFree first = substFree second) :
    substFree (context.fill first) = substFree (context.fill second) := by
  induction context with
  | hole => exact same
  | apply label before inner after recurse =>
      simp only [OneHoleContext.fill, substFree, substFreeList_eq_all, List.all_append, List.all_cons, recurse]
  | lambda binder inner recurse => simp only [OneHoleContext.fill, substFree, recurse]
  | multiLambda arity binders inner recurse => simp only [OneHoleContext.fill, substFree, recurse]
  | substBody inner replacement recurse => rfl
  | substReplacement body inner recurse => rfl
  | collection kind before inner after rest recurse =>
      simp only [OneHoleContext.fill, substFree, substFreeList_eq_all, List.all_append, List.all_cons, recurse]

/-- Two fillings both abstractions, or neither. -/
def LambdaAlike (first second : Pattern) : Prop :=
  (∃ binder body, first = .lambda binder body) ↔ ∃ binder body, second = .lambda binder body

theorem LambdaAlike.of_notLambda {first second : Pattern} (firstNot : ∀ binder body, first ≠ .lambda binder body)
    (secondNot : ∀ binder body, second ≠ .lambda binder body) : LambdaAlike first second :=
  ⟨fun ⟨binder, body, equal⟩ => absurd equal (firstNot binder body),
    fun ⟨binder, body, equal⟩ => absurd equal (secondNot binder body)⟩

/-- **A context keeps fillings alike in binding their restrictions**, when they are both abstractions or neither. -/
theorem restrictionsBind_fill (base : Block) (context : OneHoleContext) : ∀ {first second : Pattern},
    restrictionsBind base first = restrictionsBind base second → LambdaAlike first second →
      restrictionsBind base (context.fill first) = restrictionsBind base (context.fill second) ∧
        LambdaAlike (context.fill first) (context.fill second) := by
  induction context with
  | hole => exact fun same alike => ⟨same, alike⟩
  | apply label before inner after recurse =>
      intro first second same alike
      obtain ⟨innerSame, innerAlike⟩ := recurse same alike
      refine ⟨?_, LambdaAlike.of_notLambda (apply_notLambda _ _) (apply_notLambda _ _)⟩
      simp only [OneHoleContext.fill, restrictionsBind, restrictionsBindList_eq_all, List.all_append, List.all_cons,
        innerSame]
      congr 1
      refine bindsAt_congr (by simp) fun argument equal argument' equal' => ?_
      have lengthOne := congrArg List.length equal
      simp only [List.length_append, List.length_cons, List.length_nil] at lengthOne
      obtain ⟨rfl, rfl⟩ : before = [] ∧ after = [] :=
        ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
      simp only [List.nil_append, List.cons.injEq, and_true] at equal equal'
      subst equal equal'
      exact innerAlike
  | lambda binder inner recurse =>
      intro first second same alike
      obtain ⟨innerSame, _⟩ := recurse same alike
      exact ⟨by simpa [OneHoleContext.fill, restrictionsBind] using innerSame,
        ⟨fun _ => ⟨binder, inner.fill second, rfl⟩, fun _ => ⟨binder, inner.fill first, rfl⟩⟩⟩
  | multiLambda arity binders inner recurse =>
      intro first second same alike
      obtain ⟨innerSame, _⟩ := recurse same alike
      exact ⟨by simpa [OneHoleContext.fill, restrictionsBind] using innerSame,
        LambdaAlike.of_notLambda (multiLambda_notLambda _ _ _) (multiLambda_notLambda _ _ _)⟩
  | substBody inner replacement recurse =>
      intro first second same alike
      obtain ⟨innerSame, _⟩ := recurse same alike
      exact ⟨by simp only [OneHoleContext.fill, restrictionsBind, innerSame],
        LambdaAlike.of_notLambda (fun _ _ equal => by cases equal) (fun _ _ equal => by cases equal)⟩
  | substReplacement body inner recurse =>
      intro first second same alike
      obtain ⟨innerSame, _⟩ := recurse same alike
      exact ⟨by simp only [OneHoleContext.fill, restrictionsBind, innerSame],
        LambdaAlike.of_notLambda (fun _ _ equal => by cases equal) (fun _ _ equal => by cases equal)⟩
  | collection kind before inner after rest recurse =>
      intro first second same alike
      obtain ⟨innerSame, _⟩ := recurse same alike
      exact ⟨by simp only [OneHoleContext.fill, restrictionsBind, restrictionsBindList_eq_all, List.all_append,
          List.all_cons, innerSame],
        LambdaAlike.of_notLambda (collection_notLambda _ _ _) (collection_notLambda _ _ _)⟩

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
