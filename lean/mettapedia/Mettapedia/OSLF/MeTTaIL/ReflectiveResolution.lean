import Mathlib.Data.List.Perm.Basic
import Mettapedia.OSLF.MeTTaIL.ReflectiveCoherentSubstitution

/-!
# Resolving quotations of drops: fiber closure and congruence

Two facts about `resolveQuotes`, the first stage of reflective substitution.

* The literal-quotation fiber (`quotesLiteral`: quotations expose a drop only
  literally) is closed under structural substitution of fiber names.
* Every pattern is related to its resolution by every congruence satisfying
  the parallel monoid laws, read for an n-ary presentation, and quote-drop.
  The congruence is a parameter (`QuoteDropCongruence`); no particular
  relation is fixed here.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveResolution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent

variable {declaration : ReflectivePresentationDecl}

/-! ## Closure under substitution of fiber names -/


/-- Structural substitution keeps a resolved term inside the literal-quotation
fiber whenever every name it inserts lies in the fiber. -/
theorem quotesLiteral_substituteResolved
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (atIndex : Nat → Nat → Pattern)
    (atIndexLiteral : ∀ level index, quotesLiteral declaration (atIndex level index) = true)
    (depth : Nat) {body : Pattern} (resolved : QuotesResolved declaration body) :
    quotesLiteral declaration (substituteResolved declaration atIndex depth body) = true := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index => exact atIndexLiteral depth index
  | hfvar name => rfl
  | hlambda binder body ih => exact ih (depth + 1) resolved
  | hmultiLambda arity binders body ih => exact ih (depth + arity) resolved
  | hsubst body value ihBody ihValue =>
      simp only [substituteResolved, quotesLiteral, Bool.and_eq_true]
      exact ⟨ihBody (depth + 1) resolved.1, ihValue depth resolved.2⟩
  | hcollection kind elements rest ih =>
      have each := (quotesResolvedList_iff elements).mp resolved
      simp only [substituteResolved, substituteResolvedList_eq_map, quotesLiteral]
      rw [quotesLiteralList_iff]
      intro p member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember depth (each original originalMember)
  | happly constructor arguments ih =>
      have each := (quotesResolvedList_iff arguments).mp resolved.1
      match arguments, resolved, each, ih with
      | [], _, _, _ => rfl
      | first :: second :: rest, _, each, ih =>
          rw [substituteResolved_apply_long]
          simp only [List.map_cons, quotesLiteral]
          rw [quotesLiteralList_iff]
          intro p member
          have mapped : p ∈ (first :: second :: rest).map
              (substituteResolved declaration atIndex depth) := by
            simpa using member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mapped
          exact ih original originalMember depth (each original originalMember)
      | [payload], resolved, each, ih =>
          have payloadLiteral := ih payload (by simp) depth (each payload (by simp))
          have plain : ∀ {label : String}, label ≠ declaration.quoteConstructor →
              quotesLiteral declaration (.apply label
                [substituteResolved declaration atIndex depth payload]) = true := by
            intro label notQuote
            simp only [quotesLiteral, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
            exact ⟨.inl notQuote, payloadLiteral⟩
          by_cases quoted : constructor = declaration.quoteConstructor
          · subst quoted
            simp only [substituteResolved, if_true]
            exact quotesLiteral_of_resolved resolved
          · by_cases dropped : constructor = declaration.dropConstructor
            · subst dropped
              rw [substituteResolved_drop distinct]
              split
              · rcases receive_cases (declaration := declaration) declaration.dropConstructor
                    (atIndex depth depth) with received | ⟨process, shaped, received⟩
                · rw [received]
                  have nameLiteral := atIndexLiteral depth depth
                  simp only [quotesLiteral, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
                  exact ⟨.inl distinct, nameLiteral⟩
                · rw [received]
                  have nameLiteral := atIndexLiteral depth depth
                  rw [shaped] at nameLiteral
                  simp only [quotesLiteral, Bool.and_eq_true] at nameLiteral
                  exact nameLiteral.2
              · exact plain distinct
            · rw [substituteResolved_unary_plain quoted dropped]
              exact plain quoted

/-- **Closure under substitution of fiber names.** Reflective substitution of
a name in the literal-quotation fiber lands in the fiber, whatever the body. -/
theorem quotesLiteral_substituteReflective
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {replacementName : Pattern} (replacementLiteral : quotesLiteral declaration replacementName = true)
    (depth : Nat) (body : Pattern) :
    quotesLiteral declaration (substituteReflective declaration depth replacementName body) = true := by
  unfold substituteReflective
  apply quotesLiteral_substituteResolved distinct _ _ depth (resolveQuotes_resolved body)
  intro level index
  by_cases hit : index = level
  · simp [hit, replacementLiteral]
  · simp [hit, quotesLiteral]

/-! ## Every pattern is related to its resolution

The laws are those of structural congruence on parallel composition, read for
an n-ary presentation (unit, commutativity and associativity, and a
one-member composition), together with quote-drop, and congruence at every
position. -/

/-- The declared parallel composition of a list of members. -/
abbrev parallel (declaration : ReflectivePresentationDecl) (members : List Pattern) : Pattern :=
  .collection declaration.parallelCollection members none

/-- A congruence on patterns with the parallel monoid laws and quote-drop. -/
structure QuoteDropCongruence (declaration : ReflectivePresentationDecl) where
  /-- The relation. -/
  rel : Pattern → Pattern → Prop
  equivalence : Equivalence rel
  apply_congr : ∀ (constructor : String) {arguments arguments' : List Pattern},
    List.Forall₂ rel arguments arguments' →
      rel (.apply constructor arguments) (.apply constructor arguments')
  lambda_congr : ∀ (binder : Option String) {body body' : Pattern},
    rel body body' → rel (.lambda binder body) (.lambda binder body')
  multiLambda_congr : ∀ (arity : Nat) (binders : List String) {body body' : Pattern},
    rel body body' → rel (.multiLambda arity binders body) (.multiLambda arity binders body')
  subst_congr : ∀ {body body' value value' : Pattern},
    rel body body' → rel value value' → rel (.subst body value) (.subst body' value')
  collection_congr : ∀ (kind : CollType) (rest : Option String) {elements elements' : List Pattern},
    List.Forall₂ rel elements elements' →
      rel (.collection kind elements rest) (.collection kind elements' rest)
  parallel_perm : ∀ {members members' : List Pattern},
    members.Perm members' → rel (parallel declaration members) (parallel declaration members')
  parallel_unit : ∀ members : List Pattern,
    rel (parallel declaration (.apply declaration.parallelUnitConstructor [] :: members))
      (parallel declaration members)
  parallel_assoc : ∀ inner outer : List Pattern,
    rel (parallel declaration (parallel declaration inner :: outer))
      (parallel declaration (inner ++ outer))
  parallel_single : ∀ member : Pattern, rel (parallel declaration [member]) member
  quote_drop : ∀ name : Pattern,
    rel (.apply declaration.quoteConstructor [.apply declaration.dropConstructor [name]]) name

namespace QuoteDropCongruence

variable (congruence : QuoteDropCongruence declaration)

private theorem forall₂_head {first first' : Pattern} {rest : List Pattern}
    (related : congruence.rel first first') :
    List.Forall₂ congruence.rel (first :: rest) (first' :: rest) :=
  .cons related (List.forall₂_same.mpr fun _ _ => congruence.equivalence.refl _)

private theorem related_leaves_append :
    ∀ (members suffix : List Pattern),
      (∀ member ∈ members,
        congruence.rel member (parallel declaration (parallelLeaves declaration member))) →
      congruence.rel (parallel declaration (members ++ suffix))
        (parallel declaration (parallelLeavesList declaration members ++ suffix))
  | [], _, _ => congruence.equivalence.refl _
  | member :: members, suffix, related => by
      have equivalence := congruence.equivalence
      have head := related member (by simp)
      have tail := related_leaves_append members (suffix ++ parallelLeaves declaration member)
        fun other otherMember => related other (by simp [otherMember])
      refine equivalence.trans
        (congruence.collection_congr _ none (forall₂_head congruence head)) ?_
      refine equivalence.trans (congruence.parallel_assoc _ _) ?_
      have toTail : (parallelLeaves declaration member ++ (members ++ suffix)).Perm
          (members ++ (suffix ++ parallelLeaves declaration member)) := by
        simpa only [List.append_assoc] using
          List.perm_append_comm (l₁ := parallelLeaves declaration member) (l₂ := members ++ suffix)
      have fromTail : (parallelLeavesList declaration members ++
            (suffix ++ parallelLeaves declaration member)).Perm
          (parallelLeavesList declaration (member :: members) ++ suffix) := by
        simp only [parallelLeavesList, List.append_assoc]
        simpa only [List.append_assoc] using
          List.perm_append_comm (l₁ := parallelLeavesList declaration members ++ suffix)
            (l₂ := parallelLeaves declaration member)
      exact equivalence.trans (congruence.parallel_perm toTail)
        (equivalence.trans tail (congruence.parallel_perm fromTail))

/-- A pattern is related to the declared composition of its members. -/
theorem related_parallelLeaves (pattern : Pattern) :
    congruence.rel pattern (parallel declaration (parallelLeaves declaration pattern)) := by
  have single : ∀ member : Pattern, congruence.rel member (parallel declaration [member]) :=
    fun member => congruence.equivalence.symm (congruence.parallel_single member)
  induction pattern using Pattern.inductionOn with
  | hbvar index => exact single _
  | hfvar name => exact single _
  | hlambda binder body _ => exact single _
  | hmultiLambda arity binders body _ => exact single _
  | hsubst body value _ _ => exact single _
  | happly constructor arguments _ =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · subst unit
            simp only [parallelLeaves, if_true]
            exact congruence.equivalence.trans (single _) (congruence.parallel_unit [])
          · simp only [parallelLeaves, unit, if_false]
            exact single _
      | cons first rest => exact single _
  | hcollection kind elements rest related =>
      cases rest with
      | some name => exact single _
      | none =>
          by_cases parallelKind : kind = declaration.parallelCollection
          · subst parallelKind
            simp only [parallelLeaves, if_true]
            simpa using related_leaves_append congruence elements [] related
          · simp only [parallelLeaves, parallelKind, if_false]
            exact single _

private theorem related_finish (constructor : String) (arguments : List Pattern) :
    congruence.rel (.apply constructor arguments)
      (finishResolveApply declaration constructor arguments) := by
  have refl := congruence.equivalence.refl
  match arguments with
  | [] => exact refl _
  | first :: second :: rest => exact refl _
  | [payload] =>
      by_cases quoted : constructor = declaration.quoteConstructor
      · subst quoted
        cases exposed : exposedDrop? declaration payload with
        | none =>
            simp only [finishResolveApply, if_true, exposed]
            exact refl _
        | some name =>
            simp only [finishResolveApply, if_true, exposed]
            have leaves := (exposedDrop?_eq_some_iff (declaration := declaration)).mp exposed
            have toDrop : congruence.rel payload (.apply declaration.dropConstructor [name]) := by
              have related := congruence.related_parallelLeaves payload
              rw [leaves] at related
              exact congruence.equivalence.trans related (congruence.parallel_single _)
            exact congruence.equivalence.trans
              (congruence.apply_congr _ (.cons toDrop .nil)) (congruence.quote_drop name)
      · simp only [finishResolveApply, quoted, if_false]
        exact refl _

/-- **Every pattern is related to its resolution.** -/
theorem related_resolveQuotes (pattern : Pattern) :
    congruence.rel pattern (resolveQuotes declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => exact congruence.equivalence.refl _
  | hfvar name => exact congruence.equivalence.refl _
  | hlambda binder body related => exact congruence.lambda_congr binder related
  | hmultiLambda arity binders body related =>
      exact congruence.multiLambda_congr arity binders related
  | hsubst body value relatedBody relatedValue =>
      exact congruence.subst_congr relatedBody relatedValue
  | hcollection kind elements rest related =>
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      exact congruence.collection_congr kind rest
        (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr related))
  | happly constructor arguments related =>
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      exact congruence.equivalence.trans
        (congruence.apply_congr constructor
          (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr related)))
        (congruence.related_finish constructor _)

end QuoteDropCongruence

end Mettapedia.OSLF.MeTTaIL.ReflectiveResolution
