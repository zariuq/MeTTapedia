import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalRootDichotomy

/-!
# Canonical alignment with explicit collapsing stops

Equal reflective canonical forms agree constructor-by-constructor until a
Quote or bare-parallel root is reached on either side.  Those are precisely
the roots at which canonicalization may absorb, splice, sort, or collapse, so
clients must handle the remaining pair explicitly.

`CanonicalStopAligned` records this descent without committing to any client
semantics at stopped pairs.  Its producer is entirely syntax-generic.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

mutual
  /-- Structural agreement away from client-selected stops.  Rigid
  application and collection constructors cannot cross the two reflective
  root-changing forms, while a leaf delegates its entire pair to `stop`. -/
  inductive CanonicalStopAligned
      (declaration : ReflectivePresentationDecl)
      (stop : Pattern → Pattern → Prop) : Pattern → Pattern → Prop where
    | leaf {left right : Pattern} (given : stop left right) :
        CanonicalStopAligned declaration stop left right
    | bvar (index : Nat) :
        CanonicalStopAligned declaration stop (.bvar index) (.bvar index)
    | fvar (name : String) :
        CanonicalStopAligned declaration stop (.fvar name) (.fvar name)
    | apply {constructor : String}
        (ne : constructor ≠ declaration.quoteConstructor)
        {leftArguments rightArguments : List Pattern}
        (arguments : CanonicalStopAlignedList declaration stop
          leftArguments rightArguments) :
        CanonicalStopAligned declaration stop
          (.apply constructor leftArguments)
          (.apply constructor rightArguments)
    | lambda (binder : Option String) {leftBody rightBody : Pattern}
        (body : CanonicalStopAligned declaration stop leftBody rightBody) :
        CanonicalStopAligned declaration stop (.lambda binder leftBody)
          (.lambda binder rightBody)
    | multiLambda (arity : Nat) (binders : List String)
        {leftBody rightBody : Pattern}
        (body : CanonicalStopAligned declaration stop leftBody rightBody) :
        CanonicalStopAligned declaration stop
          (.multiLambda arity binders leftBody)
          (.multiLambda arity binders rightBody)
    | subst {leftBody rightBody leftReplacement rightReplacement : Pattern}
        (body : CanonicalStopAligned declaration stop leftBody rightBody)
        (replacement : CanonicalStopAligned declaration stop leftReplacement
          rightReplacement) :
        CanonicalStopAligned declaration stop
          (.subst leftBody leftReplacement)
          (.subst rightBody rightReplacement)
    | collection {collectionType : CollType}
        (ne : collectionType ≠ declaration.parallelCollection)
        {leftElements rightElements : List Pattern}
        (elements : CanonicalStopAlignedList declaration stop
          leftElements rightElements) :
        CanonicalStopAligned declaration stop
          (.collection collectionType leftElements none)
          (.collection collectionType rightElements none)
    | collectionRest (collectionType : CollType) (rest : String)
        {leftElements rightElements : List Pattern}
        (elements : CanonicalStopAlignedList declaration stop
          leftElements rightElements) :
        CanonicalStopAligned declaration stop
          (.collection collectionType leftElements (some rest))
          (.collection collectionType rightElements (some rest))

  /-- Pointwise companion of `CanonicalStopAligned`. -/
  inductive CanonicalStopAlignedList
      (declaration : ReflectivePresentationDecl)
      (stop : Pattern → Pattern → Prop) :
      List Pattern → List Pattern → Prop where
    | nil : CanonicalStopAlignedList declaration stop [] []
    | cons {leftHead rightHead : Pattern}
        {leftTail rightTail : List Pattern}
        (head : CanonicalStopAligned declaration stop leftHead rightHead)
        (tail : CanonicalStopAlignedList declaration stop leftTail rightTail) :
        CanonicalStopAlignedList declaration stop
          (leftHead :: leftTail) (rightHead :: rightTail)
end

/-- Equal canonical forms produce a rigid descent that stops exactly where
canonicalization may change a root. -/
theorem canonicalStopAligned_of_canonicalize_eq
    (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (equal : canonicalize declaration left = canonicalize declaration right) :
    CanonicalStopAligned declaration
      (fun candidateLeft candidateRight =>
        (CollapsingRoot declaration candidateLeft ∨
          CollapsingRoot declaration candidateRight) ∧
        canonicalize declaration candidateLeft =
          canonicalize declaration candidateRight)
      left right := by
  generalize measureEq : sizeOf left + sizeOf right = measure
  induction measure using Nat.strong_induction_on generalizing left right with
  | h measure smaller =>
      subst measure
      rcases canonicalize_eq_root_cases declaration equal with
          leftCollapsing | rightCollapsing | aligned
      · exact .leaf ⟨Or.inl leftCollapsing, equal⟩
      · exact .leaf ⟨Or.inr rightCollapsing, equal⟩
      · have alignChildren : ∀ {leftChildren rightChildren : List Pattern},
            List.Forall₂
                (fun leftChild rightChild =>
                  canonicalize declaration leftChild =
                    canonicalize declaration rightChild)
                leftChildren rightChildren →
            (∀ child ∈ leftChildren, sizeOf child < sizeOf left) →
            (∀ child ∈ rightChildren, sizeOf child < sizeOf right) →
            CanonicalStopAlignedList declaration
              (fun candidateLeft candidateRight =>
                (CollapsingRoot declaration candidateLeft ∨
                  CollapsingRoot declaration candidateRight) ∧
                canonicalize declaration candidateLeft =
                  canonicalize declaration candidateRight)
              leftChildren rightChildren := by
          intro leftChildren rightChildren children
          induction children with
          | nil =>
              intro _ _
              exact .nil
          | @cons leftHead rightHead leftTail rightTail head tail tailAligned =>
              intro leftBound rightBound
              refine CanonicalStopAlignedList.cons ?_ (tailAligned ?_ ?_)
              · apply smaller (sizeOf leftHead + sizeOf rightHead)
                · have leftHeadBound := leftBound leftHead (by simp)
                  have rightHeadBound := rightBound rightHead (by simp)
                  omega
                · exact head
                · rfl
              · intro child membership
                exact leftBound child (by simp [membership])
              · intro child membership
                exact rightBound child (by simp [membership])
        cases aligned with
        | bvar index => exact .bvar index
        | fvar name => exact .fvar name
        | @apply constructor ne leftArguments rightArguments children =>
            refine CanonicalStopAligned.apply ne
              (alignChildren children ?_ ?_)
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
        | @lambda binder leftBody rightBody body =>
            refine CanonicalStopAligned.lambda binder ?_
            apply smaller (sizeOf leftBody + sizeOf rightBody)
            · simp_wf
              omega
            · exact body
            · rfl
        | @multiLambda arity binders leftBody rightBody body =>
            refine CanonicalStopAligned.multiLambda arity binders ?_
            apply smaller (sizeOf leftBody + sizeOf rightBody)
            · simp_wf
              omega
            · exact body
            · rfl
        | @subst leftBody rightBody leftReplacement rightReplacement body
            replacement =>
            refine CanonicalStopAligned.subst ?_ ?_
            · apply smaller (sizeOf leftBody + sizeOf rightBody)
              · simp_wf
                omega
              · exact body
              · rfl
            · apply smaller (sizeOf leftReplacement + sizeOf rightReplacement)
              · simp_wf
                omega
              · exact replacement
              · rfl
        | @collection collectionType ne leftElements rightElements children =>
            refine CanonicalStopAligned.collection ne
              (alignChildren children ?_ ?_)
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
        | @collectionRest collectionType rest leftElements rightElements
            children =>
            refine CanonicalStopAligned.collectionRest collectionType rest
              (alignChildren children ?_ ?_)
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega

/-- Equal canonical forms strictly below a fixed parent measure produce a
stopped alignment whose every delegated pair retains that same strict bound.

This is the measure-carrying form used by clients that discharge stops by
well-founded recursion.  The bound is structural: it is propagated through
rigid constructors and is never reconstructed from constructor names. -/
theorem canonicalStopAligned_of_canonicalize_eq_below
    (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (equal : canonicalize declaration left = canonicalize declaration right)
    {parentMeasure : Nat}
    (below : sizeOf left + sizeOf right < parentMeasure) :
    CanonicalStopAligned declaration
      (fun candidateLeft candidateRight =>
        ((CollapsingRoot declaration candidateLeft ∨
            CollapsingRoot declaration candidateRight) ∧
          canonicalize declaration candidateLeft =
            canonicalize declaration candidateRight) ∧
        sizeOf candidateLeft + sizeOf candidateRight < parentMeasure)
      left right := by
  generalize measureEq : sizeOf left + sizeOf right = measure
  induction measure using Nat.strong_induction_on generalizing left right with
  | h measure smaller =>
      subst measure
      rcases canonicalize_eq_root_cases declaration equal with
          leftCollapsing | rightCollapsing | aligned
      · exact .leaf ⟨⟨Or.inl leftCollapsing, equal⟩, below⟩
      · exact .leaf ⟨⟨Or.inr rightCollapsing, equal⟩, below⟩
      · have alignChildren : ∀ {leftChildren rightChildren : List Pattern},
            List.Forall₂
                (fun leftChild rightChild =>
                  canonicalize declaration leftChild =
                    canonicalize declaration rightChild)
                leftChildren rightChildren →
            (∀ child ∈ leftChildren, sizeOf child < sizeOf left) →
            (∀ child ∈ rightChildren, sizeOf child < sizeOf right) →
            CanonicalStopAlignedList declaration
              (fun candidateLeft candidateRight =>
                ((CollapsingRoot declaration candidateLeft ∨
                    CollapsingRoot declaration candidateRight) ∧
                  canonicalize declaration candidateLeft =
                    canonicalize declaration candidateRight) ∧
                sizeOf candidateLeft + sizeOf candidateRight < parentMeasure)
              leftChildren rightChildren := by
          intro leftChildren rightChildren children
          induction children with
          | nil =>
              intro _ _
              exact .nil
          | @cons leftHead rightHead leftTail rightTail head tail tailAligned =>
              intro leftBound rightBound
              refine CanonicalStopAlignedList.cons ?_ (tailAligned ?_ ?_)
              · apply smaller (sizeOf leftHead + sizeOf rightHead)
                · have leftHeadBound := leftBound leftHead (by simp)
                  have rightHeadBound := rightBound rightHead (by simp)
                  omega
                · exact head
                · have leftHeadBound := leftBound leftHead (by simp)
                  have rightHeadBound := rightBound rightHead (by simp)
                  omega
                · rfl
              · intro child membership
                exact leftBound child (by simp [membership])
              · intro child membership
                exact rightBound child (by simp [membership])
        cases aligned with
        | bvar index => exact .bvar index
        | fvar name => exact .fvar name
        | @apply constructor ne leftArguments rightArguments children =>
            refine CanonicalStopAligned.apply ne
              (alignChildren children ?_ ?_)
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
        | @lambda binder leftBody rightBody body =>
            refine CanonicalStopAligned.lambda binder ?_
            apply smaller (sizeOf leftBody + sizeOf rightBody)
            · simp_wf
              omega
            · exact body
            · exact Nat.lt_trans (by simp_wf; omega) below
            · rfl
        | @multiLambda arity binders leftBody rightBody body =>
            refine CanonicalStopAligned.multiLambda arity binders ?_
            apply smaller (sizeOf leftBody + sizeOf rightBody)
            · simp_wf
              omega
            · exact body
            · exact Nat.lt_trans (by simp_wf; omega) below
            · rfl
        | @subst leftBody rightBody leftReplacement rightReplacement body
            replacement =>
            refine CanonicalStopAligned.subst ?_ ?_
            · apply smaller (sizeOf leftBody + sizeOf rightBody)
              · simp_wf
                omega
              · exact body
              · exact Nat.lt_trans (by simp_wf; omega) below
              · rfl
            · apply smaller (sizeOf leftReplacement + sizeOf rightReplacement)
              · simp_wf
                omega
              · exact replacement
              · exact Nat.lt_trans (by simp_wf; omega) below
              · rfl
        | @collection collectionType ne leftElements rightElements children =>
            refine CanonicalStopAligned.collection ne
              (alignChildren children ?_ ?_)
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
        | @collectionRest collectionType rest leftElements rightElements
            children =>
            refine CanonicalStopAligned.collectionRest collectionType rest
              (alignChildren children ?_ ?_)
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega
            · intro child membership
              have childBound := List.sizeOf_lt_of_mem membership
              simp_wf
              omega

/-- A root-aligned pair admits canonical stopped descent in which every
delegated collapsing pair is strictly smaller than the original pair.

Unlike the unrestricted canonical-equality producer, this theorem cannot
delegate the whole input pair as a stop: the supplied root alignment forces
one rigid descent step first. -/
theorem canonicalStopAligned_of_root_aligned
    (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (aligned : CanonicalRootAligned declaration left right) :
    CanonicalStopAligned declaration
      (fun candidateLeft candidateRight =>
        ((CollapsingRoot declaration candidateLeft ∨
            CollapsingRoot declaration candidateRight) ∧
          canonicalize declaration candidateLeft =
            canonicalize declaration candidateRight) ∧
        sizeOf candidateLeft + sizeOf candidateRight <
          sizeOf left + sizeOf right)
      left right := by
  have alignChildren : ∀ {leftChildren rightChildren : List Pattern},
        List.Forall₂
            (fun leftChild rightChild =>
              canonicalize declaration leftChild =
                canonicalize declaration rightChild)
            leftChildren rightChildren →
        (∀ child ∈ leftChildren, sizeOf child < sizeOf left) →
        (∀ child ∈ rightChildren, sizeOf child < sizeOf right) →
        CanonicalStopAlignedList declaration
          (fun candidateLeft candidateRight =>
            ((CollapsingRoot declaration candidateLeft ∨
                CollapsingRoot declaration candidateRight) ∧
              canonicalize declaration candidateLeft =
                canonicalize declaration candidateRight) ∧
            sizeOf candidateLeft + sizeOf candidateRight <
              sizeOf left + sizeOf right)
          leftChildren rightChildren := by
      intro leftChildren rightChildren children
      induction children with
      | nil =>
          intro _ _
          exact .nil
      | @cons leftHead rightHead leftTail rightTail head tail tailAligned =>
          intro leftBound rightBound
          refine .cons ?_ (tailAligned ?_ ?_)
          · apply canonicalStopAligned_of_canonicalize_eq_below declaration head
            have leftHeadBound := leftBound leftHead (by simp)
            have rightHeadBound := rightBound rightHead (by simp)
            omega
          · intro child membership
            exact leftBound child (by simp [membership])
          · intro child membership
            exact rightBound child (by simp [membership])
  cases aligned with
  | bvar index => exact .bvar index
  | fvar name => exact .fvar name
  | @apply constructor ne leftArguments rightArguments children =>
      refine .apply ne (alignChildren children ?_ ?_)
      · intro child membership
        have childBound := List.sizeOf_lt_of_mem membership
        simp_wf
        omega
      · intro child membership
        have childBound := List.sizeOf_lt_of_mem membership
        simp_wf
        omega
  | @lambda binder leftBody rightBody body =>
      refine .lambda binder
        (canonicalStopAligned_of_canonicalize_eq_below declaration body ?_)
      simp_wf
      omega
  | @multiLambda arity binders leftBody rightBody body =>
      refine .multiLambda arity binders
        (canonicalStopAligned_of_canonicalize_eq_below declaration body ?_)
      simp_wf
      omega
  | @subst leftBody rightBody leftReplacement rightReplacement body
      replacement =>
      refine .subst
        (canonicalStopAligned_of_canonicalize_eq_below declaration body ?_)
        (canonicalStopAligned_of_canonicalize_eq_below declaration replacement ?_)
      · simp_wf
        omega
      · simp_wf
        omega
  | @collection collectionType ne leftElements rightElements children =>
      refine .collection ne (alignChildren children ?_ ?_)
      · intro child membership
        have childBound := List.sizeOf_lt_of_mem membership
        simp_wf
        omega
      · intro child membership
        have childBound := List.sizeOf_lt_of_mem membership
        simp_wf
        omega
  | @collectionRest collectionType rest leftElements rightElements children =>
      refine .collectionRest collectionType rest
        (alignChildren children ?_ ?_)
      · intro child membership
        have childBound := List.sizeOf_lt_of_mem membership
        simp_wf
        omega
      · intro child membership
        have childBound := List.sizeOf_lt_of_mem membership
        simp_wf
        omega

mutual
  /-- A stopped structural alignment preserves ordinary canonical form when
  every delegated stop does.  This is the eliminator clients use to recover
  the canonical equality carried through a provenance-preserving descent. -/
  def CanonicalStopAligned.canonicalize_eq
      (declaration : ReflectivePresentationDecl)
      {stop : Pattern → Pattern → Prop}
      (stopCanonical : ∀ {left right}, stop left right →
        canonicalize declaration left = canonicalize declaration right) :
      ∀ {left right}, CanonicalStopAligned declaration stop left right →
        canonicalize declaration left = canonicalize declaration right
    | _, _, .leaf given => stopCanonical given
    | _, _, .bvar _ => rfl
    | _, _, .fvar _ => rfl
    | _, _, @CanonicalStopAligned.apply _ _ constructor ne _ _ arguments =>
        by
          rw [canonicalize_apply_of_ne_quote declaration ne,
            canonicalize_apply_of_ne_quote declaration ne]
          exact congrArg (Pattern.apply constructor)
            (arguments.canonicalizeList_eq declaration stopCanonical)
    | _, _, .lambda binder body =>
        congrArg (Pattern.lambda binder)
          (body.canonicalize_eq declaration stopCanonical)
    | _, _, .multiLambda arity binders body =>
        congrArg (Pattern.multiLambda arity binders)
          (body.canonicalize_eq declaration stopCanonical)
    | _, _, .subst body replacement =>
        congrArg₂ Pattern.subst
          (body.canonicalize_eq declaration stopCanonical)
          (replacement.canonicalize_eq declaration stopCanonical)
    | _, _, @CanonicalStopAligned.collection _ _ collectionType ne _ _
        elements => by
          rw [canonicalize_collection_of_ne_parallel declaration ne,
            canonicalize_collection_of_ne_parallel declaration ne]
          exact congrArg
            (fun values => Pattern.collection collectionType values none)
            (elements.canonicalizeList_eq declaration stopCanonical)
    | _, _, .collectionRest collectionType rest elements => by
        rw [canonicalize_collection_rest, canonicalize_collection_rest]
        exact congrArg
          (fun values => Pattern.collection collectionType values (some rest))
          (elements.canonicalizeList_eq declaration stopCanonical)

  /-- Listwise companion of `CanonicalStopAligned.canonicalize_eq`. -/
  def CanonicalStopAlignedList.canonicalizeList_eq
      (declaration : ReflectivePresentationDecl)
      {stop : Pattern → Pattern → Prop}
      (stopCanonical : ∀ {left right}, stop left right →
        canonicalize declaration left = canonicalize declaration right) :
      ∀ {left right}, CanonicalStopAlignedList declaration stop left right →
        left.map (canonicalize declaration) =
          right.map (canonicalize declaration)
    | _, _, .nil => rfl
    | _, _, .cons head tail =>
        congrArg₂ List.cons
          (head.canonicalize_eq declaration stopCanonical)
          (tail.canonicalizeList_eq declaration stopCanonical)
end

/-! ## Canary properties -/

/-- Equal rigid variables take the rigid constructor rather than a semantic
stop. -/
example (declaration : ReflectivePresentationDecl) (name : String) :
    CanonicalStopAligned declaration
      (fun left right => canonicalize declaration left =
        canonicalize declaration right)
      (.fvar name) (.fvar name) :=
  .fvar name

/-- A free variable and a bound variable cannot be aligned when the client
does not designate that pair as a semantic stop. -/
theorem not_canonicalStopAligned_fvar_bvar
    (declaration : ReflectivePresentationDecl)
    (stop : Pattern → Pattern → Prop) (name : String) (index : Nat)
    (notStop : ¬ stop (.fvar name) (.bvar index)) :
    ¬ CanonicalStopAligned declaration stop (.fvar name) (.bvar index) := by
  intro aligned
  cases aligned with
  | leaf given => exact notStop given

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
