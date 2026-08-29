import Mettapedia.GSLT.Core.Composition
import Mathlib.Logic.Equiv.List
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

set_option linter.dupNamespace false

/-!
# Structural isomorphisms of GSLTs

A structural isomorphism is a bijection of terms that preserves and reflects
both authored equations and one-step rewrites.  It is stronger than behavioral
equivalence: it identifies two presentations of the same operational theory
without erasing the distinction between equations and computation.

The constructions here supply the coherence maps needed by compositional GSLT
programming.  In particular, disjoint sum is associative up to structural
isomorphism, and every structural isomorphism lifts through the free-document
construction.
-/

namespace Mettapedia.GSLT.GSLT

universe u v w x

/-- A bijective change of GSLT syntax that preserves and reflects equations
and primitive computation separately. -/
structure StructuralIsomorphism (source target : GSLT) where
  termEquiv : source.Term ≃ target.Term
  equiv_iff : ∀ sourceTerm targetTerm,
    target.Equiv (termEquiv sourceTerm) (termEquiv targetTerm) ↔
      source.Equiv sourceTerm targetTerm
  step_iff : ∀ sourceTerm targetTerm,
    target.Step (termEquiv sourceTerm) (termEquiv targetTerm) ↔
      source.Step sourceTerm targetTerm

/-- The empty theory is the neutral object for disjoint composition.  It has
no terms, hence no equations or rewrites beyond the vacuous laws. -/
abbrev disjointSumUnit : GSLT where
  Term := Empty
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ impossible
    exact impossible.elim
  rewrites_resp_right := by
    intro _ _ _ impossible _
    exact impossible.elim

namespace StructuralIsomorphism

/-- Every structural isomorphism is, in particular, a structural embedding. -/
def toEmbedding {source target : GSLT}
    (isomorphism : StructuralIsomorphism source target) :
    Embedding source target where
  toFun := isomorphism.termEquiv
  injective := isomorphism.termEquiv.injective
  equiv_iff := isomorphism.equiv_iff
  step_iff := isomorphism.step_iff

/-- Identity change of syntax. -/
def refl (system : GSLT) : StructuralIsomorphism system system where
  termEquiv := Equiv.refl _
  equiv_iff := fun _ _ => Iff.rfl
  step_iff := fun _ _ => Iff.rfl

/-- Reverse a structural change of syntax. -/
def symm {source target : GSLT}
    (isomorphism : StructuralIsomorphism source target) :
    StructuralIsomorphism target source where
  termEquiv := isomorphism.termEquiv.symm
  equiv_iff := by
    intro sourceTerm targetTerm
    simpa using
      (isomorphism.equiv_iff
        (isomorphism.termEquiv.symm sourceTerm)
        (isomorphism.termEquiv.symm targetTerm)).symm
  step_iff := by
    intro sourceTerm targetTerm
    simpa using
      (isomorphism.step_iff
        (isomorphism.termEquiv.symm sourceTerm)
        (isomorphism.termEquiv.symm targetTerm)).symm

/-- Compose structural changes of syntax. -/
def trans {first second third : GSLT}
    (earlier : StructuralIsomorphism first second)
    (later : StructuralIsomorphism second third) :
    StructuralIsomorphism first third where
  termEquiv := earlier.termEquiv.trans later.termEquiv
  equiv_iff := by
    intro sourceTerm targetTerm
    exact (later.equiv_iff _ _).trans (earlier.equiv_iff _ _)
  step_iff := by
    intro sourceTerm targetTerm
    exact (later.step_iff _ _).trans (earlier.step_iff _ _)

/-- Structural isomorphisms are determined by their action on terms.  The
equation- and step-compatibility fields are propositions. -/
@[ext] theorem ext {source target : GSLT}
    {first second : StructuralIsomorphism source target}
    (termEquiv : first.termEquiv = second.termEquiv) : first = second := by
  cases first
  cases second
  cases termEquiv
  rfl

@[simp] theorem refl_apply (system : GSLT) (term : system.Term) :
    (refl system).termEquiv term = term :=
  rfl

@[simp] theorem symm_apply_apply {source target : GSLT}
    (isomorphism : StructuralIsomorphism source target)
    (term : source.Term) :
    isomorphism.symm.termEquiv (isomorphism.termEquiv term) = term :=
  isomorphism.termEquiv.left_inv term

@[simp] theorem apply_symm_apply {source target : GSLT}
    (isomorphism : StructuralIsomorphism source target)
    (term : target.Term) :
    isomorphism.termEquiv (isomorphism.symm.termEquiv term) = term :=
  isomorphism.termEquiv.right_inv term

/-! ## Functorial action of disjoint composition -/

/-- Disjoint composition acts independently on structural isomorphisms of
both components. -/
def disjointSumMap
    {leftSource leftTarget rightSource rightTarget : GSLT}
    (left : StructuralIsomorphism leftSource leftTarget)
    (right : StructuralIsomorphism rightSource rightTarget) :
    StructuralIsomorphism
      (disjointSum leftSource rightSource)
      (disjointSum leftTarget rightTarget) where
  termEquiv := Equiv.sumCongr left.termEquiv right.termEquiv
  equiv_iff := by
    intro source target
    rcases source with source | source <;>
      rcases target with target | target
    · constructor
      · intro equivalent
        cases equivalent with
        | left equivalent =>
            exact .left ((left.equiv_iff source target).1 (by simpa using equivalent))
      · intro equivalent
        cases equivalent with
        | left equivalent =>
            exact .left (by
              simpa using (left.equiv_iff source target).2 equivalent)
    · constructor <;> intro impossible <;> cases impossible
    · constructor <;> intro impossible <;> cases impossible
    · constructor
      · intro equivalent
        cases equivalent with
        | right equivalent =>
            exact .right ((right.equiv_iff source target).1 (by simpa using equivalent))
      · intro equivalent
        cases equivalent with
        | right equivalent =>
            exact .right (by
              simpa using (right.equiv_iff source target).2 equivalent)
  step_iff := by
    intro source target
    rcases source with source | source <;>
      rcases target with target | target
    · constructor
      · intro step
        cases step with
        | left step =>
            exact .left ((left.step_iff source target).1 (by simpa using step))
      · intro step
        cases step with
        | left step =>
            exact .left (by simpa using (left.step_iff source target).2 step)
    · constructor <;> intro impossible <;> cases impossible
    · constructor <;> intro impossible <;> cases impossible
    · constructor
      · intro step
        cases step with
        | right step =>
            exact .right ((right.step_iff source target).1 (by simpa using step))
      · intro step
        cases step with
        | right step =>
            exact .right (by simpa using (right.step_iff source target).2 step)

@[simp] theorem disjointSumMap_refl (left right : GSLT) :
    disjointSumMap (refl left) (refl right) = refl (disjointSum left right) := by
  apply ext
  apply Equiv.ext
  intro term
  cases term <;> rfl

theorem disjointSumMap_trans
    {firstLeft secondLeft thirdLeft firstRight secondRight thirdRight : GSLT}
    (leftEarlier : StructuralIsomorphism firstLeft secondLeft)
    (leftLater : StructuralIsomorphism secondLeft thirdLeft)
    (rightEarlier : StructuralIsomorphism firstRight secondRight)
    (rightLater : StructuralIsomorphism secondRight thirdRight) :
    (disjointSumMap leftEarlier rightEarlier).trans
        (disjointSumMap leftLater rightLater) =
      disjointSumMap (leftEarlier.trans leftLater)
        (rightEarlier.trans rightLater) := by
  apply ext
  apply Equiv.ext
  intro term
  cases term <;> rfl

/-! ## Lifting through free documents -/

/-- Pointwise document equations are preserved by a structural isomorphism. -/
theorem map_documentEquiv {source target : GSLT}
    (isomorphism : StructuralIsomorphism source target) {left right}
    (equivalent : DocumentEquiv source left right) :
    DocumentEquiv target
      (left.map isomorphism.termEquiv)
      (right.map isomorphism.termEquiv) := by
  induction equivalent with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons ((isomorphism.equiv_iff _ _).2 head) inductionHypothesis

/-- A primitive document step is preserved pointwise. -/
theorem map_rawDocumentStep {source target : GSLT}
    (isomorphism : StructuralIsomorphism source target) {left right}
    (step : RawDocumentStep source left right) :
    RawDocumentStep target
      (left.map isomorphism.termEquiv)
      (right.map isomorphism.termEquiv) := by
  induction step with
  | head rewrite => exact .head ((isomorphism.step_iff _ _).2 rewrite)
  | tail _ inductionHypothesis => exact .tail inductionHypothesis

/-- Equation-closed document rewriting is preserved pointwise. -/
theorem map_documentStep {source target : GSLT}
    (isomorphism : StructuralIsomorphism source target) {left right}
    (step : DocumentStep source left right) :
    DocumentStep target
      (left.map isomorphism.termEquiv)
      (right.map isomorphism.termEquiv) := by
  rcases step with
    ⟨middleLeft, middleRight, leftMiddle, rewrite, middleRightRight⟩
  exact ⟨middleLeft.map isomorphism.termEquiv,
    middleRight.map isomorphism.termEquiv,
    isomorphism.map_documentEquiv leftMiddle,
    isomorphism.map_rawDocumentStep rewrite,
    isomorphism.map_documentEquiv middleRightRight⟩

/-- Free finite documents preserve structural isomorphisms. -/
def freeDocument {source target : GSLT}
    (isomorphism : StructuralIsomorphism source target) :
    StructuralIsomorphism (GSLT.freeDocument source)
      (GSLT.freeDocument target) where
  termEquiv := Equiv.listEquivOfEquiv isomorphism.termEquiv
  equiv_iff := by
    intro left right
    constructor
    · intro equivalent
      have mappedBack := isomorphism.symm.map_documentEquiv equivalent
      change DocumentEquiv source
        (List.map isomorphism.termEquiv.symm
          (List.map isomorphism.termEquiv left))
        (List.map isomorphism.termEquiv.symm
          (List.map isomorphism.termEquiv right)) at mappedBack
      rw [List.map_map, isomorphism.termEquiv.symm_comp_self, List.map_id,
        List.map_map, isomorphism.termEquiv.symm_comp_self, List.map_id]
        at mappedBack
      exact mappedBack
    · exact isomorphism.map_documentEquiv
  step_iff := by
    intro left right
    constructor
    · intro step
      have mappedBack := isomorphism.symm.map_documentStep step
      change DocumentStep source
        (List.map isomorphism.termEquiv.symm
          (List.map isomorphism.termEquiv left))
        (List.map isomorphism.termEquiv.symm
          (List.map isomorphism.termEquiv right)) at mappedBack
      rw [List.map_map, isomorphism.termEquiv.symm_comp_self, List.map_id,
        List.map_map, isomorphism.termEquiv.symm_comp_self, List.map_id]
        at mappedBack
      exact mappedBack
    · exact isomorphism.map_documentStep

@[simp] theorem freeDocument_refl (system : GSLT) :
    (refl system).freeDocument = refl (GSLT.freeDocument system) := by
  apply ext
  apply Equiv.ext
  intro document
  change List.map (fun term : system.Term => term) document = document
  simp

theorem freeDocument_trans {first second third : GSLT}
    (earlier : StructuralIsomorphism first second)
    (later : StructuralIsomorphism second third) :
    (earlier.trans later).freeDocument =
      earlier.freeDocument.trans later.freeDocument := by
  apply ext
  apply Equiv.ext
  intro document
  change List.map (fun term => later.termEquiv (earlier.termEquiv term)) document =
    List.map later.termEquiv (List.map earlier.termEquiv document)
  rw [List.map_map]
  rfl

/-! ## Coherence of disjoint sum -/

private theorem disjointSumAssoc_equiv_forward
    (first second third : GSLT) {source target}
    (equivalent : (disjointSum (disjointSum first second) third).Equiv
      source target) :
    (disjointSum first (disjointSum second third)).Equiv
      (Equiv.sumAssoc first.Term second.Term third.Term source)
      (Equiv.sumAssoc first.Term second.Term third.Term target) := by
  cases equivalent with
  | left equivalent =>
      cases equivalent with
      | left equivalent => exact .left equivalent
      | right equivalent => exact .right (.left equivalent)
  | right equivalent => exact .right (.right equivalent)

private theorem disjointSumAssoc_equiv_backward
    (first second third : GSLT) {source target}
    (equivalent : (disjointSum first (disjointSum second third)).Equiv
      source target) :
    (disjointSum (disjointSum first second) third).Equiv
      ((Equiv.sumAssoc first.Term second.Term third.Term).symm source)
      ((Equiv.sumAssoc first.Term second.Term third.Term).symm target) := by
  cases equivalent with
  | left equivalent => exact .left (.left equivalent)
  | right equivalent =>
      cases equivalent with
      | left equivalent => exact .left (.right equivalent)
      | right equivalent => exact .right equivalent

private theorem disjointSumAssoc_step_forward
    (first second third : GSLT) {source target}
    (step : (disjointSum (disjointSum first second) third).Step source target) :
    (disjointSum first (disjointSum second third)).Step
      (Equiv.sumAssoc first.Term second.Term third.Term source)
      (Equiv.sumAssoc first.Term second.Term third.Term target) := by
  cases step with
  | left step =>
      cases step with
      | left step => exact .left step
      | right step => exact .right (.left step)
  | right step => exact .right (.right step)

private theorem disjointSumAssoc_step_backward
    (first second third : GSLT) {source target}
    (step : (disjointSum first (disjointSum second third)).Step source target) :
    (disjointSum (disjointSum first second) third).Step
      ((Equiv.sumAssoc first.Term second.Term third.Term).symm source)
      ((Equiv.sumAssoc first.Term second.Term third.Term).symm target) := by
  cases step with
  | left step => exact .left (.left step)
  | right step =>
      cases step with
      | left step => exact .left (.right step)
      | right step => exact .right step

/-- Disjoint sum is associative up to a structural GSLT isomorphism. -/
def disjointSumAssociator (first second third : GSLT) :
    StructuralIsomorphism
      (disjointSum (disjointSum first second) third)
      (disjointSum first (disjointSum second third)) where
  termEquiv := Equiv.sumAssoc first.Term second.Term third.Term
  equiv_iff := by
    intro source target
    constructor
    · intro equivalent
      have mappedBack :=
        disjointSumAssoc_equiv_backward first second third equivalent
      have sourceRoundTrip :=
        (Equiv.sumAssoc first.Term second.Term third.Term).left_inv source
      have targetRoundTrip :=
        (Equiv.sumAssoc first.Term second.Term third.Term).left_inv target
      change (disjointSum (disjointSum first second) third).Equiv
        ((Equiv.sumAssoc first.Term second.Term third.Term).invFun
          ((Equiv.sumAssoc first.Term second.Term third.Term).toFun source))
        ((Equiv.sumAssoc first.Term second.Term third.Term).invFun
          ((Equiv.sumAssoc first.Term second.Term third.Term).toFun target))
          at mappedBack
      rw [sourceRoundTrip, targetRoundTrip] at mappedBack
      exact mappedBack
    · exact disjointSumAssoc_equiv_forward first second third
  step_iff := by
    intro source target
    constructor
    · intro step
      have mappedBack :=
        disjointSumAssoc_step_backward first second third step
      have sourceRoundTrip :=
        (Equiv.sumAssoc first.Term second.Term third.Term).left_inv source
      have targetRoundTrip :=
        (Equiv.sumAssoc first.Term second.Term third.Term).left_inv target
      change (disjointSum (disjointSum first second) third).Step
        ((Equiv.sumAssoc first.Term second.Term third.Term).invFun
          ((Equiv.sumAssoc first.Term second.Term third.Term).toFun source))
        ((Equiv.sumAssoc first.Term second.Term third.Term).invFun
          ((Equiv.sumAssoc first.Term second.Term third.Term).toFun target))
          at mappedBack
      rw [sourceRoundTrip, targetRoundTrip] at mappedBack
      exact mappedBack
    · exact disjointSumAssoc_step_forward first second third

private def disjointSumLeftUnitorEquiv (system : GSLT) :
    (disjointSum disjointSumUnit system).Term ≃ system.Term where
  toFun
    | .inl impossible => Empty.elim impossible
    | .inr term => term
  invFun := Sum.inr
  left_inv := by
    intro term
    rcases term with impossible | term
    · exact Empty.elim impossible
    · rfl
  right_inv := fun _ => rfl

@[simp] private theorem disjointSumLeftUnitorEquiv_inr
    (system : GSLT) (term : system.Term) :
    disjointSumLeftUnitorEquiv system (Sum.inr term) = term :=
  rfl

private def disjointSumRightUnitorEquiv (system : GSLT) :
    (disjointSum system disjointSumUnit).Term ≃ system.Term where
  toFun
    | .inl term => term
    | .inr impossible => Empty.elim impossible
  invFun := Sum.inl
  left_inv := by
    intro term
    rcases term with term | impossible
    · rfl
    · exact Empty.elim impossible
  right_inv := fun _ => rfl

@[simp] private theorem disjointSumRightUnitorEquiv_inl
    (system : GSLT) (term : system.Term) :
    disjointSumRightUnitorEquiv system (Sum.inl term) = term :=
  rfl

/-- The empty theory is a left unit for disjoint composition. -/
def disjointSumLeftUnitor (system : GSLT) :
    StructuralIsomorphism (disjointSum disjointSumUnit system) system where
  termEquiv := disjointSumLeftUnitorEquiv system
  equiv_iff := by
    intro source target
    rcases source with source | source
    · exact Empty.elim source
    · rcases target with target | target
      · exact Empty.elim target
      · constructor
        · intro equivalent
          rw [disjointSumLeftUnitorEquiv_inr,
            disjointSumLeftUnitorEquiv_inr] at equivalent
          exact .right equivalent
        · intro equivalent
          cases equivalent with
          | right equivalent =>
              rw [disjointSumLeftUnitorEquiv_inr,
                disjointSumLeftUnitorEquiv_inr]
              exact equivalent
  step_iff := by
    intro source target
    rcases source with source | source
    · exact Empty.elim source
    · rcases target with target | target
      · exact Empty.elim target
      · constructor
        · intro step
          rw [disjointSumLeftUnitorEquiv_inr,
            disjointSumLeftUnitorEquiv_inr] at step
          exact .right step
        · intro step
          cases step with
          | right step =>
              rw [disjointSumLeftUnitorEquiv_inr,
                disjointSumLeftUnitorEquiv_inr]
              exact step

/-- The empty theory is a right unit for disjoint composition. -/
def disjointSumRightUnitor (system : GSLT) :
    StructuralIsomorphism (disjointSum system disjointSumUnit) system where
  termEquiv := disjointSumRightUnitorEquiv system
  equiv_iff := by
    intro source target
    rcases source with source | source
    · rcases target with target | target
      · constructor
        · intro equivalent
          rw [disjointSumRightUnitorEquiv_inl,
            disjointSumRightUnitorEquiv_inl] at equivalent
          exact .left equivalent
        · intro equivalent
          cases equivalent with
          | left equivalent =>
              rw [disjointSumRightUnitorEquiv_inl,
                disjointSumRightUnitorEquiv_inl]
              exact equivalent
      · exact Empty.elim target
    · exact Empty.elim source
  step_iff := by
    intro source target
    rcases source with source | source
    · rcases target with target | target
      · constructor
        · intro step
          rw [disjointSumRightUnitorEquiv_inl,
            disjointSumRightUnitorEquiv_inl] at step
          exact .left step
        · intro step
          cases step with
          | left step =>
              rw [disjointSumRightUnitorEquiv_inl,
                disjointSumRightUnitorEquiv_inl]
              exact step
      · exact Empty.elim target
    · exact Empty.elim source

/-- Independent GSLT components may be exchanged without changing either
component's equations or primitive computation. -/
def disjointSumBraiding (left right : GSLT) :
    StructuralIsomorphism (disjointSum left right) (disjointSum right left) where
  termEquiv := Equiv.sumComm left.Term right.Term
  equiv_iff := by
    intro source target
    rcases source with source | source <;>
      rcases target with target | target
    · constructor
      · intro equivalent
        exact .left (by cases equivalent with | right equivalent => exact equivalent)
      · intro equivalent
        exact .right (by cases equivalent with | left equivalent => exact equivalent)
    · constructor <;> intro impossible <;> cases impossible
    · constructor <;> intro impossible <;> cases impossible
    · constructor
      · intro equivalent
        exact .right (by cases equivalent with | left equivalent => exact equivalent)
      · intro equivalent
        exact .left (by cases equivalent with | right equivalent => exact equivalent)
  step_iff := by
    intro source target
    rcases source with source | source <;>
      rcases target with target | target
    · constructor
      · intro step
        exact .left (by cases step with | right step => exact step)
      · intro step
        exact .right (by cases step with | left step => exact step)
    · constructor <;> intro impossible <;> cases impossible
    · constructor <;> intro impossible <;> cases impossible
    · constructor
      · intro step
        exact .right (by cases step with | left step => exact step)
      · intro step
        exact .left (by cases step with | right step => exact step)

/-- Braiding twice restores the original composed theory. -/
theorem disjointSumBraiding_involutive (left right : GSLT) :
    (disjointSumBraiding left right).trans (disjointSumBraiding right left) =
      refl (disjointSum left right) := by
  apply ext
  apply Equiv.ext
  intro term
  cases term <;> rfl

/-- Exchanging components is natural in structural changes of syntax. -/
theorem disjointSumBraiding_natural
    {leftSource leftTarget rightSource rightTarget : GSLT}
    (left : StructuralIsomorphism leftSource leftTarget)
    (right : StructuralIsomorphism rightSource rightTarget) :
    (disjointSumMap left right).trans
        (disjointSumBraiding leftTarget rightTarget) =
      (disjointSumBraiding leftSource rightSource).trans
        (disjointSumMap right left) := by
  apply ext
  apply Equiv.ext
  intro term
  cases term <;> rfl

/-- The associator and unitors satisfy the monoidal triangle law. -/
theorem disjointSum_triangle (left right : GSLT) :
    (disjointSumAssociator disjointSumUnit left right).trans
        (disjointSumLeftUnitor (disjointSum left right)) =
      disjointSumMap (disjointSumLeftUnitor left) (refl right) := by
  apply ext
  apply Equiv.ext
  intro term
  rcases term with term | term
  · rcases term with term | term
    · exact Empty.elim term
    · rfl
  · rfl

/-- Reassociation is coherent: the two paths around Mac Lane's pentagon have
the same action on terms and hence are the same structural isomorphism. -/
theorem disjointSum_pentagon (first second third fourth : GSLT) :
    (disjointSumAssociator (disjointSum first second) third fourth).trans
        (disjointSumAssociator first second (disjointSum third fourth)) =
      ((disjointSumMap (disjointSumAssociator first second third)
            (refl fourth)).trans
          (disjointSumAssociator first (disjointSum second third) fourth)).trans
        (disjointSumMap (refl first)
          (disjointSumAssociator second third fourth)) := by
  apply ext
  apply Equiv.ext
  intro term
  rcases term with term | fourthTerm
  · rcases term with term | thirdTerm
    · rcases term with firstTerm | secondTerm <;> rfl
    · rfl
  · rfl

/-- Braiding is coherent with reassociation: exchanging one component with a
pair agrees with exchanging it with each component in turn. -/
theorem disjointSum_hexagon (first second third : GSLT) :
    ((disjointSumAssociator first second third).trans
        (disjointSumBraiding first (disjointSum second third))).trans
      (disjointSumAssociator second third first) =
    ((disjointSumMap (disjointSumBraiding first second) (refl third)).trans
        (disjointSumAssociator second first third)).trans
      (disjointSumMap (refl second) (disjointSumBraiding first third)) := by
  apply ext
  apply Equiv.ext
  intro term
  rcases term with term | thirdTerm
  · rcases term with firstTerm | secondTerm <;> rfl
  · rfl

/-- Reassociation remains exact after taking free finite documents. -/
def freeDocumentDisjointSumAssociator (first second third : GSLT) :
    StructuralIsomorphism
      (GSLT.freeDocument (disjointSum (disjointSum first second) third))
      (GSLT.freeDocument (disjointSum first (disjointSum second third))) :=
  (disjointSumAssociator first second third).freeDocument

/-- The left unitor remains exact after taking free finite documents. -/
def freeDocumentDisjointSumLeftUnitor (system : GSLT) :
    StructuralIsomorphism
      (GSLT.freeDocument (disjointSum disjointSumUnit system))
      (GSLT.freeDocument system) :=
  (disjointSumLeftUnitor system).freeDocument

/-- The right unitor remains exact after taking free finite documents. -/
def freeDocumentDisjointSumRightUnitor (system : GSLT) :
    StructuralIsomorphism
      (GSLT.freeDocument (disjointSum system disjointSumUnit))
      (GSLT.freeDocument system) :=
  (disjointSumRightUnitor system).freeDocument

/-- The braiding remains exact after taking free finite documents. -/
def freeDocumentDisjointSumBraiding (left right : GSLT) :
    StructuralIsomorphism
      (GSLT.freeDocument (disjointSum left right))
      (GSLT.freeDocument (disjointSum right left)) :=
  (disjointSumBraiding left right).freeDocument

end StructuralIsomorphism

end Mettapedia.GSLT.GSLT
