import Mettapedia.GSLT.Core.StructuralIsomorphism

set_option linter.dupNamespace false

/-!
# Flat composition of freely generated GSLT documents

The general product of two `CompositionalElaboration`s must treat a complete
term of either component as one generator of a new document.  That construction
works for arbitrary compositional term languages, but repeated products retain
the resulting document nesting.

`FreeDocumentElaboration` records the common stronger situation directly: the
authored language is one free finite document over a GSLT of generators.
Products then combine generator GSLTs before taking the free-document closure.
The public term language consequently stays flat under repeated composition;
only the coproduct tag is reassociated.
-/

namespace Mettapedia.GSLT

universe u v w uGen vGen wGen

namespace GSLT

/-! ## Mixed-document projections -/

namespace MixedDocument

/-- Keep the left generators of a mixed document, preserving their order. -/
def left {Left : Type u} {Right : Type v} : List (Left ⊕ Right) → List Left
  | [] => []
  | .inl value :: rest => value :: left rest
  | .inr _ :: rest => left rest

/-- Keep the right generators of a mixed document, preserving their order. -/
def right {Left : Type u} {Right : Type v} : List (Left ⊕ Right) → List Right
  | [] => []
  | .inl _ :: rest => right rest
  | .inr value :: rest => value :: right rest

@[simp] theorem left_nil {Left : Type u} {Right : Type v} :
    left ([] : List (Left ⊕ Right)) = [] :=
  rfl

@[simp] theorem right_nil {Left : Type u} {Right : Type v} :
    right ([] : List (Left ⊕ Right)) = [] :=
  rfl

@[simp] theorem left_inl {Left : Type u} {Right : Type v} (value : Left)
    (rest : List (Left ⊕ Right)) :
    left (.inl value :: rest) = value :: left rest :=
  rfl

@[simp] theorem left_inr {Left : Type u} {Right : Type v} (value : Right)
    (rest : List (Left ⊕ Right)) :
    left (.inr value :: rest) = left rest :=
  rfl

@[simp] theorem right_inl {Left : Type u} {Right : Type v} (value : Left)
    (rest : List (Left ⊕ Right)) :
    right (.inl value :: rest) = right rest :=
  rfl

@[simp] theorem right_inr {Left : Type u} {Right : Type v} (value : Right)
    (rest : List (Left ⊕ Right)) :
    right (.inr value :: rest) = value :: right rest :=
  rfl

@[simp] theorem left_append {Left : Type u} {Right : Type v}
    (first second : List (Left ⊕ Right)) :
    left (first ++ second) = left first ++ left second := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases head <;> simp [inductionHypothesis]

@[simp] theorem right_append {Left : Type u} {Right : Type v}
    (first second : List (Left ⊕ Right)) :
    right (first ++ second) = right first ++ right second := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases head <;> simp [inductionHypothesis]

@[simp] theorem left_map_inl {Left : Type u} {Right : Type v}
    (values : List Left) :
    left (values.map (Sum.inl : Left → Left ⊕ Right)) = values := by
  induction values <;> simp_all

@[simp] theorem left_map_inr {Left : Type u} {Right : Type v}
    (values : List Right) :
    left (values.map (Sum.inr : Right → Left ⊕ Right)) = [] := by
  induction values <;> simp_all

@[simp] theorem right_map_inl {Left : Type u} {Right : Type v}
    (values : List Left) :
    right (values.map (Sum.inl : Left → Left ⊕ Right)) = [] := by
  induction values <;> simp_all

@[simp] theorem right_map_inr {Left : Type u} {Right : Type v}
    (values : List Right) :
    right (values.map (Sum.inr : Right → Left ⊕ Right)) = values := by
  induction values <;> simp_all

/-- Exchange the two generator tags without changing document order. -/
def swap {Left : Type u} {Right : Type v} :
    List (Left ⊕ Right) → List (Right ⊕ Left) :=
  List.map (Equiv.sumComm Left Right)

/-- After exchanging tags, the new left projection is the old right one. -/
@[simp] theorem left_swap {Left : Type u} {Right : Type v}
    (document : List (Left ⊕ Right)) :
    left (swap document) = right document := by
  induction document with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change left (List.map Sum.swap tail) =
        right tail at inductionHypothesis
      cases head <;> simp [swap, inductionHypothesis]

/-- After exchanging tags, the new right projection is the old left one. -/
@[simp] theorem right_swap {Left : Type u} {Right : Type v}
    (document : List (Left ⊕ Right)) :
    right (swap document) = left document := by
  induction document with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change right (List.map Sum.swap tail) =
        left tail at inductionHypothesis
      cases head <;> simp [swap, inductionHypothesis]

/-- Reassociate the generator tags of a three-way flat document. -/
def reassociate {First : Type u} {Second : Type v} {Third : Type w} :
    List ((First ⊕ Second) ⊕ Third) → List (First ⊕ (Second ⊕ Third)) :=
  List.map (Equiv.sumAssoc First Second Third)

/-- The first-component projection is invariant under reassociation. -/
theorem left_reassociate {First : Type u} {Second : Type v} {Third : Type w}
    (document : List ((First ⊕ Second) ⊕ Third)) :
    left (reassociate document) = left (left document) := by
  induction document with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change left (List.map (Equiv.sumAssoc First Second Third) tail) =
        left (left tail) at inductionHypothesis
      rcases head with (firstOrSecond | third)
      · rcases firstOrSecond with first | second <;>
          simp [reassociate, inductionHypothesis]
      · simp [reassociate, inductionHypothesis]

/-- The second-component projection is invariant under reassociation. -/
theorem left_right_reassociate
    {First : Type u} {Second : Type v} {Third : Type w}
    (document : List ((First ⊕ Second) ⊕ Third)) :
    left (right (reassociate document)) = right (left document) := by
  induction document with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change left
        (right (List.map (Equiv.sumAssoc First Second Third) tail)) =
          right (left tail) at inductionHypothesis
      rcases head with (firstOrSecond | third)
      · rcases firstOrSecond with first | second <;>
          simp [reassociate, inductionHypothesis]
      · simp [reassociate, inductionHypothesis]

/-- The third-component projection is invariant under reassociation. -/
theorem right_right_reassociate
    {First : Type u} {Second : Type v} {Third : Type w}
    (document : List ((First ⊕ Second) ⊕ Third)) :
    right (right (reassociate document)) = right document := by
  induction document with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change right
        (right (List.map (Equiv.sumAssoc First Second Third) tail)) =
          right tail at inductionHypothesis
      rcases head with (firstOrSecond | third)
      · rcases firstOrSecond with first | second <;>
          simp [reassociate, inductionHypothesis]
      · simp [reassociate, inductionHypothesis]

/-- Project pointwise equations of a disjoint sum to its left component. -/
theorem left_equiv {leftSystem : GSLT.{u}} {rightSystem : GSLT.{v}}
    {source target}
    (equivalent : DocumentEquiv (disjointSum leftSystem rightSystem)
      source target) :
    DocumentEquiv leftSystem (left source) (left target) := by
  induction equivalent with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      cases head with
      | left equivalent => exact .cons equivalent inductionHypothesis
      | right _ => exact inductionHypothesis

/-- Project pointwise equations of a disjoint sum to its right component. -/
theorem right_equiv {leftSystem : GSLT.{u}} {rightSystem : GSLT.{v}}
    {source target}
    (equivalent : DocumentEquiv (disjointSum leftSystem rightSystem)
      source target) :
    DocumentEquiv rightSystem (right source) (right target) := by
  induction equivalent with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      cases head with
      | left _ => exact inductionHypothesis
      | right equivalent => exact .cons equivalent inductionHypothesis

/-- A mixed primitive step either disappears under the left projection or
remains one primitive left-component step. -/
theorem left_rawStep {leftSystem : GSLT.{u}} {rightSystem : GSLT.{v}}
    {source target}
    (step : RawDocumentStep (disjointSum leftSystem rightSystem)
      source target) :
    left source = left target ∨
      RawDocumentStep leftSystem (left source) (left target) := by
  induction step with
  | head rewrite =>
      cases rewrite with
      | left rewrite => exact Or.inr (.head rewrite)
      | right _ => exact Or.inl rfl
  | tail head inductionHypothesis =>
      rename_i mixedHead innerSource innerTarget
      cases mixedHead with
      | inl value =>
          rcases inductionHypothesis with equal | projected
          · exact Or.inl (congrArg (List.cons value) equal)
          · exact Or.inr (.tail projected)
      | inr _ => exact inductionHypothesis

/-- The symmetric primitive-step projection. -/
theorem right_rawStep {leftSystem : GSLT.{u}} {rightSystem : GSLT.{v}}
    {source target}
    (step : RawDocumentStep (disjointSum leftSystem rightSystem)
      source target) :
    right source = right target ∨
      RawDocumentStep rightSystem (right source) (right target) := by
  induction step with
  | head rewrite =>
      cases rewrite with
      | left _ => exact Or.inl rfl
      | right rewrite => exact Or.inr (.head rewrite)
  | tail head inductionHypothesis =>
      rename_i mixedHead innerSource innerTarget
      cases mixedHead with
      | inl _ => exact inductionHypothesis
      | inr value =>
          rcases inductionHypothesis with equal | projected
          · exact Or.inl (congrArg (List.cons value) equal)
          · exact Or.inr (.tail projected)

end MixedDocument

/-! ## Freely generated compositional elaborations -/

/-- An exact compositional elaboration whose authored terms are one flat free
document over a GSLT of generators.  The payload algebra remains licensed by
the authored empty document and concatenation laws. -/
structure FreeDocumentElaboration.{uGenerator, uPayload}
    (Payload : Type uPayload) where
  generators : GSLT.{uGenerator}
  elaboration : ExactElaboration (freeDocument generators) Payload
  emptyPayload : Payload
  merge : Payload → Payload → Option Payload
  elaborate_empty : elaboration.elaborate [] = some emptyPayload
  elaborate_append : ∀ first second : List generators.Term,
    elaboration.elaborate (first ++ second) =
      (elaboration.elaborate first).bind fun left =>
        (elaboration.elaborate second).bind fun right => merge left right

namespace FreeDocumentElaboration

/-- Forget that the compositional source has a chosen generator GSLT. -/
def toCompositionalElaboration {Payload : Type u}
    (system : FreeDocumentElaboration Payload) :
    CompositionalElaboration Payload where
  authoring := freeDocumentCompositional system.generators
  elaboration := system.elaboration
  emptyPayload := system.emptyPayload
  merge := system.merge
  elaborate_empty := system.elaborate_empty
  elaborate_append := system.elaborate_append

/-- The partial monoid forced by the authored flat-document laws. -/
def toPartialMonoid {Payload : Type u}
    (system : FreeDocumentElaboration Payload) : PartialMonoid Payload :=
  system.toCompositionalElaboration.toPartialMonoid

@[simp] theorem toPartialMonoid_unit {Payload : Type u}
    (system : FreeDocumentElaboration Payload) :
    system.toPartialMonoid.unit = system.emptyPayload :=
  rfl

@[simp] theorem toPartialMonoid_op {Payload : Type u}
    (system : FreeDocumentElaboration Payload) :
    system.toPartialMonoid.op = system.merge :=
  rfl

private def pairOptions {Left : Type u} {Right : Type v}
    (left : Option Left) (right : Option Right) : Option (Left × Right) :=
  match left, right with
  | some leftValue, some rightValue => some (leftValue, rightValue)
  | _, _ => none

private theorem pairOptions_merge {Left : Type u} {Right : Type v}
    (leftFirst leftSecond : Option Left)
    (rightFirst rightSecond : Option Right)
    (mergeLeft : Left → Left → Option Left)
    (mergeRight : Right → Right → Option Right) :
    pairOptions
        (leftFirst.bind fun first =>
          leftSecond.bind fun second => mergeLeft first second)
        (rightFirst.bind fun first =>
          rightSecond.bind fun second => mergeRight first second) =
      (pairOptions leftFirst rightFirst).bind fun first =>
        (pairOptions leftSecond rightSecond).bind fun second =>
          (mergeLeft first.1 second.1).bind fun mergedLeft =>
            (mergeRight first.2 second.2).bind fun mergedRight =>
              some (mergedLeft, mergedRight) := by
  cases leftFirst <;> cases leftSecond <;>
    cases rightFirst <;> cases rightSecond
  all_goals simp [pairOptions]
  rename_i firstLeft secondLeft firstRight secondRight
  cases mergeLeft firstLeft secondLeft <;>
    cases mergeRight firstRight secondRight <;> rfl

private theorem pairOptions_associative
    {First : Type u} {Second : Type v} {Third : Type w}
    (first : Option First) (second : Option Second) (third : Option Third) :
    (pairOptions (pairOptions first second) third).map
        (Equiv.prodAssoc First Second Third) =
      pairOptions first (pairOptions second third) := by
  cases first <;> cases second <;> cases third <;> rfl

private theorem pairOptions_commutative
    {Left : Type u} {Right : Type v}
    (left : Option Left) (right : Option Right) :
    (pairOptions left right).map (Equiv.prodComm Left Right) =
      pairOptions right left := by
  cases left <;> cases right <;> rfl

/-! ### The neutral elaboration -/

/-- The neutral flat authoring language has no generators and exactly one
payload.  It is genuine authored structure: its empty document elaborates to
the payload unit used by product padding. -/
def unit : FreeDocumentElaboration PUnit where
  generators := disjointSumUnit
  elaboration :=
    { elaborate := fun _ => some PUnit.unit
      equation := by intros; rfl
      rewrite := by intros; rfl
      quote := fun _ => []
      elaborate_quote := by intro; rfl }
  emptyPayload := PUnit.unit
  merge := fun _ _ => some PUnit.unit
  elaborate_empty := rfl
  elaborate_append := by intros; rfl

@[simp] theorem unit_elaborate (source : List disjointSumUnit.Term) :
    unit.elaboration.elaborate source = some PUnit.unit :=
  rfl

/-- The canonical flat document elaboration: generators elaborate to their
ordered list, with concatenation as payload composition. -/
def orderedList (Generator : Type*) : FreeDocumentElaboration (List Generator) where
  generators := discrete Generator
  elaboration :=
    { elaborate := some
      equation := by
        intro source target equivalent
        have equal := DocumentEquiv.eq_of
          (fun {left right} component => by
            change left = right at component
            exact component) equivalent
        subst target
        rfl
      rewrite := by
        intro source target step
        rcases step with ⟨_, _, _, raw, _⟩
        exact (RawDocumentStep.false_of_no_step
          (fun {left right} impossible => by
            change False at impossible
            exact impossible) raw).elim
      quote := id
      elaborate_quote := fun _ => rfl }
  emptyPayload := []
  merge := fun first second => some (first ++ second)
  elaborate_empty := rfl
  elaborate_append := by intros; rfl

private def productElaborate {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right)
    (source : List (left.generators.Term ⊕ right.generators.Term)) :
    Option (Left × Right) :=
  pairOptions
    (left.elaboration.elaborate (MixedDocument.left source))
    (right.elaboration.elaborate (MixedDocument.right source))

private theorem productElaborate_equation {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right) {source target}
    (equivalent : DocumentEquiv
      (disjointSum left.generators right.generators) source target) :
    productElaborate left right source = productElaborate left right target := by
  unfold productElaborate pairOptions
  rw [left.elaboration.equation (MixedDocument.left_equiv equivalent),
    right.elaboration.equation (MixedDocument.right_equiv equivalent)]

private theorem left_elaboration_rawStep {Left : Type u}
    (left : FreeDocumentElaboration Left)
    {rightSystem : GSLT} {source target}
    (step : RawDocumentStep (disjointSum left.generators rightSystem)
      source target) :
    left.elaboration.elaborate (MixedDocument.left source) =
      left.elaboration.elaborate (MixedDocument.left target) := by
  rcases MixedDocument.left_rawStep step with equal | projected
  · rw [equal]
  · exact left.elaboration.rewrite
      ⟨_, _, DocumentEquiv.refl _ _, projected, DocumentEquiv.refl _ _⟩

private theorem right_elaboration_rawStep {Right : Type v}
    (right : FreeDocumentElaboration Right)
    {leftSystem : GSLT} {source target}
    (step : RawDocumentStep (disjointSum leftSystem right.generators)
      source target) :
    right.elaboration.elaborate (MixedDocument.right source) =
      right.elaboration.elaborate (MixedDocument.right target) := by
  rcases MixedDocument.right_rawStep step with equal | projected
  · rw [equal]
  · exact right.elaboration.rewrite
      ⟨_, _, DocumentEquiv.refl _ _, projected, DocumentEquiv.refl _ _⟩

private theorem productElaborate_rewrite {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right) {source target}
    (step : DocumentStep (disjointSum left.generators right.generators)
      source target) :
    productElaborate left right source = productElaborate left right target := by
  rcases step with
    ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
  calc
    productElaborate left right source =
        productElaborate left right middleSource :=
      productElaborate_equation left right sourceMiddle
    _ = productElaborate left right middleTarget := by
      unfold productElaborate
      rw [left_elaboration_rawStep left rewrite,
        right_elaboration_rawStep right rewrite]
    _ = productElaborate left right target :=
      productElaborate_equation left right middleTargetTarget

/-- Flat product: combine generator theories first, then take exactly one
free-document closure.  Repeated products therefore never nest documents. -/
def product {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right) :
    FreeDocumentElaboration (Left × Right) where
  generators := disjointSum left.generators right.generators
  elaboration :=
    { elaborate := productElaborate left right
      equation := productElaborate_equation left right
      rewrite := productElaborate_rewrite left right
      quote := fun value =>
        (left.elaboration.quote value.1).map Sum.inl ++
          (right.elaboration.quote value.2).map Sum.inr
      elaborate_quote := by
        rintro ⟨leftValue, rightValue⟩
        change pairOptions
          (left.elaboration.elaborate
            (MixedDocument.left
              ((left.elaboration.quote leftValue).map Sum.inl ++
                (right.elaboration.quote rightValue).map Sum.inr)))
          (right.elaboration.elaborate
            (MixedDocument.right
              ((left.elaboration.quote leftValue).map Sum.inl ++
                (right.elaboration.quote rightValue).map Sum.inr))) =
            some (leftValue, rightValue)
        rw [MixedDocument.left_append, MixedDocument.right_append,
          MixedDocument.left_map_inl, MixedDocument.left_map_inr,
          MixedDocument.right_map_inl, MixedDocument.right_map_inr]
        simp only [List.append_nil, List.nil_append]
        rw [left.elaboration.elaborate_quote,
          right.elaboration.elaborate_quote]
        rfl }
  emptyPayload := (left.emptyPayload, right.emptyPayload)
  merge := (left.toPartialMonoid.prod right.toPartialMonoid).op
  elaborate_empty := by
    change pairOptions (left.elaboration.elaborate [])
      (right.elaboration.elaborate []) =
        some (left.emptyPayload, right.emptyPayload)
    rw [left.elaborate_empty, right.elaborate_empty]
    rfl
  elaborate_append := by
    intro first second
    change List (left.generators.Term ⊕ right.generators.Term) at first second
    change pairOptions
      (left.elaboration.elaborate (MixedDocument.left (first ++ second)))
      (right.elaboration.elaborate (MixedDocument.right (first ++ second))) =
        (pairOptions
          (left.elaboration.elaborate (MixedDocument.left first))
          (right.elaboration.elaborate (MixedDocument.right first))).bind
          fun leftValue =>
            (pairOptions
              (left.elaboration.elaborate (MixedDocument.left second))
              (right.elaboration.elaborate (MixedDocument.right second))).bind
              fun rightValue =>
                (left.toPartialMonoid.prod right.toPartialMonoid).op
                  leftValue rightValue
    rw [MixedDocument.left_append, MixedDocument.right_append]
    rw [left.elaborate_append, right.elaborate_append]
    simpa [PartialMonoid.prod] using
      pairOptions_merge
        (left.elaboration.elaborate (MixedDocument.left first))
        (left.elaboration.elaborate (MixedDocument.left second))
        (right.elaboration.elaborate (MixedDocument.right first))
        (right.elaboration.elaborate (MixedDocument.right second))
        left.merge right.merge

@[simp] theorem product_generators {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right) :
    (left.product right).generators =
      disjointSum left.generators right.generators :=
  rfl

/-- Rebracketing a three-way flat product is a structural isomorphism of its
single authored GSLT, including both equations and primitive rewrites. -/
def flatProductAssociator
    {First : Type u} {Second : Type v} {Third : Type w}
    (first : FreeDocumentElaboration First)
    (second : FreeDocumentElaboration Second)
    (third : FreeDocumentElaboration Third) :
    StructuralIsomorphism
      (freeDocument ((first.product second).product third).generators)
      (freeDocument (first.product (second.product third)).generators) := by
  change StructuralIsomorphism
    (freeDocument
      (disjointSum (disjointSum first.generators second.generators)
        third.generators))
    (freeDocument
      (disjointSum first.generators
        (disjointSum second.generators third.generators)))
  exact StructuralIsomorphism.freeDocumentDisjointSumAssociator
    first.generators second.generators third.generators

@[simp] theorem flatProductAssociator_apply
    {First : Type u} {Second : Type v} {Third : Type w}
    (first : FreeDocumentElaboration First)
    (second : FreeDocumentElaboration Second)
    (third : FreeDocumentElaboration Third)
    (source : List
      ((first.generators.Term ⊕ second.generators.Term) ⊕
        third.generators.Term)) :
    (flatProductAssociator first second third).termEquiv source =
      MixedDocument.reassociate source :=
  rfl

/-- The neutral flat elaboration is a left unit at the authored GSLT level. -/
def flatProductLeftUnitor {Payload : Type u}
    (system : FreeDocumentElaboration Payload) :
    StructuralIsomorphism
      (freeDocument (unit.product system).generators)
      (freeDocument system.generators) := by
  change StructuralIsomorphism
    (freeDocument (disjointSum disjointSumUnit system.generators))
    (freeDocument system.generators)
  exact StructuralIsomorphism.freeDocumentDisjointSumLeftUnitor
    system.generators

@[simp] theorem flatProductLeftUnitor_apply {Payload : Type u}
    (system : FreeDocumentElaboration Payload)
    (source : List (disjointSumUnit.Term ⊕ system.generators.Term)) :
    (flatProductLeftUnitor system).termEquiv source =
      MixedDocument.right source := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rcases head with impossible | term
      · exact Empty.elim impossible
      · change term :: (flatProductLeftUnitor system).termEquiv tail =
          term :: MixedDocument.right tail
        rw [inductionHypothesis]

/-- The neutral flat elaboration is a right unit at the authored GSLT level. -/
def flatProductRightUnitor {Payload : Type u}
    (system : FreeDocumentElaboration Payload) :
    StructuralIsomorphism
      (freeDocument (system.product unit).generators)
      (freeDocument system.generators) := by
  change StructuralIsomorphism
    (freeDocument (disjointSum system.generators disjointSumUnit))
    (freeDocument system.generators)
  exact StructuralIsomorphism.freeDocumentDisjointSumRightUnitor
    system.generators

@[simp] theorem flatProductRightUnitor_apply {Payload : Type u}
    (system : FreeDocumentElaboration Payload)
    (source : List (system.generators.Term ⊕ disjointSumUnit.Term)) :
    (flatProductRightUnitor system).termEquiv source =
      MixedDocument.left source := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rcases head with term | impossible
      · change term :: (flatProductRightUnitor system).termEquiv tail =
          term :: MixedDocument.left tail
        rw [inductionHypothesis]
      · exact Empty.elim impossible

/-- Flat product is symmetric at the authored GSLT level. -/
def flatProductBraiding {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right) :
    StructuralIsomorphism
      (freeDocument (left.product right).generators)
      (freeDocument (right.product left).generators) := by
  change StructuralIsomorphism
    (freeDocument (disjointSum left.generators right.generators))
    (freeDocument (disjointSum right.generators left.generators))
  exact StructuralIsomorphism.freeDocumentDisjointSumBraiding
    left.generators right.generators

@[simp] theorem flatProductBraiding_apply
    {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right)
    (source : List (left.generators.Term ⊕ right.generators.Term)) :
    (flatProductBraiding left right).termEquiv source =
      MixedDocument.swap source :=
  rfl

/-- The flat product elaborator commutes with the structural associator.  The
only change in the payload is the canonical product reassociation. -/
theorem product_elaboration_associative
    {First : Type u} {Second : Type v} {Third : Type w}
    (first : FreeDocumentElaboration First)
    (second : FreeDocumentElaboration Second)
    (third : FreeDocumentElaboration Third)
    (source : List
      ((first.generators.Term ⊕ second.generators.Term) ⊕
        third.generators.Term)) :
    (((first.product second).product third).elaboration.elaborate source).map
        (Equiv.prodAssoc First Second Third) =
      (first.product (second.product third)).elaboration.elaborate
        (MixedDocument.reassociate source) := by
  change
    (pairOptions
      (pairOptions
        (first.elaboration.elaborate
          (MixedDocument.left (MixedDocument.left source)))
        (second.elaboration.elaborate
          (MixedDocument.right (MixedDocument.left source))))
      (third.elaboration.elaborate (MixedDocument.right source))).map
        (Equiv.prodAssoc First Second Third) =
      pairOptions
        (first.elaboration.elaborate
          (MixedDocument.left (MixedDocument.reassociate source)))
        (pairOptions
          (second.elaboration.elaborate
            (MixedDocument.left
              (MixedDocument.right (MixedDocument.reassociate source))))
          (third.elaboration.elaborate
            (MixedDocument.right
              (MixedDocument.right (MixedDocument.reassociate source)))))
  rw [MixedDocument.left_reassociate,
    MixedDocument.left_right_reassociate,
    MixedDocument.right_right_reassociate]
  exact pairOptions_associative _ _ _

/-- Exchanging the two flat generator languages exchanges exactly the two
payload coordinates; it neither loses nor invents elaboration results. -/
theorem product_elaboration_commutative
    {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right)
    (source : List (left.generators.Term ⊕ right.generators.Term)) :
    ((left.product right).elaboration.elaborate source).map
        (Equiv.prodComm Left Right) =
      (right.product left).elaboration.elaborate
        (MixedDocument.swap source) := by
  change
    (pairOptions
      (left.elaboration.elaborate (MixedDocument.left source))
      (right.elaboration.elaborate (MixedDocument.right source))).map
        (Equiv.prodComm Left Right) =
      pairOptions
        (right.elaboration.elaborate
          (MixedDocument.left (MixedDocument.swap source)))
        (left.elaboration.elaborate
          (MixedDocument.right (MixedDocument.swap source)))
  rw [MixedDocument.left_swap, MixedDocument.right_swap]
  exact pairOptions_commutative _ _

/-- Removing a neutral left factor removes only its `PUnit` payload. -/
theorem product_elaboration_left_unit
    {Payload : Type u} (system : FreeDocumentElaboration Payload)
    (source : List (disjointSumUnit.Term ⊕ system.generators.Term)) :
    ((unit.product system).elaboration.elaborate source).map
        (Equiv.punitProd Payload) =
      system.elaboration.elaborate (MixedDocument.right source) := by
  change
    (pairOptions (some PUnit.unit)
      (system.elaboration.elaborate (MixedDocument.right source))).map
        (Equiv.punitProd Payload) = _
  cases system.elaboration.elaborate (MixedDocument.right source) <;> rfl

/-- Removing a neutral right factor removes only its `PUnit` payload. -/
theorem product_elaboration_right_unit
    {Payload : Type u} (system : FreeDocumentElaboration Payload)
    (source : List (system.generators.Term ⊕ disjointSumUnit.Term)) :
    ((system.product unit).elaboration.elaborate source).map
        (Equiv.prodPUnit Payload) =
      system.elaboration.elaborate (MixedDocument.left source) := by
  change
    (pairOptions (system.elaboration.elaborate (MixedDocument.left source))
      (some PUnit.unit)).map (Equiv.prodPUnit Payload) = _
  cases system.elaboration.elaborate (MixedDocument.left source) <;> rfl

/-- A left-only flat document elaborates exactly as its component, padded by
the right empty payload. -/
theorem product_elaborates_left_only {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right)
    (source : List left.generators.Term) :
    (left.product right).elaboration.elaborate
        (source.map (Sum.inl : left.generators.Term →
          left.generators.Term ⊕ right.generators.Term)) =
      (left.elaboration.elaborate source).map
        fun value => (value, right.emptyPayload) := by
  change productElaborate left right
      (source.map (Sum.inl : left.generators.Term →
        left.generators.Term ⊕ right.generators.Term)) = _
  unfold productElaborate
  rw [MixedDocument.left_map_inl, MixedDocument.right_map_inl,
    right.elaborate_empty]
  cases left.elaboration.elaborate source <;> rfl

/-- The symmetric right-only law. -/
theorem product_elaborates_right_only {Left : Type u} {Right : Type v}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right)
    (source : List right.generators.Term) :
    (left.product right).elaboration.elaborate
        (source.map (Sum.inr : right.generators.Term →
          left.generators.Term ⊕ right.generators.Term)) =
      (right.elaboration.elaborate source).map
        fun value => (left.emptyPayload, value) := by
  change productElaborate left right
      (source.map (Sum.inr : right.generators.Term →
        left.generators.Term ⊕ right.generators.Term)) = _
  unfold productElaborate
  rw [MixedDocument.left_map_inr, MixedDocument.right_map_inr,
    left.elaborate_empty]
  cases right.elaboration.elaborate source <;> rfl

/-! ### Executable separation canaries -/

private def canaryProduct := (orderedList Nat).product (orderedList Bool)

/-- Positive: independent generators remain interleaved in one flat authored
document while elaborating to their two ordered coordinates. -/
example :
    canaryProduct.elaboration.elaborate
      [Sum.inl (2 : Nat), Sum.inr true, Sum.inl (5 : Nat), Sum.inr false] =
        some ([2, 5], [true, false]) :=
  rfl

/-- Negative: the right coordinate is not erased by flat composition. -/
example :
    canaryProduct.elaboration.elaborate [Sum.inl (2 : Nat), Sum.inr true] ≠
      canaryProduct.elaboration.elaborate
        [Sum.inl (2 : Nat), Sum.inr false] := by
  decide

end FreeDocumentElaboration

end GSLT

end Mettapedia.GSLT
