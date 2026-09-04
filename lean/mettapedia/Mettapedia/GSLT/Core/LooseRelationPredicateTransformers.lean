import Mathlib.Data.Set.Insert
import Mettapedia.GSLT.Core.LooseRelationCompanions

/-!
# Predicate transformers of proof-relevant relations

A proof-relevant relation carries more information than its action on
predicates.  This module isolates the exact relationship.

For a loose relation `R : Source -> Target -> Type`, `mayPullback R` uses an
existentially reachable target, while `mustPullback R` requires every
reachable target to satisfy the postcondition.  The corresponding forward
transformers form the two standard Galois connections.  Both pullbacks
preserve relational identities and composition.  A refinement cell induces
the expected lax and colax predicate-transport inequalities.

Exact representation by a function is precisely the boundary at which may
and must both reduce to ordinary inverse image.  Predicate transformers see
exactly the propositional support of a route and cannot recover the number or
identity of its witnesses; the final canary proves this loss concretely.

These are generic facts about relations and predicates.  No language,
calculus, or runtime is selected here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LooseRelationPredicateTransformers

open Mettapedia.GSLT.LooseRelationEquipment

universe u

variable {Source Middle Target : Type u}

/-! ## Propositional support and four predicate transformers -/

/-- Propositional support forgets the identity and multiplicity of route
witnesses while retaining whether the fibre is inhabited. -/
def support (route : Loose Source Target) (source : Source)
    (target : Target) : Prop :=
  Nonempty (route source target)

/-- Existential inverse image: the source may reach a satisfying target. -/
def mayPullback (route : Loose Source Target)
    (predicate : Set Target) : Set Source :=
  { source | ∃ target, support route source target ∧ target ∈ predicate }

/-- Universal inverse image: every reachable target satisfies the
postcondition. -/
def mustPullback (route : Loose Source Target)
    (predicate : Set Target) : Set Source :=
  { source | ∀ target, support route source target → target ∈ predicate }

/-- Existential direct image: the target may be reached from a satisfying
source. -/
def mayPushforward (route : Loose Source Target)
    (predicate : Set Source) : Set Target :=
  { target | ∃ source, source ∈ predicate ∧ support route source target }

/-- Universal direct image along the converse relation: every predecessor of
the target satisfies the source predicate. -/
def mustPushforward (route : Loose Source Target)
    (predicate : Set Source) : Set Target :=
  { target | ∀ source, support route source target → source ∈ predicate }

/-! ## Support respects the relation equipment -/

@[simp] theorem support_identity_iff (source target : Source) :
    support (identity : Loose Source Source) source target ↔
      source = target := by
  constructor
  · rintro ⟨witness⟩
    exact witness.down.down
  · intro equal
    exact ⟨⟨⟨equal⟩⟩⟩

@[simp] theorem support_comp_iff
    (earlier : Loose Source Middle) (later : Loose Middle Target)
    (source : Source) (target : Target) :
    support (LooseRelationEquipment.comp earlier later) source target ↔
      ∃ middle, support earlier source middle ∧
        support later middle target := by
  constructor
  · rintro ⟨witness⟩
    exact ⟨witness.1, ⟨witness.2.1⟩, ⟨witness.2.2⟩⟩
  · rintro ⟨middle, ⟨earlierWitness⟩, ⟨laterWitness⟩⟩
    exact ⟨⟨middle, earlierWitness, laterWitness⟩⟩

/-! ## Identity and sequential composition -/

@[simp] theorem mayPullback_identity (predicate : Set Source) :
    mayPullback (identity : Loose Source Source) predicate = predicate := by
  ext source
  constructor
  · rintro ⟨target, related, member⟩
    have equal := support_identity_iff source target |>.mp related
    exact equal ▸ member
  · intro member
    exact ⟨source, (support_identity_iff source source).2 rfl, member⟩

@[simp] theorem mustPullback_identity (predicate : Set Source) :
    mustPullback (identity : Loose Source Source) predicate = predicate := by
  ext source
  constructor
  · intro allTargets
    exact allTargets source (support_identity_iff source source |>.2 rfl)
  · intro member target related
    have equal := support_identity_iff source target |>.mp related
    exact equal ▸ member

@[simp] theorem mayPullback_comp
    (earlier : Loose Source Middle) (later : Loose Middle Target)
    (predicate : Set Target) :
    mayPullback (LooseRelationEquipment.comp earlier later) predicate =
      mayPullback earlier (mayPullback later predicate) := by
  ext source
  constructor
  · rintro ⟨target, related, member⟩
    obtain ⟨middle, earlierRelated, laterRelated⟩ :=
      (support_comp_iff earlier later source target).1 related
    exact ⟨middle, earlierRelated, target, laterRelated, member⟩
  · rintro ⟨middle, earlierRelated, target, laterRelated, member⟩
    exact ⟨target,
      (support_comp_iff earlier later source target).2
        ⟨middle, earlierRelated, laterRelated⟩,
      member⟩

@[simp] theorem mustPullback_comp
    (earlier : Loose Source Middle) (later : Loose Middle Target)
    (predicate : Set Target) :
    mustPullback (LooseRelationEquipment.comp earlier later) predicate =
      mustPullback earlier (mustPullback later predicate) := by
  ext source
  constructor
  · intro allTargets middle earlierRelated target laterRelated
    exact allTargets target
      ((support_comp_iff earlier later source target).2
        ⟨middle, earlierRelated, laterRelated⟩)
  · intro allMiddle target compositeRelated
    obtain ⟨middle, earlierRelated, laterRelated⟩ :=
      (support_comp_iff earlier later source target).1 compositeRelated
    exact allMiddle middle earlierRelated target laterRelated

/-! ## Monotonicity and the two Galois connections -/

theorem mayPullback_mono (route : Loose Source Target)
    {first second : Set Target} (subset : first ⊆ second) :
    mayPullback route first ⊆ mayPullback route second := by
  rintro source ⟨target, related, member⟩
  exact ⟨target, related, subset member⟩

theorem mustPullback_mono (route : Loose Source Target)
    {first second : Set Target} (subset : first ⊆ second) :
    mustPullback route first ⊆ mustPullback route second := by
  intro source allTargets target related
  exact subset (allTargets target related)

/-- Every source has at least one target in propositional support.  This is
weaker than proof-relevant `Total` only in how the witness is packaged. -/
def SupportTotal (route : Loose Source Target) : Prop :=
  ∀ source, ∃ target, support route source target

/-- Propositional support is single-valued.  Distinct evidence for the same
visible source and target is deliberately ignored. -/
def SupportFunctional (route : Loose Source Target) : Prop :=
  ∀ source firstTarget secondTarget,
    support route source firstTarget →
      support route source secondTarget →
        firstTarget = secondTarget

/-- Exact proof-relevant representation implies total, functional support. -/
theorem support_total_functional_of_representation
    {route : Loose Source Target} (representation : Representation route) :
    SupportTotal route ∧ SupportFunctional route := by
  constructor
  · intro source
    obtain ⟨selected⟩ := representation.total source
    exact ⟨selected.1, ⟨selected.2⟩⟩
  · intro source firstTarget secondTarget
      ⟨firstWitness⟩ ⟨secondWitness⟩
    have firstEqual :=
      (representation.exact source firstTarget firstWitness).down.down
    have secondEqual :=
      (representation.exact source secondTarget secondWitness).down.down
    exact firstEqual.symm.trans secondEqual

/-- May and must agree for every postcondition exactly when the visible
support is total and single-valued.  This criterion does not inspect the
cardinality of an inhabited witness fibre. -/
theorem all_may_eq_must_iff_support_total_functional
    (route : Loose Source Target) :
    (∀ predicate : Set Target,
      mayPullback route predicate = mustPullback route predicate) ↔
      SupportTotal route ∧ SupportFunctional route := by
  constructor
  · intro allPredicates
    constructor
    · intro source
      classical
      by_contra noTarget
      have mustEmpty : source ∈ mustPullback route (∅ : Set Target) := by
        intro target related
        exact False.elim (noTarget ⟨target, related⟩)
      have mayEmpty : source ∈ mayPullback route (∅ : Set Target) := by
        rw [allPredicates (∅ : Set Target)]
        exact mustEmpty
      rcases mayEmpty with ⟨_target, _related, impossible⟩
      exact impossible
    · intro source firstTarget secondTarget firstRelated secondRelated
      have mayFirst :
          source ∈ mayPullback route ({firstTarget} : Set Target) :=
        ⟨firstTarget, firstRelated, Set.mem_singleton firstTarget⟩
      have mustFirst :
          source ∈ mustPullback route ({firstTarget} : Set Target) := by
        rw [← allPredicates ({firstTarget} : Set Target)]
        exact mayFirst
      exact (Set.mem_singleton_iff.mp
        (mustFirst secondTarget secondRelated)).symm
  · rintro ⟨total, functional⟩ predicate
    ext source
    constructor
    · rintro ⟨selectedTarget, selectedRelated, selectedMember⟩
      intro target related
      have equal := functional source selectedTarget target
        selectedRelated related
      exact equal ▸ selectedMember
    · intro allTargets
      obtain ⟨target, related⟩ := total source
      exact ⟨target, related, allTargets target related⟩

/-- Existential direct image is left adjoint, as an order map, to universal
inverse image. -/
theorem mayPushforward_subset_iff_subset_mustPullback
    (route : Loose Source Target) (sourcePredicate : Set Source)
    (targetPredicate : Set Target) :
    mayPushforward route sourcePredicate ⊆ targetPredicate ↔
      sourcePredicate ⊆ mustPullback route targetPredicate := by
  constructor
  · intro forward source sourceMember target related
    exact forward ⟨source, sourceMember, related⟩
  · rintro backward target ⟨source, sourceMember, related⟩
    exact backward sourceMember target related

/-- Existential inverse image is left adjoint, as an order map, to universal
direct image along the converse relation. -/
theorem mayPullback_subset_iff_subset_mustPushforward
    (route : Loose Source Target) (targetPredicate : Set Target)
    (sourcePredicate : Set Source) :
    mayPullback route targetPredicate ⊆ sourcePredicate ↔
      targetPredicate ⊆ mustPushforward route sourcePredicate := by
  constructor
  · intro backward target targetMember source related
    exact backward ⟨target, related, targetMember⟩
  · rintro forward source ⟨target, related, targetMember⟩
    exact forward targetMember source related

/-! ## Exact functional representation -/

/-- A represented route's existential transformer is ordinary inverse image
along its uniquely selected map. -/
theorem mayPullback_eq_preimage
    {route : Loose Source Target}
    (representation : Representation route) (predicate : Set Target) :
    mayPullback route predicate =
      Set.preimage representation.map predicate := by
  ext source
  constructor
  · rintro ⟨target, ⟨witness⟩, targetMember⟩
    have targetEquality :=
      (representation.exact source target witness).down.down
    change representation.map source ∈ predicate
    rw [targetEquality]
    exact targetMember
  · intro sourceMember
    refine ⟨representation.map source, ?_, sourceMember⟩
    exact ⟨(representation.exact source
      (representation.map source)).symm ⟨⟨rfl⟩⟩⟩

/-- A represented route's universal transformer is the same inverse image.
Proof-relevant totality and determinism are both used by the representation. -/
theorem mustPullback_eq_preimage
    {route : Loose Source Target}
    (representation : Representation route) (predicate : Set Target) :
    mustPullback route predicate =
      Set.preimage representation.map predicate := by
  ext source
  constructor
  · intro allTargets
    apply allTargets (representation.map source)
    exact ⟨(representation.exact source
      (representation.map source)).symm ⟨⟨rfl⟩⟩⟩
  · intro sourceMember target ⟨witness⟩
    have targetEquality :=
      (representation.exact source target witness).down.down
    rw [← targetEquality]
    exact sourceMember

/-- May and must coincide on every represented route. -/
theorem represented_mayPullback_eq_mustPullback
    {route : Loose Source Target}
    (representation : Representation route) (predicate : Set Target) :
    mayPullback route predicate = mustPullback route predicate := by
  rw [mayPullback_eq_preimage representation predicate,
    mustPullback_eq_preimage representation predicate]

/-! ## Refinement cells act on predicates -/

/-- A cell maps possible top executions to possible bottom executions. -/
theorem Cell.mayPullback_lax
    {Source' Target' : Type u}
    {left : Source → Source'} {right : Target → Target'}
    {top : Loose Source Target} {bottom : Loose Source' Target'}
    (cell : Cell left right top bottom) (predicate : Set Target') :
    mayPullback top (Set.preimage right predicate) ⊆
      Set.preimage left (mayPullback bottom predicate) := by
  rintro source ⟨target, ⟨witness⟩, member⟩
  exact ⟨right target, ⟨cell.map witness⟩, member⟩

/-- A universal bottom precondition restricts to a universal top
precondition along the same cell. -/
theorem Cell.mustPullback_colax
    {Source' Target' : Type u}
    {left : Source → Source'} {right : Target → Target'}
    {top : Loose Source Target} {bottom : Loose Source' Target'}
    (cell : Cell left right top bottom) (predicate : Set Target') :
    Set.preimage left (mustPullback bottom predicate) ⊆
      mustPullback top (Set.preimage right predicate) := by
  intro source bottomMust target ⟨witness⟩
  exact bottomMust (right target) ⟨cell.map witness⟩

/-! ## Predicate transformers see exactly support -/

theorem mayPullback_congr
    {first second : Loose Source Target}
    (sameSupport : ∀ source target,
      support first source target ↔ support second source target)
    (predicate : Set Target) :
    mayPullback first predicate = mayPullback second predicate := by
  ext source
  constructor
  · rintro ⟨target, related, member⟩
    exact ⟨target, (sameSupport source target).1 related, member⟩
  · rintro ⟨target, related, member⟩
    exact ⟨target, (sameSupport source target).2 related, member⟩

theorem mustPullback_congr
    {first second : Loose Source Target}
    (sameSupport : ∀ source target,
      support first source target ↔ support second source target)
    (predicate : Set Target) :
    mustPullback first predicate = mustPullback second predicate := by
  ext source
  constructor
  · intro firstMust target secondRelated
    exact firstMust target ((sameSupport source target).2 secondRelated)
  · intro secondMust target firstRelated
    exact secondMust target ((sameSupport source target).1 firstRelated)

/-- Equality of every existential predicate transformer is equivalent to
pointwise equality of propositional support.  Thus the predicate view loses
exactly proof relevance, not reachability. -/
theorem all_mayPullback_eq_iff_same_support
    (first second : Loose Source Target) :
    (∀ predicate : Set Target,
      mayPullback first predicate = mayPullback second predicate) ↔
      ∀ source target,
        support first source target ↔ support second source target := by
  constructor
  · intro allPredicates source target
    have singletonEquality := allPredicates ({target} : Set Target)
    constructor
    · intro firstRelated
      have firstMember :
          source ∈ mayPullback first ({target} : Set Target) :=
        ⟨target, firstRelated, Set.mem_singleton target⟩
      rw [singletonEquality] at firstMember
      rcases firstMember with ⟨otherTarget, secondRelated, otherEqual⟩
      have equal : otherTarget = target := Set.mem_singleton_iff.mp otherEqual
      subst otherTarget
      exact secondRelated
    · intro secondRelated
      have secondMember :
          source ∈ mayPullback second ({target} : Set Target) :=
        ⟨target, secondRelated, Set.mem_singleton target⟩
      rw [← singletonEquality] at secondMember
      rcases secondMember with ⟨otherTarget, firstRelated, otherEqual⟩
      have equal : otherTarget = target := Set.mem_singleton_iff.mp otherEqual
      subst otherTarget
      exact firstRelated
  · intro sameSupport predicate
    exact mayPullback_congr sameSupport predicate

/-! ## Positive and negative controls -/

namespace Canary

/-- A relation with exactly one witness in its only fibre. -/
def oneWitness : Loose Unit Unit := fun _source _target => Unit

/-- A relation with two distinct witnesses in the same visible fibre. -/
def twoWitnesses : Loose Unit Unit := fun _source _target => Bool

theorem one_and_two_have_same_support :
    support oneWitness = support twoWitnesses := by
  funext source target
  apply propext
  constructor
  · intro _inhabited
    exact ⟨true⟩
  · intro _inhabited
    exact ⟨()⟩

theorem unit_not_equivalent_to_bool : ¬ Nonempty (Unit ≃ Bool) := by
  rintro ⟨equivalence⟩
  have inverseEqual : equivalence.symm true = equivalence.symm false :=
    Subsingleton.elim _ _
  have impossible : true = false := by
    simpa using congrArg equivalence inverseEqual
  exact Bool.false_ne_true impossible.symm

/-- The whole predicate-transformer semantics agrees although the
proof-relevant fibres are not equivalent. -/
theorem predicate_view_agrees_but_witnesses_do_not :
    (∀ predicate : Set Unit,
      mayPullback oneWitness predicate =
        mayPullback twoWitnesses predicate) ∧
      ¬ (∀ source target,
        Nonempty (oneWitness source target ≃
          twoWitnesses source target)) := by
  constructor
  · exact (all_mayPullback_eq_iff_same_support
      oneWitness twoWitnesses).2 fun source target => by
        change Nonempty Unit ↔ Nonempty Bool
        constructor
        · intro _inhabited
          exact ⟨true⟩
        · intro _inhabited
          exact ⟨()⟩
  · intro pointwise
    exact unit_not_equivalent_to_bool (pointwise () ())

theorem twoWitnesses_support_total_functional :
    SupportTotal twoWitnesses ∧ SupportFunctional twoWitnesses := by
  constructor
  · intro _source
    exact ⟨(), ⟨false⟩⟩
  · intro _source firstTarget secondTarget _firstRelated _secondRelated
    exact Subsingleton.elim _ _

theorem twoWitnesses_not_representable :
    ¬ Nonempty (Representation twoWitnesses) := by
  rintro ⟨representation⟩
  have fibreSubsingleton : Subsingleton (twoWitnesses () ()) :=
    Representation.fibreSubsingleton representation.deterministic () ()
  have impossible : false = true :=
    fibreSubsingleton.allEq false true
  exact Bool.false_ne_true impossible

/-- Functional predicate behavior is strictly weaker than an executable
representation: duplicate retained witnesses are invisible to may and must. -/
theorem predicate_functional_but_not_proof_representable :
    (∀ predicate : Set Unit,
      mayPullback twoWitnesses predicate =
        mustPullback twoWitnesses predicate) ∧
      ¬ Nonempty (Representation twoWitnesses) :=
  ⟨(all_may_eq_must_iff_support_total_functional twoWitnesses).2
      twoWitnesses_support_total_functional,
    twoWitnesses_not_representable⟩

/-- A represented deterministic route gives the expected ordinary
precondition transformer. -/
theorem boolNot_pullbacks (predicate : Set Bool) :
    mayPullback (companion Bool.not) predicate =
        Set.preimage Bool.not predicate ∧
      mustPullback (companion Bool.not) predicate =
        Set.preimage Bool.not predicate :=
  ⟨mayPullback_eq_preimage
      (Representation.companionSelf Bool.not) predicate,
    mustPullback_eq_preimage
      (Representation.companionSelf Bool.not) predicate⟩

end Canary

#print axioms support_comp_iff
#print axioms mayPullback_comp
#print axioms mustPullback_comp
#print axioms mayPushforward_subset_iff_subset_mustPullback
#print axioms mayPullback_subset_iff_subset_mustPushforward
#print axioms all_may_eq_must_iff_support_total_functional
#print axioms mayPullback_eq_preimage
#print axioms mustPullback_eq_preimage
#print axioms Cell.mayPullback_lax
#print axioms Cell.mustPullback_colax
#print axioms all_mayPullback_eq_iff_same_support
#print axioms Canary.predicate_view_agrees_but_witnesses_do_not
#print axioms Canary.predicate_functional_but_not_proof_representable
#print axioms Canary.boolNot_pullbacks

end Mettapedia.GSLT.LooseRelationPredicateTransformers
