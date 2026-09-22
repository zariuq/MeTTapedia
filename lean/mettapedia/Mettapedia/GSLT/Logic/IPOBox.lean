import Mettapedia.GSLT.Logic.LeastEnablerBox
import Mettapedia.GSLT.Logic.RedexRelativeCongruence
import Mathlib.Data.Set.Finite.Lattice

/-!
# The backward box over idem-pushout labels

`LeastEnablerBox` builds the backward modality over *absolute* least enabling
contexts, and that base is wrong for a reflective calculus, twice over.  A
source completable in two incomparable ways has no absolute least enabler at all
(`RedexRelativeEnabling.no_least_enabler`), so the backward system is blind
there; and where such enablers do exist they do not compose
(`ParallelLeastEnablerFails.leastEnablerComposes_fails`), so the congruence that
would justify reading the labels as observations is unavailable.

This module rebuilds the same development over the labels that do work: a label
is least *for the redex it exposes*, an idem pushout in the sense of Leifer and
Milner.  Those labels carry the forward congruence (`RedexRelativeCongruence`), they
exist for every span in the theories of interest, and the box over them is a
genuine instance of the forward Hennessy-Milner development rather than a second
theory: the generic theorem is applied to the reversed transition system.
Its backward bisimilarity is not thereby identified with forward bisimilarity.

**Where the equations went.**  The development runs in the one-object category
on a monoid, so the equations are quotiented into the monoid itself before any
of this starts: for a bag presentation, the parallel equations are multiset
equality.  Equations *beyond* the monoid's — alpha, and any equation relating
distinct components — are not present here and are not claimed to be; the
`GSLT` below therefore takes equality as its setoid, honestly, rather than
naming a larger equational theory it does not carry.

**What is and is not proved.**  The adequacy theorem takes image finiteness of
labelled predecessors modulo those equations as a hypothesis, exactly as the
forward development does; it is discharged per theory, not here.  What is proved
here without hypothesis is that the system's own bisimilarity is the one the
forward congruence theorem is about.  Backward adequacy concerns the reversed
system's own bisimilarity; no agreement with the forward relation or congruence
for the backward relation is proved here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IPOBox

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u uAtom

variable {M : Type u} [Monoid M]

/-! ## The theory of agents -/

/-- The unlabelled reaction: an agent reacts when it reacts under some least
label. -/
def Reacts (rules : ReactionRule (Obj M) → Prop) (source target : Obj M ⟶ Obj M) : Prop :=
  ∃ label, ActIPO rules label source target

/-- Agents as a `GSLT`.  The setoid is equality because the monoid has already
absorbed the equations the presentation quotients by. -/
def ipoGSLT (rules : ReactionRule (Obj M) → Prop) : GSLT where
  Term := Obj M ⟶ Obj M
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites := Reacts rules
  rewrites_resp_left := by
    rintro source source' target same react
    exact ⟨target, same ▸ react, rfl⟩
  rewrites_resp_right := by
    rintro source target target' react same
    exact same ▸ react

@[simp] theorem ipoGSLT_term (rules : ReactionRule (Obj M) → Prop) :
    (ipoGSLT rules).Term = (Obj M ⟶ Obj M) := rfl

@[simp] theorem ipoGSLT_equiv (rules : ReactionRule (Obj M) → Prop)
    (left right : Obj M ⟶ Obj M) :
    (ipoGSLT rules).Equiv left right ↔ left = right := Iff.rfl

/-! ## Observations -/

/-- An observation set on agents.  Nothing about it is assumed beyond its
existence; `noObservations` is the instance that observes nothing, and it is
what makes bisimilarity here exactly `IPOBisimilar`. -/
structure Observations (M : Type u) [Monoid M] where
  /-- The atoms. -/
  Atom : Type uAtom
  /-- What each atom observes of an agent. -/
  observes : Atom → (Obj M ⟶ Obj M) → Prop

/-- The empty observation set. -/
def noObservations (M : Type u) [Monoid M] : Observations.{u, uAtom} M where
  Atom := PEmpty
  observes := fun atom => atom.elim

/-! ## The two systems -/

/-- The forward system: labels are the idem-pushout labels, and a step is a
labelled reaction. -/
def ipoSystem (rules : ReactionRule (Obj M) → Prop) (observations : Observations.{u, uAtom} M) :
    System.{uAtom, u} (ipoGSLT rules) where
  Atom := observations.Atom
  observes := observations.observes
  observes_resp := by rintro atom left right rfl; exact Iff.rfl
  Label := Obj M ⟶ Obj M
  act := fun label source target => ActIPO rules label source target
  act_resp_left := by
    rintro label left right target rfl act
    exact ⟨target, act, rfl⟩
  act_resp_right := by
    rintro label source target target' act rfl
    exact act

/-- The backward system: the same labels and the same observations, with the
direction of the step reversed. -/
def ipoBackwardSystem (rules : ReactionRule (Obj M) → Prop)
    (observations : Observations.{u, uAtom} M) :
    System.{uAtom, u} (ipoGSLT rules) where
  Atom := observations.Atom
  observes := observations.observes
  observes_resp := by rintro atom left right rfl; exact Iff.rfl
  Label := Obj M ⟶ Obj M
  act := fun label target source => ActIPO rules label source target
  act_resp_left := by
    rintro label left right target rfl act
    exact ⟨target, act, rfl⟩
  act_resp_right := by
    rintro label source target target' act rfl
    exact act

/-- The two systems share labels, observations and theory, and differ only in
the direction of the step. -/
theorem ipoBackwardSystem_act (rules : ReactionRule (Obj M) → Prop)
    (observations : Observations.{u, uAtom} M)
    (label target source : Obj M ⟶ Obj M) :
    (ipoBackwardSystem rules observations).act label target source ↔
      (ipoSystem rules observations).act label source target :=
  Iff.rfl

/-! ## The forward system's bisimilarity is the congruence's

The forward `System` relation must be identified with the relation used by the
forward congruence theorem.  With no atomic observations these two coincide.
This identification does not concern the reversed system used by backward
adequacy below. -/

/-- **The forward system's bisimilarity is exactly `IPOBisimilar`.**  This
transports the forward congruence proved by `ipoBisimilar_comp`, not a congruence
for the backward bisimilarity characterized by the box logic below. -/
theorem bisimilar_ipoSystem_iff (rules : ReactionRule (Obj M) → Prop)
    (left right : Obj M ⟶ Obj M) :
    (ipoSystem rules (noObservations.{u, uAtom} M)).Bisimilar left right ↔
      IPOBisimilar rules left right := by
  constructor
  · rintro ⟨relation, ⟨forward, backward, -⟩, related⟩
    refine ⟨fun _ => relation, fun {_} left right related => ⟨?_, ?_⟩, related⟩
    · intro _ label next step
      exact forward related label step
    · intro _ label next step
      obtain ⟨matched, matchedStep, matchedRelated⟩ := backward related label step
      exact ⟨matched, matchedStep, matchedRelated⟩
  · rintro ⟨relation, isBisim, related⟩
    refine ⟨relation (Obj M), ⟨?_, ?_, ?_⟩, related⟩
    · intro left right related label next step
      exact (isBisim left right related).1 (nextInterface := Obj M) label next step
    · intro left right related label next step
      obtain ⟨matched, matchedStep, matchedRelated⟩ :=
        (isBisim left right related).2 (nextInterface := Obj M) label next step
      exact ⟨matched, matchedStep, matchedRelated⟩
    · rintro left right related ⟨⟩

/-- **And it is a congruence**, transported along that agreement: the system's
own bisimilarity survives composition with any context, whenever the theory has
relative pushouts for the spans that arise. -/
theorem bisimilar_ipoSystem_comp (rules : ReactionRule (Obj M) → Prop)
    (pushouts : ∀ (agent : Obj M ⟶ Obj M) (rule : ReactionRule (Obj M)), rules rule →
      HasRelativePushouts agent rule.redex)
    {left right : Obj M ⟶ Obj M}
    (bisim : (ipoSystem rules (noObservations.{u, uAtom} M)).Bisimilar left right)
    (context : Obj M ⟶ Obj M) :
    (ipoSystem rules (noObservations.{u, uAtom} M)).Bisimilar
      (CategoryStruct.comp left context) (CategoryStruct.comp right context) :=
  (bisimilar_ipoSystem_iff rules _ _).mpr
    (ipoBisimilar_comp (fun _ agent rule => pushouts agent rule) ((bisimilar_ipoSystem_iff rules left right).mp bisim) context)

/-! ## The box, and its adequacy -/

/-- Image finiteness backwards: every agent has finitely many labelled
predecessors under each label.  This is what a particular presentation must
supply; nothing here assumes it. -/
def BackwardImageFiniteModulo (rules : ReactionRule (Obj M) → Prop)
    (observations : Observations.{u, uAtom} M) : Prop :=
  (ipoBackwardSystem rules observations).ImageFiniteModulo

/-- The concrete content of that hypothesis, with the `System` wrapper removed:
for each label and agent, finitely many predecessors suffice. -/
theorem backwardImageFiniteModulo_iff (rules : ReactionRule (Obj M) → Prop)
    (observations : Observations.{u, uAtom} M) :
    BackwardImageFiniteModulo rules observations ↔
      ∀ (label target : Obj M ⟶ Obj M),
        ∃ sources : Set (Obj M ⟶ Obj M), sources.Finite ∧
          ∀ ⦃source⦄, ActIPO rules label source target → source ∈ sources := by
  constructor
  · intro finite label target
    obtain ⟨sources, isFinite, covers⟩ := finite label target
    refine ⟨sources, isFinite, fun source act => ?_⟩
    obtain ⟨representative, mem, same⟩ := covers act
    exact same ▸ mem
  · intro finite label target
    obtain ⟨sources, isFinite, covers⟩ := finite label target
    exact ⟨sources, isFinite, fun source act => ⟨source, covers act, rfl⟩⟩

/-! ## When the hypothesis holds

Backward image finiteness is not a hope for parallel presentations: it is an
arithmetic fact about them.  A cancellative context monoid pins the reaction
context to the target and the predecessor to the label, so a rule that explains
a labelled step explains exactly one predecessor, and finitely many rules leave
finitely many. -/

/-- What it takes for one rule to explain a labelled step into `target`. -/
def Explains (rule : ReactionRule (Obj M)) (label source target : Obj M ⟶ Obj M) : Prop :=
  ∃ reaction, CategoryStruct.comp source label = CategoryStruct.comp rule.redex reaction ∧
    target = CategoryStruct.comp rule.reactum reaction

theorem explains_of_actIPO {rules : ReactionRule (Obj M) → Prop}
    {label source target : Obj M ⟶ Obj M} (act : ActIPO rules label source target) :
    ∃ rule, rules rule ∧ Explains rule label source target := by
  obtain ⟨rule, isRule, reaction, square, -, shape⟩ := act
  exact ⟨rule, isRule, reaction, square, shape⟩

/-- **One rule explains at most one predecessor.**  Cancelling the reactum on
the target fixes the reaction context; cancelling the label then fixes the
predecessor. -/
theorem explains_subsingleton [IsCancelMul M] (rule : ReactionRule (Obj M))
    (label target : Obj M ⟶ Obj M) :
    {source | Explains rule label source target}.Subsingleton := by
  rintro left ⟨reactionLeft, squareLeft, shapeLeft⟩
  rintro right ⟨reactionRight, squareRight, shapeRight⟩
  simp only [SingleObj.comp_as_mul] at squareLeft squareRight shapeLeft shapeRight
  have sameReaction : reactionLeft = reactionRight :=
    mul_right_cancel (b := rule.reactum) (shapeLeft ▸ shapeRight)
  refine mul_left_cancel (a := label) ?_
  rw [squareLeft, squareRight, sameReaction]

/-- **So a finitely presented parallel theory has the backward box.**  Nothing
about the particular rules enters: cancellation of the context monoid and
finiteness of the rule set are the whole hypothesis. -/
theorem backwardImageFiniteModulo_of_cancel [IsCancelMul M]
    (rules : ReactionRule (Obj M) → Prop) (ruleFinite : {rule | rules rule}.Finite)
    (observations : Observations.{u, uAtom} M) :
    BackwardImageFiniteModulo rules observations := by
  refine (backwardImageFiniteModulo_iff rules observations).mpr ?_
  intro label target
  refine ⟨⋃ rule ∈ {rule | rules rule}, {source | Explains rule label source target},
    Set.Finite.biUnion ruleFinite
      (fun rule _ => (explains_subsingleton rule label target).finite), ?_⟩
  intro source act
  obtain ⟨rule, isRule, explains⟩ := explains_of_actIPO act
  exact Set.mem_biUnion isRule explains

/-- **Backward adequacy over idem-pushout labels.**  Logical equivalence in the
backward labelled logic coincides with backward bisimilarity, under backward
image finiteness and nothing else.  The forward development supplies the proof;
what this module supplies is the base it runs on. -/
theorem backward_logicallyEquivalent_iff_bisimilar (rules : ReactionRule (Obj M) → Prop)
    (observations : Observations.{u, uAtom} M)
    (finite : BackwardImageFiniteModulo rules observations)
    (left right : Obj M ⟶ Obj M) :
    (ipoBackwardSystem rules observations).LogicallyEquivalent left right ↔
      (ipoBackwardSystem rules observations).Bisimilar left right :=
  (ipoBackwardSystem rules observations).logicallyEquivalent_iff_bisimilar finite left right

end Mettapedia.GSLT.IPOBox
