import Mettapedia.GSLT.Core.ObservedBisimulation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Basic

/-!
# Hennessy–Milner adequacy over the equation quotient

A GSLT carries an equivalence on terms (the equations) and a step relation
that respects it.  Bisimilarity and logical equivalence are therefore
properties of equation classes, and the finiteness hypothesis of the
Hennessy–Milner theorem must be read on classes: a term may have infinitely
many successor representatives while having finitely many successor classes.

This module proves, for a labeled family of steps and an explicit observation
set, both of which respect the equations:

* bisimilarity implies logical equivalence for the full fragment
  (truth, atoms, conjunction, negation, diamond);
* under image-finiteness modulo the equations, logical equivalence implies
  bisimilarity, so the two coincide;
* for the negation-free fragment (with falsity and disjunction), the logical
  preorder coincides with the simulation preorder under the same hypothesis;
* both converses also hold under finite successor covers by actual bisimilarity,
  without replacing the authored equations;
* the equations themselves are bisimulations, so every notion descends to the
  quotient, where the theorem is restated.

The unlabeled instance (one label, the GSLT step) recovers the observed
bisimilarity of `ObservedGSLT`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner

universe uAtom uLabel

/-- A GSLT with an explicit observation set and a labeled family of steps,
all respecting the equations. -/
structure System (S : GSLT) where
  /-- The observation set. -/
  Atom : Type uAtom
  /-- Atomic observations. -/
  observes : Atom → S.Term → Prop
  /-- Observations cannot separate equated terms. -/
  observes_resp : ∀ (atom : Atom) {left right : S.Term},
    S.Equiv left right → (observes atom left ↔ observes atom right)
  /-- The labels of the step family. -/
  Label : Type uLabel
  /-- The labeled steps. -/
  act : Label → S.Term → S.Term → Prop
  /-- Steps transfer along the equations on the source, up to the equations
  on the target. -/
  act_resp_left : ∀ {label : Label} {left right target : S.Term},
    S.Equiv left right → act label left target →
      ∃ target', act label right target' ∧ S.Equiv target target'
  /-- Targets are closed under the equations. -/
  act_resp_right : ∀ {label : Label} {source target target' : S.Term},
    act label source target → S.Equiv target target' → act label source target'

/-! ## The full fragment -/

/-- Hennessy–Milner formulas: truth, atoms, conjunction, negation, diamond. -/
inductive Formula (Atom : Type uAtom) (Label : Type uLabel) :
    Type (max uAtom uLabel) where
  | top : Formula Atom Label
  | atom (atom : Atom) : Formula Atom Label
  | conj (left right : Formula Atom Label) : Formula Atom Label
  | neg (inner : Formula Atom Label) : Formula Atom Label
  | dia (label : Label) (inner : Formula Atom Label) : Formula Atom Label

/-- Finite conjunction. -/
def Formula.conjList {Atom : Type uAtom} {Label : Type uLabel} :
    List (Formula Atom Label) → Formula Atom Label
  | [] => .top
  | formula :: formulas => .conj formula (Formula.conjList formulas)

/-- Negation-free formulas: truth, falsity, atoms, conjunction, disjunction,
diamond. -/
inductive PosFormula (Atom : Type uAtom) (Label : Type uLabel) :
    Type (max uAtom uLabel) where
  | top : PosFormula Atom Label
  | bot : PosFormula Atom Label
  | atom (atom : Atom) : PosFormula Atom Label
  | conj (left right : PosFormula Atom Label) : PosFormula Atom Label
  | disj (left right : PosFormula Atom Label) : PosFormula Atom Label
  | dia (label : Label) (inner : PosFormula Atom Label) : PosFormula Atom Label

/-- Finite conjunction. -/
def PosFormula.conjList {Atom : Type uAtom} {Label : Type uLabel} :
    List (PosFormula Atom Label) → PosFormula Atom Label
  | [] => .top
  | formula :: formulas => .conj formula (PosFormula.conjList formulas)

variable {S : GSLT} (M : System.{uAtom, uLabel} S)

namespace System

/-- Satisfaction. -/
def sat : Formula M.Atom M.Label → S.Term → Prop
  | .top, _ => True
  | .atom atom, term => M.observes atom term
  | .conj left right, term => sat left term ∧ sat right term
  | .neg inner, term => ¬ sat inner term
  | .dia label inner, term => ∃ target, M.act label term target ∧ sat inner target

theorem sat_conjList (formulas : List (Formula M.Atom M.Label)) (term : S.Term) :
    M.sat (Formula.conjList formulas) term ↔
      ∀ formula ∈ formulas, M.sat formula term := by
  induction formulas with
  | nil => simp [Formula.conjList, sat]
  | cons formula formulas inductionHypothesis =>
      simp [Formula.conjList, sat, inductionHypothesis]

/-- Satisfaction respects the equations: every formula is a predicate on
classes. -/
theorem sat_resp : ∀ (formula : Formula M.Atom M.Label) {left right : S.Term},
    S.Equiv left right → (M.sat formula left ↔ M.sat formula right)
  | .top, _, _, _ => Iff.rfl
  | .atom atom, _, _, equivalent => M.observes_resp atom equivalent
  | .conj left right, _, _, equivalent =>
      and_congr (sat_resp left equivalent) (sat_resp right equivalent)
  | .neg inner, _, _, equivalent => not_congr (sat_resp inner equivalent)
  | .dia label inner, _, _, equivalent => by
      constructor
      · rintro ⟨target, step, holds⟩
        obtain ⟨target', step', targetEquivalent⟩ := M.act_resp_left equivalent step
        exact ⟨target', step', (sat_resp inner targetEquivalent).mp holds⟩
      · rintro ⟨target, step, holds⟩
        obtain ⟨target', step', targetEquivalent⟩ :=
          M.act_resp_left (S.equations.iseqv.symm equivalent) step
        exact ⟨target', step', (sat_resp inner targetEquivalent).mp holds⟩

/-- Logical equivalence: the same formulas hold. -/
def LogicallyEquivalent (left right : S.Term) : Prop :=
  ∀ formula : Formula M.Atom M.Label, M.sat formula left ↔ M.sat formula right

theorem logicallyEquivalent_refl (term : S.Term) : M.LogicallyEquivalent term term :=
  fun _ => Iff.rfl

theorem logicallyEquivalent_symm {left right : S.Term}
    (equivalent : M.LogicallyEquivalent left right) : M.LogicallyEquivalent right left :=
  fun formula => (equivalent formula).symm

theorem logicallyEquivalent_trans {left middle right : S.Term}
    (first : M.LogicallyEquivalent left middle) (second : M.LogicallyEquivalent middle right) :
    M.LogicallyEquivalent left right :=
  fun formula => (first formula).trans (second formula)

theorem logicallyEquivalent_of_equiv {left right : S.Term} (equivalent : S.Equiv left right) :
    M.LogicallyEquivalent left right :=
  fun formula => M.sat_resp formula equivalent

/-! ## Bisimulation with observations -/

/-- A labeled bisimulation that also preserves every observation. -/
def IsBisimulation (relation : S.Term → S.Term → Prop) : Prop :=
  (∀ ⦃left right⦄, relation left right → ∀ (label : M.Label) ⦃left'⦄,
      M.act label left left' → ∃ right', M.act label right right' ∧ relation left' right') ∧
    (∀ ⦃left right⦄, relation left right → ∀ (label : M.Label) ⦃right'⦄,
      M.act label right right' → ∃ left', M.act label left left' ∧ relation left' right') ∧
    (∀ ⦃left right⦄, relation left right → ∀ atom,
      M.observes atom left ↔ M.observes atom right)

/-- Bisimilarity: the union of all bisimulations. -/
def Bisimilar (left right : S.Term) : Prop :=
  ∃ relation, M.IsBisimulation relation ∧ relation left right

theorem bisimilar_symm {left right : S.Term} (bisimilar : M.Bisimilar left right) :
    M.Bisimilar right left := by
  obtain ⟨relation, ⟨forward, backward, atoms⟩, related⟩ := bisimilar
  refine ⟨fun first second => relation second first, ⟨?_, ?_, ?_⟩, related⟩
  · intro left right related label left' step
    exact backward related label step
  · intro left right related label right' step
    exact forward related label step
  · intro left right related atom
    exact (atoms related atom).symm

theorem bisimilar_trans {left middle right : S.Term}
    (first : M.Bisimilar left middle) (second : M.Bisimilar middle right) :
    M.Bisimilar left right := by
  obtain ⟨firstRelation, ⟨firstForward, firstBackward, firstAtoms⟩, leftMiddle⟩ := first
  obtain ⟨secondRelation, ⟨secondForward, secondBackward, secondAtoms⟩, middleRight⟩ :=
    second
  refine ⟨fun source target => ∃ bridge, firstRelation source bridge ∧ secondRelation bridge target,
    ⟨?_, ?_, ?_⟩, middle, leftMiddle, middleRight⟩
  · rintro source target ⟨bridge, sourceBridge, bridgeTarget⟩ label source' step
    obtain ⟨bridge', bridgeStep, sourceBridge'⟩ := firstForward sourceBridge label step
    obtain ⟨target', targetStep, bridgeTarget'⟩ := secondForward bridgeTarget label bridgeStep
    exact ⟨target', targetStep, bridge', sourceBridge', bridgeTarget'⟩
  · rintro source target ⟨bridge, sourceBridge, bridgeTarget⟩ label target' step
    obtain ⟨bridge', bridgeStep, bridgeTarget'⟩ := secondBackward bridgeTarget label step
    obtain ⟨source', sourceStep, sourceBridge'⟩ := firstBackward sourceBridge label bridgeStep
    exact ⟨source', sourceStep, bridge', sourceBridge', bridgeTarget'⟩
  · rintro source target ⟨bridge, sourceBridge, bridgeTarget⟩ atom
    exact (firstAtoms sourceBridge atom).trans (secondAtoms bridgeTarget atom)

/-- The equations form a bisimulation: equated terms are bisimilar. -/
theorem bisimilar_of_equiv {left right : S.Term} (equivalent : S.Equiv left right) :
    M.Bisimilar left right := by
  refine ⟨S.Equiv, ⟨?_, ?_, ?_⟩, equivalent⟩
  · intro left right related label left' step
    exact M.act_resp_left related step
  · intro left right related label right' step
    obtain ⟨left', step', equivalent'⟩ :=
      M.act_resp_left (S.equations.iseqv.symm related) step
    exact ⟨left', step', S.equations.iseqv.symm equivalent'⟩
  · intro left right related atom
    exact M.observes_resp atom related

theorem bisimilar_refl (term : S.Term) : M.Bisimilar term term :=
  M.bisimilar_of_equiv (S.equations.iseqv.refl term)

/-! ## Adequacy, soundness direction -/

theorem sat_iff_of_isBisimulation {relation : S.Term → S.Term → Prop}
    (bisimulation : M.IsBisimulation relation) :
    ∀ (formula : Formula M.Atom M.Label) {left right : S.Term},
      relation left right → (M.sat formula left ↔ M.sat formula right)
  | .top, _, _, _ => Iff.rfl
  | .atom atom, _, _, related => bisimulation.2.2 related atom
  | .conj left right, _, _, related =>
      and_congr (sat_iff_of_isBisimulation bisimulation left related)
        (sat_iff_of_isBisimulation bisimulation right related)
  | .neg inner, _, _, related =>
      not_congr (sat_iff_of_isBisimulation bisimulation inner related)
  | .dia label inner, _, _, related => by
      constructor
      · rintro ⟨target, step, holds⟩
        obtain ⟨target', step', related'⟩ := bisimulation.1 related label step
        exact ⟨target', step',
          (sat_iff_of_isBisimulation bisimulation inner related').mp holds⟩
      · rintro ⟨target, step, holds⟩
        obtain ⟨target', step', related'⟩ := bisimulation.2.1 related label step
        exact ⟨target', step',
          (sat_iff_of_isBisimulation bisimulation inner related').mpr holds⟩

/-- Bisimilar terms satisfy the same formulas. -/
theorem logicallyEquivalent_of_bisimilar {left right : S.Term}
    (bisimilar : M.Bisimilar left right) : M.LogicallyEquivalent left right := by
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  intro formula
  exact M.sat_iff_of_isBisimulation bisimulation formula related

/-! ## Adequacy, completeness direction -/

/-- Each labelled successor set has a finite cover by the specified relation.
The covering representatives need not themselves be successors. -/
def ImageFiniteUpTo (relation : S.Term → S.Term → Prop) : Prop :=
  ∀ (label : M.Label) (term : S.Term),
    ∃ representatives : Set S.Term, representatives.Finite ∧
      ∀ ⦃target⦄, M.act label term target →
        ∃ representative ∈ representatives, relation target representative

/-- Image-finiteness modulo the authored equations. -/
def ImageFiniteModulo : Prop := M.ImageFiniteUpTo S.Equiv

/-- A finite cover by actual bisimilarity, without changing the authored equations. -/
def ImageFiniteBisimilar : Prop := M.ImageFiniteUpTo M.Bisimilar

theorem imageFiniteUpTo_mono {first second : S.Term → S.Term → Prop}
    (included : ∀ {left right}, first left right → second left right)
    (finite : M.ImageFiniteUpTo first) : M.ImageFiniteUpTo second := by
  intro label term
  obtain ⟨representatives, hFinite, covered⟩ := finite label term
  refine ⟨representatives, hFinite, ?_⟩
  intro target step
  obtain ⟨representative, hMember, related⟩ := covered step
  exact ⟨representative, hMember, included related⟩

theorem imageFiniteBisimilar_of_imageFiniteModulo (finite : M.ImageFiniteModulo) :
    M.ImageFiniteBisimilar :=
  M.imageFiniteUpTo_mono M.bisimilar_of_equiv finite

/-- A formula true at one term and false at another logically inequivalent
term, oriented by negation when needed. -/
theorem exists_separating_formula {left right : S.Term}
    (inequivalent : ¬ M.LogicallyEquivalent left right) :
    ∃ formula : Formula M.Atom M.Label, M.sat formula left ∧ ¬ M.sat formula right := by
  obtain ⟨formula, disagreement⟩ := not_forall.mp inequivalent
  by_cases leftHolds : M.sat formula left
  · refine ⟨formula, leftHolds, ?_⟩
    intro rightHolds
    exact disagreement ⟨fun _ => rightHolds, fun _ => leftHolds⟩
  · refine ⟨.neg formula, leftHolds, ?_⟩
    intro rightFails
    exact disagreement ⟨fun holds => absurd holds leftHolds, fun holds => absurd holds rightFails⟩

/-- One finite-cover distinguishing-formula argument. Only satisfaction
invariance is used; no equation or step closure is imposed on the cover. -/
theorem exists_matching_step_of_finite_cover {cover : S.Term → S.Term → Prop}
    (respect : ∀ (formula : Formula M.Atom M.Label) {first second},
      cover first second → (M.sat formula first ↔ M.sat formula second))
    (finite : M.ImageFiniteUpTo cover)
    {left right : S.Term} (equivalent : M.LogicallyEquivalent left right)
    (label : M.Label) {left' : S.Term} (step : M.act label left left') :
    ∃ right', M.act label right right' ∧ M.LogicallyEquivalent left' right' := by
  by_contra noMatch
  have unmatched : ∀ right', M.act label right right' → ¬ M.LogicallyEquivalent left' right' := by
    intro right' step' equivalent'
    exact noMatch ⟨right', step', equivalent'⟩
  have separators : ∀ candidate : S.Term,
      ∃ formula : Formula M.Atom M.Label,
        M.sat formula left' ∧
          ((∃ target, M.act label right target ∧ cover target candidate) →
            ¬ M.sat formula candidate) := by
    intro candidate
    by_cases reachable : ∃ target, M.act label right target ∧ cover target candidate
    · obtain ⟨target, actualStep, related⟩ := reachable
      have inequivalent : ¬ M.LogicallyEquivalent left' candidate := by
        intro equivalentCandidate
        exact unmatched target actualStep (fun formula =>
          (equivalentCandidate formula).trans (respect formula related).symm)
      obtain ⟨formula, holds, fails⟩ := M.exists_separating_formula inequivalent
      exact ⟨formula, holds, fun _ => fails⟩
    · exact ⟨.top, trivial, fun reached => absurd reached reachable⟩
  choose separator separatorHolds separatorFails using separators
  obtain ⟨representatives, representativesFinite, covered⟩ := finite label right
  obtain ⟨finiteRepresentatives, coe⟩ := representativesFinite.exists_finset_coe
  let bundle : Formula M.Atom M.Label :=
    Formula.conjList (finiteRepresentatives.toList.map separator)
  have leftSatisfies : M.sat (.dia label bundle) left := by
    refine ⟨left', step, ?_⟩
    rw [sat_conjList]
    intro formula membership
    obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp membership
    exact separatorHolds candidate
  have rightSatisfies : M.sat (.dia label bundle) right :=
    (equivalent (.dia label bundle)).mp leftSatisfies
  obtain ⟨right', step', holds⟩ := rightSatisfies
  obtain ⟨representative, membership, representativeEquivalent⟩ := covered step'
  have representativeHolds : M.sat (separator representative) representative := by
    have holdsAtTarget : M.sat (separator representative) right' := by
      rw [sat_conjList] at holds
      apply holds
      apply List.mem_map.mpr
      refine ⟨representative, ?_, rfl⟩
      rw [Finset.mem_toList]
      have : representative ∈ (finiteRepresentatives : Set S.Term) := by
        rw [coe]
        exact membership
      exact Finset.mem_coe.mp this
    exact (respect (separator representative) representativeEquivalent).mp holdsAtTarget
  exact separatorFails representative ⟨right', step', representativeEquivalent⟩ representativeHolds

/-- The original equation-cover endpoint of the common completeness argument. -/
theorem exists_matching_step (finite : M.ImageFiniteModulo)
    {left right : S.Term} (equivalent : M.LogicallyEquivalent left right)
    (label : M.Label) {left' : S.Term} (step : M.act label left left') :
    ∃ right', M.act label right right' ∧ M.LogicallyEquivalent left' right' :=
  M.exists_matching_step_of_finite_cover M.sat_resp finite equivalent label step

/-- Logical equivalence is a bisimulation under any finite successor cover
whose relation preserves satisfaction of the existing formulas. -/
theorem isBisimulation_logicallyEquivalent_of_finite_cover {cover : S.Term → S.Term → Prop}
    (respect : ∀ (formula : Formula M.Atom M.Label) {first second},
      cover first second → (M.sat formula first ↔ M.sat formula second))
    (finite : M.ImageFiniteUpTo cover) :
    M.IsBisimulation M.LogicallyEquivalent := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right equivalent label left' step
    exact M.exists_matching_step_of_finite_cover respect finite equivalent label step
  · intro left right equivalent label right' step
    obtain ⟨left', step', equivalent'⟩ :=
      M.exists_matching_step_of_finite_cover respect finite
        (M.logicallyEquivalent_symm equivalent) label step
    exact ⟨left', step', M.logicallyEquivalent_symm equivalent'⟩
  · intro left right equivalent atom
    exact equivalent (.atom atom)

/-- Logical equivalence is a bisimulation under the original equation cover. -/
theorem isBisimulation_logicallyEquivalent (finite : M.ImageFiniteModulo) :
    M.IsBisimulation M.LogicallyEquivalent :=
  M.isBisimulation_logicallyEquivalent_of_finite_cover M.sat_resp finite

/-- Bisimilar covering pairs already preserve satisfaction, independently of
any completeness or image-finiteness premise. -/
theorem isBisimulation_logicallyEquivalent_of_imageFiniteBisimilar
    (finite : M.ImageFiniteBisimilar) : M.IsBisimulation M.LogicallyEquivalent :=
  M.isBisimulation_logicallyEquivalent_of_finite_cover
    (fun formula {first second} related =>
      M.logicallyEquivalent_of_bisimilar (left := first) (right := second) related formula) finite

theorem bisimilar_of_logicallyEquivalent_of_imageFiniteBisimilar
    (finite : M.ImageFiniteBisimilar) {left right : S.Term}
    (equivalent : M.LogicallyEquivalent left right) : M.Bisimilar left right :=
  ⟨M.LogicallyEquivalent, M.isBisimulation_logicallyEquivalent_of_imageFiniteBisimilar finite,
    equivalent⟩

/-- Full HML adequacy under finite behavioral covers. The authored equations
remain exactly those of S. -/
theorem logicallyEquivalent_iff_bisimilar_of_imageFiniteBisimilar
    (finite : M.ImageFiniteBisimilar) (left right : S.Term) :
    M.LogicallyEquivalent left right ↔ M.Bisimilar left right :=
  ⟨M.bisimilar_of_logicallyEquivalent_of_imageFiniteBisimilar finite,
    M.logicallyEquivalent_of_bisimilar⟩

/-- Logically equivalent terms are bisimilar (image-finite modulo the
equations). -/
theorem bisimilar_of_logicallyEquivalent (finite : M.ImageFiniteModulo)
    {left right : S.Term} (equivalent : M.LogicallyEquivalent left right) :
    M.Bisimilar left right :=
  ⟨M.LogicallyEquivalent, M.isBisimulation_logicallyEquivalent finite, equivalent⟩

/-- Hennessy–Milner adequacy for the full fragment. -/
theorem logicallyEquivalent_iff_bisimilar (finite : M.ImageFiniteModulo)
    (left right : S.Term) :
    M.LogicallyEquivalent left right ↔ M.Bisimilar left right :=
  ⟨M.bisimilar_of_logicallyEquivalent finite, M.logicallyEquivalent_of_bisimilar⟩

/-! ## The negation-free fragment and the simulation preorder -/

/-- Satisfaction of negation-free formulas. -/
def psat : PosFormula M.Atom M.Label → S.Term → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atom atom, term => M.observes atom term
  | .conj left right, term => psat left term ∧ psat right term
  | .disj left right, term => psat left term ∨ psat right term
  | .dia label inner, term => ∃ target, M.act label term target ∧ psat inner target

theorem psat_conjList (formulas : List (PosFormula M.Atom M.Label)) (term : S.Term) :
    M.psat (PosFormula.conjList formulas) term ↔
      ∀ formula ∈ formulas, M.psat formula term := by
  induction formulas with
  | nil => simp [PosFormula.conjList, psat]
  | cons formula formulas inductionHypothesis =>
      simp [PosFormula.conjList, psat, inductionHypothesis]

theorem psat_resp : ∀ (formula : PosFormula M.Atom M.Label) {left right : S.Term},
    S.Equiv left right → (M.psat formula left ↔ M.psat formula right)
  | .top, _, _, _ => Iff.rfl
  | .bot, _, _, _ => Iff.rfl
  | .atom atom, _, _, equivalent => M.observes_resp atom equivalent
  | .conj left right, _, _, equivalent =>
      and_congr (psat_resp left equivalent) (psat_resp right equivalent)
  | .disj left right, _, _, equivalent =>
      or_congr (psat_resp left equivalent) (psat_resp right equivalent)
  | .dia label inner, _, _, equivalent => by
      constructor
      · rintro ⟨target, step, holds⟩
        obtain ⟨target', step', targetEquivalent⟩ := M.act_resp_left equivalent step
        exact ⟨target', step', (psat_resp inner targetEquivalent).mp holds⟩
      · rintro ⟨target, step, holds⟩
        obtain ⟨target', step', targetEquivalent⟩ :=
          M.act_resp_left (S.equations.iseqv.symm equivalent) step
        exact ⟨target', step', (psat_resp inner targetEquivalent).mp holds⟩

/-- The logical preorder: every negation-free formula true on the left is
true on the right. -/
def LogicalPreorder (left right : S.Term) : Prop :=
  ∀ formula : PosFormula M.Atom M.Label, M.psat formula left → M.psat formula right

/-- A simulation that preserves observations forward. -/
def IsSimulation (relation : S.Term → S.Term → Prop) : Prop :=
  (∀ ⦃left right⦄, relation left right → ∀ (label : M.Label) ⦃left'⦄,
      M.act label left left' → ∃ right', M.act label right right' ∧ relation left' right') ∧
    (∀ ⦃left right⦄, relation left right → ∀ atom,
      M.observes atom left → M.observes atom right)

/-- The simulation preorder. -/
def Similar (left right : S.Term) : Prop :=
  ∃ relation, M.IsSimulation relation ∧ relation left right

theorem psat_of_isSimulation {relation : S.Term → S.Term → Prop}
    (simulation : M.IsSimulation relation) :
    ∀ (formula : PosFormula M.Atom M.Label) {left right : S.Term},
      relation left right → M.psat formula left → M.psat formula right
  | .top, _, _, _, _ => trivial
  | .bot, _, _, _, absurd => absurd
  | .atom atom, _, _, related, holds => simulation.2 related atom holds
  | .conj left right, _, _, related, ⟨leftHolds, rightHolds⟩ =>
      ⟨psat_of_isSimulation simulation left related leftHolds,
        psat_of_isSimulation simulation right related rightHolds⟩
  | .disj left right, _, _, related, holds =>
      holds.elim (fun leftHolds => Or.inl (psat_of_isSimulation simulation left related leftHolds))
        (fun rightHolds => Or.inr (psat_of_isSimulation simulation right related rightHolds))
  | .dia label inner, _, _, related, ⟨target, step, holds⟩ => by
      obtain ⟨target', step', related'⟩ := simulation.1 related label step
      exact ⟨target', step', psat_of_isSimulation simulation inner related' holds⟩

/-- Similar terms are logically ordered. -/
theorem logicalPreorder_of_similar {left right : S.Term} (similar : M.Similar left right) :
    M.LogicalPreorder left right := by
  obtain ⟨relation, simulation, related⟩ := similar
  intro formula holds
  exact M.psat_of_isSimulation simulation formula related holds

/-- Forgetting the backward step and observation implications gives a simulation. -/
theorem similar_of_bisimilar {left right : S.Term} (related : M.Bisimilar left right) :
    M.Similar left right := by
  obtain ⟨relation, bisimulation, pair⟩ := related
  exact ⟨relation, ⟨bisimulation.1, fun {first second} related atom =>
    (bisimulation.2.2 (left := first) (right := second) related atom).mp⟩, pair⟩

/-- Unconditional simulation soundness in both directions supplies positive
satisfaction invariance for the behavioral cover. No completeness is used. -/
theorem psat_iff_of_bisimilar (formula : PosFormula M.Atom M.Label)
    {left right : S.Term} (related : M.Bisimilar left right) :
    M.psat formula left ↔ M.psat formula right :=
  ⟨M.logicalPreorder_of_similar (M.similar_of_bisimilar related) formula,
    M.logicalPreorder_of_similar (M.similar_of_bisimilar (M.bisimilar_symm related)) formula⟩

/-- One finite-cover transfer argument for the simulation preorder. A failure
of the preorder is already an oriented positive separator, so no negation is
needed. Covering representatives need not themselves be successors. -/
theorem exists_matching_step_pos_of_finite_cover {cover : S.Term → S.Term → Prop}
    (respect : ∀ (formula : PosFormula M.Atom M.Label) {first second},
      cover first second → (M.psat formula first ↔ M.psat formula second))
    (finite : M.ImageFiniteUpTo cover)
    {left right : S.Term} (ordered : M.LogicalPreorder left right)
    (label : M.Label) {left' : S.Term} (step : M.act label left left') :
    ∃ right', M.act label right right' ∧ M.LogicalPreorder left' right' := by
  by_contra noMatch
  have unmatched : ∀ right', M.act label right right' → ¬ M.LogicalPreorder left' right' := by
    intro right' step' ordered'
    exact noMatch ⟨right', step', ordered'⟩
  have separators : ∀ candidate : S.Term,
      ∃ formula : PosFormula M.Atom M.Label,
        M.psat formula left' ∧
          ((∃ target, M.act label right target ∧ cover target candidate) →
            ¬ M.psat formula candidate) := by
    intro candidate
    by_cases reachable : ∃ target, M.act label right target ∧ cover target candidate
    · obtain ⟨target, actualStep, related⟩ := reachable
      have notOrdered : ¬ M.LogicalPreorder left' candidate := by
        intro orderedCandidate
        exact unmatched target actualStep (fun formula holds =>
          (respect formula related).mpr (orderedCandidate formula holds))
      obtain ⟨formula, disagreement⟩ := not_forall.mp notOrdered
      have holds : M.psat formula left' := by
        by_contra fails
        exact disagreement fun holds => absurd holds fails
      exact ⟨formula, holds, fun _ fails => disagreement fun _ => fails⟩
    · exact ⟨.top, trivial, fun reached => absurd reached reachable⟩
  choose separator separatorHolds separatorFails using separators
  obtain ⟨representatives, representativesFinite, covered⟩ := finite label right
  obtain ⟨finiteRepresentatives, coe⟩ := representativesFinite.exists_finset_coe
  let bundle : PosFormula M.Atom M.Label :=
    PosFormula.conjList (finiteRepresentatives.toList.map separator)
  have leftSatisfies : M.psat (.dia label bundle) left := by
    refine ⟨left', step, ?_⟩
    rw [psat_conjList]
    intro formula membership
    obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp membership
    exact separatorHolds candidate
  have rightSatisfies : M.psat (.dia label bundle) right :=
    ordered (.dia label bundle) leftSatisfies
  obtain ⟨right', step', holds⟩ := rightSatisfies
  obtain ⟨representative, membership, representativeEquivalent⟩ := covered step'
  have representativeHolds : M.psat (separator representative) representative := by
    have holdsAtTarget : M.psat (separator representative) right' := by
      rw [psat_conjList] at holds
      apply holds
      apply List.mem_map.mpr
      refine ⟨representative, ?_, rfl⟩
      rw [Finset.mem_toList]
      have : representative ∈ (finiteRepresentatives : Set S.Term) := by
        rw [coe]
        exact membership
      exact Finset.mem_coe.mp this
    exact (respect (separator representative) representativeEquivalent).mp holdsAtTarget
  exact separatorFails representative ⟨right', step', representativeEquivalent⟩ representativeHolds

/-- The original equation-cover endpoint of the positive transfer argument. -/
theorem exists_matching_step_pos (finite : M.ImageFiniteModulo)
    {left right : S.Term} (ordered : M.LogicalPreorder left right)
    (label : M.Label) {left' : S.Term} (step : M.act label left left') :
    ∃ right', M.act label right right' ∧ M.LogicalPreorder left' right' :=
  M.exists_matching_step_pos_of_finite_cover M.psat_resp finite ordered label step

theorem isSimulation_logicalPreorder_of_finite_cover {cover : S.Term → S.Term → Prop}
    (respect : ∀ (formula : PosFormula M.Atom M.Label) {first second},
      cover first second → (M.psat formula first ↔ M.psat formula second))
    (finite : M.ImageFiniteUpTo cover) :
    M.IsSimulation M.LogicalPreorder := by
  refine ⟨?_, ?_⟩
  · intro left right ordered label left' step
    exact M.exists_matching_step_pos_of_finite_cover respect finite ordered label step
  · intro left right ordered atom holds
    exact ordered (.atom atom) holds

theorem isSimulation_logicalPreorder (finite : M.ImageFiniteModulo) :
    M.IsSimulation M.LogicalPreorder :=
  M.isSimulation_logicalPreorder_of_finite_cover M.psat_resp finite

theorem isSimulation_logicalPreorder_of_imageFiniteBisimilar (finite : M.ImageFiniteBisimilar) :
    M.IsSimulation M.LogicalPreorder :=
  M.isSimulation_logicalPreorder_of_finite_cover M.psat_iff_of_bisimilar finite

theorem similar_of_logicalPreorder_of_imageFiniteBisimilar (finite : M.ImageFiniteBisimilar)
    {left right : S.Term} (ordered : M.LogicalPreorder left right) : M.Similar left right :=
  ⟨M.LogicalPreorder, M.isSimulation_logicalPreorder_of_imageFiniteBisimilar finite, ordered⟩

/-- Positive HML adequacy under the same finite behavioral-cover hypothesis
as the full-fragment theorem. The authored equations remain unchanged. -/
theorem logicalPreorder_iff_similar_of_imageFiniteBisimilar (finite : M.ImageFiniteBisimilar)
    (left right : S.Term) : M.LogicalPreorder left right ↔ M.Similar left right :=
  ⟨M.similar_of_logicalPreorder_of_imageFiniteBisimilar finite, M.logicalPreorder_of_similar⟩

/-- Logically ordered terms are similar (image-finite modulo the equations). -/
theorem similar_of_logicalPreorder (finite : M.ImageFiniteModulo)
    {left right : S.Term} (ordered : M.LogicalPreorder left right) :
    M.Similar left right :=
  ⟨M.LogicalPreorder, M.isSimulation_logicalPreorder finite, ordered⟩

/-- Hennessy–Milner adequacy for the negation-free fragment: the logical
preorder is the simulation preorder. -/
theorem logicalPreorder_iff_similar (finite : M.ImageFiniteModulo) (left right : S.Term) :
    M.LogicalPreorder left right ↔ M.Similar left right :=
  ⟨M.similar_of_logicalPreorder finite, M.logicalPreorder_of_similar⟩

/-! ## Descent to the quotient -/

/-- Bisimilarity on equation classes. -/
def bisimilarClass : Quotient S.equations → Quotient S.equations → Prop :=
  Quotient.lift₂ M.Bisimilar fun _ _ _ _ leftEquivalent rightEquivalent =>
    propext ⟨fun bisimilar =>
        M.bisimilar_trans (M.bisimilar_of_equiv (S.equations.iseqv.symm leftEquivalent))
          (M.bisimilar_trans bisimilar (M.bisimilar_of_equiv rightEquivalent)),
      fun bisimilar =>
        M.bisimilar_trans (M.bisimilar_of_equiv leftEquivalent)
          (M.bisimilar_trans bisimilar
            (M.bisimilar_of_equiv (S.equations.iseqv.symm rightEquivalent)))⟩

/-- Logical equivalence on equation classes. -/
def logicallyEquivalentClass : Quotient S.equations → Quotient S.equations → Prop :=
  Quotient.lift₂ M.LogicallyEquivalent fun _ _ _ _ leftEquivalent rightEquivalent =>
    propext ⟨fun equivalent =>
        M.logicallyEquivalent_trans
          (M.logicallyEquivalent_of_equiv (S.equations.iseqv.symm leftEquivalent))
          (M.logicallyEquivalent_trans equivalent
            (M.logicallyEquivalent_of_equiv rightEquivalent)),
      fun equivalent =>
        M.logicallyEquivalent_trans (M.logicallyEquivalent_of_equiv leftEquivalent)
          (M.logicallyEquivalent_trans equivalent
            (M.logicallyEquivalent_of_equiv (S.equations.iseqv.symm rightEquivalent)))⟩

theorem bisimilarClass_mk (left right : S.Term) :
    M.bisimilarClass (Quotient.mk S.equations left) (Quotient.mk S.equations right) ↔
      M.Bisimilar left right :=
  Iff.rfl

theorem logicallyEquivalentClass_mk (left right : S.Term) :
    M.logicallyEquivalentClass (Quotient.mk S.equations left) (Quotient.mk S.equations right) ↔
      M.LogicallyEquivalent left right :=
  Iff.rfl

/-- Adequacy on the quotient. -/
theorem logicallyEquivalentClass_iff_bisimilarClass (finite : M.ImageFiniteModulo)
    (left right : Quotient S.equations) :
    M.logicallyEquivalentClass left right ↔ M.bisimilarClass left right := by
  induction left using Quotient.inductionOn with
  | h left =>
      induction right using Quotient.inductionOn with
      | h right => exact M.logicallyEquivalent_iff_bisimilar finite left right

/-! ## The unlabeled instance: the GSLT step with an observation set -/

/-- The system with one label whose step is the GSLT step, for observations
that respect the equations. -/
def ofObserved (observed : ObservedGSLT.{uAtom} S)
    (observes_resp : ∀ (atom : observed.Atom) {left right : S.Term},
      S.Equiv left right → (observed.observes atom left ↔ observed.observes atom right)) :
    System.{uAtom, 0} S where
  Atom := observed.Atom
  observes := observed.observes
  observes_resp := observes_resp
  Label := Unit
  act _ := S.Step
  act_resp_left equivalent step := S.rewrites_resp_left equivalent step
  act_resp_right step equivalent := S.rewrites_resp_right step equivalent

/-- Unlabeled bisimilarity is the observed bisimilarity of the GSLT. -/
theorem ofObserved_bisimilar_iff (observed : ObservedGSLT.{uAtom} S)
    (observes_resp : ∀ (atom : observed.Atom) {left right : S.Term},
      S.Equiv left right → (observed.observes atom left ↔ observed.observes atom right))
    (left right : S.Term) :
    (ofObserved observed observes_resp).Bisimilar left right ↔ observed.Bisimilar left right := by
  constructor
  · rintro ⟨relation, ⟨forward, backward, atoms⟩, related⟩
    refine ⟨relation, ⟨⟨?_, ?_⟩, atoms⟩, related⟩
    · intro left right related left' step
      exact forward related () step
    · intro left right related right' step
      exact backward related () step
  · rintro ⟨relation, ⟨⟨forward, backward⟩, atoms⟩, related⟩
    refine ⟨relation, ⟨?_, ?_, atoms⟩, related⟩
    · intro left right related _ left' step
      exact forward related step
    · intro left right related _ right' step
      exact backward related step

/-- Adequacy for the observed GSLT itself. -/
theorem observed_logicallyEquivalent_iff_bisimilar (observed : ObservedGSLT.{uAtom} S)
    (observes_resp : ∀ (atom : observed.Atom) {left right : S.Term},
      S.Equiv left right → (observed.observes atom left ↔ observed.observes atom right))
    (finite : (ofObserved observed observes_resp).ImageFiniteModulo)
    (left right : S.Term) :
    (ofObserved observed observes_resp).LogicallyEquivalent left right ↔
      observed.Bisimilar left right :=
  ((ofObserved observed observes_resp).logicallyEquivalent_iff_bisimilar finite left right).trans
    (ofObserved_bisimilar_iff observed observes_resp left right)

end System

end Mettapedia.GSLT.HennessyMilner
