import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.GSLT.Core.UltrainfiniteTransport

/-!
# Hennessy–Milner formulas along operational translations

A translation between two labeled systems maps terms, atoms, and labels,
respects the equations, preserves observations, and maps labeled steps.  A
cover additionally lifts every labeled step leaving a translated term back
to the source, up to the target equations.

The consequences separate cleanly:

* a translation preserves the negation-free formulas forward;
* a cover preserves and reflects every formula, so it reflects logical
  equivalence, reflects bisimilarity, and (when it reaches every atom and
  label) preserves bisimilarity.

None of these statements needs image-finiteness.  They are the formula-level
content of the slogan that exact behavioral transport needs outgoing
coverage, and they are what the indexed operational diagrams use to move
native types between fibres.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner

open Mettapedia.GSLT

universe uS uT uAtom uLabel uAtom' uLabel'

/-! ## Renaming atoms and labels -/

/-- Rename the atoms and labels of a formula. -/
def Formula.map {Atom : Type uAtom} {Label : Type uLabel} {Atom' : Type uAtom'}
    {Label' : Type uLabel'} (mapAtom : Atom → Atom') (mapLabel : Label → Label') :
    Formula Atom Label → Formula Atom' Label'
  | .top => .top
  | .atom name => .atom (mapAtom name)
  | .conj left right => .conj (map mapAtom mapLabel left) (map mapAtom mapLabel right)
  | .neg inner => .neg (map mapAtom mapLabel inner)
  | .dia label inner => .dia (mapLabel label) (map mapAtom mapLabel inner)

@[simp]
theorem Formula.map_id {Atom : Type uAtom} {Label : Type uLabel} :
    ∀ formula : Formula Atom Label, Formula.map id id formula = formula
  | .top => rfl
  | .atom _ => rfl
  | .conj left right => by rw [Formula.map, map_id left, map_id right]
  | .neg inner => by rw [Formula.map, map_id inner]
  | .dia _ inner => by rw [Formula.map, map_id inner]; rfl

/-- Rename the atoms and labels of a negation-free formula. -/
def PosFormula.map {Atom : Type uAtom} {Label : Type uLabel} {Atom' : Type uAtom'}
    {Label' : Type uLabel'} (mapAtom : Atom → Atom') (mapLabel : Label → Label') :
    PosFormula Atom Label → PosFormula Atom' Label'
  | .top => .top
  | .bot => .bot
  | .atom name => .atom (mapAtom name)
  | .conj left right => .conj (map mapAtom mapLabel left) (map mapAtom mapLabel right)
  | .disj left right => .disj (map mapAtom mapLabel left) (map mapAtom mapLabel right)
  | .dia label inner => .dia (mapLabel label) (map mapAtom mapLabel inner)

@[simp]
theorem PosFormula.map_id {Atom : Type uAtom} {Label : Type uLabel} :
    ∀ formula : PosFormula Atom Label, PosFormula.map id id formula = formula
  | .top => rfl
  | .bot => rfl
  | .atom _ => rfl
  | .conj left right => by rw [PosFormula.map, map_id left, map_id right]
  | .disj left right => by rw [PosFormula.map, map_id left, map_id right]
  | .dia _ inner => by rw [PosFormula.map, map_id inner]; rfl

/-! ## Translations and covers of labeled systems -/

variable {S : GSLT.{uS}} {T : GSLT.{uT}}

/-- A forward translation of labeled systems: equations, observations, and
labeled steps are carried to the target. -/
structure SystemTranslation (M : System.{uAtom, uLabel} S) (N : System.{uAtom', uLabel'} T) where
  mapTerm : S.Term → T.Term
  mapAtom : M.Atom → N.Atom
  mapLabel : M.Label → N.Label
  mapEquiv : ∀ {left right : S.Term}, S.Equiv left right →
    T.Equiv (mapTerm left) (mapTerm right)
  observes_iff : ∀ (atom : M.Atom) (term : S.Term),
    M.observes atom term ↔ N.observes (mapAtom atom) (mapTerm term)
  mapAct : ∀ {label : M.Label} {source target : S.Term},
    M.act label source target → N.act (mapLabel label) (mapTerm source) (mapTerm target)

/-- A translation whose every labeled step leaving a translated term lifts to
the source, up to the target equations. -/
structure SystemCover (M : System.{uAtom, uLabel} S) (N : System.{uAtom', uLabel'} T)
    extends SystemTranslation M N where
  liftAct : ∀ {label : M.Label} {source : S.Term} {target' : T.Term},
    N.act (mapLabel label) (mapTerm source) target' →
      ∃ target : S.Term, M.act label source target ∧ T.Equiv (mapTerm target) target'

namespace SystemTranslation

variable {M : System.{uAtom, uLabel} S} {N : System.{uAtom', uLabel'} T}
  (translation : SystemTranslation M N)

/-- Negation-free formulas are preserved forward by every translation. -/
theorem psat_map (formula : PosFormula M.Atom M.Label) :
    ∀ {term : S.Term}, M.psat formula term →
      N.psat (formula.map translation.mapAtom translation.mapLabel) (translation.mapTerm term) := by
  induction formula with
  | top => intro _ _; exact trivial
  | bot => intro _ holds; exact holds.elim
  | atom atom => intro term holds; exact (translation.observes_iff atom term).mp holds
  | conj _ _ leftIH rightIH => intro _ holds; exact ⟨leftIH holds.1, rightIH holds.2⟩
  | disj _ _ leftIH rightIH =>
      intro _ holds
      exact holds.elim (fun holds => Or.inl (leftIH holds)) (fun holds => Or.inr (rightIH holds))
  | dia _ _ innerIH =>
      rintro _ ⟨target, step, holds⟩
      exact ⟨translation.mapTerm target, translation.mapAct step, innerIH holds⟩

/-- The logical preorder on the source is reflected from the preorder of the
translated terms on the mapped formulas only as far as the positive fragment
is preserved: a translation carries the preorder forward on its image. -/
theorem logicalPreorder_map {left right : S.Term}
    (preorder : ∀ formula : PosFormula M.Atom M.Label,
      N.psat (formula.map translation.mapAtom translation.mapLabel) (translation.mapTerm left) →
        N.psat (formula.map translation.mapAtom translation.mapLabel) (translation.mapTerm right))
    (reflect : ∀ formula : PosFormula M.Atom M.Label,
      N.psat (formula.map translation.mapAtom translation.mapLabel) (translation.mapTerm right) →
        M.psat formula right) :
    M.LogicalPreorder left right :=
  fun formula holds => reflect formula (preorder formula (translation.psat_map formula holds))

end SystemTranslation

namespace SystemCover

variable {M : System.{uAtom, uLabel} S} {N : System.{uAtom', uLabel'} T} (cover : SystemCover M N)

/-- A cover preserves and reflects every formula. -/
theorem sat_map (formula : Formula M.Atom M.Label) :
    ∀ term : S.Term,
      N.sat (formula.map cover.mapAtom cover.mapLabel) (cover.mapTerm term) ↔ M.sat formula term := by
  induction formula with
  | top => intro _; exact Iff.rfl
  | atom atom => intro term; exact (cover.observes_iff atom term).symm
  | conj _ _ leftIH rightIH => intro term; exact and_congr (leftIH term) (rightIH term)
  | neg _ innerIH => intro term; exact not_congr (innerIH term)
  | dia _ _ innerIH =>
      intro term
      constructor
      · rintro ⟨target', step', holds⟩
        obtain ⟨target, step, equivalent⟩ := cover.liftAct step'
        exact ⟨target, step, (innerIH target).mp ((N.sat_resp _ equivalent).mpr holds)⟩
      · rintro ⟨target, step, holds⟩
        exact ⟨cover.mapTerm target, cover.mapAct step, (innerIH target).mpr holds⟩

/-- A cover preserves and reflects every negation-free formula. -/
theorem psat_map (formula : PosFormula M.Atom M.Label) :
    ∀ term : S.Term,
      N.psat (formula.map cover.mapAtom cover.mapLabel) (cover.mapTerm term) ↔
        M.psat formula term := by
  induction formula with
  | top => intro _; exact Iff.rfl
  | bot => intro _; exact Iff.rfl
  | atom atom => intro term; exact (cover.observes_iff atom term).symm
  | conj _ _ leftIH rightIH => intro term; exact and_congr (leftIH term) (rightIH term)
  | disj _ _ leftIH rightIH => intro term; exact or_congr (leftIH term) (rightIH term)
  | dia _ _ innerIH =>
      intro term
      constructor
      · rintro ⟨target', step', holds⟩
        obtain ⟨target, step, equivalent⟩ := cover.liftAct step'
        exact ⟨target, step, (innerIH target).mp ((N.psat_resp _ equivalent).mpr holds)⟩
      · rintro ⟨target, step, holds⟩
        exact ⟨cover.mapTerm target, cover.mapAct step, (innerIH target).mpr holds⟩

/-- Logical equivalence of the translated terms reflects to the source. -/
theorem logicallyEquivalent_of_map {left right : S.Term}
    (equivalent : N.LogicallyEquivalent (cover.mapTerm left) (cover.mapTerm right)) :
    M.LogicallyEquivalent left right :=
  fun formula =>
    ((cover.sat_map formula left).symm.trans (equivalent _)).trans (cover.sat_map formula right)

/-- The logical preorder of the translated terms reflects to the source. -/
theorem logicalPreorder_of_map {left right : S.Term}
    (preorder : N.LogicalPreorder (cover.mapTerm left) (cover.mapTerm right)) :
    M.LogicalPreorder left right :=
  fun formula holds =>
    (cover.psat_map formula right).mp (preorder _ ((cover.psat_map formula left).mpr holds))

/-- Bisimilarity of the translated terms reflects to the source. -/
theorem bisimilar_of_map {left right : S.Term}
    (bisimilar : N.Bisimilar (cover.mapTerm left) (cover.mapTerm right)) :
    M.Bisimilar left right := by
  refine ⟨fun first second => N.Bisimilar (cover.mapTerm first) (cover.mapTerm second),
    ⟨?_, ?_, ?_⟩, bisimilar⟩
  · intro first second related label first' step
    obtain ⟨relation, ⟨forward, _, _⟩, relatedPair⟩ := related
    obtain ⟨second', secondStep, relatedTargets⟩ := forward relatedPair _ (cover.mapAct step)
    obtain ⟨lifted, liftedStep, equivalent⟩ := cover.liftAct secondStep
    refine ⟨lifted, liftedStep, ?_⟩
    exact N.bisimilar_trans ⟨relation, ⟨forward, ‹_›, ‹_›⟩, relatedTargets⟩
      (N.bisimilar_of_equiv (T.equations.iseqv.symm equivalent))
  · intro first second related label second' step
    obtain ⟨relation, ⟨_, backward, _⟩, relatedPair⟩ := related
    obtain ⟨first', firstStep, relatedTargets⟩ := backward relatedPair _ (cover.mapAct step)
    obtain ⟨lifted, liftedStep, equivalent⟩ := cover.liftAct firstStep
    refine ⟨lifted, liftedStep, ?_⟩
    exact N.bisimilar_trans (N.bisimilar_of_equiv equivalent)
      ⟨relation, ⟨‹_›, backward, ‹_›⟩, relatedTargets⟩
  · intro first second related atom
    obtain ⟨relation, ⟨_, _, atoms⟩, relatedPair⟩ := related
    exact (cover.observes_iff atom first).trans
      ((atoms relatedPair _).trans (cover.observes_iff atom second).symm)

/-- When the cover reaches every atom and every label, bisimilarity is also
preserved: the image of a bisimulation, closed under the target equations,
is a bisimulation. -/
theorem bisimilar_map (atomSurjective : Function.Surjective cover.mapAtom)
    (labelSurjective : Function.Surjective cover.mapLabel)
    {left right : S.Term} (bisimilar : M.Bisimilar left right) :
    N.Bisimilar (cover.mapTerm left) (cover.mapTerm right) := by
  obtain ⟨relation, ⟨forward, backward, atoms⟩, related⟩ := bisimilar
  refine ⟨fun first second => ∃ sourceFirst sourceSecond,
      T.Equiv (cover.mapTerm sourceFirst) first ∧ T.Equiv (cover.mapTerm sourceSecond) second ∧
        relation sourceFirst sourceSecond,
    ⟨?_, ?_, ?_⟩, left, right, T.equations.iseqv.refl _, T.equations.iseqv.refl _, related⟩
  · rintro first second ⟨sourceFirst, sourceSecond, firstEquivalent, secondEquivalent, related⟩
      label' first' step
    obtain ⟨label, rfl⟩ := labelSurjective label'
    obtain ⟨first'', step', targetEquivalent⟩ :=
      N.act_resp_left (T.equations.iseqv.symm firstEquivalent) step
    obtain ⟨liftedFirst, liftedStep, liftedEquivalent⟩ := cover.liftAct step'
    obtain ⟨liftedSecond, secondStep, relatedTargets⟩ := forward related label liftedStep
    obtain ⟨second', secondStep', secondTargetEquivalent⟩ :=
      N.act_resp_left secondEquivalent (cover.mapAct secondStep)
    refine ⟨second', secondStep', liftedFirst, liftedSecond, ?_, secondTargetEquivalent, relatedTargets⟩
    exact T.equations.iseqv.trans liftedEquivalent (T.equations.iseqv.symm targetEquivalent)
  · rintro first second ⟨sourceFirst, sourceSecond, firstEquivalent, secondEquivalent, related⟩
      label' second' step
    obtain ⟨label, rfl⟩ := labelSurjective label'
    obtain ⟨second'', step', targetEquivalent⟩ :=
      N.act_resp_left (T.equations.iseqv.symm secondEquivalent) step
    obtain ⟨liftedSecond, liftedStep, liftedEquivalent⟩ := cover.liftAct step'
    obtain ⟨liftedFirst, firstStep, relatedTargets⟩ := backward related label liftedStep
    obtain ⟨first', firstStep', firstTargetEquivalent⟩ :=
      N.act_resp_left firstEquivalent (cover.mapAct firstStep)
    refine ⟨first', firstStep', liftedFirst, liftedSecond, firstTargetEquivalent, ?_, relatedTargets⟩
    exact T.equations.iseqv.trans liftedEquivalent (T.equations.iseqv.symm targetEquivalent)
  · rintro first second ⟨sourceFirst, sourceSecond, firstEquivalent, secondEquivalent, related⟩ atom'
    obtain ⟨atom, rfl⟩ := atomSurjective atom'
    rw [← N.observes_resp _ firstEquivalent, ← N.observes_resp _ secondEquivalent,
      ← cover.observes_iff, ← cover.observes_iff]
    exact atoms related atom

/-- With every atom and label reached, a cover is exact for bisimilarity. -/
theorem bisimilar_map_iff (atomSurjective : Function.Surjective cover.mapAtom)
    (labelSurjective : Function.Surjective cover.mapLabel) (left right : S.Term) :
    N.Bisimilar (cover.mapTerm left) (cover.mapTerm right) ↔ M.Bisimilar left right :=
  ⟨cover.bisimilar_of_map, cover.bisimilar_map atomSurjective labelSurjective⟩

end SystemCover

/-! ## Unlabeled covers from step covers -/

/-- A step cover between the plain step systems of two observed GSLTs, when
the observations are carried exactly, is a system cover. -/
def SystemCover.ofStepCover {mapTerm : S.Term → T.Term}
    (stepCover : Ultrainfinite.StepCover S T mapTerm)
    (mapEquiv : ∀ {left right : S.Term}, S.Equiv left right →
      T.Equiv (mapTerm left) (mapTerm right))
    (sourceObserved : ObservedGSLT.{uAtom} S) (targetObserved : ObservedGSLT.{uAtom'} T)
    (sourceResp : ∀ (atom : sourceObserved.Atom) {left right : S.Term}, S.Equiv left right →
      (sourceObserved.observes atom left ↔ sourceObserved.observes atom right))
    (targetResp : ∀ (atom : targetObserved.Atom) {left right : T.Term}, T.Equiv left right →
      (targetObserved.observes atom left ↔ targetObserved.observes atom right))
    (mapAtom : sourceObserved.Atom → targetObserved.Atom)
    (observes_iff : ∀ atom term, sourceObserved.observes atom term ↔
      targetObserved.observes (mapAtom atom) (mapTerm term)) :
    SystemCover (System.ofObserved sourceObserved sourceResp)
      (System.ofObserved targetObserved targetResp) where
  mapTerm := mapTerm
  mapAtom := mapAtom
  mapLabel := id
  mapEquiv := mapEquiv
  observes_iff := observes_iff
  mapAct := fun step => stepCover.mapStep step
  liftAct := by
    intro _ source target' step
    obtain ⟨target, step, equal⟩ := stepCover.liftStep step
    exact ⟨target, step, equal ▸ T.equations.iseqv.refl _⟩

#print axioms SystemCover.sat_map
#print axioms SystemCover.bisimilar_map_iff
#print axioms SystemTranslation.psat_map

end Mettapedia.GSLT.HennessyMilner
