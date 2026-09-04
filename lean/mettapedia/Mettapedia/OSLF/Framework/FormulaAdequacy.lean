import Mettapedia.OSLF.Framework.ConcreteHennessyMilnerBridge
import Mettapedia.GSLT.Logic.HennessyMilnerDirections

/-!
# Adequacy of the OSLF formula language

The concrete bridge reads the public OSLF formula syntax over a concrete
system: string-valued observations and one transition family, with the
step-past `box` as the predecessor-universal adjoint.  This module completes
that bridge in three ways.

* Over the equation-saturated step of a GSLT with an equation-invariant atom
  family, the reading on a language definition is the public one.
* The whole language, `box` included, is the labeled Hennessy–Milner language
  over the two directions of the step: every OSLF formula translates to a
  directional formula with the same satisfaction, and every directional
  formula is expressible in the OSLF language.  Consequently OSLF-logical
  equivalence is two-directional bisimilarity under image-finiteness modulo
  the equations in both directions.
* The box-free syntactic fragment is complete for the forward Hennessy–Milner
  language, so equivalence on that fragment (not merely on the translated
  image of forward formulas) is ordinary bisimilarity under forward
  image-finiteness alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Formula.Adequacy

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConcreteHennessyMilnerBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula

/-! ## The OSLF language over any GSLT -/

variable {S : GSLT}

/-- The concrete system of an equation-invariant atom family over the
equation-saturated step. -/
def concreteSystem (S : GSLT) (I : String → EquationPredicate S) : ConcreteSystem S where
  observes := fun atom => (I atom).1
  observes_resp := fun atom _ _ equivalent => (I atom).2 equivalent
  act := S.Step
  act_resp_left := fun equivalent step => S.rewrites_resp_left equivalent step
  act_resp_right := fun step equivalent => S.rewrites_resp_right step equivalent

/-- On a language definition the generic reading is the public one. -/
theorem satisfies_langGSLTUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (I : EquationAtomSemUsing relEnv lang) :
    ∀ (formula : OSLFFormula) (term : Pattern),
      satisfies (concreteSystem (langGSLTUsing relEnv lang) I) formula term ↔
        sem (langSemanticReducesUsing relEnv lang) (fun atom => (I atom).1) formula term
  | .top, _ => Iff.rfl
  | .bot, _ => Iff.rfl
  | .atom _, _ => Iff.rfl
  | .and left right, term =>
      and_congr (satisfies_langGSLTUsing relEnv lang I left term)
        (satisfies_langGSLTUsing relEnv lang I right term)
  | .or left right, term =>
      or_congr (satisfies_langGSLTUsing relEnv lang I left term)
        (satisfies_langGSLTUsing relEnv lang I right term)
  | .imp left right, term =>
      imp_congr (satisfies_langGSLTUsing relEnv lang I left term)
        (satisfies_langGSLTUsing relEnv lang I right term)
  | .dia inner, term =>
      exists_congr fun target =>
        and_congr Iff.rfl (satisfies_langGSLTUsing relEnv lang I inner target)
  | .box inner, term =>
      forall_congr' fun source =>
        imp_congr Iff.rfl (satisfies_langGSLTUsing relEnv lang I inner source)

/-- OSLF-logical equivalence: the same formulas hold. -/
def OSLFEquivalent (S : GSLT) (I : String → EquationPredicate S) (left right : S.Term) : Prop :=
  ∀ formula : OSLFFormula,
    satisfies (concreteSystem S I) formula left ↔ satisfies (concreteSystem S I) formula right

/-! ## The directional system of the atom family -/

/-- The observation set given by an equation-invariant atom family. -/
def atomObservations (S : GSLT) (I : String → EquationPredicate S) : ObservedGSLT.{0} S :=
  ⟨String, fun atom => (I atom).1⟩

theorem atomObservations_resp (S : GSLT) (I : String → EquationPredicate S)
    (atom : String) {left right : S.Term} (equivalent : S.Equiv left right) :
    (atomObservations S I).observes atom left ↔ (atomObservations S I).observes atom right :=
  (I atom).2 equivalent

/-- The two-direction labeled system of the atom family. -/
def directionalSystem (S : GSLT) (I : String → EquationPredicate S) : System.{0, 0} S :=
  directional (atomObservations S I) (atomObservations_resp S I)

/-- The forward, single-label system of the atom family: the concrete
bridge's Hennessy–Milner system. -/
abbrev forwardSystem (S : GSLT) (I : String → EquationPredicate S) : System.{0, 0} S :=
  (concreteSystem S I).toHMLSystem

/-! ## Translation into the directional language -/

/-- OSLF formulas as directional Hennessy–Milner formulas. -/
def toDirectional : OSLFFormula → Formula String Direction
  | .top => .top
  | .bot => .neg .top
  | .atom atom => .atom atom
  | .and left right => .conj (toDirectional left) (toDirectional right)
  | .or left right => .neg (.conj (.neg (toDirectional left)) (.neg (toDirectional right)))
  | .imp left right => .neg (.conj (toDirectional left) (.neg (toDirectional right)))
  | .dia inner => .dia .forward (toDirectional inner)
  | .box inner => .neg (.dia .backward (.neg (toDirectional inner)))

theorem sat_toDirectional (S : GSLT) (I : String → EquationPredicate S) :
    ∀ (formula : OSLFFormula) (term : S.Term),
      (directionalSystem S I).sat (toDirectional formula) term ↔
        satisfies (concreteSystem S I) formula term
  | .top, _ => Iff.rfl
  | .bot, _ => by simp [toDirectional, System.sat, satisfies]
  | .atom _, _ => Iff.rfl
  | .and left right, term =>
      and_congr (sat_toDirectional S I left term) (sat_toDirectional S I right term)
  | .or left right, term => by
      have leftIH := sat_toDirectional S I left term
      have rightIH := sat_toDirectional S I right term
      simp only [toDirectional, System.sat, satisfies]
      rw [leftIH, rightIH]
      tauto
  | .imp left right, term => by
      have leftIH := sat_toDirectional S I left term
      have rightIH := sat_toDirectional S I right term
      simp only [toDirectional, System.sat, satisfies]
      rw [leftIH, rightIH]
      tauto
  | .dia inner, term =>
      exists_congr fun target => and_congr Iff.rfl (sat_toDirectional S I inner target)
  | .box inner, term => by
      simp only [toDirectional, System.sat, satisfies]
      constructor
      · intro none source step
        by_contra fails
        exact none ⟨source, step, fun sat => fails ((sat_toDirectional S I inner source).mp sat)⟩
      · rintro holds ⟨source, step, fails⟩
        exact fails ((sat_toDirectional S I inner source).mpr (holds source step))

/-- Directional Hennessy–Milner formulas as OSLF formulas. -/
def ofDirectional : Formula String Direction → OSLFFormula
  | .top => .top
  | .atom atom => .atom atom
  | .conj left right => .and (ofDirectional left) (ofDirectional right)
  | .neg inner => .imp (ofDirectional inner) .bot
  | .dia .forward inner => .dia (ofDirectional inner)
  | .dia .backward inner => .imp (.box (.imp (ofDirectional inner) .bot)) .bot

theorem satisfies_ofDirectional (S : GSLT) (I : String → EquationPredicate S) :
    ∀ (formula : Formula String Direction) (term : S.Term),
      satisfies (concreteSystem S I) (ofDirectional formula) term ↔
        (directionalSystem S I).sat formula term
  | .top, _ => Iff.rfl
  | .atom _, _ => Iff.rfl
  | .conj left right, term =>
      and_congr (satisfies_ofDirectional S I left term) (satisfies_ofDirectional S I right term)
  | .neg inner, term => by
      simp only [ofDirectional, satisfies, System.sat]
      rw [satisfies_ofDirectional S I inner term]
  | .dia .forward inner, term =>
      exists_congr fun target => and_congr Iff.rfl (satisfies_ofDirectional S I inner target)
  | .dia .backward inner, term => by
      simp only [ofDirectional, satisfies, System.sat]
      constructor
      · intro holds
        by_contra none
        apply holds
        intro source step innerHolds
        exact none ⟨source, step, (satisfies_ofDirectional S I inner source).mp innerHolds⟩
      · rintro ⟨source, step, innerHolds⟩ holds
        exact holds source step ((satisfies_ofDirectional S I inner source).mpr innerHolds)

/-- OSLF-logical equivalence is logical equivalence of the directional system. -/
theorem oslfEquivalent_iff_logicallyEquivalent (S : GSLT) (I : String → EquationPredicate S)
    (left right : S.Term) :
    OSLFEquivalent S I left right ↔ (directionalSystem S I).LogicallyEquivalent left right := by
  constructor
  · intro equivalent formula
    rw [← satisfies_ofDirectional S I formula left, ← satisfies_ofDirectional S I formula right]
    exact equivalent _
  · intro equivalent formula
    rw [← sat_toDirectional S I formula left, ← sat_toDirectional S I formula right]
    exact equivalent _

/-! ## Adequacy of the OSLF language -/

/-- Two-directional bisimilarity (successors and predecessors) with the atoms
observed. -/
def Bidirectional (S : GSLT) (I : String → EquationPredicate S) (left right : S.Term) : Prop :=
  (directionalSystem S I).Bisimilar left right

/-- Bidirectionally bisimilar terms satisfy the same OSLF formulas. -/
theorem oslfEquivalent_of_bidirectional (S : GSLT) (I : String → EquationPredicate S)
    {left right : S.Term} (bisimilar : Bidirectional S I left right) :
    OSLFEquivalent S I left right :=
  (oslfEquivalent_iff_logicallyEquivalent S I left right).mpr
    (System.logicallyEquivalent_of_bisimilar _ bisimilar)

/-- Under image-finiteness modulo the equations in both directions, OSLF
equivalence is bidirectional bisimilarity. -/
theorem oslfEquivalent_iff_bidirectional (S : GSLT) (I : String → EquationPredicate S)
    (finite : (directionalSystem S I).ImageFiniteModulo) (left right : S.Term) :
    OSLFEquivalent S I left right ↔ Bidirectional S I left right :=
  (oslfEquivalent_iff_logicallyEquivalent S I left right).trans
    (System.logicallyEquivalent_iff_bisimilar _ finite left right)

/-! ## The box-free fragment -/

/-- OSLF formulas without the step-past box. -/
inductive Forward : OSLFFormula → Prop
  | top : Forward .top
  | bot : Forward .bot
  | atom (atom : String) : Forward (.atom atom)
  | and {left right : OSLFFormula} : Forward left → Forward right → Forward (.and left right)
  | or {left right : OSLFFormula} : Forward left → Forward right → Forward (.or left right)
  | imp {left right : OSLFFormula} : Forward left → Forward right → Forward (.imp left right)
  | dia {inner : OSLFFormula} : Forward inner → Forward (.dia inner)

/-- Box-free OSLF formulas as single-label Hennessy–Milner formulas. -/
def toForward : OSLFFormula → Formula String Unit
  | .top => .top
  | .bot => .neg .top
  | .atom atom => .atom atom
  | .and left right => .conj (toForward left) (toForward right)
  | .or left right => .neg (.conj (.neg (toForward left)) (.neg (toForward right)))
  | .imp left right => .neg (.conj (toForward left) (.neg (toForward right)))
  | .dia inner => .dia () (toForward inner)
  | .box _ => .top

theorem sat_toForward (S : GSLT) (I : String → EquationPredicate S) {formula : OSLFFormula}
    (forward : Forward formula) (term : S.Term) :
    (forwardSystem S I).sat (toForward formula) term ↔
      satisfies (concreteSystem S I) formula term := by
  induction forward generalizing term with
  | top => exact Iff.rfl
  | bot => simp [toForward, System.sat, satisfies]
  | atom _ => exact Iff.rfl
  | and _ _ leftIH rightIH => exact and_congr (leftIH term) (rightIH term)
  | or _ _ leftIH rightIH =>
      simp only [toForward, System.sat, satisfies]
      rw [leftIH term, rightIH term]
      tauto
  | imp _ _ leftIH rightIH =>
      simp only [toForward, System.sat, satisfies]
      rw [leftIH term, rightIH term]
      tauto
  | dia _ innerIH =>
      exact exists_congr fun target => and_congr Iff.rfl (innerIH target)

/-- The concrete bridge's embedding of forward formulas lands in the box-free
fragment. -/
theorem forward_fromHML : ∀ formula : Formula String Unit, Forward (fromHML formula)
  | .top => .top
  | .atom atom => .atom atom
  | .conj left right => .and (forward_fromHML left) (forward_fromHML right)
  | .neg inner => .imp (forward_fromHML inner) .bot
  | .dia _ inner => .dia (forward_fromHML inner)

/-- Equivalence on the box-free fragment. -/
def ForwardEquivalent (S : GSLT) (I : String → EquationPredicate S) (left right : S.Term) : Prop :=
  ∀ formula : OSLFFormula, Forward formula →
    (satisfies (concreteSystem S I) formula left ↔ satisfies (concreteSystem S I) formula right)

theorem forwardEquivalent_iff_logicallyEquivalent (S : GSLT) (I : String → EquationPredicate S)
    (left right : S.Term) :
    ForwardEquivalent S I left right ↔ (forwardSystem S I).LogicallyEquivalent left right := by
  constructor
  · intro equivalent formula
    exact ((satisfies_fromHML_iff (concreteSystem S I) formula left).symm.trans
      (equivalent _ (forward_fromHML formula))).trans
      (satisfies_fromHML_iff (concreteSystem S I) formula right)
  · intro equivalent formula forward
    exact ((sat_toForward S I forward left).symm.trans (equivalent _)).trans
      (sat_toForward S I forward right)

/-- Box-free OSLF equivalence is bisimilarity of the forward system, under
forward image-finiteness modulo the equations. -/
theorem forwardEquivalent_iff_bisimilar (S : GSLT) (I : String → EquationPredicate S)
    (finite : (forwardSystem S I).ImageFiniteModulo) (left right : S.Term) :
    ForwardEquivalent S I left right ↔ (forwardSystem S I).Bisimilar left right :=
  (forwardEquivalent_iff_logicallyEquivalent S I left right).trans
    (System.logicallyEquivalent_iff_bisimilar _ finite left right)

/-- Forward bisimilarity, with the atoms observed, is the observed
bisimilarity of the GSLT. -/
theorem forwardSystem_bisimilar_iff (S : GSLT) (I : String → EquationPredicate S)
    (left right : S.Term) :
    (forwardSystem S I).Bisimilar left right ↔ (atomObservations S I).Bisimilar left right :=
  System.ofObserved_bisimilar_iff (atomObservations S I) (atomObservations_resp S I) left right

end Mettapedia.OSLF.Formula.Adequacy
