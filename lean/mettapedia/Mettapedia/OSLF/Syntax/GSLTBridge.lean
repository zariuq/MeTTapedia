import Mettapedia.OSLF.Syntax.Presentation
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# Scoped closed rules induce a rule-labeled transition system

The existing scoped unconditional rule record induces terms, an equation
equivalence, and a reduction respecting that equivalence. This adapter makes
the abstract GSLT results applicable to those closed scoped terms. It is not an
identification with the canonical LanguageDef: conditional-premise integration
and its context-indexed assignments remain open.

Each label records which enumerated rule fired. The unlabelled relation is
proved to be the union of that labelled family. These rule-index labels are not
the source's least-enabling context labels or its higher-order payload
comparison; those require their own constructions and adequacy results.

The observations are an explicit equation-invariant policy, independent of the
rule labels.  Coarser observations can identify distinct equational classes.
The class-separating policy is one instance: it observes membership in every
equational class and therefore makes logical equivalence and observed
bisimilarity coincide with equational equality.  That instance is not a
behavioral minimization theorem; its observations already separate the classes.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.GSLT

set_option autoImplicit false

universe uAtom

variable {S : Signature}

namespace Presentation

/-- **A presentation at a chosen sort is a GSLT.**  Terms are the closed terms
of that sort, the equivalence is the equational theory, and the reduction is the
union over the rules, taken modulo the equations. -/
def toGSLT (Pr : Presentation S) (s : S.Srt) : GSLT where
  Term := Term S [] s
  equations := eqSetoid Pr.eqs [] s
  rewrites := Pr.StepModE
  rewrites_resp_left := by
    intro _ _ _ he h
    exact ⟨_, Pr.stepModE_resp_left (EqClosure.symm he) h, EqClosure.refl _⟩
  rewrites_resp_right := by
    intro _ _ _ h he
    exact Pr.stepModE_resp_right h he

@[simp] theorem toGSLT_Term (Pr : Presentation S) (s : S.Srt) :
    (Pr.toGSLT s).Term = Term S [] s := rfl

@[simp] theorem toGSLT_step (Pr : Presentation S) {s : S.Srt} (t u : Term S [] s) :
    (Pr.toGSLT s).Step t u ↔ Pr.StepModE t u := Iff.rfl

@[simp] theorem toGSLT_equiv (Pr : Presentation S) {s : S.Srt} (t u : Term S [] s) :
    (Pr.toGSLT s).Equiv t u ↔ EqClosure Pr.eqs t u := Iff.rfl

/-! ## The labelled system

A step of the scoped record is a step of some rule, and its index is a label.
This rule-indexed family does not construct least-enabling context labels. -/

/-- The step relation of a single rule, modulo the equations: the labelled
transition at label `i`. -/
def actOf (Pr : Presentation S) (s : S.Srt) (i : Fin Pr.rules.length)
    (t u : Term S [] s) : Prop :=
  Mettapedia.OSLF.Binding.StepModE Pr.eqs (Pr.rules.get i) t u

/-- Rule-labeled Hennessy-Milner semantics with an explicit invariant
observation policy.  The policy does not change the transition relation. -/
def toHMSystem (Pr : Presentation S) (s : S.Srt) (Atom : Type uAtom)
    (observes : Atom → Term S [] s → Prop)
    (observes_resp : ∀ a {t u}, EqClosure Pr.eqs t u → (observes a t ↔ observes a u)) :
    HennessyMilner.System (Pr.toGSLT s) where
  Atom := Atom
  observes := observes
  observes_resp := observes_resp
  Label := Fin Pr.rules.length
  act := Pr.actOf s
  act_resp_left := by
    intro _ _ _ _ he h
    exact ⟨_, Mettapedia.OSLF.Binding.stepModE_resp_left (EqClosure.symm he) h,
      EqClosure.refl _⟩
  act_resp_right := by
    intro _ _ _ _ h he
    exact Mettapedia.OSLF.Binding.stepModE_resp_right h he

/-- The explicitly class-separating policy.  Observed bisimilarity for this
instance cannot merge inequivalent equation classes, even if their behavior is
otherwise identical. -/
def classSeparatingHMSystem (Pr : Presentation S) (s : S.Srt) :
    HennessyMilner.System (Pr.toGSLT s) :=
  Pr.toHMSystem s (Term S [] s) (fun a t => EqClosure Pr.eqs t a)
    (fun _ _ _ he => ⟨fun h => EqClosure.trans (EqClosure.symm he) h,
      fun h => EqClosure.trans he h⟩)

/-- **The GSLT's reduction is the union of the labelled family.**  So the
labelling is faithful: it refines the relation without changing it. -/
theorem step_iff_exists_label (Pr : Presentation S) {s : S.Srt}
    (t u : Term S [] s) :
    (Pr.toGSLT s).Step t u ↔ ∃ i : Fin Pr.rules.length, Pr.actOf s i t u :=
  Iff.rfl

/-- Each label refines the relation. -/
theorem step_of_act (Pr : Presentation S) {s : S.Srt} {t u : Term S [] s}
    {i : Fin Pr.rules.length} (h : Pr.actOf s i t u) :
    (Pr.toGSLT s).Step t u :=
  ⟨i, h⟩

/-! ## The atoms are exactly the classes

Two controls, in opposite directions, showing that the observation set is
neither too coarse nor too fine. -/

/-- Equated terms satisfy the same atoms -- the observations cannot see inside a
class for the class-separating policy. -/
theorem observes_of_equiv (Pr : Presentation S) {s : S.Srt}
    {t u : Term S [] s} (he : EqClosure Pr.eqs t u) (a : Term S [] s) :
    (Pr.classSeparatingHMSystem s).observes a t ↔ (Pr.classSeparatingHMSystem s).observes a u :=
  (Pr.classSeparatingHMSystem s).observes_resp a he

/-- **And the observations see every class.**  Logically equivalent terms are
equationally equal for this policy, because its atoms already distinguish every
equation class.  This conclusion is not asserted for coarser observations. -/
theorem equiv_of_logicallyEquivalent (Pr : Presentation S) {s : S.Srt}
    {t u : Term S [] s}
    (h : (Pr.classSeparatingHMSystem s).LogicallyEquivalent t u) : EqClosure Pr.eqs t u := by
  have hsat : (Pr.classSeparatingHMSystem s).sat (HennessyMilner.Formula.atom t) t :=
    EqClosure.refl t
  exact EqClosure.symm ((h (HennessyMilner.Formula.atom t)).mp hsat)

/-- Bisimilar terms are therefore equationally equal as well, since bisimilarity
implies logical equivalence in the full fragment. -/
theorem equiv_of_bisimilar (Pr : Presentation S) {s : S.Srt}
    {t u : Term S [] s}
    (h : (Pr.classSeparatingHMSystem s).Bisimilar t u) : EqClosure Pr.eqs t u :=
  Pr.equiv_of_logicallyEquivalent
    ((Pr.classSeparatingHMSystem s).logicallyEquivalent_of_bisimilar h)

/-! ## Negative controls -/

/-- With no rules the generated GSLT does not step, so the labelled system is
not vacuously total. -/
theorem toGSLT_no_step (Pr : Presentation S) (hr : Pr.rules.length = 0)
    {s : S.Srt} (t u : Term S [] s) : ¬ (Pr.toGSLT s).Step t u :=
  Pr.stepModE_empty hr t u

/-- And then every term is a normal form, so the reduction is genuinely read off
the rules rather than supplied by the construction. -/
theorem toGSLT_all_normal (Pr : Presentation S) (hr : Pr.rules.length = 0)
    {s : S.Srt} (t : Term S [] s) : (Pr.toGSLT s).IsNormalForm t := by
  rintro ⟨u, hu⟩
  exact Pr.toGSLT_no_step hr t u hu

end Presentation

end Mettapedia.OSLF.Binding
