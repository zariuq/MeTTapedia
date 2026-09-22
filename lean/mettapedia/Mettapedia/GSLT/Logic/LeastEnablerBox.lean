import Mettapedia.GSLT.Logic.AdmissibleContextCongruence

/-!
# Box through least enablers

The backward modality cannot be read off raw predecessors for every theory: a
presentation can have infinitely many equation-inequivalent predecessors of one
term, and rho does.  What the least-enabler discipline supplies is a backward
system whose labels are contexts rather than terms — a step into a term is a
least enabling context together with the source it enabled — and image
finiteness is then a statement about *labelled* predecessors modulo the
equations, which is a different and weaker demand.

This module builds that system, shows it is a lawful `System` (so every
Hennessy–Milner result already proved applies to it), and records the box
modality and its adequacy as instances of the forward development rather than
as a second theory.  What must be supplied per theory is
`BackwardImageFiniteModulo`; nothing here assumes it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LeastEnablerBox

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

universe uContext uRule uAtom

variable {S : GSLT} {rules : ContextualRules.{uContext, uRule} S}

/-- The backward least-enabler relation: `backwardAct C t s` when the source
`s`, placed in the least enabling context `C`, steps to `t`. -/
def backwardAct (rules : ContextualRules.{uContext, uRule} S)
    (context : rules.Context) (target source : S.Term) : Prop :=
  rules.Act context source target

/-- The backward system.  Its labels are the same least enabling contexts as
the forward system's; only the direction of the step is reversed. -/
def backwardSystem (rules : ContextualRules.{uContext, uRule} S)
    (observations : ContextualRules.Observations.{uAtom} S) :
    System.{uAtom, uContext} S where
  Atom := observations.Atom
  observes := observations.observes
  observes_resp := observations.observes_resp
  Label := rules.Context
  act := backwardAct rules
  act_resp_left := by
    intro label left right target equivalent act
    exact ⟨target, rules.act_resp_right act equivalent, S.equations.iseqv.refl _⟩
  act_resp_right := by
    intro label source target target' act equivalent
    obtain ⟨target'', act', equivalent'⟩ := rules.act_resp_left equivalent act
    exact rules.act_resp_right act' (S.equations.iseqv.symm equivalent')

/-- The two systems share their labels, observations and underlying theory;
they differ only in the direction of the step. -/
theorem backwardSystem_act (rules : ContextualRules.{uContext, uRule} S)
    (observations : ContextualRules.Observations.{uAtom} S)
    (context : rules.Context) (target source : S.Term) :
    (backwardSystem rules observations).act context target source ↔
      (rules.hmlSystem observations).act context source target :=
  Iff.rfl

/-! ## The box modality

Box and diamond here range over *labelled* predecessors: the label is the least
enabling context, and the observation set plays no part in either, so neither
takes one. -/

/-- `box C φ` holds at a term when every source that reaches it by a step
labelled `C` satisfies `φ`.  This is the backward diamond's dual, taken over
labelled predecessors rather than raw ones. -/
def box (rules : ContextualRules.{uContext, uRule} S)
    (context : rules.Context) (φ : S.Term → Prop) (target : S.Term) : Prop :=
  ∀ source : S.Term, rules.Act context source target → φ source

/-- `dia C φ` holds at a term when some source reaches it by a step labelled
`C` and satisfies `φ`. -/
def dia (rules : ContextualRules.{uContext, uRule} S)
    (context : rules.Context) (φ : S.Term → Prop) (target : S.Term) : Prop :=
  ∃ source : S.Term, rules.Act context source target ∧ φ source

/-- Box and diamond are de Morgan duals over labelled predecessors. -/
theorem box_eq_not_dia_not (rules : ContextualRules.{uContext, uRule} S)
    (context : rules.Context) (φ : S.Term → Prop) (target : S.Term) :
    box rules context φ target ↔
      ¬ dia rules context (fun source => ¬ φ source) target := by
  constructor
  · rintro hbox ⟨source, act, hnot⟩
    exact hnot (hbox source act)
  · intro hnot source act
    by_contra hφ
    exact hnot ⟨source, act, hφ⟩

/-- Box transfers along the equations on the term it is evaluated at.  The
predicate needs no invariance of its own, because it is applied to the
predecessor rather than to that term. -/
theorem box_resp (rules : ContextualRules.{uContext, uRule} S)
    (context : rules.Context) {φ : S.Term → Prop}
    {left right : S.Term} (equivalent : S.Equiv left right) :
    box rules context φ left → box rules context φ right := by
  intro hbox source act
  exact hbox source
    (rules.act_resp_right act (S.equations.iseqv.symm equivalent))

/-! ## Image finiteness backwards -/

/-- Image finiteness for the backward system: every term has finitely many
equation-classes of labelled predecessors under each label.  This is what a
particular theory must supply for backward adequacy; it is strictly weaker
than finiteness of raw predecessors, which fails for reflective calculi. -/
def BackwardImageFiniteModulo
    (rules : ContextualRules.{uContext, uRule} S)
    (observations : ContextualRules.Observations.{uAtom} S) : Prop :=
  (backwardSystem rules observations).ImageFiniteModulo

/-- Backward adequacy is the forward theorem applied to the backward system:
logical equivalence in the backward labelled logic coincides with backward
bisimilarity, whenever labelled predecessors are finite modulo the equations.
No separate development is needed, and no adequacy is claimed without that
hypothesis. -/
theorem backward_logicallyEquivalent_iff_bisimilar
    (rules : ContextualRules.{uContext, uRule} S)
    (observations : ContextualRules.Observations.{uAtom} S)
    (finite : BackwardImageFiniteModulo rules observations)
    (left right : S.Term) :
    (backwardSystem rules observations).LogicallyEquivalent left right ↔
      (backwardSystem rules observations).Bisimilar left right :=
  (backwardSystem rules observations).logicallyEquivalent_iff_bisimilar finite left right

end Mettapedia.GSLT.LeastEnablerBox
