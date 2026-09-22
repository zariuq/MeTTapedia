import Mettapedia.OSLF.Syntax.ContextualSplitting
import Mettapedia.OSLF.Syntax.LinearContexts
import Mettapedia.OSLF.Syntax.ModalityAndObservation

/-!
# Every transition is a located event, and every located event is a modality

The three layers built so far describe the same thing from three sides.  The
labelled transition system says a state can move.  The splitting of a term into
a shape and a subterm says *where* a move would happen.  The generated modality
says *which rule* moves and *what it needs at the chosen position*.  Until these
are related, each is a separate development that happens to share a signature.

This module relates them in the one direction that was missing.  The generated
modality was already shown to refine the diamond; here the refinement is closed
into a characterization, and the thing that closes it is the splitting.  A step
of the generated relation is exactly a cut at which the rule fires, so the
relation *is* the bundle of available events projected to its endpoints; and the
root step inside such an event carries an instance, so it hands back a generated
modality at the chosen position.

That makes the splitting load-bearing rather than decorative: it is the datum
that carries a transition back to a located modality, and nothing else in the
development does that.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.GSLT

set_option autoImplicit false

variable {S : Signature}

/-! ## A step is a cut at which the rule fires -/

/-- Any root step at a linear cut is an available event at that cut. -/
theorem fire_of_rootStep {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt}
    (K : Term S [P.sort] s) {a b : Term S [] P.sort} (h : RootStep P a b) :
    Fire P (⟨P.sort, K, a⟩ : Splitting S [] s) :=
  ⟨rfl, b, h⟩

/-- **Every step is located.**  Read left to right this is the converse of
`fire_gives_a_step`: a step of the generated relation is not merely accompanied
by a cut, it *is* a cut at which the rule fires, together with the reduct that
firing produces. -/
theorem step_iff_cut {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} (t u : Term S [] s) :
    Step P t u ↔
      ∃ (K : Term S [P.sort] s) (a b : Term S [] P.sort),
        holeCount K = 1 ∧ RootStep P a b ∧
        plug (⟨P.sort, K, a⟩ : Splitting S [] s) = t ∧ residual K b = u := by
  constructor
  · rintro ⟨K, a, b, hlin, hroot, ht, hu⟩
    exact ⟨K, a, b, hlin, hroot, ht, hu⟩
  · rintro ⟨K, a, b, hlin, hroot, ht, hu⟩
    exact ⟨K, a, b, hlin, hroot, ht, hu⟩

/-- **The relation is the bundle of available events, projected.**  Every state
that can move does so at a splitting which is an available event of the rule, and
the state it moves from is the one that splitting reconstructs. -/
theorem exists_fire_of_step {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} {t u : Term S [] s}
    (h : Step P t u) :
    ∃ Sp : Splitting S [] s, Fire P Sp ∧ plug Sp = t := by
  obtain ⟨K, a, b, -, hroot, ht, -⟩ := h
  exact ⟨⟨P.sort, K, a⟩, fire_of_rootStep K hroot, ht⟩

/-! ## A located event is a generated modality -/

/-- **A root step hands back the modality at the chosen position.**  The
instance it carries names a redex at the position's carrier, and the modality
there is inhabited with the root step's own reduct as its target. -/
theorem exists_stepsFromPosition_of_rootStep {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {a b : Term S [] P.sort}
    (h : RootStep P a b) :
    ∃ r : Term S [] P.position.carrier,
      StepsFromPosition P (fun v => v = b) r := by
  obtain ⟨I, -, hr⟩ := h
  exact ⟨_, stepsFromPosition_intro I hr⟩

/-- The same, from an available event: the cut's subterm side exposes the redex,
and the modality sits at the position inside it. -/
theorem exists_stepsFromPosition_of_fire {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} {Sp : Splitting S [] s}
    (h : Fire P Sp) :
    ∃ (b : Term S [] P.sort) (r : Term S [] P.position.carrier),
      StepsFromPosition P (fun v => v = b) r := by
  obtain ⟨_hc, b, hroot⟩ := h
  obtain ⟨r, hr⟩ := exists_stepsFromPosition_of_rootStep hroot
  exact ⟨b, r, hr⟩

/-! ## The chain, at the level of the transition system -/

namespace Presentation

/-- **A transition is a located generated modality, up to the equations.**  Given
a labelled transition, the splitting says where it happens, the root step says
what it produces, and the generated modality at the position says what the rule
needed there.  The equations appear only at the two ends, which is where the
transition system put them. -/
theorem act_is_a_located_modality (Pr : Presentation S)
    (i : Fin Pr.rules.length)
    {t u : Term S [] (Pr.rules.get i).sort}
    (h : (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).act i t u) :
    ∃ (K : Term S [(Pr.rules.get i).sort] (Pr.rules.get i).sort)
      (a b : Term S [] (Pr.rules.get i).sort)
      (r : Term S [] (Pr.rules.get i).position.carrier),
      holeCount K = 1
      ∧ RootStep (Pr.rules.get i) a b
      ∧ Fire (Pr.rules.get i)
          (⟨(Pr.rules.get i).sort, K, a⟩ : Splitting S [] (Pr.rules.get i).sort)
      ∧ StepsFromPosition (Pr.rules.get i) (fun v => v = b) r
      ∧ EqClosure Pr.eqs t (plug (⟨(Pr.rules.get i).sort, K, a⟩ :
          Splitting S [] (Pr.rules.get i).sort))
      ∧ EqClosure Pr.eqs (residual K b) u := by
  obtain ⟨t', u', hlt, hstep, hru⟩ := h
  obtain ⟨K, a, b, hlin, hroot, ht, hu⟩ := hstep
  obtain ⟨r, hr⟩ := exists_stepsFromPosition_of_rootStep hroot
  refine ⟨K, a, b, r, hlin, hroot, fire_of_rootStep K hroot, hr, ?_, ?_⟩
  · rw [show plug (⟨(Pr.rules.get i).sort, K, a⟩ :
      Splitting S [] (Pr.rules.get i).sort) = t' from ht]
    exact hlt
  · rw [show residual K b = u' from hu]
    exact hru

/-- And the converse at the same level: an available event at a linear cut is a
transition of the presentation at that rule's label. -/
theorem act_of_fire (Pr : Presentation S) (i : Fin Pr.rules.length)
    {K : Term S [(Pr.rules.get i).sort] (Pr.rules.get i).sort}
    {a b : Term S [] (Pr.rules.get i).sort}
    (hlin : holeCount K = 1) (hroot : RootStep (Pr.rules.get i) a b) :
    (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).act i
      (plug (⟨(Pr.rules.get i).sort, K, a⟩ :
        Splitting S [] (Pr.rules.get i).sort)) (residual K b) :=
  stepModE_of_step (fire_gives_a_step K a b hroot hlin)

end Presentation

/-! ## Events compose

An available event is a cut at which the rule fires.  Two cuts compose, so two
events should compose with them -- an event inside a context is an event of the
enclosing term.  That is congruence of the generated relation under contexts,
and it is the property that makes the relation an operational semantics rather
than a set of pairs.

Stating it needs the cut to be *structurally* linear.  In the variable
representation linearity is a side condition, and a composite of two linear
contexts is linear only by a theorem about how occurrence counts multiply
through a substitution; in the structural representation the composite is linear
because its type says so.  So the relation is presented once more, with its cut
structural, and congruence is then immediate. -/

/-- A step whose cut is structurally linear. -/
def StepAt {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    {s : S.Srt} (t u : Term S [] s) : Prop :=
  ∃ (Kc : LinCtx S P.sort [] s) (a b : Term S [] P.sort),
    RootStep P a b ∧ inst (LinCtx.toTerm Kc) a = t ∧ inst (LinCtx.toTerm Kc) b = u

/-- **A structural step is a step.**  The linearity side condition is discharged
by the type, not assumed. -/
theorem step_of_stepAt {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} {t u : Term S [] s}
    (h : StepAt P t u) : Step P t u := by
  obtain ⟨Kc, a, b, hroot, ht, hu⟩ := h
  exact ⟨LinCtx.toTerm Kc, a, b, LinCtx.holeCount_toTerm Kc, hroot, ht, hu⟩

/-- A root step is a structural step at the bare cut. -/
theorem stepAt_of_rootStep {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {a b : Term S [] P.sort}
    (h : RootStep P a b) : StepAt P a b :=
  ⟨LinCtx.hole, a, b, h, inst_hole a, inst_hole b⟩

/-- **The generated relation is closed under structurally linear contexts.**
An event inside a context is an event of the enclosing term, at the composite
cut -- which is linear with nothing to prove, because composition in the
structural representation preserves the type. -/
theorem stepAt_congr {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s s' : S.Srt}
    (L : LinCtx S s [] s') {t u : Term S [] s} (h : StepAt P t u) :
    StepAt P (inst (LinCtx.toTerm L) t) (inst (LinCtx.toTerm L) u) := by
  obtain ⟨Kc, a, b, hroot, ht, hu⟩ := h
  refine ⟨LinCtx.comp L Kc, a, b, hroot, ?_, ?_⟩
  · rw [LinCtx.toTerm_comp L Kc, ContextCat.inst_comp, ht]
  · rw [LinCtx.toTerm_comp L Kc, ContextCat.inst_comp, hu]

/-- **Events compose**: a firing inside a context is a step of the enclosing
term, so the bundle of available events is closed under enlarging the cut. -/
theorem stepAt_of_fire_in_context {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s s' : S.Srt}
    (Kc : LinCtx S P.sort [] s) (L : LinCtx S s [] s')
    {a b : Term S [] P.sort} (hroot : RootStep P a b) :
    StepAt P (inst (LinCtx.toTerm (LinCtx.comp L Kc)) a)
      (inst (LinCtx.toTerm (LinCtx.comp L Kc)) b) :=
  ⟨LinCtx.comp L Kc, a, b, hroot, rfl, rfl⟩

/-! ## The chain is inhabited

A control over the one-rule presentation: the contextual transition exhibited
earlier is recovered as a located event, and the modality it hands back is the
one at the rule's chosen position. -/

namespace ParallelFragment

/-- The contextual step really does yield a located event whose cut is the
context the step fired in. -/
theorem contextual_step_is_located (a b c : Term psig [] PSrt.proc) :
    ∃ Sp : Splitting psig [] PSrt.proc,
      Fire dropRight Sp ∧ plug Sp = parT (parT a b) c :=
  exists_fire_of_step (contextual_step a b c)

/-- ... and hands back the generated modality at the rule's position. -/
theorem contextual_step_gives_a_modality (a b : Term psig [] PSrt.proc) :
    ∃ r : Term psig [] dropRight.position.carrier,
      StepsFromPosition dropRight (fun v => v = a) r :=
  exists_stepsFromPosition_of_rootStep (dropRight_rootStep a b)

end ParallelFragment

end Mettapedia.OSLF.Binding
