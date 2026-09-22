import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Scoped closed positioned-rule data

The canonical LanguageDef already carries signature declarations, equations,
and conditional rewrite rules. This scoped record is a separate unconditional
construction, with selected positions attached to its rules and closed root
instances. It does not replace the canonical language definition. Deriving the
scoped conditional rule algebra from that definition remains open; selected
positions must not become mandatory core rule fields through this adapter.

Here the reduction relation is the union of the existing positioned-rule
relations. Their common equations support the equational quotient unchanged.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

/-- A **presentation**: the signature's metavariable declarations, the equations
over them, and the positioned rewrite rules. -/
structure Presentation (S : Signature) where
  /-- What the rules and equations may be parametric in. -/
  metas : List (MetaArity S)
  /-- The second component. -/
  eqs : List (EqAxiom S metas)
  /-- The third component: as many rules as the author writes. -/
  rules : List (PositionedRewrite (withMetas S metas))

namespace Presentation

variable (Pr : Presentation S)

/-- The step relation a presentation denotes: some rule fires. -/
def Step {s : S.Srt} (t u : Term S [] s) : Prop :=
  ∃ i : Fin Pr.rules.length, Mettapedia.OSLF.Binding.Step (Pr.rules.get i) t u

/-- The step relation modulo the presentation's own equations. -/
def StepModE {s : S.Srt} (t u : Term S [] s) : Prop :=
  ∃ i : Fin Pr.rules.length,
    Mettapedia.OSLF.Binding.StepModE Pr.eqs (Pr.rules.get i) t u

variable {Pr}

/-- A step of any rule is a step of the presentation. -/
theorem step_of_rule {s : S.Srt} (i : Fin Pr.rules.length) {t u : Term S [] s}
    (h : Mettapedia.OSLF.Binding.Step (Pr.rules.get i) t u) : Pr.Step t u :=
  ⟨i, h⟩

theorem stepModE_of_rule {s : S.Srt} (i : Fin Pr.rules.length) {t u : Term S [] s}
    (h : Mettapedia.OSLF.Binding.StepModE Pr.eqs (Pr.rules.get i) t u) :
    Pr.StepModE t u :=
  ⟨i, h⟩

/-- **The presentation's step relation is a step relation modulo its equations**:
it respects them on the left. -/
theorem stepModE_resp_left {s : S.Srt} {t t' u : Term S [] s}
    (he : EqClosure Pr.eqs t t') (h : Pr.StepModE t' u) : Pr.StepModE t u := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, Mettapedia.OSLF.Binding.stepModE_resp_left he hi⟩

/-- And on the right. -/
theorem stepModE_resp_right {s : S.Srt} {t u u' : Term S [] s}
    (h : Pr.StepModE t u) (he : EqClosure Pr.eqs u u') : Pr.StepModE t u' := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, Mettapedia.OSLF.Binding.stepModE_resp_right hi he⟩

/-- **A presentation with no rules steps nowhere**, so the union is not
vacuously everything. -/
theorem step_empty {s : S.Srt} (Pr : Presentation S) (hr : Pr.rules.length = 0)
    (t u : Term S [] s) : ¬ Pr.Step t u := by
  rintro ⟨i, -⟩
  exact absurd i.isLt (by omega)

/-- With no rules there is no step modulo the equations either, so the
equational closure of an empty relation is still empty. -/
theorem stepModE_empty {s : S.Srt} (Pr : Presentation S) (hr : Pr.rules.length = 0)
    (t u : Term S [] s) : ¬ Pr.StepModE t u := by
  rintro ⟨i, -⟩
  exact absurd i.isLt (by omega)

/-- **Adding a rule can only add steps.** -/
theorem step_mono {s : S.Srt} {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    {rs rs' : List (PositionedRewrite (withMetas S M))}
    (hsub : ∀ i : Fin rs.length, ∃ j : Fin rs'.length, rs'.get j = rs.get i)
    {t u : Term S [] s} (h : (⟨M, E, rs⟩ : Presentation S).Step t u) :
    (⟨M, E, rs'⟩ : Presentation S).Step t u := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨j, hj⟩ := hsub i
  exact ⟨j, by rw [hj]; exact hi⟩

end Presentation

end Mettapedia.OSLF.Binding
