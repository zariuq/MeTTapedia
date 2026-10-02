import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Scoped closed rewrite presentations

The canonical LanguageDef already carries signature declarations, equations,
and conditional rewrite rules. This scoped record is a separate unconditional
construction, with selected positions attached to its rules and closed root
instances. It does not replace the canonical language definition. Deriving the
scoped conditional rule algebra from that definition remains open; selected
positions must not become mandatory core rule fields through this adapter.

Here the reduction relation is the union of the existing positioned-rule
relations. Their common equations support the equational quotient unchanged.
The unpositioned unconditional presentation below exposes exactly the data
which the step relation uses; forgetting selected positions preserves steps.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

/-- Transport a single authored axiom along equality of declarations. -/
private theorem eqClosure_ax_of_index_eq {M : List (MetaArity S)}
    {F : List (EqAxiom S M)} (j : Fin F.length) (a : EqAxiom S M)
    (equalAxiom : F.get j = a) {Θ Γ : Ctx S}
    (body : ContextualAssignment S M Θ) (ambient : Sub S Θ Γ)
    (ordinary : Sub S a.ctx Γ) :
    EqClosure F (ContextualAssignment.instantiate body ambient ordinary a.lhs)
      (ContextualAssignment.instantiate body ambient ordinary a.rhs) := by
  subst a
  exact .ax j body ambient ordinary

mutual
/-- Enlarging an authored axiom list preserves every derivable equation,
including congruence below binding arguments. -/
theorem eqClosure_of_axiom_inclusion {M : List (MetaArity S)}
    {E F : List (EqAxiom S M)}
    (includeAxiom : ∀ i : Fin E.length,
      ∃ j : Fin F.length, F.get j = E.get i) :
    ∀ {Γ : Ctx S} {s : S.Srt} {t u : Term S Γ s},
      EqClosure E t u → EqClosure F t u
  | _, _, _, _, .ax i body ambient ordinary => by
      obtain ⟨j, equalAxiom⟩ := includeAxiom i
      exact eqClosure_ax_of_index_eq j (E.get i) equalAxiom body ambient ordinary
  | _, _, _, _, .refl t => .refl t
  | _, _, _, _, .symm h => .symm (eqClosure_of_axiom_inclusion includeAxiom h)
  | _, _, _, _, .trans h h' =>
      .trans (eqClosure_of_axiom_inclusion includeAxiom h)
        (eqClosure_of_axiom_inclusion includeAxiom h')
  | _, _, _, _, .cong o h =>
      .cong o (eqArgs_of_axiom_inclusion includeAxiom h)

theorem eqArgs_of_axiom_inclusion {M : List (MetaArity S)}
    {E F : List (EqAxiom S M)}
    (includeAxiom : ∀ i : Fin E.length,
      ∃ j : Fin F.length, F.get j = E.get i) :
    ∀ {ars : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {as bs : Args S ars Γ}, EqArgs E as bs → EqArgs F as bs
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail =>
      .cons (eqClosure_of_axiom_inclusion includeAxiom head)
        (eqArgs_of_axiom_inclusion includeAxiom tail)
end

/-- An unconditional rewrite schema before a redex position is selected. -/
structure UnpositionedRewrite (S : Signature) where
  ctx : Ctx S
  sort : S.Srt
  lhs : Term S ctx sort
  rhs : Term S ctx sort

namespace UnpositionedRewrite

/-- A closed root firing supplies both metavariable bodies and rule variables. -/
def RootStep {M : List (MetaArity S)}
    (rule : UnpositionedRewrite (withMetas S M))
    (source target : Term S [] rule.sort) : Prop :=
  ∃ (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (close : Sub S rule.ctx []),
    bind close (instantiate body rule.lhs) = source ∧
      bind close (instantiate body rule.rhs) = target

/-- Contextual closure uses a genuine one-hole context. -/
def Step {M : List (MetaArity S)}
    (rule : UnpositionedRewrite (withMetas S M)) {s : S.Srt}
    (source target : Term S [] s) : Prop :=
  ∃ (context : Term S [rule.sort] s)
    (redex reduct : Term S [] rule.sort),
    holeCount context = 1 ∧ rule.RootStep redex reduct ∧
      inst context redex = source ∧ inst context reduct = target

/-- Operational closure under authored equations. -/
def StepModE {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rule : UnpositionedRewrite (withMetas S M)) {s : S.Srt}
    (source target : Term S [] s) : Prop :=
  ∃ source' target' : Term S [] s,
    EqClosure equations source source' ∧ rule.Step source' target' ∧
      EqClosure equations target' target

/-- Equation-closed reduction is stable when its source is replaced by an
equivalent term. -/
theorem stepModE_resp_left {M : List (MetaArity S)}
    {equations : List (EqAxiom S M)}
    {rule : UnpositionedRewrite (withMetas S M)}
    {s : S.Srt} {source source' target : Term S [] s}
    (equivalent : EqClosure equations source source')
    (step : rule.StepModE equations source' target) :
    rule.StepModE equations source target := by
  obtain ⟨redex, reduct, before, fires, after⟩ := step
  exact ⟨redex, reduct, .trans equivalent before, fires, after⟩

/-- The same stability holds at the target. -/
theorem stepModE_resp_right {M : List (MetaArity S)}
    {equations : List (EqAxiom S M)}
    {rule : UnpositionedRewrite (withMetas S M)}
    {s : S.Srt} {source target target' : Term S [] s}
    (step : rule.StepModE equations source target)
    (equivalent : EqClosure equations target target') :
    rule.StepModE equations source target' := by
  obtain ⟨redex, reduct, before, fires, after⟩ := step
  exact ⟨redex, reduct, before, fires, .trans after equivalent⟩

end UnpositionedRewrite

/-- The unconditional fragment of the source's bare signature/equations/rules
triple. Conditional premises belong to the canonical `LanguageDef` layer. -/
structure UnpositionedPresentation (S : Signature) where
  metas : List (MetaArity S)
  eqs : List (EqAxiom S metas)
  rules : List (UnpositionedRewrite (withMetas S metas))

namespace UnpositionedPresentation

/-- A step generated by one of the presentation's rules. -/
def Step (presentation : UnpositionedPresentation S)
    {s : S.Srt} (source target : Term S [] s) : Prop :=
  ∃ i : Fin presentation.rules.length,
    (presentation.rules.get i).Step source target

/-- The same relation modulo the presentation's equations. -/
def StepModE (presentation : UnpositionedPresentation S)
    {s : S.Srt} (source target : Term S [] s) : Prop :=
  ∃ i : Fin presentation.rules.length,
    (presentation.rules.get i).StepModE presentation.eqs source target

theorem stepModE_resp_left (presentation : UnpositionedPresentation S)
    {s : S.Srt} {source source' target : Term S [] s}
    (equivalent : EqClosure presentation.eqs source source')
    (step : presentation.StepModE source' target) :
    presentation.StepModE source target := by
  obtain ⟨i, fires⟩ := step
  exact ⟨i, UnpositionedRewrite.stepModE_resp_left equivalent fires⟩

theorem stepModE_resp_right (presentation : UnpositionedPresentation S)
    {s : S.Srt} {source target target' : Term S [] s}
    (step : presentation.StepModE source target)
    (equivalent : EqClosure presentation.eqs target target') :
    presentation.StepModE source target' := by
  obtain ⟨i, fires⟩ := step
  exact ⟨i, UnpositionedRewrite.stepModE_resp_right fires equivalent⟩

end UnpositionedPresentation

namespace PositionedRewrite

/-- Forget the selected position while retaining both sides and their scope. -/
def unpositioned (rule : PositionedRewrite S) : UnpositionedRewrite S where
  ctx := rule.ctx
  sort := rule.sort
  lhs := rule.lhs
  rhs := rule.rhs

/-- Selecting a position does not change the rule's root firings. -/
theorem rootStep_iff_unpositioned {M : List (MetaArity S)}
    (rule : PositionedRewrite (withMetas S M))
    {source target : Term S [] rule.sort} :
    RootStep rule source target ↔ rule.unpositioned.RootStep source target := by
  constructor
  · rintro ⟨firing, left, right⟩
    exact ⟨firing.body, firing.close, left, right⟩
  · rintro ⟨body, close, left, right⟩
    exact ⟨⟨body, close⟩, left, right⟩

/-- The contextual step relation also forgets the selected position exactly. -/
theorem step_iff_unpositioned {M : List (MetaArity S)}
    (rule : PositionedRewrite (withMetas S M))
    {s : S.Srt} {source target : Term S [] s} :
    Mettapedia.OSLF.Binding.Step rule source target ↔
      rule.unpositioned.Step source target := by
  constructor
  · rintro ⟨context, redex, reduct, linear, fires, left, right⟩
    exact ⟨context, redex, reduct, linear,
      (rule.rootStep_iff_unpositioned).mp fires, left, right⟩
  · rintro ⟨context, redex, reduct, linear, fires, left, right⟩
    exact ⟨context, redex, reduct, linear,
      (rule.rootStep_iff_unpositioned).mpr fires, left, right⟩

/-- The comparison continues to hold after quotienting by the same equations. -/
theorem stepModE_iff_unpositioned {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rule : PositionedRewrite (withMetas S M))
    {s : S.Srt} {source target : Term S [] s} :
    Mettapedia.OSLF.Binding.StepModE equations rule source target ↔
      rule.unpositioned.StepModE equations source target := by
  constructor
  · rintro ⟨source', target', left, fires, right⟩
    exact ⟨source', target', left, (rule.step_iff_unpositioned).mp fires, right⟩
  · rintro ⟨source', target', left, fires, right⟩
    exact ⟨source', target', left, (rule.step_iff_unpositioned).mpr fires, right⟩

end PositionedRewrite

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

/-- Forget every selected redex position. This changes the data available to
later constructions, but does not change the unconditional dynamics. -/
def toUnpositioned : UnpositionedPresentation S where
  metas := Pr.metas
  eqs := Pr.eqs
  rules := Pr.rules.map PositionedRewrite.unpositioned

/-- The step relation a presentation denotes: some rule fires. -/
def Step {s : S.Srt} (t u : Term S [] s) : Prop :=
  ∃ i : Fin Pr.rules.length, Mettapedia.OSLF.Binding.Step (Pr.rules.get i) t u

/-- The step relation modulo the presentation's own equations. -/
def StepModE {s : S.Srt} (t u : Term S [] s) : Prop :=
  ∃ i : Fin Pr.rules.length,
    Mettapedia.OSLF.Binding.StepModE Pr.eqs (Pr.rules.get i) t u

/-- Selecting positions leaves the whole unconditional step relation intact. -/
theorem step_iff_toUnpositioned {s : S.Srt} {t u : Term S [] s} :
    Pr.Step t u ↔ Pr.toUnpositioned.Step t u := by
  constructor
  · rintro ⟨i, fires⟩
    let j : Fin Pr.toUnpositioned.rules.length :=
      ⟨i.val, by simp [toUnpositioned]⟩
    refine ⟨j, ?_⟩
    simpa [j, toUnpositioned] using
      (PositionedRewrite.step_iff_unpositioned _).mp fires
  · rintro ⟨j, fires⟩
    rcases j with ⟨index, bound⟩
    have originalBound : index < Pr.rules.length := by
      simpa [toUnpositioned] using bound
    refine ⟨⟨index, originalBound⟩, ?_⟩
    apply (PositionedRewrite.step_iff_unpositioned _).mpr
    simpa [toUnpositioned, List.get_eq_getElem, List.getElem_map] using fires

/-- The comparison also preserves reduction modulo authored equations. -/
theorem stepModE_iff_toUnpositioned {s : S.Srt} {t u : Term S [] s} :
    Pr.StepModE t u ↔ Pr.toUnpositioned.StepModE t u := by
  constructor
  · rintro ⟨i, fires⟩
    let j : Fin Pr.toUnpositioned.rules.length :=
      ⟨i.val, by simp [toUnpositioned]⟩
    refine ⟨j, ?_⟩
    simpa [j, toUnpositioned] using
      (PositionedRewrite.stepModE_iff_unpositioned Pr.eqs _).mp fires
  · rintro ⟨j, fires⟩
    rcases j with ⟨index, bound⟩
    have originalBound : index < Pr.rules.length := by
      simpa [toUnpositioned] using bound
    refine ⟨⟨index, originalBound⟩, ?_⟩
    apply (PositionedRewrite.stepModE_iff_unpositioned Pr.eqs _).mpr
    simpa [toUnpositioned, List.get_eq_getElem, List.getElem_map] using fires

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
