import Mettapedia.GSLT.Logic.MinimalEnablingContext

/-!
# Congruence of context-labelled bisimilarity, relative to a class of contexts

Summarising the least-enabler construction as "the induced bisimulation is a
congruence" is false unqualified.  Congruence holds with respect to a class `A`
of admissible contexts, and observations must be restricted to the same class.
This module makes the class a parameter and proves the congruence from exactly
the two properties that qualification names:

* `LeastEnablerComposes` — for contexts of the class, being a least enabler at
  `C[p]` is the same as being a least enabler at `p` after composing with `C`.
  It is stated as a hypothesis rather than assumed of GSLTs at large because it
  is a statement about a particular operational theory, not a general fact.

  **It is false for parallel contexts**, so the congruence below does not reach a
  process calculus whose composition is parallel.  Narrowing the class can repair
  it in principle -- `identityOnly_composes` discharges the obligation at
  `{identity}` -- but not for rho, whose class contains parallel remainders, which
  is exactly what the counterexample uses.  `ParallelLeastEnablerFails.leastEnablerComposes_fails` refutes it
  over a commutative monoid of contexts — where every plug law is an unconditional
  equation — with the admissible class taken to be all contexts.  The failure is
  not scarcity of least enablers: they exist at every source there.  Composing one
  with its context re-adds siblings the rule never needed, and the result is no
  longer least.  `RedexRelativeEnabling.no_least_enabler` exhibits the other,
  independent failure, where the universal property is not attained at all.

  What a parallel calculus uses instead is redex-relativity, where the universal
  property is an idem pushout and the congruence
  (`RedexRelativeCongruence.ipoBisimilar_comp`) needs no class parameter at all.

* `ObservationsRespectClass` — an observation cannot separate `C[p]` from `C[q]`
  when `p` and `q` are bisimilar and `C` is admissible.  Without it an
  observation could look through a context at a distinction the labels cannot
  make, and no amount of care with labels would repair that.

Both hypotheses are necessary, and `NecessityCanaries` below exhibits a failure
of congruence when the second is dropped.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.AdmissibleContextCongruence

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext

universe uContext uRule uAtom

variable {S : GSLT} {rules : ContextualRules.{uContext, uRule} S}

/-- A class of contexts closed under the identity and composition.  Labels and
observations are both restricted to it. -/
structure AdmissibleClass (rules : ContextualRules.{uContext, uRule} S) where
  /-- Membership in the class. -/
  Admissible : rules.Context → Prop
  /-- The empty context is admissible. -/
  identity_mem : Admissible rules.identity
  /-- Admissible contexts compose. -/
  compose_mem : ∀ {outer inner : rules.Context},
    Admissible outer → Admissible inner → Admissible (rules.compose outer inner)

namespace AdmissibleClass

variable (A : AdmissibleClass rules)

/-- Being a least enabler at `C[p]` is being a least enabler at `p` after
composition with `C`, for contexts of the class.  A redex-relative-pushout
construction for a particular theory is what discharges this. -/
def LeastEnablerComposes : Prop :=
  ∀ {outer inner : rules.Context} {source : S.Term} {rule : rules.Rule},
    A.Admissible inner → A.Admissible outer →
      (rules.IsLeastEnabler outer (rules.plug inner source) rule ↔
        rules.IsLeastEnabler (rules.compose outer inner) source rule)

/-- Observations are restricted to the class: an admissible context cannot
expose a difference between bisimilar terms. -/
def ObservationsRespectClass (M : System.{uAtom, uContext} S) : Prop :=
  ∀ {context : rules.Context} {left right : S.Term},
    A.Admissible context → M.Bisimilar left right →
      ∀ atom : M.Atom,
        M.observes atom (rules.plug context left) ↔
          M.observes atom (rules.plug context right)

/-- **The labelled system of a class.**  Its labels are the admissible
contexts, so a label is admissible *by construction*.

This is the structural point the class parameter turns on.  Labelling with
every context of the theory and then asking, as a hypothesis, that every label
be admissible forces the class to be everything — see
`labelsAdmissible_forces_total` below — which makes the parameter decorative
and puts every non-trivial class, the rho quote-free one included, out of
reach.  Restricting the labels instead is what lets a class be supplied, and it
is where `compose_mem` finally does work: the composed label of a step out of a
filled context must itself be admissible. -/
def labelledSystem (A : AdmissibleClass rules)
    (observations : ContextualRules.Observations.{uAtom} S) :
    System.{uAtom, uContext} S where
  Atom := observations.Atom
  observes := observations.observes
  observes_resp := observations.observes_resp
  Label := {context : rules.Context // A.Admissible context}
  act := fun label => rules.Act label.val
  act_resp_left := fun {label} => rules.act_resp_left
  act_resp_right := fun {label} => rules.act_resp_right

end AdmissibleClass

/-! ## Bisimilarity as a bisimulation

Three projections used repeatedly below: bisimilar terms match each other's
labelled steps and agree on every observation. -/

theorem bisimilar_forward {M : System.{uAtom, uContext} S} {left right : S.Term}
    (bisimilar : M.Bisimilar left right) (label : M.Label) {left' : S.Term}
    (step : M.act label left left') :
    ∃ right', M.act label right right' ∧ M.Bisimilar left' right' := by
  obtain ⟨relation, isBisim, related⟩ := bisimilar
  obtain ⟨right', step', related'⟩ := isBisim.1 related label step
  exact ⟨right', step', ⟨relation, isBisim, related'⟩⟩

theorem bisimilar_backward {M : System.{uAtom, uContext} S} {left right : S.Term}
    (bisimilar : M.Bisimilar left right) (label : M.Label) {right' : S.Term}
    (step : M.act label right right') :
    ∃ left', M.act label left left' ∧ M.Bisimilar left' right' := by
  obtain ⟨relation, isBisim, related⟩ := bisimilar
  obtain ⟨left', step', related'⟩ := isBisim.2.1 related label step
  exact ⟨left', step', ⟨relation, isBisim, related'⟩⟩

theorem bisimilar_observes {M : System.{uAtom, uContext} S} {left right : S.Term}
    (bisimilar : M.Bisimilar left right) (atom : M.Atom) :
    M.observes atom left ↔ M.observes atom right := by
  obtain ⟨relation, isBisim, related⟩ := bisimilar
  exact isBisim.2.2 related atom

/-! ## The congruence -/

variable {observations : ContextualRules.Observations.{uAtom} S}

/-- The relation used to prove congruence: bisimilar pairs, together with
pairs obtained by filling one admissible context with bisimilar terms. -/
abbrev contextClosure (A : AdmissibleClass rules)
    (M : System.{uAtom, uContext} S) (left right : S.Term) : Prop :=
  M.Bisimilar left right ∨
    ∃ (context : rules.Context) (inner innerRight : S.Term),
      A.Admissible context ∧ M.Bisimilar inner innerRight ∧
        S.Equiv left (rules.plug context inner) ∧
        S.Equiv right (rules.plug context innerRight)

/-- A labelled step out of a filled admissible context is a step out of the
inner term under the composed context. -/
theorem act_of_plug (A : AdmissibleClass rules)
    (composes : A.LeastEnablerComposes)
    {context label : rules.Context} {inner target : S.Term}
    (hcontext : A.Admissible context) (hlabel : A.Admissible label)
    (act : rules.Act label (rules.plug context inner) target) :
    ∃ target', rules.Act (rules.compose label context) inner target' ∧
      S.Equiv target target' := by
  obtain ⟨rule, least, fires⟩ := act
  have leastComposed :
      rules.IsLeastEnabler (rules.compose label context) inner rule :=
    (composes hcontext hlabel).mp least
  have hplug : S.Equiv (rules.plug (rules.compose label context) inner)
      (rules.plug label (rules.plug context inner)) :=
    rules.plug_compose label context inner
  obtain ⟨target', fires', equivalent⟩ :=
    rules.fires_resp_left (S.equations.iseqv.symm hplug) fires
  exact ⟨target', ⟨rule, leastComposed, fires'⟩, equivalent⟩

/-- Conversely, a labelled step out of the inner term under a composed context
is a step out of the filled context. -/
theorem act_of_compose (A : AdmissibleClass rules)
    (composes : A.LeastEnablerComposes)
    {context label : rules.Context} {inner target : S.Term}
    (hcontext : A.Admissible context) (hlabel : A.Admissible label)
    (act : rules.Act (rules.compose label context) inner target) :
    ∃ target', rules.Act label (rules.plug context inner) target' ∧
      S.Equiv target target' := by
  obtain ⟨rule, least, fires⟩ := act
  have leastFilled : rules.IsLeastEnabler label (rules.plug context inner) rule :=
    (composes hcontext hlabel).mpr least
  have hplug : S.Equiv (rules.plug (rules.compose label context) inner)
      (rules.plug label (rules.plug context inner)) :=
    rules.plug_compose label context inner
  obtain ⟨target', fires', equivalent⟩ := rules.fires_resp_left hplug fires
  exact ⟨target', ⟨rule, leastFilled, fires'⟩, equivalent⟩

/-- **Congruence.**  Context-labelled bisimilarity is preserved by every
context of the admissible class, given that least enablers compose with the
class and that observations do not look through it. -/
theorem bisimilar_plug (A : AdmissibleClass rules)
    (composes : A.LeastEnablerComposes)
    (respects : A.ObservationsRespectClass (rules.hmlSystem observations))
    (labelsAdmissible : ∀ label : rules.Context, A.Admissible label)
    {context : rules.Context} {left right : S.Term}
    (hcontext : A.Admissible context)
    (bisimilar : (rules.hmlSystem observations).Bisimilar left right) :
    (rules.hmlSystem observations).Bisimilar
      (rules.plug context left) (rules.plug context right) := by
  classical
  set M := rules.hmlSystem observations with hM
  refine ⟨contextClosure A M, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- a step of the left term is matched by the right
    rintro first second (hbis | ⟨ctx, p, q, hctx, hpq, hfirst, hsecond⟩) label first' step
    · obtain ⟨second', step', bis'⟩ := bisimilar_forward hbis label step
      exact ⟨second', step', Or.inl bis'⟩
    · obtain ⟨atPlug, actPlug, equivPlug⟩ := rules.act_resp_left hfirst step
      obtain ⟨innerTarget, actInner, equivInner⟩ :=
        act_of_plug A composes hctx (labelsAdmissible label) actPlug
      obtain ⟨innerRight, actRight, bisInner⟩ :=
        bisimilar_forward hpq (rules.compose label ctx) actInner
      obtain ⟨filled, actFilled, equivFilled⟩ :=
        act_of_compose A composes hctx (labelsAdmissible label) actRight
      obtain ⟨second', actSecond, equivSecond⟩ :=
        rules.act_resp_left (S.equations.iseqv.symm hsecond) actFilled
      refine ⟨second', actSecond, Or.inl ?_⟩
      have leftChain : M.Bisimilar first' innerTarget :=
        M.bisimilar_of_equiv (S.equations.iseqv.trans equivPlug equivInner)
      have rightChain : M.Bisimilar innerRight second' :=
        M.bisimilar_of_equiv (S.equations.iseqv.trans equivFilled equivSecond)
      exact M.bisimilar_trans leftChain (M.bisimilar_trans bisInner rightChain)
  · -- a step of the right term is matched by the left
    rintro first second (hbis | ⟨ctx, p, q, hctx, hpq, hfirst, hsecond⟩) label second' step
    · obtain ⟨first', step', bis'⟩ := bisimilar_backward hbis label step
      exact ⟨first', step', Or.inl bis'⟩
    · obtain ⟨atPlug, actPlug, equivPlug⟩ := rules.act_resp_left hsecond step
      obtain ⟨innerTarget, actInner, equivInner⟩ :=
        act_of_plug A composes hctx (labelsAdmissible label) actPlug
      obtain ⟨innerLeft, actLeft, bisInner⟩ :=
        bisimilar_backward hpq (rules.compose label ctx) actInner
      obtain ⟨filled, actFilled, equivFilled⟩ :=
        act_of_compose A composes hctx (labelsAdmissible label) actLeft
      obtain ⟨first', actFirst, equivFirst⟩ :=
        rules.act_resp_left (S.equations.iseqv.symm hfirst) actFilled
      refine ⟨first', actFirst, Or.inl ?_⟩
      have leftChain : M.Bisimilar first' innerLeft :=
        M.bisimilar_symm
          (M.bisimilar_of_equiv (S.equations.iseqv.trans equivFilled equivFirst))
      have rightChain : M.Bisimilar innerTarget second' :=
        M.bisimilar_symm
          (M.bisimilar_of_equiv (S.equations.iseqv.trans equivPlug equivInner))
      exact M.bisimilar_trans leftChain (M.bisimilar_trans bisInner rightChain)
  · -- observations agree
    rintro first second (hbis | ⟨ctx, p, q, hctx, hpq, hfirst, hsecond⟩) atom
    · exact bisimilar_observes hbis atom
    · exact (M.observes_resp atom hfirst).trans
        ((respects hctx hpq atom).trans (M.observes_resp atom hsecond).symm)
  · exact Or.inr ⟨context, left, right, hcontext, bisimilar,
      S.equations.iseqv.refl _, S.equations.iseqv.refl _⟩

/-- The hypothesis that every label is admissible forces the class to be
everything.  Stated so that the defect it names cannot quietly come back. -/
theorem labelsAdmissible_forces_total (A : AdmissibleClass rules)
    (labelsAdmissible : ∀ label : rules.Context, A.Admissible label) :
    A.Admissible = fun _ => True := by
  funext context
  exact propext ⟨fun _ => trivial, fun _ => labelsAdmissible context⟩

/-- **Congruence, with the class doing work.**  Context-labelled bisimilarity
in the labelled system of a class is preserved by every context of that class,
given that least enablers compose with the class and that observations do not
look through it.

There is no hypothesis forcing the class to be everything: a label is an
admissible context by construction, and the composed label of a step out of a
filled context is admissible by `compose_mem`. -/
theorem bisimilar_plug_labelled (A : AdmissibleClass rules)
    (composes : A.LeastEnablerComposes)
    (respects : A.ObservationsRespectClass (A.labelledSystem observations))
    {context : rules.Context} {left right : S.Term}
    (hcontext : A.Admissible context)
    (bisimilar : (A.labelledSystem observations).Bisimilar left right) :
    (A.labelledSystem observations).Bisimilar
      (rules.plug context left) (rules.plug context right) := by
  classical
  set M := A.labelledSystem observations with hM
  refine ⟨contextClosure A M, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro first second (hbis | ⟨ctx, p, q, hctx, hpq, hfirst, hsecond⟩) label first' step
    · obtain ⟨second', step', bis'⟩ := bisimilar_forward hbis label step
      exact ⟨second', step', Or.inl bis'⟩
    · obtain ⟨atPlug, actPlug, equivPlug⟩ := rules.act_resp_left hfirst step
      obtain ⟨innerTarget, actInner, equivInner⟩ :=
        act_of_plug A composes hctx label.property actPlug
      obtain ⟨innerRight, actRight, bisInner⟩ :=
        bisimilar_forward hpq
          ⟨rules.compose label.val ctx, A.compose_mem label.property hctx⟩ actInner
      obtain ⟨filled, actFilled, equivFilled⟩ :=
        act_of_compose A composes hctx label.property actRight
      obtain ⟨second', actSecond, equivSecond⟩ :=
        rules.act_resp_left (S.equations.iseqv.symm hsecond) actFilled
      refine ⟨second', actSecond, Or.inl ?_⟩
      have leftChain : M.Bisimilar first' innerTarget :=
        M.bisimilar_of_equiv (S.equations.iseqv.trans equivPlug equivInner)
      have rightChain : M.Bisimilar innerRight second' :=
        M.bisimilar_of_equiv (S.equations.iseqv.trans equivFilled equivSecond)
      exact M.bisimilar_trans leftChain (M.bisimilar_trans bisInner rightChain)
  · rintro first second (hbis | ⟨ctx, p, q, hctx, hpq, hfirst, hsecond⟩) label second' step
    · obtain ⟨first', step', bis'⟩ := bisimilar_backward hbis label step
      exact ⟨first', step', Or.inl bis'⟩
    · obtain ⟨atPlug, actPlug, equivPlug⟩ := rules.act_resp_left hsecond step
      obtain ⟨innerTarget, actInner, equivInner⟩ :=
        act_of_plug A composes hctx label.property actPlug
      obtain ⟨innerLeft, actLeft, bisInner⟩ :=
        bisimilar_backward hpq
          ⟨rules.compose label.val ctx, A.compose_mem label.property hctx⟩ actInner
      obtain ⟨filled, actFilled, equivFilled⟩ :=
        act_of_compose A composes hctx label.property actLeft
      obtain ⟨first', actFirst, equivFirst⟩ :=
        rules.act_resp_left (S.equations.iseqv.symm hfirst) actFilled
      refine ⟨first', actFirst, Or.inl ?_⟩
      have leftChain : M.Bisimilar first' innerLeft :=
        M.bisimilar_symm
          (M.bisimilar_of_equiv (S.equations.iseqv.trans equivFilled equivFirst))
      have rightChain : M.Bisimilar innerTarget second' :=
        M.bisimilar_symm
          (M.bisimilar_of_equiv (S.equations.iseqv.trans equivPlug equivInner))
      exact M.bisimilar_trans leftChain (M.bisimilar_trans bisInner rightChain)
  · rintro first second (hbis | ⟨ctx, p, q, hctx, hpq, hfirst, hsecond⟩) atom
    · exact bisimilar_observes hbis atom
    · exact (M.observes_resp atom hfirst).trans
        ((respects hctx hpq atom).trans (M.observes_resp atom hsecond).symm)
  · exact Or.inr ⟨context, left, right, hcontext, bisimilar,
      S.equations.iseqv.refl _, S.equations.iseqv.refl _⟩

/-! ## The observation hypothesis is necessary

A theory with no rules at all, whose contexts merely wrap a term.  Nothing
steps, so every pair of terms with the same observations is bisimilar; the two
wrappable terms are therefore bisimilar.  An observation that fires on one
wrapped term and not the other then separates them, so bisimilarity is not a
congruence for this class.  The class is closed under identity and composition
and the labels are unconstrained, so the only hypothesis of `bisimilar_plug`
that fails here is `ObservationsRespectClass` — which is what makes this a
necessity witness for it rather than for something else. -/

namespace NecessityCanaries

/-- Two plain terms and their two wrapped forms. -/
inductive Wrapped where
  | plain (flag : Bool)
  | wrap (flag : Bool)
  deriving DecidableEq

/-- No term rewrites to anything. -/
abbrev inertGSLT : GSLT where
  Term := Wrapped
  equations :=
    { r := Eq
      iseqv := { refl := Eq.refl, symm := Eq.symm, trans := Eq.trans } }
  rewrites := fun _ _ => False
  rewrites_resp_left := by intro _ _ _ _ step; exact step.elim
  rewrites_resp_right := by intro _ _ _ step _; exact step.elim

/-- Contexts either leave a term alone or wrap it. -/
inductive WrapContext where
  | id
  | wrap
  deriving DecidableEq

/-- Wrapping a plain term records its flag; wrapping anything else is inert. -/
def wrapPlug : WrapContext → Wrapped → Wrapped
  | .id, term => term
  | .wrap, .plain flag => .wrap flag
  | .wrap, .wrap flag => .wrap flag

abbrev inertRules : ContextualRules inertGSLT where
  Context := WrapContext
  identity := .id
  compose := fun outer inner =>
    match outer, inner with
    | .id, c => c
    | .wrap, _ => .wrap
  plug := wrapPlug
  plug_identity := by intro term; rfl
  plug_compose := by
    intro outer inner term
    cases outer <;> cases inner <;> cases term <;> rfl
  plug_resp := by intro _ _ _ equal; subst equal; rfl
  Rule := Unit
  fires := fun _ _ _ => False
  fires_resp_left := by intro _ _ _ _ _ fires; exact fires.elim
  fires_resp_right := by intro _ _ _ _ fires _; exact fires.elim
  fires_step := by intro _ _ _ fires; exact fires.elim

/-- The observation sees a wrapped true flag and nothing else. -/
abbrev seesWrappedTrue : ContextualRules.Observations inertGSLT where
  Atom := Unit
  observes := fun _ term => term = .wrap true
  observes_resp := by intro _ _ _ equal; subst equal; exact Iff.rfl

abbrev canarySystem := inertRules.hmlSystem seesWrappedTrue

/-- Every context is admissible, and the class is closed. -/
abbrev everyContext : AdmissibleClass inertRules where
  Admissible := fun _ => True
  identity_mem := trivial
  compose_mem := by intro _ _ _ _; trivial

/-- Nothing ever acts, since no rule fires. -/
theorem no_act (label : WrapContext) (source target : Wrapped) :
    ¬ inertRules.Act label source target := by
  rintro ⟨_, _, fires⟩
  exact fires.elim

/-- The two plain terms are bisimilar: neither steps, and neither is observed. -/
theorem plain_bisimilar :
    canarySystem.Bisimilar (.plain true) (.plain false) := by
  refine ⟨fun left right => (left = .plain true ∧ right = .plain false), ⟨?_, ?_, ?_⟩, ⟨rfl, rfl⟩⟩
  · rintro left right ⟨hl, hr⟩ label left' step
    exact ((no_act label left left') step).elim
  · rintro left right ⟨hl, hr⟩ label right' step
    exact ((no_act label right right') step).elim
  · rintro left right ⟨hl, hr⟩ atom
    subst hl; subst hr
    constructor
    · intro h; exact Wrapped.noConfusion h
    · intro h; exact Wrapped.noConfusion h

/-- Their wrapped forms are not: the observation separates them. -/
theorem wrapped_not_bisimilar :
    ¬ canarySystem.Bisimilar
        (inertRules.plug .wrap (.plain true))
        (inertRules.plug .wrap (.plain false)) := by
  intro bisimilar
  have := bisimilar_observes bisimilar ()
  have hleft : canarySystem.observes () (inertRules.plug .wrap (.plain true)) := by
    show (Wrapped.wrap true) = Wrapped.wrap true
    rfl
  have hright := this.mp hleft
  have : (Wrapped.wrap false) = Wrapped.wrap true := hright
  exact absurd this (by decide)

/-- Hence congruence fails for this class, and the hypothesis
`ObservationsRespectClass` of `bisimilar_plug` cannot be dropped. -/
theorem congruence_fails :
    ¬ ∀ {context : WrapContext} {left right : Wrapped},
        everyContext.Admissible context →
        canarySystem.Bisimilar left right →
          canarySystem.Bisimilar
            (inertRules.plug context left) (inertRules.plug context right) := by
  intro congruence
  exact wrapped_not_bisimilar (congruence (context := .wrap) trivial plain_bisimilar)

/-! ### The class is doing work

The same theory, the same labelled-system construction, and only the class
different: congruence holds when the class is cut to the identity context and
fails when it is not.  This is what the class parameter buys, and it could not
be exhibited at all while a hypothesis forced the class to be everything. -/

/-- The labelled system of the unrestricted class. -/
abbrev canaryLabelled := everyContext.labelledSystem seesWrappedTrue

/-- The two plain terms are bisimilar in the labelled system too. -/
theorem plain_bisimilar_labelled :
    canaryLabelled.Bisimilar (.plain true) (.plain false) := by
  refine ⟨fun left right => (left = .plain true ∧ right = .plain false),
    ⟨?_, ?_, ?_⟩, ⟨rfl, rfl⟩⟩
  · rintro left right ⟨hl, hr⟩ label left' step
    exact ((no_act label.val left left') step).elim
  · rintro left right ⟨hl, hr⟩ label right' step
    exact ((no_act label.val right right') step).elim
  · rintro left right ⟨hl, hr⟩ atom
    subst hl; subst hr
    constructor
    · intro h; exact Wrapped.noConfusion h
    · intro h; exact Wrapped.noConfusion h

/-- Their wrapped forms are not. -/
theorem wrapped_not_bisimilar_labelled :
    ¬ canaryLabelled.Bisimilar
        (inertRules.plug .wrap (.plain true))
        (inertRules.plug .wrap (.plain false)) := by
  intro bisimilar
  have separated := bisimilar_observes bisimilar ()
  have hleft : canaryLabelled.observes () (inertRules.plug .wrap (.plain true)) := by
    show (Wrapped.wrap true) = Wrapped.wrap true
    rfl
  have hright : (Wrapped.wrap false) = Wrapped.wrap true := separated.mp hleft
  exact absurd hright (by decide)

/-- With the class unrestricted, congruence fails. -/
theorem congruence_fails_labelled :
    ¬ ∀ {context : WrapContext} {left right : Wrapped},
        everyContext.Admissible context →
        canaryLabelled.Bisimilar left right →
          canaryLabelled.Bisimilar
            (inertRules.plug context left) (inertRules.plug context right) := by
  intro congruence
  exact wrapped_not_bisimilar_labelled
    (congruence (context := .wrap) trivial plain_bisimilar_labelled)

/-- The same theory with the class cut down to the identity context. -/
abbrev identityOnly : AdmissibleClass inertRules where
  Admissible := fun context => context = .id
  identity_mem := rfl
  compose_mem := by
    intro outer inner houter hinner
    subst houter; subst hinner; rfl

/-- The restricted class is strictly smaller than everything. -/
theorem identityOnly_proper : ¬ identityOnly.Admissible .wrap := by decide

/-- Least enablers compose for it: no rule fires here, so no context enables
anything and both sides of the equivalence are empty. -/
theorem identityOnly_composes : identityOnly.LeastEnablerComposes := by
  intro outer inner source rule _ _
  constructor
  · rintro ⟨⟨_, fires⟩, _⟩; exact fires.elim
  · rintro ⟨⟨_, fires⟩, _⟩; exact fires.elim

/-- Observations do not look through the identity context. -/
theorem identityOnly_respects :
    identityOnly.ObservationsRespectClass
      (identityOnly.labelledSystem seesWrappedTrue) := by
  intro context left right hcontext bisimilar atom
  subst hcontext
  exact bisimilar_observes bisimilar atom

/-- **Congruence holds for the restricted class on the very theory where it
fails for the unrestricted one.** -/
theorem identityOnly_congruence {context : WrapContext} {left right : Wrapped}
    (hcontext : identityOnly.Admissible context)
    (bisimilar : (identityOnly.labelledSystem seesWrappedTrue).Bisimilar left right) :
    (identityOnly.labelledSystem seesWrappedTrue).Bisimilar
      (inertRules.plug context left) (inertRules.plug context right) :=
  bisimilar_plug_labelled identityOnly identityOnly_composes identityOnly_respects
    hcontext bisimilar

/-- And the failing hypothesis is exactly that one. -/
theorem observations_do_not_respect_class :
    ¬ everyContext.ObservationsRespectClass canarySystem := by
  intro respects
  have h := respects (context := .wrap) trivial plain_bisimilar ()
  have hleft : canarySystem.observes () (inertRules.plug .wrap (.plain true)) := rfl
  have hright := h.mp hleft
  have hbad : (Wrapped.wrap false) = Wrapped.wrap true := hright
  exact absurd hbad (by decide)

end NecessityCanaries

end Mettapedia.GSLT.AdmissibleContextCongruence
