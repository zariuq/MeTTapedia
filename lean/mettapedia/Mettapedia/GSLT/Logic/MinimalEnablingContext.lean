import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# Minimal enabling contexts as a universal property

A context label is not minimal merely because a presentation marks it so.
For a fixed source and authored rule it must be a least enabling context under
context factorization: every other context enabling that rule factors through
it.  This module isolates exactly the data and laws needed to state that
property and derives the corresponding labeled Hennessy--Milner system.

An implementation based on redex relative pushouts supplies this interface by
proving that its computed context has the universal property.  Existence is
intentionally not assumed for arbitrary GSLTs; it is a theorem or admitted
capability of the particular operational theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.MinimalEnablingContext

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner

universe uContext uRule uAtom

/-- Context composition and rule-indexed firing for one GSLT.  Rule identity
is retained because minimality is relative to the rule being enabled.  The
plug laws hold up to the equations, as every law of a GSLT does; a syntactic
carrier such as a bag of parallel components satisfies them only modulo its
collection laws. -/
structure ContextualRules (S : GSLT) where
  Context : Type uContext
  identity : Context
  compose : Context → Context → Context
  plug : Context → S.Term → S.Term
  plug_identity : ∀ term, S.Equiv (plug identity term) term
  plug_compose : ∀ outer inner term,
    S.Equiv (plug (compose outer inner) term) (plug outer (plug inner term))
  plug_resp : ∀ context {left right},
    S.Equiv left right → S.Equiv (plug context left) (plug context right)
  Rule : Type uRule
  fires : Rule → S.Term → S.Term → Prop
  fires_resp_left : ∀ {rule left right target},
    S.Equiv left right → fires rule left target →
      ∃ target', fires rule right target' ∧ S.Equiv target target'
  fires_resp_right : ∀ {rule source target target'},
    fires rule source target → S.Equiv target target' →
      fires rule source target'
  fires_step : ∀ {rule source target}, fires rule source target → S.Step source target

variable {S : GSLT} (rules : ContextualRules.{uContext, uRule} S)

namespace ContextualRules

/-- `inner` factors into `outer` when `outer` is, up to the GSLT equations,
some residual context around `inner`.  Thus `inner` is no larger than
`outer`. -/
def Factors (inner outer : rules.Context) : Prop :=
  ∃ residual : rules.Context, ∀ term : S.Term,
    S.Equiv (rules.plug outer term)
      (rules.plug residual (rules.plug inner term))

theorem factors_refl (context : rules.Context) : rules.Factors context context := by
  refine ⟨rules.identity, ?_⟩
  intro term
  exact S.equations.iseqv.symm (rules.plug_identity _)

theorem factors_trans {first second third : rules.Context}
    (firstSecond : rules.Factors first second)
    (secondThird : rules.Factors second third) :
    rules.Factors first third := by
  obtain ⟨afterFirst, firstSecond⟩ := firstSecond
  obtain ⟨afterSecond, secondThird⟩ := secondThird
  refine ⟨rules.compose afterSecond afterFirst, ?_⟩
  intro term
  exact S.equations.iseqv.trans (secondThird term)
    (S.equations.iseqv.trans (rules.plug_resp afterSecond (firstSecond term))
      (S.equations.iseqv.symm (rules.plug_compose afterSecond afterFirst _)))

/-- A context enables a particular authored rule at a source when plugging
the source exposes an instance of that rule. -/
def Enables (context : rules.Context) (source : S.Term) (rule : rules.Rule) : Prop :=
  ∃ target, rules.fires rule (rules.plug context source) target

/-- Equation-equivalent sources have exactly the same enabling contexts for a
fixed rule. -/
theorem enables_iff_of_equiv (context : rules.Context) (rule : rules.Rule)
    {left right : S.Term} (equivalent : S.Equiv left right) :
    rules.Enables context left rule ↔ rules.Enables context right rule := by
  constructor
  · rintro ⟨target, fires⟩
    obtain ⟨target', fires', _⟩ :=
      rules.fires_resp_left (rules.plug_resp context equivalent) fires
    exact ⟨target', fires'⟩
  · rintro ⟨target, fires⟩
    obtain ⟨target', fires', _⟩ := rules.fires_resp_left
      (rules.plug_resp context (S.equations.iseqv.symm equivalent)) fires
    exact ⟨target', fires'⟩

/-- The universal property of a minimal enabling context: it enables the
chosen rule, and it factors into every other context that does so. -/
def IsLeastEnabler (context : rules.Context) (source : S.Term)
    (rule : rules.Rule) : Prop :=
  rules.Enables context source rule ∧
    ∀ other, rules.Enables other source rule → rules.Factors context other

/-- Least-enabler status is invariant under the GSLT equations. -/
theorem isLeastEnabler_iff_of_equiv (context : rules.Context) (rule : rules.Rule)
    {left right : S.Term} (equivalent : S.Equiv left right) :
    rules.IsLeastEnabler context left rule ↔
      rules.IsLeastEnabler context right rule := by
  constructor
  · rintro ⟨enabled, least⟩
    refine ⟨(rules.enables_iff_of_equiv context rule equivalent).mp enabled, ?_⟩
    intro other otherEnabled
    exact least other
      ((rules.enables_iff_of_equiv other rule equivalent).mpr otherEnabled)
  · rintro ⟨enabled, least⟩
    refine ⟨(rules.enables_iff_of_equiv context rule equivalent).mpr enabled, ?_⟩
    intro other otherEnabled
    exact least other
      ((rules.enables_iff_of_equiv other rule equivalent).mp otherEnabled)

/-- The minimal-context labeled transition relation.  A firing is admitted
only together with the least-enabler universal property for its source and
authored rule. -/
def Act (context : rules.Context) (source target : S.Term) : Prop :=
  ∃ rule : rules.Rule,
    rules.IsLeastEnabler context source rule ∧
      rules.fires rule (rules.plug context source) target

theorem act_step {context : rules.Context} {source target : S.Term}
    (act : rules.Act context source target) :
    S.Step (rules.plug context source) target := by
  obtain ⟨rule, _, fires⟩ := act
  exact rules.fires_step fires

theorem act_resp_left {context : rules.Context} {left right target : S.Term}
    (equivalent : S.Equiv left right) (act : rules.Act context left target) :
    ∃ target', rules.Act context right target' ∧ S.Equiv target target' := by
  obtain ⟨rule, least, fires⟩ := act
  obtain ⟨target', fires', targetEquivalent⟩ :=
    rules.fires_resp_left (rules.plug_resp context equivalent) fires
  exact ⟨target', ⟨rule,
    (rules.isLeastEnabler_iff_of_equiv context rule equivalent).mp least,
    fires'⟩, targetEquivalent⟩

theorem act_resp_right {context : rules.Context} {source target target' : S.Term}
    (act : rules.Act context source target) (equivalent : S.Equiv target target') :
    rules.Act context source target' := by
  obtain ⟨rule, least, fires⟩ := act
  exact ⟨rule, least, rules.fires_resp_right fires equivalent⟩

/-- A family of equation-invariant atomic observations. -/
structure Observations (S : GSLT) where
  Atom : Type uAtom
  observes : Atom → S.Term → Prop
  observes_resp : ∀ atom {left right},
    S.Equiv left right → (observes atom left ↔ observes atom right)

/-- The Hennessy--Milner system whose labels are precisely the contexts that
satisfy the least-enabler obligation at a transition. -/
def hmlSystem (observations : Observations.{uAtom} S) :
    System.{uAtom, uContext} S where
  Atom := observations.Atom
  observes := observations.observes
  observes_resp := observations.observes_resp
  Label := rules.Context
  act := rules.Act
  act_resp_left := rules.act_resp_left
  act_resp_right := rules.act_resp_right

/-! ## Positive and negative boundary lemmas -/

/-- A least enabling firing is admitted as a context-labeled transition. -/
theorem act_of_least_firing {context : rules.Context} {source target : S.Term}
    {rule : rules.Rule} (least : rules.IsLeastEnabler context source rule)
    (fires : rules.fires rule (rules.plug context source) target) :
    rules.Act context source target :=
  ⟨rule, least, fires⟩

/-- Merely firing in a context is insufficient when that context is not a
least enabler. -/
theorem not_act_of_no_least_rule {context : rules.Context} {source target : S.Term}
    (noLeast : ∀ rule, ¬ rules.IsLeastEnabler context source rule) :
    ¬ rules.Act context source target := by
  rintro ⟨rule, least, _⟩
  exact noLeast rule least

/-! ## A non-vacuous factorization canary

Natural-number contexts add tokens to a counter.  The sole rule consumes one
token.  Context `1` is therefore the least enabler of the rule at source `0`;
context `2` also exposes a firing, but is rejected as a label because it does
not factor into the smaller enabling context. -/

namespace CounterCanary

/-- A counter decreases by exactly one at each step. -/
abbrev counterGSLT : GSLT where
  Term := Nat
  equations :=
    { r := Eq
      iseqv :=
        { refl := Eq.refl
          symm := Eq.symm
          trans := Eq.trans } }
  rewrites := fun source target => 0 < source ∧ target + 1 = source
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Contexts add a fixed number of tokens before the counter rule fires. -/
abbrev counterRules : ContextualRules counterGSLT where
  Context := Nat
  identity := 0
  compose := Nat.add
  plug := Nat.add
  plug_identity := by intro term; exact Nat.zero_add term
  plug_compose := by intro outer inner term; exact Nat.add_assoc outer inner term
  plug_resp := by
    intro context left right equal
    subst right
    rfl
  Rule := Unit
  fires := fun _ source target => 0 < source ∧ target + 1 = source
  fires_resp_left := by
    intro rule left right target equal fires
    subst right
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro rule source target target' fires equal
    subst target'
    exact fires
  fires_step := by intro rule source target fires; exact fires

/-- Adding one token is the least context that enables consumption at zero. -/
theorem one_isLeastEnabler : counterRules.IsLeastEnabler 1 0 () := by
  constructor
  · change ∃ target, 0 < 1 + 0 ∧ target + 1 = 1 + 0
    exact ⟨0, Nat.zero_lt_succ 0, rfl⟩
  · intro other enabled
    change ∃ target, 0 < other + 0 ∧ target + 1 = other + 0 at enabled
    obtain ⟨target, positive, _⟩ := enabled
    have one_le : 1 ≤ other := by
      simpa using (Nat.add_one_le_iff.mpr positive : 0 + 1 ≤ other)
    change ∃ residual, ∀ term, other + term = residual + (1 + term)
    refine ⟨other - 1, ?_⟩
    intro term
    calc
      other + term = (other - 1 + 1) + term := by
        rw [Nat.sub_add_cancel one_le]
      _ = (other - 1) + (1 + term) := Nat.add_assoc _ _ _

/-- The least context is admitted as an actual minimal-context label. -/
theorem one_act : counterRules.Act 1 0 0 :=
  counterRules.act_of_least_firing one_isLeastEnabler (by
    change 0 < 1 + 0 ∧ 0 + 1 = 1 + 0
    exact ⟨Nat.zero_lt_succ 0, rfl⟩)

/-- Adding two tokens exposes a genuine rule firing. -/
theorem two_fires :
    counterRules.fires () (counterRules.plug 2 0) 1 := by
  change 0 < 2 + 0 ∧ 1 + 1 = 2 + 0
  exact ⟨Nat.zero_lt_succ 1, rfl⟩

/-- The larger firing context is not least: it cannot factor through the
one-token context. -/
theorem two_not_isLeastEnabler : ¬ counterRules.IsLeastEnabler 2 0 () := by
  intro least
  have factors := least.2 1 one_isLeastEnabler.1
  change ∃ residual, ∀ term, 1 + term = residual + (2 + term) at factors
  obtain ⟨residual, factors⟩ := factors
  have impossible : 1 = residual + 2 := by simpa using factors 0
  have two_le_one : 2 ≤ 1 := by
    rw [impossible]
    exact Nat.le_add_left 2 residual
  exact (by decide : ¬ 2 ≤ 1) two_le_one

/-- Negative control: a firing alone is not enough to manufacture a minimal
context label. -/
theorem two_fires_but_not_act :
    counterRules.fires () (counterRules.plug 2 0) 1 ∧
      ¬ counterRules.Act 2 0 1 := by
  refine ⟨two_fires, ?_⟩
  rintro ⟨rule, least, _⟩
  cases rule
  exact two_not_isLeastEnabler least

#print axioms one_isLeastEnabler
#print axioms one_act
#print axioms two_fires_but_not_act

end CounterCanary

#print axioms factors_trans
#print axioms enables_iff_of_equiv
#print axioms isLeastEnabler_iff_of_equiv
#print axioms act_resp_left
#print axioms act_resp_right
#print axioms hmlSystem
#print axioms not_act_of_no_least_rule

end ContextualRules

end Mettapedia.GSLT.MinimalEnablingContext
