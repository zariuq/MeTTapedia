import Mettapedia.GSLT.Logic.MinimalEnablingContext
import Mettapedia.GSLT.Logic.RelativePushout
import Mettapedia.GSLT.Logic.RedexRelativeCongruence
import Mathlib.CategoryTheory.SingleObj

/-!
# Why a label must be least *for its redex*, and not least outright

`MinimalEnablingContext.ContextualRules.IsLeastEnabler` asks a context to factor
into **every** context that enables the rule at the source.  That is a genuine
universal property, and it is the one the context-labelled transition relation
`Act` demands.  This module shows what it costs.

A source that can be completed in two incomparable ways has no least enabling
context at all — not because the theory is badly presented, but because the two
completions correspond to two different redexes, and no context is below both.
Since `Act` admits a firing only together with the absolute property, the
labelled system is then **blind at that source**: it has no transition out of a
term that plainly reduces in context.

That is the situation of a reflective process calculus.  An output can be
completed by an input on its own channel, and it can equally be placed beside a
self-contained interaction on some other channel; neither completion factors
through the other.  It is why `AdmissibleClass.LeastEnablerComposes` has never
been discharged for rho, and it is not a gap that a cleverer proof closes.

The repair is redex-relativity, and the universal property it wants is the
relative pushout of `RelativePushout`.  The same two completions that have no
common lower bound *are* least once the redex is fixed, and both are exhibited
below as idem pushouts in Mathlib's sense, in the one-object category of the
theory's own contexts.

**What is and is not built here.**  The canary's contexts form a commutative
monoid, so they are literally the morphisms of a one-object category and the
categorical notions apply on the nose.  For a general `ContextualRules` the
context category is a quotient of contexts by agreement on every filling, and
that construction is not built, so no general transport theorem is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.RedexRelativeEnabling

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open CategoryTheory
open Mettapedia.GSLT.RelativePushout

/-! ## A theory with two channels -/

/-- A term is how many tokens sit on each of two channels. -/
abbrev Tokens := ℕ × ℕ

/-- The rule fires when some channel carries a pair, and consumes everything. -/
def Fires (source target : Tokens) : Prop :=
  (2 ≤ source.1 ∨ 2 ≤ source.2) ∧ target = (0, 0)

/-- The theory: terms are token counts, the equations are equality, and the one
rule consumes a pair on either channel. -/
abbrev twoChannelGSLT : GSLT where
  Term := Tokens
  equations :=
    { r := Eq
      iseqv := { refl := Eq.refl, symm := Eq.symm, trans := Eq.trans } }
  rewrites := Fires
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- Contexts add tokens.  Composition is addition, so the contexts form a
commutative monoid — which is what makes them the morphisms of a one-object
category further down. -/
abbrev twoChannelRules : ContextualRules twoChannelGSLT where
  Context := Tokens
  identity := (0, 0)
  compose := fun outer inner => outer + inner
  plug := fun context term => context + term
  plug_identity := by
    intro term
    show ((0, 0) : Tokens) + term = term
    simp
  plug_compose := by
    intro outer inner term
    show outer + inner + term = outer + (inner + term)
    simp [add_assoc]
  plug_resp := by intro context left right equal; subst equal; rfl
  Rule := Unit
  fires := fun _ source target => Fires source target
  fires_resp_left := by
    intro rule left right target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro rule source target target' fires equal
    subst equal
    exact fires
  fires_step := by intro rule source target fires; exact fires

/-! ## Two incomparable completions -/

/-- The source: one token on the first channel, which cannot fire alone. -/
def source : Tokens := (1, 0)

/-- Completing the source on its own channel. -/
def completeFirst : Tokens := (1, 0)

/-- Or supplying a self-contained interaction on the other channel. -/
def completeSecond : Tokens := (0, 2)

theorem completeFirst_enables : twoChannelRules.Enables completeFirst source () :=
  ⟨(0, 0), Or.inl (by decide), rfl⟩

theorem completeSecond_enables : twoChannelRules.Enables completeSecond source () :=
  ⟨(0, 0), Or.inr (by decide), rfl⟩

/-- Neither completion factors through the other: the first supplies a token the
second does not, and conversely. -/
theorem completeFirst_not_factors :
    ¬ twoChannelRules.Factors completeFirst completeSecond := by
  rintro ⟨residual, factorisation⟩
  have evaluated := factorisation (0, 0)
  simp only [completeFirst, completeSecond] at evaluated
  have coordinate : (0 : ℕ) = residual.1 + 1 := congrArg Prod.fst evaluated
  omega

theorem completeSecond_not_factors :
    ¬ twoChannelRules.Factors completeSecond completeFirst := by
  rintro ⟨residual, factorisation⟩
  have evaluated := factorisation (0, 0)
  simp only [completeFirst, completeSecond] at evaluated
  have coordinate : (0 : ℕ) = residual.2 + 2 := congrArg Prod.snd evaluated
  omega

/-! ## So there is no least enabling context -/

/-- **The absolute universal property is unsatisfiable here.**  A least enabler
would have to factor into both completions, which forces it to be the empty
context — and the empty context does not enable the rule. -/
theorem no_least_enabler :
    ¬ ∃ context : Tokens, twoChannelRules.IsLeastEnabler context source () := by
  rintro ⟨context, enabled, least⟩
  obtain ⟨firstResidual, firstFactorisation⟩ := least completeFirst completeFirst_enables
  obtain ⟨secondResidual, secondFactorisation⟩ := least completeSecond completeSecond_enables
  have firstEval := firstFactorisation (0, 0)
  have secondEval := secondFactorisation (0, 0)
  simp only [completeFirst, completeSecond] at firstEval secondEval
  have firstSecond : (0 : ℕ) = firstResidual.2 + context.2 :=
    congrArg Prod.snd firstEval
  have secondFirst : (0 : ℕ) = secondResidual.1 + context.1 :=
    congrArg Prod.fst secondEval
  have isEmpty : context = (0, 0) := by
    refine Prod.ext ?_ ?_ <;> simp <;> omega
  obtain ⟨target, fires⟩ := enabled
  rw [isEmpty] at fires
  simp only [source] at fires
  rcases fires.1 with h | h <;> simp at h

/-- **And the labelled system is blind at this source.**  `Act` admits a firing
only with the absolute property, so no labelled transition leaves this term. -/
theorem no_act : ∀ context target : Tokens, ¬ twoChannelRules.Act context source target := by
  rintro context target ⟨rule, least, -⟩
  exact no_least_enabler ⟨context, least⟩

/-- Although the term plainly reduces in context, twice over. -/
theorem source_reduces_first :
    twoChannelGSLT.rewrites (twoChannelRules.plug completeFirst source) (0, 0) :=
  ⟨Or.inl (by decide), rfl⟩

theorem source_reduces_second :
    twoChannelGSLT.rewrites (twoChannelRules.plug completeSecond source) (0, 0) :=
  ⟨Or.inr (by decide), rfl⟩

/-! ## The same two completions, as relative pushouts

Contexts here compose by addition, so they are exactly the morphisms of the
one-object category on that monoid, and terms are morphisms of the same
category.  The relative-pushout notions therefore apply with nothing
transported. -/

/-- The context monoid as a one-object category. -/
abbrev Ctx := SingleObj (Multiplicative Tokens)

/-- A token count, as a morphism of that category. -/
def tok (first second : ℕ) : (SingleObj.star (Multiplicative Tokens)) ⟶
    (SingleObj.star (Multiplicative Tokens)) :=
  Multiplicative.ofAdd (first, second)

theorem tok_comp (a b c d : ℕ) : tok a b ≫ tok c d = tok (a + c) (b + d) := by
  show Multiplicative.ofAdd ((c, d) : Tokens) * Multiplicative.ofAdd ((a, b) : Tokens)
      = Multiplicative.ofAdd ((a + c, b + d) : Tokens)
  have coordinates : ((c, d) : Tokens) + (a, b) = (a + c, b + d) := by
    simp [Nat.add_comm]
  exact congrArg Multiplicative.ofAdd coordinates

theorem tok_id : tok 0 0 = 𝟙 (SingleObj.star (Multiplicative Tokens)) := rfl

theorem tok_injective {a b c d : ℕ} (equal : tok a b = tok c d) : a = c ∧ b = d := by
  have raw : ((a, b) : Tokens) = (c, d) := congrArg Multiplicative.toAdd equal
  exact ⟨congrArg Prod.fst raw, congrArg Prod.snd raw⟩

/-- Every morphism of the context category is a token count. -/
theorem tok_surjective (m : (SingleObj.star (Multiplicative Tokens)) ⟶
    (SingleObj.star (Multiplicative Tokens))) :
    ∃ a b : ℕ, m = tok a b :=
  ⟨(Multiplicative.toAdd m).1, (Multiplicative.toAdd m).2, rfl⟩

/-- The redex the first completion exposes: a pair on the first channel. -/
def redexFirst : (SingleObj.star (Multiplicative Tokens)) ⟶
    (SingleObj.star (Multiplicative Tokens)) := tok 2 0

/-- And the one the second exposes, on the other channel. -/
def redexSecond : (SingleObj.star (Multiplicative Tokens)) ⟶
    (SingleObj.star (Multiplicative Tokens)) := tok 0 2

/-- The first completion bounds the source against its own redex. -/
theorem squareFirst : tok 1 0 ≫ tok 1 0 = redexFirst ≫ tok 0 0 := by
  simp [redexFirst, tok_comp]

/-- The second completion bounds it against the other redex, with the source's
own token as the reaction context. -/
theorem squareSecond : tok 1 0 ≫ tok 0 2 = redexSecond ≫ tok 1 0 := by
  simp [redexSecond, tok_comp]

/-- **The first completion is least for its redex.**  Every candidate collapses:
the reaction context is empty, so nothing can be cut away. -/
theorem first_isIdemPushout :
    IsIdemPushout (tok 1 0) redexFirst (tok 1 0) (tok 0 0) squareFirst := by
  intro d
  obtain ⟨dx, dy, hdown⟩ := tok_surjective d.down
  obtain ⟨lx, ly, hinl⟩ := tok_surjective d.inl
  obtain ⟨rx, ry, hinr⟩ := tok_surjective d.inr
  have rightFac := d.fac_right
  have leftFac := d.fac_left
  rw [hinr, hdown, tok_comp] at rightFac
  rw [hinl, hdown, tok_comp] at leftFac
  obtain ⟨rightFirst, rightSecond⟩ := tok_injective rightFac
  obtain ⟨leftFirst, leftSecond⟩ := tok_injective leftFac
  have downFirst : dx = 0 := by omega
  have downSecond : dy = 0 := by omega
  have inlFirst : lx = 1 := by omega
  have inlSecond : ly = 0 := by omega
  have inrFirst : rx = 0 := by omega
  have inrSecond : ry = 0 := by omega
  subst downFirst; subst downSecond; subst inlFirst; subst inlSecond
  subst inrFirst; subst inrSecond
  refine ⟨tok 0 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hinl]; exact tok_comp 1 0 0 0
  · rw [hinr]; exact tok_comp 0 0 0 0
  · rw [hdown, tok_comp]; exact tok_id
  · rintro k ⟨mediatesLeft, -, -⟩
    obtain ⟨kx, ky, hk⟩ := tok_surjective k
    rw [hk, hinl] at mediatesLeft
    have expanded : tok (1 + kx) (0 + ky) = tok 1 0 := by
      rw [← tok_comp]; exact mediatesLeft
    obtain ⟨kFirst, kSecond⟩ := tok_injective expanded
    have kxZero : kx = 0 := by omega
    have kyZero : ky = 0 := by omega
    rw [hk, kxZero, kyZero]

/-- **And so is the second, for its own redex.**  Two least labels, one for each
redex, where the absolute notion had none. -/
theorem second_isIdemPushout :
    IsIdemPushout (tok 1 0) redexSecond (tok 0 2) (tok 1 0) squareSecond := by
  intro d
  obtain ⟨dx, dy, hdown⟩ := tok_surjective d.down
  obtain ⟨lx, ly, hinl⟩ := tok_surjective d.inl
  obtain ⟨rx, ry, hinr⟩ := tok_surjective d.inr
  have rightFac := d.fac_right
  have leftFac := d.fac_left
  rw [hinr, hdown, tok_comp] at rightFac
  rw [hinl, hdown, tok_comp] at leftFac
  obtain ⟨rightFirst, rightSecond⟩ := tok_injective rightFac
  obtain ⟨leftFirst, leftSecond⟩ := tok_injective leftFac
  have downFirst : dx = 0 := by omega
  have downSecond : dy = 0 := by omega
  have inlFirst : lx = 0 := by omega
  have inlSecond : ly = 2 := by omega
  have inrFirst : rx = 1 := by omega
  have inrSecond : ry = 0 := by omega
  subst downFirst; subst downSecond; subst inlFirst; subst inlSecond
  subst inrFirst; subst inrSecond
  refine ⟨tok 0 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hinl]; exact tok_comp 0 2 0 0
  · rw [hinr]; exact tok_comp 1 0 0 0
  · rw [hdown, tok_comp]; exact tok_id
  · rintro k ⟨mediatesLeft, -, -⟩
    obtain ⟨kx, ky, hk⟩ := tok_surjective k
    rw [hk, hinl] at mediatesLeft
    have expanded : tok (0 + kx) (2 + ky) = tok 0 2 := by
      rw [← tok_comp]; exact mediatesLeft
    obtain ⟨kFirst, kSecond⟩ := tok_injective expanded
    have kxZero : kx = 0 := by omega
    have kyZero : ky = 0 := by omega
    rw [hk, kxZero, kyZero]

/-! ### And relative pushouts exist here

Existence is what turns "the label is least for its redex" from a property some
bounds happen to have into something a transition system can rely on.  In this
theory it holds, and the construction is the obvious one: the largest part two
bounds share is their componentwise minimum, and cutting it away is least. -/

/-- **The candidate that cuts away what two bounds share.**  The shared part is
the componentwise minimum; removing it is the reduction a relative pushout
performs, and both directions of the characterisation below use it. -/
def cutCandidate (a b c d p q r s : ℕ) (wFirst : a + p = c + r) (wSecond : b + q = d + s) :
    Candidate (tok a b) (tok c d) (tok p q) (tok r s) where
  apex := SingleObj.star (Multiplicative Tokens)
  inl := tok (p - min p r) (q - min q s)
  inr := tok (r - min p r) (s - min q s)
  down := tok (min p r) (min q s)
  comm := by
    rw [tok_comp, tok_comp]
    have first : a + (p - min p r) = c + (r - min p r) := by omega
    have second : b + (q - min q s) = d + (s - min q s) := by omega
    rw [first, second]
  fac_left := by
    rw [tok_comp]
    have first : p - min p r + min p r = p := by omega
    have second : q - min q s + min q s = q := by omega
    rw [first, second]
  fac_right := by
    rw [tok_comp]
    have first : r - min p r + min p r = r := by omega
    have second : s - min q s + min q s = s := by omega
    rw [first, second]

/-- **The canary has relative pushouts**, for every span and every bound. -/
theorem twoChannel_hasRelativePushouts (a b c d : ℕ) :
    HasRelativePushouts (tok a b) (tok c d) := by
  intro apex h i w
  obtain ⟨p, q, hEq⟩ := tok_surjective h
  obtain ⟨r, s, iEq⟩ := tok_surjective i
  subst hEq
  subst iEq
  rw [tok_comp, tok_comp] at w
  obtain ⟨wFirst, wSecond⟩ := tok_injective w
  refine ⟨cutCandidate a b c d p q r s wFirst wSecond, ?_⟩
  · intro candidate
    obtain ⟨u, v, inlEq⟩ := tok_surjective candidate.inl
    obtain ⟨x, y, inrEq⟩ := tok_surjective candidate.inr
    obtain ⟨m, n, downEq⟩ := tok_surjective candidate.down
    have leftFac := candidate.fac_left
    have rightFac := candidate.fac_right
    rw [inlEq, downEq, tok_comp] at leftFac
    rw [inrEq, downEq, tok_comp] at rightFac
    obtain ⟨leftFirst, leftSecond⟩ := tok_injective leftFac
    obtain ⟨rightFirst, rightSecond⟩ := tok_injective rightFac
    refine ⟨tok (min p r - m) (min q s - n), ⟨?_, ?_, ?_⟩, ?_⟩
    · show tok (p - min p r) (q - min q s) ≫ tok (min p r - m) (min q s - n) =
        candidate.inl
      rw [tok_comp, inlEq]
      have first : p - min p r + (min p r - m) = u := by omega
      have second : q - min q s + (min q s - n) = v := by omega
      rw [first, second]
    · show tok (r - min p r) (s - min q s) ≫ tok (min p r - m) (min q s - n) =
        candidate.inr
      rw [tok_comp, inrEq]
      have first : r - min p r + (min p r - m) = x := by omega
      have second : s - min q s + (min q s - n) = y := by omega
      rw [first, second]
    · show tok (min p r - m) (min q s - n) ≫ candidate.down =
        tok (min p r) (min q s)
      rw [downEq, tok_comp]
      have first : min p r - m + m = min p r := by omega
      have second : min q s - n + n = min q s := by omega
      rw [first, second]
    · rintro mediator ⟨mediatesLeft, -, -⟩
      obtain ⟨e, g, mediatorEq⟩ := tok_surjective mediator
      have restated : tok (p - min p r) (q - min q s) ≫ tok e g = tok u v := by
        rw [← mediatorEq, ← inlEq]
        exact mediatesLeft
      rw [tok_comp] at restated
      obtain ⟨mediatesFirst, mediatesSecond⟩ := tok_injective restated
      rw [mediatorEq]
      have first : e = min p r - m := by omega
      have second : g = min q s - n := by omega
      rw [first, second]

/-- **So every bound here reduces to an idem pushout**, by the general theorem
rather than by exhibiting one — which is what existence is for. -/
theorem twoChannel_every_bound_reduces (a b c d : ℕ) {apex : Ctx}
    (h : (SingleObj.star (Multiplicative Tokens)) ⟶ apex)
    (i : (SingleObj.star (Multiplicative Tokens)) ⟶ apex)
    (w : tok a b ≫ h = tok c d ≫ i) :
    ∃ candidate : Candidate (tok a b) (tok c d) h i,
      IsIdemPushout (tok a b) (tok c d) candidate.inl candidate.inr candidate.comm :=
  exists_idemPushout_below (twoChannel_hasRelativePushouts a b c d) w

/-! ### Leastness, characterised — and pasting, instantiated

In this theory a bound can be cut down exactly by the part its two legs share.
So it is least exactly when they share nothing, which turns every question about
idem pushouts here into arithmetic. -/

/-- **A bound with nothing in common is an idem pushout.** -/
theorem isIdemPushout_tok (a b c d p q r s : ℕ)
    (w : tok a b ≫ tok p q = tok c d ≫ tok r s)
    (sharedFirst : min p r = 0) (sharedSecond : min q s = 0) :
    IsIdemPushout (tok a b) (tok c d) (tok p q) (tok r s) w := by
  intro candidate
  obtain ⟨u, v, inlEq⟩ := tok_surjective candidate.inl
  obtain ⟨x, y, inrEq⟩ := tok_surjective candidate.inr
  obtain ⟨m, n, downEq⟩ := tok_surjective candidate.down
  have leftFac := candidate.fac_left
  have rightFac := candidate.fac_right
  rw [inlEq, downEq, tok_comp] at leftFac
  rw [inrEq, downEq, tok_comp] at rightFac
  obtain ⟨leftFirst, leftSecond⟩ := tok_injective leftFac
  obtain ⟨rightFirst, rightSecond⟩ := tok_injective rightFac
  refine ⟨tok 0 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · show tok p q ≫ tok 0 0 = candidate.inl
    rw [tok_comp, inlEq]
    have first : p + 0 = u := by omega
    have second : q + 0 = v := by omega
    rw [first, second]
  · show tok r s ≫ tok 0 0 = candidate.inr
    rw [tok_comp, inrEq]
    have first : r + 0 = x := by omega
    have second : s + 0 = y := by omega
    rw [first, second]
  · show tok 0 0 ≫ candidate.down = tok 0 0
    rw [downEq, tok_comp]
    have first : 0 + m = 0 := by omega
    have second : 0 + n = 0 := by omega
    rw [first, second]
  · rintro mediator ⟨mediatesLeft, -, -⟩
    obtain ⟨e, g, mediatorEq⟩ := tok_surjective mediator
    have restated : tok p q ≫ tok e g = tok u v := by
      rw [← mediatorEq, ← inlEq]
      exact mediatesLeft
    rw [tok_comp] at restated
    obtain ⟨mediatesFirst, mediatesSecond⟩ := tok_injective restated
    rw [mediatorEq]
    have first : e = 0 := by omega
    have second : g = 0 := by omega
    rw [first, second]

/-- **And conversely: an idem pushout has nothing in common.**  So leastness here
is exactly the arithmetic condition, in both directions. -/
theorem min_eq_zero_of_isIdemPushout {a b c d p q r s : ℕ}
    (w : tok a b ≫ tok p q = tok c d ≫ tok r s)
    (ipo : IsIdemPushout (tok a b) (tok c d) (tok p q) (tok r s) w) :
    min p r = 0 ∧ min q s = 0 := by
  rw [tok_comp, tok_comp] at w
  obtain ⟨wFirst, wSecond⟩ := tok_injective w
  obtain ⟨mediator, ⟨mediatesLeft, -, -⟩, -⟩ := ipo (cutCandidate a b c d p q r s wFirst wSecond)
  obtain ⟨e, g, mediatorEq⟩ := tok_surjective mediator
  have restated : tok p q ≫ tok e g = tok (p - min p r) (q - min q s) := by
    rw [← mediatorEq]
    exact mediatesLeft
  rw [tok_comp] at restated
  obtain ⟨first, second⟩ := tok_injective restated
  exact ⟨by omega, by omega⟩

/-- **Leastness, characterised.** -/
theorem isIdemPushout_tok_iff (a b c d p q r s : ℕ)
    (w : tok a b ≫ tok p q = tok c d ≫ tok r s) :
    IsIdemPushout (tok a b) (tok c d) (tok p q) (tok r s) w ↔
      (min p r = 0 ∧ min q s = 0) :=
  ⟨min_eq_zero_of_isIdemPushout w,
    fun shared => isIdemPushout_tok a b c d p q r s w shared.1 shared.2⟩

/-- Enlarging the source by a token on the other channel: the outer square that
places the first completion in a wider context. -/
theorem outer_isIdemPushout :
    IsIdemPushout (tok 0 1) (tok 1 0) (tok 1 0) (tok 0 1)
      (by rw [tok_comp, tok_comp]) :=
  isIdemPushout_tok 0 1 1 0 1 0 0 1 (by rw [tok_comp, tok_comp]) (by decide) (by decide)

/-- **Pasting, instantiated.**  The first completion is least for its redex at
the source; placing the source in a context that adds an inert token on the
other channel is least for that label; so the same completion is least for the
same redex at the enlarged source.  Enlarging the context by material the redex
does not touch does not move the label. -/
theorem paste_instance :
    IsIdemPushout (tok 1 0 ≫ tok 0 1) redexFirst (tok 1 0) (tok 0 0 ≫ tok 0 1)
      (by rw [Category.assoc, ← Category.assoc, redexFirst]; simp [tok_comp]) :=
  isIdemPushout_paste (tok 1 0) redexFirst (tok 1 0) (tok 0 0) (tok 0 1) (tok 1 0) (tok 0 1)
    squareFirst (by rw [tok_comp, tok_comp])
    (twoChannel_hasRelativePushouts 1 0 2 0)
    first_isIdemPushout outer_isIdemPushout

/-- And the enlarged source really is enlarged: it carries a token the original
did not. -/
theorem paste_instance_enlarges : tok 1 0 ≫ tok 0 1 = tok 1 1 := by
  rw [tok_comp]

/-- **The moral, as one statement.**  The two redexes each have a least
completion, and there is no completion least for both.  A context-labelled
transition relation that demands the second gets no labels here at all; one that
demands the first gets two, and they are the two interactions the term can take
part in. -/
theorem two_relative_minima_no_absolute_minimum :
    IsIdemPushout (tok 1 0) redexFirst (tok 1 0) (tok 0 0) squareFirst ∧
      IsIdemPushout (tok 1 0) redexSecond (tok 0 2) (tok 1 0) squareSecond ∧
        ¬ ∃ context : Tokens, twoChannelRules.IsLeastEnabler context source () :=
  ⟨first_isIdemPushout, second_isIdemPushout, no_least_enabler⟩

/-! ## The congruence, met

`RedexRelativeCongruence` proves context-labelled bisimilarity a congruence from
relative-pushout existence, for every context and with no class of admissible
contexts.  Here that hypothesis is discharged, so the congruence holds in a real
theory rather than under an assumption. -/

namespace Congruence

open Mettapedia.GSLT.RedexRelativeCongruence

/-- Existence, for every span of this theory. -/
theorem hasRelativePushouts_all
    (first second : Obj (Multiplicative Tokens) ⟶ Obj (Multiplicative Tokens)) :
    HasRelativePushouts first second := by
  obtain ⟨a, b, firstEq⟩ := tok_surjective first
  obtain ⟨c, d, secondEq⟩ := tok_surjective second
  subst firstEq
  subst secondEq
  exact twoChannel_hasRelativePushouts a b c d

/-- **So the congruence holds here.**  Bisimilar agents stay bisimilar in every
context. -/
theorem congruence (rules : ReactionRule (Obj (Multiplicative Tokens)) → Prop)
    {left right : Obj (Multiplicative Tokens) ⟶ Obj (Multiplicative Tokens)}
    (bisim : IPOBisimilar rules left right)
    (context : Obj (Multiplicative Tokens) ⟶ Obj (Multiplicative Tokens)) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => hasRelativePushouts_all agent rule.redex) bisim context

/-! ### And the transition relation is inhabited

A congruence for a relation with no transitions would say nothing.  Here is one. -/

/-- The rule that consumes a pair on the first channel. -/
def pairRule : ReactionRule (Obj (Multiplicative Tokens)) where
  codomain := Obj (Multiplicative Tokens)
  redex := tok 2 0
  reactum := tok 0 0

/-- The one-rule theory. -/
def oneRule : ReactionRule (Obj (Multiplicative Tokens)) → Prop := fun rule => rule = pairRule

/-- **A labelled transition.**  One token on the first channel steps under the
label that supplies the second — and the label is least for that redex, by
`first_isIdemPushout`. -/
theorem token_steps :
    ActIPO oneRule (tok 1 0) (tok 1 0) (tok 0 0 ≫ tok 0 0) :=
  ⟨pairRule, rfl, tok 0 0, squareFirst, first_isIdemPushout, rfl⟩

/-- **Every transition of a second-channel agent, characterised.**  It steps
only under the label that supplies the missing pair, and only to itself: the
leastness condition forces both. -/
theorem act_token_iff (n : ℕ)
    (label target : Obj (Multiplicative Tokens) ⟶ Obj (Multiplicative Tokens)) :
    ActIPO oneRule label (tok 0 n) target ↔ (label = tok 2 0 ∧ target = tok 0 n) := by
  constructor
  · rintro ⟨rule, rfl, reaction, square, ipo, targetEq⟩
    obtain ⟨e, g, rfl⟩ := tok_surjective label
    obtain ⟨x, y, rfl⟩ := tok_surjective reaction
    obtain ⟨sharedFirst, sharedSecond⟩ := min_eq_zero_of_isIdemPushout square ipo
    have squareCoords := square
    simp only [pairRule, tok_comp] at squareCoords
    obtain ⟨first, second⟩ := tok_injective squareCoords
    have eIs : e = 2 := by omega
    have gIs : g = 0 := by omega
    have xIs : x = 0 := by omega
    have yIs : y = n := by omega
    subst eIs; subst gIs; subst xIs
    refine ⟨rfl, ?_⟩
    rw [targetEq]
    simp only [pairRule, tok_comp]
    rw [yIs]
    simp
  · rintro ⟨rfl, rfl⟩
    refine ⟨pairRule, rfl, tok 0 n, ?_, ?_, ?_⟩
    · show tok 0 n ≫ tok 2 0 = tok 2 0 ≫ tok 0 n
      rw [tok_comp, tok_comp]
      simp
    · exact isIdemPushout_tok 0 n 2 0 2 0 0 n (by rw [tok_comp, tok_comp]; simp)
        (by decide) (by simp)
    · show tok 0 n = tok 0 0 ≫ tok 0 n
      rw [tok_comp]
      simp

/-- **Two distinct agents, bisimilar.**  Each has exactly one transition, under
the same label, to itself — so the relation pairing them is a bisimulation
although they are different agents. -/
theorem distinct_bisimilar : IPOBisimilar oneRule (tok 0 1) (tok 0 2) := by
  refine ⟨fun _ left right => left = tok 0 1 ∧ right = tok 0 2, ?_, rfl, rfl⟩
  rintro _ left right ⟨rfl, rfl⟩
  constructor
  · intro _ label next step
    obtain ⟨labelEq, nextEq⟩ := (act_token_iff 1 label next).mp step
    exact ⟨tok 0 2, (act_token_iff 2 label (tok 0 2)).mpr ⟨labelEq, rfl⟩, nextEq, rfl⟩
  · intro _ label next step
    obtain ⟨labelEq, nextEq⟩ := (act_token_iff 2 label next).mp step
    exact ⟨tok 0 1, (act_token_iff 1 label (tok 0 1)).mpr ⟨labelEq, rfl⟩, rfl, nextEq⟩

theorem distinct_agents : tok 0 1 ≠ tok 0 2 := by
  intro equal
  obtain ⟨-, second⟩ := tok_injective equal
  omega

/-- **The congruence, instantiated at a pair that is not reflexivity.**  Two
different agents, bisimilar, stay bisimilar in every context — with the
existence hypothesis discharged rather than assumed. -/
theorem congruence_instance
    (context : Obj (Multiplicative Tokens) ⟶ Obj (Multiplicative Tokens)) :
    IPOBisimilar oneRule (tok 0 1 ≫ context) (tok 0 2 ≫ context) :=
  congruence oneRule distinct_bisimilar context

/-- Behavioral quotienting really identifies distinct agents. -/
theorem distinct_agents_same_class :
    toClass oneRule (tok 0 1) = toClass oneRule (tok 0 2) ∧ tok 0 1 ≠ tok 0 2 :=
  ⟨(class_eq_iff oneRule _ _).mpr distinct_bisimilar, distinct_agents⟩

/-- The quotient is not constant: the label that completes a single token
cannot complete the empty agent. -/
theorem active_and_idle_classes_distinct :
    toClass oneRule (tok 1 0) ≠ toClass oneRule (tok 0 0) := by
  intro equal
  have bisim := (class_eq_iff oneRule _ _).mp equal
  obtain ⟨matched, step, -⟩ := ipoBisimilar_forward bisim token_steps
  have labelEqual := ((act_token_iff 0 (tok 1 0) matched).mp step).1
  have coordinates := (tok_injective labelEqual).1
  omega

/-- The class action is not an identity action: adjoining a token changes
the empty agent's behavioral class, with RPO existence discharged. -/
theorem context_map_changes_class :
    contextClassMap
        (fun _ agent rule _ => hasRelativePushouts_all agent rule.redex)
        (tok 1 0) (toClass oneRule (tok 0 0)) ≠ toClass oneRule (tok 0 0) := by
  rw [contextClassMap_toClass]
  have composed : tok 0 0 ≫ tok 1 0 = tok 1 0 := by rw [tok_comp]
  rw [composed]
  exact active_and_idle_classes_distinct

#print axioms distinct_agents_same_class
#print axioms active_and_idle_classes_distinct
#print axioms context_map_changes_class

end Congruence

end Mettapedia.GSLT.RedexRelativeEnabling
