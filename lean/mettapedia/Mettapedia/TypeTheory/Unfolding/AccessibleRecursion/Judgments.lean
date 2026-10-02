import Mettapedia.TypeTheory.Unfolding.ConversionTransport
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Syntax

/-!
# Proposition codes with an accessibility recursor: the two variants

Three judgment forms share one data context `Γ` and one ordered list of
hypotheses:

* `holds Γ hyps φ`: the code `φ` is derivable;
* `conv Γ hyps T t u`: `t` and `u` are definitionally equal at `T`;
* `equal Γ hyps T t u`: `t` and `u` are propositionally equal at `T`.

Derivability is Curry style: proofs are not terms, so two derivations of one
code are never compared, and nothing computes on them.

**Shared rules** (`SharedRule`): hypotheses; introduction and elimination of
implication and of every quantifier symbol; the *conversion rule*, retyping a
derivable code along definitional equality; propositional equality, which
contains definitional equality and is symmetric, transitive, a congruence
for application and, under binders, for abstraction (the extensionality of
functions); *transport* of a derivable code along propositional equality; and
the *propositional unfolding* of the recursor,
`recTerm R F a = unfoldTerm R F a`, whenever `accCode R a` and `respCode R F`
are derivable.

**Carved conversion** (`ConvRule`): beta conversion of the one-ground calculus,
closed under symmetry, transitivity and the term constructors.

**Strong-only conversion** (`UnfoldRule`): the *definitional unfolding*
`recTerm R F a ≡ unfoldTerm R F a`, under the same two derivable premises.

The strong variant adds `UnfoldRule` to the carved one.  Reading every
definitional equality as the corresponding propositional equality
(`Judgment.reflect`) reflects each rule family into the carved variant:
the conversion rule becomes a transport, carved conversion becomes
propositional equality, and definitional unfolding becomes propositional
unfolding.  Hence every strong derivation of a code is a carved derivation
of the same code (`strong_holds_iff`), and every strong definitional equality
is a carved propositional equality (`conv_reflects_to_equal`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.Logic
open Mettapedia.TypeTheory.Unfolding
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

variable (A P : Ty)

/-- Judgments over a data context and an ordered list of hypotheses. -/
inductive Judgment : Type
  | holds (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (goal : Tm A P Γ prop)
  | conv (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (left right : Tm A P Γ T)
  | equal (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (left right : Tm A P Γ T)

variable {A P}

/-- Weakening of a hypothesis list by one data variable. -/
def wkHyps {Γ : List Ty} {B : Ty} (hyps : List (Tm A P Γ prop)) : List (Tm A P (B :: Γ) prop) :=
  hyps.map wk

/-- The rules of both variants.  The flag `witness` guards the propositional
unfolding rule, so that the carved variant can be compared with its fragment
without it. -/
inductive SharedRule (witness : Bool) : List (Judgment A P) → Judgment A P → Prop
  | hyp {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {goal : Tm A P Γ prop} :
      goal ∈ hyps → SharedRule witness [] (.holds Γ hyps goal)
  | impIntro {Γ : List Ty} {hyps : List (Tm A P Γ prop)} (premise conclusion : Tm A P Γ prop) :
      SharedRule witness [.holds Γ (premise :: hyps) conclusion]
        (.holds Γ hyps (imp premise conclusion))
  | impElim {Γ : List Ty} {hyps : List (Tm A P Γ prop)} (premise conclusion : Tm A P Γ prop) :
      SharedRule witness [.holds Γ hyps (imp premise conclusion), .holds Γ hyps premise]
        (.holds Γ hyps conclusion)
  | allIntro {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {σ : Ty}
      (quantifier : Var (signature A P) (quantTy σ)) (body : Tm A P Γ (.arr σ prop)) :
      SharedRule witness [.holds (σ :: Γ) (wkHyps hyps) (.app (wk body) (.var .zero))]
        (.holds Γ hyps (all quantifier body))
  | allElim {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {σ : Ty}
      (quantifier : Var (signature A P) (quantTy σ)) (body : Tm A P Γ (.arr σ prop))
      (witnessTerm : Tm A P Γ σ) :
      SharedRule witness [.holds Γ hyps (all quantifier body)]
        (.holds Γ hyps (.app body witnessTerm))
  | convert {Γ : List Ty} {hyps : List (Tm A P Γ prop)} (source target : Tm A P Γ prop) :
      SharedRule witness [.holds Γ hyps source, .conv Γ hyps prop source target]
        (.holds Γ hyps target)
  | equalOfConv {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty} (left right : Tm A P Γ T) :
      SharedRule witness [.conv Γ hyps T left right] (.equal Γ hyps T left right)
  | equalSymm {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty} (left right : Tm A P Γ T) :
      SharedRule witness [.equal Γ hyps T left right] (.equal Γ hyps T right left)
  | equalTrans {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
      (left middle right : Tm A P Γ T) :
      SharedRule witness [.equal Γ hyps T left middle, .equal Γ hyps T middle right]
        (.equal Γ hyps T left right)
  | equalApp {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T T' : Ty}
      (function function' : Tm A P Γ (.arr T T')) (argument argument' : Tm A P Γ T) :
      SharedRule witness
        [.equal Γ hyps (.arr T T') function function', .equal Γ hyps T argument argument']
        (.equal Γ hyps T' (.app function argument) (.app function' argument'))
  | equalLam {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T T' : Ty}
      (body body' : Tm A P (T :: Γ) T') :
      SharedRule witness [.equal (T :: Γ) (wkHyps hyps) T' body body']
        (.equal Γ hyps (.arr T T') (.lam body) (.lam body'))
  | transport {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
      (motive : Tm A P (T :: Γ) prop) (left right : Tm A P Γ T) :
      SharedRule witness [.equal Γ hyps T left right, .holds Γ hyps (inst motive left)]
        (.holds Γ hyps (inst motive right))
  | unfoldEqual {Γ : List Ty} {hyps : List (Tm A P Γ prop)} (R : Tm A P Γ (relTy A))
      (F : Tm A P Γ (stepTy A P)) (point : Tm A P Γ A) :
      witness = true →
      SharedRule witness [.holds Γ hyps (accCode R point), .holds Γ hyps (respCode R F)]
        (.equal Γ hyps P (recTerm R F point) (unfoldTerm R F point))

/-- Definitional equality of the carved variant: beta conversion of the
one-ground calculus, closed under symmetry, transitivity and the term
constructors. -/
inductive ConvRule : List (Judgment A P) → Judgment A P → Prop
  | beta {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty} (left right : Tm A P Γ T) :
      BetaConv left right → ConvRule [] (.conv Γ hyps T left right)
  | symm {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty} (left right : Tm A P Γ T) :
      ConvRule [.conv Γ hyps T left right] (.conv Γ hyps T right left)
  | trans {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty} (left middle right : Tm A P Γ T) :
      ConvRule [.conv Γ hyps T left middle, .conv Γ hyps T middle right]
        (.conv Γ hyps T left right)
  | app {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T T' : Ty}
      (function function' : Tm A P Γ (.arr T T')) (argument argument' : Tm A P Γ T) :
      ConvRule [.conv Γ hyps (.arr T T') function function', .conv Γ hyps T argument argument']
        (.conv Γ hyps T' (.app function argument) (.app function' argument'))
  | lam {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T T' : Ty} (body body' : Tm A P (T :: Γ) T') :
      ConvRule [.conv (T :: Γ) (wkHyps hyps) T' body body']
        (.conv Γ hyps (.arr T T') (.lam body) (.lam body'))

/-- The definitional unfolding of the recursor, present only in the strong
variant.  Its premises are those of the propositional unfolding. -/
inductive UnfoldRule : List (Judgment A P) → Judgment A P → Prop
  | unfold {Γ : List Ty} {hyps : List (Tm A P Γ prop)} (R : Tm A P Γ (relTy A))
      (F : Tm A P Γ (stepTy A P)) (point : Tm A P Γ A) :
      UnfoldRule [.holds Γ hyps (accCode R point), .holds Γ hyps (respCode R F)]
        (.conv Γ hyps P (recTerm R F point) (unfoldTerm R F point))

/-- Read a definitional equality as the corresponding propositional equality;
read every other judgment as itself. -/
def Judgment.reflect : Judgment A P → Judgment A P
  | .holds Γ hyps goal => .holds Γ hyps goal
  | .conv Γ hyps T left right => .equal Γ hyps T left right
  | .equal Γ hyps T left right => .equal Γ hyps T left right

variable (A P)

/-- The conversion split of the calculus. -/
def unfoldingSplit : ConversionSplit (Judgment A P) where
  shared := SharedRule true
  carvedConversion := ConvRule
  strongConversion := UnfoldRule
  reflect := Judgment.reflect

/-- Derivability in the carved variant: propositional unfolding only. -/
abbrev Carved (judgment : Judgment A P) : Prop := Derives (unfoldingSplit A P).carved judgment

/-- Derivability in the strong variant: definitional unfolding as well. -/
abbrev Strong (judgment : Judgment A P) : Prop := Derives (unfoldingSplit A P).strong judgment

variable {A P}

/-! ## The three obligations -/

/-- The shared rules are reflected: the conversion rule becomes a transport
along the identity motive, and every other shared rule is read as itself. -/
theorem shared_reflects : (unfoldingSplit A P).Reflects (SharedRule true) := by
  intro premises conclusion rule subderivations
  cases rule with
  | hyp member => exact derives₀ (Or.inl (SharedRule.hyp member))
  | impIntro premise conclusion' =>
      exact derives₁ (Or.inl (SharedRule.impIntro premise conclusion')) (subderivations _ mem₀)
  | impElim premise conclusion' =>
      exact derives₂ (Or.inl (SharedRule.impElim premise conclusion'))
        (subderivations _ mem₀) (subderivations _ mem₁)
  | allIntro quantifier body =>
      exact derives₁ (Or.inl (SharedRule.allIntro quantifier body)) (subderivations _ mem₀)
  | allElim quantifier body witnessTerm =>
      exact derives₁ (Or.inl (SharedRule.allElim quantifier body witnessTerm))
        (subderivations _ mem₀)
  | convert source target =>
      exact derives₂ (Or.inl (SharedRule.transport (.var .zero) source target))
        (subderivations _ mem₁) (subderivations _ mem₀)
  | equalOfConv left right => exact subderivations (.conv _ _ _ left right) mem₀
  | equalSymm left right =>
      exact derives₁ (Or.inl (SharedRule.equalSymm left right)) (subderivations _ mem₀)
  | equalTrans left middle right =>
      exact derives₂ (Or.inl (SharedRule.equalTrans left middle right))
        (subderivations _ mem₀) (subderivations _ mem₁)
  | equalApp function function' argument argument' =>
      exact derives₂ (Or.inl (SharedRule.equalApp function function' argument argument'))
        (subderivations _ mem₀) (subderivations _ mem₁)
  | equalLam body body' =>
      exact derives₁ (Or.inl (SharedRule.equalLam body body')) (subderivations _ mem₀)
  | transport motive left right =>
      exact derives₂ (Or.inl (SharedRule.transport motive left right))
        (subderivations _ mem₀) (subderivations _ mem₁)
  | unfoldEqual R F point witness =>
      exact derives₂ (Or.inl (SharedRule.unfoldEqual R F point witness))
        (subderivations _ mem₀) (subderivations _ mem₁)

/-- Carved conversion is reflected: definitional equality implies
propositional equality, and each closure rule has its propositional
counterpart. -/
theorem conv_reflects : (unfoldingSplit A P).Reflects ConvRule := by
  intro premises conclusion rule subderivations
  cases rule with
  | beta left right convertible =>
      exact derives₁ (Or.inl (SharedRule.equalOfConv left right))
        (derives₀ (Or.inr (ConvRule.beta left right convertible)))
  | symm left right =>
      exact derives₁ (Or.inl (SharedRule.equalSymm left right)) (subderivations _ mem₀)
  | trans left middle right =>
      exact derives₂ (Or.inl (SharedRule.equalTrans left middle right))
        (subderivations _ mem₀) (subderivations _ mem₁)
  | app function function' argument argument' =>
      exact derives₂ (Or.inl (SharedRule.equalApp function function' argument argument'))
        (subderivations _ mem₀) (subderivations _ mem₁)
  | lam body body' =>
      exact derives₁ (Or.inl (SharedRule.equalLam body body')) (subderivations _ mem₀)

/-- Definitional unfolding is reflected by propositional unfolding. -/
theorem unfold_reflects : (unfoldingSplit A P).Reflects UnfoldRule := by
  intro premises conclusion rule subderivations
  cases rule with
  | unfold R F point =>
      exact derives₂ (Or.inl (SharedRule.unfoldEqual R F point rfl))
        (subderivations _ mem₀) (subderivations _ mem₁)

/-! ## Reflection for the calculus -/

/-- **Reflection.**  Every strong derivation yields a carved derivation of the
read judgment. -/
theorem reflection {judgment : Judgment A P} (derivation : Strong A P judgment) :
    Carved A P judgment.reflect :=
  (unfoldingSplit A P).reflection shared_reflects conv_reflects unfold_reflects derivation

/-- A code is derivable with definitional unfolding exactly when it is
derivable with propositional unfolding. -/
theorem strong_holds_iff {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {goal : Tm A P Γ prop} :
    Strong A P (.holds Γ hyps goal) ↔ Carved A P (.holds Γ hyps goal) :=
  (unfoldingSplit A P).strong_iff_carved shared_reflects conv_reflects unfold_reflects rfl

/-- The two variants have the same propositional equalities. -/
theorem strong_equal_iff {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
    {left right : Tm A P Γ T} :
    Strong A P (.equal Γ hyps T left right) ↔ Carved A P (.equal Γ hyps T left right) :=
  (unfoldingSplit A P).strong_iff_carved shared_reflects conv_reflects unfold_reflects rfl

/-- Every strong definitional equality is a carved propositional equality. -/
theorem conv_reflects_to_equal {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
    {left right : Tm A P Γ T} (derivation : Strong A P (.conv Γ hyps T left right)) :
    Carved A P (.equal Γ hyps T left right) :=
  reflection derivation

/-- The carved variant is a restriction of the strong one. -/
theorem carved_restricts {judgment : Judgment A P} (derivation : Carved A P judgment) :
    Strong A P judgment :=
  (unfoldingSplit A P).restriction derivation

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
