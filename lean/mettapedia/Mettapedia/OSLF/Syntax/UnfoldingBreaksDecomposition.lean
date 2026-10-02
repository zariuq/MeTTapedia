import Mettapedia.OSLF.Syntax.EquationalQuotient
import Mettapedia.OSLF.Syntax.NormalFormStrength

/-!
# An unfolding law destroys every numeric decomposition invariant

The repair of unique decomposition proved elsewhere rests on the multiplicities
of the primes being a *complete* invariant of the equational theory: two
processes with the same counts are congruent, and congruent processes have the
same counts.  That is what makes the prime support of a predicate meaningful, and
it holds when the theory is associativity, commutativity and a unit.

It is tempting to conclude that the quotient is always the free commutative
monoid on the primes, so that decomposition is multiset equality and nothing
harder is ever needed.  That conclusion is false, and the source says so: a
presentation may take replication as a primitive and put its unfolding law in the
equational theory, in which case a term and that term beside a copy of its body
are equal, and a term with replication has infinitely many decompositions.

This module makes the obstruction exact.  With an unfolding law present, the
class of a single replicated process contains, for every natural number, a
process with that many copies of the body.  So no function to a numeric
invariant -- no count, no multiplicity vector, no multiset of primes -- can be
constant on classes, and the quotient is not free.  Unique decomposition in such
a presentation is the hard theorem about processes, not the easy one about
multisets.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

namespace Unfolding

inductive RSrt where
  | proc
  deriving DecidableEq

/-- A unit, parallel composition, an inert token, and replication. -/
inductive ROp : RSrt → Type where
  | nul : ROp RSrt.proc
  | par : ROp RSrt.proc
  | tick : ROp RSrt.proc
  | bang : ROp RSrt.proc

abbrev rsig : Signature where
  Srt := RSrt
  Op := ROp
  arity := fun {_} o => match o with
    | .nul => []
    | .par => [([], RSrt.proc), ([], RSrt.proc)]
    | .tick => []
    | .bang => [([], RSrt.proc)]

abbrev noMetas : List (MetaArity rsig) := []

abbrev eqSig : Signature := withMetas rsig noMetas

/-- **The unfolding law**: `!X = !X | X`.  Taking this into the equational theory
is exactly the choice the source describes, and exactly the choice that makes a
replicated term have infinitely many decompositions. -/
def unfoldAx : EqAxiom rsig noMetas where
  ctx := [RSrt.proc]
  sort := RSrt.proc
  lhs := Term.op (S := eqSig) (Sum.inl ROp.bang) (.cons (Term.var Var.zero) .nil)
  rhs := Term.op (S := eqSig) (Sum.inl ROp.par)
    (.cons (Term.op (S := eqSig) (Sum.inl ROp.bang) (.cons (Term.var Var.zero) .nil))
      (.cons (Term.var Var.zero) .nil))

abbrev unfoldE : List (EqAxiom rsig noMetas) := [unfoldAx]

def emptyBody : (k : Fin noMetas.length) →
    Term rsig (noMetas.get k).1 (noMetas.get k).2 := fun k => k.elim0

/-! ## Terms and the count -/

def tick : Term rsig [] RSrt.proc := Term.op (S := rsig) ROp.tick Args.nil

def bang (t : Term rsig [] RSrt.proc) : Term rsig [] RSrt.proc :=
  Term.op (S := rsig) ROp.bang (.cons t .nil)

def parT (a b : Term rsig [] RSrt.proc) : Term rsig [] RSrt.proc :=
  Term.op (S := rsig) ROp.par (.cons a (.cons b .nil))

def headTick {s : RSrt} (o : ROp s) : Nat :=
  match o with
  | .tick => 1
  | _ => 0

mutual
/-- How many inert tokens a process contains. -/
def countTick : {Γ : Ctx rsig} → {s : RSrt} → Term rsig Γ s → Nat
  | _, _, .var _ => 0
  | _, _, .op o args => headTick o + countTickArgs args

def countTickArgs : {as : List (List RSrt × RSrt)} → {Γ : Ctx rsig} →
    Args rsig as Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => countTick head + countTickArgs tail
end

/-! ## The class of a replicated token is numerically unbounded -/

/-- `!tick` with `k` further copies of `tick` beside it. -/
def spread : Nat → Term rsig [] RSrt.proc
  | 0 => bang tick
  | k + 1 => parT (spread k) tick

/-- A closing substitution for the unfolding axiom. -/
def closeAt (t : Term rsig [] RSrt.proc) :
    (s : RSrt) → Var [RSrt.proc] s → Term rsig [] s
  | _, .zero => t
  | _, .succ v => nomatch v

/-- One unfolding step. -/
theorem unfold_step (t : Term rsig [] RSrt.proc) :
    EqClosure unfoldE (bang t) (parT (bang t) t) := by
  have h : EqClosure unfoldE (bind (closeAt t) (instantiate emptyBody unfoldAx.lhs))
      (bind (closeAt t) (instantiate emptyBody unfoldAx.rhs)) :=
    EqClosure.ax_closed unfoldE (Γ := ([] : Ctx rsig)) ⟨0, by decide⟩ emptyBody
      (closeAt t)
  simpa only [unfoldAx, instantiate, instantiateArgs, bind, bindArgs, liftSub,
    closeAt, bang, parT] using h

theorem parCong {a a' b b' : Term rsig [] RSrt.proc}
    (ha : EqClosure unfoldE a a') (hb : EqClosure unfoldE b b') :
    EqClosure unfoldE (parT a b) (parT a' b') := by
  show EqClosure unfoldE (Term.op (S := rsig) ROp.par (.cons a (.cons b .nil)))
    (Term.op (S := rsig) ROp.par (.cons a' (.cons b' .nil)))
  refine EqClosure.cong (S := rsig) ROp.par ?_
  exact .cons ha (.cons hb .nil)

/-- **Every spread is in the class of the single replicated token.** -/
theorem spread_eq : ∀ k : Nat, EqClosure unfoldE (bang tick) (spread k)
  | 0 => EqClosure.refl _
  | k + 1 =>
      EqClosure.trans (unfold_step tick)
        (parCong (spread_eq k) (EqClosure.refl tick))

/-- And the spreads have every count. -/
theorem countTick_spread : ∀ k : Nat, countTick (spread k) = k + 1
  | 0 => rfl
  | k + 1 => by
      show countTick (parT (spread k) tick) = k + 2
      simp only [parT, tick, countTick, countTickArgs, headTick,
        countTick_spread k]
      omega

/-! ## The consequence -/

/-- **No numeric invariant is constant on classes.**  For every number there is a
process equal to the single replicated token carrying exactly that many tokens,
so a function that separates counts cannot descend to the quotient. -/
theorem class_has_every_count (k : Nat) :
    ∃ u : Term rsig [] RSrt.proc,
      EqClosure unfoldE (bang tick) u ∧ countTick u = k + 1 :=
  ⟨spread k, spread_eq k, countTick_spread k⟩

/-- **So the count is not an invariant at all**, which is the hypothesis the
easy form of unique decomposition rests on. -/
theorem countTick_not_invariant :
    ¬ ∀ {Γ : Ctx rsig} {s : RSrt} {a b : Term rsig Γ s},
        EqClosure unfoldE a b → countTick a = countTick b := by
  intro hinv
  have h0 := hinv (spread_eq 0)
  have h1 := hinv (spread_eq 1)
  rw [countTick_spread 0] at h0
  rw [countTick_spread 1] at h1
  omega

/-- **And the quotient is not free on its primes.**  A free commutative monoid
has a well-defined number of factors; here one element has, in its own class,
representatives with every number of factors. -/
theorem not_free_on_primes :
    ∀ k : Nat, ∃ u, EqClosure unfoldE (bang tick) u ∧ k < countTick u :=
  fun k => ⟨spread k, spread_eq k, by rw [countTick_spread k]; omega⟩

/-! ### The scope this fixes

The repaired unique-decomposition theorem elsewhere in this development is
proved for a theory of associativity, commutativity and a unit, where the
multiplicities are a complete invariant.  This module is the reason that
hypothesis cannot be dropped: a presentation whose equational theory relates a
term to a parallel composition containing itself has no such invariant, and the
decomposition question there is the hard one about processes rather than the
easy one about multisets.  A presentation is free to make either choice, and the
source says as much -- with the unfolding law in the theory a replicated term and
that term beside its body are equal, and without it they are not. -/

/-! ## Said in the general vocabulary

The parallel fragment has a canonical form for its structural equations -- a
section of the quotient, exhibited as one.  With an unfolding law there is none
that respects the count, and that is the same statement as the failure above,
transported to the notion the other fragment instantiates. -/

/-- **No count-faithful canonical form exists here.**  A section of this quotient
must send every spreading of a replicated process to one representative, so no
representative can report the count -- which is the exact sense in which the
unfolding law destroys decomposition. -/
theorem no_count_faithful_nf :
    ¬ ∃ N : Mettapedia.OSLF.Syntax.NormalFormStrength.SemanticNF
        (fun t u : Term rsig [] RSrt.proc => EqClosure unfoldE t u),
      ∀ t, countTick (N.rep t) = countTick t := by
  rintro ⟨N, hfaithful⟩
  have hrep : N.rep (spread 0) = N.rep (spread 1) :=
    N.complete _ _ (EqClosure.trans (EqClosure.symm (spread_eq 0)) (spread_eq 1))
  have e0 := hfaithful (spread 0)
  have e1 := hfaithful (spread 1)
  rw [hrep, e1, countTick_spread 0, countTick_spread 1] at e0
  omega

end Unfolding

end Mettapedia.OSLF.Binding
