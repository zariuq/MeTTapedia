import Mettapedia.OSLF.Syntax.TheoryMorphism

/-!
# Splittings, locations, and the events available now

Chapter 17 of Finding Mind separates two things that are easy to conflate.  A
one-hole context is a *shape*: it says what the surroundings look like, and the
same shape sits around indefinitely many subterms of indefinitely many terms.
What locates is the *pair*.

Definition 17.2 makes a splitting of a term the pair `(K, t)` with `K[t] = s`,
with `plug` sending a splitting to the term it reconstructs and forgetting where
the cut was; a location in `s` is then a point of the fibre of `plug` over `s`.
Definition 17.3 restricts to the splittings at which something can happen: the
bundle `Fire` of available events, those cuts whose subterm side exposes a redex,
with the context side being where that rewrite is to fire.

All four claims the source makes about this are proved here: that a context does
not locate, that a location is a point of a fibre and nothing else, that the
fibre over a state is exactly the redex positions of that state, and that `Fire`
is a proper sub-bundle -- most cuts are inert, and the sparseness is the content.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

/-! ## Definition 17.2: splittings and the plug map -/

/-- A **splitting**: a one-hole context and a subterm, with no equation tying
them to any particular term.  This is the pair, not the position: the point of
the definition is that the pair carries the location and neither half does. -/
structure Splitting (S : Signature) (Γ : Ctx S) (s : S.Srt) where
  /-- The sort of the cut. -/
  carrier : S.Srt
  /-- The shape: what the surroundings look like. -/
  ctxt : Term S (carrier :: Γ) s
  /-- The subterm side of the cut. -/
  redex : Term S Γ carrier

/-- `plug` reconstructs the term and forgets where the cut was. -/
def plug {Γ : Ctx S} {s : S.Srt} (Sp : Splitting S Γ s) : Term S Γ s :=
  inst Sp.ctxt Sp.redex

/-! ## Section 17.3: a context is a shape, not a place -/

/-- **A shape is not a place.**  One context, two subterms, two different terms:
the context alone does not say which surroundings, of which term, one is in the
middle of.  This is the source's argument, with the lambda example replaced by
the smallest one that makes the point. -/
theorem shape_does_not_locate {Γ : Ctx S} {c : S.Srt} (t u : Term S Γ c)
    (hne : t ≠ u) :
    plug (⟨c, Term.var Var.zero, t⟩ : Splitting S Γ c)
      ≠ plug (⟨c, Term.var Var.zero, u⟩ : Splitting S Γ c) := hne

/-! ## A location is a point of a fibre

The source says a location in `s` is a point of the fibre of `plug` over `s`.
That fibre is exactly the redex positions of `s`, which is why the position
structure is the right notion of "where" and why it carries a plugging equation
rather than a path. -/

/-- A point of the fibre gives a position. -/
def positionOfFibre {Γ : Ctx S} {s : S.Srt} {L : Term S Γ s}
    (Sp : Splitting S Γ s) (h : plug Sp = L) : RedexPosition S Γ s L where
  carrier := Sp.carrier
  ctxt := Sp.ctxt
  redex := Sp.redex
  plugs := h

/-- A position gives a point of the fibre. -/
def fibreOfPosition {Γ : Ctx S} {s : S.Srt} {L : Term S Γ s}
    (P : RedexPosition S Γ s L) : Splitting S Γ s where
  carrier := P.carrier
  ctxt := P.ctxt
  redex := P.redex

theorem fibreOfPosition_plug {Γ : Ctx S} {s : S.Srt} {L : Term S Γ s}
    (P : RedexPosition S Γ s L) : plug (fibreOfPosition P) = L := P.plugs

theorem positionOfFibre_fibreOfPosition {Γ : Ctx S} {s : S.Srt} {L : Term S Γ s}
    (P : RedexPosition S Γ s L) :
    positionOfFibre (fibreOfPosition P) (fibreOfPosition_plug P) = P := rfl

theorem fibreOfPosition_positionOfFibre {Γ : Ctx S} {s : S.Srt} {L : Term S Γ s}
    (Sp : Splitting S Γ s) (h : plug Sp = L) :
    fibreOfPosition (positionOfFibre Sp h) = Sp := rfl

/-! ## Definition 17.3: the bundle of available events -/

/-- An **available event**: a splitting whose subterm side exposes a redex of the
rule, with the context side being where that rewrite is to fire. -/
def Fire {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    {s : S.Srt} (Sp : Splitting S [] s) : Prop :=
  ∃ (h : Sp.carrier = P.sort) (b : Term S [] P.sort),
    RootStep P (castTermSort h Sp.redex) b

/-- **The residual of an available event**: the term the state becomes when that
event happens, with the context side untouched. -/
def residual {M : List (MetaArity S)} {P : PositionedRewrite (withMetas S M)}
    {s : S.Srt} (K : Term S [P.sort] s) (b : Term S [] P.sort) : Term S [] s :=
  inst K b

/-- **An available event is a direction the state can move in.**  Firing at the
cut is a step of the relation the rule generates, from the term the splitting
reconstructs to the residual, with the context side untouched. -/
theorem fire_gives_a_step {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt}
    (K : Term S [P.sort] s) (t b : Term S [] P.sort)
    (hstep : RootStep P t b) (hlin : holeCount K = 1) :
    Step P (plug ⟨P.sort, K, t⟩) (residual K b) :=
  ⟨K, t, b, hlin, hstep, rfl, rfl⟩

/-- The event really is at that cut: the state it moves from is the one the
splitting reconstructs. -/
theorem fire_source {M : List (MetaArity S)} {P : PositionedRewrite (withMetas S M)}
    {s : S.Srt} (K : Term S [P.sort] s) (t : Term S [] P.sort) :
    plug (⟨P.sort, K, t⟩ : Splitting S [] s) = inst K t := rfl

end Mettapedia.OSLF.Binding
