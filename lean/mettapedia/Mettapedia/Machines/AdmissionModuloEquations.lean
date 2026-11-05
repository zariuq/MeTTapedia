import Mathlib.Tactic

/-!
# Admission modulo the language's equations: no cliff between equal programs

A fast route that admits programs by their spelling draws its boundary through classes
of programs the language already proves equal.  Measured (11/04, frozen opt binary):
`(if c t)` and `(if c t (empty))` answer alike (PeTTa's missing else is no result),
yet the two-armed form is refused by the compiled tier ("if arity") and, the refusal
being contagious, the whole program runs 44-58x slower; a query body spelled with
`let*`, `case`, a bare `once`, or a size observer applied directly are refused where
the nested `let` spelling of the same body is admitted (3-19x).

The remedy is to admit by normal form: a normalizer `N` rewrites a program to a
canonical representative of its class under the language's proven equations, and the
fast route is offered `N P` instead of `P`.

The model: programs `P`, observations `O`, a semantics `eval`, an equivalence `equiv`
that `eval` respects, a normalizer with `equiv (N P) P`, and a fast route
`fast : P → Option O` sound on what it admits.  This file proves:
* `normalized_sound`: offering the normal form keeps the route sound;
* `normalized_respects`: when `N` is canonical (equivalent programs have one normal
  form), the normalized route admits a program exactly when it admits every program
  equivalent to it, and answers alike on them: its boundary is a union of classes;
* `normalized_admits_more`: when `N` fixes what the route already admitted, the
  normalized route admits everything the spelled route admitted, and more.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionModuloEquations

variable {P O : Type}

/-- A language with a semantics, an equational theory it respects, and a normalizer. -/
structure Language (P O : Type) where
  eval : P → O
  equiv : P → P → Prop
  equiv_eval : ∀ p q, equiv p q → eval p = eval q
  norm : P → P
  norm_equiv : ∀ p, equiv (norm p) p

/-- A fast route, sound on what it admits. -/
structure Route (L : Language P O) where
  fast : P → Option O
  sound : ∀ p o, fast p = some o → o = L.eval p

variable {L : Language P O}

/-- The route offered normal forms. -/
def Route.normalized (R : Route L) (p : P) : Option O := R.fast (L.norm p)

theorem normalized_sound (R : Route L) (p : P) (o : O) (h : R.normalized p = some o) :
    o = L.eval p := by
  have := R.sound _ _ h
  rw [this, L.equiv_eval _ _ (L.norm_equiv p)]

/-- A canonical normalizer: equivalent programs have one normal form. -/
def Canonical (L : Language P O) : Prop := ∀ p q, L.equiv p q → L.norm p = L.norm q

/-- The normalized route answers alike on equivalent programs, admission included. -/
theorem normalized_respects (R : Route L) (hc : Canonical L) (p q : P)
    (h : L.equiv p q) : R.normalized p = R.normalized q := by
  simp only [Route.normalized, hc p q h]

/-- Its admitted set is closed under the equations. -/
theorem normalized_admitted_closed (R : Route L) (hc : Canonical L) (p q : P)
    (h : L.equiv p q) : (R.normalized p).isSome = (R.normalized q).isSome := by
  rw [normalized_respects R hc p q h]

/-- If the normalizer fixes every program the spelled route admits, the normalized
route admits all of them. -/
theorem normalized_admits_more (R : Route L)
    (hfix : ∀ p, (R.fast p).isSome = true → L.norm p = p) (p : P)
    (h : (R.fast p).isSome = true) : (R.normalized p).isSome = true := by
  simp only [Route.normalized, hfix p h, h]

/-- A cliff of the spelled route is a pair of equivalent programs it separates; the
normalized route has none. -/
theorem no_cliff_between_equal_programs (R : Route L) (hc : Canonical L) (p q : P)
    (h : L.equiv p q) (hp : (R.normalized p).isSome = true) :
    (R.normalized q).isSome = true := by
  rw [← normalized_admitted_closed R hc p q h]; exact hp

end Mettapedia.Machines.AdmissionModuloEquations
