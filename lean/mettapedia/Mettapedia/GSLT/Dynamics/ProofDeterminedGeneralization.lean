/-!
# The proof, not the example, determines the generalization

Miniature of the ProofGen insight (Tate--Stepp--Lerner, POPL 2010):
a before/after example underdetermines its safe generalization; the PROOF of
the example picks one.  The paper's own specimen: `0 * 0 → 0` generalizes to
`x * 0 → 0` or to `0 * x → 0` depending on WHICH annihilation proof justified
it, and the two generalizations are incomparable.

Here that is a theorem, in the smallest honest setting: a toy term language,
two root rewrite axioms, proof-indexed derivations, a generalizer that reads
only the proof constructor, and three results:

* `generalize_sound` — the generalized family is derivable at EVERY instance
  by the same proof skeleton (the ProofGen re-validation step);
* `generalize_meets_example` — both generalizations instantiate back to the
  original concrete example (the example is their common instance);
* `generalizations_incomparable` — each generalization has instances the
  other cannot produce: neither subsumes the other, so no example-only
  procedure could have chosen between them.

Scope honesty: root-position rewriting only, no congruence closure, no
pullback/pushout machinery — this is the seed specimen for the post-crown
occurrence-diagram tranche, not that tranche.  The bridge to the sealed
provenance module is the intended next play: backward proof slicing is
support-of-provenance (`ProvenanceInterpretation`).
-/

namespace Mettapedia.GSLT.Dynamics.ProofDeterminedGeneralization

/-- Toy terms: numeric literals, variables, and one binary operator. -/
inductive Tm : Type where
  | lit : Nat → Tm
  | var : Nat → Tm
  | mul : Tm → Tm → Tm
deriving DecidableEq, Repr

/-- Root-position derivations: the two annihilation axioms, each applicable
to an arbitrary co-factor.  A value of `Deriv a b` IS the proof object. -/
inductive Deriv : Tm → Tm → Type where
  | mulZeroR (t : Tm) : Deriv (.mul t (.lit 0)) (.lit 0)
  | mulZeroL (t : Tm) : Deriv (.mul (.lit 0) t) (.lit 0)

/-- The concrete example: `0 * 0 → 0`, proved by the RIGHT annihilation. -/
def exampleByRight : Deriv (.mul (.lit 0) (.lit 0)) (.lit 0) :=
  .mulZeroR (.lit 0)

/-- The same concrete example, proved by the LEFT annihilation.  Two distinct
proof objects for one before/after pair. -/
def exampleByLeft : Deriv (.mul (.lit 0) (.lit 0)) (.lit 0) :=
  .mulZeroL (.lit 0)

/-- A rewrite-rule family: for each instantiation of the abstracted position,
a source and a target term. -/
def RuleFamily : Type := Tm → Tm × Tm

/-- The generalizer reads ONLY the proof constructor — never the example —
and abstracts exactly the position the proof left unconstrained. -/
def generalize {a b : Tm} : Deriv a b → RuleFamily
  | .mulZeroR _ => fun x => (.mul x (.lit 0), .lit 0)
  | .mulZeroL _ => fun x => (.mul (.lit 0) x, .lit 0)

/-- **Re-validation**: every instance of the generalized family is derivable,
by the same proof skeleton that proved the concrete example. -/
def generalize_sound {a b : Tm} (d : Deriv a b) (x : Tm) :
    Deriv (generalize d x).1 (generalize d x).2 :=
  match d with
  | .mulZeroR _ => .mulZeroR x
  | .mulZeroL _ => .mulZeroL x

/-- Both generalizations meet at the concrete example: instantiating either
family at `0` returns exactly the original before/after pair. -/
theorem generalize_meets_example :
    generalize exampleByRight (.lit 0) =
        (.mul (.lit 0) (.lit 0), .lit 0) ∧
      generalize exampleByLeft (.lit 0) =
        (.mul (.lit 0) (.lit 0), .lit 0) := by
  constructor <;> rfl

/-- **Incomparability**: the right-proof generalization produces an instance
the left-proof generalization cannot, and vice versa.  The example alone
could never have chosen — only the proof does. -/
theorem generalizations_incomparable :
    (∃ x, ∀ y, generalize exampleByRight x ≠ generalize exampleByLeft y) ∧
      (∃ x, ∀ y, generalize exampleByLeft x ≠ generalize exampleByRight y) := by
  constructor
  · exact ⟨.var 0, fun y h => by
      simp only [generalize, exampleByRight, exampleByLeft,
        Prod.mk.injEq, Tm.mul.injEq] at h
      exact Tm.noConfusion h.1.1⟩
  · exact ⟨.var 0, fun y h => by
      simp only [generalize, exampleByRight, exampleByLeft,
        Prod.mk.injEq, Tm.mul.injEq] at h
      exact Tm.noConfusion h.1.2⟩

end Mettapedia.GSLT.Dynamics.ProofDeterminedGeneralization
