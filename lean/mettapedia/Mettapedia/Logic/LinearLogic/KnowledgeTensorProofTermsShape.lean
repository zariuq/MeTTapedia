import Mettapedia.Logic.LinearLogic.KnowledgeTensorProofTerms

/-!
# The structural quotient asks nothing of the guards

The theorem that proofs from one source are equal modulo the structural equations exactly when
they have the same readout uses only the atoms of the terms. Guards and knowledge decide which
terms are proofs; they do not decide which proofs are equal.

* `System.unguarded`: the same declarations with nothing asked.
* `System.Shaped`: a term has the shape of a proof when it is a proof with nothing asked.
  `System.Typed.shaped`: every proof has the shape of a proof.
* `System.eqv_iff_readout_of_shaped`: **terms with the shape of proofs from the same atoms are
  equal modulo the structural equations exactly when they have the same readout.**
* `System.eqv_iff_readout_of_typed`: so proofs from the same atoms are, whatever knowledge each
  starts from.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

namespace System

open ProofTerm

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : System K Atom Rule)

/-- The same declarations with nothing asked. -/
def unguarded : System K Atom Rule where
  take := sys.take
  read := sys.read
  make := sys.make
  tell := sys.tell
  guard := fun _ _ => True
  guard_mono := by
    intros
    exact True.intro

/-- A term has the shape of a proof when it is a proof with nothing asked: its atoms fit. -/
abbrev Shaped (p : ProofTerm K Atom Rule) (k : K) (Γ : Multiset Atom) (k' : K)
    (Γ' : Multiset Atom) : Prop :=
  sys.unguarded.Typed p k Γ k' Γ'

variable {sys}

/-- Every proof has the shape of a proof. -/
theorem Typed.shaped {p : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom}
    (typed : sys.Typed p k Γ k' Γ') : sys.Shaped p k Γ k' Γ' := by
  induction typed with
  | identity k Γ => exact Typed.identity k Γ
  | rule declaration k asked => exact Typed.rule (sys := sys.unguarded) declaration k True.intro
  | frame extra _ ih => exact Typed.frame extra ih
  | strengthen more _ ih => exact Typed.strengthen more ih
  | cut _ _ ihFirst ihSecond => exact Typed.cut ihFirst ihSecond

variable [DecidableEq Atom]

/-- **Terms with the shape of proofs from the same atoms are equal modulo the structural
equations exactly when they have the same readout.** Nothing is asked of the guards or of the
knowledge. -/
theorem eqv_iff_readout_of_shaped {p q : ProofTerm K Atom Rule} {k k' j j' : K}
    {Γ Γ' Δ' : Multiset Atom} (first : sys.Shaped p k Γ k' Γ') (second : sys.Shaped q j Γ j' Δ') :
    Eqv p q ↔ p.readout = q.readout := by
  constructor
  · exact Eqv.readout_eq
  · intro same
    have normalFirst : Eqv p (sys.unguarded.normal Γ p.readout) := Typed.normalize first
    have normalSecond : Eqv q (sys.unguarded.normal Γ q.readout) := Typed.normalize second
    rw [same] at normalFirst
    exact .trans normalFirst (.symm normalSecond)

/-- Proofs from the same atoms are equal modulo the structural equations exactly when they have
the same readout, whatever knowledge each starts from. -/
theorem eqv_iff_readout_of_typed {p q : ProofTerm K Atom Rule} {k k' j j' : K}
    {Γ Γ' Δ' : Multiset Atom} (first : sys.Typed p k Γ k' Γ') (second : sys.Typed q j Γ j' Δ') :
    Eqv p q ↔ p.readout = q.readout :=
  eqv_iff_readout_of_shaped first.shaped second.shaped

end System

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
