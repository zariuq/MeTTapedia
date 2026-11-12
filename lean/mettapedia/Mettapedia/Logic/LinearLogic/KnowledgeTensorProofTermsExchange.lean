import Mettapedia.Logic.LinearLogic.KnowledgeTensorProofTerms

/-!
# The exchange of two uses in proof terms

The structural equations of proof terms do not exchange two uses. This module says when the
exchange is an equation between proofs.

* `System.beside`: two uses side by side over the remaining atoms, one of them first. Each is
  framed by the other's atoms and by the rest.
* `System.exchange_typed`: where each guard holds at the source without the other's tell, the
  two orders are proofs of one sequent.
* `System.Typed.first_asked`: the first use of a sequential proof is asked at the source.
* `System.exchange_typed_iff`: **the two orders are both proofs from a source exactly where both
  guards hold there.** The exchange is an equation of the uses whose guards do not wait for one
  another's tells; it is not an equation of all uses.
* `System.exchange_of_no_guards`: where no use asks anything, every two uses exchange.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

namespace System

open ProofTerm

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : System K Atom Rule)

/-- Two uses side by side over `rest`, the first one first: each is framed by the other's atoms
and by `rest`. -/
def beside (first second : Rule) (rest : Multiset Atom) : ProofTerm K Atom Rule :=
  .cut (.frame (sys.premises second + rest) (.rule first))
    (.frame (sys.conclusions first + rest) (.rule second))

variable {sys}

/-- The first use of a sequential proof is asked at the source. -/
theorem Typed.first_asked {extra : Multiset Atom} {first : Rule}
    {later : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom}
    (typed : sys.Typed (.cut (.frame extra (.rule first)) later) k Γ k' Γ') :
    sys.guard first (k ⊓ sys.tell first) := by
  cases typed with
  | cut one two =>
      cases one with
      | frame extra inner =>
          cases inner with
          | rule declaration k asked => exact asked

/-- Two uses whose guards hold at the source run side by side, the first one first. -/
theorem Typed.beside (first second : Rule) (rest : Multiset Atom) (k : K)
    (firstAsked : sys.guard first (k ⊓ sys.tell first))
    (secondAsked : sys.guard second (k ⊓ sys.tell second)) :
    sys.Typed (sys.beside first second rest) k (sys.premises first + (sys.premises second + rest))
      (k ⊓ sys.tell first ⊓ sys.tell second)
      (sys.conclusions second + (sys.conclusions first + rest)) := by
  have one := Typed.frame (sys.premises second + rest) (Typed.rule first k firstAsked)
  have later : sys.guard second (k ⊓ sys.tell first ⊓ sys.tell second) :=
    sys.guard_mono second (le_inf (inf_le_left.trans inf_le_left) inf_le_right) secondAsked
  have two := Typed.frame (sys.conclusions first + rest)
    (Typed.rule second (k ⊓ sys.tell first) later)
  rw [add_left_comm (sys.premises second)] at two
  exact Typed.cut one two

/-- **Where both guards hold at the source, the two orders are proofs of one sequent.** -/
theorem exchange_typed (first second : Rule) (rest : Multiset Atom) (k : K)
    (firstAsked : sys.guard first (k ⊓ sys.tell first))
    (secondAsked : sys.guard second (k ⊓ sys.tell second)) :
    sys.Typed (sys.beside first second rest) k (sys.premises first + (sys.premises second + rest))
        (k ⊓ sys.tell first ⊓ sys.tell second)
        (sys.conclusions second + (sys.conclusions first + rest)) ∧
      sys.Typed (sys.beside second first rest) k
        (sys.premises first + (sys.premises second + rest))
        (k ⊓ sys.tell first ⊓ sys.tell second)
        (sys.conclusions second + (sys.conclusions first + rest)) := by
  have exchanged := Typed.beside second first rest k secondAsked firstAsked
  rw [add_left_comm (sys.premises second), inf_right_comm,
    add_left_comm (sys.conclusions first)] at exchanged
  exact ⟨Typed.beside first second rest k firstAsked secondAsked, exchanged⟩

/-- **The two orders are both proofs from a source exactly where both guards hold there.** -/
theorem exchange_typed_iff (first second : Rule) (rest : Multiset Atom) (k : K) :
    ((∃ (k' : K) (Γ' : Multiset Atom), sys.Typed (sys.beside first second rest) k
          (sys.premises first + (sys.premises second + rest)) k' Γ') ∧
        ∃ (k' : K) (Γ' : Multiset Atom), sys.Typed (sys.beside second first rest) k
          (sys.premises first + (sys.premises second + rest)) k' Γ') ↔
      sys.guard first (k ⊓ sys.tell first) ∧ sys.guard second (k ⊓ sys.tell second) := by
  constructor
  · rintro ⟨⟨_, _, straight⟩, ⟨_, _, exchanged⟩⟩
    exact ⟨straight.first_asked, exchanged.first_asked⟩
  · rintro ⟨firstAsked, secondAsked⟩
    obtain ⟨straight, exchanged⟩ := exchange_typed first second rest k firstAsked secondAsked
    exact ⟨⟨_, _, straight⟩, ⟨_, _, exchanged⟩⟩

/-- **Where no use asks anything, every two uses exchange.** This is the case of a Petri net. -/
theorem exchange_of_no_guards (free : ∀ (declaration : Rule) (k : K), sys.guard declaration k)
    (first second : Rule) (rest : Multiset Atom) (k : K) :
    sys.Typed (sys.beside first second rest) k (sys.premises first + (sys.premises second + rest))
        (k ⊓ sys.tell first ⊓ sys.tell second)
        (sys.conclusions second + (sys.conclusions first + rest)) ∧
      sys.Typed (sys.beside second first rest) k
        (sys.premises first + (sys.premises second + rest))
        (k ⊓ sys.tell first ⊓ sys.tell second)
        (sys.conclusions second + (sys.conclusions first + rest)) :=
  exchange_typed first second rest k (free first _) (free second _)

end System

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
