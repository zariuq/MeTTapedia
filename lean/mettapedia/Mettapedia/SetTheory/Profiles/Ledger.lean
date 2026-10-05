import Mettapedia.SetTheory.Profiles.Diaconescu
import Mettapedia.SetTheory.Profiles.Foundation
import Mettapedia.SetTheory.Profiles.Pairing

/-!
# Three principle ledgers

Each ledger records the principles a profile assumes and the facts derived
or refuted from them. The profiles are stated abstractly. The Megalodon
profile is extensionality, empty set, union, power set, separation,
replacement, membership induction and a choice operator. The hyperset profile
is the same set-forming principles together with a Quine atom, and without
membership induction. The bare profile assumes no set principle; its logical
content is the empty higher-order theory in `BareTheory`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles

universe u

variable {S : Type u} (mem : Mem S)

/-- The principles of the Megalodon set theory, stated on an arbitrary carrier. -/
structure MegalodonAssumptions where
  extensional : Extensional mem
  empty : HasEmpty mem
  union : HasUnion mem
  power : HasPower mem
  separation : HasSeparation mem
  replacement : HasReplacement mem
  induction : HasMemInduction mem
  epsilon : (S → Prop) → S
  choice : ChoiceLaw epsilon

/-- Facts that follow from the Megalodon principles, and the Quine atom they refute. -/
structure MegalodonLedger (A : MegalodonAssumptions mem) : Prop where
  excludedMiddle : ∀ p : Prop, p ∨ ¬ p
  irreflexive : ∀ x, ¬ mem x x
  noQuineAtom : ¬ HasQuineAtom mem
  unorderedPair : HasPairing mem
  unorderedPairByChoice : HasPairing mem

/-- The Megalodon ledger. Excluded middle uses the choice operator. Pairs
follow from empty set, power set, separation and replacement, and also by the
choice construction on the separated index. -/
theorem megalodonLedger (A : MegalodonAssumptions mem) : MegalodonLedger mem A where
  excludedMiddle := lem_of_choice A.extensional A.separation A.empty A.power A.epsilon A.choice
  irreflexive := irreflexive_of_induction A.induction
  noQuineAtom := noQuineAtom_of_induction A.induction
  unorderedPair := unorderedPair A.empty A.power A.separation A.replacement
  unorderedPairByChoice :=
    unorderedPair_of_choice A.empty A.power A.separation A.replacement A.epsilon A.choice

/-- The principles of a hyperset profile: the set-forming principles, a Quine
atom, and no membership-induction assumption. -/
structure HypersetAssumptions where
  extensional : Extensional mem
  empty : HasEmpty mem
  union : HasUnion mem
  power : HasPower mem
  separation : HasSeparation mem
  replacement : HasReplacement mem
  quineAtom : HasQuineAtom mem

/-- The hyperset ledger. The atom is a self-member, and it refutes membership
induction and irreflexivity. Pairs follow from the set-forming principles. -/
structure HypersetLedger (A : HypersetAssumptions mem) : Prop where
  selfMember : ∃ x, mem x x
  refutesInduction : ¬ HasMemInduction mem
  refutesIrreflexive : ¬ ∀ x, ¬ mem x x
  unorderedPair : HasPairing mem

theorem hypersetLedger (A : HypersetAssumptions mem) : HypersetLedger mem A where
  selfMember := selfMember_of_quineAtom A.quineAtom
  refutesInduction := quineAtom_refutes_induction A.quineAtom
  refutesIrreflexive := quineAtom_refutes_irreflexive A.quineAtom
  unorderedPair := unorderedPair A.empty A.power A.separation A.replacement

/-- The bare profile assumes no membership principle. -/
structure BareAssumptions : Prop

end Mettapedia.SetTheory.Profiles
