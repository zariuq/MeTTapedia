import Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

/-! Composition and decomposition of exact scalar spans. These laws connect
grammar-driven printing with the original source-recognition judgment. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

open ClassAwareParserPackCorrespondence

theorem sequence_split {input first second : List Nat} {start stop : Nat}
    (matched : ScalarSequenceMatchesAt input (first ++ second) start stop) :
    ∃ middle, Nonempty (ScalarSequenceMatchesAt input first start middle) ∧
      Nonempty (ScalarSequenceMatchesAt input second middle stop) := by
  induction first generalizing start with
  | nil => exact ⟨start, ⟨.nil start⟩, ⟨matched⟩⟩
  | cons point rest ih =>
    cases matched with
    | cons lookup tail =>
      obtain ⟨middle, ⟨left⟩, right⟩ := ih tail
      exact ⟨middle, ⟨.cons lookup left⟩, right⟩

def sequence_of_lookups (input points : List Nat) (start : Nat)
    (found : ∀ index : Fin points.length,
      input[start + index.val]? = some points[index.val]) :
    ScalarSequenceMatchesAt input points start (start + points.length) := by
  induction points generalizing start with
  | nil => exact .nil start
  | cons point rest ih =>
    have head : input[start]? = some point := by simpa using found ⟨0, by simp⟩
    have tail := ih (start + 1) (fun index => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found index.succ)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ScalarSequenceMatchesAt.cons head tail

def sequence_self (input : List Nat) : ScalarSequenceMatchesAt input input 0 input.length := by
  simpa using sequence_of_lookups input input 0 (fun index => by simp)

end Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
