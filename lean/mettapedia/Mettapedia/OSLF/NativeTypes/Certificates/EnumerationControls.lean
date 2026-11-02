import Mettapedia.OSLF.NativeTypes.Certificates.NativeEnumeration
import Mettapedia.OSLF.NativeTypes.Certificates.Controls

/-!
# Full native wire and certificate-search controls

The complete dependent syntax is exercised with a higher-order quantified
predicate, conditional comprehension, quotation and duplicate assumptions.
Wire decoding rejects malformed tags and out-of-scope variables. Search retains
an explicit unresolved cursor, and a decoded accepted certificate is conclusive.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.EnumerationControls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Controls
open Mettapedia.OSLF.Binding.WireCodec

deriving instance Encodable for TypeSymbol, PredicateSymbol

instance : Encodable symbols.TypeSymbol := inferInstanceAs (Encodable TypeSymbol)
instance : Encodable symbols.TermSymbol := inferInstanceAs (Encodable Empty)
instance : Encodable symbols.PredicateSymbol := inferInstanceAs (Encodable PredicateSymbol)

def codecs : NativeWire.SymbolCodecs symbols := NativeEnumeration.symbolCodecs

def conditionalJudgment : Judgment symbols :=
  .term conditionalContext (.refine (scalar 1) (positive 1) (.var 0))
    (.comprehension (scalar 1) (positive 1))

def quantifiedJudgment : Judgment symbols :=
  .entails .nil (.all (predicateFunctionAt 0)
    (.all (scalar 1) (.implies appliedPredicate appliedPredicate)))

def atEmptyCode : Search.State (Refinement.presentation signature) :=
  ⟨Encodable.encode Controls.empty, none⟩

theorem duplicate_origin_codes_distinct :
    Encodable.encode Controls.newest ≠ Encodable.encode Controls.older :=
  Tree.distinct_codes Controls.duplicate_origin_certificates_distinct

theorem conditional_wire_roundtrip :
    Encodable.decode (α := Refinement.Certificate signature)
      (Encodable.encode Controls.conditional) = some Controls.conditional :=
  Tree.decode_encode Controls.conditional

theorem quantified_discovered_by_size :
    ∃ certificate,
      (NativeEnumeration.search (D := signature) quantifiedJudgment
        (Tree.discoveryBound (Tree.wireSize Controls.quantified))).found = some certificate := by
  apply NativeEnumeration.discover_within_wire_bound quantifiedJudgment Controls.quantified
  exact Refinement.check_erase quantifiedPredicateFunction

theorem conditional_resume_exact (first second : Nat) :
    NativeEnumeration.search (D := signature) conditionalJudgment (first + second) =
      Search.run conditionalJudgment second
        (NativeEnumeration.search (D := signature) conditionalJudgment first) :=
  NativeEnumeration.exact_resume conditionalJudgment first second

#guard (NativeWire.rule codecs signature).get
  ((NativeWire.rule codecs signature).put .contextNil) = some .contextNil
#guard (NativeWire.rule codecs signature).get (.atom 0) = none
#guard (NativeWire.rule codecs signature).get (.pair (.atom 137) (.atom 0)) = none
#guard ((NativeWire.termAt codecs 0).get
  (.pair (.atom 1) (.pair (.atom 0) (.atom 0)))).isNone
#guard !((NativeWire.termAt codecs 1).get
  (.pair (.atom 1) (.pair (.atom 0) (.atom 0)))).isNone
#guard ((NativeWire.typeAt codecs 0).get
  ((NativeWire.typeAt codecs 0).put (predicateFunctionAt 0))).isSome
#guard (NativeEnumeration.search (D := signature) conditionalJudgment 0).found.isNone
#guard (Search.step (P := Refinement.presentation signature) (.context .nil) atEmptyCode).found.isSome
#guard (NativeWire.rule codecs signature).get
  ((NativeWire.rule codecs signature).put
    (.comprehensionIntroduction conditionalContext (scalar 1) (positive 1) (.var 0))) =
      some (.comprehensionIntroduction conditionalContext (scalar 1) (positive 1) (.var 0))

def formationSeeds : List (Refinement.Certificate signature) :=
  [Controls.damagedFamily, Controls.conditional, Controls.quantified]

theorem second_seed_found :
    (NativeEnumeration.searchWithSeeds formationSeeds conditionalJudgment 2).found =
      some Controls.conditional := by
  have bad : Controls.damagedFamily.check conditionalJudgment = false := by decide
  have good : Controls.conditional.check conditionalJudgment = true := Controls.conditional_checked
  simp [NativeEnumeration.searchWithSeeds, SeededSearch.search, SeededSearch.run,
    Search.Scheduled.step, Search.initial, SeededSearch.candidate, formationSeeds, bad, good]

theorem seeded_resume_exact (first second : Nat) :
    NativeEnumeration.searchWithSeeds formationSeeds conditionalJudgment (first + second) =
      SeededSearch.run formationSeeds conditionalJudgment second
        (NativeEnumeration.searchWithSeeds formationSeeds conditionalJudgment first) :=
  NativeEnumeration.seeded_exact_resume formationSeeds conditionalJudgment first second

theorem seed_failure_retains_unknown :
    (NativeEnumeration.searchWithSeeds formationSeeds conditionalJudgment 1).found = none := by rfl

#guard (NativeEnumeration.searchWithSeeds formationSeeds conditionalJudgment 1).found.isNone
#guard (NativeEnumeration.searchWithSeeds formationSeeds conditionalJudgment 2).found.isSome
#guard (NativeEnumeration.searchWithSeeds formationSeeds conditionalJudgment 52).found.isSome
#guard (NativeEnumeration.searchWithSeeds formationSeeds quantifiedJudgment 2).found.isNone
#guard (NativeEnumeration.searchWithSeeds formationSeeds quantifiedJudgment 3).found.isSome
#guard (SeededSearch.run formationSeeds conditionalJudgment 1
  (NativeEnumeration.searchWithSeeds formationSeeds conditionalJudgment 1)).found.isSome

end Mettapedia.OSLF.NativeTypes.Certificates.EnumerationControls
