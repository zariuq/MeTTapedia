import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionReflection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterTextLaws
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePatternPolicy

/-! Every identifier subtree produced by the independent program printer
has an allowed spelling. The invariant composes through ordinary source
constructors and does not invoke a native parser. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Policy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Datalog

def root (label : String) (children : List Pattern) : Prop :=
  label = "dl-src:identifier-one" ∨ label = "dl-src:identifier-more" →
    ∃ name, CorePrinter.printText? "DlIdentifier" (.apply label children) = some name ∧
      name ∉ SourcePolicy.reservedWords

abbrev Holds := SourcePatternPolicy.Holds root
abbrev ChildrenHold := SourcePatternPolicy.ChildrenHold root

theorem node_holds (label : String) (children : List Pattern)
    (differentOne : label ≠ "identifier-one") (differentMore : label ≠ "identifier-more")
    (holds : ChildrenHold children) : Holds (node label children) := by
  refine ⟨?_, holds⟩
  intro equal
  rcases equal with equal | equal
  · exfalso
    apply differentOne
    exact (String.append_right_inj "dl-src:").mp equal
  · exfalso
    apply differentMore
    exact (String.append_right_inj "dl-src:").mp equal

theorem nibble_holds (value : Fin 16) : Holds (Radix16Codec.nibble value) := by
  have different : "R16Nibble" ++ toString value.val ≠ "dl-src:identifier-one" ∧
      "R16Nibble" ++ toString value.val ≠ "dl-src:identifier-more" := by
    fin_cases value <;> decide +kernel
  exact ⟨fun equal => False.elim (equal.elim different.1 different.2), trivial⟩

theorem radix_holds (word : Fin (16 ^ 6)) : Holds (Radix16Codec.encode word) := by
  constructor
  · intro equal
    have different : ¬ ("R16Pack24" = "dl-src:identifier-one" ∨ "R16Pack24" = "dl-src:identifier-more") := by decide
    exact False.elim (different equal)
  · exact ⟨nibble_holds _, nibble_holds _, nibble_holds _, nibble_holds _, nibble_holds _, nibble_holds _, trivial⟩

theorem leaf_holds (row : ScalarCore.Row) (point : Nat)
    (formed : SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className point) :
    Holds (ScalarCore.leaf row point formed) := by
  refine ⟨?_, radix_holds _, trivial⟩
  have different : "dl-scalar:" ++ (ScalarCore.lexicalState row).resultSort ≠ "dl-src:identifier-one" ∧
      "dl-scalar:" ++ (ScalarCore.lexicalState row).resultSort ≠ "dl-src:identifier-more" := by
    fin_cases row <;> decide +kernel
  intro equal
  exact False.elim (equal.elim different.1 different.2)

theorem scalar_holds (sort : String) (character : Char) (pattern : Pattern)
    (built : scalar? sort character = .ok pattern) : Holds pattern := by
  unfold scalar? at built
  cases selected : CorePrinter.lexicalRow? sort with
  | none => simp [selected] at built
  | some row =>
    simp only [selected] at built
    split at built
    · cases Except.ok.inj built; exact leaf_holds _ _ _
    · cases built

theorem identifier_tail_holds (characters : List Char) (pattern : Pattern)
    (built : identifierTail? characters = .ok pattern) : Holds pattern := by
  cases characters with
  | nil => cases built
  | cons first rest =>
    cases rest with
    | nil =>
      obtain ⟨head, headRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide) ⟨scalar_holds _ _ _ headRead, trivial⟩
    | cons second rest =>
      obtain ⟨head, headRead, built⟩ := bind_ok built
      obtain ⟨tail, tailRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide)
        ⟨scalar_holds _ _ _ headRead, identifier_tail_holds _ _ tailRead, trivial⟩
termination_by characters.length

theorem identifier_holds (name : String) (pattern : Pattern)
    (built : identifier? name = .ok pattern) : Holds pattern := by
  have notReserved := identifier_not_reserved name pattern built
  have printed := identifier_print name pattern built
  unfold identifier? at built
  rw [if_neg notReserved] at built
  cases characters : name.toList with
  | nil => simp [characters] at built
  | cons first rest =>
    cases rest with
    | nil =>
      simp only [characters] at built
      obtain ⟨head, headRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact ⟨fun _ => ⟨name, printed, notReserved⟩, scalar_holds _ _ _ headRead, trivial⟩
    | cons second rest =>
      simp only [characters] at built
      obtain ⟨head, headRead, built⟩ := bind_ok built
      obtain ⟨tail, tailRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact ⟨fun _ => ⟨name, printed, notReserved⟩,
        scalar_holds _ _ _ headRead, identifier_tail_holds _ _ tailRead, trivial⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Policy
