import Mettapedia.Languages.MM0.Presentation.SubstitutionCorrespondence

/-! # Positive and adversarial controls for authored substitution computation -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.SubstitutionControls

open Kernel
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => substitutionProgram
local notation "H" => naturalHost

theorem simultaneous_not_recursive :
    Applies P H "mm0:subst"
      [encode (.app (.var 0) (.var 1)), encodeValues [.var 1, .term 7]]
      (encodeResult (some (.app (.var 1) (.term 7)))) :=
  substitution_computes _ _

theorem recursively_replacing_the_image_rejected :
    ¬ Applies P H "mm0:subst"
      [encode (.app (.var 0) (.var 1)), encodeValues [.var 1, .term 7]]
      (encodeResult (some (.app (.term 7) (.term 7)))) := by
  intro wrong
  have same := wrong.deterministic simultaneous_not_recursive
  have bad := encodeResult_injective same
  cases bad

theorem repeated_variable_reuses_one_image :
    Applies P H "mm0:subst"
      [encode (.app (.var 0) (.var 0)), encodeValues [.app (.term 4) (.var 3)]]
      (encodeResult (some (.app (.app (.term 4) (.var 3)) (.app (.term 4) (.var 3))))) :=
  substitution_computes _ _

theorem missing_argument_refuses :
    Applies P H "mm0:subst" [encode (.app (.term 0) (.var 1)), encodeValues [.term 5]]
      (encodeResult none) := substitution_computes _ _

theorem unused_missing_entries_do_not_refuse :
    Applies P H "mm0:subst" [encode (.term 123), encodeValues []]
      (encodeResult (some (.term 123))) := substitution_computes _ _

theorem large_index_refuses_without_wrapping :
    Applies P H "mm0:subst" [encode (.var 18446744073709551616), encodeValues [.term 5]]
      (encodeResult none) := substitution_computes _ _

theorem large_symbol_is_preserved :
    Applies P H "mm0:subst" [encode (.term 18446744073709551616), encodeValues []]
      (encodeResult (some (.term 18446744073709551616))) := substitution_computes _ _

theorem zero_fuel_is_exhaustion :
    apply P H 0 "mm0:subst" [encode (.var 0), encodeValues []] = .exhausted := rfl

theorem completed_runs_cannot_fault (source : Preterm) (values : List Preterm) (fuel : Nat) :
    apply P H fuel "mm0:subst" [encode source, encodeValues values] ≠ .failure := by
  intro failed
  have result := (substitution_computes source values).completed fuel
    (by rw [failed]; intro h; cases h)
  rw [failed] at result
  cases result

private def forgedProgram : Program :=
  [⟨"forge", "mm0:subst", [.var "source", .var "values"],
    .expr [.sym "Some", encode (.term 0)]⟩]

/-- Changing a rule body changes checking behavior; the shared engine does
not supply the missing independent guest correspondence. -/
theorem mutated_rule_invents_an_image :
    apply forgedProgram H 4 "mm0:subst" [encode (.var 0), encodeValues []] =
      .value (encodeResult (some (.term 0))) := rfl

theorem original_rules_reject_invented_image :
    ¬ Applies P H "mm0:subst" [encode (.var 0), encodeValues []]
      (encodeResult (some (.term 0))) := by
  intro wrong
  have same := wrong.deterministic (substitution_computes (.var 0) [])
  have bad := encodeResult_injective same
  cases bad

end Mettapedia.Languages.MM0.Presentation.SubstitutionControls
