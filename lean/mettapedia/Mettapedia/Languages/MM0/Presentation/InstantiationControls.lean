import Mettapedia.Languages.MM0.Presentation.InstantiationCorrespondence

/-! # Admissibility and actual replacement in one authored MM0 computation -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalInstantiation.Controls

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => instantiationProgram
local notation "H" => computationalHost

private def table : SignatureTable := [(0, ⟨[.regular 0 ∅], 1, ∅⟩), (1, ⟨[], 1, ∅⟩)]
private def formal : Context := [.bound 0, .regular 1 ∅]
private def target : Context := [.regular 1 ∅, .bound 0]

private theorem checked (sourceContext targetContext : Context) (expressions : List Preterm)
    (body : Preterm) (result : Option Preterm)
    (calculation : Substitution.instantiate (signatureOf table) sourceContext targetContext expressions body = result) :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext sourceContext, encodeContext targetContext, encodeExpressions expressions, encode body]
      (encodeResult result) := by
  simpa only [calculation] using instantiation_computes table sourceContext targetContext expressions body

theorem authorized_replacement_is_performed :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions [.var 1, .term 1], encode (.var 1)]
      (encodeResult (some (.term 1))) := checked _ _ _ _ _ (by decide)

theorem replacements_are_simultaneous :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions [.var 1, .term 1], encode (.var 0)]
      (encodeResult (some (.var 1))) := checked _ _ _ _ _ (by decide)

theorem replacement_cannot_be_substituted_again :
    ¬ Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions [.var 1, .term 1], encode (.var 0)]
      (encodeResult (some (.term 1))) := by
  intro run
  have impossible := encodeResult_injective (run.deterministic replacements_are_simultaneous)
  cases impossible

theorem application_is_rebuilt :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions [.var 1, .term 1],
        encode (.app (.term 0) (.var 0))]
      (encodeResult (some (.app (.term 0) (.var 1)))) := checked _ _ _ _ _ (by decide)

theorem forbidden_dependency_prevents_replacement :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext [.bound 0, .regular 1 {0}],
        encodeExpressions [.var 0, .var 1], encode (.var 1)] (.sym "None") := checked _ _ _ _ none (by decide)

theorem inadmissibility_is_not_ignored_for_a_closed_body :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext [.bound 0, .regular 1 {0}],
        encodeExpressions [.var 0, .var 1], encode (.term 1)] (.sym "None") := checked _ _ _ _ none (by decide)

theorem missing_argument_prevents_closed_body_instantiation :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions [.var 1], encode (.term 1)]
      (.sym "None") := checked _ _ _ _ none (by decide)

theorem body_referring_outside_formal_context_refuses :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions [.var 1, .term 1], encode (.var 2)]
      (.sym "None") := checked _ _ _ _ none (by decide)

theorem repeated_body_variable_reuses_same_image :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions [.var 1, .term 1],
        encode (.app (.var 1) (.var 1))]
      (encodeResult (some (.app (.term 1) (.term 1)))) := checked _ _ _ _ _ (by decide)

theorem codec_preserves_order_and_multiplicity (first second : Preterm) :
    Applies P H "mm0:substitution-values" [encodeExpressions [first, second, first]]
      (encodeValues [first, second, first]) := values_computes _

theorem codec_cannot_reverse_arguments :
    ¬ Applies P H "mm0:substitution-values" [encodeExpressions [.var 0, .term 1]]
      (encodeValues [.term 1, .var 0]) := by
  intro run
  have impossible := run.deterministic (values_computes [.var 0, .term 1])
  simp [encodeValues, encode] at impossible

theorem zero_fuel_is_not_an_instantiation_refusal :
    apply P H 0 "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions [.var 1, .term 1], encode (.var 1)] =
      .exhausted := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalInstantiation.Controls
