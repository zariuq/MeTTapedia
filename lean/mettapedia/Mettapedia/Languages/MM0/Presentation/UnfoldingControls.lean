import Mettapedia.Languages.MM0.Presentation.UnfoldingCorrespondence

/-! # Complete unfolding requests distinguish stores, arguments and fresh images -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions.Controls

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => unfoldingProgram
local notation "H" => computationalHost

private def table : SignatureTable := [
  (0, ⟨[], 0, ∅⟩),
  (1, ⟨[.regular 0 ∅], 0, ∅⟩),
  (2, ⟨[.regular 0 ∅], 0, ∅⟩),
  (3, ⟨[.regular 0 ∅], 0, ∅⟩),
  (4, ⟨[.bound 0], 0, ∅⟩)]

private def definitions : DefinitionTable := [
  (1, ⟨[], .var 0⟩),
  (2, ⟨[0], .var 0⟩),
  (3, ⟨[0, 0], .var 0⟩),
  (4, ⟨[], .var 0⟩)]

private def target : Context := [.bound 0, .bound 0, .bound 1, .regular 0 {0}, .regular 0 ∅]

private def request (bodies : DefinitionTable) (symbol : Nat) (arguments : List Preterm) (images : List Nat) : List Term :=
  [encodeTable table, encodeDefinitions bodies, encodeContext target,
    natural symbol, encodeExpressions arguments, encodeNaturals images]

private theorem checked (bodies : DefinitionTable) (symbol : Nat) (arguments : List Preterm)
    (images : List Nat) (result : Option Preterm)
    (calculation : Definition.unfold? (signatureOf table) (definitionsOf bodies) target symbol arguments images = result) :
    Applies P H "mm0:unfold" (request bodies symbol arguments images) (encodeResult result) := by
  simpa only [request, calculation] using unfolding_computes table bodies target symbol arguments images

theorem declared_body_is_substituted :
    Applies P H "mm0:unfold" (request definitions 1 [.term 0] []) (encodeResult (some (.term 0))) :=
  checked _ _ _ _ _ (by decide)

theorem fresh_dummy_is_checked :
    Applies P H "mm0:unfold" (request definitions 2 [.term 0] [1]) (encodeResult (some (.term 0))) :=
  checked _ _ _ _ _ (by decide)

theorem capture_in_parameter_refuses :
    Applies P H "mm0:unfold" (request definitions 2 [.var 0] [0]) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem declared_parameter_dependency_refuses :
    Applies P H "mm0:unfold" (request definitions 2 [.var 3] [0]) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem independent_parameter_accepts :
    Applies P H "mm0:unfold" (request definitions 2 [.var 4] [0]) (encodeResult (some (.var 4))) :=
  checked _ _ _ _ _ (by decide)

theorem repeated_dummy_image_refuses :
    Applies P H "mm0:unfold" (request definitions 3 [.term 0] [1, 1]) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem wrong_dummy_sort_refuses :
    Applies P H "mm0:unfold" (request definitions 2 [.term 0] [2]) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem regular_dummy_image_refuses :
    Applies P H "mm0:unfold" (request definitions 2 [.term 0] [4]) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem missing_dummy_image_refuses :
    Applies P H "mm0:unfold" (request definitions 2 [.term 0] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem extra_dummy_image_refuses :
    Applies P H "mm0:unfold" (request definitions 1 [.term 0] [0]) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem missing_parameter_refuses :
    Applies P H "mm0:unfold" (request definitions 1 [] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem extra_parameter_refuses :
    Applies P H "mm0:unfold" (request definitions 1 [.term 0, .term 0] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem wrong_parameter_sort_refuses :
    Applies P H "mm0:unfold" (request definitions 1 [.var 2] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem no_dummies_do_not_bypass_argument_typing :
    Applies P H "mm0:unfold" (request definitions 1 [.var 9] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem bound_parameter_accepts_bound_image :
    Applies P H "mm0:unfold" (request definitions 4 [.var 1] []) (encodeResult (some (.var 1))) :=
  checked _ _ _ _ _ (by decide)

theorem bound_parameter_refuses_same_sort_regular_image :
    Applies P H "mm0:unfold" (request definitions 4 [.var 4] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem primitive_declaration_is_not_a_definition :
    Applies P H "mm0:unfold" (request definitions 0 [] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem a_body_without_a_declaration_refuses :
    Applies P H "mm0:unfold" (request [(7, ⟨[], .term 0⟩)] 7 [] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem changed_body_changes_result :
    Applies P H "mm0:unfold" (request [(1, ⟨[], .term 0⟩)] 1 [.var 4] []) (encodeResult (some (.term 0))) :=
  checked _ _ _ _ _ (by decide)

theorem stale_body_result_is_rejected :
    ¬ Applies P H "mm0:unfold" (request [(1, ⟨[], .term 0⟩)] 1 [.var 4] []) (encodeResult (some (.var 4))) := by
  intro run
  have impossible := encodeResult_injective (run.deterministic changed_body_changes_result)
  cases impossible

theorem missing_image_inside_unadmitted_body_refuses :
    Applies P H "mm0:unfold" (request [(1, ⟨[], .var 1⟩)] 1 [.term 0] []) (.sym "None") :=
  checked _ _ _ _ none (by decide)

theorem unfolding_alone_does_not_admit_a_body :
    Applies P H "mm0:unfold" (request [(1, ⟨[], .term 99⟩)] 1 [.term 0] []) (encodeResult (some (.term 99))) :=
  checked _ _ _ _ _ (by decide)

theorem exhausted_unfolding_has_no_verdict :
    apply P H 0 "mm0:unfold" (request definitions 1 [.term 0] []) = .exhausted := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions.Controls
