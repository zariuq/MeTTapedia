import Mettapedia.Languages.VibeITP.Presentation.SubstitutionSignature

/-!
# Bound-variable substitution controls

The controls retain the raw-operation domain, including count/list mismatch
and pruning outside the word range. A signature snapshot restricted to the
source is demonstrably insufficient when a replacement has a binder head.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution.Controls

open ComputationalData ComputationalShift
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => substitutionProgram
local notation "H" => computationalHost

private def s : Spec.SymId := .fresh 13
private def t : Spec.SymId := .fresh 14
private def positions : SignatureTable := [(s, ⟨.constant, [1, 0]⟩)]
private def imageBinder : SignatureTable := [(t, ⟨.constant, [1]⟩)]

theorem last_argument_replaces_lowest_variable :
    Applies P H "vibe:subst" [encodeTable [], natural 2, .list (encodeTerms [.bvar 16, .bvar 17]),
      encode (.bvar 0), natural 0] (encodeResult (some (.bvar 17))) :=
  substitution_computes [] 2 [.bvar 16, .bvar 17] (.bvar 0) 0

theorem first_argument_replaces_highest_parameter :
    Applies P H "vibe:subst" [encodeTable [], natural 2, .list (encodeTerms [.bvar 16, .bvar 17]),
      encode (.bvar 1), natural 0] (encodeResult (some (.bvar 16))) :=
  substitution_computes [] 2 [.bvar 16, .bvar 17] (.bvar 1) 0

theorem forward_argument_order_is_refused :
    ¬ Applies P H "vibe:subst" [encodeTable [], natural 2, .list (encodeTerms [.bvar 16, .bvar 17]),
      encode (.bvar 0), natural 0] (encodeResult (some (.bvar 16))) := by
  rw [substitution_accepts_iff]
  decide

theorem bound_variable_stays :
    Applies P H "vibe:subst" [encodeTable [], natural 1, .list (encodeTerms [.bvar 16]),
      encode (.bvar 0), natural 1] (encodeResult (some (.bvar 0))) :=
  substitution_computes [] 1 [.bvar 16] (.bvar 0) 1

theorem crossed_binders_shift_image :
    Applies P H "vibe:subst" [encodeTable [], natural 1, .list (encodeTerms [.bvar 16]),
      encode (.bvar 1), natural 1] (encodeResult (some (.bvar 17))) :=
  substitution_computes [] 1 [.bvar 16] (.bvar 1) 1

theorem capturing_image_is_refused :
    ¬ Applies P H "vibe:subst" [encodeTable [], natural 1, .list (encodeTerms [.bvar 16]),
      encode (.bvar 1), natural 1] (encodeResult (some (.bvar 16))) := by
  rw [substitution_accepts_iff]
  decide

theorem each_argument_has_its_binder_offset :
    Applies P H "vibe:subst" [encodeTable positions, natural 1, .list (encodeTerms [.bvar 2]),
      encode (.app s [.bvar 1, .bvar 0]), natural 0]
      (encodeResult (some (.app s [.bvar 3, .bvar 2]))) :=
  substitution_computes positions 1 [.bvar 2] (.app s [.bvar 1, .bvar 0]) 0

theorem repeated_arguments_retain_multiplicity :
    Applies P H "vibe:subst" [encodeTable [], natural 1, .list (encodeTerms [.bvar 2]),
      encode (.app s [.bvar 0, .bvar 0]), natural 0]
      (encodeResult (some (.app s [.bvar 2, .bvar 2]))) :=
  substitution_computes [] 1 [.bvar 2] (.app s [.bvar 0, .bvar 0]) 0

theorem zero_count_prunes_word_and_binder_guards :
    Applies P H "vibe:subst" [encodeTable [(s, ⟨.constant, [Spec.wordBound]⟩)], natural 0,
      .list [], encode (.app s [.bvar Spec.wordBound]), natural Spec.wordBound]
      (encodeResult (some (.app s [.bvar Spec.wordBound]))) :=
  substitution_computes [(s, ⟨.constant, [Spec.wordBound]⟩)] 0 [] (.app s [.bvar Spec.wordBound]) Spec.wordBound

theorem closed_application_prunes_unused_images :
    Applies P H "vibe:subst" [encodeTable [(s, ⟨.constant, [1]⟩)], natural 9,
      .list (encodeTerms [.bvar Spec.wordBound]), encode (.app s [.bvar 0]), natural 0]
      (encodeResult (some (.app s [.bvar 0]))) :=
  substitution_computes [(s, ⟨.constant, [1]⟩)] 9 [.bvar Spec.wordBound] (.app s [.bvar 0]) 0

theorem missing_image_defaults_to_zero :
    Applies P H "vibe:subst" [encodeTable [], natural 2, .list [], encode (.bvar 0), natural 0]
      (encodeResult (some (.bvar 0))) := substitution_computes [] 2 [] (.bvar 0) 0

theorem missing_image_is_shifted :
    Applies P H "vibe:subst" [encodeTable [], natural 2, .list [], encode (.bvar 1), natural 1]
      (encodeResult (some (.bvar 1))) := substitution_computes [] 2 [] (.bvar 1) 1

theorem extra_image_does_not_change_explicit_count :
    Applies P H "vibe:subst" [encodeTable [], natural 1, .list (encodeTerms [.bvar 16, .bvar 17]),
      encode (.bvar 0), natural 0] (encodeResult (some (.bvar 16))) :=
  substitution_computes [] 1 [.bvar 16, .bvar 17] (.bvar 0) 0

theorem literal_bytes_are_preserved :
    Applies P H "vibe:subst" [encodeTable [], natural Spec.wordBound, .list [],
      encode (.lit [0, 255, 42]), natural Spec.wordBound]
      (encodeResult (some (.lit [0, 255, 42]))) :=
  substitution_computes [] Spec.wordBound [] (.lit [0, 255, 42]) Spec.wordBound

theorem variable_above_parameters_uses_relative_index :
    Applies P H "vibe:subst" [encodeTable [], natural 2, .list [], encode (.bvar 4), natural 1]
      (encodeResult (some (.bvar 3))) := substitution_computes [] 2 [] (.bvar 4) 1

theorem shifted_image_at_word_boundary_refuses :
    Applies P H "vibe:subst" [encodeTable [], natural 1, .list (encodeTerms [.bvar (Spec.wordBound - 2)]),
      encode (.bvar 1), natural 1] (encodeResult none) :=
  substitution_computes [] 1 [.bvar (Spec.wordBound - 2)] (.bvar 1) 1

theorem relative_index_at_word_boundary_refuses :
    Applies P H "vibe:subst" [encodeTable [], natural 1, .list [],
      encode (.bvar (Spec.wordBound - 1)), natural 0] (encodeResult none) :=
  substitution_computes [] 1 [] (.bvar (Spec.wordBound - 1)) 0

theorem binder_addition_at_word_boundary_refuses :
    Applies P H "vibe:subst" [encodeTable [(s, ⟨.constant, [1]⟩)], natural 1,
      .list (encodeTerms [.bvar 0]), encode (.app s [.bvar Spec.wordBound]), natural (Spec.wordBound - 1)]
      (encodeResult none) :=
  substitution_computes [(s, ⟨.constant, [1]⟩)] 1 [.bvar 0] (.app s [.bvar Spec.wordBound]) (Spec.wordBound - 1)

theorem late_child_refusal_is_preserved :
    Applies P H "vibe:subst" [encodeTable [], natural 1, .list (encodeTerms [.bvar 2]),
      encode (.app s [.bvar 0, .bvar Spec.wordBound]), natural 0] (encodeResult none) :=
  substitution_computes [] 1 [.bvar 2] (.app s [.bvar 0, .bvar Spec.wordBound]) 0

theorem unknown_head_uses_zero_binders :
    Applies P H "vibe:subst" [encodeTable [], natural 1, .list (encodeTerms [.bvar 2]),
      encode (.app (.fresh 18446744073709551629) [.bvar 0]), natural 0]
      (encodeResult (some (.app (.fresh 18446744073709551629) [.bvar 2]))) :=
  substitution_computes [] 1 [.bvar 2] (.app (.fresh 18446744073709551629) [.bvar 0]) 0

theorem list_length_includes_every_element :
    Applies P H "vibe:list-length" [.list [.sym "a", .sym "a", .var "unbound"]] (natural 3) :=
  listLength_computes _

theorem list_lookup_does_not_execute_selected_data :
    Applies P H "vibe:get-default"
      [.list [.expr [.sym "unknown-call", .var "unbound"]], natural 0, .sym "default"]
      (.expr [.sym "unknown-call", .var "unbound"]) := getDefault_computes _ 0 _

theorem list_lookup_after_length_returns_default :
    Applies P H "vibe:get-default" [.list [.sym "a"], natural 1, .sym "default"] (.sym "default") :=
  getDefault_computes _ 1 _

theorem list_lookup_large_index_returns_default :
    Applies P H "vibe:get-default" [.list [.sym "a"], natural 18446744073709551629, .sym "default"]
      (.sym "default") := getDefault_computes _ 18446744073709551629 _

theorem image_head_is_included_in_snapshot :
    Applies P H "vibe:subst"
      [encodeTable (substitutionSnapshot (signatureOf imageBinder) (.bvar 1) [.app t [.bvar 0]]),
        natural 1, .list (encodeTerms [.app t [.bvar 0]]), encode (.bvar 1), natural 1]
      (encodeResult (some (.app t [.bvar 0]))) :=
  substitution_computes_for_signature (signatureOf imageBinder) 1 [.app t [.bvar 0]] (.bvar 1) 1

theorem source_only_snapshot_changes_substitution :
    Spec.substBVars (signatureOf (snapshot (signatureOf imageBinder) (.bvar 1))) 1
      [.app t [.bvar 0]] (.bvar 1) 1 = some (.app t [.bvar 1]) ∧
    Spec.substBVars (signatureOf imageBinder) 1 [.app t [.bvar 0]] (.bvar 1) 1 = some (.app t [.bvar 0]) := by
  constructor <;> rfl

theorem invented_result_is_refused (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset : Nat) (claimed : Term)
    (different : claimed ≠ encodeResult (Spec.substBVars (signatureOf table) count images body offset)) :
    ¬ Applies P H "vibe:subst"
      [encodeTable table, natural count, .list (encodeTerms images), encode body, natural offset] claimed := by
  rw [substitution_result_exact]
  exact different

theorem no_fuel_is_exhaustion :
    apply P H 0 "vibe:subst" [encodeTable [], natural 1, .list [], encode (.bvar 0), natural 0] = .exhausted := rfl

theorem malformed_count_faults :
    apply P H 3 "vibe:subst" [encodeTable [], .sym "wrong", .list [], encode (.bvar 0), natural 0] = .failure := rfl

theorem malformed_list_lookup_faults :
    apply P H 3 "vibe:get-default" [.sym "wrong", natural 0, .sym "default"] = .failure := rfl

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution.Controls
