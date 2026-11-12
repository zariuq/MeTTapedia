import Mettapedia.Languages.MeTTa.PeTTa.CallArityDispatch

/-!
# Body holding belongs to the selected literal declaration family

This composes the existing arity-admission judgment, literal demand policy
and complete-call protocol. Frozen descriptors retain source arity and body
mode across activation; a substituted result spelling must not reclassify
the body. Partial-family selection is proved here, not its execution protocol.

Explicit execution escapes, source declaration readout and native scheduling
are separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SelectedBodyPolicy

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CallGuardOptimization CallArityDispatch TypedCallLowering
open Mettapedia.Machines.OrderedProtocol

inductive HoldsBody (kind : Kind) (supplied : Nat) (family : List Signature) : Prop where
  | selected (signature : Signature) (member : signature ∈ family)
      (admitted : Applicable supplied kind signature) (literal : signature.codomain = .symbol "Atom") :
      HoldsBody kind supplied family

def selectedHolding (kind : Kind) (supplied : Nat) (family : List Signature) : Bool :=
  holdBody (select kind supplied family)

theorem raw_codomain_iff (formal : Atom) : demand formal = .raw ↔ formal = .symbol "Atom" := by
  constructor
  · intro raw
    have same := demand_raw formal
    simpa [raw] using same.symm
  · intro same; subst formal; decide

theorem selectedHolding_iff (kind : Kind) (supplied : Nat) (family : List Signature) :
    selectedHolding kind supplied family = true ↔ HoldsBody kind supplied family := by
  constructor
  · intro held
    obtain ⟨signature, member, raw⟩ := List.any_eq_true.mp held
    have admitted := (mem_select kind supplied signature family).mp member
    exact .selected signature admitted.1 admitted.2 ((raw_codomain_iff _).mp (beq_iff_eq.mp raw))
  · intro held
    cases held with
    | selected signature member admitted literal =>
        apply List.any_eq_true.mpr
        exact ⟨signature, (mem_select ..).mpr ⟨member, admitted⟩, by simp [literal, demand]⟩

/-- Native arity and mode flags are frozen before whole-scheme activation.
The existing plan's demand count is its source arity. -/
def frozenEligible (kind : Kind) (supplied : Nat) (plan : Plan) : Bool :=
  match kind with
  | .complete => plan.demands.length == supplied
  | .underApplied => decide (supplied ≤ plan.demands.length)

def descriptorHolding (kind : Kind) (supplied : Nat) (plans : List Plan) : Bool :=
  plans.any fun plan => frozenEligible kind supplied plan && plan.holdResult

theorem frozenEligible_compile (kind : Kind) (supplied : Nat) (signature : Signature) :
    frozenEligible kind supplied (compile signature) = eligible kind supplied signature := by
  cases kind <;> simp [frozenEligible, compile, eligible]

theorem compiled_descriptors_equal_selected_source (kind : Kind) (supplied : Nat) (family : List Signature) :
    descriptorHolding kind supplied (family.map compile) = selectedHolding kind supplied family := by
  simp only [descriptorHolding, List.any_map, selectedHolding, select, holdBody,
    List.any_filter, Function.comp_def]
  congr 1
  funext signature
  rw [frozenEligible_compile]
  rfl

theorem descriptor_holding_has_the_source_judgment (kind : Kind) (supplied : Nat) (family : List Signature) :
    descriptorHolding kind supplied (family.map compile) = true ↔ HoldsBody kind supplied family := by
  rw [compiled_descriptors_equal_selected_source, selectedHolding_iff]

theorem activation_keeps_frozen_holding (instantiate : Signature → Signature)
    (kind : Kind) (supplied : Nat) (plans : List Plan) :
    descriptorHolding kind supplied (plans.map (activate instantiate)) = descriptorHolding kind supplied plans := by
  simp only [descriptorHolding, List.any_map, Function.comp_def]
  cases kind <;> rfl

theorem wrong_complete_arity_cannot_change_holding (supplied : Nat) (before after : List Signature)
    (signature : Signature) (different : signature.domains.length ≠ supplied) :
    selectedHolding .complete supplied (before ++ signature :: after) =
      selectedHolding .complete supplied (before ++ after) := by
  simp only [selectedHolding, irrelevant_declaration supplied before after signature different]

theorem holding_rename (names : String → String) (kind : Kind) (supplied : Nat) (family : List Signature) :
    selectedHolding kind supplied (family.map (renameSignature names)) = selectedHolding kind supplied family := by
  cases kind <;> simp [selectedHolding, select, eligible, holdBody, renameSignature, demand_rename,
    List.any_filter, Function.comp_def]

/-- The independently compiled complete protocol uses the same selected-family
holding as the independently defined source family. Effects, ordering and
terminal continuations are retained; body realization remains a service. -/
theorem complete_protocol_exact {State World Fault Pause Result : Type}
    (services : Services State World Fault Pause Result) (supplied : Nat) (family : List Signature) :
    alternatives ((compileDispatch (selectedHolding .complete supplied family) supplied family).map (execute services)) =
      sourceFamily services (select .complete supplied family) := by
  simp only [compileDispatch, selectedHolding, sourceFamily, List.map_map]
  apply alternatives_map_congr
  intro signature member
  exact compileCall_exact services _ signature

namespace Controls

def nullaryHeld : Signature := ⟨[], .symbol "Atom"⟩
def unaryChecked : Signature := ⟨[.symbol "Number"], .symbol "Number"⟩
def binaryHeld : Signature := ⟨[.symbol "Number", .symbol "Number"], .symbol "Atom"⟩
def variableResult : Signature := ⟨[.var "t"], .var "t"⟩

theorem complete_holding_is_source_arity_local :
    selectedHolding .complete 1 [nullaryHeld, unaryChecked] = false := by decide

theorem partial_holding_uses_its_selected_longer_declarations :
    selectedHolding .underApplied 1 [binaryHeld, unaryChecked] = true ∧
      selectedHolding .complete 1 [binaryHeld, unaryChecked] = false := by decide

theorem erasing_arity_holds_the_wrong_complete_body :
    holdBody [nullaryHeld, unaryChecked] = true ∧
      selectedHolding .complete 1 [nullaryHeld, unaryChecked] = false := by decide

theorem an_open_result_bound_to_Atom_does_not_change_its_frozen_mode :
    descriptorHolding .complete 1 [(activate (fun _ => ⟨[.symbol "Number"], .symbol "Atom"⟩) (compile variableResult))] = false := by decide

theorem reclassifying_an_activated_signature_is_a_wrong_mode_mutation :
    holdBody [((activate (fun _ => ⟨[.symbol "Number"], .symbol "Atom"⟩) (compile variableResult))).signature] = true ∧
      descriptorHolding .complete 1 [compile variableResult] = false := by decide

def modeServices : Services Unit Nat Unit Unit (List Nat)
  | .body held => fun state success pending _saved _fault _pause world => success state pending (world + if held then 0 else 1)
  | _ => done

def observe (held : Bool) (family : List Signature) : List Nat :=
  alternatives ((compileDispatch held 1 family).map (execute modeServices))
    () (fun _ pending world => world :: pending world) (fun _ => []) (fun _ => [])
    (fun _ _ => []) (fun _ _ => []) 0

theorem a_head_wide_holding_mutation_suppresses_a_required_body_effect :
    observe (selectedHolding .complete 1 [nullaryHeld, unaryChecked]) [nullaryHeld, unaryChecked] = [1] ∧
      observe (holdBody [nullaryHeld, unaryChecked]) [nullaryHeld, unaryChecked] = [0] := by decide

theorem repeated_applicable_occurrences_stay_repeated :
    observe (selectedHolding .complete 1 [unaryChecked, unaryChecked]) [unaryChecked, unaryChecked] = [1, 2] := by decide

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.SelectedBodyPolicy
