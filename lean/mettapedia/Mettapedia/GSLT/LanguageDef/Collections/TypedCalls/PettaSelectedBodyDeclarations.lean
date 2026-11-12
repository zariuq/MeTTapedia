import Mettapedia.Languages.MeTTa.PeTTa.SelectedBodyPolicy
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyEntry

/-!
# Selected body modes read the actual literal source declarations

The source witness is an arrow declaration at a symbol subject, with its
source arity intact. Existing annotation and arrow destructors read those
witnesses; their computed family is not a second typing relation. The
result-passing compiler's complete-body selector and the frozen descriptor
selector agree on this source readout.

These are literal body-mode laws. Intrinsic declaration precedence, native
family caching and explicit execution escapes retain their own obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyDeclarations

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open CallGuardOptimization CallArityDispatch SelectedBodyPolicy

def decode (type : Atom) : Option CallGuardOptimization.Signature := do
  let domains ← Mettapedia.Languages.MeTTa.HE.getFunctionArgTypes type
  let codomain ← Mettapedia.Languages.MeTTa.HE.getFunctionRetType type
  pure ⟨domains, codomain⟩

theorem arrow_parts_iff (type : Atom) (signature : CallGuardOptimization.Signature) :
    (Mettapedia.Languages.MeTTa.HE.getFunctionArgTypes type = some signature.domains ∧
      Mettapedia.Languages.MeTTa.HE.getFunctionRetType type = some signature.codomain) ↔
      type = signature.scheme := by
  cases signature with
  | mk domains codomain =>
    cases type with
    | symbol _ | var _ | grounded _ =>
      simp [Mettapedia.Languages.MeTTa.HE.getFunctionArgTypes,
        Mettapedia.Languages.MeTTa.HE.getFunctionRetType, Signature.scheme]
    | expression items =>
      cases items with
      | nil =>
        simp [Mettapedia.Languages.MeTTa.HE.getFunctionArgTypes,
          Mettapedia.Languages.MeTTa.HE.getFunctionRetType, Signature.scheme]
      | cons operator types =>
        cases operator with
        | var _ | grounded _ | expression _ =>
          simp [Mettapedia.Languages.MeTTa.HE.getFunctionArgTypes,
            Mettapedia.Languages.MeTTa.HE.getFunctionRetType, Signature.scheme]
        | symbol name =>
          by_cases arrow : name = "->"
          · subst name
            cases types using List.reverseRecOn with
            | nil =>
              simp [Mettapedia.Languages.MeTTa.HE.getFunctionArgTypes,
                Mettapedia.Languages.MeTTa.HE.getFunctionRetType, Signature.scheme]
            | append_singleton parameters returned =>
              simp [Mettapedia.Languages.MeTTa.HE.getFunctionArgTypes,
                Mettapedia.Languages.MeTTa.HE.getFunctionRetType, Signature.scheme]
          · simp [Mettapedia.Languages.MeTTa.HE.getFunctionArgTypes,
              Mettapedia.Languages.MeTTa.HE.getFunctionRetType, Signature.scheme, arrow]

theorem decode_iff (type : Atom) (signature : CallGuardOptimization.Signature) :
    decode type = some signature ↔ type = signature.scheme := by
  rw [← arrow_parts_iff]
  constructor
  · intro parsed
    simp only [decode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨domains, arguments, codomain, result, same⟩ := parsed
    cases same
    exact ⟨arguments, result⟩
  · rintro ⟨arguments, result⟩
    simp [decode, arguments, result]

def family (program : SpaceSemantics.Program) (head : String) : List CallGuardOptimization.Signature :=
  (PettaSourceTypeRows.annotations program.declarations (.symbol head)).filterMap decode

theorem literal_annotation_iff (rows : List Atom) (head : String) (type : Atom) :
    type ∈ PettaSourceTypeRows.annotations rows (.symbol head) ↔
      .expression [.symbol ":", .symbol head, type] ∈ rows := by
  simp only [PettaSourceTypeRows.annotations, Mettapedia.Languages.MeTTa.HE.getAnnotatedTypes,
    List.mem_filterMap]
  constructor
  · rintro ⟨row, present, selected⟩
    split at selected
    · rename_i subject actualType
      split at selected
      · rename_i same
        have subjectEq := beq_iff_eq.mp same
        have typeEq := Option.some.inj selected
        simpa only [subjectEq, typeEq] using present
      · cases selected
    · cases selected
  · intro present
    exact ⟨_, present, by simp⟩

theorem family_member_iff (program : SpaceSemantics.Program) (head : String)
    (signature : CallGuardOptimization.Signature) :
    signature ∈ family program head ↔
      .expression [.symbol ":", .symbol head, signature.scheme] ∈ program.declarations := by
  simp [family, List.mem_filterMap, decode_iff, literal_annotation_iff]

/-- The compiler's Boolean reflects literal source evidence, rather than
being used as the definition of that evidence. -/
theorem rawOutput_iff (program : SpaceSemantics.Program) (head : String) (arity : Nat) :
    OutputPlan.rawOutput program head arity = true ↔ HoldsBody .complete arity (family program head) := by
  constructor
  · intro held
    obtain ⟨row, present, selected⟩ := List.any_eq_true.mp held
    split at selected
    · rename_i name types
      simp only [Bool.and_eq_true, beq_iff_eq] at selected
      obtain ⟨⟨named, lengthEq⟩, result⟩ := selected
      subst name
      cases types using List.reverseRecOn with
      | nil => simp at lengthEq
      | append_singleton parameters returned =>
        have arityEq : parameters.length = arity := by simpa using lengthEq
        have returnedEq : returned = .symbol "Atom" := by simpa [← arityEq] using result
        subst returned
        exact .selected ⟨parameters, .symbol "Atom"⟩
          ((family_member_iff ..).mpr present) (.complete arityEq) rfl
    · cases selected
  · intro held
    cases held with
    | selected signature member admitted literal =>
      have arityEq := (applicable_iff arity .complete signature).mp admitted
      apply List.any_eq_true.mpr
      refine ⟨_, (family_member_iff ..).mp member, ?_⟩
      simp [Signature.scheme, literal, ← arityEq]

theorem source_mode_eq_selected_family (program : SpaceSemantics.Program) (head : String) (arity : Nat) :
    OutputPlan.rawOutput program head arity = selectedHolding .complete arity (family program head) := by
  apply Bool.eq_iff_iff.mpr
  exact (rawOutput_iff program head arity).trans (selectedHolding_iff ..).symm

theorem frozen_descriptors_eq_compiler_mode (program : SpaceSemantics.Program) (head : String) (arity : Nat) :
    descriptorHolding .complete arity ((family program head).map compile) =
      OutputPlan.rawOutput program head arity := by
  rw [compiled_descriptors_equal_selected_source, source_mode_eq_selected_family]

theorem activated_descriptors_eq_compiler_mode (program : SpaceSemantics.Program) (head : String) (arity : Nat)
    (instantiate : CallGuardOptimization.Signature → CallGuardOptimization.Signature) :
    descriptorHolding .complete arity (((family program head).map compile).map (activate instantiate)) =
      OutputPlan.rawOutput program head arity := by
  rw [activation_keeps_frozen_holding, frozen_descriptors_eq_compiler_mode]

/-- Actual source readout earns the held formation mode, including overloads.
Execution of this formed plan is the already proved quote boundary. This is
not a claim that the native driver implements the complete formation relation. -/
theorem selected_formation_executes_quote {context : OutputPlan.Context}
    {equation : SpaceSemantics.Equation} {result : OutputPlan.Result}
    (formed : OutputPlan.EquationBodyRel context equation result)
    (held : descriptorHolding .complete equation.arguments.length
      ((family context.source equation.head).map compile) = true) :
    (OutputPlan.normalized result).execute = OutputPlan.hold equation.body := by
  have raw : OutputPlan.rawOutput context.source equation.head equation.arguments.length = true := by
    simpa only [frozen_descriptors_eq_compiler_mode] using held
  exact PettaHeldBodyReturn.held_formation_executes_quote formed raw

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyDeclarations
