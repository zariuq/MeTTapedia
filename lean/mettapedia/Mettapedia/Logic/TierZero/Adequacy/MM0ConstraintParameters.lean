import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingTheoremApplication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTProtectedParameters

/-!
# The actual MM0 encoding is rigid in its declared ambient interface

MM0 bound variables are ABT indices, and regular variables carry their
declared dependency indices. Existing support theorems prove that the actual
encodings are fixed by the generic protected-ambient substitution action.
This is not an assertion that every raw ABT is ground: loose indices remain
mobile, and the exact decoder still refuses an undeclared loose index.

This module proves the rigidity boundary only. It supplies neither a new
MM0 proof interpreter nor the remaining schema-admission/reachability bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintParameters

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open MM0ContextualSupport

abbrev action (context : Context) := ABTProtectedParameters.action (Head := Head) context.length

/-- The representation of an undeclared object variable is an opaque guest
head. Scope protection alone therefore does not certify sorting. -/
theorem all_encoded_expressions_supported {sorts : SortSignature} {context : Context}
    (formed : Context.WellFormed sorts context) (expression : Preterm) :
    Term.supportedAt context.length (encode context expression) = true := by
  induction expression with
  | var index =>
      cases lookup : context[index]? with
      | none => simp [encode, encodeVariable, lookup, Term.supportedAt, Term.Fields.supportedAt]
      | some binder =>
          cases binder with
          | bound sort => exact encode_supported formed (.bound lookup)
          | regular sort dependencies => exact encode_supported formed (.regular lookup)
  | term symbol => rfl
  | app function argument ihFunction ihArgument =>
      simp [encode, Term.supportedAt, Term.Fields.supportedAt, ihFunction, ihArgument]

theorem all_encoded_expressions_fixed {sorts : SortSignature} {context : Context}
    (formed : Context.WellFormed sorts context) (expression : Preterm) :
    FixedMatching.Fixed (action context) (encode context expression) :=
  ABTProtectedParameters.fixed_of_supported _ _ (all_encoded_expressions_supported formed expression)

theorem encoded_expression_fixed {sorts : SortSignature} {context : Context}
    (formed : Context.WellFormed sorts context) {expression : Preterm} {support : Finset Nat}
    (supported : Preterm.Supports context expression support) :
    FixedMatching.Fixed (action context) (encode context expression) :=
  ABTProtectedParameters.fixed_of_supported _ _ (encode_supported formed supported)

theorem typed_expression_fixed {sorts : SortSignature} {signature : TermSignature}
    {context remaining : Context} (formed : Context.WellFormed sorts context)
    {expression : Preterm} {sort : Nat}
    (typed : Preterm.HasType signature context expression remaining sort) :
    FixedMatching.Fixed (action context) (encode context expression) :=
  ABTProtectedParameters.fixed_of_supported _ _ (encode_typed_supported formed typed)

theorem judgment_fixed (width : Nat) (tag : String) (terms : List MM0Rewriting.Tm)
    (supported : ∀ term ∈ terms, Term.supportedAt width term = true) :
    FixedMatching.Fixed (ABTProtectedParameters.action width) (MM0Rewriting.judgment tag terms) := by
  apply ABTProtectedParameters.fixed_of_supported
  exact (MM0Rewriting.fields_supported width terms).mpr supported

theorem proof_value_fixed {sorts : SortSignature} {signature : TermSignature}
    {context remaining : Context} (formed : Context.WellFormed sorts context)
    {expression : Preterm} {sort : Nat}
    (typed : Preterm.HasType signature context expression remaining sort) :
    FixedMatching.Fixed (action context) (MM0Rewriting.proofValue context expression) := by
  apply judgment_fixed
  intro term member
  have same : term = encode context expression := List.mem_singleton.mp member
  subst term
  exact encode_typed_supported formed typed

theorem proof_value_fixed_of_context {sorts : SortSignature} {context : Context}
    (formed : Context.WellFormed sorts context) (expression : Preterm) :
    FixedMatching.Fixed (action context) (MM0Rewriting.proofValue context expression) := by
  apply judgment_fixed
  intro term member
  have same : term = encode context expression := List.mem_singleton.mp member
  subst term
  exact all_encoded_expressions_supported formed expression

theorem encoded_request_fixed_of_context {sorts : SortSignature} {context : Context}
    (formed : Context.WellFormed sorts context) (name : String) (arguments : List Preterm) :
    FixedMatching.Fixed (action context)
      (MM0Rewriting.requestValue name (arguments.map (encode context))) := by
  apply judgment_fixed
  intro term member
  obtain ⟨argument, _, rfl⟩ := List.mem_map.mp member
  exact all_encoded_expressions_supported formed argument

theorem admitted_request_fixed {sorts : SortSignature} {signature : TermSignature}
    {formal context : Context} (formed : Context.WellFormed sorts context)
    (name : String) {arguments : List Preterm}
    (admitted : Substitution.Admissible signature formal context arguments) :
    FixedMatching.Fixed (action context)
      (MM0Rewriting.requestValue name (arguments.map (encode context))) := by
  apply judgment_fixed
  intro term member
  obtain ⟨argument, present, rfl⟩ := List.mem_map.mp member
  exact MM0Rewriting.admitted_arguments_supported formed admitted argument present

namespace Controls

def dependentContext : Context := [.bound 0, .regular 0 {0}]

theorem a_regular_variable_keeps_its_actual_dependency_index :
    FixedMatching.Fixed (action dependentContext) (encode dependentContext (.var 1)) := by
  apply ABTProtectedParameters.fixed_of_supported
  decide +kernel

theorem an_ambient_bound_variable_is_protected :
    FixedMatching.Fixed (action [.bound 0]) (encode [.bound 0] (.var 0)) := by
  apply ABTProtectedParameters.fixed_of_supported
  decide +kernel

theorem raw_loose_indices_remain_mobile :
    ¬FixedMatching.Fixed (action dependentContext) (.idx 2) :=
  ABTProtectedParameters.the_boundary_index_is_not_fixed 2

theorem a_mobile_raw_index_is_not_an_admitted_guest_variable :
    MM0Rewriting.decodeExact [.bound 0] (.idx 1) = none := by
  simp [MM0Rewriting.decodeExact, decode, encode, encodeVariable]

theorem an_opaque_undeclared_code_is_fixed :
    FixedMatching.Fixed (action []) (encode [] (.var 1)) := by
  apply ABTProtectedParameters.fixed_of_supported
  decide +kernel

theorem fixedness_does_not_supply_sorting (signature : TermSignature) :
    ¬∃ remaining sort, Preterm.HasType signature [] (.var 1) remaining sort := by
  rintro ⟨remaining, sort, typed⟩
  have bounded := typed.varsBelow
  simp [Preterm.VarsBelow] at bounded

end Controls

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintParameters
