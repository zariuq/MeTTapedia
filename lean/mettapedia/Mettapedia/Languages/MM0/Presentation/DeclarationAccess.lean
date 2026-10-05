import Mettapedia.Languages.MM0.Presentation.DeclarationProgram

/-! # Shared computations used by MM0 declaration admission -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalConversion ComputationalProof
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => declarationProgram
local notation "A" => declarationEquations
local notation "H" => dataEqualityHost

theorem argument_reused (head : String) (used : head ∈ argumentProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies argumentProgram computationalHost head arguments result) :
    Applies P H head arguments result := by
  have inUnfolding : head ∈ unfoldingProgram.calledHeads := by
    simp only [unfoldingProgram, ComputationalInstantiation.instantiationProgram,
      ComputationalAdmissible.admissibleProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl (Or.inl (Or.inl used))
  have inConversion : head ∈ conversionProgram.calledHeads := by
    simp only [conversionProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl inUnfolding
  have inProof : head ∈ proofProgram.calledHeads := by
    simp only [proofProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl inConversion
  exact proof_reused head inProof _ _
    (ComputationalProof.conversion_reused head inConversion _ _
      (ComputationalConversion.argument_reused head used _ _ computed))

theorem typing_reused (head : String) (used : head ∈ typingProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies typingProgram computationalHost head arguments result) :
    Applies P H head arguments result := by
  let tail := listAppendProgram ++ ComputationalSupport.supportEquations ++ naturalMembershipProgram ++
    ComputationalDependency.dependencyEquations ++ argumentEquations
  have run := (Applies.append_iff typingProgram tail computationalHost (by decide)
    head used _ _).mpr computed
  apply argument_reused head (by
    simp only [argumentProgram, ComputationalDependency.dependencyProgram,
      ComputationalSupport.supportProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl (Or.inl (Or.inl used)))
  simpa only [argumentProgram, ComputationalDependency.dependencyProgram,
    ComputationalSupport.supportProgram, tail, List.append_assoc] using run

theorem lookup_reused {α : Type} (encode : α → Term) (table : List (Nat × α)) (index : Nat) :
    Applies P H "nik:nat-table-get" [encodeNaturalTable encode table, natural index]
      (encodeLookupResult ((table.lookup index).map encode)) := by
  have run := (Applies.frame_iff naturalLookupProgram
    (ComputationalInstantiation.instantiationProgram ++ ComputationalFreshDummies.freshEquations) unfoldingEquations
    computationalHost (by decide) (by decide) "nik:nat-table-get" (by decide) _ _).mpr
      (natural_lookup_computes encode table index)
  have inUnfolding : Applies unfoldingProgram computationalHost "nik:nat-table-get"
      [encodeNaturalTable encode table, natural index]
      (encodeLookupResult ((table.lookup index).map encode)) := by
    simpa only [unfoldingProgram, List.append_assoc] using run
  have used : "nik:nat-table-get" ∈ unfoldingProgram.calledHeads := by
    simp only [unfoldingProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  have inConversion : "nik:nat-table-get" ∈ conversionProgram.calledHeads := by
    simp only [conversionProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl used
  have inProof : "nik:nat-table-get" ∈ proofProgram.calledHeads := by
    simp only [proofProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl inConversion
  exact proof_reused _ inProof _ _
    (ComputationalProof.conversion_reused _ inConversion _ _
      (ComputationalConversion.unfolding_reused _ used _ _ inUnfolding))

theorem append_reused (left right : List Term) :
    Applies P H "nik:list-append" [.list left, .list right] (.list (left ++ right)) := by
  let suffix := ComputationalSupport.supportEquations ++ naturalMembershipProgram ++
    ComputationalDependency.dependencyEquations ++ argumentEquations
  have run := (Applies.frame_iff listAppendProgram typingProgram suffix computationalHost
    (by decide) (by decide) "nik:list-append" (by decide) _ _).mpr (list_append_computes left right)
  apply argument_reused _ (by decide)
  simpa only [argumentProgram, ComputationalDependency.dependencyProgram,
    ComputationalSupport.supportProgram, suffix, List.append_assoc] using run

theorem view_computes (values : List Term) :
    Applies P H "nik:list-view" [.list values] (listView values) :=
  .primitive (by rfl) (by rfl)

theorem not_computes (value : Bool) :
    Applies P H "mm0:form-not" [boolean value] (boolean (!value)) := by
  cases value <;> exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩

theorem and_computes (left right : Bool) :
    Applies P H "mm0:form-and" [boolean left, boolean right] (boolean (left && right)) := by
  cases left <;> exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩

theorem bound_item_computes (binder : Option Kernel.Binder) :
    Applies P H "mm0:form-bound-item" [encodeBinderResult binder]
      (boolean (match binder with | some (.bound _) => true | _ => false)) := by
  cases binder with
  | none => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | some binder => cases binder <;> exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩

theorem bound_index_computes (context : Context) (index : Nat) :
    Applies P H "mm0:form-bound-index" [encodeContext context, natural index]
      (boolean (Context.isBound context index)) := by
  refine declaration_equation (equation := A[4]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (bound_item_computes context[index]?)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (typing_reused _ (by decide) _ _ (context_lookup_computes context index))

inductive SortUse where
  | bound | regular | result | statement | dummy

def SortUse.name : SortUse → String
  | .bound => "Bound"
  | .regular => "Regular"
  | .result => "Result"
  | .statement => "Statement"
  | .dummy => "Dummy"

def SortUse.allows : SortUse → SortInfo → Bool
  | .bound, info => !info.strict
  | .regular, _ => true
  | .result, info => !info.pure
  | .statement, info => info.provable
  | .dummy, info => !info.strict && !info.free

theorem sort_info_computes (info : Option SortInfo) (use : SortUse) :
    Applies P H "mm0:form-sort-info" [encodeLookupResult (info.map encodeSort), .sym use.name]
      (boolean (info.any use.allows)) := by
  cases info with
  | none => cases use <;> exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | some info =>
      cases use with
      | regular => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
      | statement => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
      | bound =>
          refine declaration_equation (equation := A[15]) (by decide) (by rfl) (by rfl) ?_
          exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (not_computes info.strict)
      | result =>
          refine declaration_equation (equation := A[17]) (by decide) (by rfl) (by rfl) ?_
          exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (not_computes info.pure)
      | dummy =>
          refine declaration_equation (equation := A[19]) (by decide) (by rfl) (by rfl) ?_
          refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) (and_computes (!info.strict) (!info.free))
          · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (not_computes info.strict)
          · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (not_computes info.free)

theorem sort_computes (sorts : SortTable) (sort : Nat) (use : SortUse) :
    Applies P H "mm0:form-sort" [encodeSorts sorts, natural sort, .sym use.name]
      (boolean ((sortsOf sorts sort).any use.allows)) := by
  refine declaration_equation (equation := A[13]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (sort_info_computes _ use)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (lookup_reused encodeSort sorts sort)

end Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration
