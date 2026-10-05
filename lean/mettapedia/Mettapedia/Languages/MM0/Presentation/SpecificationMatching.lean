import Mettapedia.Languages.MM0.Presentation.SpecificationProgram

/-! # Authored declaration matching preserves kinds and complete payloads -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSpecification

open Kernel ComputationalContext ComputationalTyping ComputationalDefinitions
open ComputationalProof ComputationalDeclaration ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => specificationProgram
local notation "A" => specificationEquations
local notation "H" => dataEqualityHost

private theorem key_computes {α : Type} [DecidableEq α]
    (encodePayload : α → Term) (injective : Function.Injective encodePayload)
    (index actual : Nat) (payload stored : α) :
    Applies P H "nik:data-eq"
      [.list [natural index, encodePayload payload], .list [natural actual, encodePayload stored]]
      (boolean (decide (index = actual ∧ payload = stored))) := by
  apply Applies.primitive (by rfl)
  simp [dataEqualityHost, natural_injective.eq_iff, injective.eq_iff]

theorem body_match_computes (expected : Option Definition.Body) (body : Definition.Body) :
    Applies P H "mm0:spec-body" [encodeBodyResult expected, encodeBody body]
      (boolean (decide (expected = none ∨ expected = some body))) := by
  cases expected with
  | none => exact ⟨1, by rw [specification_apply _ (by decide)]; rfl⟩
  | some expected =>
      simp only [Option.some_ne_none, Option.some.injEq, false_or]
      refine specification_equation (equation := A[7]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (.primitive (by rfl) (dataEqualityHost_encoded encodeBody encodeBody_injective _ _))

private theorem and_reused (left right : Bool) :
    Applies P H "mm0:form-and" [boolean left, boolean right] (boolean (left && right)) :=
  admission_reused _ (by
    simp only [admissionProgram, ComputationalDefinitionAdmission.bodyProgram,
      ComputationalDefinitionAdmission.bodyBase, declarationProgram,
      Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (by decide))))) _ _ (and_imported left right)

theorem match_computes (entry : SpecificationEntry) (admission : Admission) :
    Applies P H "mm0:spec-match" [encodeEntry entry, encodeAdmission admission]
      (boolean (entry.checkMatch admission)) := by
  cases entry <;> cases admission
  all_goals first
    | exact ⟨1, by rw [specification_apply _ (by decide)]; rfl⟩
    | skip
  case sort.sort index payload actual stored =>
    refine specification_equation (equation := A[0]) (by decide) (by rfl) (by rfl) ?_
    exact Evaluates.call (by simp [Special])
      (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) .nil))
      (key_computes encodeSort encodeSort_injective index actual payload stored)
  case term.term index payload actual stored =>
    refine specification_equation (equation := A[1]) (by decide) (by rfl) (by rfl) ?_
    exact Evaluates.call (by simp [Special])
      (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) .nil))
      (key_computes encodeDeclaration encodeDeclaration_injective index actual payload stored)
  case definition.definition index payload expected actual stored body =>
    have combined : Applies P H "mm0:form-and"
        [boolean (decide (index = actual ∧ payload = stored)),
          boolean (decide (expected = none ∨ expected = some body))]
        (boolean ((SpecificationEntry.definition index payload expected).checkMatch
          (.definition actual stored body))) := by
      simpa only [SpecificationEntry.checkMatch, Bool.decide_and, Bool.and_assoc] using
        and_reused (decide (index = actual ∧ payload = stored))
          (decide (expected = none ∨ expected = some body))
    refine specification_equation (equation := A[2]) (by decide) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) combined
    · exact Evaluates.call (by simp [Special])
        (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
          (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) .nil))
        (key_computes encodeDeclaration encodeDeclaration_injective index actual payload stored)
    · exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (body_match_computes expected body)
  case axiomDecl.axiomDecl index payload actual stored =>
    refine specification_equation (equation := A[3]) (by decide) (by rfl) (by rfl) ?_
    exact Evaluates.call (by simp [Special])
      (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) .nil))
      (key_computes encodeTheorem encodeTheorem_injective index actual payload stored)
  case theoremDecl.theoremDecl index payload actual stored dummies proof =>
    refine specification_equation (equation := A[4]) (by decide) (by rfl) (by rfl) ?_
    exact Evaluates.call (by simp [Special])
      (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (.cons (Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) .nil))
      (key_computes encodeTheorem encodeTheorem_injective index actual payload stored)

theorem auxiliary_computes (admission : Admission) :
    Applies P H "mm0:spec-auxiliary" [encodeAdmission admission]
      (boolean (ProofDeclaration.auxiliary admission)) := by
  cases admission <;> exact ⟨1, by rw [specification_apply _ (by decide)]; rfl⟩

private theorem guard_computes (allowed : Bool) (pending : List SpecificationEntry) :
    Applies P H "mm0:spec-guard" [boolean allowed, encodeEntries pending]
      (encodePendingResult (if allowed then some pending else none)) := by
  cases allowed <;> exact ⟨2, by rw [specification_apply _ (by decide)]; rfl⟩

theorem public_computes (pending : List SpecificationEntry) (admission : Admission) :
    Applies P H "mm0:spec-public" [listView (pending.map encodeEntry), encodeAdmission admission]
      (encodePendingResult (match pending with
        | [] => none
        | expected :: remaining => if expected.checkMatch admission then some remaining else none)) := by
  cases pending with
  | nil => exact ⟨1, by rw [specification_apply _ (by decide)]; rfl⟩
  | cons entry rest =>
      refine specification_equation (equation := A[16]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) .nil)) (guard_computes (entry.checkMatch admission) rest)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (match_computes entry admission)

theorem pending_computes (pending : List SpecificationEntry) (declaration : ProofDeclaration) :
    Applies P H "mm0:spec-pending"
      [boolean declaration.isLocal, encodeEntries pending, encodeAdmission declaration.admission]
      (encodePendingResult (if declaration.isLocal then
          if ProofDeclaration.auxiliary declaration.admission then some pending else none
        else match pending with
          | [] => none
          | expected :: remaining => if expected.checkMatch declaration.admission then some remaining else none)) := by
  rcases declaration with ⟨admission, flag⟩
  cases flag with
  | true =>
      refine specification_equation (equation := A[11]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) .nil)) (guard_computes (ProofDeclaration.auxiliary admission) pending)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (auxiliary_computes admission)
  | false =>
      refine specification_equation (equation := A[12]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) .nil)) (public_computes pending admission)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
        (.primitive (by rfl) (by rfl))

theorem match_accepts_iff (entry : SpecificationEntry) (admission : Admission) :
    Applies P H "mm0:spec-match" [encodeEntry entry, encodeAdmission admission] (.sym "True") ↔
      SpecificationEntry.Matches entry admission := by
  constructor
  · intro accepted
    have same := accepted.deterministic (match_computes entry admission)
    apply (SpecificationEntry.checkMatch_iff _ _).mp
    cases checked : entry.checkMatch admission with
    | false => simp [checked, boolean] at same
    | true => rfl
  · intro matched
    simpa [(SpecificationEntry.checkMatch_iff _ _).mpr matched, boolean] using match_computes entry admission

end Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
