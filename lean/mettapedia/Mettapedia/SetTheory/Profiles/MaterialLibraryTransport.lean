import Mettapedia.SetTheory.CarveOuts.Sites.GSets
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSet

/-!
# Material library contracts transported through membership isomorphisms

A membership isomorphism preserves and reflects the complete first-order
material language, including its quantifiers. It transports qualified values
without forgetting the value on which a dependent contract was checked.

The concrete isomorphism is between `ZFSet` and the well-founded part of
`HSet`. Quantifiers on the hyperset side range over that part. Extending them
to all hypersets changes the theory: a self-member exists in `HSet`, while
neither well-founded carrier has one. This comparison does not supply an
interpretation of an arbitrary foreign higher-order signature.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.MaterialLibraryTransport

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)

universe u v

variable {A : Type u} {B : Type v} {left : A → A → Prop} {right : B → B → Prop}

theorem map_extend (comparison : left ≃r right) {n : Nat}
    (environment : Fin n → A) (value : A) :
    (fun index => comparison (Fin.cases value environment index)) =
      Fin.cases (comparison value) (fun index => comparison (environment index)) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Surjectivity is used at the quantifiers; an injective membership embedding
alone is insufficient for this statement. -/
theorem tarski_iff (comparison : left ≃r right) {n : Nat}
    (formula : Formula n) (environment : Fin n → A) :
    Tarski right formula (fun index => comparison (environment index)) ↔
      Tarski left formula environment := by
  induction formula with
  | bottom => exact Iff.rfl
  | equal first second => exact comparison.injective.eq_iff
  | member child parent => exact comparison.map_rel_iff
  | both first second ihFirst ihSecond => exact and_congr (ihFirst environment) (ihSecond environment)
  | either first second ihFirst ihSecond => exact or_congr (ihFirst environment) (ihSecond environment)
  | imply first second ihFirst ihSecond => exact imp_congr (ihFirst environment) (ihSecond environment)
  | all body ih =>
      change (∀ value, Tarski right body (Fin.cases value
        (fun index => comparison (environment index)))) ↔
        ∀ value, Tarski left body (Fin.cases value environment)
      constructor
      · intro holds value
        have mapped := holds (comparison value)
        rw [← map_extend] at mapped
        exact (ih _).mp mapped
      · intro holds value
        obtain ⟨original, rfl⟩ := comparison.surjective value
        rw [← map_extend]
        exact (ih _).mpr (holds original)
  | exist body ih =>
      change (∃ value, Tarski right body (Fin.cases value
        (fun index => comparison (environment index)))) ↔
        ∃ value, Tarski left body (Fin.cases value environment)
      constructor
      · rintro ⟨value, holds⟩
        obtain ⟨original, rfl⟩ := comparison.surjective value
        rw [← map_extend] at holds
        exact ⟨original, (ih _).mp holds⟩
      · rintro ⟨value, holds⟩
        refine ⟨comparison value, ?_⟩
        rw [← map_extend]
        exact (ih _).mpr holds

/-- A checked material predicate is a dependent contract on the transported
value. The inverse returns the original value, not a replacement witness. -/
def qualifiedValues (comparison : left ≃r right) {n : Nat}
    (body : Formula (n + 1)) (environment : Fin n → A) :
    {value : A // Tarski left body (Fin.cases value environment)} ≃
      {value : B // Tarski right body (Fin.cases value
        (fun index => comparison (environment index)))} where
  toFun value := ⟨comparison value.1, by
    rw [← map_extend]
    exact (tarski_iff comparison body _).mpr value.2⟩
  invFun value := ⟨comparison.symm value.1, by
    apply (tarski_iff comparison body _).mp
    rw [map_extend, comparison.apply_symm_apply]
    exact value.2⟩
  left_inv value := Subtype.ext (comparison.symm_apply_apply value.1)
  right_inv value := Subtype.ext (comparison.apply_symm_apply value.1)

@[simp] theorem qualifiedValues_value (comparison : left ≃r right) {n : Nat}
    (body : Formula (n + 1)) (environment : Fin n → A)
    (value : {value : A // Tarski left body (Fin.cases value environment)}) :
    (qualifiedValues comparison body environment value).1 = comparison value.1 := rfl

def wellFoundedMembership : WellFoundedPart.{u} → WellFoundedPart.{u} → Prop :=
  fun child parent => child.1 ∈ parent.1

/-- This is constructed from the actual well-founded comparison and its
membership theorem. It is not a postulated library-interpretation interface. -/
def wellFoundedIso : wellFoundedMembership.{u} ≃r (fun x y : ZFSet.{u} => x ∈ y) where
  toEquiv := HSet.wellFoundedPartEquivZFSet
  map_rel_iff' := HSet.wellFoundedPartEquivZFSet_mem_iff

theorem wellFounded_formula_iff {n : Nat} (formula : Formula n)
    (environment : Fin n → WellFoundedPart.{u}) :
    Tarski (fun x y : ZFSet.{u} => x ∈ y) formula
        (fun index => HSet.toZFSet (environment index).1) ↔
      Tarski wellFoundedMembership formula environment :=
  tarski_iff wellFoundedIso formula environment

def selfMemberSentence : Formula 0 := .exist (.member 0 0)

theorem wellFounded_no_selfMember (environment : Fin 0 → WellFoundedPart.{u}) :
    ¬ Tarski wellFoundedMembership selfMemberSentence environment := by
  rintro ⟨value, self⟩
  exact value.2.notMem_self self

theorem hyperset_selfMember (environment : Fin 0 → HSet.{u}) :
    Tarski (fun x y : HSet.{u} => x ∈ y) selfMemberSentence environment :=
  ⟨HSet.quineAtom, HSet.quineAtom_mem_self⟩

/-- Extending a well-founded library's quantifiers to the whole hyperset
carrier is not formula preservation. -/
theorem unrestricted_transport_refused :
    ¬ ∀ {n : Nat} (formula : Formula n) (environment : Fin n → ZFSet.{u}),
      Tarski (fun x y : HSet.{u} => x ∈ y) formula
          (fun index => HSet.ofZFSet (environment index)) ↔
        Tarski (fun x y : ZFSet.{u} => x ∈ y) formula environment := by
  intro preserves
  obtain ⟨value, self⟩ := (preserves selfMemberSentence Fin.elim0).mp
    (hyperset_selfMember _)
  exact ZFSet.mem_irrefl value self

end Mettapedia.SetTheory.Profiles.MaterialLibraryTransport
