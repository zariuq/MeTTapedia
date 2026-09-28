import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Restriction

/-!
# Identity controls for the executable package

* **The base without identity elimination.** In a stage of the package that
  does not declare `id:eliminate`, an application of it has no type and no
  computation step: the name stays uninterpreted there. The eliminator's rule
  belongs to its declaration, and the package, which declares it, fires it.
* **No uniqueness of identity proofs by conversion.** A variable proof of
  `zero = zero` is not equal to `refl zero` in the package's typed equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Package (jName U0 numT)

/-! ## Typed applications have typed heads -/

section Heads

variable {R : Rules Tower.Head} {n : Nat} {Γ : Tower.Ctx n}

/-- The head of a typed application is typed. -/
theorem typed_spine_head :
    ∀ (args : List (Tower.Tm n)) {f T : Tower.Tm n}, Typed R Γ (appSpine f args) T →
      ∃ T', Typed R Γ f T'
  | [], _, _, typing => ⟨_, typing⟩
  | _ :: args, _, _, typing => by
      obtain ⟨_, typed⟩ := typed_spine_head args typing
      obtain ⟨_, _, tf, _, _⟩ := Typed.generation typed
      exact ⟨_, tf⟩

/-- A typed constant is declared. -/
theorem typed_const_declared {name : DeclName} {T : Tower.Tm n}
    (typing : Typed R Γ (.const name) T) : ∃ type, R.constantType name = some type := by
  obtain ⟨type, _, declared, _⟩ := Typed.generation typing
  exact ⟨type, declared⟩

end Heads

/-! ## The base without identity elimination -/

section Base

variable {allowed : DeclName → Bool} (jFree : allowed jName = false)
include jFree

/-- In a stage without `id:eliminate`, its applications have no type. -/
theorem jFree_untyped {n : Nat} {Γ : Tower.Ctx n} (args : List (Tower.Tm n)) {T : Tower.Tm n} :
    ¬ Typed (stage allowed) Γ (appSpine (.const jName) args) T := by
  intro typing
  obtain ⟨_, head⟩ := typed_spine_head args typing
  obtain ⟨type, declared⟩ := typed_const_declared head
  change (if allowed jName then allTypes jName else none) = some type at declared
  have absent : ¬ allowed jName = true := by
    rw [jFree]
    exact Bool.false_ne_true
  rw [if_neg absent] at declared
  cases declared

/-- In a stage without `id:eliminate`, its applications have no root step. -/
theorem jFree_no_step {n : Nat} (args : List (Tower.Tm n)) {r : Tower.Tm n} :
    ¬ (stage allowed).computation.step (appSpine (.const jName) args) r := by
  intro step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  obtain ⟨listed, present⟩ := List.mem_filter.mp mem
  obtain ⟨_, same⟩ := computations_headed entry listed h
  obtain ⟨names, _⟩ := appSpine_const_injective same
  have present' : allowed entry.1 = true := present
  rw [← names, jFree] at present'
  cases present'

end Base

/-- The stage of the natural numbers and their constructors declares no
identity elimination. -/
theorem ctorStage_jFree : allowedIn [numN, zeroN, sucN] jName = false := by decide

/-- The package declares identity elimination, and its rule fires at
reflexivity. -/
theorem j_fires {n : Nat} (a x f d y z : Tower.Tm n) :
    rules.computation.step (appSpine (.const jName) [a, x, f, d, y, .refl z]) d :=
  rules_step (listed 3 (by decide)) ⟨a, x, f, d, y, z, rfl, rfl⟩

/-! ## No uniqueness of identity proofs by conversion -/

/-- The context `p : zero = zero`. -/
abbrev pathCtx : Tower.Ctx 1 := .snoc .nil (.id numT (.const zeroN) (.const zeroN))

theorem pathCtx_formed : CtxFormed rules pathCtx := by
  have numMem : numN ∈ [numN, zeroN] := List.mem_cons_self ..
  have zeroMem : zeroN ∈ [numN, zeroN] := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have typed : Typed (stage (allowedIn [numN, zeroN])) .nil
      (.id numT (.const zeroN) (.const zeroN)) U0 :=
    idT (numT_typed numMem) (zero_typed numMem zeroMem) (zero_typed numMem zeroMem)
  exact .snoc .nil ⟨_, .sort _, Derivable.mono (stage_sub_rules _) typed⟩

/-- A variable proof of `zero = zero` is not `refl zero`. -/
theorem path_ne_refl :
    ¬ Equal rules pathCtx (.var 0) (.refl (.const zeroN)) (.id numT (.const zeroN) (.const zeroN)) :=
  Equal.neutral_ne_refl (S := setting fun _ => 0) (laws _) (constants _) (.var 0) pathCtx_formed

#print axioms jFree_untyped
#print axioms jFree_no_step
#print axioms j_fires
#print axioms path_ne_refl

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
