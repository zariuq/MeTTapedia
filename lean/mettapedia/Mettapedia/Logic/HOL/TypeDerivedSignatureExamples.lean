import Mettapedia.Logic.HOL.TypeDerivedSignature

/-!+# Concrete type-derived interpretations

The composition specimen changes both types and constant symbols, carries a
beta derivation through two arrows, and rejects an incorrectly ordered symbol
map. A separate sort-collapse arrow preserves proofs but fails to reflect them.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.TypeDerivedSignatureExamples

open CategoryTheory TypeDerivedSignature

/-- Each simple type has its own countable family of constant symbols. -/
abbrev source : TypeDerivedSignature := ⟨Unit, ⟨fun _ => Nat⟩⟩
abbrev middle : TypeDerivedSignature := ⟨Bool, ⟨fun _ => Nat⟩⟩
abbrev target : TypeDerivedSignature := ⟨Unit, ⟨fun _ => Nat⟩⟩

def first : source ⟶ middle where
  base _ := .arr (.base false) (.base true)
  constants n := n + 1

def second : middle ⟶ target where
  base b := if b then .base () else .prop
  constants n := 2 * n

theorem composite_type : (first ≫ second).base () = .arr .prop (.base ()) := rfl
theorem composite_constant : (first ≫ second).constants (a := .base ()) 3 = 8 := rfl

/-- A deliberately incorrect constant map with the same correctly composed types. -/
def wrongOrder : source ⟶ target where
  base _ := .arr .prop (.base ())
  constants n := 2 * n + 1

theorem wrongOrder_ne_composite : wrongOrder ≠ first ≫ second := by
  intro equal
  have values := congrArg
    (fun f : source ⟶ target =>
      (⟨Ty.substitute f.base (.base ()), f.constants (a := .base ()) 3⟩ :
        Σ a, target.2.Const a)) equal
  have impossible : (7 : Nat) = 8 := eq_of_heq (Sigma.mk.inj_iff.mp values).2
  exact (by decide : (7 : Nat) ≠ 8) impossible

def sourceBeta : ClosedFormula source.2.Const :=
  .eq (.app (.lam (.var .vz)) (.const (τ := .base ()) 3)) (.const 3)

def targetBeta : ClosedFormula target.2.Const :=
  .eq (.app (.lam (.var .vz)) (.const (τ := .arr .prop (.base ())) 8)) (.const 8)

theorem sourceBeta_provable : ExtDerivation.Theorem source.2.Const sourceBeta :=
  .beta (.const 3) (.var .vz)

theorem composed_sentence : sentence.map (first ≫ second) sourceBeta = targetBeta := rfl

/-- The existing beta proof travels through both actual interpretation arrows. -/
theorem targetBeta_provable : ExtDerivation.Theorem target.2.Const targetBeta := by
  rw [← composed_sentence]
  exact theorem_map (first ≫ second) sourceBeta_provable

theorem successive_sentence :
    sentence.map second (sentence.map first sourceBeta) = targetBeta :=
  (mapTypes_comp_closed first.base second.base first.constants second.constants sourceBeta).trans
    composed_sentence

abbrev twoSorts : TypeDerivedSignature := ⟨Bool, ⟨TypeSubstitutionExample.NoConstants Bool⟩⟩
abbrev oneSort : TypeDerivedSignature := ⟨Unit, ⟨TypeSubstitutionExample.NoConstants Unit⟩⟩
def collapse : twoSorts ⟶ oneSort :=
  ⟨TypeSubstitutionExample.collapseTypes,
    fun {a} => TypeSubstitutionExample.noConstantsMap TypeSubstitutionExample.collapseTypes (A := a)⟩

/-- Being an arrow of the signature category does not imply theorem reflection. -/
theorem collapse_not_reflecting :
    ExtDerivation.Theorem oneSort.2.Const
        (sentence.map collapse TypeSubstitutionExample.sourceClaim) ∧
      ¬ ExtDerivation.Theorem twoSorts.2.Const TypeSubstitutionExample.sourceClaim :=
  TypeSubstitutionExample.collapseTypes_does_not_reflect_theorems

#print axioms targetBeta_provable
#print axioms wrongOrder_ne_composite
#print axioms collapse_not_reflecting

end Mettapedia.Logic.HOL.TypeDerivedSignatureExamples
