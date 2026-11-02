import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateStructuralProfile
import Mettapedia.Logic.HOL.PredicateSigmaControls

/-!
# Structural dispatch and selected identity-guard controls

Carrier dispatch is exercised with genuinely different component carriers.
Two pair layouts may share a result carrier; the unannotated projections are
then refused unless the profile chooses one. These dispatch controls do not
assert semantic pair laws for arbitrary lexical constants. The guarded identity
controls use the independent natural-index/tree-evidence model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.StructuralControls

open Mettapedia.Logic
open Presentation TypedEquality.Annotated
local infixr:60 " ⇒ " => HOL.Ty.arr

inductive Base where
  | first | second | packed
  deriving DecidableEq

inductive Symbol : HOL.Ty Base → Type where
  | named (name : Nat) (type : HOL.Ty Base) : Symbol type

def first : HOL.Ty Base := .base .first
def second : HOL.Ty Base := .base .second
def packed : HOL.Ty Base := .base .packed

def constant (name : Nat) (type : HOL.Ty Base) : HOL.ClosedTerm Symbol type := .const (.named name type)

def structural (projections : Bool) : (operator : StructuralOperator Base) →
    Option (Σ result : HOL.Ty Base, HOL.ClosedTerm Symbol (operator.codeType result))
  | .sigma (.base .first) (.base .second) => some ⟨packed, constant 2 _⟩
  | .pair (.base .first) (.base .second) => some ⟨packed, constant 3 _⟩
  | .pair (.base .second) (.base .first) =>
      if projections then none else some ⟨packed, constant 4 _⟩
  | .first (.base .packed) => if projections then some ⟨first, constant 5 _⟩ else none
  | .second (.base .packed) => if projections then some ⟨second, constant 6 _⟩ else none
  | .identity _endpoint => some ⟨packed, constant 7 _⟩
  | .reflexivity _endpoint => some ⟨packed, constant 8 _⟩
  | _ => none

def lexical (projections : Bool) : LexicalReading Nat Base Symbol where
  constCode? name :=
    if name = `first then some ⟨first, constant 0 first⟩
    else if name = `second then some ⟨second, constant 1 second⟩
    else none
  headCode? head :=
    if head = 0 then some ⟨first ⇒ .prop, HOL.PredicateProducts.full first⟩
    else if head = 1 then some ⟨second ⇒ .prop, HOL.PredicateProducts.full second⟩
    else none
  structuralCode? := structural projections

def pairSource : CTm Nat 0 := .pair (.const `first) (.const `second)
def reversePairSource : CTm Nat 0 := .pair (.const `second) (.const `first)

theorem heterogeneous_pair :
    Reader.infer? (lexical true) [] pairSource =
      some ⟨packed, .app (.app (constant 3 _) (constant 0 first)) (constant 1 second)⟩ := by
  apply Reader.infer?_complete
  exact .pair rfl (.constant rfl) (.constant rfl)

theorem heterogeneous_first :
    Reader.infer? (lexical true) [] (.fst pairSource) =
      some ⟨first, .app (constant 5 (packed ⇒ first))
        (.app (.app (constant 3 (first ⇒ second ⇒ packed)) (constant 0 first)) (constant 1 second))⟩ := by
  apply Reader.infer?_complete
  exact .first rfl (.pair rfl (.constant rfl) (.constant rfl))

theorem heterogeneous_second :
    Reader.infer? (lexical true) [] (.snd pairSource) =
      some ⟨second, .app (constant 6 (packed ⇒ second))
        (.app (.app (constant 3 (first ⇒ second ⇒ packed)) (constant 0 first)) (constant 1 second))⟩ := by
  apply Reader.infer?_complete
  exact .second rfl (.pair rfl (.constant rfl) (.constant rfl))

theorem heterogeneous_sigma :
    Reader.infer? (lexical true) [] (.sigma (.head 0) (.head 1)) =
      some ⟨packed ⇒ .prop, .app (.app (constant 2 _) (HOL.PredicateProducts.full first))
        (.lam (HOL.weakenCtx [first] (HOL.PredicateProducts.full second)))⟩ := by
  apply Reader.infer?_complete
  exact .dependentSum rfl (.head rfl) (.head rfl)

theorem two_layouts_are_readable :
    (Reader.infer? (lexical false) [] pairSource).isSome = true ∧
      (Reader.infer? (lexical false) [] reversePairSource).isSome = true := by
  decide +kernel

theorem ambiguous_projection_refused :
    Reader.infer? (lexical false) [] (.fst pairSource) = none ∧
      Reader.infer? (lexical false) [] (.snd reversePairSource) = none := by
  decide +kernel

theorem unsupported_pair_refused :
    Reader.infer? (lexical true) [] (.pair (.const `first) (.const `first)) = none := by
  decide +kernel

theorem mismatched_identity_refused :
    Reader.infer? (lexical true) [] (.id (.head 0) (.const `first) (.const `second)) = none := by
  decide +kernel

theorem endpoint_dependent_reflexivity :
    Reader.infer? (lexical true) [] (.refl (.const `second)) =
      some ⟨packed, .app (constant 8 _) (constant 1 second)⟩ := by
  apply Reader.infer?_complete
  exact .reflexivity rfl (.constant rfl)

theorem unreadable_reflexivity_refused :
    Reader.infer? (lexical true) [] (.refl (.const `missing)) = none := by
  decide +kernel

def legacy : LexicalReading Nat Base Symbol :=
  { lexical true with structuralCode? := fun _ => none }

theorem default_profile_refuses_structural_forms :
    Reader.infer? legacy [] pairSource = none ∧
    Reader.infer? legacy [] (.sigma (.head 0) (.head 1)) = none ∧
    Reader.infer? legacy [] (.id (.head 0) (.const `first) (.const `first)) = none ∧
    Reader.infer? legacy [] (.refl (.const `first)) = none := by
  decide +kernel

namespace GuardedIdentity
open HOL.PredicateSigma.Controls

def full : HOL.ClosedTerm Const (N ⇒ .prop) := HOL.PredicateProducts.full N
def empty : HOL.ClosedTerm Const (N ⇒ .prop) := .lam .bot

theorem equal_endpoints_admitted :
    (model.denote (.app (StructuralProfile.identityPredicate (.const .refl) full
      (.const .zero) (.const .zero)) (.const .refl))
      (fun index => nomatch index)).down := by
  rw [StructuralProfile.identity_denote]
  exact ⟨True.intro, True.intro, rfl, rfl⟩

theorem empty_domain_refused :
    ¬ (model.denote (.app (StructuralProfile.identityPredicate (.const .refl) empty
      (.const .zero) (.const .zero)) (.const .refl))
      (fun index => nomatch index)).down := by
  rw [StructuralProfile.identity_denote]
  exact fun impossible => impossible.1

end GuardedIdentity

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.StructuralControls
