import Mettapedia.SetTheory.Profiles.ProfileIndexedCalculusExtensions

/-!
# Occurrence and origin dependencies of profile deductions

The ledger distinguishes adopted-law occurrences from local assumptions.
It retains repeated syntactic uses and declaration origins. Formula equality
does not authorize discarding this information: two duplicate assumptions
can be consumed at different positions by the same logical rule.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileIndexedCalculus

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula)
open GraphRealizedDeduction (Proof)

universe u v

def hypothesisPositions {count : Nat} {assumptions : List (Formula count)} {body : Formula count}
    (proof : Proof assumptions body) : List Nat := (CommonCore.freeHypotheses proof).map Fin.val

theorem positions_transport_context {count : Nat} {first second : List (Formula count)}
    {body : Formula count} (same : first = second) (proof : Proof first body) :
    hypothesisPositions (same ▸ proof) = hypothesisPositions proof := by
  cases same
  rfl

theorem positions_mpr_context {count : Nat} {first second : List (Formula count)}
    {body : Formula count} (same : first = second) (changed : Proof first body = Proof second body)
    (proof : Proof second body) : hypothesisPositions (changed.mpr proof) = hypothesisPositions proof := by
  cases same
  simp

def Derivation.usedPositions {profile : Profile.{u}} {count : Nat}
    {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation profile assumptions body) : List Nat := hypothesisPositions derivation.proof

inductive Dependency (profile : Profile.{u}) where
  | adopted (position origin : Nat) (name : profile.RuleName)
  | local (position : Nat)

def Derivation.dependency {profile : Profile.{u}} {count : Nat}
    {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation profile assumptions body)
    (index : Fin (declarationFormulas derivation.declarations ++ assumptions).length) : Dependency profile :=
  if law : index.val < derivation.declarations.length then
    let declaration := derivation.declarations[index.val]
    .adopted index.val declaration.origin declaration.adoption.name
  else .local (index.val - derivation.declarations.length)

def Derivation.dependencies {profile : Profile.{u}} {count : Nat}
    {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation profile assumptions body) : List (Dependency profile) :=
  (CommonCore.freeHypotheses derivation.proof).map derivation.dependency

theorem translated_usedPositions {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count : Nat}
    {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation source assumptions body) :
    (translation.derivation derivation).usedPositions = derivation.usedPositions := by
  let same := congrArg (fun declarations => declarations ++ assumptions)
    (translated_declarationFormulas translation derivation.declarations)
  let changed := congrArg (fun context => Proof context body) same
  change hypothesisPositions (changed.mpr derivation.proof) = hypothesisPositions derivation.proof
  exact positions_mpr_context same changed derivation.proof

theorem adopted_origin_is_not_formula_identity {profile : Profile.{u}} {count : Nat}
    {body : Formula count} (adoption : Adoption profile body) :
    (⟨body, adoption, 0⟩ : Declaration profile count) ≠ ⟨body, adoption, 1⟩ := by
  intro same
  have impossible := congrArg Declaration.origin same
  exact Nat.zero_ne_one impossible

theorem same_formula_different_origins {profile : Profile.{u}} {count : Nat}
    {body : Formula count} (adoption : Adoption profile body) :
    declarationFormulas ([⟨body, adoption, 0⟩] : List (Declaration profile count)) =
      declarationFormulas [⟨body, adoption, 1⟩] := rfl

def duplicateLeft {profile : Profile.{u}} {count : Nat} (body : Formula count) :
    Derivation profile [body, body] body :=
  Derivation.logical (Proof.hypothesis (assumptions := [body, body]) 0)

def duplicateRight {profile : Profile.{u}} {count : Nat} (body : Formula count) :
    Derivation profile [body, body] body :=
  Derivation.logical (Proof.hypothesis (assumptions := [body, body]) 1)

theorem duplicate_dependencies_distinct {profile : Profile.{u}} {count : Nat} (body : Formula count) :
    (duplicateLeft (profile := profile) body).dependencies ≠
      (duplicateRight (profile := profile) body).dependencies := by
  change [Dependency.local 0] ≠ [Dependency.local 1]
  intro same
  have impossible : (0 : Nat) = 1 := Dependency.local.inj (List.cons.inj same).1
  exact Nat.zero_ne_one impossible

theorem repeated_cut_retains_repeated_use {count : Nat} (body : Formula count)
    {target : List (Formula count)} (replacement : Proof target body) :
    hypothesisPositions (substituteHypotheses
      (Proof.bothIntro (Proof.hypothesis (assumptions := [body]) 0)
        (Proof.hypothesis (assumptions := [body]) 0))
      (Fin.cases replacement (fun index => Fin.elim0 index))) =
    hypothesisPositions replacement ++ hypothesisPositions replacement := by
  simp only [substituteHypotheses, hypothesisPositions, CommonCore.freeHypotheses, List.map_append]
  rfl

end Mettapedia.SetTheory.Profiles.ProfileIndexedCalculus
