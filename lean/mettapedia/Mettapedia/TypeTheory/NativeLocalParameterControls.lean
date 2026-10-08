import Mettapedia.TypeTheory.NativeLocalTypeFormers
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

/-!
# Varying native parameter-space controls

The domain has one or two arguments according to the supplied Boolean
context. The codomain has `n + 1` witnesses at an argument whose value is
`n`. Its name is an actual natural map on the total argument context.
The universal parameter-space evaluator recovers that map, and a
nonidentity context substitution changes the argument domain. Erasing the
name changes the decoded domain and cannot preserve the original family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.NativeLocalParameterControls

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers

abbrev World := Discrete PUnit.{1}

def world : Worldᵒᵖ := Opposite.op (Discrete.mk PUnit.unit)
abbrev constant (carrier : Type) : Face.{0, 0, 0} World where
  obj _ := carrier
  map _ := 𝟙 carrier
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev booleans : Face.{0, 0, 0} World := constant Bool
abbrev naturals : Face.{0, 0, 0} World := constant Nat

abbrev finiteFibre : DisplayedFamily.{0, 0, 0, 0} naturals where
  obj point := Fin (point.2 + 1)
  map {source target} arrow := TypeCat.ofHom fun value =>
    Fin.cast (congrArg (fun n : Nat => n + 1) arrow.property) value
  map_id _ := by ext value; rfl
  map_comp _ _ := by ext value; rfl

def sizeName : booleans ⟶ naturals where
  app _ := TypeCat.ofHom fun value => if value then 1 else 0
  naturality := by intros; rfl

abbrev domain : NativeType booleans := ⟨naturals, finiteFibre, sizeName⟩

def argumentName : totalSpace domain.decoded ⟶ naturals where
  app _ := TypeCat.ofHom fun receipt => receipt.2.val
  naturality := by intros; rfl

abbrev codomain : NativeType (totalSpace domain.decoded) :=
  ⟨naturals, finiteFibre, argumentName⟩

theorem domain_false : domain.decoded.obj ⟨world, false⟩ = Fin 1 := rfl
theorem domain_true : domain.decoded.obj ⟨world, true⟩ = Fin 2 := rfl

def trueOne : (totalSpace domain.decoded).obj world := ⟨true, ⟨1, by decide⟩⟩
def trueZero : (totalSpace domain.decoded).obj world := ⟨true, ⟨0, by decide⟩⟩

theorem dependent_codomain_one : codomain.decoded.obj ⟨world, trueOne⟩ = Fin 2 := rfl
theorem dependent_codomain_zero : codomain.decoded.obj ⟨world, trueZero⟩ = Fin 1 := rfl

noncomputable def universalName := formerName domain codomain

theorem actual_evaluation_recovers_name :
    totalReindexMap universalName (parameterDomain domain codomain) ≫
      NativeLocalFunctionParameters.evaluation domain.family codomain.parameters = argumentName :=
  NativeLocalFunctionParameters.name_evaluation domain.name domain.family
    codomain.parameters codomain.name

theorem evaluation_one :
    (totalReindexMap universalName (parameterDomain domain codomain) ≫
      NativeLocalFunctionParameters.evaluation domain.family codomain.parameters).app world trueOne = (1 : Nat) := by
  rw [actual_evaluation_recovers_name]
  rfl

theorem evaluation_zero :
    (totalReindexMap universalName (parameterDomain domain codomain) ≫
      NativeLocalFunctionParameters.evaluation domain.family codomain.parameters).app world trueZero = (0 : Nat) := by
  rw [actual_evaluation_recovers_name]
  rfl

def exchange : booleans ⟶ booleans where
  app _ := TypeCat.ofHom Bool.not
  naturality := by intros; rfl

theorem exchanged_true_domain : (domain.reindex exchange).decoded.obj ⟨world, true⟩ = Fin 1 := rfl
theorem exchanged_false_domain : (domain.reindex exchange).decoded.obj ⟨world, false⟩ = Fin 2 := rfl

theorem name_substitution :
    formerName (domain.reindex exchange)
        (codomain.reindex (totalReindexMap exchange domain.decoded)) = exchange ≫ universalName :=
  NativeLocalFunctionParameters.name_substitution exchange domain.name domain.family
    codomain.parameters codomain.name

def erasedName : booleans ⟶ naturals where
  app _ := TypeCat.ofHom fun _ => (0 : Nat)
  naturality := by intros; rfl

def erasedDomain : NativeType booleans := ⟨naturals, finiteFibre, erasedName⟩

theorem erased_domain_changes_fibre : erasedDomain.decoded ≠ domain.decoded := by
  intro same
  have fibres := congrArg (fun family : DisplayedFamily.{0, 0, 0, 0} booleans =>
    family.obj ⟨world, true⟩) same
  have cards := congrArg Nat.card fibres
  change Nat.card (Fin 1) = Nat.card (Fin 2) at cards
  norm_num [Nat.card_eq_fintype_card] at cards

end Mettapedia.TypeTheory.NativeLocalParameterControls
