import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicSoundness
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetCollection

/-!
# Logical interpretation on the actual contextual hyperset carrier

The varying final set family instantiates the complete-future first-order
interpretation and its intuitionistic deduction rules. Arbitrary formulas
construct stable parameter predicates. Separation and Strong Collection
therefore apply to their actual interpreted schemas, not only to a
separately supplied relation. The full future extensionality sentence is
validated in the same model. External host dependencies remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualMaterialLogic

open _root_.CategoryTheory ContextualMaterialLogic
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualSetCollection

universe u
variable {D : Type u} [Category.{u} D]

def model : Model (sets (D := D)) where
  member := Member
  member_transport := member_transport

def assignments (n : Nat) : D ⥤ Type (u+1) where
  obj point := Environment (sets (D := D)) n point
  map arrow := TypeCat.ofHom (ContextualMaterialLogic.transport sets arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro environment
    exact ContextualMaterialLogic.transport_id sets point environment
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro environment
    exact ContextualMaterialLogic.transport_comp sets first second environment

def unaryPredicate {n : Nat} (formula : Formula (n+1)) :
    CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product (assignments (D := D) n) sets) where
  holds row := force sets model formula row.1 (extend sets row.2.1 row.2.2)
  closed {first second} move holds := by
    have mapped := force_transport model formula move.1 (extend sets first.2.1 first.2.2) holds
    have rowEq := congrArg₂ (extend sets) (congrArg Prod.fst move.2) (congrArg Prod.snd move.2)
    exact (congrArg (force sets model formula second.1)
      ((ContextualMaterialLogic.transport_extend sets move.1 first.2.1 first.2.2).trans rowEq)) ▸ mapped

def binaryPredicate {n : Nat} (formula : Formula (n+2)) :
    CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product (assignments (D := D) n)
        (CoveredFuturePowerClassifier.product sets sets)) where
  holds row := force sets model formula row.1 (extend sets (extend sets row.2.1 row.2.2.1) row.2.2.2)
  closed {first second} move holds := by
    have mapped := force_transport model formula move.1
      (extend sets (extend sets first.2.1 first.2.2.1) first.2.2.2) holds
    have firstEq := ContextualMaterialLogic.transport_extend sets move.1
      (extend sets first.2.1 first.2.2.1) first.2.2.2
    have secondEq := congrArg (fun environment => extend sets environment (sets.map move.1 first.2.2.2))
      (ContextualMaterialLogic.transport_extend sets move.1 first.2.1 first.2.2.1)
    have rowEq := congrArg₂ (fun environment pair => extend sets (extend sets environment pair.1) pair.2)
      (congrArg Prod.fst move.2) (congrArg Prod.snd move.2)
    exact (congrArg (force sets model formula second.1) (firstEq.trans (secondEq.trans rowEq))) ▸ mapped

noncomputable def formulaSeparation {n : Nat} (formula : Formula (n+1)) :
    Mettapedia.TypeTheory.ContextualWitnessCover.NaturalHom
      (CoveredFuturePowerClassifier.product (assignments (D := D) n) sets) sets :=
  separationSet (assignments n) (unaryPredicate formula)

theorem formulaSeparation_future {n : Nat} (formula : Formula (n+1))
    (point target : D) (arrow : point ⟶ target) (environment : Environment sets n point)
    (parent : sets.obj point) (child : sets.obj target) :
    Member target child (sets.map arrow ((formulaSeparation formula).app point (environment, parent))) ↔
      Member target child (sets.map arrow parent) ∧
        force sets model formula target (extend sets (ContextualMaterialLogic.transport sets arrow environment) child) :=
  (futureMember_iff arrow child _).symm.trans
    ((future_separation (assignments n) (unaryPredicate formula) arrow environment parent child).trans
      (and_congr (futureMember_iff arrow child parent) Iff.rfl))

theorem formulaStrongCollection {n : Nat} (formula : Formula (n+2))
    (point : D) (environment : Environment sets n point) (parent : sets.obj point)
    (total : ∀ (target : D) (arrow : point ⟶ target) (child : sets.obj target),
      Member target child (sets.map arrow parent) → ∃ witness : sets.obj target,
        force sets model formula target
          (extend sets (extend sets (ContextualMaterialLogic.transport sets arrow environment) child) witness)) :
    ∃ collection : sets.obj point, ∀ (target : D) (arrow : point ⟶ target),
      (∀ child : sets.obj target, Member target child (sets.map arrow parent) →
        ∃ witness : sets.obj target, Member target witness (sets.map arrow collection) ∧
          force sets model formula target
            (extend sets (extend sets (ContextualMaterialLogic.transport sets arrow environment) child) witness)) ∧
      (∀ witness : sets.obj target, Member target witness (sets.map arrow collection) →
        ∃ child : sets.obj target, Member target child (sets.map arrow parent) ∧
          force sets model formula target
            (extend sets (extend sets (ContextualMaterialLogic.transport sets arrow environment) child) witness)) :=
  internal_strongCollection (assignments n) (binaryPredicate formula) point environment parent total

def equivalent {n : Nat} (first second : Formula n) : Formula n :=
  .both (.imply first second) (.imply second first)

def extensionality : Formula 2 :=
  .imply (.all (equivalent (.member 0 1) (.member 0 2))) (.equal 0 1)

theorem extensionality_valid (point : D) (environment : Environment sets 2 point) :
    force sets model extensionality point environment := by
  intro target arrow premise
  apply (internal_extensionality target _ _).mp
  intro later tail child
  have agreement := premise later tail child
  have forward := agreement.1 later (𝟙 later)
  have backward := agreement.2 later (𝟙 later)
  rw [ContextualMaterialLogic.transport_id] at forward backward
  exact ⟨forward, backward⟩

/-- Every closed logical proof is checked against this same actual set
family. Set-schema validity is supplied by the independent constructions. -/
theorem logical_derivation_valid {n : Nat} {conclusion : Formula n}
    (derivation : Derivation [] conclusion) (point : D) (environment : Environment sets n point) :
    force sets model conclusion point environment :=
  closed_derivation_sound model derivation point environment

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualMaterialLogic
