import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualMaterialLogic
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInfinity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSetTheory

/-!
# Logical set-axiom formulas in the actual contextual hyperset model

The explicit first-order sentences use the same membership, varying carrier
and all-future logical quantifiers as the checked deduction system. Their
witnesses are the independently constructed natural set operations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetTheorySoundness

open _root_.CategoryTheory ContextualMaterialLogic ContextualMaterialFormulaSemantics
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualMaterialLogic (model formulaSeparation formulaSeparation_future formulaStrongCollection)
open ContextualMaterialSetTheory
open HostChoiceContextualSetPowers HostChoiceContextualSetInfinity
universe u

variable {D : Type u} [Category.{u} D]

theorem empty_valid (point : D) (environment : Environment sets 0 point) :
    force sets model emptyAxiom point environment := by
  refine ⟨emptySet.val point, ?_⟩
  intro target arrow child later tail premise
  change Member later (sets.map tail child) (sets.map tail (sets.map arrow (emptySet.val point))) at premise
  rw [← sets.map_comp_apply] at premise
  rw [emptySet.property (arrow ≫ tail)] at premise
  exact member_empty later _ premise


theorem pairing_valid (point : D) (environment : Environment sets 0 point) :
    force sets model pairingAxiom point environment := by
  intro firstPoint firstArrow first secondPoint secondArrow second
  refine ⟨pairSet.app secondPoint (sets.map secondArrow first, second), ?_⟩
  intro target arrow child
  apply (force_equivalent_iff model _ _ target _).mpr
  intro later tail
  change Member later (sets.map tail child)
      (sets.map tail (sets.map arrow (pairSet.app secondPoint (sets.map secondArrow first, second)))) ↔
    sets.map tail child = sets.map tail (sets.map arrow (sets.map secondArrow first)) ∨
      sets.map tail child = sets.map tail (sets.map arrow second)
  have membership := (futureMember_iff (arrow ≫ tail) (sets.map tail child)
    (pairSet.app secondPoint (sets.map secondArrow first, second))).symm
  have paired := future_pair (arrow ≫ tail) (sets.map tail child) (sets.map secondArrow first) second
  simpa only [sets.map_comp_apply] using
    membership.trans (paired.trans (or_congr eq_comm eq_comm))

theorem union_valid (point : D) (environment : Environment sets 0 point) :
    force sets model unionAxiom point environment := by
  intro firstPoint firstArrow parent
  refine ⟨unionSet.app firstPoint parent, ?_⟩
  intro target arrow child
  apply (force_equivalent_iff model _ _ target _).mpr
  intro later tail
  change Member later (sets.map tail child)
      (sets.map tail (sets.map arrow (unionSet.app firstPoint parent))) ↔
    ∃ middle : sets.obj later,
      Member later middle (sets.map tail (sets.map arrow parent)) ∧
        Member later (sets.map tail child) middle
  rw [← sets.map_comp_apply, ← sets.map_comp_apply]
  exact (futureMember_iff (arrow ≫ tail) _ _).symm.trans
    ((future_union (arrow ≫ tail) _ _).trans
      (exists_congr fun middle => and_congr (futureMember_iff (arrow ≫ tail) middle parent) Iff.rfl))

theorem powerset_valid (point : D) (environment : Environment sets 0 point) :
    force sets model powersetAxiom point environment := by
  intro firstPoint firstArrow parent
  refine ⟨powersetSet.app firstPoint parent, ?_⟩
  intro target arrow child
  apply (force_equivalent_iff model _ _ target _).mpr
  intro later tail
  change Member later (sets.map tail child)
      (sets.map tail (sets.map arrow (powersetSet.app firstPoint parent))) ↔
    ∀ (future : D) (move : later ⟶ future) (member : sets.obj future),
      ∀ (last : D) (endMove : future ⟶ last),
        Member last (sets.map endMove member)
          (sets.map endMove (sets.map move (sets.map tail child))) →
        Member last (sets.map endMove member)
          (sets.map endMove (sets.map move (sets.map tail (sets.map arrow parent))))
  rw [← sets.map_comp_apply]
  rw [← futureMember_iff (arrow ≫ tail), future_powerset]
  constructor
  · intro contained future move member last endMove belongs
    have allMembers := (subset_iff_future_members later (sets.map tail child)
      (sets.map (arrow ≫ tail) parent)).mp contained
    have admitted : Member last (sets.map endMove member)
        (sets.map (move ≫ endMove) (sets.map tail child)) := by
      simpa only [sets.map_comp_apply] using belongs
    have answer := allMembers last (move ≫ endMove) (sets.map endMove member) admitted
    simpa only [sets.map_comp_apply] using answer
  · intro contained
    apply (subset_iff_future_members _ _ _).mpr
    intro future move member belongs
    have answer := contained future move member future (𝟙 future)
    simp only [sets.map_id_apply] at answer
    simpa only [sets.map_comp_apply] using answer belongs

theorem separation_valid {n : Nat} (formula : Formula (n+1)) (point : D)
    (environment : Environment sets n point) :
    force sets model (separationAxiom formula) point environment := by
  intro parentPoint parentArrow parent
  let savedEnvironment := ContextualMaterialLogic.transport sets parentArrow environment
  refine ⟨(formulaSeparation formula).app parentPoint (savedEnvironment, parent), ?_⟩
  intro target arrow child
  apply (force_equivalent_iff model _ _ target _).mpr
  intro later tail
  have separated := formulaSeparation_future formula parentPoint later (arrow ≫ tail) savedEnvironment parent
    (sets.map tail child)
  have reduced := force_discardTwo model formula later
    (ContextualMaterialLogic.transport sets tail
      (ContextualMaterialLogic.transport sets arrow savedEnvironment))
    (sets.map tail (sets.map arrow parent))
    (sets.map tail (sets.map arrow ((formulaSeparation formula).app parentPoint (savedEnvironment, parent))))
    (sets.map tail child)
  change Member later (sets.map tail child)
      (sets.map tail (sets.map arrow ((formulaSeparation formula).app parentPoint (savedEnvironment, parent)))) ↔
    Member later (sets.map tail child) (sets.map tail (sets.map arrow parent)) ∧ _
  have identity : ContextualMaterialLogic.transport sets (arrow ≫ tail) savedEnvironment =
      ContextualMaterialLogic.transport sets tail
        (ContextualMaterialLogic.transport sets arrow savedEnvironment) :=
    ContextualMaterialLogic.transport_comp sets arrow tail savedEnvironment
  have law := (Iff.of_eq (congrArg (Member later (sets.map tail child))
    (sets.map_comp_apply arrow tail
      ((formulaSeparation formula).app parentPoint (savedEnvironment, parent))))).symm.trans separated
  apply law.trans
  apply and_congr
  · exact Iff.of_eq (congrArg (Member later (sets.map tail child))
      (sets.map_comp_apply arrow tail parent))
  · exact (Iff.of_eq (congrArg
      (fun assignment => force sets model formula later (extend sets assignment (sets.map tail child))) identity)).trans
      (by simpa only [ContextualMaterialLogic.transport_extend] using reduced.symm)

theorem empty_property_valid {n : Nat} (point : D) (environment : Environment sets n point)
    (index : Fin n) (constructed : environment index = emptySet.val point) :
    force sets model (emptyProperty index) point environment := by
  intro target arrow child later tail belongs
  change Member later (sets.map tail child) (sets.map tail (sets.map arrow (environment index))) at belongs
  have moved : sets.map tail (sets.map arrow (environment index)) = emptySet.val later :=
    (congrArg (fun value => sets.map tail (sets.map arrow value)) constructed).trans
      ((congrArg (sets.map tail) (emptySet.property arrow)).trans (emptySet.property tail))
  exact member_empty later _ (moved ▸ belongs)

theorem successor_property_valid {n : Nat} (point : D) (environment : Environment sets n point)
    (first second : Fin n) (constructed : environment second = successorSet.app point (environment first)) :
    force sets model (successorProperty first second) point environment := by
  intro target arrow child
  apply (force_equivalent_iff model _ _ target _).mpr
  intro later tail
  change Member later (sets.map tail child) (sets.map tail (sets.map arrow (environment second))) ↔
    Member later (sets.map tail child) (sets.map tail (sets.map arrow (environment first))) ∨
      sets.map tail child = sets.map tail (sets.map arrow (environment first))
  have law := (futureMember_iff (arrow ≫ tail) (sets.map tail child)
    (successorSet.app point (environment first))).symm.trans
      ((future_successor (arrow ≫ tail) (environment first) (sets.map tail child)).trans
        (or_congr (futureMember_iff (arrow ≫ tail) (sets.map tail child) (environment first)) eq_comm))
  simpa only [sets.map_comp_apply, constructed] using law

theorem infinity_valid (point : D) (environment : Environment sets 0 point) :
    force sets model infinityAxiom point environment := by
  refine ⟨naturals.val point, ?_⟩
  constructor
  · refine ⟨emptySet.val point, ?_⟩
    exact ⟨empty_property_valid point _ 0 rfl, (internal_infinity point).1⟩
  · intro target arrow child later tail belongs
    change Member later (sets.map tail child)
      (sets.map tail (sets.map arrow (naturals.val point))) at belongs
    refine ⟨successorSet.app later (sets.map tail child), ?_⟩
    constructor
    · exact successor_property_valid later _ 1 0 rfl
    · change Member later (successorSet.app later (sets.map tail child))
        (sets.map tail (sets.map arrow (naturals.val point)))
      have moved : sets.map tail (sets.map arrow (naturals.val point)) = naturals.val later :=
        (congrArg (sets.map tail) (naturals.property arrow)).trans (naturals.property tail)
      exact moved.symm ▸ (internal_infinity later).2 _ (moved ▸ belongs)

theorem strongCollection_valid {n : Nat} (formula : Formula (n+2)) (point : D)
    (environment : Environment sets n point) :
    force sets model (strongCollectionAxiom formula) point environment := by
  intro parentPoint parentArrow parent accountPoint accountArrow premise
  rw [ContextualMaterialLogic.transport_extend] at premise ⊢
  let savedEnvironment := ContextualMaterialLogic.transport sets accountArrow
    (ContextualMaterialLogic.transport sets parentArrow environment)
  let savedParent := sets.map accountArrow parent
  change force sets model (collectionPremise formula) accountPoint
    (extend sets savedEnvironment savedParent) at premise
  have total : ∀ (target : D) (arrow : accountPoint ⟶ target) (child : sets.obj target),
      Member target child (sets.map arrow savedParent) → ∃ witness : sets.obj target,
        force sets model formula target
          (extend sets (extend sets (ContextualMaterialLogic.transport sets arrow savedEnvironment) child) witness) := by
    intro target arrow child belongs
    have current := premise target arrow child target (𝟙 target)
    simp only [ContextualMaterialLogic.transport_id, ContextualMaterialLogic.transport_extend, sets.map_id_apply] at current
    change Member target child (sets.map arrow savedParent) → ∃ witness : sets.obj target,
      force sets model (substitute behindTwoOne formula) target
        (extend sets (extend sets (extend sets
          (ContextualMaterialLogic.transport sets arrow savedEnvironment) (sets.map arrow savedParent)) child) witness) at current
    obtain ⟨witness, related⟩ := current belongs
    exact ⟨witness, (force_discardOneAfterTwo model formula target _ _ child witness).mp related⟩
  obtain ⟨collection, conditions⟩ := formulaStrongCollection formula accountPoint savedEnvironment savedParent total
  refine ⟨collection, ?_⟩
  constructor
  · intro target arrow child later tail belongs
    change Member later (sets.map tail child) (sets.map tail (sets.map arrow savedParent)) at belongs
    have admitted : Member later (sets.map tail child) (sets.map (arrow ≫ tail) savedParent) := by
      simpa only [sets.map_comp_apply] using belongs
    obtain ⟨witness, collected, related⟩ := (conditions later (arrow ≫ tail)).1 (sets.map tail child) admitted
    refine ⟨witness, ?_, ?_⟩
    · change Member later witness (sets.map tail (sets.map arrow collection))
      simpa only [sets.map_comp_apply] using collected
    · have shifted : force sets model formula later
          (extend sets (extend sets (ContextualMaterialLogic.transport sets tail
            (ContextualMaterialLogic.transport sets arrow savedEnvironment)) (sets.map tail child)) witness) := by
        simpa only [ContextualMaterialLogic.transport_comp] using related
      have inserted := (force_discardTwoAfterTwo model formula later
        (ContextualMaterialLogic.transport sets tail (ContextualMaterialLogic.transport sets arrow savedEnvironment))
        (sets.map tail (sets.map arrow savedParent)) (sets.map tail (sets.map arrow collection))
        (sets.map tail child) witness).mpr shifted
      simpa only [ContextualMaterialLogic.transport_extend] using inserted
  · intro target arrow witness later tail collected
    change Member later (sets.map tail witness) (sets.map tail (sets.map arrow collection)) at collected
    have admitted : Member later (sets.map tail witness) (sets.map (arrow ≫ tail) collection) := by
      simpa only [sets.map_comp_apply] using collected
    obtain ⟨child, belongs, related⟩ := (conditions later (arrow ≫ tail)).2 (sets.map tail witness) admitted
    refine ⟨child, ?_, ?_⟩
    · change Member later child (sets.map tail (sets.map arrow savedParent))
      simpa only [sets.map_comp_apply] using belongs
    · have shifted : force sets model formula later
          (extend sets (extend sets (ContextualMaterialLogic.transport sets tail
            (ContextualMaterialLogic.transport sets arrow savedEnvironment)) child) (sets.map tail witness)) := by
        simpa only [ContextualMaterialLogic.transport_comp] using related
      have inserted := (force_swapDiscardTwoAfterTwo model formula later
        (ContextualMaterialLogic.transport sets tail (ContextualMaterialLogic.transport sets arrow savedEnvironment))
        (sets.map tail (sets.map arrow savedParent)) (sets.map tail (sets.map arrow collection))
        (sets.map tail witness) child).mpr shifted
      simpa only [ContextualMaterialLogic.transport_extend] using inserted

theorem valid_theory : ContextualMaterialSetTheory.ValidTheory (model (D := D)) := by
  intro n formula adopted
  induction adopted with
  | empty => exact empty_valid
  | pairing => exact pairing_valid
  | union => exact union_valid
  | powerset => exact powerset_valid
  | infinity => exact infinity_valid
  | extensionality => exact HostChoiceContextualMaterialLogic.extensionality_valid
  | separation formula => exact separation_valid formula
  | strongCollection formula => exact strongCollection_valid formula
  | substitution indices _ inductionHypothesis =>
    intro point environment
    exact (force_substitute model indices _ point environment).mpr
      (inductionHypothesis point (fun index => environment (indices index)))

/-- Logical proofs from this explicitly adopted set theory are interpreted
in the constructed varying hyperset carrier. -/
theorem set_derivation_valid {n : Nat} {assumptions : List (Formula n)} {conclusion : Formula n}
    (derivation : ContextualMaterialLogic.Derivation assumptions conclusion)
    (adopted : ∀ formula ∈ assumptions, ContextualMaterialSetTheory.Axiom formula)
    (point : D) (environment : Environment sets n point) :
    force sets model conclusion point environment :=
  ContextualMaterialSetTheory.derivation_valid model valid_theory derivation adopted point environment

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetTheorySoundness
