import Mettapedia.SetTheory.Profiles.CommonCoreConstructive

/-!
# Substitution of actual material proof trees

Variable substitution is constructed on the existing occurrence-indexed
proof syntax. Quantifier introduction moves through weakening, elimination
commutes with instantiation, and equality elimination uses the substituted
body. The transformed law assumptions are actual core schema instances.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreSubstitution

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula substitute liftVariables weakenFormula instantiate)
open GraphRealizedDeduction (Proof)
open CommonCore

theorem liftVariables_identity (count : Nat) : liftVariables (@id (Fin count)) = id := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem liftVariables_composition {first middle last : Nat}
    (earlier : Fin first → Fin middle) (later : Fin middle → Fin last) :
    liftVariables later ∘ liftVariables earlier = liftVariables (later ∘ earlier) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem substitute_identity {count : Nat} (body : Formula count) : substitute id body = body := by
  induction body with
  | bottom => rfl
  | equal _ _ => rfl
  | member _ _ => rfl
  | both _ _ first second => simp only [substitute, first, second]
  | either _ _ first second => simp only [substitute, first, second]
  | imply _ _ first second => simp only [substitute, first, second]
  | all _ induction => simp only [substitute, liftVariables_identity, induction]
  | exist _ induction => simp only [substitute, liftVariables_identity, induction]

theorem substitute_composition {first middle last : Nat}
    (earlier : Fin first → Fin middle) (later : Fin middle → Fin last)
    (body : Formula first) :
    substitute later (substitute earlier body) = substitute (later ∘ earlier) body := by
  induction body generalizing middle last with
  | bottom => rfl
  | equal _ _ => rfl
  | member _ _ => rfl
  | both _ _ first second => simp only [substitute, first, second]
  | either _ _ first second => simp only [substitute, first, second]
  | imply _ _ first second => simp only [substitute, first, second]
  | all _ induction => simp only [substitute, induction, liftVariables_composition]
  | exist _ induction => simp only [substitute, induction, liftVariables_composition]

theorem substitute_weaken {count other : Nat} (indices : Fin count → Fin other)
    (body : Formula count) :
    substitute (liftVariables indices) (weakenFormula body) =
      weakenFormula (substitute indices body) := by
  unfold weakenFormula
  rw [substitute_composition, substitute_composition]
  rfl

theorem substitute_instantiate {count other : Nat} (indices : Fin count → Fin other)
    (index : Fin count) (body : Formula (count+1)) :
    substitute indices (substitute (instantiate index) body) =
      substitute (instantiate (indices index)) (substitute (liftVariables indices) body) := by
  rw [substitute_composition, substitute_composition]
  congr 1
  funext bound
  exact Fin.cases rfl (fun _ => rfl) bound

theorem substitute_weakened_context {count other : Nat} (indices : Fin count → Fin other)
    (assumptions : List (Formula count)) :
    (assumptions.map weakenFormula).map (substitute (liftVariables indices)) =
      (assumptions.map (substitute indices)).map weakenFormula := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro body _
  exact substitute_weaken indices body

def mappedPosition {α β : Type} (mapping : α → β) (source : List α)
    (index : Fin source.length) : Fin (source.map mapping).length :=
  ⟨index.val, by simp⟩

def originalPosition {α β : Type} (mapping : α → β) (source : List α)
    (index : Fin (source.map mapping).length) : Fin source.length :=
  ⟨index.val, by simpa only [List.length_map] using index.isLt⟩

def substituteProof {count other : Nat} {assumptions : List (Formula count)}
    {conclusion : Formula count} (indices : Fin count → Fin other)
    (proof : Proof assumptions conclusion) :
    Proof (assumptions.map (substitute indices)) (substitute indices conclusion) :=
  match proof with
  | .hypothesis index => by
      simpa [mappedPosition] using Proof.hypothesis
        (mappedPosition (substitute indices) _ index)
  | .weakening previous positions same => by
      apply Proof.weakening (substituteProof indices previous)
        (fun index => mappedPosition (substitute indices) _
          (positions (originalPosition (substitute indices) _ index)))
      intro index
      simpa [mappedPosition, originalPosition] using
        congrArg (substitute indices) (same (originalPosition (substitute indices) _ index))
  | .bottomElim previous => .bottomElim (substituteProof indices previous)
  | .bothIntro left right => .bothIntro (substituteProof indices left) (substituteProof indices right)
  | .bothLeft previous => .bothLeft (substituteProof indices previous)
  | .bothRight previous => .bothRight (substituteProof indices previous)
  | .eitherLeft previous => .eitherLeft (substituteProof indices previous)
  | .eitherRight previous => .eitherRight (substituteProof indices previous)
  | .eitherElim previous left right =>
      .eitherElim (substituteProof indices previous) (substituteProof indices left) (substituteProof indices right)
  | .implyIntro previous => .implyIntro (substituteProof indices previous)
  | .implyElim previous premise => .implyElim (substituteProof indices previous) (substituteProof indices premise)
  | .allIntro previous => by
      apply Proof.allIntro
      rw [← substitute_weakened_context]
      exact substituteProof (liftVariables indices) previous
  | .allElim previous index => by
      rw [substitute_instantiate]
      exact Proof.allElim (substituteProof indices previous) (indices index)
  | .existIntro index previous => by
      apply Proof.existIntro (indices index)
      rw [← substitute_instantiate]
      exact substituteProof indices previous
  | .existElim previous branch => by
      apply Proof.existElim (substituteProof indices previous)
      have changed := substituteProof (liftVariables indices) branch
      simpa only [List.map_cons, substitute_weakened_context, substitute_weaken] using changed
  | .equalRefl index => .equalRefl (indices index)
  | .equalElim same previous => by
      rw [substitute_instantiate]
      apply Proof.equalElim (body := substitute (liftVariables indices) _)
        (substituteProof indices same)
      rw [← substitute_instantiate]
      exact substituteProof indices previous

def substituteDerivation {count other : Nat} {conclusion : Formula count}
    (indices : Fin count → Fin other) (derivation : Derivation conclusion) :
    Derivation (substitute indices conclusion) where
  assumptions := derivation.assumptions.map (substitute indices)
  adopted := fun index => by
    let original := originalPosition (substitute indices) derivation.assumptions index
    have same : (derivation.assumptions.map (substitute indices))[index.val] =
        substitute indices derivation.assumptions[original.val] := by simp [original, originalPosition]
    exact same.symm ▸ Axiom.substitution indices (derivation.adopted original)
  proof := substituteProof indices derivation.proof

theorem mapped_occurrence_value {α β : Type} (mapping : α → β) (source : List α)
    (index : Fin source.length) : (mappedPosition mapping source index).val = index.val := rfl

theorem original_occurrence_value {α β : Type} (mapping : α → β) (source : List α)
    (index : Fin (source.map mapping).length) : (originalPosition mapping source index).val = index.val := rfl

theorem adoption_name_transport {count : Nat} {first second : Formula count}
    (same : first = second) (adopted : Axiom first) :
    (same ▸ adopted).name = adopted.name := by
  cases same
  rfl

theorem substitute_adoption_name {count other : Nat} {conclusion : Formula count}
    (indices : Fin count → Fin other) (derivation : Derivation conclusion)
    (index : Fin (substituteDerivation indices derivation).assumptions.length) :
    ((substituteDerivation indices derivation).adopted index).name =
      (derivation.adopted (originalPosition (substitute indices) derivation.assumptions index)).name := by
  unfold substituteDerivation
  exact adoption_name_transport _ _

end Mettapedia.SetTheory.Profiles.CommonCoreSubstitution
