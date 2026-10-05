import Mettapedia.TypeTheory.ContextualWitnessCover

/-!
# Contextual first-order material logic

Equality and membership are interpreted in an actual varying value family.
Implication and universal quantification retain every future context and
arrow. Formula substitution commutes with the interpretation, including
under binders. Logical soundness does not select a material foundation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic

open _root_.CategoryTheory
universe u v

inductive Formula : Nat → Type where
  | bottom {n : Nat} : Formula n
  | equal {n : Nat} (first second : Fin n) : Formula n
  | member {n : Nat} (child parent : Fin n) : Formula n
  | both {n : Nat} (left right : Formula n) : Formula n
  | either {n : Nat} (left right : Formula n) : Formula n
  | imply {n : Nat} (left right : Formula n) : Formula n
  | all {n : Nat} (body : Formula (n+1)) : Formula n
  | exist {n : Nat} (body : Formula (n+1)) : Formula n

def liftVariables {n m : Nat} (indices : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun index => (indices index).succ)

def substitute {n m : Nat} (indices : Fin n → Fin m) : Formula n → Formula m
  | .bottom => .bottom
  | .equal first second => .equal (indices first) (indices second)
  | .member child parent => .member (indices child) (indices parent)
  | .both left right => .both (substitute indices left) (substitute indices right)
  | .either left right => .either (substitute indices left) (substitute indices right)
  | .imply left right => .imply (substitute indices left) (substitute indices right)
  | .all body => .all (substitute (liftVariables indices) body)
  | .exist body => .exist (substitute (liftVariables indices) body)

variable {D : Type u} [Category.{u} D] (values : D ⥤ Type v)

structure Model where
  member : (point : D) → values.obj point → values.obj point → Prop
  member_transport : ∀ {point target : D} (arrow : point ⟶ target)
    {child parent : values.obj point}, member point child parent →
      member target (values.map arrow child) (values.map arrow parent)

abbrev Environment (n : Nat) (point : D) := Fin n → values.obj point

def transport {n : Nat} {point target : D} (arrow : point ⟶ target)
    (environment : Environment values n point) : Environment values n target :=
  fun index => values.map arrow (environment index)

def extend {n : Nat} {point : D} (environment : Environment values n point)
    (value : values.obj point) : Environment values (n+1) point := Fin.cases value environment

theorem transport_id {n : Nat} (point : D) (environment : Environment values n point) :
    transport values (𝟙 point) environment = environment := by
  funext index
  exact values.map_id_apply point (environment index)

theorem transport_comp {n : Nat} {first second third : D}
    (earlier : first ⟶ second) (later : second ⟶ third)
    (environment : Environment values n first) :
    transport values (earlier ≫ later) environment = transport values later (transport values earlier environment) := by
  funext index
  exact values.map_comp_apply earlier later (environment index)

theorem transport_extend {n : Nat} {point target : D} (arrow : point ⟶ target)
    (environment : Environment values n point) (value : values.obj point) :
    transport values arrow (extend values environment value) =
      extend values (transport values arrow environment) (values.map arrow value) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

def force (model : Model values) {n : Nat} : Formula n →
    (point : D) → Environment values n point → Prop
  | .bottom, _, _ => False
  | .equal first second, _, environment => environment first = environment second
  | .member child parent, point, environment => model.member point (environment child) (environment parent)
  | .both left right, point, environment => force model left point environment ∧ force model right point environment
  | .either left right, point, environment => force model left point environment ∨ force model right point environment
  | .imply left right, point, environment =>
      ∀ (target : D) (arrow : point ⟶ target),
        force model left target (transport values arrow environment) →
          force model right target (transport values arrow environment)
  | .all body, point, environment =>
      ∀ (target : D) (arrow : point ⟶ target) (value : values.obj target),
        force model body target (extend values (transport values arrow environment) value)
  | .exist body, point, environment =>
      ∃ value : values.obj point, force model body point (extend values environment value)

variable {values} (model : Model values)

theorem force_transport {n : Nat} (formula : Formula n) {point target : D}
    (arrow : point ⟶ target) (environment : Environment values n point)
    (holds : force values model formula point environment) :
    force values model formula target (transport values arrow environment) := by
  induction formula generalizing point target with
  | bottom => exact holds
  | equal first second => exact congrArg (values.map arrow) holds
  | member child parent => exact model.member_transport arrow holds
  | both left right leftIH rightIH => exact ⟨leftIH arrow environment holds.1, rightIH arrow environment holds.2⟩
  | either left right leftIH rightIH =>
    exact holds.elim (fun proof => Or.inl (leftIH arrow environment proof))
      (fun proof => Or.inr (rightIH arrow environment proof))
  | imply left right _ _ =>
    intro later tail premise
    rw [← transport_comp] at premise ⊢
    exact holds later (arrow ≫ tail) premise
  | all body _ =>
    intro later tail value
    rw [← transport_comp]
    exact holds later (arrow ≫ tail) value
  | exist body bodyIH =>
    obtain ⟨value, proof⟩ := holds
    refine ⟨values.map arrow value, ?_⟩
    exact (transport_extend values arrow environment value) ▸ bodyIH arrow _ proof

theorem extended_substitution {n m : Nat} (indices : Fin n → Fin m) (point : D)
    (environment : Environment values m point) (value : values.obj point) :
    (fun index => extend values environment value (liftVariables indices index)) =
      extend values (fun index => environment (indices index)) value := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem force_substitute {n m : Nat} (indices : Fin n → Fin m) (formula : Formula n)
    (point : D) (environment : Environment values m point) :
    force values model (substitute indices formula) point environment ↔
      force values model formula point (fun index => environment (indices index)) := by
  induction formula generalizing m point with
  | bottom => exact Iff.rfl
  | equal first second => exact Iff.rfl
  | member child parent => exact Iff.rfl
  | both left right leftIH rightIH => exact and_congr (leftIH indices point environment) (rightIH indices point environment)
  | either left right leftIH rightIH => exact or_congr (leftIH indices point environment) (rightIH indices point environment)
  | imply left right leftIH rightIH =>
    refine forall_congr' fun target => forall_congr' fun arrow => ?_
    exact imp_congr (leftIH indices target (transport values arrow environment))
      (rightIH indices target (transport values arrow environment))
  | all body bodyIH =>
    refine forall_congr' fun target => forall_congr' fun arrow => forall_congr' fun value => ?_
    exact (bodyIH (liftVariables indices) target (extend values (transport values arrow environment) value)).trans
      (Iff.of_eq (congrArg (force values model body target)
        (extended_substitution indices target (transport values arrow environment) value)))
  | exist body bodyIH =>
    refine exists_congr fun value => ?_
    exact (bodyIH (liftVariables indices) point (extend values environment value)).trans
      (Iff.of_eq (congrArg (force values model body point)
        (extended_substitution indices point environment value)))

theorem force_modusPonens {n : Nat} (antecedent consequent : Formula n) (point : D)
    (environment : Environment values n point)
    (step : force values model (.imply antecedent consequent) point environment)
    (premise : force values model antecedent point environment) :
    force values model consequent point environment := by
  have current := step point (𝟙 point)
  rw [transport_id] at current
  exact current premise

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
