import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic

/-!
# Future semantics of material logical equivalence

A biconditional in intuitionistic contextual logic compares both formulas
at every future arrow. Present agreement alone is insufficient.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialFormulaSemantics

open _root_.CategoryTheory ContextualMaterialLogic
universe u v

variable {D : Type u} [Category.{u} D] {values : D ⥤ Type v} (model : Model values)

theorem force_equivalent_iff {n : Nat} (first second : Formula n) (point : D)
    (environment : Environment values n point) :
    force values model (.both (.imply first second) (.imply second first)) point environment ↔
      ∀ (target : D) (arrow : point ⟶ target),
        force values model first target (transport values arrow environment) ↔
          force values model second target (transport values arrow environment) := by
  constructor
  · rintro ⟨forward, backward⟩ target arrow
    exact ⟨forward target arrow, backward target arrow⟩
  · intro agreement
    exact ⟨fun target arrow => (agreement target arrow).mp,
      fun target arrow => (agreement target arrow).mpr⟩

def behindHeadTwo {n : Nat} : Fin (n+1) → Fin (n+3) :=
  Fin.cases 0 (fun index => index.succ.succ.succ)

theorem discardTwo {n : Nat} (point : D) (environment : Environment values n point)
    (first second head : values.obj point) :
    (fun index => extend values (extend values (extend values environment first) second) head
      (behindHeadTwo index)) = extend values environment head := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem force_discardTwo {n : Nat} (formula : Formula (n+1)) (point : D)
    (environment : Environment values n point) (first second head : values.obj point) :
    force values model (substitute behindHeadTwo formula) point
      (extend values (extend values (extend values environment first) second) head) ↔
      force values model formula point (extend values environment head) :=
  (force_substitute model behindHeadTwo formula point _).trans
    (Iff.of_eq (congrArg (force values model formula point)
      (discardTwo point environment first second head)))

def behindTwoOne {n : Nat} : Fin (n+2) → Fin (n+3) :=
  Fin.cases 0 (Fin.cases 1 (fun index => index.succ.succ.succ))

def behindTwoTwo {n : Nat} : Fin (n+2) → Fin (n+4) :=
  Fin.cases 0 (Fin.cases 1 (fun index => index.succ.succ.succ.succ))

def swappedBehindTwoTwo {n : Nat} : Fin (n+2) → Fin (n+4) :=
  Fin.cases 1 (Fin.cases 0 (fun index => index.succ.succ.succ.succ))

theorem discardOneAfterTwo {n : Nat} (point : D) (environment : Environment values n point)
    (inserted child witness : values.obj point) :
    (fun index => extend values (extend values (extend values environment inserted) child) witness
      (behindTwoOne index)) = extend values (extend values environment child) witness := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

theorem discardTwoAfterTwo {n : Nat} (point : D) (environment : Environment values n point)
    (first second child witness : values.obj point) :
    (fun index => extend values (extend values (extend values (extend values environment first) second) child) witness
      (behindTwoTwo index)) = extend values (extend values environment child) witness := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

theorem swapDiscardTwoAfterTwo {n : Nat} (point : D) (environment : Environment values n point)
    (first second witness child : values.obj point) :
    (fun index => extend values (extend values (extend values (extend values environment first) second) witness) child
      (swappedBehindTwoTwo index)) = extend values (extend values environment child) witness := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

theorem force_discardOneAfterTwo {n : Nat} (formula : Formula (n+2)) (point : D)
    (environment : Environment values n point) (inserted child witness : values.obj point) :
    force values model (substitute behindTwoOne formula) point
      (extend values (extend values (extend values environment inserted) child) witness) ↔
      force values model formula point (extend values (extend values environment child) witness) :=
  (force_substitute model behindTwoOne formula point _).trans
    (Iff.of_eq (congrArg (force values model formula point)
      (discardOneAfterTwo point environment inserted child witness)))

theorem force_discardTwoAfterTwo {n : Nat} (formula : Formula (n+2)) (point : D)
    (environment : Environment values n point) (first second child witness : values.obj point) :
    force values model (substitute behindTwoTwo formula) point
      (extend values (extend values (extend values (extend values environment first) second) child) witness) ↔
      force values model formula point (extend values (extend values environment child) witness) :=
  (force_substitute model behindTwoTwo formula point _).trans
    (Iff.of_eq (congrArg (force values model formula point)
      (discardTwoAfterTwo point environment first second child witness)))

theorem force_swapDiscardTwoAfterTwo {n : Nat} (formula : Formula (n+2)) (point : D)
    (environment : Environment values n point) (first second witness child : values.obj point) :
    force values model (substitute swappedBehindTwoTwo formula) point
      (extend values (extend values (extend values (extend values environment first) second) witness) child) ↔
      force values model formula point (extend values (extend values environment child) witness) :=
  (force_substitute model swappedBehindTwoTwo formula point _).trans
    (Iff.of_eq (congrArg (force values model formula point)
      (swapDiscardTwoAfterTwo point environment first second witness child)))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialFormulaSemantics
