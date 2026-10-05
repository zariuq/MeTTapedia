import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic

/-!
# Soundness of intuitionistic material derivations

Natural deduction for membership and equality is interpreted in the full
contextual value family. Binder rules retain transported assumptions and
arbitrary future values. Equality substitution uses actual value equality;
no equality reflection, excluded middle or witness-selection rule is added.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic

open _root_.CategoryTheory
universe u v

def instantiate {n : Nat} (index : Fin n) : Fin (n+1) → Fin n := Fin.cases index id

def weakenFormula {n : Nat} (formula : Formula n) : Formula (n+1) := substitute Fin.succ formula

inductive Derivation : {n : Nat} → List (Formula n) → Formula n → Type where
  | hypothesis {n : Nat} {assumptions : List (Formula n)} {formula : Formula n}
      (included : formula ∈ assumptions) : Derivation assumptions formula
  | weakening {n : Nat} {assumptions larger : List (Formula n)} {formula : Formula n}
      (proof : Derivation assumptions formula)
      (included : ∀ formula, formula ∈ assumptions → formula ∈ larger) : Derivation larger formula
  | bottomElim {n : Nat} {assumptions : List (Formula n)} {formula : Formula n}
      (proof : Derivation assumptions .bottom) : Derivation assumptions formula
  | bothIntro {n : Nat} {assumptions : List (Formula n)} {left right : Formula n}
      (leftProof : Derivation assumptions left) (rightProof : Derivation assumptions right) :
      Derivation assumptions (.both left right)
  | bothLeft {n : Nat} {assumptions : List (Formula n)} {left right : Formula n}
      (proof : Derivation assumptions (.both left right)) : Derivation assumptions left
  | bothRight {n : Nat} {assumptions : List (Formula n)} {left right : Formula n}
      (proof : Derivation assumptions (.both left right)) : Derivation assumptions right
  | eitherLeft {n : Nat} {assumptions : List (Formula n)} {left right : Formula n}
      (proof : Derivation assumptions left) : Derivation assumptions (.either left right)
  | eitherRight {n : Nat} {assumptions : List (Formula n)} {left right : Formula n}
      (proof : Derivation assumptions right) : Derivation assumptions (.either left right)
  | eitherElim {n : Nat} {assumptions : List (Formula n)} {left right result : Formula n}
      (proof : Derivation assumptions (.either left right))
      (leftBranch : Derivation (left :: assumptions) result)
      (rightBranch : Derivation (right :: assumptions) result) : Derivation assumptions result
  | implyIntro {n : Nat} {assumptions : List (Formula n)} {left right : Formula n}
      (proof : Derivation (left :: assumptions) right) : Derivation assumptions (.imply left right)
  | implyElim {n : Nat} {assumptions : List (Formula n)} {left right : Formula n}
      (proof : Derivation assumptions (.imply left right)) (premise : Derivation assumptions left) :
      Derivation assumptions right
  | allIntro {n : Nat} {assumptions : List (Formula n)} {body : Formula (n+1)}
      (proof : Derivation (assumptions.map weakenFormula) body) : Derivation assumptions (.all body)
  | allElim {n : Nat} {assumptions : List (Formula n)} {body : Formula (n+1)}
      (proof : Derivation assumptions (.all body)) (index : Fin n) :
      Derivation assumptions (substitute (instantiate index) body)
  | existIntro {n : Nat} {assumptions : List (Formula n)} {body : Formula (n+1)}
      (index : Fin n) (proof : Derivation assumptions (substitute (instantiate index) body)) :
      Derivation assumptions (.exist body)
  | existElim {n : Nat} {assumptions : List (Formula n)} {body : Formula (n+1)} {result : Formula n}
      (proof : Derivation assumptions (.exist body))
      (branch : Derivation (body :: assumptions.map weakenFormula) (weakenFormula result)) :
      Derivation assumptions result
  | equalRefl {n : Nat} {assumptions : List (Formula n)} (index : Fin n) :
      Derivation assumptions (.equal index index)
  | equalElim {n : Nat} {assumptions : List (Formula n)} {body : Formula (n+1)} {first second : Fin n}
      (same : Derivation assumptions (.equal first second))
      (proof : Derivation assumptions (substitute (instantiate first) body)) :
      Derivation assumptions (substitute (instantiate second) body)

variable {D : Type u} [Category.{u} D] {values : D ⥤ Type v} (model : Model values)

theorem force_weaken {n : Nat} (formula : Formula n) (point : D)
    (environment : Environment values n point) (value : values.obj point) :
    force values model (weakenFormula formula) point (extend values environment value) ↔
      force values model formula point environment :=
  force_substitute model Fin.succ formula point (extend values environment value)

theorem instantiate_environment {n : Nat} (index : Fin n) (point : D)
    (environment : Environment values n point) :
    (fun bound => environment (instantiate index bound)) = extend values environment (environment index) := by
  funext bound
  exact Fin.cases rfl (fun _ => rfl) bound

theorem force_instantiate {n : Nat} (body : Formula (n+1)) (index : Fin n) (point : D)
    (environment : Environment values n point) :
    force values model (substitute (instantiate index) body) point environment ↔
      force values model body point (extend values environment (environment index)) :=
  (force_substitute model (instantiate index) body point environment).trans
    (Iff.of_eq (congrArg (force values model body point) (instantiate_environment index point environment)))

theorem assumptions_weaken {n : Nat} (assumptions : List (Formula n)) (point : D)
    (environment : Environment values n point) (value : values.obj point)
    (admitted : ∀ formula, formula ∈ assumptions → force values model formula point environment) :
    ∀ formula, formula ∈ assumptions.map weakenFormula →
      force values model formula point (extend values environment value) := by
  intro formula included
  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp included
  exact (force_weaken model original point environment value).mpr (admitted original originalIn)

theorem assumptions_cons {n : Nat} {assumptions : List (Formula n)} {extra : Formula n}
    (point : D) (environment : Environment values n point)
    (admitted : ∀ formula, formula ∈ assumptions → force values model formula point environment)
    (holds : force values model extra point environment) :
    ∀ formula, formula ∈ extra :: assumptions → force values model formula point environment := by
  intro formula included
  rcases List.mem_cons.mp included with rfl | previous
  · exact holds
  · exact admitted formula previous

theorem derivation_sound {n : Nat} {assumptions : List (Formula n)} {conclusion : Formula n}
    (derivation : Derivation assumptions conclusion) (point : D) (environment : Environment values n point)
    (admitted : ∀ formula, formula ∈ assumptions → force values model formula point environment) :
    force values model conclusion point environment := by
  induction derivation generalizing point with
  | hypothesis included => exact admitted _ included
  | weakening _ included proofIH => exact proofIH point environment (fun formula member => admitted formula (included formula member))
  | bottomElim _ proofIH => exact (proofIH point environment admitted).elim
  | bothIntro _ _ leftIH rightIH => exact ⟨leftIH point environment admitted, rightIH point environment admitted⟩
  | bothLeft _ proofIH => exact (proofIH point environment admitted).1
  | bothRight _ proofIH => exact (proofIH point environment admitted).2
  | eitherLeft _ proofIH => exact Or.inl (proofIH point environment admitted)
  | eitherRight _ proofIH => exact Or.inr (proofIH point environment admitted)
  | eitherElim _ _ _ proofIH leftIH rightIH =>
    exact (proofIH point environment admitted).elim
      (fun holds => leftIH point environment (assumptions_cons model point environment admitted holds))
      (fun holds => rightIH point environment (assumptions_cons model point environment admitted holds))
  | implyIntro _ proofIH =>
    intro target arrow premise
    apply proofIH target (transport values arrow environment)
    intro formula included
    rcases List.mem_cons.mp included with rfl | previous
    · exact premise
    · exact force_transport model formula arrow environment (admitted formula previous)
  | implyElim _ _ proofIH premiseIH =>
    exact force_modusPonens model _ _ point environment
      (proofIH point environment admitted) (premiseIH point environment admitted)
  | allIntro _ proofIH =>
    intro target arrow value
    exact proofIH target (extend values (transport values arrow environment) value)
      (assumptions_weaken model _ target (transport values arrow environment) value
        (fun formula previous => force_transport model formula arrow environment (admitted formula previous)))
  | allElim _ index proofIH =>
    have current := proofIH point environment admitted point (𝟙 point) (environment index)
    rw [transport_id] at current
    exact (force_instantiate model _ index point environment).mpr current
  | existIntro index _ proofIH =>
    exact ⟨environment index, (force_instantiate model _ index point environment).mp (proofIH point environment admitted)⟩
  | existElim _ _ proofIH branchIH =>
    obtain ⟨value, holds⟩ := proofIH point environment admitted
    apply (force_weaken model _ point environment value).mp
    apply branchIH point (extend values environment value)
    intro formula included
    rcases List.mem_cons.mp included with rfl | previous
    · exact holds
    · exact assumptions_weaken model _ point environment value admitted formula previous
  | equalRefl _ => exact rfl
  | equalElim _ _ sameIH proofIH =>
    have same : environment _ = environment _ := sameIH point environment admitted
    have premise := (force_instantiate model _ _ point environment).mp (proofIH point environment admitted)
    exact (force_instantiate model _ _ point environment).mpr
      ((congrArg (fun value => force values model _ point (extend values environment value)) same) ▸ premise)

/-- Every closed logical derivation is valid throughout every contextual
model, with no added material set axiom. -/
theorem closed_derivation_sound {n : Nat} {conclusion : Formula n}
    (derivation : Derivation [] conclusion) (point : D) (environment : Environment values n point) :
    force values model conclusion point environment :=
  derivation_sound model derivation point environment (fun _ included => (List.not_mem_nil included).elim)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
