import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic

/-!
# Full first-order realization in the varying graph universe

Atomic realizers retain the actual future-indexed matching and member
receipts. Existential realization contains a current witness. Implication
and universal realization inspect every future context and actual arrow.
Persistence and equality substitution compute realizers for arbitrary
formulas, including implication and both unbounded quantifiers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFormulaRealization

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
universe u v w
variable (D : Type u) [Category.{u} D]

abbrev Formula := ContextualMaterialLogic.Formula
abbrev Environment (count : Nat) (point : D) := Fin count → Value D point

def extend {count : Nat} {point : D} (value : Value D point)
    (environment : Environment D count point) : Environment D (count+1) point :=
  Fin.cases value environment

def moveEnvironment {count : Nat} {first second : D} (arrival : first ⟶ second)
    (environment : Environment D count first) : Environment D count second :=
  fun index => move D arrival (environment index)

theorem moveEnvironment_identity {count : Nat} (point : D)
    (environment : Environment D count point) :
    moveEnvironment D (𝟙 point) environment = environment := by
  funext index
  exact move_identity D point (environment index)

theorem moveEnvironment_composition {count : Nat} {first middle last : D}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (environment : Environment D count first) :
    moveEnvironment D (earlier ≫ later) environment =
      moveEnvironment D later (moveEnvironment D earlier environment) := by
  funext index
  exact move_composition D earlier later (environment index)

theorem moveEnvironment_extend {count : Nat} {first second : D} (arrival : first ⟶ second)
    (value : Value D first) (environment : Environment D count first) :
    moveEnvironment D arrival (extend D value environment) =
      extend D (move D arrival value) (moveEnvironment D arrival environment) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

def realize {count : Nat} : Formula count → (point : D) → Environment D count point → Type (u+1)
  | .bottom, _, _ => PEmpty
  | .equal first second, _, environment => ULift.{u+1} (Equal (environment first) (environment second))
  | .member child parent, _, environment => ULift.{u+1} (Member (environment child) (environment parent))
  | .both left right, point, environment => realize left point environment × realize right point environment
  | .either left right, point, environment => realize left point environment ⊕ realize right point environment
  | .imply left right, point, environment =>
      (target : D) → (arrival : point ⟶ target) →
        realize left target (moveEnvironment D arrival environment) →
          realize right target (moveEnvironment D arrival environment)
  | .all body, point, environment =>
      (target : D) → (arrival : point ⟶ target) → (value : Value D target) →
        realize body target (extend D value (moveEnvironment D arrival environment))
  | .exist body, point, environment =>
      Σ value : Value D point, realize body point (extend D value environment)

def persistence {count : Nat} (formula : Formula count) {point target : D}
    (arrival : point ⟶ target) (environment : Environment D count point)
    (proof : realize D formula point environment) :
    realize D formula target (moveEnvironment D arrival environment) :=
  match formula with
  | .bottom => proof
  | .equal _ _ => ⟨Equal.restrict arrival proof.down⟩
  | .member _ _ => ⟨Member.restrict arrival proof.down⟩
  | .both left right =>
      ⟨persistence left arrival environment proof.1, persistence right arrival environment proof.2⟩
  | .either left right =>
      proof.elim (fun data => .inl (persistence left arrival environment data))
        (fun data => .inr (persistence right arrival environment data))
  | .imply _ _ => fun later tail argument => by
      rw [← moveEnvironment_composition] at argument ⊢
      exact proof later (arrival ≫ tail) argument
  | .all _ => fun later tail value => by
      rw [← moveEnvironment_composition]
      exact proof later (arrival ≫ tail) value
  | .exist body =>
      ⟨move D arrival proof.1, (moveEnvironment_extend D arrival proof.1 environment) ▸
        persistence body arrival (extend D proof.1 environment) proof.2⟩

def equalityTransport {count : Nat} (formula : Formula count) {point : D}
    (first second : Environment D count point)
    (same : ∀ index, Equal (first index) (second index)) :
    realize D formula point first → realize D formula point second :=
  match formula with
  | .bottom => PEmpty.elim
  | .equal left right => fun proof => ⟨(same left).symm.trans (proof.down.trans (same right))⟩
  | .member child parent => fun proof => ⟨Member.transport (same child) (same parent) proof.down⟩
  | .both left right => fun proof =>
      ⟨equalityTransport left first second same proof.1, equalityTransport right first second same proof.2⟩
  | .either left right => fun proof => proof.elim
      (fun data => .inl (equalityTransport left first second same data))
      (fun data => .inr (equalityTransport right first second same data))
  | .imply left right => fun proof target arrival argument =>
      equalityTransport right (moveEnvironment D arrival first) (moveEnvironment D arrival second)
        (fun index => Equal.restrict arrival (same index))
        (proof target arrival
          (equalityTransport left (moveEnvironment D arrival second) (moveEnvironment D arrival first)
            (fun index => (Equal.restrict arrival (same index)).symm) argument))
  | .all body => fun proof target arrival value =>
      equalityTransport body (extend D value (moveEnvironment D arrival first))
        (extend D value (moveEnvironment D arrival second))
        (Fin.cases (Equal.refl value) (fun index => Equal.restrict arrival (same index)))
        (proof target arrival value)
  | .exist body => fun proof =>
      ⟨proof.1, equalityTransport body (extend D proof.1 first) (extend D proof.1 second)
        (Fin.cases (Equal.refl proof.1) same) proof.2⟩

theorem extend_substitution {count other : Nat} {point : D}
    (indices : Fin count → Fin other) (value : Value D point)
    (environment : Environment D other point) :
    extend D value environment ∘ ContextualMaterialLogic.liftVariables indices =
      extend D value (environment ∘ indices) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem dependentPi_congr {Index : Type v} {first second : Index → Type w}
    (same : ∀ index, first index = second index) :
    ((index : Index) → first index) = ((index : Index) → second index) :=
  congrArg (fun family => (index : Index) → family index) (funext same)

theorem realize_substitution {count other : Nat} (indices : Fin count → Fin other)
    (formula : Formula count) (point : D) (environment : Environment D other point) :
    realize D (ContextualMaterialLogic.substitute indices formula) point environment =
      realize D formula point (environment ∘ indices) := by
  induction formula generalizing other point with
  | bottom => rfl
  | equal _ _ => rfl
  | member _ _ => rfl
  | both left right leftIH rightIH => exact congrArg₂ Prod (leftIH indices point environment) (rightIH indices point environment)
  | either left right leftIH rightIH => exact congrArg₂ Sum (leftIH indices point environment) (rightIH indices point environment)
  | imply left right leftIH rightIH =>
    change ((target : D) → (arrival : point ⟶ target) →
      realize D (ContextualMaterialLogic.substitute indices left) target (moveEnvironment D arrival environment) →
        realize D (ContextualMaterialLogic.substitute indices right) target (moveEnvironment D arrival environment)) = _
    exact dependentPi_congr (fun target => dependentPi_congr (fun arrival =>
      congrArg₂ (fun source target => source → target)
        (leftIH indices target (moveEnvironment D arrival environment))
        (rightIH indices target (moveEnvironment D arrival environment))))
  | all body induction =>
    change ((target : D) → (arrival : point ⟶ target) → (value : Value D target) →
      realize D (ContextualMaterialLogic.substitute (ContextualMaterialLogic.liftVariables indices) body)
        target (extend D value (moveEnvironment D arrival environment))) = _
    apply dependentPi_congr
    intro target
    apply dependentPi_congr
    intro arrival
    apply dependentPi_congr
    intro value
    rw [induction, extend_substitution]
    rfl
  | exist body induction =>
    change (Σ value : Value D point,
      realize D (ContextualMaterialLogic.substitute (ContextualMaterialLogic.liftVariables indices) body)
        point (extend D value environment)) = _
    congr 1
    funext value
    rw [induction, extend_substitution]

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFormulaRealization
