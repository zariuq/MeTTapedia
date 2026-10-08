import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFormulaRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedDeduction

/-!
# First-order deduction in the varying graph realization

An actual deduction tree computes a realizer in the contextual graph
model. Hypothesis positions retain distinct receipts. Implication and
universal introduction recurse at every actual future context and arrow;
existential elimination opens its current witness. Equality elimination
uses the graph model's future matching action on the entire formula.

The interpretation uses the same authored proof syntax as the constant
graph model, with the contextual interpretation's stronger future clauses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedDeduction

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization
open ContextualMaterialLogic (instantiate weakenFormula substitute)
open GraphRealizedDeduction (Proof)

universe u
variable {D : Type u} [Category.{u} D]

abbrev Receipts {count : Nat} {point : D} (assumptions : List (Formula count))
    (environment : Environment D count point) :=
  (index : Fin assumptions.length) → realize D assumptions[index.val] point environment

def consReceipts {count : Nat} {point : D} {assumptions : List (Formula count)}
    {extra : Formula count} {environment : Environment D count point}
    (head : realize D extra point environment) (tail : Receipts assumptions environment) :
    Receipts (extra :: assumptions) environment := Fin.cases head tail

def persistReceipts {count : Nat} {first second : D} (assumptions : List (Formula count))
    (arrival : first ⟶ second) (environment : Environment D count first)
    (receipts : Receipts assumptions environment) :
    Receipts assumptions (moveEnvironment D arrival environment) :=
  fun index => persistence D assumptions[index.val] arrival environment (receipts index)

/-- Elimination evaluates a full future implication at the actual identity
arrow and transports the environment through the proved identity law. -/
def applyImplication {count : Nat} {left right : Formula count} (point : D)
    (environment : Environment D count point) (proof : realize D (.imply left right) point environment)
    (premise : realize D left point environment) : realize D right point environment :=
  (congrArg (realize D right point) (moveEnvironment_identity D point environment)) ▸
    proof point (𝟙 point)
      ((congrArg (realize D left point) (moveEnvironment_identity D point environment)).symm ▸ premise)

def applyUniversal {count : Nat} {body : Formula (count+1)} (point : D)
    (environment : Environment D count point) (proof : realize D (.all body) point environment)
    (value : Value D point) : realize D body point (extend D value environment) :=
  (congrArg (fun changed => realize D body point (extend D value changed))
    (moveEnvironment_identity D point environment)) ▸ proof point (𝟙 point) value

theorem realize_weaken {count : Nat} (formula : Formula count) (point : D)
    (environment : Environment D count point) (value : Value D point) :
    realize D (weakenFormula formula) point (extend D value environment) = realize D formula point environment :=
  realize_substitution D Fin.succ formula point (extend D value environment)

theorem instantiate_environment {count : Nat} (index : Fin count) (point : D)
    (environment : Environment D count point) :
    environment ∘ instantiate index = extend D (environment index) environment := by
  funext bound
  exact Fin.cases rfl (fun _ => rfl) bound

theorem realize_instantiate {count : Nat} (body : Formula (count+1)) (index : Fin count)
    (point : D) (environment : Environment D count point) :
    realize D (substitute (instantiate index) body) point environment =
      realize D body point (extend D (environment index) environment) := by
  rw [realize_substitution D, instantiate_environment]

def weakenReceipts {count : Nat} (assumptions : List (Formula count)) (point : D)
    (environment : Environment D count point) (value : Value D point)
    (receipts : Receipts assumptions environment) :
    Receipts (assumptions.map weakenFormula) (extend D value environment) := by
  intro index
  let original : Fin assumptions.length := ⟨index.val, by simpa using index.isLt⟩
  have same : (assumptions.map weakenFormula)[index.val] = weakenFormula assumptions[original.val] := by
    simp [original]
  rw [same, realize_weaken]
  exact receipts original

/-- Soundness computes complete contextual realizers from an actual
first-order deduction tree and its retained hypothesis occurrences. -/
def interpret {count : Nat} {assumptions : List (Formula count)} {conclusion : Formula count}
    (proof : Proof assumptions conclusion) (point : D) (environment : Environment D count point)
    (receipts : Receipts assumptions environment) : realize D conclusion point environment :=
  match proof with
  | .hypothesis index => receipts index
  | .weakening previous positions same =>
      interpret previous point environment (fun index => same index ▸ receipts (positions index))
  | .bottomElim previous => PEmpty.elim (interpret previous point environment receipts)
  | .bothIntro left right => ⟨interpret left point environment receipts, interpret right point environment receipts⟩
  | .bothLeft previous => (interpret previous point environment receipts).1
  | .bothRight previous => (interpret previous point environment receipts).2
  | .eitherLeft previous => .inl (interpret previous point environment receipts)
  | .eitherRight previous => .inr (interpret previous point environment receipts)
  | .eitherElim previous leftBranch rightBranch =>
      match interpret previous point environment receipts with
      | .inl value => interpret leftBranch point environment (consReceipts value receipts)
      | .inr value => interpret rightBranch point environment (consReceipts value receipts)
  | .implyIntro previous => fun future arrival premise =>
      interpret previous future (moveEnvironment D arrival environment)
        (consReceipts premise (persistReceipts _ arrival environment receipts))
  | .implyElim previous premise =>
      applyImplication point environment (interpret previous point environment receipts)
        (interpret premise point environment receipts)
  | .allIntro previous => fun future arrival value =>
      interpret previous future (extend D value (moveEnvironment D arrival environment))
        (weakenReceipts _ future (moveEnvironment D arrival environment) value
          (persistReceipts _ arrival environment receipts))
  | .allElim previous index =>
      (realize_instantiate _ index point environment).symm ▸
        applyUniversal point environment (interpret previous point environment receipts) (environment index)
  | .existIntro index previous =>
      ⟨environment index, realize_instantiate _ index point environment ▸ interpret previous point environment receipts⟩
  | .existElim previous branch =>
      let witness := interpret previous point environment receipts
      realize_weaken _ point environment witness.1 ▸
        interpret branch point (extend D witness.1 environment)
          (consReceipts witness.2 (weakenReceipts _ point environment witness.1 receipts))
  | .equalRefl index => ⟨Equal.refl (environment index)⟩
  | .equalElim sameProof premiseProof =>
      let same := (interpret sameProof point environment receipts).down
      let premise := realize_instantiate _ _ point environment ▸ interpret premiseProof point environment receipts
      (realize_instantiate _ _ point environment).symm ▸
        equalityTransport D _ (point := point) (extend D (environment _) environment) (extend D (environment _) environment)
          (Fin.cases same (fun index => Equal.refl (environment index))) premise

def closed {count : Nat} {conclusion : Formula count} (proof : Proof [] conclusion)
    (point : D) (environment : Environment D count point) : realize D conclusion point environment :=
  interpret proof point environment (fun index => False.elim (Nat.not_lt_zero _ index.isLt))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedDeduction
