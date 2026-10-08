import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphFormulaRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicSoundness

/-!
# Receipt-preserving natural deduction for realized graphs

Hypotheses are positions in a context, so duplicate assumptions keep
their separate witnesses. Every logical proof computes a formula realizer.
Equality elimination transports the formula along actual matching data;
it never changes literal graph identity or an arbitrary native family.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedDeduction

open GraphSetRealization GraphFormulaRealization
open ContextualMaterialLogic (instantiate weakenFormula substitute)

universe u

abbrev Receipts {count : Nat} (assumptions : List (Formula count)) (environment : Environment.{u} count) :=
  (index : Fin assumptions.length) → realize assumptions[index.val] environment

def consReceipts {count : Nat} {assumptions : List (Formula count)} {extra : Formula count}
    {environment : Environment.{u} count} (head : realize extra environment)
    (tail : Receipts assumptions environment) : Receipts (extra :: assumptions) environment :=
  Fin.cases head tail

theorem realize_weaken {count : Nat} (formula : Formula count) (environment : Environment.{u} count)
    (value : Graph.{u}) : realize (weakenFormula formula) (extend value environment) = realize formula environment :=
  realize_substitution Fin.succ formula (extend value environment)

theorem instantiate_environment {count : Nat} (index : Fin count) (environment : Environment.{u} count) :
    environment ∘ instantiate index = extend (environment index) environment := by
  funext bound
  exact Fin.cases rfl (fun _ => rfl) bound

theorem realize_instantiate {count : Nat} (body : Formula (count+1)) (index : Fin count)
    (environment : Environment.{u} count) :
    realize (substitute (instantiate index) body) environment = realize body (extend (environment index) environment) := by
  rw [realize_substitution, instantiate_environment]

def weakenReceipts {count : Nat} (assumptions : List (Formula count)) (environment : Environment.{u} count)
    (value : Graph.{u}) (receipts : Receipts assumptions environment) :
    Receipts (assumptions.map weakenFormula) (extend value environment) := by
  intro index
  let original : Fin assumptions.length := ⟨index.val, by simpa using index.isLt⟩
  have same : (assumptions.map weakenFormula)[index.val] = weakenFormula assumptions[original.val] := by
    simp [original]
  rw [same, realize_weaken]
  exact receipts original

inductive Proof : {count : Nat} → List (Formula count) → Formula count → Type where
  | hypothesis {count : Nat} {assumptions : List (Formula count)} (index : Fin assumptions.length) :
      Proof assumptions assumptions[index.val]
  | weakening {count : Nat} {assumptions larger : List (Formula count)} {formula : Formula count}
      (proof : Proof assumptions formula) (positions : Fin assumptions.length → Fin larger.length)
      (same : ∀ index, larger[(positions index).val] = assumptions[index.val]) : Proof larger formula
  | bottomElim {count : Nat} {assumptions : List (Formula count)} {formula : Formula count}
      (proof : Proof assumptions .bottom) : Proof assumptions formula
  | bothIntro {count : Nat} {assumptions : List (Formula count)} {left right : Formula count}
      (leftProof : Proof assumptions left) (rightProof : Proof assumptions right) : Proof assumptions (.both left right)
  | bothLeft {count : Nat} {assumptions : List (Formula count)} {left right : Formula count}
      (proof : Proof assumptions (.both left right)) : Proof assumptions left
  | bothRight {count : Nat} {assumptions : List (Formula count)} {left right : Formula count}
      (proof : Proof assumptions (.both left right)) : Proof assumptions right
  | eitherLeft {count : Nat} {assumptions : List (Formula count)} {left right : Formula count}
      (proof : Proof assumptions left) : Proof assumptions (.either left right)
  | eitherRight {count : Nat} {assumptions : List (Formula count)} {left right : Formula count}
      (proof : Proof assumptions right) : Proof assumptions (.either left right)
  | eitherElim {count : Nat} {assumptions : List (Formula count)} {left right result : Formula count}
      (proof : Proof assumptions (.either left right)) (leftBranch : Proof (left :: assumptions) result)
      (rightBranch : Proof (right :: assumptions) result) : Proof assumptions result
  | implyIntro {count : Nat} {assumptions : List (Formula count)} {left right : Formula count}
      (proof : Proof (left :: assumptions) right) : Proof assumptions (.imply left right)
  | implyElim {count : Nat} {assumptions : List (Formula count)} {left right : Formula count}
      (proof : Proof assumptions (.imply left right)) (premise : Proof assumptions left) : Proof assumptions right
  | allIntro {count : Nat} {assumptions : List (Formula count)} {body : Formula (count+1)}
      (proof : Proof (assumptions.map weakenFormula) body) : Proof assumptions (.all body)
  | allElim {count : Nat} {assumptions : List (Formula count)} {body : Formula (count+1)}
      (proof : Proof assumptions (.all body)) (index : Fin count) :
      Proof assumptions (substitute (instantiate index) body)
  | existIntro {count : Nat} {assumptions : List (Formula count)} {body : Formula (count+1)}
      (index : Fin count) (proof : Proof assumptions (substitute (instantiate index) body)) :
      Proof assumptions (.exist body)
  | existElim {count : Nat} {assumptions : List (Formula count)} {body : Formula (count+1)} {result : Formula count}
      (proof : Proof assumptions (.exist body))
      (branch : Proof (body :: assumptions.map weakenFormula) (weakenFormula result)) : Proof assumptions result
  | equalRefl {count : Nat} {assumptions : List (Formula count)} (index : Fin count) : Proof assumptions (.equal index index)
  | equalElim {count : Nat} {assumptions : List (Formula count)} {body : Formula (count+1)} {first second : Fin count}
      (same : Proof assumptions (.equal first second))
      (proof : Proof assumptions (substitute (instantiate first) body)) :
      Proof assumptions (substitute (instantiate second) body)

/-- Every deduction tree computes its result from the retained hypothesis
occurrences, including existential witnesses and equality strategies. -/
def interpret {count : Nat} {assumptions : List (Formula count)} {conclusion : Formula count}
    (proof : Proof assumptions conclusion) (environment : Environment.{u} count)
    (receipts : Receipts assumptions environment) : realize conclusion environment :=
  match proof with
  | .hypothesis index => receipts index
  | .weakening previous positions same =>
      interpret previous environment (fun index => same index ▸ receipts (positions index))
  | .bottomElim previous => PEmpty.elim (interpret previous environment receipts)
  | .bothIntro left right => ⟨interpret left environment receipts, interpret right environment receipts⟩
  | .bothLeft previous => (interpret previous environment receipts).1
  | .bothRight previous => (interpret previous environment receipts).2
  | .eitherLeft previous => .inl (interpret previous environment receipts)
  | .eitherRight previous => .inr (interpret previous environment receipts)
  | .eitherElim previous leftBranch rightBranch =>
      match interpret previous environment receipts with
      | .inl value => interpret leftBranch environment (consReceipts value receipts)
      | .inr value => interpret rightBranch environment (consReceipts value receipts)
  | .implyIntro previous => fun premise => interpret previous environment (consReceipts premise receipts)
  | .implyElim previous premise => interpret previous environment receipts (interpret premise environment receipts)
  | .allIntro previous => fun value => interpret previous (extend value environment) (weakenReceipts _ environment value receipts)
  | .allElim previous index =>
      (realize_instantiate _ index environment).symm ▸ interpret previous environment receipts (environment index)
  | .existIntro index previous =>
      ⟨environment index, realize_instantiate _ index environment ▸ interpret previous environment receipts⟩
  | .existElim previous branch =>
      let witness := interpret previous environment receipts
      realize_weaken _ environment witness.1 ▸
        interpret branch (extend witness.1 environment)
          (consReceipts witness.2 (weakenReceipts _ environment witness.1 receipts))
  | .equalRefl index => ⟨Equal.refl (environment index)⟩
  | .equalElim sameProof premiseProof =>
      let same := (interpret sameProof environment receipts).down
      let premise := realize_instantiate _ _ environment ▸ interpret premiseProof environment receipts
      (realize_instantiate _ _ environment).symm ▸
        GraphFormulaRealization.transport _ (extend (environment _) environment) (extend (environment _) environment)
          (Fin.cases same (fun index => Equal.refl (environment index))) premise

def closed {count : Nat} {conclusion : Formula count} (proof : Proof [] conclusion)
    (environment : Environment.{u} count) : realize conclusion environment :=
  interpret proof environment (fun index => False.elim (Nat.not_lt_zero _ index.isLt))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedDeduction
