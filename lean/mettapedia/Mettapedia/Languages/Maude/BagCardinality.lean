import Mettapedia.Languages.Maude.ACUFlattenSubstitution
import Mettapedia.Languages.Maude.Examples

/-! Cardinality in the authored GOLD-BAG source theory. The executable
reference observes the source atom count; the proofs below construct actual
equation instances and typed contexts. They are independent of the emitted
matcher and do not assert generic ACU confluence or frontend correctness.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Maude.BagCardinality

def zeroOperator : Operator := ⟨"bag.zero", "0", [], "Nat", {constructor := true}⟩
def successorOperator : Operator := ⟨"bag.succ", "s", ["Nat"], "Nat", {constructor := true}⟩
def cardOperator : Operator := ⟨"bag.card", "card", ["Bag"], "Nat", {}⟩
def mergeOperator : Operator := ⟨"bag.merge", "__", ["Bag", "Bag"], "Bag",
  {constructor := true, associative := true, commutative := true, identity := some (.app "bag.empty" [])}⟩
def token (letter : String) : Term := .app ("bag." ++ letter) []
def card (bag : Term) : Term := .app "bag.card" [bag]
def successor (term : Term) : Term := .app "bag.succ" [term]
def numeral := Examples.numeral "bag"

theorem zero_member : zeroOperator ∈ Examples.cardinality.signature.operators := by
  simp [zeroOperator, Examples.cardinality, Examples.natData]
theorem successor_member : successorOperator ∈ Examples.cardinality.signature.operators := by
  simp [successorOperator, Examples.cardinality, Examples.natData]
theorem card_member : cardOperator ∈ Examples.cardinality.signature.operators := by
  simp [cardOperator, Examples.cardinality]
theorem merge_member : mergeOperator ∈ Examples.cardinality.signature.operators := by
  simp [mergeOperator, Examples.cardinality, Examples.bagOperators, Examples.constant]

def operation : ACUOperation Examples.cardinality [] where
  declaration := mergeOperator
  declared := merge_member
  arguments := rfl
  associative := rfl
  commutative := rfl
  unit := .app "bag.empty" []
  identity := rfl
  unit_sorted := .app
    (declaration := ⟨"bag.empty", "empty", [], "Bag", {constructor := true}⟩)
    (by simp [Examples.cardinality, Examples.bagOperators]) .nil

def Allowed (letter : String) : Prop := letter = "a" ∨ letter = "b"

theorem token_sorted (context : VariableContext) (letter : String) (allowed : Allowed letter) :
    HasSort Examples.cardinality.signature context (token letter) "Bag" := by
  rcases allowed with rfl | rfl
  · exact .app (declaration := ⟨"bag.a", "a", [], "Bag", {constructor := true}⟩)
      (by simp [Examples.cardinality, Examples.bagOperators]) .nil
  · exact .app (declaration := ⟨"bag.b", "b", [], "Bag", {constructor := true}⟩)
      (by simp [Examples.cardinality, Examples.bagOperators]) .nil

theorem card_sorted {context : VariableContext} {term : Term}
    (typed : HasSort Examples.cardinality.signature context term "Bag") :
    HasSort Examples.cardinality.signature context (card term) "Nat" :=
  .app card_member (.cons typed .nil)

theorem successor_sorted {context : VariableContext} {term : Term}
    (typed : HasSort Examples.cardinality.signature context term "Nat") :
    HasSort Examples.cardinality.signature context (successor term) "Nat" :=
  .app successor_member (.cons typed .nil)

def successorFrame : ArgumentContext Examples.cardinality.signature [] "Nat" "Nat" :=
  ⟨successorOperator, successor_member, [], [], [], [], rfl, rfl, .nil, .nil⟩
def cardFrame : ArgumentContext Examples.cardinality.signature [] "Bag" "Nat" :=
  ⟨cardOperator, card_member, [], [], [], [], rfl, rfl, .nil, .nil⟩

def emptyRow : Row := ⟨"card-empty", [], [], card operation.unit, numeral 0⟩
def letterRow (letter : String) : Row := ⟨"card-" ++ letter, [("B", "Bag")], [],
  card (operation.merge (token letter) (.var "B")), successor (card (.var "B"))⟩

theorem emptyRow_member : emptyRow ∈ Examples.cardinality.equations := by
  simp [emptyRow, Examples.cardinality, card, operation, numeral, Examples.numeral, Examples.constant]

theorem letterRow_member (letter : String) (allowed : Allowed letter) :
    letterRow letter ∈ Examples.cardinality.equations := by
  rcases allowed with rfl | rfl <;>
    simp [letterRow, Examples.cardinality, card, successor, operation, ACUOperation.merge,
      mergeOperator, token, Examples.binary, Examples.constant, Examples.bag]

theorem empty_equivalent : Equivalent Examples.cardinality [] "Nat" (card operation.unit) (numeral 0) := by
  let assignment : Valuation := fun _ => operation.unit
  have contextEmpty : emptyRow.usedContext = [] := by simp [emptyRow, Row.usedContext]
  have valuation : TypedValuation Examples.cardinality.signature [] emptyRow.usedContext assignment := by
    intro name sort found
    rw [contextEmpty] at found
    cases found
  have left : HasSort Examples.cardinality.signature emptyRow.usedContext emptyRow.left "Nat" := by
    rw [contextEmpty]
    exact card_sorted operation.unit_sorted
  have right : HasSort Examples.cardinality.signature emptyRow.usedContext emptyRow.right "Nat" := by
    rw [contextEmpty]
    exact .app zero_member .nil
  have step := Equivalent.equation assignment emptyRow_member (by decide_cbv) left right valuation (.nil assignment)
  simpa only [emptyRow, card, operation, numeral, Examples.numeral, Examples.constant, String.reduceAppend,
    Term.substitute, List.map_cons, List.map_nil] using step

theorem letter_equivalent (letter : String) (allowed : Allowed letter) (rest : Term)
    (restTyped : HasSort Examples.cardinality.signature [] rest "Bag") :
    Equivalent Examples.cardinality [] "Nat" (card (operation.merge (token letter) rest))
      (successor (card rest)) := by
  let assignment : Valuation := fun _ => rest
  have contextSame : (letterRow letter).usedContext = [("B", "Bag")] := by
    simp [letterRow, Row.usedContext, card, successor, ACUOperation.merge, token, Term.variables]
  have valueTyped : HasSort Examples.cardinality.signature [("B", "Bag")] (.var "B") "Bag" :=
    .var (by simp [List.lookup])
  have valuation : TypedValuation Examples.cardinality.signature [] (letterRow letter).usedContext assignment := by
    intro name sort found
    rw [contextSame] at found
    have sortSame : sort = "Bag" := by
      simp only [List.lookup] at found
      split at found
      · exact (Option.some.inj found).symm
      · cases found
    subst sort
    exact restTyped
  have left : HasSort Examples.cardinality.signature (letterRow letter).usedContext (letterRow letter).left "Nat" := by
    rw [contextSame]
    apply card_sorted
    apply HasSort.app operation.declared
    rw [operation.arguments]
    exact .cons (token_sorted _ letter allowed) (.cons valueTyped .nil)
  have right : HasSort Examples.cardinality.signature (letterRow letter).usedContext (letterRow letter).right "Nat" := by
    rw [contextSame]
    exact successor_sorted (card_sorted valueTyped)
  have checked : (letterRow letter).check Examples.cardinality.signature = true := by
    rcases allowed with rfl | rfl <;> decide_cbv
  have step := Equivalent.equation assignment (letterRow_member letter allowed) checked left right valuation (.nil assignment)
  simpa only [letterRow, card, successor, ACUOperation.merge, token, Term.substitute, List.map_cons, List.map_nil,
    assignment] using step

theorem card_fold_equivalent (letters : List String) (allowed : ∀ letter ∈ letters, Allowed letter) :
    Equivalent Examples.cardinality [] "Nat" (card (operation.fold (letters.map token))) (numeral letters.length) := by
  induction letters with
  | nil => exact empty_equivalent
  | cons first rest ih =>
    have restAllowed := fun letter member => allowed letter (List.mem_cons_of_mem first member)
    have restSorted : operation.Sorted (rest.map token) := by
      intro term member
      obtain ⟨letter, inside, rfl⟩ := List.mem_map.mp member
      exact token_sorted [] letter (restAllowed letter inside)
    have root := letter_equivalent first (allowed first List.mem_cons_self)
      (operation.fold (rest.map token)) (operation.fold_sorted _ restSorted)
    have tail := Equivalent.argument successorFrame (ih restAllowed)
    simpa only [List.map_cons, List.length_cons, ACUOperation.fold, numeral, Examples.numeral, successorFrame,
      ArgumentContext.plug, successor, successorOperator, List.nil_append, Examples.constant, String.reduceAppend]
      using root.trans tail

def letters? (source : Term) : Option (List String) :=
  (operation.flatten source).mapM fun
    | .app "bag.a" [] => some "a"
    | .app "bag.b" [] => some "b"
    | _ => none

def value? : Term → Option Nat
  | .app "bag.zero" [] => some 0
  | .app "bag.succ" [source] => Nat.succ <$> value? source
  | .app "bag.card" [source] => List.length <$> letters? source
  | _ => none

#print axioms card_fold_equivalent

end Mettapedia.Languages.Maude.BagCardinality
