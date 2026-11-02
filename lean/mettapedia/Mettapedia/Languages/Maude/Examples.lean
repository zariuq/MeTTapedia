import Mettapedia.Languages.Maude.Semantics

/-! Prepared first-order theories for the fixed M0 reference programs.
The two modules in the bag file stay separate theories. These fixtures do
not assert that ordinary-source lowering or equation certificates are done. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.Examples

def constant (id : String) : Term := .app id []
def binary (id : String) (first second : Term) : Term := .app id [first, second]
def n : Term := .var "N"
def m : Term := .var "M"
def bag : Term := .var "B"

def natData (namespaceName : String) : List Operator :=
  [⟨namespaceName ++ ".zero", "0", [], "Nat", {constructor := true}⟩,
   ⟨namespaceName ++ ".succ", "s", ["Nat"], "Nat", {constructor := true}⟩]

def numeral (namespaceName : String) : Nat → Term
  | 0 => constant (namespaceName ++ ".zero")
  | value + 1 => .app (namespaceName ++ ".succ") [numeral namespaceName value]

def peano : Theory := {
  name := "GOLD-PEANO"
  signature := ⟨["Nat"], natData "peano" ++
    [⟨"peano.add", "_+_", ["Nat", "Nat"], "Nat", {}⟩,
     ⟨"peano.mul", "_*_", ["Nat", "Nat"], "Nat", {}⟩]⟩
  equations := [
    ⟨"add-zero", [("M", "Nat")], [], binary "peano.add" (numeral "peano" 0) m, m⟩,
    ⟨"add-succ", [("N", "Nat"), ("M", "Nat")], [],
      binary "peano.add" (.app "peano.succ" [n]) m, .app "peano.succ" [binary "peano.add" n m]⟩,
    ⟨"mul-zero", [("M", "Nat")], [], binary "peano.mul" (numeral "peano" 0) m, numeral "peano" 0⟩,
    ⟨"mul-succ", [("N", "Nat"), ("M", "Nat")], [],
      binary "peano.mul" (.app "peano.succ" [n]) m, binary "peano.add" m (binary "peano.mul" n m)⟩]}

def bagOperators (namespaceName sort : String) : List Operator :=
  [⟨namespaceName ++ ".empty", "empty", [], sort, {constructor := true}⟩,
   ⟨namespaceName ++ ".a", "a", [], sort, {constructor := true}⟩,
   ⟨namespaceName ++ ".b", "b", [], sort, {constructor := true}⟩,
   ⟨namespaceName ++ ".merge", "__", [sort, sort], sort,
     {constructor := true, associative := true, commutative := true, identity := some (constant (namespaceName ++ ".empty"))}⟩]

def cardinality : Theory := {
  name := "GOLD-BAG"
  signature := ⟨["Nat", "Bag"], natData "bag" ++ bagOperators "bag" "Bag" ++
    [⟨"bag.card", "card", ["Bag"], "Nat", {}⟩]⟩
  equations := [
    ⟨"card-empty", [], [], .app "bag.card" [constant "bag.empty"], numeral "bag" 0⟩,
    ⟨"card-a", [("B", "Bag")], [], .app "bag.card" [binary "bag.merge" (constant "bag.a") bag],
      .app "bag.succ" [.app "bag.card" [bag]]⟩,
    ⟨"card-b", [("B", "Bag")], [], .app "bag.card" [binary "bag.merge" (constant "bag.b") bag],
      .app "bag.succ" [.app "bag.card" [bag]]⟩]}

def idempotent : Theory := {
  name := "GOLD-SET"
  signature := ⟨["Bag"], bagOperators "set" "Bag"⟩
  equations := [⟨"idempotence", [("B", "Bag")], [], binary "set.merge" bag bag, bag⟩]}

def conditional : Theory := {
  name := "GOLD-MAX"
  signature := ⟨["Nat", "Bool"], natData "max" ++
    [⟨"max.true", "true", [], "Bool", {constructor := true}⟩,
     ⟨"max.false", "false", [], "Bool", {constructor := true}⟩,
     ⟨"max.le", "_<=_", ["Nat", "Nat"], "Bool", {}⟩,
     ⟨"max.max", "max", ["Nat", "Nat"], "Nat", {}⟩]⟩
  equations := [
    ⟨"le-zero", [("N", "Nat")], [], binary "max.le" (numeral "max" 0) n, constant "max.true"⟩,
    ⟨"le-succ-zero", [("N", "Nat")], [], binary "max.le" (.app "max.succ" [n]) (numeral "max" 0), constant "max.false"⟩,
    ⟨"le-succ-succ", [("N", "Nat"), ("M", "Nat")], [],
      binary "max.le" (.app "max.succ" [n]) (.app "max.succ" [m]), binary "max.le" n m⟩,
    ⟨"max-left", [("N", "Nat"), ("M", "Nat")], [⟨binary "max.le" m n, constant "max.true"⟩], binary "max.max" n m, n⟩,
    ⟨"max-right", [("N", "Nat"), ("M", "Nat")], [⟨binary "max.le" n m, constant "max.true"⟩], binary "max.max" n m, m⟩]}

def markingOperators (namespaceName : String) (names : List String) : List Operator :=
  names.map (fun name => ⟨namespaceName ++ "." ++ name, name, [], "Marking", {constructor := true}⟩) ++
    [⟨namespaceName ++ ".merge", "__", ["Marking", "Marking"], "Marking",
      {constructor := true, associative := true, commutative := true, identity := some (constant (namespaceName ++ ".empty"))}⟩]

def marking (namespaceName : String) (tokens : List String) : Term :=
  (tokens.map (fun name => constant (namespaceName ++ "." ++ name))).foldr (binary (namespaceName ++ ".merge")) (constant (namespaceName ++ ".empty"))

def vending : Theory := {
  name := "GOLD-VENDING"
  signature := ⟨["Marking"], markingOperators "vending" ["empty", "$", "q", "a", "c"]⟩
  rules := [
    ⟨"coffee", [], [], constant "vending.$", constant "vending.c"⟩,
    ⟨"apple", [], [], constant "vending.$", binary "vending.merge" (constant "vending.a") (constant "vending.q")⟩,
    ⟨"change", [], [], binary "vending.merge" (constant "vending.q")
      (binary "vending.merge" (constant "vending.q") (binary "vending.merge" (constant "vending.q") (constant "vending.q"))),
      constant "vending.$"⟩]}

def mutex : Theory := {
  name := "GOLD-MUTEX"
  signature := ⟨["Marking"], markingOperators "mutex" ["empty", "idle1", "idle2", "crit1", "crit2", "permit", "init"]⟩
  equations := [⟨"init", [], [], constant "mutex.init",
    binary "mutex.merge" (constant "mutex.idle1") (binary "mutex.merge" (constant "mutex.idle2") (constant "mutex.permit"))⟩]
  rules := [
    ⟨"enter1", [], [], binary "mutex.merge" (constant "mutex.idle1") (constant "mutex.permit"), constant "mutex.crit1"⟩,
    ⟨"leave1", [], [], constant "mutex.crit1", binary "mutex.merge" (constant "mutex.idle1") (constant "mutex.permit")⟩,
    ⟨"enter2", [], [], binary "mutex.merge" (constant "mutex.idle2") (constant "mutex.permit"), constant "mutex.crit2"⟩,
    ⟨"leave2", [], [], constant "mutex.crit2", binary "mutex.merge" (constant "mutex.idle2") (constant "mutex.permit")⟩]}

def theories : List Theory := [peano, cardinality, idempotent, conditional, vending, mutex]

#guard theories.all Theory.check
#guard !( {peano.signature with sorts := []} : Signature).check
#guard !( {peano.signature with operators := peano.signature.operators ++ peano.signature.operators} : Signature).check
#guard !( {cardinality.signature with operators := cardinality.signature.operators ++
  [⟨"bad.unit", "bad", ["Bag", "Bag"], "Bag", {identity := some (constant "bag.zero")}⟩]} : Signature).check

end Mettapedia.Languages.Maude.Examples
