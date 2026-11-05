import Mettapedia.Languages.CHR.Syntax

/-! Independent IR versions of the fixed ground-CHR reference programs.
These are ordinary programs consumed by the general compiler/controller. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Examples

def v (index : Nat) : Term := .var index
def n (value : Int) : Term := .value (.integer value)
def atom (name : String) : Term := .value (.atom name)
def h (name : String) (arguments : List Term) : Head := ⟨name, arguments⟩
def i (index : Nat) : IntExpr := .index index
def num (value : Int) : IntExpr := .literal value
def op (operator : IntOperator) (left right : IntExpr) : IntExpr := .operation operator left right
def cmp (operator : Comparison) (left right : IntExpr) : Guard := .compare operator left right
def fact (name : String) (arguments : List Value) : Constraint := ⟨name, arguments⟩

def minimum : Program :=
  ⟨[⟨"minimum", 1⟩], [⟨"minimum_remove", [h "minimum" [v 0]], [h "minimum" [v 1]],
    [cmp .lessEqual (i 0) (i 1)], []⟩]⟩

def gcd : Program :=
  ⟨[⟨"gcd", 1⟩], [⟨"gcd_zero", [], [h "gcd" [n 0]], [], []⟩,
    ⟨"gcd_reduce", [h "gcd" [v 0]], [h "gcd" [v 1]], [cmp .lessEqual (i 0) (i 1)],
      [.assign 2 (op .modulo (i 1) (i 0)), .tell (h "gcd" [v 2])]⟩]⟩

def sieve : Program :=
  ⟨[⟨"candidate", 1⟩, ⟨"prime", 1⟩],
   [⟨"sieve_end", [], [h "candidate" [n 1]], [], []⟩,
    ⟨"sieve_next", [], [h "candidate" [v 0]], [],
      [.tell (h "prime" [v 0]), .assign 1 (op .subtract (i 0) (num 1)), .tell (h "candidate" [v 1])]⟩,
    ⟨"sieve_remove", [h "prime" [v 0]], [h "prime" [v 1]],
      [cmp .equal (num 0) (op .modulo (i 1) (i 0))], []⟩]⟩

def fibonacci : Program :=
  ⟨[⟨"upto", 1⟩, ⟨"fib", 2⟩],
   [⟨"fib_duplicate", [h "fib" [v 0,v 1]], [h "fib" [v 0,v 1]], [], []⟩,
    ⟨"fib_next", [h "upto" [v 0],h "fib" [v 1,v 2],h "fib" [v 3,v 4]], [],
      [cmp .equal (i 3) (op .add (i 1) (num 1)), cmp .less (i 3) (i 0)],
      [.assign 5 (op .add (i 3) (num 1)), .assign 6 (op .add (i 2) (i 4)), .tell (h "fib" [v 5,v 6])]⟩]⟩

def paths : Program :=
  ⟨[⟨"path", 2⟩],
   [⟨"path_duplicate", [h "path" [v 0,v 1]], [h "path" [v 0,v 1]], [], []⟩,
    ⟨"path_transitive", [h "path" [v 0,v 1],h "path" [v 1,v 2]], [], [], [.tell (h "path" [v 0,v 2])]⟩]⟩

def propagation : Program :=
  ⟨[⟨"signal", 1⟩,⟨"published", 1⟩],
    [⟨"publish", [h "signal" [v 0]], [], [], [.tell (h "published" [v 0])]⟩]⟩

def guarded : Program :=
  ⟨[⟨"blocked", 1⟩,⟨"released", 1⟩],
    [⟨"release", [], [h "blocked" [v 0]], [cmp .less (i 0) (num 0)], [.tell (h "released" [v 0])]⟩]⟩

def partnerChoice : Program :=
  ⟨[⟨"gate",0⟩,⟨"item",1⟩,⟨"chosen",1⟩],
    [⟨"pick", [], [h "gate" [],h "item" [v 0]], [], [.tell (h "chosen" [v 0])]⟩]⟩

def partnerPair : Program :=
  ⟨[⟨"pair_gate",0⟩,⟨"pair_item",1⟩,⟨"chosen_pair",2⟩],
    [⟨"pick_pair", [], [h "pair_gate" [],h "pair_item" [v 0],h "pair_item" [v 1]], [],
      [.tell (h "chosen_pair" [v 0,v 1])]⟩]⟩

def guardedPartner : Program :=
  ⟨[⟨"guard_gate",0⟩,⟨"guard_item",1⟩,⟨"guard_chosen",1⟩],
    [⟨"guarded_pick", [], [h "guard_gate" [],h "guard_item" [v 0]],
      [cmp .greater (i 0) (num 1)], [.tell (h "guard_chosen" [v 0])]⟩]⟩

structure Example where
  name : String
  program : Program
  inputs : List Constraint
  expected : List Constraint

def examples : List Example :=
  [⟨"minimum", minimum, [4,2,2,9].map (fun value => fact "minimum" [.integer value]),
      [fact "minimum" [.integer 2]]⟩,
   ⟨"propagation", propagation, [fact "signal" [.integer 7],fact "signal" [.integer 7]],
      [fact "signal" [.integer 7],fact "signal" [.integer 7],
       fact "published" [.integer 7],fact "published" [.integer 7]]⟩,
   ⟨"gcd", gcd, [84,30,18].map (fun value => fact "gcd" [.integer value]), [fact "gcd" [.integer 6]]⟩,
   ⟨"sieve", sieve, [fact "candidate" [.integer 10]], [2,3,5,7].map (fun value => fact "prime" [.integer value])⟩,
   ⟨"fibonacci", fibonacci, [fact "upto" [.integer 6],fact "fib" [.integer 0,.integer 0],fact "fib" [.integer 1,.integer 1]],
      fact "upto" [.integer 6] :: [[0,0],[1,1],[2,1],[3,2],[4,3],[5,5],[6,8]].map
        (fun values => fact "fib" (values.map Value.integer))⟩,
   ⟨"cyclic_paths", paths, [fact "path" [.atom "a",.atom "b"],fact "path" [.atom "b",.atom "c"],fact "path" [.atom "c",.atom "a"]],
      ["a","b","c"].flatMap (fun left => ["a","b","c"].map (fun right => fact "path" [.atom left,.atom right]))⟩,
   ⟨"empty", ⟨[],[]⟩, [], []⟩,
   ⟨"guard_false", guarded, [fact "blocked" [.integer 0]], [fact "blocked" [.integer 0]]⟩,
   ⟨"guard_true", guarded, [fact "blocked" [.integer (-1)]], [fact "released" [.integer (-1)]]⟩,
   ⟨"partner_choice", partnerChoice,
      [fact "item" [.integer 2],fact "item" [.integer 1],fact "gate" []],
      [fact "item" [.integer 2],fact "chosen" [.integer 1]]⟩,
   ⟨"partner_choice_wide", partnerChoice,
      (List.range 20).map (fun n => fact "item" [.integer n]) ++ [fact "gate" []],
      (List.range 19).map (fun n => fact "item" [.integer n]) ++ [fact "chosen" [.integer 19]]⟩,
   ⟨"partner_pair", partnerPair,
      [1,2,3].map (fun n => fact "pair_item" [.integer n]) ++ [fact "pair_gate" []],
      [fact "pair_item" [.integer 1],fact "chosen_pair" [.integer 3,.integer 2]]⟩,
   ⟨"guarded_partner", guardedPartner,
      [fact "guard_item" [.integer 3],fact "guard_item" [.integer 1],fact "guard_gate" []],
      [fact "guard_item" [.integer 1],fact "guard_chosen" [.integer 3]]⟩]

end Mettapedia.Languages.CHR.Examples
