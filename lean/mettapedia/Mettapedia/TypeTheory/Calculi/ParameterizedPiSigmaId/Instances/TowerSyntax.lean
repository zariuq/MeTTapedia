import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectors

/-!
# Typed syntax in the cumulative tower: the package

An extrinsic encoding of well-typed expressions indexed by their object type, with several
constructors at one index, presented inside the normalization model without a new case of its logical
relation. It is not an inductive family: at a variable index it has an element a family lacks, and
two typings of one expression are equal only propositionally.

The model's only self-referential type former is the simple inductive type: a constant with a fixed
list of constructors whose fields are the type itself or closed types. A family declared by recursion
on its index can refer to itself only at the fields of the index, so a constructor such as
`add : exp tnum → exp tnum → exp tnum`, whose arguments sit at the index of its result, needs a simple
inductive type declared before it. This package declares that type, the untyped expressions, and
refines it by a typing relation computed by recursion:

* the object types `ty` with `tnum`, `tbool`;
* the Booleans `bool` with `true`, `false`;
* the untyped expressions `raw`, with `rnum : num → raw`, `rbool : bool → raw`,
  `radd : raw → raw → raw`, `rif : raw → raw → raw → raw` and `riszero : raw → raw`;
* the computed equations of the index, `is-num t` and `is-bool t` (`unit` at the matching type,
  `void` at the other);
* the typing relation `typed : raw → ty → U0`, by recursion on the expression:

  `typed (rnum k) t ⟶ is-num t`, `typed (rbool b) t ⟶ is-bool t`,
  `typed (radd a b) t ⟶ Σ (is-num t). Σ (typed a tnum). typed b tnum`,
  `typed (rif c a b) t ⟶ Σ (typed c tbool). Σ (typed a t). typed b t`,
  `typed (riszero a) t ⟶ Σ (is-bool t). typed a tnum`;

* the value type `val : ty → U0`, `val tnum ⟶ num`, `val tbool ⟶ bool`;
* the transports along the computed equations, `at-num Q x t u : Q t` for `x : Q tnum` and
  `u : is-num t` (`at-num Q x tnum u ⟶ x`, and the empty type's recursor at `tbool`), and `at-bool`;
* **the recursion principle of typed expressions**, `syntax-rec`, by structural recursion on the
  untyped expression, with the index and the typing proof as later arguments:

  `syntax-rec : Π (Q : ty → U0) (mnum : num → Q tnum) (mbool : bool → Q tbool)
     (madd : Q tnum → Q tnum → Q tnum) (mif : Π (t : ty). Q tbool → Q t → Q t → Q t)
     (mzero : Q tnum → Q tbool) (r : raw) (t : ty) (p : typed r t). Q t`;

* addition and `is-zero : num → bool`, the interpreter's primitives.

The family is `exp t = Σ (r : raw). typed r t`; its constructors are pairs of an untyped constructor
and a tuple of proofs (`TowerSyntaxEval`).

The constants of each declaration's earlier stage are the package's own declared types restricted
to a list of names (`restrict`), with the package's computation; a stage only has to declare the
constants a body mentions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)
open TowerVectorsModel (unit tt unitRec void voidRec add unitCtors U0 numC zeroC succC unitC ttC
  addC unitRecC voidC voidRecC TowerLike)

namespace TowerSyntaxModel

/-! ## Names -/

/-- The Booleans. -/
def bool : DeclName := .mkSimple "bool"
def btrue : DeclName := .mkSimple "true"
def bfalse : DeclName := .mkSimple "false"
def boolRec : DeclName := .mkSimple "bool-rec"
/-- The object types. -/
def ty : DeclName := .mkSimple "ty"
def tnum : DeclName := .mkSimple "tnum"
def tbool : DeclName := .mkSimple "tbool"
def tyRec : DeclName := .mkSimple "ty-rec"
/-- The untyped expressions. -/
def raw : DeclName := .mkSimple "raw"
def rnum : DeclName := .mkSimple "rnum"
def rbool : DeclName := .mkSimple "rbool"
def radd : DeclName := .mkSimple "radd"
def rif : DeclName := .mkSimple "rif"
def rzero : DeclName := .mkSimple "riszero"
def rawRec : DeclName := .mkSimple "raw-rec"
/-- The computed equations of the index. -/
def isNum : DeclName := .mkSimple "is-num"
def isBool : DeclName := .mkSimple "is-bool"
/-- The value type. -/
def val : DeclName := .mkSimple "val"
/-- The typing relation. -/
def typing : DeclName := .mkSimple "typed"
/-- Zero test of the numbers. -/
def isZero : DeclName := .mkSimple "is-zero"
/-- The transports along the computed equations. -/
def atNum : DeclName := .mkSimple "at-num"
def atBool : DeclName := .mkSimple "at-bool"
/-- The recursion principle of typed expressions. -/
def synRec : DeclName := .mkSimple "syntax-rec"

/-- The field types of the untyped constructors with data. -/
abbrev numT : Tm Tower.Head 0 := .const num
abbrev boolT : Tm Tower.Head 0 := .const bool

def boolCtors : List (DeclName × List (Field Tower.Head)) := [(btrue, []), (bfalse, [])]
def tyCtors : List (DeclName × List (Field Tower.Head)) := [(tnum, []), (tbool, [])]
def rawCtors : List (DeclName × List (Field Tower.Head)) :=
  [(rnum, [.closed numT]), (rbool, [.closed boolT]), (radd, [.recursive, .recursive]),
   (rif, [.recursive, .recursive, .recursive]), (rzero, [.recursive])]

theorem mem_btrue : ((btrue, []) : DeclName × List (Field Tower.Head)) ∈ boolCtors := by
  simp [boolCtors]
theorem mem_bfalse : ((bfalse, []) : DeclName × List (Field Tower.Head)) ∈ boolCtors := by
  simp [boolCtors]
theorem mem_tnum : ((tnum, []) : DeclName × List (Field Tower.Head)) ∈ tyCtors := by simp [tyCtors]
theorem mem_tbool : ((tbool, []) : DeclName × List (Field Tower.Head)) ∈ tyCtors := by simp [tyCtors]
theorem mem_rnum : ((rnum, [.closed numT]) : DeclName × List (Field Tower.Head)) ∈ rawCtors := by
  simp [rawCtors]
theorem mem_rbool : ((rbool, [.closed boolT]) : DeclName × List (Field Tower.Head)) ∈ rawCtors := by
  simp [rawCtors]
theorem mem_radd : ((radd, [.recursive, .recursive]) : DeclName × List (Field Tower.Head)) ∈ rawCtors := by
  simp [rawCtors]
theorem mem_rif :
    ((rif, [.recursive, .recursive, .recursive]) : DeclName × List (Field Tower.Head)) ∈ rawCtors := by
  simp [rawCtors]
theorem mem_rzero : ((rzero, [.recursive]) : DeclName × List (Field Tower.Head)) ∈ rawCtors := by
  simp [rawCtors]

/-! ## Terms -/

abbrev boolC {n : Nat} : Tm Tower.Head n := .const bool
abbrev btrueC {n : Nat} : Tm Tower.Head n := .const btrue
abbrev bfalseC {n : Nat} : Tm Tower.Head n := .const bfalse
abbrev tyC {n : Nat} : Tm Tower.Head n := .const ty
abbrev tnumC {n : Nat} : Tm Tower.Head n := .const tnum
abbrev tboolC {n : Nat} : Tm Tower.Head n := .const tbool
abbrev rawC {n : Nat} : Tm Tower.Head n := .const raw
abbrev rnumC {n : Nat} (k : Tm Tower.Head n) : Tm Tower.Head n := .app (.const rnum) k
abbrev rboolC {n : Nat} (b : Tm Tower.Head n) : Tm Tower.Head n := .app (.const rbool) b
abbrev raddC {n : Nat} (a b : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const radd) a) b
abbrev rifC {n : Nat} (c a b : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.const rif) c) a) b
abbrev rzeroC {n : Nat} (a : Tm Tower.Head n) : Tm Tower.Head n := .app (.const rzero) a
abbrev isNumC {n : Nat} (t : Tm Tower.Head n) : Tm Tower.Head n := .app (.const isNum) t
abbrev isBoolC {n : Nat} (t : Tm Tower.Head n) : Tm Tower.Head n := .app (.const isBool) t
abbrev valC {n : Nat} (t : Tm Tower.Head n) : Tm Tower.Head n := .app (.const val) t
abbrev typingC {n : Nat} (r t : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const typing) r) t
abbrev isZeroC {n : Nat} (k : Tm Tower.Head n) : Tm Tower.Head n := .app (.const isZero) k
abbrev boolRecC {n : Nat} (P x y b : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.app (.const boolRec) P) x) y) b
abbrev atNumC {n : Nat} (Q x t p : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.app (.const atNum) Q) x) t) p
abbrev atBoolC {n : Nat} (Q x t p : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.app (.const atBool) Q) x) t) p
/-- `syntax-rec Q mnum mbool madd mif mzero r t p`. -/
abbrev synRecC {n : Nat} (Q m₁ m₂ m₃ m₄ m₅ r t p : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.const synRec) Q) m₁) m₂) m₃) m₄) m₅) r) t) p

/-- **The family of typed expressions**: `exp t = Σ (r : raw). typed r t`. -/
abbrev expC {n : Nat} (t : Tm Tower.Head n) : Tm Tower.Head n :=
  .sigma rawC (typingC (.var 0) (Presentation.rename wk t))

/-! ## The declarations by recursion -/

/-- The telescope of a family over the object types. -/
def tyEntries : (i : Nat) → Tm Tower.Head i := fun _ => tyC

/-- `is-num`: `unit` at `tnum`, `void` at `tbool`. -/
def isNumBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + 0 + (recPositions fields).length)
  | k, [] => if k = tnum then unitC else voidC
  | _, _ => unitC

/-- `is-bool`: `void` at `tnum`, `unit` at `tbool`. -/
def isBoolBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + 0 + (recPositions fields).length)
  | k, [] => if k = tnum then voidC else unitC
  | _, _ => unitC

/-- `val`: `num` at `tnum`, `bool` at `tbool`. -/
def valBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + 0 + (recPositions fields).length)
  | k, [] => if k = tnum then numC else boolC
  | _, _ => unitC

/-- The declared type of a family over the object types. -/
def tyFamType : Tm Tower.Head 0 := closeType (ofEntries tyEntries (0 + 1 + 0)) U0

theorem tyFamType_eq : tyFamType = .pi tyC U0 := rfl

/-- The telescope of `is-zero`. -/
def numEntries : (i : Nat) → Tm Tower.Head i := fun _ => numC

/-- `is-zero zero ⟶ true`, `is-zero (succ n) ⟶ false`. -/
def isZeroBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + 0 + (recPositions fields).length)
  | _, [] => btrueC
  | _, [.recursive] => (bfalseC : Tm Tower.Head 2)
  | _, _ => btrueC

def isZeroType : Tm Tower.Head 0 := closeType (ofEntries numEntries (0 + 1 + 0)) boolC

theorem isZeroType_eq : isZeroType = .pi numC boolC := rfl

/-- The telescope of the typing relation: an expression, then an object type. -/
def typingEntries : (i : Nat) → Tm Tower.Head i
  | 0 => rawC
  | _ + 1 => tyC

/-- The right-hand sides of the typing relation, the recursive calls abstracted as families over the
object types. -/
def typingBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + 1 + (recPositions fields).length)
  | k, [.closed _] => (if k = rnum then isNumC (.var 0) else isBoolC (.var 0) : Tm Tower.Head 2)
  | _, [.recursive, .recursive] =>
      (.sigma (isNumC (.var 2)) (.sigma (.app (.var 2) tnumC) (.app (.var 2) tnumC)) : Tm Tower.Head 5)
  | _, [.recursive, .recursive, .recursive] =>
      (.sigma (.app (.var 2) tboolC) (.sigma (.app (.var 2) (.var 4)) (.app (.var 2) (.var 5))) :
        Tm Tower.Head 7)
  | _, [.recursive] => (.sigma (isBoolC (.var 1)) (.app (.var 1) tnumC) : Tm Tower.Head 3)
  | _, _ => unitC

def typingType : Tm Tower.Head 0 := closeType (ofEntries typingEntries (0 + 1 + 1)) U0

theorem typingType_eq : typingType = .pi rawC (.pi tyC U0) := rfl

/-- The telescope of `at-num`: a family `Q` over the object types, `x : Q tnum`, the index `t`,
`u : is-num t`. -/
def atNumEntries : (i : Nat) → Tm Tower.Head i
  | 0 => .pi tyC U0
  | 1 => .app (.var 0) tnumC
  | 2 => tyC
  | 3 => isNumC (.var 0)
  | _ => tyC

/-- The telescope of `at-bool`. -/
def atBoolEntries : (i : Nat) → Tm Tower.Head i
  | 0 => .pi tyC U0
  | 1 => .app (.var 0) tboolC
  | 2 => tyC
  | 3 => isBoolC (.var 0)
  | _ => tyC

/-- The result `Q t` of the transports. -/
def atResult : Tm Tower.Head (2 + 1 + 1) := .app (.var 3) (.var 1)

/-- `at-num Q x tnum u ⟶ x`, `at-num Q x tbool u ⟶ void-rec (λ _. Q tbool) u`. -/
def atNumBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (2 + fields.length + 1 + (recPositions fields).length)
  | k, [] => (if k = tnum then .var 1 else voidRecC (.lam (.app (.var 3) tboolC)) (.var 0) :
      Tm Tower.Head 3)
  | _, _ => unitC

/-- `at-bool Q x tbool u ⟶ x`, `at-bool Q x tnum u ⟶ void-rec (λ _. Q tnum) u`. -/
def atBoolBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (2 + fields.length + 1 + (recPositions fields).length)
  | k, [] => (if k = tnum then voidRecC (.lam (.app (.var 3) tnumC)) (.var 0) else .var 1 :
      Tm Tower.Head 3)
  | _, _ => unitC

def atNumType : Tm Tower.Head 0 := closeType (ofEntries atNumEntries (2 + 1 + 1)) atResult
def atBoolType : Tm Tower.Head 0 := closeType (ofEntries atBoolEntries (2 + 1 + 1)) atResult

/-- The telescope of the recursion principle: the family `Q`, the five methods, the expression `r`,
the index `t`, the proof `p : typed r t`. -/
def synEntries : (i : Nat) → Tm Tower.Head i
  | 0 => .pi tyC U0
  | 1 => .pi numC (.app (.var 1) tnumC)
  | 2 => .pi boolC (.app (.var 2) tboolC)
  | 3 => .pi (.app (.var 2) tnumC) (.pi (.app (.var 3) tnumC) (.app (.var 4) tnumC))
  | 4 => .pi tyC (.pi (.app (.var 4) tboolC) (.pi (.app (.var 5) (.var 1))
      (.pi (.app (.var 6) (.var 2)) (.app (.var 7) (.var 3)))))
  | 5 => .pi (.app (.var 4) tnumC) (.app (.var 5) tboolC)
  | 6 => rawC
  | 7 => tyC
  | 8 => typingC (.var 1) (.var 0)
  | _ => rawC

/-- The result `Q t`. -/
def synResult : Tm Tower.Head (6 + 1 + 2) := .app (.var 8) (.var 1)

/-- The right-hand sides of the recursion principle, the recursive calls abstracted as functions of
the index and the proof:

* `rnum k`: `at-num Q (mnum k) t p`; `rbool b`: `at-bool Q (mbool b) t p`;
* `radd a b`: `at-num Q (madd (ha tnum (fst (snd p))) (hb tnum (snd (snd p)))) t (fst p)`;
* `rif c a b`: `mif t (hc tbool (fst p)) (ha t (fst (snd p))) (hb t (snd (snd p)))`;
* `riszero a`: `at-bool Q (mzero (ha tnum (snd p))) t (fst p)`. -/
def synBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (6 + fields.length + 2 + (recPositions fields).length)
  | k, [.closed _] =>
      (if k = rnum then atNumC (.var 8) (.app (.var 7) (.var 2)) (.var 1) (.var 0)
        else atBoolC (.var 8) (.app (.var 6) (.var 2)) (.var 1) (.var 0) : Tm Tower.Head 9)
  | _, [.recursive, .recursive] =>
      (atNumC (.var 11)
        (.app (.app (.var 8) (.app (.app (.var 1) tnumC) (.fst (.snd (.var 2)))))
          (.app (.app (.var 0) tnumC) (.snd (.snd (.var 2)))))
        (.var 3) (.fst (.var 2)) : Tm Tower.Head 12)
  | _, [.recursive, .recursive, .recursive] =>
      (.app (.app (.app (.app (.var 9) (.var 4)) (.app (.app (.var 2) tboolC) (.fst (.var 3))))
        (.app (.app (.var 1) (.var 4)) (.fst (.snd (.var 3)))))
        (.app (.app (.var 0) (.var 4)) (.snd (.snd (.var 3)))) : Tm Tower.Head 14)
  | _, [.recursive] =>
      (atBoolC (.var 9) (.app (.var 4) (.app (.app (.var 0) tnumC) (.snd (.var 1)))) (.var 2)
        (.fst (.var 1)) : Tm Tower.Head 10)
  | _, _ => unitC

def synType : Tm Tower.Head 0 := closeType (ofEntries synEntries (6 + 1 + 2)) synResult

/-! ## The package -/

variable (lv : LevelExpr Nat)

/-- The declared types of the package. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = num then some (.head u)
  else if name = zero then some (ctorType num [])
  else if name = succ then some (ctorType num [.recursive])
  else if name = numRec then some (recType num (.sort lv) ctors)
  else if name = unit then some (.head u)
  else if name = tt then some (ctorType unit [])
  else if name = unitRec then some (recType unit (.sort lv) unitCtors)
  else if name = void then some (.head u)
  else if name = voidRec then some (recType void (.sort lv) [])
  else if name = bool then some (.head u)
  else if name = btrue then some (ctorType bool [])
  else if name = bfalse then some (ctorType bool [])
  else if name = boolRec then some (recType bool (.sort lv) boolCtors)
  else if name = ty then some (.head u)
  else if name = tnum then some (ctorType ty [])
  else if name = tbool then some (ctorType ty [])
  else if name = tyRec then some (recType ty (.sort lv) tyCtors)
  else if name = raw then some (.head u)
  else if name = rnum then some (ctorType raw [.closed numT])
  else if name = rbool then some (ctorType raw [.closed boolT])
  else if name = radd then some (ctorType raw [.recursive, .recursive])
  else if name = rif then some (ctorType raw [.recursive, .recursive, .recursive])
  else if name = rzero then some (ctorType raw [.recursive])
  else if name = rawRec then some (recType raw (.sort lv) rawCtors)
  else if name = add then some TowerVectorsModel.addType
  else if name = isZero then some isZeroType
  else if name = isNum then some tyFamType
  else if name = isBool then some tyFamType
  else if name = val then some tyFamType
  else if name = typing then some typingType
  else if name = atNum then some atNumType
  else if name = atBool then some atBoolType
  else if name = synRec then some synType
  else none

/-- The computations: six recursors at their constructors, and the equations of nine definitions by
structural recursion. -/
def computations : List (DeclName × RootComputation Tower.Head) :=
  [(numRec, iotaComputation numRec ctors),
   (unitRec, iotaComputation unitRec unitCtors),
   (voidRec, iotaComputation voidRec []),
   (boolRec, iotaComputation boolRec boolCtors),
   (tyRec, iotaComputation tyRec tyCtors),
   (rawRec, iotaComputation rawRec rawCtors),
   (add, recursionComputation add ctors TowerVectorsModel.addEntries 0 1 TowerVectorsModel.addBody),
   (isZero, recursionComputation isZero ctors numEntries 0 0 isZeroBody),
   (isNum, recursionComputation isNum tyCtors tyEntries 0 0 isNumBody),
   (isBool, recursionComputation isBool tyCtors tyEntries 0 0 isBoolBody),
   (val, recursionComputation val tyCtors tyEntries 0 0 valBody),
   (typing, recursionComputation typing rawCtors typingEntries 0 1 typingBody),
   (atNum, recursionComputation atNum tyCtors atNumEntries 2 1 atNumBody),
   (atBool, recursionComputation atBool tyCtors atBoolEntries 2 1 atBoolBody),
   (synRec, recursionComputation synRec rawCtors synEntries 6 2 synBody)]

/-- The names of the package's constants. -/
def allNames : List DeclName :=
  [num, zero, succ, numRec, unit, tt, unitRec, void, voidRec, bool, btrue, bfalse, boolRec, ty, tnum,
    tbool, tyRec, raw, rnum, rbool, radd, rif, rzero, rawRec, add, isZero, isNum, isBool, val, typing,
    atNum, atBool, synRec]

/-- **The package**: the tower with numbers, the unit, empty and Boolean types, the object types,
the untyped expressions with their typing relation, the value type, the transports along the index
equations and the recursion principle of typed expressions; the recursors' motives land in level `lv`.
Its declared constants are the listed ones. -/
def rules : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name => if name ∈ allNames then constantType lv name else none
    computation := RootComputation.unionAll computations }

/-! ## Roles -/

/-- The roles of the constants other than the inductive types. -/
def otherRoles : Roles Tower.Head := fun name =>
  if name = zero then .constructor 0
  else if name = succ then .constructor 1
  else if name = tt then .constructor 0
  else if name = btrue then .constructor 0
  else if name = bfalse then .constructor 0
  else if name = tnum then .constructor 0
  else if name = tbool then .constructor 0
  else if name = rnum then .constructor 1
  else if name = rbool then .constructor 1
  else if name = radd then .constructor 2
  else if name = rif then .constructor 3
  else if name = rzero then .constructor 1
  else if name = numRec then .computes 4 (.split 3 .constructor fun _ => .leaf)
  else if name = unitRec then .computes 3 (.split 2 .constructor fun _ => .leaf)
  else if name = voidRec then .computes 2 (.split 1 .constructor fun _ => .leaf)
  else if name = boolRec then .computes 4 (.split 3 .constructor fun _ => .leaf)
  else if name = tyRec then .computes 4 (.split 3 .constructor fun _ => .leaf)
  else if name = rawRec then .computes 7 (.split 6 .constructor fun _ => .leaf)
  else if name = add then .computes 2 (.split 0 .constructor fun _ => .leaf)
  else if name = isZero then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = isNum then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = isBool then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = val then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = typing then .computes 2 (.split 0 .constructor fun _ => .leaf)
  else if name = atNum then .computes 4 (.split 2 .constructor fun _ => .leaf)
  else if name = atBool then .computes 4 (.split 2 .constructor fun _ => .leaf)
  else if name = synRec then .computes 9 (.split 6 .constructor fun _ => .leaf)
  else .rigid

/-- The roles of the declared constants: six inductive types first. -/
def roles : Roles Tower.Head := fun name =>
  if name = num then .inductive ctors
  else if name = unit then .inductive unitCtors
  else if name = void then .inductive []
  else if name = bool then .inductive boolCtors
  else if name = ty then .inductive tyCtors
  else if name = raw then .inductive rawCtors
  else otherRoles name

/-- An `if` differs from a value when both branches do. -/
theorem ite_ne_of {α : Sort _} {c : Prop} [Decidable c] {a b x : α} (ha : c → a ≠ x)
    (hb : ¬ c → b ≠ x) : (if c then a else b) ≠ x := by
  by_cases h : c
  · rw [if_pos h]
    exact ha h
  · rw [if_neg h]
    exact hb h

/-- The other constants are never inductive types. -/
theorem otherRoles_not_inductive (name : DeclName) (cs : List (DeclName × List (Field Tower.Head))) :
    otherRoles name ≠ .inductive cs := by
  unfold otherRoles
  repeat (refine ite_ne_of (fun _ h => nomatch h) (fun _ => ?_))
  exact fun h => nomatch h

theorem roles_num : roles num = .inductive ctors := rfl
theorem roles_unit : roles unit = .inductive unitCtors := rfl
theorem roles_void : roles void = .inductive [] := rfl
theorem roles_bool : roles bool = .inductive boolCtors := rfl
theorem roles_ty : roles ty = .inductive tyCtors := rfl
theorem roles_raw : roles raw = .inductive rawCtors := rfl
theorem roles_numRec : roles numRec = .computes (ctors.length + 2)
    (.split (ctors.length + 1) .constructor fun _ => .leaf) := rfl
theorem roles_unitRec : roles unitRec = .computes (unitCtors.length + 2)
    (.split (unitCtors.length + 1) .constructor fun _ => .leaf) := rfl
theorem roles_voidRec : roles voidRec =
    .computes (([] : List (DeclName × List (Field Tower.Head))).length + 2)
      (.split (([] : List (DeclName × List (Field Tower.Head))).length + 1) .constructor
        fun _ => .leaf) := rfl
theorem roles_boolRec : roles boolRec = .computes (boolCtors.length + 2)
    (.split (boolCtors.length + 1) .constructor fun _ => .leaf) := rfl
theorem roles_tyRec : roles tyRec = .computes (tyCtors.length + 2)
    (.split (tyCtors.length + 1) .constructor fun _ => .leaf) := rfl
theorem roles_rawRec : roles rawRec = .computes (rawCtors.length + 2)
    (.split (rawCtors.length + 1) .constructor fun _ => .leaf) := rfl
theorem roles_add : roles add = .computes (0 + 1 + 1) (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_isZero : roles isZero = .computes (0 + 1 + 0) (.split 0 .constructor fun _ => .leaf) :=
  rfl
theorem roles_isNum : roles isNum = .computes (0 + 1 + 0) (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_isBool : roles isBool = .computes (0 + 1 + 0) (.split 0 .constructor fun _ => .leaf) :=
  rfl
theorem roles_val : roles val = .computes (0 + 1 + 0) (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_typing : roles typing = .computes (0 + 1 + 1) (.split 0 .constructor fun _ => .leaf) :=
  rfl
theorem roles_atNum : roles atNum = .computes (2 + 1 + 1) (.split 2 .constructor fun _ => .leaf) := rfl
theorem roles_atBool : roles atBool = .computes (2 + 1 + 1) (.split 2 .constructor fun _ => .leaf) :=
  rfl
theorem roles_synRec : roles synRec = .computes (6 + 1 + 2) (.split 6 .constructor fun _ => .leaf) :=
  rfl

/-- The inductive types are `num`, `unit`, `void`, `bool`, `ty` and `raw`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    (role : roles T = .inductive cs) :
    (T = num ∧ cs = ctors) ∨ (T = unit ∧ cs = unitCtors) ∨ (T = void ∧ cs = []) ∨
      (T = bool ∧ cs = boolCtors) ∨ (T = ty ∧ cs = tyCtors) ∨ (T = raw ∧ cs = rawCtors) := by
  unfold roles at role
  by_cases h₁ : T = num
  · rw [if_pos h₁] at role
    exact .inl ⟨h₁, (Role.inductive.inj role).symm⟩
  rw [if_neg h₁] at role
  by_cases h₂ : T = unit
  · rw [if_pos h₂] at role
    exact .inr (.inl ⟨h₂, (Role.inductive.inj role).symm⟩)
  rw [if_neg h₂] at role
  by_cases h₃ : T = void
  · rw [if_pos h₃] at role
    exact .inr (.inr (.inl ⟨h₃, (Role.inductive.inj role).symm⟩))
  rw [if_neg h₃] at role
  by_cases h₄ : T = bool
  · rw [if_pos h₄] at role
    exact .inr (.inr (.inr (.inl ⟨h₄, (Role.inductive.inj role).symm⟩)))
  rw [if_neg h₄] at role
  by_cases h₅ : T = ty
  · rw [if_pos h₅] at role
    exact .inr (.inr (.inr (.inr (.inl ⟨h₅, (Role.inductive.inj role).symm⟩))))
  rw [if_neg h₅] at role
  by_cases h₆ : T = raw
  · rw [if_pos h₆] at role
    exact .inr (.inr (.inr (.inr (.inr ⟨h₆, (Role.inductive.inj role).symm⟩))))
  rw [if_neg h₆] at role
  exact absurd role (otherRoles_not_inductive T cs)

theorem constructorsDeclared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fields role mem
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    · simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · simp only [unitCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      obtain ⟨rfl, rfl⟩ := mem
      rfl
    · exact absurd mem List.not_mem_nil
    · simp only [boolCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  distinct := by
    intro T cs role
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;> decide

/-! ## The shape of the computation -/

theorem mem_numRec : (numRec, iotaComputation numRec ctors) ∈ computations := by
  simp [computations]
theorem mem_unitRec : (unitRec, iotaComputation unitRec unitCtors) ∈ computations := by
  simp [computations]
theorem mem_voidRec : (voidRec, iotaComputation voidRec []) ∈ computations := by
  simp [computations]
theorem mem_boolRec : (boolRec, iotaComputation boolRec boolCtors) ∈ computations := by
  simp [computations]
theorem mem_tyRec : (tyRec, iotaComputation tyRec tyCtors) ∈ computations := by
  simp [computations]
theorem mem_rawRec : (rawRec, iotaComputation rawRec rawCtors) ∈ computations := by
  simp [computations]
theorem mem_add : (add, recursionComputation add ctors TowerVectorsModel.addEntries 0 1
    TowerVectorsModel.addBody) ∈ computations := by
  simp [computations]
theorem mem_isZero : (isZero, recursionComputation isZero ctors numEntries 0 0 isZeroBody) ∈
    computations := by
  simp [computations]
theorem mem_isNum : (isNum, recursionComputation isNum tyCtors tyEntries 0 0 isNumBody) ∈
    computations := by
  simp [computations]
theorem mem_isBool : (isBool, recursionComputation isBool tyCtors tyEntries 0 0 isBoolBody) ∈
    computations := by
  simp [computations]
theorem mem_val : (val, recursionComputation val tyCtors tyEntries 0 0 valBody) ∈ computations := by
  simp [computations]
theorem mem_typing : (typing, recursionComputation typing rawCtors typingEntries 0 1 typingBody) ∈
    computations := by
  simp [computations]
theorem mem_atNum : (atNum, recursionComputation atNum tyCtors atNumEntries 2 1 atNumBody) ∈
    computations := by
  simp [computations]
theorem mem_atBool : (atBool, recursionComputation atBool tyCtors atBoolEntries 2 1 atBoolBody) ∈
    computations := by
  simp [computations]
theorem mem_synRec : (synRec, recursionComputation synRec rawCtors synEntries 6 2 synBody) ∈
    computations := by
  simp [computations]

theorem computations_spine : ∀ entry ∈ computations, SpineShaped roles entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact fun _ _ _ step => IotaStep.spine (T := num) roles_num roles_numRec constructorsDeclared step
  · exact fun _ _ _ step => IotaStep.spine (T := unit) roles_unit roles_unitRec constructorsDeclared step
  · exact fun _ _ _ step => IotaStep.spine (T := void) roles_void roles_voidRec constructorsDeclared step
  · exact fun _ _ _ step => IotaStep.spine (T := bool) roles_bool roles_boolRec constructorsDeclared step
  · exact fun _ _ _ step => IotaStep.spine (T := ty) roles_ty roles_tyRec constructorsDeclared step
  · exact fun _ _ _ step => IotaStep.spine (T := raw) roles_raw roles_rawRec constructorsDeclared step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_add step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_isZero step
  · exact fun _ _ _ step => RecursionStep.spine roles_ty constructorsDeclared roles_isNum step
  · exact fun _ _ _ step => RecursionStep.spine roles_ty constructorsDeclared roles_isBool step
  · exact fun _ _ _ step => RecursionStep.spine roles_ty constructorsDeclared roles_val step
  · exact fun _ _ _ step => RecursionStep.spine roles_raw constructorsDeclared roles_typing step
  · exact fun _ _ _ step => RecursionStep.spine roles_ty constructorsDeclared roles_atNum step
  · exact fun _ _ _ step => RecursionStep.spine roles_ty constructorsDeclared roles_atBool step
  · exact fun _ _ _ step => RecursionStep.spine roles_raw constructorsDeclared roles_synRec step

theorem computations_headed : ∀ entry ∈ computations, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact iotaComputation_headed
  · exact iotaComputation_headed
  · exact iotaComputation_headed
  · exact iotaComputation_headed
  · exact iotaComputation_headed
  · exact iotaComputation_headed
  all_goals exact recursionComputation_headed

theorem computations_deterministic : ∀ entry ∈ computations, Deterministic entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact fun _ _ _ _ step step' => IotaStep.deterministic (T := num) roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := unit) roles_unit constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := void) roles_void constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := bool) roles_bool constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => IotaStep.deterministic (T := ty) roles_ty constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := raw) roles_raw constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_ty constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_ty constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_ty constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_raw constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_ty constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_ty constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_raw constructorsDeclared step step'

theorem computations_distinct : (computations.map Prod.fst).Nodup := by
  decide

theorem shape : RootShape (rules lv) roles where
  spine := fun step => RootComputation.unionAll_spine computations_spine step
  deterministic := fun step step' =>
    (RootComputation.unionAll_deterministic computations_distinct computations_headed
      computations_deterministic step step').symm

/-- The tower's level model, for this rule package. -/
def levels (valuation : Nat → Nat) : LevelModel (rules lv) ℕ where
  level := (TowerModel.levels valuation).level
  successor := (TowerModel.levels valuation).successor
  universe_typing := (TowerModel.levels valuation).universe_typing
  ground_typing := (TowerModel.levels valuation).ground_typing
  cumulative_universe := (TowerModel.levels valuation).cumulative_universe
  headEq_level := (TowerModel.levels valuation).headEq_level
  join_level := (TowerModel.levels valuation).join_level
  join_exists := (TowerModel.levels valuation).join_exists
  join_upper := (TowerModel.levels valuation).join_upper
  cumulative_refl := (TowerModel.levels valuation).cumulative_refl
  headEq_symm := (TowerModel.levels valuation).headEq_symm
  headEq_trans := (TowerModel.levels valuation).headEq_trans
  universe_decided := (TowerModel.levels valuation).universe_decided

/-- The normalization setting, at a generic equality. -/
def settingAt (valuation : Nat → Nat) (E : GenericEquality Tower.Head) : Setting Tower.Head ℕ where
  R := rules lv
  roles := roles
  E := E
  levels := levels lv valuation
  shape := shape lv
  constructors := constructorsDeclared

/-- The normalization setting, at the typed equality. -/
def setting (valuation : Nat → Nat) : Setting Tower.Head ℕ :=
  settingAt lv valuation (declarative (rules lv))

theorem laws (valuation : Nat → Nat) :
    (setting lv valuation).E.Laws (setting lv valuation).R (setting lv valuation).roles :=
  declarative_laws roles (levels lv valuation)

/-! ## Stages: the package's own declarations, restricted to a list of names -/

/-- The package with only the listed constants declared, and its full computation. -/
def restrict (names : List DeclName) : Rules Tower.Head :=
  { rules lv with constantType := fun name => if name ∈ names then constantType lv name else none }

theorem restrict_declared {names : List DeclName} {name : DeclName} {type : Tm Tower.Head 0}
    (declared : (restrict lv names).constantType name = some type) :
    name ∈ names ∧ constantType lv name = some type := by
  change (if name ∈ names then constantType lv name else none) = some type at declared
  split at declared
  · exact ⟨‹_›, declared⟩
  · cases declared

theorem restrict_of_mem {names : List DeclName} {name : DeclName} (mem : name ∈ names) :
    (restrict lv names).constantType name = constantType lv name := by
  change (if name ∈ names then constantType lv name else none) = _
  rw [if_pos mem]

/-- The package is its own stage at the list of all its names. -/
theorem rules_eq_restrict : (rules lv).constantType = (restrict lv allNames).constantType := rfl

/-- A declared constant of a stage of listed names is a declared constant of the package. -/
theorem declared_of_restrict {names : List DeclName} (listed : ∀ name ∈ names, name ∈ allNames)
    {name : DeclName} {type : Tm Tower.Head 0}
    (declared : (restrict lv names).constantType name = some type) :
    (rules lv).constantType name = some type := by
  obtain ⟨mem, found⟩ := restrict_declared lv declared
  change (if name ∈ allNames then constantType lv name else none) = some type
  rw [if_pos (listed name mem)]
  exact found

/-- A stage of listed names is a sub-package of the package. -/
theorem sub_restrict (names : List DeclName) (listed : ∀ name ∈ names, name ∈ allNames) :
    RulesSub (restrict lv names) (rules lv) :=
  ⟨id, id, id, id, id, fun declared => declared_of_restrict lv listed declared, id⟩

/-- A stage is a sub-package of a larger stage. -/
theorem restrict_mono {names names' : List DeclName} (sub : ∀ name ∈ names, name ∈ names') :
    RulesSub (restrict lv names) (restrict lv names') :=
  ⟨id, id, id, id, id, fun declared => by
    obtain ⟨mem, declared⟩ := restrict_declared lv declared
    rw [restrict_of_mem lv (sub _ mem)]
    exact declared, id⟩

/-- Adding one name to a stage. -/
theorem restrict_cons {x : DeclName} {names : List DeclName} {name : DeclName} {type : Tm Tower.Head 0}
    (declared : (restrict lv (x :: names)).constantType name = some type) :
    (restrict lv names).constantType name = some type ∨ (name = x ∧ constantType lv x = some type) := by
  obtain ⟨mem, found⟩ := restrict_declared lv declared
  rcases List.mem_cons.mp mem with same | mem'
  · subst same
    exact .inr ⟨rfl, found⟩
  · exact .inl (by rw [restrict_of_mem lv mem']; exact found)

/-- A stage has the tower's universes. -/
theorem towerLike_restrict (names : List DeclName) : TowerLike (restrict lv names) :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩

theorem towerLike_rules : TowerLike (rules lv) :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩

/-- Every constant of a stage is semantic when every listed constant is. -/
theorem allSemantic_restrict {S : Setting Tower.Head ℕ} {names : List DeclName}
    (each : ∀ name ∈ names, ∀ {type : Tm Tower.Head 0}, constantType lv name = some type →
      SemanticConstant S name type) :
    AllSemantic S (restrict lv names) := by
  intro name type declared
  obtain ⟨mem, declared⟩ := restrict_declared lv declared
  exact each name mem declared

/-! ### The stages of the package -/

/-- The inductive types with their constructors. -/
def baseNames : List DeclName :=
  [num, zero, succ, unit, tt, void, bool, btrue, bfalse, ty, tnum, tbool, raw, rnum, rbool, radd, rif,
    rzero]

/-- The stage of the typing relation: the base and the two equations of the index. -/
def typingNames : List DeclName := isNum :: isBool :: baseNames

/-- The stage of the transports: also the empty type's recursor. -/
def atNames : List DeclName := voidRec :: typingNames

/-- The stage of the recursion principle: also the typing relation and the transports. -/
def synNames : List DeclName := typing :: atNum :: atBool :: atNames

abbrev baseStage : Rules Tower.Head := restrict lv baseNames
abbrev typingStage : Rules Tower.Head := restrict lv typingNames
abbrev atStage : Rules Tower.Head := restrict lv atNames
abbrev synStage : Rules Tower.Head := restrict lv synNames

/-! ## The equations as steps -/

theorem isNum_tnum_step {n : Nat} : (rules lv).computation.step (isNumC tnumC : Tm Tower.Head n) unitC :=
  RootComputation.step_unionAll mem_isNum
    ⟨tnum, [], consSub tnumC fun i => Fin.elim0 i, [], mem_tnum, rfl, rfl, rfl⟩

theorem isNum_tbool_step {n : Nat} :
    (rules lv).computation.step (isNumC tboolC : Tm Tower.Head n) voidC :=
  RootComputation.step_unionAll mem_isNum
    ⟨tbool, [], consSub tboolC fun i => Fin.elim0 i, [], mem_tbool, rfl, rfl, rfl⟩

theorem isBool_tnum_step {n : Nat} :
    (rules lv).computation.step (isBoolC tnumC : Tm Tower.Head n) voidC :=
  RootComputation.step_unionAll mem_isBool
    ⟨tnum, [], consSub tnumC fun i => Fin.elim0 i, [], mem_tnum, rfl, rfl, rfl⟩

theorem isBool_tbool_step {n : Nat} :
    (rules lv).computation.step (isBoolC tboolC : Tm Tower.Head n) unitC :=
  RootComputation.step_unionAll mem_isBool
    ⟨tbool, [], consSub tboolC fun i => Fin.elim0 i, [], mem_tbool, rfl, rfl, rfl⟩

theorem val_tnum_step {n : Nat} : (rules lv).computation.step (valC tnumC : Tm Tower.Head n) numC :=
  RootComputation.step_unionAll mem_val
    ⟨tnum, [], consSub tnumC fun i => Fin.elim0 i, [], mem_tnum, rfl, rfl, rfl⟩

theorem val_tbool_step {n : Nat} : (rules lv).computation.step (valC tboolC : Tm Tower.Head n) boolC :=
  RootComputation.step_unionAll mem_val
    ⟨tbool, [], consSub tboolC fun i => Fin.elim0 i, [], mem_tbool, rfl, rfl, rfl⟩

theorem typing_rnum_step {n : Nat} (k t : Tm Tower.Head n) :
    (rules lv).computation.step (typingC (rnumC k) t) (isNumC t) :=
  RootComputation.step_unionAll mem_typing
    ⟨rnum, [.closed numT], consSub t (consSub (rnumC k) fun i => Fin.elim0 i), [k], mem_rnum, rfl, rfl,
      rfl⟩

theorem typing_rbool_step {n : Nat} (b t : Tm Tower.Head n) :
    (rules lv).computation.step (typingC (rboolC b) t) (isBoolC t) :=
  RootComputation.step_unionAll mem_typing
    ⟨rbool, [.closed boolT], consSub t (consSub (rboolC b) fun i => Fin.elim0 i), [b], mem_rbool, rfl,
      rfl, rfl⟩

theorem typing_radd_step {n : Nat} (a b t : Tm Tower.Head n) :
    (rules lv).computation.step (typingC (raddC a b) t)
      (.sigma (isNumC t) (.sigma (typingC (Presentation.rename wk a) tnumC)
        (typingC (Presentation.rename wk (Presentation.rename wk b)) tnumC))) :=
  RootComputation.step_unionAll mem_typing
    ⟨radd, [.recursive, .recursive], consSub t (consSub (raddC a b) fun i => Fin.elim0 i), [a, b],
      mem_radd, rfl, rfl, rfl⟩

theorem typing_rif_step {n : Nat} (c a b t : Tm Tower.Head n) :
    (rules lv).computation.step (typingC (rifC c a b) t)
      (.sigma (typingC c tboolC) (.sigma (typingC (Presentation.rename wk a) (Presentation.rename wk t))
        (typingC (Presentation.rename wk (Presentation.rename wk b))
          (Presentation.rename wk (Presentation.rename wk t))))) :=
  RootComputation.step_unionAll mem_typing
    ⟨rif, [.recursive, .recursive, .recursive], consSub t (consSub (rifC c a b) fun i => Fin.elim0 i),
      [c, a, b], mem_rif, rfl, rfl, rfl⟩

theorem typing_rzero_step {n : Nat} (a t : Tm Tower.Head n) :
    (rules lv).computation.step (typingC (rzeroC a) t)
      (.sigma (isBoolC t) (typingC (Presentation.rename wk a) tnumC)) :=
  RootComputation.step_unionAll mem_typing
    ⟨rzero, [.recursive], consSub t (consSub (rzeroC a) fun i => Fin.elim0 i), [a], mem_rzero, rfl, rfl,
      rfl⟩

end TowerSyntaxModel

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
