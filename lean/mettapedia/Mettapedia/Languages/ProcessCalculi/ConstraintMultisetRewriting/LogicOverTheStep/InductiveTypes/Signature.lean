import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Facts

/-!
# The signature of the examples: numbers, lists of numbers, vectors, and work rows

One store holds every example, so one placement serves them all. Contents are ground terms of the
step (`NamesOnTheStep.Expr`):

* numbers: `zeroE`, `succE x`; the row "`x` is a number" is `natRow x`, at the handle `num`;
* lists of numbers: `nilE`, `consE x l`; the row "`l` is a list" is `lstRow l`, at `lst`;
* vectors: the row "`l` is a vector of length `n`" is `vecRow n l`, at `vec`;
* work rows of the addition program, `askAdd x y`, `runAdd x y`, `outE v`, at `work`;
* `junkE`, a term that no constructor makes.

The installed schemas (`Schema`) and their activation (`activate`) are the declared constructors of
the three types, a schema that makes the row `natRow junkE` from nothing, one that makes the row of
the numeral two from nothing, and the three rules of addition. Each constructor activates the step
instance `ctor` of its declared rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes

open NamesOnTheStep NamesOnTheStep.IssuingControls

/-! ## Terms and rows -/

/-- Zero. -/
def zeroE : Expr := .sym 100
/-- The successor. -/
def succE (x : Expr) : Expr := .app (.sym 101) x
/-- The row "`x` is a number". -/
def natRow (x : Expr) : Expr := .app (.sym 102) x
/-- The empty list. -/
def nilE : Expr := .sym 110
/-- A list with a first element. -/
def consE (x l : Expr) : Expr := .app (.app (.sym 111) x) l
/-- The row "`l` is a list of numbers". -/
def lstRow (l : Expr) : Expr := .app (.sym 112) l
/-- The row "`l` is a vector of length `n`". -/
def vecRow (n l : Expr) : Expr := .app (.app (.sym 120) n) l
/-- A request for the sum of `x` and `y`. -/
def askAdd (x y : Expr) : Expr := .app (.app (.sym 130) x) y
/-- The state of an addition: `x` left to move, `y` moved so far. -/
def runAdd (x y : Expr) : Expr := .app (.app (.sym 131) x) y
/-- An answer. -/
def outE (v : Expr) : Expr := .app (.sym 132) v
/-- A term no constructor makes. -/
def junkE : Expr := .sym 199

/-- The numeral of a natural number. -/
def numeral : ℕ → Expr
  | 0 => zeroE
  | k + 1 => succE (numeral k)

/-- The list of numerals of a list of natural numbers. -/
def listE : List ℕ → Expr
  | [] => nilE
  | k :: ks => consE (numeral k) (listE ks)

theorem succE_injective {x y : Expr} (same : succE x = succE y) : x = y := by
  simp only [succE, Expr.app.injEq] at same
  exact same.2

theorem natRow_injective {x y : Expr} (same : natRow x = natRow y) : x = y := by
  simp only [natRow, Expr.app.injEq] at same
  exact same.2

theorem numeral_injective {k m : ℕ} (same : numeral k = numeral m) : k = m := by
  induction k generalizing m with
  | zero =>
      cases m with
      | zero => rfl
      | succ m => simp [numeral, zeroE, succE] at same
  | succ k ih =>
      cases m with
      | zero => simp [numeral, zeroE, succE] at same
      | succ m => exact congrArg (· + 1) (ih (succE_injective same))

/-! ## Handles -/

/-- The handles of the store's regions. -/
inductive Handle where
  | num
  | lst
  | vec
  | work
  | other
  deriving DecidableEq, Repr

/-- **Where a content lives.** -/
def place : Expr → Handle
  | .app (.sym 102) _ => .num
  | .app (.sym 112) _ => .lst
  | .app (.app (.sym 120) _) _ => .vec
  | .app (.app (.sym 130) _) _ => .work
  | .app (.app (.sym 131) _) _ => .work
  | .app (.sym 132) _ => .work
  | _ => .other

@[simp] theorem place_natRow (x : Expr) : place (natRow x) = .num := rfl
@[simp] theorem place_lstRow (l : Expr) : place (lstRow l) = .lst := rfl
@[simp] theorem place_vecRow (n l : Expr) : place (vecRow n l) = .vec := rfl
@[simp] theorem place_askAdd (x y : Expr) : place (askAdd x y) = .work := rfl
@[simp] theorem place_runAdd (x y : Expr) : place (runAdd x y) = .work := rfl
@[simp] theorem place_outE (v : Expr) : place (outE v) = .work := rfl

/-- The rows at `num` are the rows `natRow x`. -/
theorem place_num {e : Expr} (at_ : place e = .num) : ∃ x, e = natRow x := by
  unfold place at at_
  split at at_ <;> first | exact ⟨_, rfl⟩ | cases at_

/-- The rows at `lst` are the rows `lstRow l`. -/
theorem place_lst {e : Expr} (at_ : place e = .lst) : ∃ l, e = lstRow l := by
  unfold place at at_
  split at at_ <;> first | exact ⟨_, rfl⟩ | cases at_

/-- The rows at `vec` are the rows `vecRow n l`. -/
theorem place_vec {e : Expr} (at_ : place e = .vec) : ∃ n l, e = vecRow n l := by
  unfold place at at_
  split at at_ <;> first | exact ⟨_, _, rfl⟩ | cases at_

/-! ## Declared constructors -/

/-- **The numbers**: zero, and the successor of a number. -/
def natRules : Set (List Expr × Expr) :=
  {d | d = ([], natRow zeroE) ∨ ∃ x, d = ([natRow x], natRow (succE x))}

/-- **Lists of numbers**: the empty list, and a number in front of a list. -/
def lstRules : Set (List Expr × Expr) :=
  {d | d = ([], lstRow nilE) ∨ ∃ x l, d = ([natRow x, lstRow l], lstRow (consE x l))}

/-- **Vectors**: the empty vector at length zero, and a number in front of a vector of length `n`,
at length `succE n`. -/
def vecRules : Set (List Expr × Expr) :=
  {d | d = ([], vecRow zeroE nilE) ∨
    ∃ x n l, d = ([natRow x, vecRow n l], vecRow (succE n) (consE x l))}

/-! ## Schemas and their activation -/

/-- The installable schemas. -/
inductive Schema where
  | zero
  | succ
  | nil
  | cons
  | vnil
  | vcons
  | junk
  | shortcut
  | start
  | peel
  | finish
  deriving DecidableEq, Repr

/-- **Activation**: each constructor activates the step instance of its declared rule; `junk` makes
`natRow junkE` from nothing; `shortcut` makes the row of the numeral two from nothing, a generated row
without its premise; `start`, `peel`, `finish` are the rules of addition. -/
def activate : Schema → List Expr → Option (RuleInstance Expr)
  | .zero, [] => some (ctor ([], natRow zeroE))
  | .succ, [x] => some (ctor ([natRow x], natRow (succE x)))
  | .nil, [] => some (ctor ([], lstRow nilE))
  | .cons, [x, l] => some (ctor ([natRow x, lstRow l], lstRow (consE x l)))
  | .vnil, [] => some (ctor ([], vecRow zeroE nilE))
  | .vcons, [x, n, l] => some (ctor ([natRow x, vecRow n l], vecRow (succE n) (consE x l)))
  | .junk, [] => some (rule [] [] [natRow junkE])
  | .shortcut, [] => some (rule [] [] [natRow (succE (succE zeroE))])
  | .start, [x, y] => some (rule [askAdd x y] [natRow x, natRow y] [runAdd x y])
  | .peel, [x, y] => some (rule [runAdd (succE x) y] [] [runAdd x (succE y)])
  | .finish, [y] => some (rule [runAdd zeroE y] [] [outE y])
  | _, _ => none

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes
