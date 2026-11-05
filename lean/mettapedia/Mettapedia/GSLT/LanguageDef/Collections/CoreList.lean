import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.Languages.MeTTa.PLeaTTa.PeTTaSpec.PrologTermAlgebra
import Mettapedia.Logic.Unification.ListSpliceTerms

/-!
# The LanguageDef core list and its form in each MeTTa dialect

The core list of a LanguageDef is Lean's `List`, the free monoid in its
`nil`/`cons` presentation. On the CeTTa wire it is written with `LNil` and
`LCons` (`CettaWire.encodeList`). Each MeTTa dialect writes a list of its own
terms as one of its terms, its **manifestation**:

* HE writes it as the expression of its elements (`he`): HE has no list
  values, and its list library reads expressions as sequences;
* plain PeTTa writes it as a Prolog list, cons cells ending in `[]`, which
  PeTTa prints `()` (`petta`);
* extended PeTTa and the Prime draft write it as a list value `[a b c]`,
  distinct from the expression `(a b c)` (`prime`).

`Contract` is what a manifestation and the dialect's own operations must
satisfy: reading inverts writing and accepts nothing else, writing is
injective, and length, indexing, head and tail computed by the dialect agree
with the core list. Each dialect's operations are defined on its own terms
(flat expressions, cons cells, list values), so each contract is a theorem
about that representation: `he_contract`, `petta_contract`, `prime_contract`,
`wire_contract`. All four therefore agree on every one of these observations
(`Contract.agree`), and their printers emit the elements in order
(`he_print`, `petta_print`, `prime_print`).

Controls: a list value is not the expression of its elements
(`Controls.list_value_ne_expression`); an improper cons chain is no list
(`Controls.improper_cells_not_a_list`); data spelled `(cons a (cons b nil))`
is a three-element expression, not the list `[a b]`
(`Controls.spelled_cons_is_data`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.CoreList

universe u

/-- A dialect's manifestation of lists of its terms, with its own operations. -/
structure Manifestation (T : Type u) where
  write : List T → T
  read : T → Option (List T)
  length : T → Option ℕ
  nth : T → ℕ → Option T
  head : T → Option T
  tail : T → Option T

/-- The contract a manifestation and its operations implement. -/
structure Contract {T : Type u} (M : Manifestation T) : Prop where
  read_write : ∀ xs, M.read (M.write xs) = some xs
  write_read : ∀ t xs, M.read t = some xs → M.write xs = t
  length_write : ∀ xs, M.length (M.write xs) = some xs.length
  nth_write : ∀ xs i, M.nth (M.write xs) i = xs[i]?
  head_write : ∀ xs, M.head (M.write xs) = xs.head?
  tail_write : ∀ x xs, M.tail (M.write (x :: xs)) = some (M.write xs)

namespace Contract

variable {T : Type u} {M : Manifestation T}

theorem write_injective (contract : Contract M) : Function.Injective M.write := by
  intro xs ys same
  have := congrArg M.read same
  rwa [contract.read_write, contract.read_write, Option.some.injEq] at this

/-- **Manifestations agree on every observation.** Two dialects that write
the same core list, each through its own translation of the elements, report
the same length, the translated element at each index, the translated head,
and tails that are again manifestations of the core tail. -/
theorem agree {T₁ T₂ α : Type*} {M₁ : Manifestation T₁} {M₂ : Manifestation T₂}
    (first : Contract M₁) (second : Contract M₂) (f : α → T₁) (g : α → T₂) (xs : List α) :
    M₁.length (M₁.write (xs.map f)) = M₂.length (M₂.write (xs.map g)) ∧
      (∀ i, (M₁.nth (M₁.write (xs.map f)) i) = (xs[i]?).map f ∧
        (M₂.nth (M₂.write (xs.map g)) i) = (xs[i]?).map g) ∧
      M₁.head (M₁.write (xs.map f)) = (xs.head?).map f ∧
      M₂.head (M₂.write (xs.map g)) = (xs.head?).map g := by
  refine ⟨by rw [first.length_write, second.length_write, List.length_map, List.length_map],
    fun i => ⟨by rw [first.nth_write, List.getElem?_map], by rw [second.nth_write,
      List.getElem?_map]⟩, by rw [first.head_write, List.head?_map],
    by rw [second.head_write, List.head?_map]⟩

end Contract

/-! ## The wire: `LNil` and `LCons` -/

section Wire

open CettaWire

/-- The core list on the wire. -/
def wire : Manifestation CettaWire.Term where
  write := encodeList id
  read := decodeList some
  length t := (decodeList some t).map List.length
  nth t i := (decodeList some t).bind (·[i]?)
  head t := (decodeList some t).bind List.head?
  tail t := (decodeList some t).bind fun xs => match xs with
    | [] => none
    | _ :: rest => some (encodeList id rest)

theorem wire_contract : Contract wire where
  read_write xs := decodeList_encodeList some id (fun _ => rfl) xs
  write_read t xs accepted := encodeList_decodeList some id (fun _ _ h => (Option.some.inj h).symm)
    t xs accepted
  length_write xs := by simp [wire, decodeList_encodeList some id (fun _ => rfl) xs]
  nth_write xs i := by simp [wire, decodeList_encodeList some id (fun _ => rfl) xs]
  head_write xs := by simp [wire, decodeList_encodeList some id (fun _ => rfl) xs]
  tail_write x xs := by
    simp [wire, decodeList_encodeList some id (fun _ => rfl) (x :: xs)]

end Wire

/-! ## HE: the expression of the elements -/

section HE

open Mettapedia.Languages.MeTTa.OSLFCore

/-- HE's own sequence operations: `size-atom`, `index-atom`, `car-atom`,
`cdr-atom`, on expressions. -/
def he : Manifestation Atom where
  write := .expression
  read | .expression xs => some xs | _ => none
  length | .expression xs => some xs.length | _ => none
  nth | .expression xs, i => xs[i]? | _, _ => none
  head | .expression (x :: _) => some x | _ => none
  tail | .expression (_ :: xs) => some (.expression xs) | _ => none

theorem he_contract : Contract he where
  read_write _ := rfl
  write_read t xs accepted := by
    cases t <;> simp [he] at accepted
    rw [accepted]; rfl
  length_write _ := rfl
  nth_write _ _ := rfl
  head_write xs := by cases xs <;> rfl
  tail_write _ _ := rfl

mutual
/-- HE's printed form, as tokens. -/
def heTokens : Atom → List String
  | .symbol s => [s]
  | .var v => ["$" ++ v]
  | .grounded g => [toString g]
  | .expression xs => "(" :: heTokensList xs ++ [")"]

def heTokensList : List Atom → List String
  | [] => []
  | x :: xs => heTokens x ++ heTokensList xs
end

theorem heTokensList_eq (xs : List Atom) : heTokensList xs = (xs.map heTokens).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [heTokensList, ih]

/-- HE prints the elements in order, between parentheses. -/
theorem he_print (xs : List Atom) :
    heTokens (he.write xs) = "(" :: (xs.map heTokens).flatten ++ [")"] := by
  simp [he, heTokens, heTokensList_eq]

end HE

/-! ## Plain PeTTa: cons cells -/

section PeTTa

open Mettapedia.Languages.MeTTa.PLeaTTa.PeTTaSpec.PrologCore.Canonical

/-- A Prolog list: cons cells ending in `[]`. -/
def cells (xs : List Tree) : Tree := Tree.prologList xs none

/-- Read a proper Prolog list, walking its cells. -/
def cellRead : Tree → Option (List Tree)
  | .node .nil [] => some []
  | .node .cons [x, rest] => (cellRead rest).map (x :: ·)
  | _ => none

/-- The number of cells before `[]`. -/
def cellLength : Tree → Option ℕ
  | .node .nil [] => some 0
  | .node .cons [_, rest] => (cellLength rest).map (· + 1)
  | _ => none

/-- The element in a cell, walking `i` cells first. -/
def cellNth : Tree → ℕ → Option Tree
  | .node .cons [x, _], 0 => some x
  | .node .cons [_, rest], i + 1 => cellNth rest i
  | _, _ => none

def cellHead : Tree → Option Tree
  | .node .cons [x, _] => some x
  | _ => none

def cellTail : Tree → Option Tree
  | .node .cons [_, rest] => some rest
  | _ => none

/-- PeTTa's own list operations, on cons cells. -/
def petta : Manifestation Tree where
  write := cells
  read := cellRead
  length := cellLength
  nth := cellNth
  head := cellHead
  tail := cellTail

@[simp] theorem cells_nil : cells [] = .node .nil [] := rfl
@[simp] theorem cells_cons (x : Tree) (xs : List Tree) :
    cells (x :: xs) = .node .cons [x, cells xs] := rfl

theorem cellRead_eq_some (t : Tree) (xs : List Tree) (accepted : cellRead t = some xs) :
    cells xs = t := by
  induction xs generalizing t with
  | nil =>
      unfold cellRead at accepted
      split at accepted
      · rfl
      · simp at accepted
      · simp at accepted
  | cons x xs ih =>
      unfold cellRead at accepted
      split at accepted
      · simp at accepted
      · rename_i y rest
        simp only [Option.map_eq_some_iff, List.cons.injEq] at accepted
        obtain ⟨ys, inner, rfl, rfl⟩ := accepted
        rw [cells_cons, ih rest inner]
      · simp at accepted

theorem petta_contract : Contract petta where
  read_write xs := by
    change cellRead (cells xs) = some xs
    induction xs with
    | nil => rfl
    | cons x xs ih => rw [cells_cons]; simp [cellRead, ih]
  write_read t xs accepted := cellRead_eq_some t xs accepted
  length_write xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [petta, cellLength] at *; exact ih
  nth_write xs i := by
    induction xs generalizing i with
    | nil => cases i <;> rfl
    | cons x xs ih =>
        cases i with
        | zero => rfl
        | succ i => simpa [petta, cellNth] using ih i
  head_write xs := by cases xs <;> rfl
  tail_write _ _ := rfl

mutual
/-- PeTTa's printed form of a term, as tokens: a proper list prints as a
MeTTa expression, an improper tail after a bar. -/
def cellTokens : Tree → List String
  | .node .nil [] => ["(", ")"]
  | .node .cons [x, rest] => "(" :: cellTokens x ++ tailTokens rest
  | .node (.atom name) _ => [name]
  | _ => ["?"]

/-- The rest of a cell chain. -/
def tailTokens : Tree → List String
  | .node .nil [] => [")"]
  | .node .cons [x, rest] => cellTokens x ++ tailTokens rest
  | other => "|" :: cellTokens other ++ [")"]
end

/-- PeTTa prints a Prolog list as the expression of its elements, in order,
walking its cells. -/
theorem petta_print (x : Tree) (xs : List Tree) :
    cellTokens (cells (x :: xs)) = "(" :: ((x :: xs).map cellTokens).flatten ++ [")"] := by
  have tail : ∀ ys : List Tree, tailTokens (cells ys) = (ys.map cellTokens).flatten ++ [")"] := by
    intro ys
    induction ys with
    | nil => simp [tailTokens]
    | cons y ys ih => simp [tailTokens, ih]
  simp [cellTokens, tail]

end PeTTa

/-! ## Extended PeTTa and Prime: list values -/

section Prime

open Mettapedia.Logic.Unification.ListSplice

variable {Leaf Var : Type}

/-- The list operations on list values. -/
def prime : Manifestation (Term Leaf Var) where
  write := .list
  read | .list xs => some xs | _ => none
  length | .list xs => some xs.length | _ => none
  nth | .list xs, i => xs[i]? | _, _ => none
  head | .list (x :: _) => some x | _ => none
  tail | .list (_ :: xs) => some (.list xs) | _ => none

theorem prime_contract : Contract (prime (Leaf := Leaf) (Var := Var)) where
  read_write _ := rfl
  write_read t xs accepted := by
    cases t <;> simp [prime] at accepted
    rw [accepted]; rfl
  length_write _ := rfl
  nth_write _ _ := rfl
  head_write xs := by cases xs <;> rfl
  tail_write _ _ := rfl

mutual
/-- The printed form of a list-value term, as tokens. -/
def primeTokens (leaf : Leaf → String) (var : Var → String) : Term Leaf Var → List String
  | .atom a => [leaf a]
  | .var v => ["$" ++ var v]
  | .expr xs => "(" :: primeTokensList leaf var xs ++ [")"]
  | .list xs => "[" :: primeTokensList leaf var xs ++ ["]"]
  | .rest xs tail => "[" :: primeTokensList leaf var xs ++ "|" :: primeTokens leaf var tail ++ ["]"]

def primeTokensList (leaf : Leaf → String) (var : Var → String) : List (Term Leaf Var) → List String
  | [] => []
  | x :: xs => primeTokens leaf var x ++ primeTokensList leaf var xs
end

theorem primeTokensList_eq (leaf : Leaf → String) (var : Var → String) (xs : List (Term Leaf Var)) :
    primeTokensList leaf var xs = (xs.map (primeTokens leaf var)).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [primeTokensList, ih]

/-- A list value prints its elements in order, between brackets. -/
theorem prime_print (leaf : Leaf → String) (var : Var → String) (xs : List (Term Leaf Var)) :
    primeTokens leaf var (prime.write xs) = "[" :: (xs.map (primeTokens leaf var)).flatten ++ ["]"] := by
  simp [prime, primeTokens, primeTokensList_eq]

end Prime

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.Unification.ListSplice
open Mettapedia.Languages.MeTTa.PLeaTTa.PeTTaSpec.PrologCore.Canonical

/-- `[a b] ≠ (a b)`: a list value is not the expression of its elements, and
the dialect's list operations refuse the expression. -/
theorem list_value_ne_expression :
    (prime.write [.atom "a", .atom "b"] : Term String String) ≠ .expr [.atom "a", .atom "b"] ∧
      prime.read (.expr [.atom "a", .atom "b"] : Term String String) = none := by
  exact ⟨by simp [prime], rfl⟩

/-- In HE the expression is the list: `(a b)` is the manifestation of `[a b]`. -/
theorem he_expression_is_the_list :
    he.write [.symbol "a", .symbol "b"] = .expression [.symbol "a", .symbol "b"] := rfl

/-- A cons chain ending in a symbol is improper: no list, no length. -/
theorem improper_cells_not_a_list :
    cellRead (.node .cons [.node (.atom "a") [], .node (.atom "b") []]) = none ∧
      cellLength (.node .cons [.node (.atom "a") [], .node (.atom "b") []]) = none := by
  exact ⟨rfl, rfl⟩

/-- Data spelled `(cons a (cons b nil))` is a three-element expression whose
head is `cons`, with the symbol `nil` at its end: not the list `[a b]`. -/
theorem spelled_cons_is_data :
    petta.read (petta.write [.node (.atom "cons") [], .node (.atom "a") [],
        cells [.node (.atom "cons") [], .node (.atom "b") [], .node (.atom "nil") []]]) =
      some [.node (.atom "cons") [], .node (.atom "a") [],
        cells [.node (.atom "cons") [], .node (.atom "b") [], .node (.atom "nil") []]] ∧
      cells [.node (.atom "a") [], .node (.atom "b") []] ≠
        cells [.node (.atom "cons") [], .node (.atom "a") [],
          cells [.node (.atom "cons") [], .node (.atom "b") [], .node (.atom "nil") []]] := by
  refine ⟨petta_contract.read_write _, ?_⟩
  intro same
  have := congrArg cellLength same
  simp [cellLength] at this

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.CoreList
