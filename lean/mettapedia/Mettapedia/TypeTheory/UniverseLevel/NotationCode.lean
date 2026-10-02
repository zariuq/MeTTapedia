import Mettapedia.TypeTheory.UniverseLevel.Notation

/-!
# An explicit code of the ordinal notations

Each notation tree is written as a list of natural numbers in prefix order: `zero` is `[0]`,
and `oadd e n a` is `n + 1` followed by the code of `e` and the code of `a`. Reading a list
back is a function. The two are inverse: the code of a tree reads back as that tree, and a
list that reads as a tree is the code of that tree. No choice is used.

Positive example: the code of `ω` is `[1, 1, 0, 0, 0]`, and it reads back as `ω`. Negative
examples: the empty list and `[1, 0]` are codes of no tree, and a code followed by further
numbers is not a code.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

namespace Cnf

/-- The code of a notation tree, in prefix order. -/
def code : Cnf → List Nat
  | zero => [0]
  | oadd e n a => (n + 1) :: (code e ++ code a)

/-- Read one notation tree from the front of a list, in at most the given number of steps.
The result is the tree and the rest of the list. -/
def readFuel : Nat → List Nat → Option (Cnf × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, 0 :: rest => some (zero, rest)
  | fuel + 1, (n + 1) :: rest =>
    match readFuel fuel rest with
    | none => none
    | some (e, rest') =>
      match readFuel fuel rest' with
      | none => none
      | some (a, rest'') => some (oadd e n a, rest'')

/-- The code of a tree, followed by anything, reads back as the tree and what follows, once
the fuel covers the length of the code. -/
theorem readFuel_code (x : Cnf) :
    ∀ (fuel : Nat) (rest : List Nat), (code x).length ≤ fuel →
      readFuel fuel (code x ++ rest) = some (x, rest) := by
  induction x with
  | zero =>
    intro fuel rest enough
    cases fuel with
    | zero => exact absurd enough (by decide)
    | succ fuel => rfl
  | oadd e n a ihe iha =>
    intro fuel rest enough
    cases fuel with
    | zero => exact absurd enough (Nat.not_succ_le_zero _)
    | succ fuel =>
      have sizes : (code e).length + (code a).length ≤ fuel := by
        have : (code e ++ code a).length + 1 ≤ fuel + 1 := enough
        rw [List.length_append] at this
        exact Nat.le_of_succ_le_succ this
      have first : readFuel fuel (code e ++ (code a ++ rest)) = some (e, code a ++ rest) :=
        ihe fuel _ (Nat.le_trans (Nat.le_add_right _ _) sizes)
      have second : readFuel fuel (code a ++ rest) = some (a, rest) :=
        iha fuel _ (Nat.le_trans (Nat.le_add_left _ _) sizes)
      show readFuel (fuel + 1) ((n + 1) :: ((code e ++ code a) ++ rest)) = _
      rw [List.append_assoc]
      simp only [readFuel, first, second]

/-- A list that reads as a tree and a rest is the code of the tree followed by the rest. -/
theorem eq_code_append_of_readFuel :
    ∀ (fuel : Nat) (l : List Nat) (x : Cnf) (rest : List Nat),
      readFuel fuel l = some (x, rest) → l = code x ++ rest := by
  intro fuel
  induction fuel with
  | zero =>
    intro l x rest found
    cases found
  | succ fuel ih =>
    intro l x rest found
    cases l with
    | nil => cases found
    | cons k tail =>
      cases k with
      | zero =>
        have same : (zero, tail) = (x, rest) := Option.some.inj found
        cases same
        rfl
      | succ n =>
        simp only [readFuel] at found
        cases first : readFuel fuel tail with
        | none => simp [first] at found
        | some pair =>
          obtain ⟨e, rest'⟩ := pair
          cases second : readFuel fuel rest' with
          | none => simp [first, second] at found
          | some pair' =>
            obtain ⟨a, rest''⟩ := pair'
            simp only [first, second] at found
            have same : (oadd e n a, rest'') = (x, rest) := Option.some.inj found
            cases same
            rw [ih tail e rest' first, ih rest' a rest second]
            show (n + 1) :: (code e ++ (code a ++ rest)) =
              (n + 1) :: ((code e ++ code a) ++ rest)
            rw [List.append_assoc]

/-- The tree a list is the code of, if any. -/
def decode (l : List Nat) : Option Cnf :=
  match readFuel l.length l with
  | some (x, []) => some x
  | _ => none

/-- **The code of a tree reads back as the tree.** -/
theorem decode_code (x : Cnf) : decode (code x) = some x := by
  have read := readFuel_code x (code x).length [] (Nat.le_refl _)
  rw [List.append_nil] at read
  simp only [decode, read]

/-- **A list that reads as a tree is the code of that tree.** -/
theorem code_of_decode {l : List Nat} {x : Cnf} (found : decode l = some x) : code x = l := by
  unfold decode at found
  cases read : readFuel l.length l with
  | none =>
    rw [read] at found
    cases found
  | some pair =>
    obtain ⟨y, rest⟩ := pair
    rw [read] at found
    cases rest with
    | nil =>
      have same : y = x := Option.some.inj found
      have shape := eq_code_append_of_readFuel _ _ _ _ read
      rw [List.append_nil] at shape
      rw [← same]
      exact shape.symm
    | cons _ _ => cases found

/-- The code is injective. -/
theorem code_injective : Function.Injective code := fun x y same =>
  Option.some.inj ((decode_code x).symm.trans ((congrArg decode same).trans (decode_code y)))

end Cnf

namespace Level

/-- The code of an ordinal notation below ε₀: the code of its tree. -/
def code (d : Level) : List Nat := Cnf.code d.1

/-- The notation a list is the code of, if any: the list reads as a tree in normal form. -/
def decode (l : List Nat) : Option Level :=
  match Cnf.decode l with
  | some x => if normal : x.NF then some ⟨x, normal⟩ else none
  | none => none

/-- The code of a notation reads back as the notation. -/
theorem decode_code (d : Level) : decode (code d) = some d := by
  show (match Cnf.decode (Cnf.code d.1) with
    | some x => if normal : x.NF then some (⟨x, normal⟩ : Level) else none
    | none => none) = some d
  rw [Cnf.decode_code]
  exact dif_pos d.2

/-- A list that reads as a notation is the code of that notation. -/
theorem code_of_decode {l : List Nat} {d : Level} (found : decode l = some d) : code d = l := by
  unfold decode at found
  cases read : Cnf.decode l with
  | none =>
    rw [read] at found
    cases found
  | some x =>
    rw [read] at found
    by_cases normal : x.NF
    · simp only [dif_pos normal] at found
      have same : (⟨x, normal⟩ : Level) = d := Option.some.inj found
      rw [← same]
      exact Cnf.code_of_decode read
    · simp only [dif_neg normal] at found
      cases found

end Level

/-! ## Examples -/

/-- The code of `ω`. -/
example : Level.code Level.omega = [1, 1, 0, 0, 0] := by decide

/-- It reads back as `ω`. -/
example : Level.decode [1, 1, 0, 0, 0] = some Level.omega := Level.decode_code Level.omega

/-- The empty list is the code of no tree. -/
example : Cnf.decode [] = none := by decide

/-- A tree whose tail is missing is the code of no tree. -/
example : Cnf.decode [1, 0] = none := by decide

/-- A code followed by a further number is not a code. -/
example : Cnf.decode [0, 0] = none := by decide

end Mettapedia.TypeTheory.UniverseLevel
