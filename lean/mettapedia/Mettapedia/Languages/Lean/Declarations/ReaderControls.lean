import Mettapedia.Languages.Lean.Declarations.Profile
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSource
import Mettapedia.TypeTheory.IndexedPositiveContainer

/-!
# Controls for reading Lean declarations

Lean's own `Nat` and a Lean length-indexed `Vec` are read and handed to the
existing authored Nat/Vec profile.  Admission gives the constructor codes of
the independently built vector family `IndexedInductiveNatVec.Vectors`, the
family whose `.module` text reaches the guest Nat/Vec declarations.  That
family is the vector container of the positive-container Vector control: at
each length its values are the container's extension, a payload at each of
`Fin length` positions, with the head of a `cons` at position 0.  The
general profile admits Lean's `Nat`, `List`, `Option`, `Sum`, `Eq`, `Or` and
`Nat.le`, keeps elimination and erasure facts, and admits `Fin` and `Exists`
with their proof fields as guards: `isLt : val < n` is the guard
`Nat.le (Nat.succ val) n` on the data field `val`, and `h : p w` the guard
`p w` on `w`.  It refuses by name a function field (`Rose`), a dependent field
that is data rather than a proof (`Sigma`), a nested occurrence (`Tree`) and a
mutual block (`Even`/`Odd`).  Without the Reader's proof information a guard
is a dependent data sort and is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.Controls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Profile

universe u

/-- Length-indexed vectors; the length of a cons is its first field. -/
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} (x : α) (v : Vec α n) : Vec α (n + 1)

/-- A recursive field under a function arrow. -/
inductive Rose where
  | leaf : Rose
  | node (children : Nat → Rose) : Rose

/-- A nested occurrence. -/
inductive Tree where
  | node (children : List Tree) : Tree

mutual
/-- A mutual pair. -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ {n : Nat} (odd : Odd n) : Even (n + 1)
inductive Odd : Nat → Prop where
  | succ {n : Nat} (even : Even n) : Odd (n + 1)
end

/-! ## Readings -/

/-- A reading as one line: the family, its elimination and kept fields. -/
def describe (name : Lean.Name) : Lean.Meta.MetaM String := do
  match ← read name with
  | .ok reading =>
      return s!"{reading.family.print} | {repr reading.elimination} | kept {reading.keptFields}"
  | .error refusal => return s!"refused: {repr refusal}"

/--
info: Nat parameters () indices () : Type { Nat.zero () : Nat; Nat.succ (n : Nat) : Nat; } | Mettapedia.Languages.Lean.Declarations.Elimination.anySort | kept [[], [true]]
-/
#guard_msgs in #eval do IO.println (← describe ``Nat)

/--
info: Mettapedia.Languages.Lean.Declarations.Controls.Vec parameters (α : Type) indices (a : Nat) : Type { Mettapedia.Languages.Lean.Declarations.Controls.Vec.nil () : ((Mettapedia.Languages.Lean.Declarations.Controls.Vec α) Nat.zero); Mettapedia.Languages.Lean.Declarations.Controls.Vec.cons (n : Nat, x : α, v : ((Mettapedia.Languages.Lean.Declarations.Controls.Vec α) n)) : ((Mettapedia.Languages.Lean.Declarations.Controls.Vec α) (Nat.succ n)); } | Mettapedia.Languages.Lean.Declarations.Elimination.anySort | kept [[], [true, true, true]]
-/
#guard_msgs in #eval do IO.println (← describe ``Vec)

/--
info: Eq parameters (α : Type, a : α) indices (index0 : α) : Prop { Eq.refl () : (((Eq α) a) a); } | Mettapedia.Languages.Lean.Declarations.Elimination.anySort | kept [[]]
-/
#guard_msgs in #eval do IO.println (← describe ``Eq)

/--
info: Or parameters (a : Prop, b : Prop) indices () : Prop { Or.inl (h : a) : ((Or a) b); Or.inr (h : b) : ((Or a) b); } | Mettapedia.Languages.Lean.Declarations.Elimination.propOnly | kept [[false], [false]]
-/
#guard_msgs in #eval do IO.println (← describe ``Or)

/--
info: Fin parameters (n : Nat) indices () : Type { Fin.mk (val : Nat, isLt : ((((LT.lt Nat) instLTNat) val) n)) : (Fin n); } | Mettapedia.Languages.Lean.Declarations.Elimination.anySort | kept [[true, false]]
-/
#guard_msgs in #eval do IO.println (← describe ``Fin)

/--
info: refused: Mettapedia.Languages.Lean.Declarations.Refusal.nestedOccurrences
  "Mettapedia.Languages.Lean.Declarations.Controls.Tree"
  1
-/
#guard_msgs in #eval do IO.println (← describe ``Tree)

/--
info: refused: Mettapedia.Languages.Lean.Declarations.Refusal.mutualBlock
  ["Mettapedia.Languages.Lean.Declarations.Controls.Even", "Mettapedia.Languages.Lean.Declarations.Controls.Odd"]
-/
#guard_msgs in #eval do IO.println (← describe ``Even)

/-! ## Lean's Nat and Vec are the existing authored vector family -/

/-- The authored Nat/Vec profile under Lean's names. -/
def leanNames : IndexedNatVecSource.Names :=
  { natural := "Nat", zero := "Nat.zero", successor := "Nat.succ",
    vector := "Mettapedia.Languages.Lean.Declarations.Controls.Vec", payload := "α" }

/-- Lean's `Vec` lowers to the authored vector constructors, field for field. -/
theorem lean_vec_lowered :
    (IndexedNatVecSource.lower leanNames (lean_family% Nat) (lean_family% Vec)).map
        (·.map (·.body)) =
      some ((IndexedNatVecNames.vectorSource "n" "x" "v").map (·.body)) := rfl

/-- Lean's `Nat` is admitted as the existing natural family. -/
theorem lean_nat_admitted :
    (IndexedNatVecSource.admitNatural leanNames (lean_family% Nat)).map
        (·.constructors.map (·.body)) =
      some (IndexedInductiveNatVec.Natural.admitted.constructors.map (·.body)) := rfl

/-- Lean's `Vec` is admitted with exactly the constructor codes of the
independently built vector family. -/
theorem lean_vec_admitted (A : Type) :
    (IndexedNatVecSource.admit A leanNames (lean_family% Nat) (lean_family% Vec)).map
        (·.constructors.map (·.body)) =
      some ((IndexedInductiveNatVec.Vectors.admitted A).constructors.map (·.body)) := rfl

/-- The family Lean's `Vec` admits to is the container of the Vector control
(`IndexedPositiveContainer.VectorControl.entry`): at each length, its values
are that container's extension. -/
noncomputable def lean_vec_container (A : Type) (length : IndexedInductiveNatVec.Natural.Carrier) :
    IndexedInductiveNatVec.Vectors.Vector A length ≃
      Mettapedia.TypeTheory.IndexedPositiveContainer.VectorControl.entry.container.Extension A
        (IndexedInductiveNatVec.Natural.toNat length) :=
  (IndexedInductiveNatVec.Vectors.listEquiv A length).trans
    ((Equiv.vectorEquivFin A _).trans (Equiv.uniqueSigma (fun _ : Unit => Fin _ → A)).symm)

/-- The head of a `cons` is the payload at the container's first position. -/
theorem lean_vec_container_cons_zero (A : Type) (length : IndexedInductiveNatVec.Natural.Carrier)
    (head : A) (tail : IndexedInductiveNatVec.Vectors.Vector A length) :
    (lean_vec_container A (IndexedInductiveNatVec.Natural.succ length)
        (IndexedInductiveNatVec.Vectors.cons head tail)).2
      ⟨0, by simp [IndexedInductiveNatVec.Natural.toNat_succ]⟩ = head := rfl

/-! ## The general profile -/

/-- The refusal of an admission, if any. -/
def refusalOf {α : Type} : Except Profile.Refusal α → Option Profile.Refusal
  | .error refusal => some refusal
  | .ok _ => none

/-- How many constructors an admission keeps, if it succeeds. -/
def admittedCount (family : SFamily) : Option Nat :=
  ((admit Model.syntactic family).toOption).map (·.constructors.length)

theorem nat_admitted : admittedCount (lean_family% Nat) = some 2 := rfl
theorem list_admitted : admittedCount (lean_family% List) = some 2 := rfl
theorem option_admitted : admittedCount (lean_family% Option) = some 2 := rfl
theorem sum_admitted : admittedCount (lean_family% Sum) = some 2 := rfl
theorem vec_admitted : admittedCount (lean_family% Vec) = some 2 := rfl
theorem eq_admitted : admittedCount (lean_family% Eq) = some 1 := rfl
theorem or_admitted : admittedCount (lean_family% Or) = some 2 := rfl

/-- A recursive field under an arrow is refused, as for every source. -/
theorem rose_refused :
    refusalOf (admit Model.syntactic (lean_family% Rose)) =
      some (.functionField "Mettapedia.Languages.Lean.Declarations.Controls.Rose.node" "") := rfl

theorem nat_le_admitted : admittedCount (lean_family% Nat.le) = some 2 := rfl

/-! ## Guards -/

/-- Admission of a whole reading, with its proof fields. -/
def admitReading (reading : Reading) :=
  admit Model.syntactic reading.family reading.proofFields reading.keptFields

def guardsOf (reading : Reading) :=
  guards Model.syntactic reading.family reading.proofFields

/-- `Fin.mk` keeps one data field; its proof field is the guard
`Nat.le (Nat.succ val) n`, Lean's `val < n` unfolded to its inductive head. -/
theorem fin_admitted :
    ((admitReading (lean_reading% Fin)).toOption).map (·.constructors.length) = some 1 := rfl

theorem fin_guard :
    guardsOf (lean_reading% Fin) =
      .ok [[⟨"isLt", 1, 1, .app (.app (.name "Nat.le") (.app (.name "Nat.succ") (.var ⟨0, by decide⟩)))
        (.name "n")⟩]] := rfl

/-- `Exists.intro` keeps its witness; its proof is the guard `p w`. -/
theorem exists_admitted :
    ((admitReading (lean_reading% Exists)).toOption).map (·.constructors.length) = some 1 := rfl

theorem exists_guard :
    guardsOf (lean_reading% Exists) =
      .ok [[⟨"h", 1, 1, .app (.name "p") (.var ⟨0, by decide⟩)⟩]] := rfl

/-! ## Run-time use, read from the inventory -/

/-- The code-equation exporter keeps `Fin.mk`'s value and drops its guard. -/
theorem fin_kept : inventoryKept (lean_reading% Fin) = some [("Fin.mk", [true, false])] := rfl

/-- In `Or`, an inductive proposition, the proof field is a data field of
sort `a` whose values are erased. -/
theorem or_kept :
    inventoryKept (lean_reading% Or) = some [("Or.inl", [false]), ("Or.inr", [false])] := rfl

/-- In `Nat.le`, the recursive proof is erased, the natural kept. -/
theorem nat_le_kept :
    inventoryKept (lean_reading% Nat.le) =
      some [("Nat.le.refl", []), ("Nat.le.step", [true, false])] := rfl

theorem vec_kept :
    inventoryKept (lean_reading% Vec) =
      some [("Mettapedia.Languages.Lean.Declarations.Controls.Vec.nil", []),
            ("Mettapedia.Languages.Lean.Declarations.Controls.Vec.cons", [true, true, true])] := rfl

/-- Negative: the second component of a dependent pair is data whose sort
depends on the first, not a proof; it is refused. -/
theorem sigma_refused :
    refusalOf (admitReading (lean_reading% Sigma)) = some (.dependentDataSort "Sigma.mk" "snd") := rfl

/-- Negative: without the Reader's proof information, the proof field of
`Fin.mk` is a dependent data sort, and is refused. -/
theorem fin_without_proof_fields_refused :
    refusalOf (admit Model.syntactic (lean_family% Fin)) =
      some (.dependentDataSort "Fin.mk" "isLt") := rfl

end Mettapedia.Languages.Lean.Declarations.Controls
