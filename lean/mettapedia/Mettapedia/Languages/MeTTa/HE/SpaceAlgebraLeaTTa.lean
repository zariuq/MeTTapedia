/-
# LeaTTa's named spaces as an instance of the abstract space algebra

`SpaceAlgebra.lean` fixes one signature (`StorageOps`) and separates the removal
semantics into law bundles (`CountedBagLaws` vs `SetLaws`).  This module cashes
that design out on a real engine: LeaTTa's named spaces.

Why this instantiation is shaped the way it is:

* **The carrier is the per-space `List Atom`, not the `HashMap`.**  LeaTTa's
  `World.spaces : HashMap String (List Atom)` is an indexed family of spaces;
  the storage algebra is about ONE space.  The content of one space is exactly
  the list stored under its key, so that list is the honest carrier, and the
  `World` layer is recovered by the projection lemmas at the end of the file.

* **`add a s := s ++ [a]`, appending on the RIGHT.**  This is not a free choice:
  `World.appendSpace` computes `(cur.getD []) ++ atoms`, and `World.eraseFromSpace`
  uses `List.erase`, which drops the FIRST occurrence.  Multiplicity alone cannot
  distinguish `s ++ [a]` from `a :: s`, but the pair (append-right, erase-first)
  is what makes LeaTTa's spaces behave first-in-first-out under repeated removal,
  so the orientation is chosen to match the source rather than to shorten a proof.
  `spaceContents_appendSpace` below pins the choice to `World.appendSpace`.

* **The atom type is restricted to the fragment where LeaTTa's own structural
  equality is an equality test.**  `Atom` carries `Ground.float`, and Lean's
  `Float` equality is IEEE 754, so `BEq Atom` is not lawful: a payload that is
  not equal to itself is not counted by `List.count` even after it is added.
  `rawSpaceOps_not_storageLaws` shows the restriction carries content: as soon as
  ONE `Float` fails self-equality — which IEEE `nan` does — the unrestricted
  instance breaks even the shared core law `multiplicity_add_self`.  Float-freeness
  is a sufficient condition, deliberately syntactic so that it is checkable by
  computation; it is not claimed to be the weakest such condition.

The payoff of the law-variant design is `leattaSpaceOps_not_setLaws`: LeaTTa's
named spaces satisfy `CountedBagLaws` and provably fail `SetLaws`, so the two
bundles separate a real engine rather than recording a distinction without a
difference.
-/
import Mettapedia.Languages.MeTTa.HE.SpaceAlgebra
import MettaHyperonFull.Proofs.Basic
import MettaHyperonFull.Minimal.Interpreter

namespace Mettapedia.Languages.MeTTa.HE.SpaceAlgebraLeaTTa

open Mettapedia.Languages.MeTTa.HE.SpaceAlgebra
open Metta (Atom Ground)
open Metta.Minimal (World)

/-! ## Counting and erasing agree on the same boolean test

Mathlib's `List.count_erase_self` and `List.count_erase_of_ne` are stated for a
`LawfulBEq` element type, which `Atom` is not.  The first of the two does not
actually need lawfulness: `List.erase` deletes the first element passing
`(· == a)` and `List.count a` counts the elements passing the very same test, so
the count drops by exactly one whenever anything was deleted.  Proving it in that
generality is what lets the counted-bag law hold for LeaTTa with no side
condition on the space contents at all. -/

/-- Erasing decrements the count by one, for an arbitrary (possibly unlawful)
`BEq`.  The two sides are driven by the identical boolean test, which is the
whole reason no lawfulness hypothesis is needed. -/
theorem count_erase_self {α : Type _} [BEq α] (a : α) (l : List α) :
    (l.erase a).count a = l.count a - 1 := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      by_cases h : (b == a) = true
      · rw [List.erase_cons, if_pos h, List.count_cons, if_pos h]
        omega
      · rw [List.erase_cons, if_neg h, List.count_cons, List.count_cons, if_neg h, ih]
        omega

/-- Erasing `b` leaves the count of `a` alone, provided nothing that passes the
`b`-test also passes the `a`-test.  Stated through the boolean tests rather than
through `a ≠ b` so that it applies to an unlawful `BEq`. -/
theorem count_erase_of_test {α : Type _} [BEq α] (a b : α) (l : List α)
    (h : ∀ x : α, (x == b) = true → (x == a) = false) :
    (l.erase b).count a = l.count a := by
  induction l with
  | nil => simp
  | cons c cs ih =>
      by_cases hc : (c == b) = true
      · rw [List.erase_cons, if_pos hc, List.count_cons, if_neg (by simp [h c hc])]
        omega
      · rw [List.erase_cons, if_neg hc, List.count_cons, List.count_cons, ih]

/-- Appending a single element adds one exactly when that element passes the
test. -/
theorem count_append_singleton {α : Type _} [BEq α] (a x : α) (l : List α) :
    (l ++ [x]).count a = l.count a + (if (x == a) = true then 1 else 0) := by
  rw [List.count_append, List.count_singleton]

/-! ## The fragment on which LeaTTa's structural equality is an equality test

`Ground.float` is the only payload whose host equality misbehaves.  We isolate
it syntactically so that the restriction is checkable by computation, rather than
by assuming the property we need. -/

/-- Mirror of the derived `BEq Ground`, written with explicit equations so that
`simp` can reduce it; `ground_beq_eq` shows it IS the derived instance. -/
def groundBeq : Ground → Ground → Bool
  | .int a, .int b => a == b
  | .float a, .float b => a == b
  | .str a, .str b => a == b
  | .bool a, .bool b => a == b
  | .unit, .unit => true
  | .error a, .error b => a == b
  | .external a b, .external c d => (a == c) && (b == d)
  | _, _ => false

theorem ground_beq_eq (g₁ g₂ : Ground) : (g₁ == g₂) = groundBeq g₁ g₂ := by
  cases g₁ <;> cases g₂ <;> rfl

/-- A grounded payload whose host equality is an equality test: everything except
`Float`, whose IEEE semantics makes `nan` differ from itself and identifies
`0.0` with `-0.0`. -/
def groundFloatFree : Ground → Bool
  | .float _ => false
  | _ => true

theorem ground_beq_self {g : Ground} (h : groundFloatFree g = true) : (g == g) = true := by
  cases g <;> simp_all [ground_beq_eq, groundBeq, groundFloatFree]

theorem ground_eq_of_beq {g₁ g₂ : Ground} (h₂ : groundFloatFree g₂ = true)
    (h : (g₁ == g₂) = true) : g₁ = g₂ := by
  cases g₁ <;> cases g₂ <;> simp_all [ground_beq_eq, groundBeq, groundFloatFree]

-- Float-freeness is defined mutually with its list companion, in the same shape
-- as LeaTTa's `Atom.beq`/`Atom.beqList`, so the recursion is structural on the
-- nested inductive `Atom`.
mutual
/-- Atoms containing no `Float` payload anywhere. -/
def atomFloatFree : Atom → Bool
  | .sym _ => true
  | .var _ => true
  | .gnd g => groundFloatFree g
  | .expr xs => atomListFloatFree xs
/-- Lists of atoms all of which contain no `Float` payload. -/
def atomListFloatFree : List Atom → Bool
  | [] => true
  | x :: xs => atomFloatFree x && atomListFloatFree xs
end

/-- Pointwise self-equality lifts from the members of a list to the list. -/
private theorem beqList_self_of_pointwise (xs : List Atom)
    (h : ∀ x ∈ xs, Atom.beq x x = true) : Atom.beqList xs xs = true := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      have hy : Atom.beq y y = true := h y (by simp)
      have hys : Atom.beqList ys ys = true := ih (fun z hz => h z (by simp [hz]))
      simp [Atom.beqList, hy, hys]

/-- Pointwise injectivity lifts from the members of a list to the list. -/
private theorem beqList_eq_of_pointwise (as : List Atom)
    (h : ∀ b ∈ as, ∀ x, Atom.beq x b = true → x = b) :
    ∀ xs, Atom.beqList xs as = true → xs = as := by
  induction as with
  | nil =>
      intro xs hx
      cases xs with
      | nil => rfl
      | cons _ _ => simp [Atom.beqList] at hx
  | cons b bs ih =>
      intro xs hx
      cases xs with
      | nil => simp [Atom.beqList] at hx
      | cons y ys =>
          simp only [Atom.beqList, Bool.and_eq_true] at hx
          have hy : y = b := h b (by simp) y hx.1
          have hys : ys = bs := ih (fun c hc => h c (by simp [hc])) ys hx.2
          rw [hy, hys]

/-- On the float-free fragment LeaTTa's structural equality is reflexive. -/
theorem atom_beq_self {a : Atom} (h : atomFloatFree a = true) : Atom.beq a a = true := by
  induction a with
  | sym s => simp [Atom.beq]
  | var v => simp [Atom.beq]
  | gnd g => exact ground_beq_self (by simpa [atomFloatFree] using h)
  | expr xs ih =>
      refine beqList_self_of_pointwise xs (fun x hx => ih x hx ?_)
      have hxs : atomListFloatFree xs = true := by simpa [atomFloatFree] using h
      clear h ih
      induction xs with
      | nil => cases hx
      | cons y ys ihs =>
          simp only [atomListFloatFree, Bool.and_eq_true] at hxs
          rcases List.mem_cons.1 hx with hx' | hx'
          · exact hx' ▸ hxs.1
          · exact ihs hx' hxs.2

/-- On the float-free fragment LeaTTa's structural equality identifies only equal
atoms.  Note the asymmetry: only the RIGHT argument has to be float-free, because
a float payload on the left already fails against a float-free right argument. -/
theorem atom_eq_of_beq {a : Atom} (ha : atomFloatFree a = true) :
    ∀ x : Atom, Atom.beq x a = true → x = a := by
  induction a with
  | sym s =>
      intro x hx
      cases x <;> simp_all [Atom.beq]
  | var v =>
      intro x hx
      cases x <;> simp_all [Atom.beq]
  | gnd g =>
      intro x hx
      cases x with
      | gnd g' =>
          have := ground_eq_of_beq (g₁ := g') (by simpa [atomFloatFree] using ha)
            (by simpa [Atom.beq] using hx)
          rw [this]
      | _ => simp [Atom.beq] at hx
  | expr xs ih =>
      have hxs : atomListFloatFree xs = true := by simpa [atomFloatFree] using ha
      have hpt : ∀ b ∈ xs, atomFloatFree b = true := by
        clear ih ha
        induction xs with
        | nil => intro b hb; cases hb
        | cons y ys ihs =>
            simp only [atomListFloatFree, Bool.and_eq_true] at hxs
            intro b hb
            rcases List.mem_cons.1 hb with hb' | hb'
            · exact hb' ▸ hxs.1
            · exact ihs hxs.2 b hb'
      intro x hx
      cases x with
      | expr ys =>
          have := beqList_eq_of_pointwise xs (fun b hb => ih b hb (hpt b hb)) ys
            (by simpa [Atom.beq] using hx)
          rw [this]
      | _ => simp [Atom.beq] at hx

/-! ## The atom type of LeaTTa's space algebra -/

/-- The atoms LeaTTa's named spaces can store and retrieve reliably: those whose
structural equality is a genuine equality test.  This is a restriction on the
ATOM type, not on the space contents — the carrier below is still an arbitrary
`List Atom`, so a space may hold float payloads; they are simply not
addressable. -/
def FFAtom : Type := {a : Atom // atomFloatFree a = true}

namespace FFAtom

instance : CoeHead FFAtom Atom := ⟨Subtype.val⟩

theorem val_injective {a b : FFAtom} (h : a.val = b.val) : a = b := Subtype.ext h

/-- Structural equality decides equality on this type — the property the whole
restriction exists to secure. -/
theorem beq_iff (a b : FFAtom) : Atom.beq a.val b.val = true ↔ a = b := by
  constructor
  · intro h
    exact val_injective (atom_eq_of_beq b.property a.val h)
  · rintro rfl
    exact atom_beq_self a.property

theorem beq_false_of_ne {a b : FFAtom} (h : a ≠ b) : (a.val == b.val) = false := by
  have : ¬ (Atom.beq a.val b.val = true) := fun hb => h ((beq_iff a b).1 hb)
  simpa [BEq.beq] using this

/-- Reflexivity restated through `==`, the form the `List.count` lemmas expect. -/
theorem beq_self (a : FFAtom) : ((a.val : Atom) == a.val) = true := atom_beq_self a.property

end FFAtom

/-! ## The instance -/

/-- LeaTTa's named-space storage, read off `World.appendSpace` (append on the
right) and `World.eraseFromSpace` (`List.erase`, first occurrence only), with
multiplicity given by `List.count` under LeaTTa's own `BEq Atom`. -/
def leattaSpaceOps : StorageOps (List Atom) FFAtom where
  empty := []
  add a s := s ++ [a.val]
  remove a s := s.erase a.val
  multiplicity s a := s.count a.val

@[simp] theorem leattaSpaceOps_empty : leattaSpaceOps.empty = ([] : List Atom) := rfl

@[simp] theorem leattaSpaceOps_add (a : FFAtom) (s : List Atom) :
    leattaSpaceOps.add a s = s ++ [a.val] := rfl

@[simp] theorem leattaSpaceOps_remove (a : FFAtom) (s : List Atom) :
    leattaSpaceOps.remove a s = s.erase a.val := rfl

@[simp] theorem leattaSpaceOps_multiplicity (s : List Atom) (a : FFAtom) :
    leattaSpaceOps.multiplicity s a = s.count a.val := rfl

/-- **LeaTTa's named spaces are a counted bag.**  All five laws, with no side
condition on the space contents. -/
theorem leattaSpaceOps_countedBagLaws : CountedBagLaws leattaSpaceOps where
  multiplicity_empty := by
    intro a
    simp
  multiplicity_add_self := by
    intro a s
    simp [List.count_singleton, FFAtom.beq_self a]
  multiplicity_add_other := by
    intro a b s hab
    simp [List.count_singleton, FFAtom.beq_false_of_ne hab]
  multiplicity_remove_self := by
    intro a s
    simpa using count_erase_self a.val s
  multiplicity_remove_other := by
    intro a b s hab
    show (s.erase a.val).count b.val = s.count b.val
    refine count_erase_of_test b.val a.val s ?_
    intro x hx
    have hxa : x = a.val := atom_eq_of_beq a.property x hx
    subst hxa
    exact FFAtom.beq_false_of_ne hab

/-- The shared-core half of the bundle, for downstream use. -/
theorem leattaSpaceOps_storageLaws : StorageLaws leattaSpaceOps :=
  leattaSpaceOps_countedBagLaws.toStorageLaws

/-! ## Negative witness 1: LeaTTa is NOT a set space

The concrete separation the two law bundles were introduced for.  A space holding
`(a)` twice still holds it once after `remove-atom`, so `SetLaws` — which demands
multiplicity `0` after a removal — is refuted, while `CountedBagLaws` holds. -/

/-- A concrete float-free atom to witness with. -/
def atomA : FFAtom := ⟨Atom.sym "a", rfl⟩

/-- A concrete DIFFERENT float-free atom, used for the positive membership
witnesses. -/
def atomB : FFAtom := ⟨Atom.sym "b", rfl⟩

theorem atomA_ne_atomB : atomA ≠ atomB := by
  intro h
  have hv : Atom.sym "a" = Atom.sym "b" := congrArg Subtype.val h
  simp at hv

/-- The duplicate-holding space: `(a)` added twice. -/
def dupSpace : List Atom := leattaSpaceOps.add atomA (leattaSpaceOps.add atomA leattaSpaceOps.empty)

@[simp] theorem dupSpace_eq : dupSpace = [Atom.sym "a", Atom.sym "a"] := rfl

/-- POSITIVE witness: two additions really do give multiplicity two. -/
theorem multiplicity_dupSpace : leattaSpaceOps.multiplicity dupSpace atomA = 2 := by decide

/-- NEGATIVE witness: after ONE removal the atom is still present with
multiplicity one, not zero. -/
theorem multiplicity_remove_dupSpace :
    leattaSpaceOps.multiplicity (leattaSpaceOps.remove atomA dupSpace) atomA = 1 := by decide

/-- The atom is still a member after removal — a predicate that could not reject
anything would prove nothing, so this is paired with `not_mem_removed_twice`
below. -/
theorem mem_after_one_removal :
    leattaSpaceOps.Mem (leattaSpaceOps.remove atomA dupSpace) atomA := by
  show 0 < leattaSpaceOps.multiplicity (leattaSpaceOps.remove atomA dupSpace) atomA
  rw [multiplicity_remove_dupSpace]
  omega

/-- NEGATIVE witness for membership: after the second removal it is gone, so the
membership predicate does reject. -/
theorem not_mem_removed_twice :
    ¬ leattaSpaceOps.Mem (leattaSpaceOps.remove atomA (leattaSpaceOps.remove atomA dupSpace))
      atomA := by
  show ¬ (0 < leattaSpaceOps.multiplicity
    (leattaSpaceOps.remove atomA (leattaSpaceOps.remove atomA dupSpace)) atomA)
  decide

/-- NEGATIVE witness for membership across atoms: adding `(a)` never makes `(b)`
present. -/
theorem not_mem_other : ¬ leattaSpaceOps.Mem dupSpace atomB := by
  show ¬ (0 < leattaSpaceOps.multiplicity dupSpace atomB)
  decide

/-- **LeaTTa's named spaces do NOT satisfy set semantics.**  This is the payoff
of splitting the removal laws into two bundles over one signature: both bundles
are inhabited by real engines and they are not interderivable. -/
theorem leattaSpaceOps_not_setLaws : ¬ SetLaws leattaSpaceOps := by
  intro hs
  have h := hs.multiplicity_remove_self atomA dupSpace
  rw [multiplicity_remove_dupSpace] at h
  exact absurd h (by decide)

/-- The two bundles are therefore genuinely distinct as law variants: something
satisfies one and not the other. -/
theorem countedBagLaws_ne_setLaws :
    ∃ (S A : Type) (ops : StorageOps S A), CountedBagLaws ops ∧ ¬ SetLaws ops :=
  ⟨List Atom, FFAtom, leattaSpaceOps, leattaSpaceOps_countedBagLaws,
    leattaSpaceOps_not_setLaws⟩

/-! ## Negative witness 2: why the atom type is restricted

Dropping the float-free restriction does not merely make the proofs harder — it
makes the shared core law FALSE.  Lean's kernel cannot evaluate `Float`, so the
IEEE fact `nan == nan = false` is taken as the hypothesis `hx` rather than
asserted; every IEEE `nan` satisfies it. -/

/-- The same operations with no restriction on the atom type. -/
def rawSpaceOps : StorageOps (List Atom) Atom where
  empty := []
  add a s := s ++ [a]
  remove a s := s.erase a
  multiplicity s a := s.count a

/-- Adding an atom whose host equality is not reflexive does not increase its
multiplicity, so the unrestricted instance fails even the shared core laws. -/
theorem rawSpaceOps_not_storageLaws (x : Float) (hx : (x == x) = false) :
    ¬ StorageLaws rawSpaceOps := by
  intro hl
  have h := hl.multiplicity_add_self (Atom.gnd (Ground.float x)) []
  -- `Atom.beq` on a grounded pair is the host `Float` test, definitionally.
  have hbeq : ((Atom.gnd (Ground.float x) : Atom) == Atom.gnd (Ground.float x)) = false := hx
  have h' : List.count (Atom.gnd (Ground.float x)) ([] ++ [Atom.gnd (Ground.float x)])
      = List.count (Atom.gnd (Ground.float x)) [] + 1 := h
  rw [List.nil_append, List.count_singleton, hbeq] at h'
  simp at h'

/-! ## Query layer: exact-atom lookup

The relational core of `SpaceAlgebra` is instantiated here by exact-atom lookup
— asking a space whether it holds a given atom — not by LeaTTa's full pattern
matcher, which binds variables and therefore needs the richer result type the
enumeration extension is designed for.  Exact lookup is enough to exhibit the
coherence and enumeration layers as inhabited, which is what the abstract
development leaves open. -/

/-- Exact-atom lookup: the only answer to a ground pattern is the pattern
itself, and only when the space actually holds it. -/
def leattaExactLookup : QueryOps (List Atom) FFAtom FFAtom where
  QueryRel s pattern result := result = pattern ∧ leattaSpaceOps.Mem s pattern

/-- Coherence: lookup sees exactly what storage holds. -/
theorem leattaExactLookup_coherent :
    QueryCoherent leattaSpaceOps leattaExactLookup id where
  visible_iff_present := by
    intro s a
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨rfl, h⟩

/-- A deterministic readout for exact lookup: one solution when present, none
otherwise. -/
def leattaExactEnumeration : QueryEnumeration leattaExactLookup where
  enumerate s pattern := if 0 < s.count pattern.val then [pattern] else []
  mem_enumerate_iff := by
    intro s pattern r
    by_cases h : 0 < s.count pattern.val
    · simp [h, leattaExactLookup, StorageOps.Mem, leattaSpaceOps]
    · simp [h, leattaExactLookup, StorageOps.Mem, leattaSpaceOps]

/-- POSITIVE readout witness. -/
theorem enumerate_dupSpace :
    leattaExactEnumeration.enumerate dupSpace atomA = [atomA] := by
  show (if 0 < dupSpace.count atomA.val then [atomA] else []) = [atomA]
  rw [if_pos (by decide)]

/-- NEGATIVE readout witness: an absent atom enumerates nothing, so the query is
not the constantly-inhabited relation. -/
theorem enumerate_absent :
    leattaExactEnumeration.enumerate dupSpace atomB = [] := by
  show (if 0 < dupSpace.count atomB.val then [atomB] else []) = []
  rw [if_neg (by decide)]

/-! ## Back to `World`: the per-space projection is the algebra's carrier

These close the loop with the `HashMap`-indexed state: the content of one named
space, `w.spaces.getD name []`, transforms under `World.appendSpace` and
`World.eraseFromSpace` exactly as `add` and `remove` transform the carrier. -/

open Std in
/-- The content of one named space. -/
def spaceContents (w : World) (name : String) : List Atom := w.spaces.getD name []

theorem spaceContents_appendSpace (w : World) (name : String) (as : List Atom) :
    spaceContents (w.appendSpace name as) name = spaceContents w name ++ as := by
  simp [spaceContents, World.appendSpace, Std.HashMap.getD_eq_getD_getElem?]

theorem spaceContents_eraseFromSpace (w : World) (name : String) (a : Atom) :
    spaceContents (w.eraseFromSpace name a) name = (spaceContents w name).erase a := by
  simp [spaceContents, World.eraseFromSpace, Std.HashMap.getD_eq_getD_getElem?]

/-- `add` in the algebra IS `World.appendSpace` of a single atom, read through
the per-space projection.  This is what fixes the append-on-the-right
orientation. -/
theorem spaceContents_appendSpace_single (w : World) (name : String) (a : FFAtom) :
    spaceContents (w.appendSpace name [a.val]) name
      = leattaSpaceOps.add a (spaceContents w name) := by
  simp [spaceContents_appendSpace]

/-- `remove` in the algebra IS `World.eraseFromSpace`, read through the same
projection. -/
theorem spaceContents_eraseFromSpace_single (w : World) (name : String) (a : FFAtom) :
    spaceContents (w.eraseFromSpace name a.val) name
      = leattaSpaceOps.remove a (spaceContents w name) := by
  simp [spaceContents_eraseFromSpace]

end Mettapedia.Languages.MeTTa.HE.SpaceAlgebraLeaTTa
