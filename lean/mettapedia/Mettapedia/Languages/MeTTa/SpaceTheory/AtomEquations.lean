import Mettapedia.Languages.MeTTa.SpaceTheory.Atoms
import Mettapedia.GSLT.Core.EndpointSaturation
import Mettapedia.GSLT.Equations.PreferredSection
import Mathlib.Logic.Relation

/-!
# The equation view of native Atoms

Only children of an expression are Atom positions. A symbol's spelling,
a variable's name, or the payload of a grounded value is not itself a
child Atom. A written equation can equate two such atoms as wholes without
allowing a substitution into their names or payloads.

This is the explicit equation-aware view; raw inspection and a dialect's
choice of when to evaluate are independent of it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Atoms (Content Preference)
open Mettapedia.GSLT

/-- A written variadic equation gives one generator from its first atom to
each other member. Preference selects a representative, not a direction
of equality. -/
def Generator (atoms : List Atom) (first member : Atom) : Prop :=
  ∃ (pref : Preference) (second : Atom) (rest : List Atom),
    (Content.equation pref first second rest).syntax ∈ atoms ∧ member ∈ second :: rest

inductive Context where
  | hole
  | child (before : List Atom) (inner : Context) (after : List Atom)

def Context.fill : Context → Atom → Atom
  | .hole, a => a
  | .child before inner after, a => .expression (before ++ inner.fill a :: after)

def Context.comp : Context → Context → Context
  | .hole, inner => inner
  | .child before children after, inner => .child before (children.comp inner) after

@[simp] theorem Context.fill_comp (outer inner : Context) (a : Atom) :
    (outer.comp inner).fill a = outer.fill (inner.fill a) := by
  induction outer with
  | hole => rfl
  | child before children after ih => simp [Context.comp, Context.fill, ih]

inductive ContextStep (atoms : List Atom) : Atom → Atom → Prop where
  | inside (context : Context) {a b : Atom} :
      Generator atoms a b → ContextStep atoms (context.fill a) (context.fill b)

def Equivalent (atoms : List Atom) : Atom → Atom → Prop := Relation.EqvGen (ContextStep atoms)

def setoid (atoms : List Atom) : Setoid Atom where
  r := Equivalent atoms
  iseqv := ⟨.refl, fun h => .symm _ _ h, fun h k => .trans _ _ _ h k⟩

theorem authored {atoms : List Atom} {a b : Atom} (declared : Generator atoms a b) :
    Equivalent atoms a b :=
  .rel _ _ (.inside .hole declared)

theorem fill_equivalent (context : Context) {atoms : List Atom} {a b : Atom}
    (equivalent : Equivalent atoms a b) :
    Equivalent atoms (context.fill a) (context.fill b) := by
  induction equivalent with
  | rel a b one =>
    cases one with
    | inside inner declared =>
      exact .rel _ _ (by simpa only [Context.fill_comp] using
        ContextStep.inside (context.comp inner) declared)
  | refl => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ first second => exact .trans _ _ _ first second

/-- The generated view is the least equivalence that honors all written
equations at Atom positions. Its definition makes no commitment about
matching within an evaluator's quotation syntax. -/
theorem least (atoms : List Atom) (other : Setoid Atom)
    (agrees : ∀ a b, Generator atoms a b → other.r a b)
    (fills : ∀ (c : Context) a b, other.r a b → other.r (c.fill a) (c.fill b))
    {a b : Atom} (equivalent : Equivalent atoms a b) : other.r a b := by
  induction equivalent with
  | rel a b one =>
    cases one with
    | inside inner declared => exact fills inner _ _ (agrees _ _ declared)
  | refl => exact other.iseqv.refl _
  | symm a b _ ih => exact other.iseqv.symm ih
  | trans a b c _ _ first second => exact other.iseqv.trans first second

theorem monotone {first second : List Atom} (included : first ⊆ second) {a b : Atom}
    (equivalent : Equivalent first a b) : Equivalent second a b :=
  least first (setoid second) (fun _ _ h => authored (by
    obtain ⟨pref, next, rest, written, member⟩ := h
    exact ⟨pref, next, rest, included written, member⟩))
    (fun c _ _ => fill_equivalent c) equivalent

theorem without_generators (atoms : List Atom) (noneWritten : ∀ a b, ¬ Generator atoms a b)
    (a b : Atom) : Equivalent atoms a b ↔ a = b := by
  constructor
  · exact least atoms ⟨Eq, Eq.refl, Eq.symm, Eq.trans⟩
      (fun x y h => (noneWritten x y h).elim) (fun c _ _ h => congrArg c.fill h)
  · rintro rfl
    exact .refl _

private def members : Content → List Atom
  | .equation _ anchor next rest => anchor :: next :: rest
  | _ => []

private def arrows : Content → List (Atom × Atom)
  | .equation .rightward anchor next rest =>
      Mettapedia.GSLT.Equations.Preference.consecutive (anchor :: next :: rest)
  | .equation .leftward anchor next rest =>
      Mettapedia.GSLT.Equations.Preference.consecutive (anchor :: next :: rest).reverse
  | _ => []

def representatives (atoms : List Atom) : Finset Atom :=
  (atoms.flatMap (members ∘ Atoms.content)).toFinset

def preferences (atoms : List Atom) : List (Atom × Atom) :=
  atoms.flatMap (arrows ∘ Atoms.content)

private theorem arrows_inside (record : Content) {a b : Atom} (edge : (a, b) ∈ arrows record) :
    a ∈ members record ∧ b ∈ members record := by
  cases record
  case equation preference anchor next rest =>
    cases preference with
    | indifferent => cases edge
    | rightward => exact Mettapedia.GSLT.Equations.Preference.consecutive_inside edge
    | leftward =>
      have inside := Mettapedia.GSLT.Equations.Preference.consecutive_inside
        (xs := (anchor :: next :: rest).reverse) (a := a) (b := b) edge
      simpa only [members, List.mem_reverse] using inside
  all_goals cases edge

theorem preference_within_class (atoms : List Atom) {a b : Atom}
    (edge : (a, b) ∈ preferences atoms) : Equivalent atoms a b := by
  obtain ⟨written, listed, preferred⟩ := List.mem_flatMap.mp edge
  have inside := arrows_inside (Atoms.content written) preferred
  cases form : Atoms.content written
  case equation pref anchor next rest =>
    have identifies : ∀ x ∈ anchor :: next :: rest, Equivalent atoms anchor x := by
      intro x member
      rcases List.mem_cons.mp member with rfl | continues
      · exact Relation.EqvGen.refl _
      · apply authored
        have spelling : (Content.equation pref anchor next rest).syntax = written := by
          rw [← form, Atoms.content_syntax]
        exact ⟨pref, next, rest, spelling ▸ listed, continues⟩
    have aEq := identifies a (by simpa only [form, members] using inside.1)
    have bEq := identifies b (by simpa only [form, members] using inside.2)
    exact .trans _ _ _ (.symm _ _ aEq) bEq
  all_goals simp [form, members] at inside

noncomputable def print (atoms : List Atom) (rank : Atom → Nat) (a : Atom) : Atom :=
  Mettapedia.GSLT.Equations.PreferredSection.printed
    (setoid atoms) (representatives atoms) (Mettapedia.GSLT.Equations.Preference.Edge (preferences atoms))
    rank (Quotient.mk (setoid atoms) a)

/-- Printing is a section of the native equality classes. -/
theorem printed_equal (atoms : List Atom) (rank : Atom → Nat) (a : Atom) :
    Equivalent atoms (print atoms rank a) a := by
  change (setoid atoms).r _ _
  exact @Quotient.exact _ (setoid atoms) _ _
    (Mettapedia.GSLT.Equations.PreferredSection.printed_section
      (setoid atoms) (representatives atoms)
      (Mettapedia.GSLT.Equations.Preference.Edge (preferences atoms)) rank (Quotient.mk (setoid atoms) a))

theorem same_print_iff (atoms : List Atom) (rank : Atom → Nat) (a b : Atom) :
    print atoms rank a = print atoms rank b ↔ Equivalent atoms a b :=
  Mettapedia.GSLT.Equations.PreferredSection.same_print_iff (setoid atoms) _ _ _ a b

/-- A scalar with no equation mentioning it as a whole cannot be
changed by any path of equation steps. -/
theorem isolated_scalar {atoms : List Atom} (a : Atom)
    (scalar : ∀ children, a ≠ .expression children)
    (noOutgoing : ∀ b, ¬ Generator atoms a b)
    (noIncoming : ∀ b, ¬ Generator atoms b a) (b : Atom) :
    Equivalent atoms a b ↔ a = b := by
  have preserves {x y : Atom} (h : Equivalent atoms x y) : x = a ↔ y = a := by
    induction h with
    | rel x y one =>
      cases one with
      | inside context declaration =>
        cases context with
        | hole =>
          constructor
          · rintro rfl; exact (noOutgoing _ declaration).elim
          · rintro rfl; exact (noIncoming _ declaration).elim
        | child pre inner post =>
          exact ⟨fun same => (scalar _ same.symm).elim, fun same => (scalar _ same.symm).elim⟩
    | refl => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ first second => exact first.trans second
  exact ⟨fun h => ((preserves h).mp rfl).symm, fun h => h ▸ .refl a⟩

/-- The atom-space quotient can be used with whatever firing judgment
the selected dialect and observation supply. It does not replace the
dialect's judgment of an authored firing. -/
def theory (atoms : List Atom) (firing : Atom → Atom → Prop) : GSLT :=
  EndpointSaturation.theory (setoid atoms) firing

theorem firing_of_print_iff (atoms : List Atom) (firing : Atom → Atom → Prop)
    (rank : Atom → Nat) (a b : Atom) :
    (theory atoms firing).Step (print atoms rank a) (print atoms rank b) ↔
      (theory atoms firing).Step a b := by
  let eq := setoid atoms
  have left : eq.r (print atoms rank a) a := printed_equal atoms rank a
  have right : eq.r (print atoms rank b) b := printed_equal atoms rank b
  constructor
  · rintro ⟨x, y, into, step, out⟩
    exact ⟨x, y, eq.iseqv.trans (eq.iseqv.symm left) into, step, eq.iseqv.trans out right⟩
  · rintro ⟨x, y, into, step, out⟩
    exact ⟨x, y, eq.iseqv.trans left into, step, eq.iseqv.trans out (eq.iseqv.symm right)⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations
