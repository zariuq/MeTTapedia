import Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations
import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleTheories
import Mathlib.Data.Fintype.EquivFin

/-!
# An obstruction to interpreting finite written equations as schemes

Read the selected names of an Atom from left to right. In a one-hole
context this word is prefixed and suffixed by fixed words. Therefore
an equation between terms that do not mention the selected names
cannot move, erase or introduce a selected name, even inside an
arbitrary context and along an arbitrary chain of equations.

Variables in a written equation contribute their literal spelling to
this calculation. That is the equation interpretation, in contrast to
the metavariables of function definitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.GroundEquationBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open AtomEquations (Context Equivalent Generator)
open Atoms (Content)

mutual
def letters : Atom → List String
  | .symbol name | .var name => [name]
  | .grounded _ => []
  | .expression children => lettersOf children

def lettersOf : List Atom → List String
  | [] => []
  | head :: tail => letters head ++ lettersOf tail
end

theorem lettersOf_append (first second : List Atom) :
    lettersOf (first ++ second) = lettersOf first ++ lettersOf second := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, lettersOf, ih, List.append_assoc]

def alphabet (declarations : List Atom) : Finset String := (lettersOf declarations).toFinset
def word (marked : Finset String) (atom : Atom) : List String :=
  (letters atom).filter fun name => decide (name ∈ marked)

theorem word_in_context (marked : Finset String) (context : Context) {first second : Atom}
    (same : word marked first = word marked second) :
    word marked (context.fill first) = word marked (context.fill second) := by
  induction context with
  | hole => exact same
  | child left inner right ih =>
    unfold word at ih
    simp only [Context.fill, word, letters, lettersOf_append, lettersOf, List.filter_append, ih]

theorem child_names {children : List Atom} {a : Atom} (member : a ∈ children) {name : String}
    (occurs : name ∈ letters a) : name ∈ lettersOf children := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact List.mem_append_left _ occurs
    · exact List.mem_append_right _ (ih later)

private theorem generator_alphabet {declarations : List Atom} {first second : Atom}
    (declared : Generator declarations first second) :
    ∀ name ∈ letters first ++ letters second, name ∈ alphabet declarations := by
  obtain ⟨pref, next, rest, stored, component⟩ := declared
  intro name occurs
  apply List.mem_toFinset.mpr
  apply child_names stored
  change name ∈ lettersOf (.symbol pref.symbol :: first :: next :: rest)
  rcases List.mem_append.mp occurs with atFirst | atSecond
  · exact child_names (by simp) atFirst
  · exact child_names (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ component)) atSecond

private theorem word_eq_nil {marked : Finset String} {atom : Atom}
    (absent : ∀ name ∈ letters atom, name ∉ marked) : word marked atom = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name seen
  obtain ⟨inside, selected⟩ := List.mem_filter.mp seen
  exact absent name inside (of_decide_eq_true selected)

/-- Equating finitely written atoms preserves the ordered word of
names outside the entire authored alphabet. This also handles cycles. -/
theorem fresh_word_of_equivalent {declarations : List Atom} {marked : Finset String}
    (fresh : Disjoint marked (alphabet declarations)) {first second : Atom}
    (same : Equivalent declarations first second) :
    word marked first = word marked second := by
  let words : Setoid Atom :=
    ⟨fun a b => word marked a = word marked b, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  exact AtomEquations.least declarations words (by
  · intro a b generator
    have aEmpty : word marked a = [] := word_eq_nil fun n occurs selected =>
      Finset.disjoint_left.mp fresh selected (generator_alphabet generator n (List.mem_append_left _ occurs))
    have bEmpty : word marked b = [] := word_eq_nil fun n occurs selected =>
      Finset.disjoint_left.mp fresh selected (generator_alphabet generator n (List.mem_append_right _ occurs))
    exact aEmpty.trans bEmpty.symm)
    (fun context _ _ agree => word_in_context marked context agree) same

private theorem two_outside (used : Finset String) : ∃ a b, a ∉ used ∧ b ∉ used ∧ a ≠ b := by
  obtain ⟨a, first⟩ := Infinite.exists_notMem_finset used
  obtain ⟨b, second⟩ := Infinite.exists_notMem_finset (insert a used)
  have separated : b ≠ a ∧ b ∉ used := by simpa only [Finset.mem_insert, not_or] using second
  exact ⟨a, b, first, separated.2, Ne.symm separated.1⟩

def pairAt (head a b : String) : Atom := .expression [.symbol head, .symbol a, .symbol b]

/-- No finite inventory of literal equations implements all instances
of binary commutation on a raw expression. A space's outer multiset
still implements commutation without writing any such equations. -/
theorem commutation_scheme_is_not_a_finite_ground_presentation (declarations : List Atom) (head : String) :
    ∃ a b, a ≠ b ∧ ¬Equivalent declarations (pairAt head a b) (pairAt head b a) := by
  obtain ⟨a, b, freshA, freshB, unequal⟩ := two_outside (insert head (alphabet declarations))
  have aInfo : a ≠ head ∧ a ∉ alphabet declarations := by
    simpa only [Finset.mem_insert, not_or] using freshA
  have bInfo : b ≠ head ∧ b ∉ alphabet declarations := by
    simpa only [Finset.mem_insert, not_or] using freshB
  refine ⟨a, b, unequal, fun same => ?_⟩
  have fresh : Disjoint ({a, b} : Finset String) (alphabet declarations) := by
    simp [Finset.disjoint_insert_left, aInfo.2, bInfo.2]
  have words := fresh_word_of_equivalent fresh same
  have swapped : [a, b] = [b, a] := by
    simpa [word, pairAt, letters, lettersOf, Ne.symm aInfo.1, Ne.symm bInfo.1] using words
  exact unequal (List.cons.inj swapped).1

/-- The same fresh spelling appears in a printed binder and in its
printed use. Neither occurrence is a binder position of the Atom. -/
def rawReceiver (name : String) : Atom :=
  .expression [.symbol "receive", .symbol "channel", .symbol name,
    .expression [.symbol "drop", .symbol name]]

/-- Alpha is not a rule of the raw named Atom tree, even after adding
arbitrarily many, but finitely written, literal equations. -/
theorem alpha_scheme_is_not_a_finite_ground_presentation (declarations : List Atom) :
    ∃ a b, a ≠ b ∧ ¬Equivalent declarations (rawReceiver a) (rawReceiver b) := by
  let fixed := insert "receive" (insert "channel" (insert "drop" (alphabet declarations)))
  obtain ⟨a, b, freshA, freshB, different⟩ := two_outside fixed
  have separated :
      a ≠ "receive" ∧ a ≠ "channel" ∧ a ≠ "drop" ∧ a ∉ alphabet declarations := by
    simpa only [fixed, Finset.mem_insert, not_or] using freshA
  obtain ⟨receiver, channel, drop, notWritten⟩ := separated
  refine ⟨a, b, different, fun same => ?_⟩
  have fresh : Disjoint ({a} : Finset String) (alphabet declarations) := by simpa using notWritten
  have words := fresh_word_of_equivalent fresh same
  simp [rawReceiver, word, letters, lettersOf, Ne.symm receiver, Ne.symm channel, Ne.symm drop,
    Ne.symm different] at words

section ContextControl

open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern)

private def left : Atom := .symbol "A"
private def right : Atom := .symbol "B"
private def rule : Atom := (Content.definition left right).syntax
private def hold (atom : Atom) : Atom := .expression [.symbol "held", atom]

/-- A ground definition at the root introduces no rule for a new
rewriting context. This contrasts with equations, which do have
contextual closure, and with a dialect's own evaluation strategy. -/
theorem root_definition_does_not_declare_a_rewriting_context :
    let theory := ModuleTheories.theory (fun _ _ => False) [rule]
    theory.Step left right ∧ ¬theory.Step (hold left) (hold right) := by
  have noEquation (a b : Atom) : ¬Generator [rule] a b := by
    rintro ⟨preference, second, rest, written, occurs⟩
    have same := List.mem_singleton.mp written
    cases preference <;> simp [rule, Atoms.Content.syntax, Atoms.Preference.symbol] at same
  constructor
  · have writtenFires : ModuleTheories.InstanceOf rule left right := by
      refine ⟨left, right, rfl, [], by decide +kernel, by decide +kernel⟩
    exact ⟨left, right, .refl _, Or.inr ⟨rule, List.mem_cons_self, writtenFires⟩, .refl _⟩
  · rintro ⟨source, target, inputEq, ready, outputEq⟩
    have exactSource := (AtomEquations.without_generators [rule] noEquation _ _).mp inputEq
    subst source
    rcases ready with absent | ⟨written, listed, l, r, classified, bindings, admits, result⟩
    · exact absent
    · obtain rfl := List.mem_singleton.mp listed
      change Content.definition left right = .definition l r at classified
      obtain ⟨rfl, rfl⟩ := Content.definition.inj classified
      have empty :
          matchPattern (GroundData.schema left) (GroundData.encode (hold left)) = [] := by decide +kernel
      rw [empty] at admits
      exact List.not_mem_nil admits

end ContextControl

end Mettapedia.Languages.MeTTa.SpaceTheory.GroundEquationBoundary
