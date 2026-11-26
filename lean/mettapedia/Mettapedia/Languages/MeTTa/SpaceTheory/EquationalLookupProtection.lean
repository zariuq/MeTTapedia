import Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations

/-!
# Protecting one equation-aware request

A new equation may matter underneath an unchanged head symbol. For
an extension by new atoms, the current equivalence class of a request
is preserved exactly if no new equation in an Atom context crosses
its boundary. Different classes of the same space may have different
answers to this test. Preference declarations do not choose the
representatives searched by an equation-aware entry.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.EquationalLookupProtection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open AtomEquations (Context Generator ContextStep Equivalent)

def SameClass (first second : List Atom) (query : Atom) : Prop :=
  ∀ member, Equivalent first query member ↔ Equivalent second query member

/-- Test the generator across every possible Atom position, in either
direction. This is a semantic test; it does not enumerate contexts. -/
def ClosedClass (base added : List Atom) (query : Atom) : Prop :=
  ∀ (context : Context) {first second : Atom}, Generator added first second →
    (Equivalent base query (context.fill first) ↔ Equivalent base query (context.fill second))

theorem generator_append (first second : List Atom) (a b : Atom) :
    Generator (first ++ second) a b ↔ Generator first a b ∨ Generator second a b := by
  constructor
  · rintro ⟨pref, next, rest, written, member⟩
    rcases List.mem_append.mp written with left | right
    · exact Or.inl ⟨pref, next, rest, left, member⟩
    · exact Or.inr ⟨pref, next, rest, right, member⟩
  · rintro (⟨pref, next, rest, written, member⟩ | ⟨pref, next, rest, written, member⟩)
    · exact ⟨pref, next, rest, List.mem_append_left _ written, member⟩
    · exact ⟨pref, next, rest, List.mem_append_right _ written, member⟩

private theorem membership_iff_of_related {base : List Atom} {query a b : Atom} (related : Equivalent base a b) :
    Equivalent base query a ↔ Equivalent base query b :=
  ⟨fun first => .trans _ _ _ first related, fun second => .trans _ _ _ second (.symm _ _ related)⟩

private theorem membership_along_extension {base added : List Atom} {query a b : Atom}
    (closed : ClosedClass base added query) (connected : Equivalent (base ++ added) a b) :
    Equivalent base query a ↔ Equivalent base query b := by
  induction connected with
  | rel first second one =>
    cases one with
    | inside context written =>
      rcases (generator_append base added _ _).mp written with prior | later
      · exact membership_iff_of_related (AtomEquations.fill_equivalent context (AtomEquations.authored prior))
      · exact closed context later
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih next => exact ih.trans next

theorem class_append_iff (base added : List Atom) (query : Atom) :
    SameClass base (base ++ added) query ↔ ClosedClass base added query := by
  constructor
  · intro same context a b written
    have prior : Equivalent added (context.fill a) (context.fill b) :=
      AtomEquations.fill_equivalent context (AtomEquations.authored written)
    have now : Equivalent (base ++ added) (context.fill a) (context.fill b) :=
      AtomEquations.monotone (List.subset_append_right (l₁ := base) (l₂ := added)) prior
    exact (same _).trans ((membership_iff_of_related now).trans (same _).symm)
  · intro closed representative
    exact ⟨AtomEquations.monotone (List.subset_append_left (l₁ := base) (l₂ := added)),
      fun reached => (membership_along_extension closed reached).mp (.refl _)⟩

/-- Adding an already justified equation may add a preference, but
cannot introduce another member of any query's class. -/
theorem redundant_equations_keep_classes {base added : List Atom}
    (redundant : ∀ a b, Generator added a b → Equivalent base a b) (query : Atom) :
    SameClass base (base ++ added) query :=
  (class_append_iff base added query).mpr
    (fun context _ _ written =>
      membership_iff_of_related (AtomEquations.fill_equivalent context (redundant _ _ written)))

section Controls

open Atoms (Content Preference)

private def cold : Atom := .symbol "Cold"
private def warm : Atom := .symbol "Warm"
private def measure := Atom.symbol "measure"
private def call (a : Atom) := Atom.expression [measure, a]
private def link := (Content.equation .indifferent cold warm []).syntax

theorem unchanged_head_does_not_protect_its_equation_class :
    Equivalent [link] (call cold) (call warm) ∧
      ¬SameClass [] [link] (call cold) := by
  have written : Generator [link] cold warm :=
    ⟨.indifferent, warm, [], List.mem_cons_self, List.mem_cons_self⟩
  have changes := AtomEquations.fill_equivalent (.child [measure] .hole [])
    (AtomEquations.authored written)
  refine ⟨changes, ?_⟩
  intro claim
  have old := (claim (call warm)).mpr changes
  have noEquations (a b : Atom) : ¬Generator [] a b := fun ⟨_, _, _, member, _⟩ => List.not_mem_nil member
  exact (by decide : call cold ≠ call warm)
    ((AtomEquations.without_generators [] noEquations (call cold) (call warm)).mp old)

theorem changing_the_preference_preserves_the_query_class :
    let preferred := (Content.equation .rightward cold warm []).syntax
    SameClass [link] [link, preferred] (call cold) := by
  change SameClass [link] ([link] ++ [(Content.equation .rightward cold warm []).syntax]) (call cold)
  apply redundant_equations_keep_classes
  rintro a b ⟨pref, next, rest, present, member⟩
  have shape := List.mem_singleton.mp present
  change Atom.expression (_ :: a :: next :: rest) =
    Atom.expression [.symbol "=e>", cold, warm] at shape
  have endpoints := Atom.expression.inj shape
  obtain ⟨_, rfl, rfl, rfl⟩ := by simpa only [List.cons.injEq] using endpoints
  exact AtomEquations.authored ⟨.indifferent, warm, [], List.mem_cons_self, member⟩

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.EquationalLookupProtection
