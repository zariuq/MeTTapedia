import Mettapedia.Languages.MeTTa.PeTTa.AtomFreshNamespaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Disequality

/-!
# Fresh Atom namespaces as morphisms of disequation frames

The combined substitution agrees with the caller on protected terms and the
entire retained negative frame. It realizes independent assignments in fresh
namespaces. Preservation holds after every later separating substitution, so
the construction is a morphism of the existing disequation-frame category.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeFreshNamespaces

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open AtomFreshNamespaces (Bounded)

abbrev Frame := Disequality.Frame atomAction
abbrev Hom := Disequality.Hom atomAction
abbrev X := Disequality.frames atomAction

def support (frame : Frame) (protectedTerms : List Atom) : List Atom :=
  protectedTerms ++ frame.1.map Prod.fst ++ frame.1.map Prod.snd

def bound (frame : Frame) (protectedTerms : List Atom) : Nat :=
  AtomFreshNamespaces.supportBound (support frame protectedTerms)

theorem protected_bounded (frame : Frame) (protectedTerms : List Atom) (term : Atom)
    (member : term ∈ protectedTerms) : Bounded (bound frame protectedTerms) term :=
  AtomFreshNamespaces.bounded_of_mem (List.mem_append_left _ (List.mem_append_left _ member))

theorem frame_bounded (frame : Frame) (protectedTerms : List Atom)
    (equation : Atom × Atom) (member : equation ∈ frame.1) :
    Bounded (bound frame protectedTerms) equation.1 ∧
      Bounded (bound frame protectedTerms) equation.2 := by
  constructor
  · exact AtomFreshNamespaces.bounded_of_mem
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem member)))
  · exact AtomFreshNamespaces.bounded_of_mem (List.mem_append_right _ (List.mem_map_of_mem member))

/-- The morphism law quantifies over later solutions of the target frame;
separation merely at the current substitution would be weaker. -/
def combine {source target : Frame} (protectedTerms : List Atom) (caller : Hom source target)
    (requested : Nat → Subst) : Hom source target :=
  ⟨AtomFreshNamespaces.combine (bound source protectedTerms) caller.1 requested, by
    intro later separated equation member equal
    apply caller.2 later separated equation member
    rw [atomAction.apply_compose, atomAction.apply_compose]
    rw [atomAction.apply_compose, atomAction.apply_compose] at equal
    change subst later (subst caller.1 equation.1) = subst later (subst caller.1 equation.2)
    change subst later (subst (AtomFreshNamespaces.combine (bound source protectedTerms)
      caller.1 requested) equation.1) =
        subst later (subst (AtomFreshNamespaces.combine (bound source protectedTerms)
          caller.1 requested) equation.2) at equal
    rw [AtomFreshNamespaces.source_agrees _ caller.1 requested _
        (frame_bounded source protectedTerms equation member).1,
      AtomFreshNamespaces.source_agrees _ caller.1 requested _
        (frame_bounded source protectedTerms equation member).2] at equal
    exact equal⟩

theorem combine_protected {source target : Frame} (protectedTerms : List Atom)
    (caller : Hom source target) (requested : Nat → Subst) (term : Atom)
    (member : term ∈ protectedTerms) :
    X.act (combine protectedTerms caller requested) term = X.act caller term :=
  AtomFreshNamespaces.source_agrees _ caller.1 requested term
    (protected_bounded source protectedTerms term member)

theorem combine_opening {source target : Frame} (protectedTerms : List Atom)
    (caller : Hom source target) (requested : Nat → Subst) (index : Nat) (term : Atom) :
    X.act (combine protectedTerms caller requested)
      (subst (AtomFreshNamespaces.opening (bound source protectedTerms) index) term) =
        subst (requested index) term :=
  AtomFreshNamespaces.combine_opening _ caller.1 requested index term

theorem combine_separates {source target : Frame} (protectedTerms : List Atom)
    (caller : Hom source target) (requested : Nat → Subst) :
    Disequality.Separates atomAction (combine protectedTerms caller requested).1 source.1 :=
  Disequality.separates_hom (combine protectedTerms caller requested)

/-- Later refinement preserves the agreement on caller coordinates. -/
theorem combine_protected_after {source target later : Frame} (protectedTerms : List Atom)
    (caller : Hom source target) (requested : Nat → Subst) (refinement : Hom target later)
    (term : Atom) (member : term ∈ protectedTerms) :
    X.act (X.comp refinement (combine protectedTerms caller requested)) term =
      X.act (X.comp refinement caller) term := by
  rw [X.act_comp, X.act_comp, combine_protected protectedTerms caller requested term member]

end Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeFreshNamespaces
