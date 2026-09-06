import Mettapedia.GSLT.Logic.ObserverRefinement
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Identity notions and the maps licensed between them

There is no single equality.  Over one operational theory `S` this module
names seven notions of identity and states, as typed maps, which ones
determine which:

* judgmental conversion, a relation sound for the equations `E`;
* the equations `E` themselves;
* behavioural equivalence under a fine and under a coarse observer;
* extensional equality in a model, a denotation respecting `E`;
* occurrence identity, the retained event, which erases to its endpoints;
* diachronic lineage, an execution path, which maps to reachability only.

The maps go conversion → `E` → behavioural (fine) → behavioural (coarse),
`E` → model equality, occurrence → endpoints, lineage → reachability.  No
map goes the other way in general.  The temporal specimen at the end has two
moments that a fine observer separates, a coarse observer identifies, and a
lineage relates, while their identity is not derivable; and a family descends
through an observer exactly when it is invariant under that observer's
behavioural equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IdentityNotions

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Ultrainfinite (Route)
open Mettapedia.GSLT.IndexedOperational

universe uS uAtom uLabel uAtomFine uLabelFine uMeaning uFamily

/-! ## The licensed maps -/

/-- Judgmental conversion: any relation sound for the equations. -/
structure Conversion (S : GSLT.{uS}) where
  Conv : S.Term → S.Term → Prop
  sound : ∀ {left right}, Conv left right → S.Equiv left right

/-- Extensional equality in a model: a denotation respecting the equations. -/
structure Denotation (S : GSLT.{uS}) (Meaning : Type uMeaning) where
  denote : S.Term → Meaning
  resp : ∀ {left right}, S.Equiv left right → denote left = denote right

variable {S : GSLT.{uS}}

/-- Conversion determines the equations. -/
theorem conversion_to_equations (conversion : Conversion S) {left right : S.Term}
    (converts : conversion.Conv left right) : S.Equiv left right :=
  conversion.sound converts

/-- The equations determine behavioural equivalence under every observer. -/
theorem equations_to_behavioural (M : System.{uAtom, uLabel} S) {left right : S.Term}
    (equal : S.Equiv left right) : M.Bisimilar left right :=
  M.bisimilar_of_equiv equal

/-- Fine behavioural equivalence determines coarse behavioural equivalence. -/
theorem fine_to_coarse {coarse : System.{uAtom, uLabel} S}
    {fine : System.{uAtomFine, uLabelFine} S}
    (refinement : ObserverRefinement coarse fine) {left right : S.Term}
    (bisimilar : fine.Bisimilar left right) : coarse.Bisimilar left right :=
  refinement.bisimilar_forget bisimilar

/-- The equations determine extensional model equality. -/
theorem equations_to_model {Meaning : Type uMeaning} (denotation : Denotation S Meaning)
    {left right : S.Term} (equal : S.Equiv left right) :
    denotation.denote left = denotation.denote right :=
  denotation.resp equal

/-- Diachronic lineage: a finite execution path. -/
abbrev Lineage (S : GSLT.{uS}) (source target : S.Term) : Type uS :=
  ExecutionPath S source target

/-- Lineage determines reachability, and nothing finer. -/
theorem lineage_to_reachable {source target : S.Term} (lineage : Lineage S source target) :
    Nonempty (ExecutionPath S source target) :=
  ⟨lineage⟩

/-! ## Descent of a family through an observer -/

/-- A family of types over states descends through an observer when it
factors through that observer's behavioural classes. -/
def DescendsThrough (M : System.{uAtom, uLabel} S) (family : S.Term → Type uFamily) : Prop :=
  ∃ quotientFamily : M.BehavioralClass → Type uFamily,
    ∀ term, family term = quotientFamily (M.toBehavioralClass term)

/-- A family descends through an observer exactly when it is invariant under
the observer's behavioural equivalence. -/
theorem descendsThrough_iff (M : System.{uAtom, uLabel} S) (family : S.Term → Type uFamily) :
    DescendsThrough M family ↔
      ∀ left right, M.Bisimilar left right → family left = family right := by
  constructor
  · rintro ⟨quotientFamily, factors⟩ left right bisimilar
    rw [factors left, factors right, (M.behavioralClass_eq_iff left right).2 bisimilar]
  · intro invariant
    exact ⟨Quotient.lift family (fun left right bisimilar => invariant left right bisimilar),
      fun _ => rfl⟩

/-! ## The temporal specimen -/

namespace Temporal

/-- Three moments of one history. -/
inductive Moment
  | first
  | second
  | third
  deriving DecidableEq

/-- The history: first to second to third, with no equations. -/
def specimen : GSLT where
  Term := Moment
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target :=
    (source = .first ∧ target = .second) ∨ (source = .second ∧ target = .third)
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-- The fine observer sees every moment and every step. -/
def fine : System specimen where
  Atom := Moment
  observes atom term := atom = term
  observes_resp := by
    intro atom left right equal
    cases equal
    exact Iff.rfl
  Label := Unit
  act _ source target := specimen.rewrites source target
  act_resp_left := by
    intro _ left right target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  act_resp_right := by
    intro _ source target target' step equal
    cases equal
    exact step

/-- The coarse observer sees only whether the moment is the first, and no
steps at all. -/
def coarse : System specimen where
  Atom := Unit
  observes _ term := term = .first
  observes_resp := by
    intro _ left right equal
    cases equal
    exact Iff.rfl
  Label := PEmpty
  act label := label.elim
  act_resp_left := by
    intro label
    exact label.elim
  act_resp_right := by
    intro label
    exact label.elim

/-- The coarse observer is a coarsening of the fine one. -/
def coarsening : ObserverRefinement coarse fine where
  mapAtom _ := .first
  mapLabel label := label.elim
  observes_iff _ _ := eq_comm
  act_iff label := label.elim

/-- The second and third moments are lineage-related. -/
def lineage : Lineage specimen .second .third :=
  Route.cons (Step := fun left right : Moment => PLift (specimen.Step left right))
    ⟨Or.inr ⟨rfl, rfl⟩⟩ (Route.refl _)

/-- Their identity is not derivable: the equations are equality. -/
theorem not_identical : ¬ specimen.Equiv .second .third := by
  intro equal
  cases equal

/-- The coarse observer identifies them. -/
theorem coarse_identifies : coarse.Bisimilar .second .third := by
  refine ⟨fun left right => left ≠ .first ∧ right ≠ .first, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro _ _ _ label
    exact label.elim
  · intro _ _ _ label
    exact label.elim
  · intro left right related _
    exact ⟨fun leftFirst => absurd leftFirst related.1, fun rightFirst => absurd rightFirst related.2⟩
  · exact ⟨(fun equal => nomatch equal), (fun equal => nomatch equal)⟩

/-- The fine observer separates them. -/
theorem fine_separates : ¬ fine.Bisimilar .second .third := by
  rintro ⟨relation, ⟨_, _, atoms⟩, related⟩
  have observed := (atoms related Moment.second).1 rfl
  cases observed

/-- Coarse observation cannot mint fine identity. -/
theorem coarse_cannot_mint_fine :
    ¬ ∀ left right, coarse.Bisimilar left right → fine.Bisimilar left right :=
  fun mint => fine_separates (mint _ _ coarse_identifies)

/-- Coarse observation cannot mint intensional identity. -/
theorem coarse_cannot_mint_equations :
    ¬ ∀ left right, coarse.Bisimilar left right → specimen.Equiv left right :=
  fun mint => not_identical (mint _ _ coarse_identifies)

/-- Lineage relates the two moments while none of the identities holds. -/
theorem lineage_without_identity :
    Nonempty (Lineage specimen .second .third) ∧
      coarse.Bisimilar .second .third ∧
        ¬ fine.Bisimilar .second .third ∧
          ¬ specimen.Equiv .second .third :=
  ⟨⟨lineage⟩, coarse_identifies, fine_separates, not_identical⟩

/-- A family marking the second moment. -/
def marker : Moment → Type
  | .second => PUnit
  | _ => PEmpty

/-- Fine behavioural equivalence is identity of moments. -/
theorem fine_bisimilar_iff (left right : Moment) : fine.Bisimilar left right ↔ left = right := by
  constructor
  · rintro ⟨relation, ⟨_, _, atoms⟩, related⟩
    exact (atoms related left).1 rfl
  · rintro rfl
    exact fine.bisimilar_refl _

/-- The marker descends through the fine observer. -/
theorem marker_descends_fine : DescendsThrough fine marker :=
  (descendsThrough_iff fine marker).2 (fun left right bisimilar => by
    rw [(fine_bisimilar_iff left right).1 bisimilar])

/-- The marker does not descend through the coarse observer. -/
theorem marker_not_descends_coarse : ¬ DescendsThrough coarse marker := by
  intro descends
  have invariant := ((descendsThrough_iff coarse marker).1 descends) _ _ coarse_identifies
  have equivalence : PUnit ≃ PEmpty := Equiv.cast invariant
  exact (equivalence PUnit.unit).elim

end Temporal

#print axioms descendsThrough_iff
#print axioms Temporal.lineage_without_identity
#print axioms Temporal.coarse_cannot_mint_fine
#print axioms Temporal.coarse_cannot_mint_equations
#print axioms Temporal.marker_not_descends_coarse

end Mettapedia.TypeTheory.IdentityNotions
