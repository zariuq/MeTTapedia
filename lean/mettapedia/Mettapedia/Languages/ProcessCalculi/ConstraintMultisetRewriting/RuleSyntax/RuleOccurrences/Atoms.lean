import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Plain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Tools for examples of the candidate at one frame

Three facts used by the examples and controls of this folder.

* `enabled_of`: a selection is enabled when its taken and read rows are present, no row is both
  taken and read, and its made identities are not present.
* `holds_of_none`: a firing whose spec has no checks, no collect patterns, no rule queries and no
  installed or removed rules passes its guard predicate at every solution.
* `fresh_of_ground`: at one frame, with the identity extension, a firing whose spec's terms every
  substitution fixes is opened freshly by any opening (the tree's `Examples.fresh_of_ground`, for the
  candidate).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (Terms frames ext)

universe uO uT uH uE uOcc uR uC uZ uS

/-- **A selection is enabled** when its taken and read rows are present, no row is both taken and
read, and its made identities are not present. -/
theorem enabled_of {O : Type uOcc} [DecidableEq O] {present : Finset O} {selection : Selection O}
    (taken : ∀ o ∈ selection.taken, o ∈ present) (read : ∀ o ∈ selection.read, o ∈ present)
    (apart : ∀ o ∈ selection.taken, o ∉ selection.read)
    (fresh : ∀ o ∈ selection.made, o ∉ present) :
    Enabled (fun _ : O => ()) present (selection.commit (T := Unit)) where
  taken_subset := fun o inside => taken o (List.mem_toFinset.mp inside)
  kept_subset := fun o inside => read o (List.mem_toFinset.mp inside)
  apart := Finset.disjoint_left.mpr fun o inTaken inRead =>
    apart o (List.mem_toFinset.mp inTaken) (List.mem_toFinset.mp inRead)
  fresh := Finset.disjoint_left.mpr fun o inMade inPresent =>
    fresh o (List.mem_toFinset.mp inMade) inPresent
  queries_hold := fun _ inside => absurd inside List.not_mem_nil

section Guards

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)
  {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ} {E : Extensions.{uO, uH, uE} Hom}
  {codes : Codes Tm C Z} {s : RState Tm O R C Z} (f : RFiring O R E codes s)

/-- **Nothing to check**: a firing whose spec has no checks, no collect patterns, no rule queries and
no installed or removed rules passes its guard predicate at every solution. -/
theorem holds_of_none (checks : f.spec.body.checks = []) (collect : f.spec.collect = [])
    (unmatched : f.spec.unmatched = []) (installs : f.spec.installs = [])
    (removes : f.spec.removes = []) (publishes : f.spec.publishes = []) {b : Obj}
    (σ : Hom (E.target f.ext) b) : f.Holds X σ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro check member
    have opened : (f.base.opened X).checks = f.spec.body.checks.map (Check.map (X.act f.opening)) := rfl
    rw [opened, checks] at member
    exact absurd member List.not_mem_nil
  · intro q member
    have opened : f.base.collectOpened X = f.spec.collect.map (X.act f.opening) := rfl
    rw [opened, collect] at member
    exact absurd member List.not_mem_nil
  · intro q member
    rw [unmatched] at member
    exact absurd member List.not_mem_nil
  · intro x member
    rw [installs, List.zip_nil_left] at member
    exact absurd member List.not_mem_nil
  · intro x member
    rw [removes, List.zip_nil_left] at member
    exact absurd member List.not_mem_nil
  · intro x member
    rw [publishes, List.zip_nil_left] at member
    exact absurd member List.not_mem_nil

end Guards

section Ground

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uOcc} {R : Type uR}
  {C : Type uC} {Z : Type uZ} {codes : Codes (Terms T) C Z}

/-- **A spec whose terms every substitution fixes is opened freshly by any opening**, at every state
whatever it mentions. -/
theorem fresh_of_ground {s : RState (Terms T) O R C Z} (f : RFiring O R (ext A) codes s)
    (ground : ∀ t ∈ f.spec.terms, ∀ σ : S, A.apply σ t = t) : f.Fresh (frames A) := by
  intro b θ h
  refine ⟨θ, fun t _ => ?_, fun t member => ?_⟩
  · show A.E (A.apply θ (A.apply A.identity t)) (A.apply θ t)
    rw [A.apply_identity]
    exact A.equivalence.refl _
  · show A.E (A.apply θ (A.apply f.opening t)) (A.apply h t)
    rw [ground t member f.opening, ground t member θ, ground t member h]
    exact A.equivalence.refl _

end Ground

#print axioms enabled_of
#print axioms holds_of_none
#print axioms fresh_of_ground

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
