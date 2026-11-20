import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derived
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derivations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Congruence

/-!
# Two held rules that overlap: when their results agree and when they differ

Over first-order atoms at one frame, at the state with one token `1`, holding two rules of the
present step persistently at the identities `0` and `1` (`holding`, with no ambient program). The
rules of each pair **overlap**: their take patterns are the same term `1`, so both fire on the token.

* **Results agree** (`agree_pair`): the link from `1` to `2` and the same link with a guard that
  always holds. The two occurrences fire on the token with the same selection and reach the **same
  state**: which declaration is used does not show in the result.
* **Results differ** (`differ_pair`): the link from `1` to `2` and the link from `1` to `3`. Both
  occurrences fire on the token, and the two results are different states: the row made is `2` in one
  and `3` in the other.
* **The check** (`link_results_eq_iff`): for two links that take the same term, the results of their
  firings with the same opening and selection are equal exactly when the terms they make are equal.
  For rules without unknowns, "unify the take patterns, compare the results" is this comparison.

So for an overlapping pair there are two cases and a decidable test between them. Where the results
agree no choice between the declarations is observable; where they differ both results are reachable
and nothing in the step orders them.

* **One rule held twice** (`twice_not_injective`): with the same link held at two identities, two
  admitted firings lie over one firing of the program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Overlap

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open Examples (Tm X E c tokenState)
open Derived (link)
open Derived.Atoms (tokenFiring token_admitted)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- The link from `1` to `2` with a guard that always holds. -/
def guardedLink : Rule Tm := ⟨PUnit.unit, ⟨[c 1], [], [], [.equal (c 5) (c 5)], [c 2]⟩, []⟩

/-- The guarded link takes the token at row `0` and makes row `1`. -/
def guardedFiring {P : Program Tm} (member : guardedLink ∈ P) : Firing ℕ E P tokenState.frame :=
  ⟨guardedLink, member, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩

theorem guarded_admitted {P : Program Tm} (member : guardedLink ∈ P) :
    (guardedFiring member).Admits X tokenState := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action tokenState (guardedFiring member)
    intro t inside σ
    have terms : t ∈ [c 1, c 5, c 5, c 2] := inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at terms
    rcases terms with isTerm | isTerm | isTerm | isTerm <;> rw [isTerm] <;> rfl
  · apply enabled_of <;> simp [guardedFiring, tokenState]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
    have equation : e ∈ [(c 1, c 1)] := inside
    obtain rfl := List.mem_singleton.mp equation
    rfl
  · intro _ σ _
    refine ⟨fun check inside => ?_, fun q inside => absurd inside List.not_mem_nil⟩
    have checks : check ∈ [Check.equal (c 5) (c 5)] := inside
    obtain rfl := List.mem_singleton.mp checks
    rfl

/-- **The link and the guarded link reach the same state** from the token. -/
theorem guarded_result {P : Program Tm} (member : guardedLink ∈ P) (member' : link (c 1) (c 2) ∈ P) :
    (guardedFiring member).result X tokenState = (tokenFiring 2 member').result X tokenState := rfl

/-- **The check for links**: with the same taken term, opening and selection, two links reach the same
state exactly when they make the same term. -/
theorem link_results_eq_iff {P : Program Tm} (made made' : ℕ) (member : link (c 1) (c made) ∈ P)
    (member' : link (c 1) (c made') ∈ P) :
    (tokenFiring made member).result X tokenState = (tokenFiring made' member').result X tokenState ↔
      made = made' := by
  constructor
  · intro same
    have labels : ((tokenFiring made member).result X tokenState).label 1 =
        ((tokenFiring made' member').result X tokenState).label 1 := by rw [same]
    have constants : c made = c made' := labels
    exact Term.const.inj constants
  · rintro rfl
    rfl

/-! ## The two pairs, held as rule occurrences -/

/-- The token state holding the rule `first` at identity `0` and the rule `second` at identity `1`. -/
abbrev pair (first second : Rule Tm) : RState Tm ℕ ℕ (Rule Tm) Unit :=
  holding tokenState {0, 1} (fun ρ => if ρ = 0 then first else second) (fun _ => ())

/-- **An overlapping pair whose results agree**: the two occurrences fire on the token and reach the
same state. -/
theorem agree_pair :
    ∃ f f' : RFiring ℕ ℕ E (ofRules Unit) (pair (link (c 1) (c 2)) guardedLink),
      f.use = Use.held 0 ∧ f'.use = Use.held 1 ∧ f.Admits X (∅ : Set (Rule Tm)) ∧
        f'.Admits X (∅ : Set (Rule Tm)) ∧ f.result X = f'.result X := by
  have member : link (c 1) (c 2) ∈ ({link (c 1) (c 2), guardedLink} : Program Tm) := Or.inl rfl
  have member' : guardedLink ∈ ({link (c 1) (c 2), guardedLink} : Program Tm) := Or.inr rfl
  obtain ⟨f, -, use, -, admitted, result⟩ :=
    lift_admits (rules := {0, 1}) (code := fun ρ => if ρ = 0 then link (c 1) (c 2) else guardedLink)
      (zone := fun _ => ()) (ambient := (∅ : Set (Rule Tm))) (u := Use.held 0) X
      (tokenFiring 2 member) (token_admitted 2 member) (Finset.mem_insert_self 0 {1}) rfl
  obtain ⟨f', -, use', -, admitted', result'⟩ :=
    lift_admits (rules := {0, 1}) (code := fun ρ => if ρ = 0 then link (c 1) (c 2) else guardedLink)
      (zone := fun _ => ()) (ambient := (∅ : Set (Rule Tm))) (u := Use.held 1) X
      (guardedFiring member') (guarded_admitted member')
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self 1)) rfl
  refine ⟨f, f', use, use', admitted, admitted', ?_⟩
  rw [result, result', guarded_result member' member]

/-- **An overlapping pair whose results differ**: the two occurrences fire on the token and reach
different states. -/
theorem differ_pair :
    ∃ f f' : RFiring ℕ ℕ E (ofRules Unit) (pair (link (c 1) (c 2)) (link (c 1) (c 3))),
      f.use = Use.held 0 ∧ f'.use = Use.held 1 ∧ f.Admits X (∅ : Set (Rule Tm)) ∧
        f'.Admits X (∅ : Set (Rule Tm)) ∧ f.result X ≠ f'.result X := by
  have member : link (c 1) (c 2) ∈ ({link (c 1) (c 2), link (c 1) (c 3)} : Program Tm) := Or.inl rfl
  have member' : link (c 1) (c 3) ∈ ({link (c 1) (c 2), link (c 1) (c 3)} : Program Tm) := Or.inr rfl
  obtain ⟨f, -, use, -, admitted, result⟩ :=
    lift_admits (rules := {0, 1})
      (code := fun ρ => if ρ = 0 then link (c 1) (c 2) else link (c 1) (c 3))
      (zone := fun _ => ()) (ambient := (∅ : Set (Rule Tm))) (u := Use.held 0) X
      (tokenFiring 2 member) (token_admitted 2 member) (Finset.mem_insert_self 0 {1}) rfl
  obtain ⟨f', -, use', -, admitted', result'⟩ :=
    lift_admits (rules := {0, 1})
      (code := fun ρ => if ρ = 0 then link (c 1) (c 2) else link (c 1) (c 3))
      (zone := fun _ => ()) (ambient := (∅ : Set (Rule Tm))) (u := Use.held 1) X
      (tokenFiring 3 member') (token_admitted 3 member')
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self 1)) rfl
  refine ⟨f, f', use, use', admitted, admitted', ?_⟩
  rw [result, result']
  intro same
  have states := holding_injective same
  exact absurd ((link_results_eq_iff 2 3 member member').mp states) (by decide)

/-! ## One rule held twice -/

/-- **A rule held by two identities has two firings over each firing of the program**: at the token
state, with the link from `1` to `2` held at the identities `0` and `1`, the projection onto the
firings of the program is not injective. This is the instance of the hypotheses of
`two_over_one` and `not_injective_of_twice`. -/
theorem twice_not_injective :
    ¬ Function.Injective (project (E := E) (P := (∅ : Program Tm)) X
      (offers_image (fun _ : ℕ => link (c 1) (c 2)) {0, 1}) (fun _ : ℕ => ()) tokenState) :=
  not_injective_of_twice X (offers_image (fun _ : ℕ => link (c 1) (c 2)) {0, 1}) (fun _ : ℕ => ())
    ⟨tokenFiring 2 (Or.inr ⟨0, Finset.mem_coe.mpr (Finset.mem_insert_self 0 {1}), rfl⟩),
      token_admitted 2 _⟩
    (ρ := 0) (ρ' := 1) (Finset.mem_insert_self 0 {1})
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self 1)) (by decide) rfl rfl

#print axioms twice_not_injective
#print axioms guarded_admitted
#print axioms guarded_result
#print axioms link_results_eq_iff
#print axioms agree_pair
#print axioms differ_pair

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Overlap
