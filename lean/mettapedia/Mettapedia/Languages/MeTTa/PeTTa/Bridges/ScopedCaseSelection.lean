import Mettapedia.Languages.MeTTa.PeTTa.DestinationProtectedSlots

/-!
# First matching case arm over reached Destination equations

Selection commits before the selected body runs. The operation uses the same
two-way finite-term refinement as the existing source owner, with no term
record reset. The independent judgment records every preceding refusal.
It neither evaluates the key nor runs any body; those remain source tasks.
Native pattern views require their own admission/representation connection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseSelection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination

structure Choice where
  occurrence : Nat
  bindings : Equations
  body : Atom
  deriving DecidableEq

def select (bindings : Equations) (key : Atom) : Nat → SpaceSemantics.Cases → Option Choice
  | _, [] => none
  | occurrence, (pattern, body) :: rest =>
      match refine bindings pattern key with
      | some bound => some ⟨occurrence, bound, body⟩
      | none => select bindings key (occurrence + 1) rest

inductive Selection (bindings : Equations) (key : Atom) :
    Nat → SpaceSemantics.Cases → Option Choice → Prop where
  | exhausted (occurrence : Nat) : Selection bindings key occurrence [] none
  | selected (occurrence : Nat) (pattern body : Atom) (rest : SpaceSemantics.Cases) (bound : Equations)
      (matched : Refinement bindings pattern key (some bound)) :
      Selection bindings key occurrence ((pattern, body) :: rest) (some ⟨occurrence, bound, body⟩)
  | refused (occurrence : Nat) (pattern body : Atom) (rest : SpaceSemantics.Cases) (outcome : Option Choice)
      (unmatched : Refinement bindings pattern key none)
      (later : Selection bindings key (occurrence + 1) rest outcome) :
      Selection bindings key occurrence ((pattern, body) :: rest) outcome

theorem select_has_source (bindings : Equations) (key : Atom) (occurrence : Nat) (rows : SpaceSemantics.Cases) :
    Selection bindings key occurrence rows (select bindings key occurrence rows) := by
  induction rows generalizing occurrence with
  | nil => exact .exhausted _
  | cons row rest ih =>
      rcases row with ⟨pattern, body⟩
      cases matched : refine bindings pattern key with
      | none => simpa only [select, matched] using
          Selection.refused occurrence pattern body rest _ ((refinement_iff _ _ _ _).mpr matched) (ih (occurrence + 1))
      | some bound => simpa only [select, matched] using
          Selection.selected occurrence pattern body rest bound ((refinement_iff _ _ _ _).mpr matched)

theorem Selection.execution {bindings : Equations} {key : Atom} {occurrence : Nat}
    {rows : SpaceSemantics.Cases} {outcome : Option Choice}
    (source : Selection bindings key occurrence rows outcome) : select bindings key occurrence rows = outcome := by
  induction source with
  | exhausted => rfl
  | selected occurrence pattern body rest bound matched => simp [select, (refinement_iff _ _ _ _).mp matched]
  | refused occurrence pattern body rest outcome unmatched later ih =>
      simpa only [select, (refinement_iff _ _ _ _).mp unmatched] using ih

theorem select_iff_source (bindings : Equations) (key : Atom) (occurrence : Nat)
    (rows : SpaceSemantics.Cases) (outcome : Option Choice) :
    select bindings key occurrence rows = outcome ↔ Selection bindings key occurrence rows outcome := by
  constructor
  · rintro rfl
    exact select_has_source _ _ _ _
  · exact Selection.execution

theorem selected_record {bindings : Equations} {key : Atom} {occurrence : Nat}
    {rows : SpaceSemantics.Cases} {choice : Choice}
    (source : Selection bindings key occurrence rows (some choice)) :
    RefinementTransport.Extends bindings choice.bindings ∧
      ∃ pattern, (pattern, choice.body) ∈ rows ∧
        choice.bindings = bindings ++ [(pattern, key)] ∧
        ∃ environment, Solves environment choice.bindings := by
  induction rows generalizing occurrence with
  | nil => cases source
  | cons row rest ih =>
      cases source with
      | selected occurrence pattern body rest bound matched =>
          refine ⟨RefinementTransport.accepted_extends matched, pattern, List.mem_cons_self, ?_⟩
          cases matched with
          | accepted environment old same =>
              exact ⟨rfl, environment, (solves_append_equation _ _ _ _).mpr ⟨old, same⟩⟩
      | refused occurrence pattern body rest outcome unmatched later =>
          obtain ⟨extended, chosen, member, retained, solved⟩ := ih later
          exact ⟨extended, chosen, List.mem_cons_of_mem _ member, retained, solved⟩

theorem selected_occurrence {bindings : Equations} {key : Atom} {occurrence : Nat}
    {rows : SpaceSemantics.Cases} {choice : Choice}
    (source : Selection bindings key occurrence rows (some choice)) :
    occurrence ≤ choice.occurrence ∧ choice.occurrence < occurrence + rows.length := by
  induction rows generalizing occurrence with
  | nil => cases source
  | cons row rest ih =>
      cases source with
      | selected => simp
      | refused occurrence pattern body rest outcome unmatched later =>
          have bounds := ih later
          simp only [List.length_cons]
          omega

theorem selected_body_property {bindings : Equations} {key : Atom} {occurrence : Nat}
    {rows : SpaceSemantics.Cases} {choice : Choice} (property : Atom → Prop)
    (bodies : ∀ row ∈ rows, property row.2)
    (source : Selection bindings key occurrence rows (some choice)) : property choice.body := by
  obtain ⟨_, pattern, present, _⟩ := selected_record source
  exact bodies (pattern, choice.body) present

theorem selected_keeps_fixed {bindings : Equations} {key slot value : Atom} {occurrence : Nat}
    {rows : SpaceSemantics.Cases} {choice : Choice}
    (source : Selection bindings key occurrence rows (some choice))
    (fixed : ProtectedSlots.Fixed bindings slot value) : ProtectedSlots.Fixed choice.bindings slot value :=
  fixed.extends (selected_record source).1

/-- Adding later arms cannot turn failure of an already selected body into
a request to try those later arms. Pattern choice has committed already. -/
theorem selected_append {bindings : Equations} {key : Atom} {occurrence : Nat}
    {rows : SpaceSemantics.Cases} {choice : Choice}
    (source : Selection bindings key occurrence rows (some choice)) (extra : SpaceSemantics.Cases) :
    Selection bindings key occurrence (rows ++ extra) (some choice) := by
  induction rows generalizing occurrence with
  | nil => cases source
  | cons row rest ih =>
      cases source with
      | selected occurrence pattern body rest bound matched => exact .selected _ _ _ _ _ matched
      | refused occurrence pattern body rest outcome unmatched later => exact .refused _ _ _ _ _ unmatched (ih later)

theorem first_match_ignores_later_arms (bindings : Equations) (key pattern body : Atom)
    (occurrence : Nat) (bound : Equations) (left right : SpaceSemantics.Cases)
    (matched : refine bindings pattern key = some bound) :
    select bindings key occurrence ((pattern, body) :: left) =
      select bindings key occurrence ((pattern, body) :: right) := by simp [select, matched]

theorem no_selection_iff (bindings : Equations) (key : Atom) (occurrence : Nat)
    (rows : SpaceSemantics.Cases) :
    select bindings key occurrence rows = none ↔ ∀ row ∈ rows, refine bindings row.1 key = none := by
  induction rows generalizing occurrence with
  | nil => simp [select]
  | cons row rest ih =>
      rcases row with ⟨pattern, body⟩
      cases matched : refine bindings pattern key with
      | none => simpa [select, matched] using ih (occurrence + 1)
      | some bound => simp [select, matched]

namespace Controls

private def num (n : Int) : Atom := .grounded (.int n)
private def empty : Atom := .expression [.symbol "empty"]

theorem selected_empty_does_not_try_next_body :
    (select [] (num 1) 0 [(.var "x", empty), (.var "y", num 9)]).map Choice.body = some empty := by cbv

theorem earlier_incompatible_arm_is_skipped :
    (select [] (num 1) 0 [(num 2, .symbol "wrong"), (.var "x", num 9)]).map Choice.occurrence = some 1 := by cbv

theorem selection_retains_caller_alias :
    (select [(.var "caller", num 1)] (.var "caller") 0
      [(num 2, .symbol "wrong"), (.var "x", .var "caller")]).map Choice.bindings =
      some [(.var "caller", num 1), (.var "x", .var "caller")] := by cbv

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseSelection
