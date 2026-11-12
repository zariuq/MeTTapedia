import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkTyped

/-!
# Every actual typed/source dispatcher step preserves return lineage

The selected frame is already in its body phase. Its argument phases cannot
be mistaken for owned inner calls, even when identical frames occur elsewhere.
All marker choices are the output of the deterministic positional update.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks Stack WorkMarked)

theorem not_selected_argument {User : Type} {saved : CallFrame} {argument : Atom}
    (control : DControl) (context : Context User) (origins : List Nat) (mark : Option Nat)
    (frame : CallFrame) (outside : List CallFrame)
    (held : WorkMarked saved argument mark (control, context, origins))
    (calls : context.calls = frame :: outside) (body : saved.phase = .body)
    (notBody : frame.phase ≠ .body) : mark ≠ some 0 := by
  intro selected
  have present := PettaSelectedReturnWork.selected_position (held 0 selected)
  have same : frame = saved := Option.some.inj (by simpa only [calls, List.getElem?_cons_zero] using present)
  exact notBody (same ▸ body)

theorem delegate_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks))
    (good : PettaCallOrder.Invariant source) (inactive : frameActive source = false)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (delegate operations .eagerValue program source current parents control context origins pending) := by
  unfold delegate
  split
  next head arguments destination older atCall =>
    split
    next admitted =>
      have ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at admitted
        exact admitted.1
      split
      · exact owned_step_keeps program source _ held depths good inactive
      · exact rows_keeps operations source current parents control context origins pending mark pendingMarks callerMark parentMarks
          head arguments destination older held scopes front atCall ordinary
    next => exact owned_step_keeps program source _ held depths good inactive
  next => exact owned_step_keeps program source _ held depths good inactive

theorem step_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (source : State User) (marks : List Marks)
    (held : Stack saved argument marks source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth marks)
    (good : PettaCallOrder.Invariant source) (body : saved.phase = .body) :
    Preserves saved argument marks source (PettaOccurrenceOverlay.step operations .eagerValue program source) := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (good.2.nonempty scopes)
  | cons current parents =>
      cases front : current.frontier with
      | nil =>
          have inactive : frameActive source = false := by
            simp [frameActive, PettaInheritedContext.nest, PettaInheritedContext.boundary,
              Bridges.DestinationContextMap.state, Bridges.DestinationContextMap.configuration,
              Bridges.DestinationContextMap.scope, scopes, front]
          simpa only [PettaOccurrenceOverlay.step, scopes, front] using
            owned_step_keeps program source marks held depths good inactive
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          cases marks with
          | nil => rw [scopes] at held; cases held
          | cons currentMarks parentMarks =>
              rcases currentMarks with ⟨tags, callerMark⟩
              cases tags with
              | nil =>
                  have impossible := (List.forall₂_cons.mp (scopes ▸ held)).1.1
                  rw [front] at impossible
                  cases impossible
              | cons mark pendingMarks =>
                  have active : WorkMarked saved argument mark (control, context, origins) :=
                    (List.forall₂_cons.mp (front ▸ (List.forall₂_cons.mp (scopes ▸ held)).1.1)).1
                  have view := frame_active_view source current parents control context origins pending scopes front
                  cases calls : context.calls with
                  | nil =>
                      have inactive : frameActive source = false := by simpa only [calls] using view
                      simpa only [PettaOccurrenceOverlay.step, scopes, front, calls] using
                        delegate_keeps operations program source current parents control context origins pending mark pendingMarks
                          callerMark parentMarks held depths good inactive scopes front
                  | cons frame outside =>
                      by_cases level : frame.scopeDepth = parents.length + 1
                      · have depth : frame.scopeDepth = source.2.scopes.length := by
                          simpa only [scopes, List.length_cons] using level
                        simp only [PettaOccurrenceOverlay.step, scopes, front, calls, List.length_cons, if_pos level]
                        cases phase : frame.phase with
                        | nextArgument =>
                            exact next_argument_keeps operations source current parents control context origins pending mark pendingMarks
                              callerMark parentMarks frame outside held scopes front calls depth phase
                              (not_selected_argument control context origins mark frame outside active calls body (by simp [phase]))
                        | argument formal slot =>
                            by_cases terminal : control.goals.isEmpty = true
                            · simp only [terminal, if_true]
                              cases resolved : resolve control.bindings with
                              | none => exact call_keeps _ source _ held
                              | some environment =>
                                  exact argument_guard_keeps operations source current parents control context origins pending mark
                                    pendingMarks callerMark parentMarks frame outside formal slot (read environment control.destination)
                                    held scopes front calls depth (List.isEmpty_iff.mp terminal)
                                    (not_selected_argument control context origins mark frame outside active calls body (by simp [phase]))
                            · have inactive : frameActive source = false := by
                                simpa only [calls, depth, decide_true, phase, Bool.true_and, Bool.eq_false_iff.mpr terminal] using view
                              simp only [terminal]
                              exact delegate_keeps operations program source current parents control context origins pending mark
                                pendingMarks callerMark parentMarks held depths good inactive scopes front
                        | body =>
                            by_cases terminal : control.goals.isEmpty = true
                            · simp only [terminal, if_true]
                              cases resolved : resolve control.bindings with
                              | none => exact call_keeps _ source _ held
                              | some environment =>
                                  exact body_guard_keeps operations source current parents control context origins pending mark pendingMarks
                                    callerMark parentMarks frame outside (read environment control.destination) held scopes front calls depth
                                    (List.isEmpty_iff.mp terminal)
                            · have inactive : frameActive source = false := by
                                simpa only [calls, depth, decide_true, phase, Bool.true_and, Bool.eq_false_iff.mpr terminal] using view
                              simp only [terminal]
                              exact delegate_keeps operations program source current parents control context origins pending mark
                                pendingMarks callerMark parentMarks held depths good inactive scopes front
                      · have notDepth : frame.scopeDepth ≠ source.2.scopes.length := by
                          simpa only [scopes, List.length_cons] using level
                        have inactive : frameActive source = false := by
                          simpa only [calls, decide_false, notDepth, Bool.false_and] using view
                        simp only [PettaOccurrenceOverlay.step, scopes, front, calls, List.length_cons, if_neg level]
                        exact delegate_keeps operations program source current parents control context origins pending mark pendingMarks
                          callerMark parentMarks held depths good inactive scopes front

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
