import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrderMachine
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopeBoundary

/-!
# A marked return belongs to one source scope depth

Frontier marks belong to the current depth; a saved caller mark belongs to
the parent depth. Child frontiers may be untracked while their saved caller
retains the outer obligation. Combined with earned call-stack order, this
metadata identifies the active frame without assuming its depth.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkDepth

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

structure ScopeAt (owner depth : Nat) (marks : Marks) : Prop where
  frontier : ∀ mark ∈ marks.frontier, ∀ index, mark = some index → owner = depth
  caller : ∀ index, marks.caller = some index → owner + 1 = depth

inductive Depths (owner : Nat) : List Marks → Prop where
  | nil : Depths owner []
  | cons {marks : Marks} {parents : List Marks}
      (here : ScopeAt owner (parents.length + 1) marks) (rest : Depths owner parents) :
      Depths owner (marks :: parents)

theorem untracked_at {User : Type} (owner depth : Nat) (current : Scope User) :
    ScopeAt owner depth (PettaSelectedReturnScopes.untracked current) := by
  constructor
  · intro mark member index marked
    have empty : mark = none := (List.mem_replicate.mp member).2
    rw [empty] at marked
    cases marked
  · intro index impossible
    cases impossible

theorem untracked_depths {User : Type} (owner : Nat) (scopes : List (Scope User)) :
    Depths owner (scopes.map PettaSelectedReturnScopes.untracked) := by
  induction scopes with
  | nil => exact .nil
  | cons current parents ih => exact .cons (untracked_at owner _ current) ih

theorem frontier_owner {owner : Nat} {marks : Marks} {parents : List Marks}
    (held : Depths owner (marks :: parents)) (index : Nat) (marked : some index ∈ marks.frontier) :
    owner = parents.length + 1 := by
  cases held with
  | cons here rest => exact here.frontier (some index) marked index rfl

theorem source_owner_of_stack {User : Type} {Held : Nat → Work User → Prop} {owner : Nat}
    (source : State User) (marks : Marks) (parents : List Marks)
    (stack : PettaScopeMarks.Stack Held (marks :: parents) source.2.scopes)
    (held : Depths owner (marks :: parents)) (index : Nat)
    (marked : some index ∈ marks.frontier) : owner = source.2.scopes.length := by
  have actual := frontier_owner held index marked
  have length := List.Forall₂.length_eq stack
  simp only [List.length_cons] at length
  omega

theorem source_owner {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (marks : Marks) (parents : List Marks)
    (stack : PettaSelectedReturnScopes.Stack saved argument (marks :: parents) source.2.scopes)
    (held : Depths saved.scopeDepth (marks :: parents)) (index : Nat)
    (marked : some index ∈ marks.frontier) : saved.scopeDepth = source.2.scopes.length :=
  source_owner_of_stack source marks parents stack held index marked

theorem ScopeAt.forward {User : Type} {owner depth : Nat} (mark : Option Nat) (pending : List (Option Nat))
    (caller : Option Nat) (held : ScopeAt owner depth ⟨mark :: pending, caller⟩)
    (before : Work User) (generated : List (Work User)) :
    ScopeAt owner depth
      ⟨generated.map (fun item => PettaReturnMarkUpdate.shift before.2.1.calls.length item.2.1.calls.length mark) ++ pending, caller⟩ := by
  refine ⟨?_, held.caller⟩
  intro selected member index same
  rcases List.mem_append.mp member with fresh | old
  · obtain ⟨item, _present, produced⟩ := List.mem_map.mp fresh
    have shifted := produced.trans same
    obtain ⟨original, origin, _within, _position⟩ := PettaReturnMarkUpdate.shift_has_origin shifted
    exact held.frontier mark List.mem_cons_self original origin
  · exact held.frontier selected (List.mem_cons_of_mem _ old) index same

theorem ScopeAt.drop_pending {owner depth : Nat} (mark : Option Nat) (pending : List (Option Nat))
    (caller : Option Nat) (held : ScopeAt owner depth ⟨mark :: pending, caller⟩) (removed : Nat) :
    ScopeAt owner depth ⟨mark :: pending.drop removed, caller⟩ := by
  refine ⟨?_, held.caller⟩
  intro selected member index same
  rcases List.mem_cons.mp member with first | old
  · exact held.frontier mark List.mem_cons_self index (first.symm.trans same)
  · exact held.frontier selected (List.mem_cons_of_mem _ (List.mem_of_mem_drop old)) index same

theorem collection_push {owner : Nat} (mark : Option Nat) (pending : List (Option Nat))
    (caller : Option Nat) (parents : List Marks)
    (held : Depths owner (⟨mark :: pending, caller⟩ :: parents)) (childCount : Nat) :
    Depths owner (⟨List.replicate childCount none, mark⟩ :: ⟨pending, caller⟩ :: parents) := by
  cases held with
  | cons here rest =>
      apply Depths.cons
      · constructor
        · intro selected member index same
          have empty : selected = none := (List.mem_replicate.mp member).2
          rw [empty] at same
          cases same
        · intro index marked
          have owner := here.frontier mark List.mem_cons_self index marked
          simp only [List.length_cons]
          omega
      · exact .cons ⟨fun selected member index same =>
          here.frontier selected (List.mem_cons_of_mem _ member) index same, here.caller⟩ rest

theorem collection_resume {owner : Nat} (child parent : Marks) (parents : List Marks)
    (held : Depths owner (child :: parent :: parents)) :
    Depths owner (⟨child.caller :: parent.frontier, parent.caller⟩ :: parents) := by
  cases held with
  | cons childAt rest =>
      cases rest with
      | cons parentAt outside =>
          refine .cons ⟨?_, parentAt.caller⟩ outside
          intro mark member index marked
          rcases List.mem_cons.mp member with rfl | previous
          · have owner := childAt.caller index marked
            simp only [List.length_cons] at owner
            omega
          · exact parentAt.frontier mark previous index marked

theorem same_scope_depth {User : Type} {owner depth : Nat} (source : State User) (current after : Scope User)
    (marks next : Marks) (held : ScopeAt owner depth marks)
    (computed : PettaReturnMarkUpdate.sameScope source current marks after = some next) : ScopeAt owner depth next := by
  cases marks with
  | mk tags caller =>
    cases front : current.frontier with
    | nil =>
        cases labels : tags with
        | nil =>
            simp only [labels] at held computed
            simp only [PettaReturnMarkUpdate.sameScope, front] at computed
            cases Option.some.inj computed
            exact held
        | cons mark pending => simp [PettaReturnMarkUpdate.sameScope, front, labels] at computed
    | cons before pending =>
        cases labels : tags with
        | nil => simp [PettaReturnMarkUpdate.sameScope, front, labels] at computed
        | cons mark pendingMarks =>
            simp only [labels] at held computed
            simp only [PettaReturnMarkUpdate.sameScope, front] at computed
            cases active : PettaReturnMarkUpdate.frameActive source with
            | true =>
                simp only [active, if_true] at computed
                cases Option.some.inj computed
                exact ScopeAt.forward mark pendingMarks caller held before _
            | false =>
                simp only [active, Bool.false_eq_true, if_false] at computed
                split at computed
                next older atCommit =>
                  cases Option.some.inj computed
                  exact ScopeAt.drop_pending mark pendingMarks caller held _
                next =>
                  cases Option.some.inj computed
                  exact ScopeAt.forward mark pendingMarks caller held before _

/-- The update itself preserves ownership depths. Separate source and typed
operation laws check that surviving marks retain their return obligations;
this metadata law cannot manufacture a new owning scope. -/
theorem advance_depths {User : Type} {owner : Nat} (marks next : List Marks) (source after : State User)
    (held : Depths owner marks) (computed : PettaReturnMarkUpdate.advance marks source after = some next) :
    Depths owner next := by
  cases oldScopes : source.2.scopes with
  | nil =>
      cases marks with
      | nil =>
          cases afterScopes : after.2.scopes with
          | nil =>
              simp only [PettaReturnMarkUpdate.advance, oldScopes, afterScopes] at computed
              cases Option.some.inj computed
              exact .nil
          | cons current parents => simp [PettaReturnMarkUpdate.advance, oldScopes, afterScopes] at computed
      | cons mark parents => simp [PettaReturnMarkUpdate.advance, oldScopes] at computed
  | cons current parents =>
      cases marks with
      | nil => simp [PettaReturnMarkUpdate.advance, oldScopes] at computed
      | cons mark labels =>
        cases afterScopes : after.2.scopes with
        | nil => simp [PettaReturnMarkUpdate.advance, oldScopes, afterScopes] at computed
        | cons reached reachedParents =>
          simp only [PettaReturnMarkUpdate.advance, oldScopes, afterScopes] at computed
          split at computed
          next same =>
            cases localUpdate : PettaReturnMarkUpdate.sameScope source current mark reached with
            | none => simp [localUpdate] at computed
            | some label =>
                simp only [localUpdate, Option.map_some] at computed
                cases Option.some.inj computed
                cases held with
                | cons here rest => exact .cons (same_scope_depth source current reached mark label here localUpdate) rest
          next different =>
            split at computed
            next pushed =>
              cases front : current.frontier with
              | nil => simp [front] at computed
              | cons before pending =>
                cases tags : mark.frontier with
                | nil => simp [front, tags] at computed
                | cons selected pendingMarks =>
                    simp only [front, tags] at computed
                    cases Option.some.inj computed
                    have shape : mark = ⟨selected :: pendingMarks, mark.caller⟩ := by cases mark; simp_all
                    rw [shape] at held
                    exact collection_push selected pendingMarks mark.caller labels held reached.frontier.length
            next notPushed =>
              split at computed
              next popped =>
                cases parents with
                | nil => simp at computed
                | cons parent outer =>
                  cases labels with
                  | nil => simp at computed
                  | cons parentMark outside =>
                      cases Option.some.inj computed
                      exact collection_resume mark parentMark outside held
              next unchanged => cases computed

theorem initial_depths {User : Type} (saved : CallFrame) (parents : List (Scope User))
    (generatedCount pendingCount : Nat) (owner : saved.scopeDepth = parents.length + 1) :
    Depths saved.scopeDepth
      (⟨List.replicate generatedCount (some 0) ++ List.replicate pendingCount none, none⟩ ::
        parents.map PettaSelectedReturnScopes.untracked) := by
  refine .cons ⟨?_, ?_⟩ (untracked_depths saved.scopeDepth parents)
  · intro mark member index marked
    rcases List.mem_append.mp member with _fresh | old
    · simpa only [List.length_map] using owner
    · have empty : mark = none := (List.mem_replicate.mp old).2
      rw [empty] at marked
      cases marked
  · intro index impossible
    cases impossible

theorem active_top_depth_of_positions {User : Type} {saved : CallFrame} {Held : Nat → Work User → Prop}
    (position : ∀ {index : Nat} {item : Work User}, Held index item → item.2.1.calls[index]? = some saved)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks) (index : Nat)
    (stack : PettaScopeMarks.Stack Held
      (⟨some index :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (depths : Depths saved.scopeDepth (⟨some index :: pendingMarks, callerMark⟩ :: parentMarks))
    (good : PettaCallOrder.Invariant source)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (frame : CallFrame) (outside : List CallFrame) (calls : context.calls = frame :: outside) :
    frame.scopeDepth = source.2.scopes.length := by
  have owner := source_owner_of_stack source _ parentMarks stack depths index List.mem_cons_self
  have contextOrder := PettaContextFacts.active source current parents control context origins pending good.1 scopes front
  have contextBounds := PettaCallOrder.active_bounds source current parents control context origins pending good.2 scopes front
  have selected := PettaScopeMarks.active_work current control context origins pending index pendingMarks callerMark
    (List.forall₂_cons.mp (scopes ▸ stack)).1 front
  exact PettaCallOrder.member_depth contextOrder contextBounds (List.mem_of_getElem? (position selected)) owner calls

theorem active_top_depth {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks) (index : Nat)
    (stack : PettaSelectedReturnScopes.Stack saved argument
      (⟨some index :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (depths : Depths saved.scopeDepth (⟨some index :: pendingMarks, callerMark⟩ :: parentMarks))
    (good : PettaCallOrder.Invariant source)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (frame : CallFrame) (outside : List CallFrame) (calls : context.calls = frame :: outside) :
    frame.scopeDepth = source.2.scopes.length :=
  active_top_depth_of_positions (fun tracked => PettaSelectedReturnWork.selected_position tracked) source current parents
    control context origins pending pendingMarks callerMark parentMarks index stack depths good scopes front frame outside calls

/-- A terminal owned occurrence cannot bypass the active typed dispatcher.
Its depth is derived from the actual scope and call-order invariants. -/
theorem terminal_unmarked_of_positions {User : Type} {saved : CallFrame} {Held : Nat → Work User → Prop}
    (position : ∀ {index : Nat} {item : Work User}, Held index item → item.2.1.calls[index]? = some saved)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (stack : PettaScopeMarks.Stack Held
      (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (depths : Depths saved.scopeDepth (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks))
    (good : PettaCallOrder.Invariant source)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (inactive : PettaReturnMarkUpdate.frameActive source = false)
    (terminal : control.goals = []) : mark = none := by
  cases mark with
  | none => rfl
  | some index =>
      have selected := PettaScopeMarks.active_work current control context origins pending index pendingMarks callerMark
        (List.forall₂_cons.mp (scopes ▸ stack)).1 front
      have present := position selected
      cases calls : context.calls with
      | nil => simp only [calls, List.getElem?_nil] at present; cases present
      | cons frame outside =>
          have depth := active_top_depth_of_positions position source current parents control context origins pending pendingMarks callerMark parentMarks
            index stack depths good scopes front frame outside calls
          have active := PettaReturnMarkUpdate.frame_active_at source current parents control context origins pending
            frame outside scopes front calls depth (.inr terminal)
          rw [inactive] at active
          cases active

theorem terminal_unmarked {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (stack : PettaSelectedReturnScopes.Stack saved argument
      (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (depths : Depths saved.scopeDepth (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks))
    (good : PettaCallOrder.Invariant source)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (inactive : PettaReturnMarkUpdate.frameActive source = false) (terminal : control.goals = []) : mark = none :=
  terminal_unmarked_of_positions (fun tracked => PettaSelectedReturnWork.selected_position tracked) source current parents
    control context origins pending mark pendingMarks callerMark parentMarks stack depths good scopes front inactive terminal

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkDepth
