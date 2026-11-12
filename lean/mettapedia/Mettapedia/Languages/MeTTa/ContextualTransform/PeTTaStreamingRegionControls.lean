import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionReachability

/-!
# Missing, mismatched and correctly nested streaming regions

These controls distinguish marker association from ground values or valid
bindings. A stale callee handler may remain after return; the caller is not
inside it. First demand removes its own prefix and retains the outer bank.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingRegionControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Streaming

def a : Unifying.Answer := ⟨.symbol "a",[]⟩
def b : Unifying.Answer := ⟨.symbol "b",[]⟩
def base : State := {world := {state := Effects.empty},agenda := []}
def program : SpaceSemantics.Program := {equations := [],declarations := []}

def dangling : State :=
  {base with agenda := [.execute ⟨.returned [a],[.first 0]⟩],nextBoundary := 1}

theorem dangling_marker_is_detected : ¬Regions.WellFormed dangling := by
  intro good
  obtain ⟨remaining,found⟩ := Regions.first_resolves (Regions.head_and_tail good rfl).1
  have computed := found.computed
  change (none : Option (List Job)) = some remaining at computed
  cases computed

theorem dangling_delivery_does_not_invent_a_suffix : step program dangling = none := rfl

def wrongKind : State :=
  {base with agenda := [.execute ⟨.returned [a],[.first 0]⟩,.handler 0],nextBoundary := 1}

theorem same_number_wrong_kind_is_detected : ¬Regions.WellFormed wrongKind := by
  intro good
  obtain ⟨remaining,found⟩ := Regions.first_resolves (Regions.head_and_tail good rfl).1
  have computed := found.computed
  change (none : Option (List Job)) = some remaining at computed
  cases computed

def duplicateKeys : State := {base with agenda := [.first 0,.handler 0],nextBoundary := 1}

theorem different_kinds_cannot_reuse_a_key : ¬Regions.WellFormed duplicateKeys := by
  intro good
  have impossible : 0 < 0 := good.1.2.1
  omega

def wrongCaller : State :=
  {base with
    agenda := [.execute ⟨.returned [a],[.collection 0]⟩,.collect 0 [] [.source .dispatch] []]
    nextBoundary := 1}

theorem collection_caller_association_is_required : ¬Regions.WellFormed wrongCaller := by
  intro good
  have fit : Regions.framesFit (Regions.markers [.collect 0 [] [.source .dispatch] []]) [.collection 0] :=
    (Regions.head_and_tail good rfl).1
  obtain ⟨before,after,shape,nested⟩ := fit
  have present : Regions.Boundary.collection 0 [] ∈ Regions.markers [.collect 0 [] [.source .dispatch] []] := by
    rw [shape]
    exact List.mem_append_right _ List.mem_cons_self
  have equal : Regions.Boundary.collection 0 [] = Regions.Boundary.collection 0 [.source .dispatch] := by
    simpa only [Regions.markers,List.filterMap_cons,Regions.boundary,List.filterMap_nil,List.mem_singleton] using present
  have impossible := (Regions.Boundary.collection.inj equal).2
  cases impossible

def outsideHandler : State :=
  {base with agenda := [.execute ⟨.returned [a],[]⟩,.handler 0],nextBoundary := 1}

theorem returned_caller_can_be_outside_an_old_handler : Regions.WellFormed outsideHandler :=
  ⟨⟨by decide,True.intro⟩,True.intro,True.intro,True.intro⟩

def nestedFirst : State :=
  {base with
    agenda := [.execute ⟨.returned [a,b],[.first 1,.collection 0]⟩,
      .handler 2,.first 1,.collect 0 [] [] []]
    nextBoundary := 3}

theorem nested_first_is_wellFormed : Regions.WellFormed nestedFirst := by
  refine ⟨⟨by decide,⟨by decide,⟨by decide,True.intro⟩⟩⟩,?_,True.intro,True.intro,True.intro,True.intro⟩
  exact ⟨[.handler 2],[.collection 0 []],rfl,[],[],rfl,True.intro⟩

def afterCut : State :=
  {base with agenda := [.execute ⟨.returned [a],[.collection 0]⟩,.collect 0 [] [] []],nextBoundary := 3}

theorem first_cut_retains_the_outer_bank : step program nestedFirst = some afterCut := rfl

theorem first_cut_keeps_the_region_links : Regions.WellFormed afterCut :=
  Regions.step_wellFormed first_cut_retains_the_outer_bank nested_first_is_wellFormed

theorem full_drain_returns_only_the_first_packet :
    (advance program 4 nestedFirst).agenda = [] ∧
      values (advance program 4 nestedFirst) = [.expression [.symbol "a"]] := by constructor <;> rfl

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingRegionControls
