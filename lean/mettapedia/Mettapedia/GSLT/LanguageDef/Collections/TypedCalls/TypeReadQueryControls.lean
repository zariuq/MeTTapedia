import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryServices
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRows

/-!
# A retained closure hit followed by a genuinely fresh read

The cold service executes the actual closure primitive; the warm service
reuses its previously computed immutable-ground reply and leaves the supply
unchanged. Both then execute the actual open annotation read. Their raw
fresh names differ, but one final coordinate world relates the whole trace.
The allocation counters here belong to the model, not a native cost claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQueryDemand
open Mettapedia.Machines.ReadOnlyQueryWorldRelation
open TypeReadQueryWorlds
open TypeReadSupply (Supply)
open NativeTypeCallGraph (Reply)

def external : RetainedTypePayloads.ExternalView := fun tag key => .grounded (.custom tag key)
def source : NativeTypeSourcePorts.Source where
  rows := [.expression [.symbol ":", .symbol "K", .expression [.symbol "Pair", .var "element", .var "element"]],
    .expression [.symbol ":<", .symbol "A", .symbol "Number"]]
  intrinsicRows := []
  rename := fun _ _ name => name
  subtypeBudget := 2
  subtypeFresh := "out"
  alpha := TypeAlphaComparison.check

def family : List Atom := [.symbol "A", .symbol "Number"]
def initial : Supply := ⟨["caller", "alias"], 0⟩

def cold (supply : Supply) (key : Bool) : Option Reply × Supply :=
  NativeTypeScopedReads.primitive source external supply
    (if key then .annotations (.symbol "K") else .closure [.symbol "A"])

def cached : Option Reply := (cold initial false).1

def warm (supply : Supply) (key : Bool) : Option Reply × Supply :=
  if key then cold supply key else
    match cached with
    | some (.types types) =>
        if RetainedTypePayloads.admittedList types then (some (.types types), supply) else cold supply key
    | _ => cold supply key

theorem cached_is_actual_closed_reply : cached = some (.types family) := by cbv
theorem cached_family_admitted : RetainedTypePayloads.admittedList family = true := by decide
theorem source_safe : NativeTypeSourcePorts.Safe source := by unfold NativeTypeSourcePorts.Safe; decide

theorem cold_closed_reply (supply : Supply) : (cold supply false).1 = some (.types family) :=
  NativeTypeClosureReadWorlds.retained_closure_equal source external
    (ScopedSubtypeReadSafety.rowsSafe_of_resourceFree source.rows source_safe.1)
    TypeAlphaComparison.equivariant [.symbol "A"] (by decide) initial supply family
    cached_is_actual_closed_reply cached_family_admitted

theorem warm_hit (supply : Supply) : warm supply false = (some (.types family), supply) := by
  simp [warm, cached_is_actual_closed_reply, cached_family_admitted]

def controlWorlds : Worlds Coordinates Bool Reply where
  grows := Grows
  grows_refl := grows_refl
  grows_trans := grows_trans
  keys _ first second := first = second
  replies := RepliesRelated
  keys_mono := fun {_ _} _ {_ _} same => same
  replies_mono := replies_mono

theorem services_related : ServicesRelated controlWorlds Protected cold warm := by
  intro world first second supplies firstKey secondKey keys
  change firstKey = secondKey at keys
  subst secondKey
  cases firstKey with
  | true =>
      simpa only [cold, warm, if_true, controlWorlds] using
        TypeReadQueryServices.annotation source external source_safe world first second supplies (.symbol "K")
          ⟨by simp [atomVariables], by simp [atomVariables]⟩
  | false =>
      refine ⟨world, grows_refl world, ⟨?_, ?_⟩, ?_⟩
      · intro name member
        exact NativeTypeScopedReads.primitive_remembers source external first (.closure [.symbol "A"])
          (supplies.1 member)
      · simpa only [warm_hit] using supplies.2
      · rw [cold_closed_reply, warm_hit]
        exact .some (.types ⟨by decide, by simp [family, atomListVariables, atomVariables], rfl⟩)

def probe : Program Bool Reply (Reply × Reply) :=
  .read false fun first => .read true fun second => .pure (first, second)

def PairRelated (world : Coordinates) (first second : Reply × Reply) : Prop :=
  RepliesRelated world first.1 second.1 ∧ RepliesRelated world first.2 second.2

theorem probe_related (world : Coordinates) : Related controlWorlds PairRelated world probe probe := by
  refine .read rfl ?_
  intro middle _ first second replies
  refine .read rfl ?_
  intro last extended left right later
  exact .pure ⟨replies_mono extended replies, later⟩

def startingWorld : Coordinates := ⟨Equiv.refl String, ["caller", "alias"]⟩

theorem warm_hit_preserves_following_fresh_read :
    let left := Mettapedia.Machines.QueryState.run cold (Mettapedia.Machines.ReadOnlyQueryDemand.demand probe) initial
    let right := Mettapedia.Machines.QueryState.run warm (Mettapedia.Machines.ReadOnlyQueryDemand.demand probe) initial
    ∃ last, Grows startingWorld last ∧ Protected last left.state right.state ∧
      Option.Rel (PairRelated last) left.answer right.answer ∧
      List.Forall₂ (EventRelated controlWorlds last) left.reads right.reads :=
  demand_run_related controlWorlds PairRelated Protected cold warm services_related
    (probe_related startingWorld) initial initial ⟨by simp [startingWorld, initial], by simp [startingWorld, initial]⟩

theorem raw_reply_equality_is_too_strong :
    (Mettapedia.Machines.QueryState.run cold (Mettapedia.Machines.ReadOnlyQueryDemand.demand probe) initial).answer ≠
      (Mettapedia.Machines.QueryState.run warm (Mettapedia.Machines.ReadOnlyQueryDemand.demand probe) initial).answer := by
  cbv
  simp

theorem a_hit_really_skips_private_work :
    (Mettapedia.Machines.QueryState.run warm (Mettapedia.Machines.ReadOnlyQueryDemand.demand probe) initial).state.next <
      (Mettapedia.Machines.QueryState.run cold (Mettapedia.Machines.ReadOnlyQueryDemand.demand probe) initial).state.next := by cbv

theorem open_annotation_is_not_a_literal_cache_payload :
    match (cold initial true).1 with
    | some (.types types) => RetainedTypePayloads.admittedList types = false
    | _ => False := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryControls
