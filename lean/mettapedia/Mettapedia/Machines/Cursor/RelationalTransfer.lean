import Mettapedia.Machines.Cursor.Relational
import Mettapedia.Machines.Cursor.Transfer
import Mettapedia.Machines.Cursor.Controls

/-!
# Representation transfer without a canonical state decoder

An optimizer can propose a replacement for the current residual at any
request boundary. Successful proposals must preserve the relation to every
currently related reference state; refusal retains the existing residual.
Local protocol bisimulation then lifts this condition to every bounded client,
including a client that adapts to replies or stops early.

The relation need not be a function into one distinguished store. Existing
functional transfer is recovered as the graph-relation special case. A
specializer can supply proposals, but producing them and proving their local
law is separate work. These theorems do not manufacture a supercompiler,
guarantee profitable switching, or authorize changing the current profile.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {source target : Provider P}

/-- A successful migration preserves all views that currently relate the
residual states. This is a local state law, not an assumed client equivalence. -/
def RelationalSoundOffer (rel : StateRel source target) (offer : Offer source) : Prop :=
  ∀ {base index} (left next : source.State base index)
    (right : target.State base index) (request : P.Shape base index),
    rel left right → offer left request = some next → rel next right

theorem choose_preserves_relation (rel : StateRel source target)
    (offer : Offer source) (sound : RelationalSoundOffer rel offer)
    {base : Base} {index : Index base} (left : source.State base index)
    (right : target.State base index) (request : P.Shape base index)
    (related : rel left right) : rel (choose offer left request) right := by
  cases offered : offer left request with
  | none => simpa [choose, offered] using related
  | some next =>
      simpa [choose, offered] using (sound left next right request related offered)

/-- Migration followed by a request is bisimilar to the reference request.
Neither the current client nor the provider is restarted. -/
theorem switching_bisimulation (rel : StateRel source target)
    (localLaw : Bisimulation rel) (offer : Offer source)
    (sound : RelationalSoundOffer rel offer) :
    Bisimulation (source := switchingProvider source offer) (target := target) rel := by
  intro base index left right related request
  exact localLaw (choose offer left request) right
    (choose_preserves_relation rel offer sound left right request related) request

/-- Arbitrarily many accepted or refused migration proposals preserve the
complete bounded interaction. Costs may differ and require separate evidence. -/
theorem switching_advance_related
    {Return : (base : Base) → Index base → Type u}
    (client : Client (P := P) (Return := Return))
    (rel : StateRel source target) (localLaw : Bisimulation rel)
    (offer : Offer source) (sound : RelationalSoundOffer rel offer)
    (leftCost : Charge (switchingProvider source offer)) (rightCost : Charge target)
    (budget : Nat) {base : Base}
    {left : Packet (switchingProvider source offer) client base}
    {right : Packet target client base}
    (related : PacketRel (source := switchingProvider source offer) (target := target)
      client rel left right) :
    OutcomeRel (source := switchingProvider source offer) (target := target) client rel
      (advance (switchingProvider source offer) client leftCost budget left).2
      (advance target client rightCost budget right).2 :=
  advance_related (source := switchingProvider source offer) (target := target)
    client rel (switching_bisimulation rel localLaw offer sound)
    leftCost rightCost budget related

/-- A functional state map is recovered by theorem; the generic contract
does not require selecting such a map from a possibly many-valued relation. -/
theorem relationalSoundOffer_graph_iff (decode : Hom source target)
    (offer : Offer source) :
    RelationalSoundOffer (fun left right => decode.map left = right) offer ↔
      SoundOffer decode offer := by
  constructor
  · intro sound base index left next request offered
    exact sound left next (decode.map left) request rfl offered
  · intro sound base index left next right request related offered
    exact (sound left next request offered).trans related

namespace RelationalTransferControls

open Sequence Controls

/-- A real tail-list to array-slice proposal satisfies the relational law. -/
theorem promotion_is_relationally_sound :
    RelationalSoundOffer
      (fun left right =>
        (familyHom representations (tails Nat) representationHom).map left = right)
      promote :=
  (relationalSoundOffer_graph_iff _ promote).mpr promote_sound

/-- Resetting to the original sequence after consuming its first answer is
rejected; duplicate/replayed answers cannot be hidden by changing the store. -/
theorem replay_is_not_relationally_sound :
    ¬ RelationalSoundOffer (source := tails Nat) (target := tails Nat)
      (fun left right => left = right) replayOffer := by
  intro sound
  have wrong := sound (base := ()) (index := ()) [8, 9] [7, 8, 9] [8, 9] () rfl rfl
  change [7, 8, 9] = [8, 9] at wrong
  have heads := congrArg List.head? wrong
  contradiction

end RelationalTransferControls

end Mettapedia.Machines.Cursor
