import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiStore
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls

/-!
# Controls: π's store and its communication index

π's modal decider on the store (`PiStore.decider`), whose successors come from the communication index when every
replicated component copies one component, and from the front door's presentations otherwise:

- **A server serves once and stays** (`serving_by_store`), the forwarder steps back to itself
  (`forwarder_by_store`), and `!(x⟨w⟩ | x(y).0)` steps back to itself (`replicated_pair_by_store`).
- **Beside `x⟨w⟩` an input on `x` steps** (`receiver_beside_sender_by_store`), and a private server does not
  (`private_server_stuck_by_store`, negative).
- **A replicated component whose copies carry a restriction** (`!(νa) x⟨a⟩`) is not a generator of single copies;
  the store lists the front door's successors there, and a receiver still takes the private name
  (`restricted_copies_by_store`).
- **Fewer successors, the same answers**: the index lists one successor where the front door lists three for the
  server and the forwarder, and two for the replicated pair (`index_lists_fewer`); the two deciders agree on these
  questions (`deciders_agree`).
- **A refutation over every successor**: three servers and five clients never reach inaction within three steps
  (`busy_never_inaction`); the index pairs only the inputs and outputs on one channel, so every successor of every
  state is listed once.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiStoreControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiStore
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartners (frontDoor partnerLabel listed)
open PiControls (input output zero replicate server restrict)
open PiPrenexControls (x w serving forwarder pair privateServer)

/-- The partner `□` beside a process. -/
abbrev beside (partner : Pattern) : StepLabel := partnerLabel "hole" partner

/-- **A server serves once and stays**, by the store. -/
theorem serving_by_store : frontDoor.sat Env.closed (.possibly .any (.is (server x zero))) serving :=
  decided_holds (by decide +kernel)

/-- **The forwarder steps back to itself**, by the store. -/
theorem forwarder_by_store : frontDoor.sat Env.closed (.possibly .any (.is forwarder)) forwarder :=
  decided_holds (by decide +kernel)

/-- **`!(x⟨w⟩ | x(y).0)` steps back to itself**, by the store. -/
theorem replicated_pair_by_store : frontDoor.sat Env.closed (.possibly .any (.is (replicate pair))) (replicate pair) :=
  decided_holds (by decide +kernel)

/-- **Beside an output on `x` an input on `x` steps**, by the store. -/
theorem receiver_beside_sender_by_store :
    frontDoor.sat Env.closed (.possibly (beside (output x w)) .top) (input x zero) :=
  decided_holds (by decide +kernel)

/-- **A private server stays private**, by the store. -/
theorem private_server_stuck_by_store : ¬ frontDoor.sat Env.closed (.possibly .any .top) privateServer :=
  decided_fails (by decide +kernel)

/-- `!(νa) x⟨a⟩ | x(z).z⟨w⟩`: a replicated output of a private name beside a receiver. -/
def restrictedCopies : Pattern := .collection .hashBag
  [replicate (restrict (output x (.bvar 0))), input x (output (.bvar 0) w)] none

/-- **Copies with a restriction**: the store lists the front door's successors, and the receiver takes the private
name, which it then uses under the restriction. -/
theorem restricted_copies_by_store :
    frontDoor.sat Env.closed (.possibly .any .top) restrictedCopies ∧
      (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.flatServers
        Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks.piRepBlock
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonP
          Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks.piRepBlock restrictedCopies)) = false :=
  ⟨decided_holds (by decide +kernel), by decide +kernel⟩

/-- **The index lists fewer successors than the front door's presentations.** -/
theorem index_lists_fewer :
    (storeSuccessors serving).length = 1 ∧ (listed serving).length = 3 ∧
      (storeSuccessors forwarder).length = 1 ∧ (listed forwarder).length = 3 ∧
      (storeSuccessors (replicate pair)).length = 1 ∧ (listed (replicate pair)).length = 2 := by
  decide +kernel

/-- **The store's decider and the front door's agree** on these questions. -/
theorem deciders_agree :
    decider.decide (.possibly .any (.is forwarder)) forwarder =
        PiPartners.decider.decide (.possibly .any (.is forwarder)) forwarder ∧
      decider.decide (.possibly .any (.is (server x zero))) serving =
        PiPartners.decider.decide (.possibly .any (.is (server x zero))) serving ∧
      decider.decide (.possibly .any .top) privateServer = PiPartners.decider.decide (.possibly .any .top) privateServer := by
  decide +kernel

def z : Pattern := .fvar "z"
def v : Pattern := .fvar "v"

/-- `!x(y).0 | !z(y).0 | !v(y).0 | x⟨w⟩ | z⟨w⟩ | v⟨w⟩ | x⟨w⟩ | z⟨w⟩`. -/
def busy : Pattern := .collection .hashBag
  [server x zero, server z zero, server v zero, output x w, output z w, output v w, output x w, output z w] none

/-- **Three servers and five clients never reach inaction within three steps**: the servers stay. -/
theorem busy_never_inaction :
    ¬ frontDoor.sat Env.closed (.possibly .any (.possibly .any (.possibly .any (.is zero)))) busy :=
  decided_fails (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiStoreControls
