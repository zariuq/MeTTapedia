import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopBranch

/-! Reached caller-frame facts between the authored EU loop's source phases.
These records state readings and freshness, not execution success. Each
source-phase theorem constructs its next record from its actual predecessor. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopFrames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor)
open FlatQueryRowCodec (Codec)
open CTLUntilSourceRows (number)
open CTLUntilLoopSource (Names)

variable {Label : Type}

structure IncrementFrame (codec : Codec Label) (label holds : Label) (round : Nat)
    (names : Names) (caller : Control) where
  principal : Environment
  resolved : resolve caller.bindings = some principal
  formula : read principal (.var names.formula) = codec.encode label
  operand : read principal (.var names.operand) = codec.encode holds
  current : read principal (.var names.current) = number round
  next : read principal (.var names.next) = number (round + 1)
  fresh : ∀ name ∈ [names.count, names.dropped, names.result], FreshFor name caller.bindings

structure RoundFrame (codec : Codec Label) (label holds : Label) (round count : Nat)
    (names : Names) (caller : Control) where
  principal : Environment
  resolved : resolve caller.bindings = some principal
  formula : read principal (.var names.formula) = codec.encode label
  operand : read principal (.var names.operand) = codec.encode holds
  current : read principal (.var names.current) = number round
  next : read principal (.var names.next) = number (round + 1)
  count : read principal (.var names.count) = number count
  fresh : ∀ name ∈ [names.dropped, names.result], FreshFor name caller.bindings

def branchNames (names : Names) : CTLUntilLoopBranch.Names :=
  ⟨names.formula, names.operand, names.next, names.count, names.result⟩

abbrev BranchFrame (codec : Codec Label) (label holds : Label) (round count : Nat)
    (names : Names) (caller : Control) :=
  CTLUntilLoopBranch.Frame codec label holds (round + 1) count (branchNames names) caller

theorem branch_source (names : Names) :
    CTLUntilLoopBranch.source (branchNames names) = CTLUntilLoopSource.branch names := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopFrames
