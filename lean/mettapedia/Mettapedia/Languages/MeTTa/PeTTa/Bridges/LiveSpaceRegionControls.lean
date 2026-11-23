import Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveCountRegion
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation

/-! Source controls for changes to the theory of an ordinary PeTTa space. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveSpaceRegionControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands
open ProgramQuotation Eval ProgramReplay

private def selfSource : QuotedProgram :=
  petta_source% "!(let* (($before (probe 2)) ($added (add-atom &self (= (probe 2) Fresh))) ($during (probe 2)) ($row (collapse (match &self (= (probe 2) $rhs) $rhs))) ($removed (remove-atom &self (= (probe 2) Fresh)))) (Observed $before $during $row (probe 2)))"
    sha256 "ce483fc85442633cb3aabb910f3c53e150d595fe395356136b96c4437a26a057"

private def namedSource : QuotedProgram :=
  petta_source% "(= (which) SelfValue)\n!(let $installed (add-atom alpha (= (which) Alpha)) (which))"
    sha256 "59de54a0756e49867fd65916ed7a70c9c88ad88b2a959f677c1eaefe5f8ce1aa"

private def countSource : QuotedProgram :=
  petta_source% "(Item a)\n(Item a)\n(Item b)\n(Other a)\n!(let $installed (add-atom &self (= (count-items) (size-atom (collapse (match &self (Item $x) seen))))) (+ 10 (count-items)))"
    sha256 "0129b682ec197feab0da490cc834500a37b41bcb0e35aad47babc6bc55a8f2ff"

private def expression (head : String) (arguments : List Atom := []) : Atom :=
  .expression (.symbol head :: arguments)

private def equation (head : String) (body : Atom) : Atom :=
  expression "=" [expression head, body]

private def probe : Atom := expression "probe" [.grounded (.int 2)]

private def reread : Configuration :=
  LiveRegistry.advance 180 (Eval.start (Effects.loaded selfSource.program) selfSource.program.initializers[0])

/-- A definition acquired during a request changes the next call, and withdrawal
restores data evaluation. Raw match can inspect the active definition. -/
theorem install_read_and_withdraw :
    reread.control = .returned
      [expression "Observed" [probe, .symbol "Fresh", .expression [.symbol "Fresh"], probe]] ∧
    reread.frames = [] ∧ reread.state.core = [] := by
  decide +kernel

private def alpha : NamedSpaces.Handle := .namedSpace ⟨"alpha", by decide⟩
private def beta : NamedSpaces.Handle := .namedSpace ⟨"beta", by decide⟩
private def namedStore : Effects.State :=
  { Effects.loaded namedSource.program with
    namedSpaces := [("beta", [equation "which" (.symbol "Beta")])] }

private def evaluateIn (handle : NamedSpaces.Handle) (state : Effects.State) (term : Atom) :
    Controller.Session :=
  Controller.advance {} 100
    { world := { packet := ProgramReplay.snapshot [] (Eval.start state term), current := handle, fuel := 100 } }

private def installed : Controller.Session :=
  evaluateIn alpha namedStore namedSource.program.initializers[0]

theorem named_space_edit_and_dispatch :
    installed.world.packet.control = .returned [.symbol "Alpha"] ∧
    installed.world.packet.frames = [] ∧
    (evaluateIn beta installed.world.packet.decode.state (expression "which")).world.packet.control =
      .returned [.symbol "Beta"] ∧
    (evaluateIn .self installed.world.packet.decode.state (expression "which")).world.packet.control =
      .returned [.symbol "SelfValue"] := by
  decide +kernel

private def startingCount : Configuration :=
  { Eval.start (Effects.loaded countSource.program) countSource.program.initializers[0] with
    input := [.symbol "retained-input"], output := [.symbol "retained-output"] }

private def findsRegion : Nat → Configuration → Bool
  | 0, _ => false
  | fuel + 1, configuration =>
    if (LiveCountRegion.prepare configuration).isSome then true
    else
      match LiveRegistry.step configuration with
      | none => false
      | some next => findsRegion fuel next

theorem installed_count_is_admitted : findsRegion 90 startingCount = true := by decide +kernel

private def afterCount := LiveCountRegion.advance 100 startingCount

/-- The just-installed count sees both occurrences of Item a, returns to
the already pending addition and retains the caller's I/O. -/
theorem counted_result_and_caller :
    afterCount.control = .returned [.grounded (.int 13)] ∧ afterCount.frames = [] ∧
    afterCount.input = startingCount.input ∧ afterCount.output = startingCount.output ∧
    afterCount.state.core.length = startingCount.state.core.length + 1 := by
  decide +kernel

private def countBody : Atom :=
  expression "size-atom" [expression "collapse"
    [expression "match" [.symbol "&self", expression "Item" [.var "x"], .symbol "seen"]]]

private def ready (bodies : List Atom) : Configuration :=
  { state := NamedSpaces.Store.new (bodies.map (equation "count-items")) []
    control := .arguments [] (.function "count-items") [] [] 0 }

theorem duplicate_definition_declines :
    (LiveCountRegion.prepare (ready [countBody, countBody])).isNone = true := by decide +kernel

private def printingBody : Atom :=
  expression "size-atom" [expression "collapse"
    [expression "match" [.symbol "&self", expression "Item" [.var "x"], expression "println!" [.var "x"]]]]

theorem effectful_template_declines :
    (LiveCountRegion.prepare (ready [printingBody])).isNone = true := by decide +kernel

theorem refused_region_preserves_printing :
    let entered := ready [printingBody]
    let withItem := {entered with state :=
      {entered.state with core := entered.state.core ++ [expression "Item" [.symbol "a"]]}}
    let after := LiveCountRegion.advance 80 withItem
    after.control = .returned [.grounded (.int 1)] ∧ after.output = [.symbol "a"] := by
  decide +kernel

#print axioms install_read_and_withdraw
#print axioms named_space_edit_and_dispatch
#print axioms installed_count_is_admitted
#print axioms counted_result_and_caller
#print axioms duplicate_definition_declines
#print axioms effectful_template_declines
#print axioms refused_region_preserves_printing

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveSpaceRegionControls
