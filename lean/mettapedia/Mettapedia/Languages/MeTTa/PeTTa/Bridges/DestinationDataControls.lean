import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataEntry

/-!
# Constructor-region controls on the actual destination machine

The reference constructor runs its child work. A quoted-value lowering has
a different internal path but the same completed read in this fixture.
Equal fuel cutoffs are deliberately not identified. Deleting the skeleton
equation and treating exhausted work as completed are refuted separately.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open DestinationDataRecipe DestinationDataDebt DestinationDataCheckpoint

def num (value : Int) : Atom := .grounded (.int value)
def text (value : String) : Atom := .grounded (.string value)
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def held : Atom := call "+" [num 1, num 2]
def recipe : Atom := call "Cell" [.var "input", .symbol "Nil"]
def expected : Atom := call "Cell" [held, .symbol "Nil"]
def equation : SpaceSemantics.Equation := ⟨"rebuild", [recipe], recipe⟩
def program : SpaceSemantics.Program := {equations := [equation], declarations := []}
def destination : Atom := .var "result"
def older : List Goal := [.invoke "println!" [text "caller"] (.var "printed")]
def control : Control :=
  ⟨[(.var "input", held)], [.evaluate recipe destination] ++ older, destination, ∅, 0⟩
def initial : Cursor Unit := ⟨{state := Effects.loaded program, output := [num 7]}, control, ()⟩

theorem recipe_is_data : Recipe program recipe := by
  apply Recipe.named "Cell" [.var "input", .symbol "Nil"] rfl rfl (by decide) (by decide)
  intro child member
  rcases List.mem_cons.mp member with rfl | later
  · exact .variableValue _
  · cases List.mem_singleton.mp later
    exact .symbol _

def observe (fuel : Nat) (source : Cursor Unit) : Option (Atom × List Atom) :=
  match (regionMachine program older).run fuel source with
  | (_, .suspended (.inl ()) reached) =>
      (resolve reached.control.bindings).map fun environment =>
        (read environment reached.control.destination, reached.world.output)
  | _ => none

theorem held_field_is_not_re_evaluated : observe 7 initial = some (expected, [num 7]) := by cbv

theorem exhaustion_is_not_a_checkpoint : observe 6 initial = none := by cbv

theorem the_saved_caller_suffix_does_not_run : observe 500 initial = some (expected, [num 7]) := by cbv

def plainOutput (fuel : Nat) : Option (List Atom) :=
  match (EagerDFS.Destination.machine .eagerValue program).run fuel initial with
  | (_, .exhausted reached) => some reached.world.output
  | _ => none

theorem running_past_the_boundary_executes_the_caller :
    plainOutput 7 = some [num 7, text "caller"] := by cbv

def quoted : Cursor Unit :=
  {initial with control := {control with goals := [.evaluate (call "quote" [expected]) destination] ++ older}}

theorem a_shorter_lowering_has_the_same_completed_read : observe 3 quoted = observe 7 initial := by cbv

theorem equal_fuel_cutoffs_are_not_equivalent :
    observe 3 initial = none ∧ observe 3 quoted = some (expected, [num 7]) := by cbv

def omittedSkeleton : Cursor Unit :=
  {initial with control := {control with goals := (expansion program control recipe destination).dropLast ++ older}}

theorem omitting_the_skeleton_leaves_the_result_unbound :
    observe 5 omittedSkeleton = some (destination, [num 7]) := by cbv

theorem pending_data_is_not_an_already_proved_read :
    (resolve control.bindings).map (fun environment => read environment destination == read environment recipe) = some false := by cbv

theorem an_executable_child_is_not_a_data_recipe : ¬ Recipe program held := by
  intro data
  cases data with
  | named head arguments ordinary localForm inert surface children =>
      have interpreted : callable program "+" = true := by decide
      rw [interpreted] at inert
      cases inert
  | tuple children noHead parts => exact (noHead "+" [num 1, num 2] rfl).elim

theorem quotation_is_not_a_constructor_self_return : ¬ Recipe program (call "quote" [expected]) := by
  intro data
  cases data with
  | named head arguments ordinary localForm inert surface children => cases ordinary
  | tuple children noHead parts => exact (noHead "quote" [expected] rfl).elim

def clashing : Cursor Unit :=
  {initial with control := {control with bindings := control.bindings ++ [(destination, .symbol "Different")]}}

def refused (fuel : Nat) (source : Cursor Unit) : Bool :=
  match (regionMachine program older).run fuel source with
  | (_, .finished (.noValue _, _)) => true
  | _ => false

theorem an_actual_equation_clash_is_refusal_not_checkpoint :
    refused 20 clashing = true ∧ observe 20 clashing = none := by cbv

def callControl : Control :=
  {control with bindings := [], goals := [.invoke "rebuild" [expected] destination] ++ older}

def selected : Option Control := ClauseChoice.attempt callControl "rebuild" [expected] destination older 0 equation

theorem the_compound_pattern_is_selected_by_actual_source_matching : selected.isSome = true := by cbv

theorem the_freshened_constructor_body_reaches_the_checkpoint :
    selected.bind (fun next => observe 7 ⟨initial.world, next, ()⟩) = some (expected, [num 7]) := by cbv

/-- The actual matched compound formal, rather than a variable-only surrogate,
instantiates the source-earned return-alias theorem. -/
theorem the_selected_body_earns_its_alias (next : Control) (chosen : selected = some next)
    (fuel : Nat) (after : Cursor Unit)
    (reached : ((regionMachine program older).run fuel ⟨initial.world, next, ()⟩).2 = .suspended (.inl ()) after) :
    ScopedReturnLocal.AliasHolds expected after.control := by
  exact DestinationDataEntry.selected_checkpoint_alias program callControl "rebuild" [expected] destination older 0
    equation next 0 expected recipe initial.world () chosen rfl rfl rfl recipe_is_data fuel after reached
    "result" rfl rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataControls
