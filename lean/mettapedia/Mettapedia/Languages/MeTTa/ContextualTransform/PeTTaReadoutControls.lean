import Mettapedia.Languages.MeTTa.PeTTa.AnswerReadout
import Lean.Elab.Tactic.Cbv

/-!
# Open-answer observations and identity-preserving inverse transport

The controls distinguish shared and independent variables, joint and individual
observations, and executable identities from display labels. The retained-cell
example runs the actual source continuation after both transports.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaReadoutControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK
open Unifying

def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)

def shared : List Atom := [call "p" [.var "x"],call "q" [.var "x"]]
def independent : List Atom := [call "p" [.var "x"],call "q" [.var "y"]]

theorem same_printed_shape_can_hide_cross_answer_sharing :
    VariantReadout.each shared = VariantReadout.each independent ∧
      VariantReadout.joint shared ≠ VariantReadout.joint independent := by decide

theorem shared_positions_are_retained :
    VariantReadout.normalize (call "pair" [.var "x",.var "x"]) = call "pair" [.var "0",.var "0"] ∧
      VariantReadout.normalize (call "pair" [.var "x",.var "y"]) = call "pair" [.var "0",.var "1"] := by decide

theorem legal_decimal_source_names_need_no_reservation :
    VariantReadout.normalize (call "pair" [.var "0",.var "outside"]) =
      call "pair" [.var "0",.var "1"] ∧
      VariantReadout.restore (VariantReadout.pack [.var "0",.var "outside"]) = [.var "0",.var "outside"] := by
  exact ⟨by decide,VariantReadout.restore_pack _⟩

theorem raw_scoped_spelling_is_not_erased_to_its_base :
    ¬AtomRenaming.Variant (call "pair" [.var "x#0",.var "x#1"])
      (call "pair" [.var "x",.var "x"]) := by
  rw [← VariantReadout.normalize_equal_iff_variant]
  decide

def registry : SpaceSemantics.Program := {equations := [],declarations := []}
def stored : Atom := .var "v#0"
def world : Effects.State := Effects.empty.putCell "cell" stored

def waiting : Configuration :=
  {state := world,control := .returned [],uses := 2,
    frames := [.bind (.var "x#1") (call "==" [.var "x#1",call "get-state" [.symbol "cell"]])]}

def transported : Configuration := AnswerReadout.resume waiting (AnswerReadout.packAnswers [⟨stored,[]⟩])
def displayOnly : Configuration :=
  {waiting with control := .returned ((VariantReadout.joint [stored]).map fun value => ⟨value,[]⟩)}

theorem inverse_transport_retains_the_cell_alias :
    observed (run registry 100 transported) = .answers [Effects.boolean true] := by cbv

theorem display_labels_alone_lose_the_cell_alias :
    observed (run registry 100 displayOnly) = .answers [Effects.boolean false] := by cbv

def branchWaiting : Configuration :=
  {waiting with
    frames := [.bind (.var "result#1")
      (call "==" [.var "x#1",call "get-state" [.symbol "cell"]])]}

def branchAnswers : List Answer :=
  [⟨.symbol "token",[("x#1",stored)]⟩,
   ⟨.symbol "token",[("x#1",.var "other#0")]⟩]

def branchTransported : Configuration :=
  AnswerReadout.resume branchWaiting (AnswerReadout.packAnswers branchAnswers)

def branchBindingsErased : Configuration :=
  {branchWaiting with
    control := .returned (branchAnswers.map fun answer => ⟨answer.value,[]⟩)}

theorem identical_visible_values_can_retain_different_constraints :
    observed (run registry 100 branchTransported) =
      .answers [Effects.boolean true,Effects.boolean false] := by cbv

theorem dropping_latent_bindings_changes_the_continuation :
    observed (run registry 100 branchBindingsErased) =
      .answers [Effects.boolean false,Effects.boolean false] := by cbv

theorem printed_and_returned_sharing_is_joint :
    AnswerReadout.displayedOutput
        (AnswerReadout.completed Effects.empty [.var "kept"] [] [.var "kept"]) = [.var "0"] ∧
      AnswerReadout.displayedAnswers
        (AnswerReadout.completed Effects.empty [.var "kept"] [] [.var "kept"]) = [.var "0"] := by decide

def copiedAlternatives : Atom :=
  call "let" [.expression [.var "a",.var "b"],
    call "collapse" [call "superpose" [.expression [.var "x",.var "x"]]],
    call "==" [.var "a",.var "b"]]

theorem actual_collection_isolates_answer_variables :
    observed (run registry 100 (ScopedSource.enter 0 [] Effects.empty copiedAlternatives)) =
      .answers [Effects.boolean false] := by cbv

def copiedPair : Atom :=
  call "let" [.expression [call "pair" [.var "a",.var "b"]],
    call "collapse" [call "quote" [call "pair" [.var "x",.var "x"]]],
    call "==" [.var "a",.var "b"]]

theorem actual_collection_keeps_internal_aliases :
    observed (run registry 100 (ScopedSource.enter 0 [] Effects.empty copiedPair)) =
      .answers [Effects.boolean true] := by cbv

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaReadoutControls
