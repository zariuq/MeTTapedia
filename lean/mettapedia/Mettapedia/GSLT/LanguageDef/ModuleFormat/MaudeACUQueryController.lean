import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagQuery
import Mettapedia.Machines.ResumableSearchFilter
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner

/-! The ACU query controller specializes the shared resumable filter.
Source substitutions have their own semantic readout. Here a single total
tick advances one candidate machine and retains the remaining candidates,
collected answers and complete current search across suspension.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagQuery.Controller

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines ResumableSearchRunner
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire

def search (spec : CompleteEmission.Spec) :=
  Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode

def request (source : Pattern) : Pattern := .apply requestName [source]

def read (wrapper : String) : Pattern → ResumableSearchFilter.Decision Pattern String
  | .apply label [.collection .hashBag parts none] =>
    if label = resultName then .accept (.apply wrapper [.collection .hashBag parts none])
    else .fault "UnexpectedResult"
  | .apply label [.apply _ _] =>
    if label = requestName then .reject else .fault "UnexpectedResult"
  | _ => .fault "UnexpectedResult"

abbrev ModelState (spec : CompleteEmission.Spec) := ResumableSearchFilter.State
  Pattern Pattern (Complete.Classes.State spec.plan) GeneralOccurrenceSemantics.Receipt Pattern String

def begin (spec : CompleteEmission.Spec) (sources : List Pattern) (answers : List Pattern := []) : ModelState spec :=
  ResumableSearchFilter.begin (search spec) request sources answers

def step (spec : CompleteEmission.Spec) (wrapper : String) (quantum : Nat) : ModelState spec → ModelState spec :=
  ResumableSearchFilter.step (search spec) request (read wrapper) quantum

def advance (spec : CompleteEmission.Spec) (wrapper : String) (ticks quantum : Nat)
    (state : ModelState spec) : ModelState spec :=
  ResumableSearchFilter.advance (search spec) request (read wrapper) ticks quantum state

theorem advance_add (spec : CompleteEmission.Spec) (wrapper : String) (first extra quantum : Nat)
    (state : ModelState spec) :
    advance spec wrapper (first + extra) quantum state =
      advance spec wrapper extra quantum (advance spec wrapper first quantum state) :=
  ResumableSearchFilter.advance_add (search spec) request (read wrapper) first extra quantum state

theorem advance_retains_answers (spec : CompleteEmission.Spec) (wrapper : String) (ticks quantum : Nat)
    (state : ModelState spec) :
    state.answers <:+ (advance spec wrapper ticks quantum state).answers :=
  ResumableSearchFilter.advance_retains_answers (search spec) request (read wrapper) ticks quantum state

def stateTerm (spec : CompleteEmission.Spec) : ModelState spec → CettaWire.Term
  | .done answers => .application "MaudeQueryDone" [encodeList InferenceCettaWire.encodePattern answers]
  | .active remaining answers machine => .application "MaudeQueryActive"
    [encodeList InferenceCettaWire.encodePattern remaining, encodeList InferenceCettaWire.encodePattern answers,
      CompleteExecution.classMachineTerm spec.plan machine]
  | .failed error remaining answers machine => .application "MaudeQueryFault"
    [.string error, encodeList InferenceCettaWire.encodePattern remaining,
      encodeList InferenceCettaWire.encodePattern answers, CompleteExecution.classMachineTerm spec.plan machine]

#print axioms advance_add
#print axioms advance_retains_answers

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagQuery.Controller
