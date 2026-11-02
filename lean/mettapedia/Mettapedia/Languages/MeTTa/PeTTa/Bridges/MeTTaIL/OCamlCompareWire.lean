import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOrderExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading
import Mettapedia.Languages.OCaml.ComparisonLaws

/-! Structural comparison reuses the existing source value codecs. Its
runtime view continues exactly on an equal prefix and otherwise preserves
the first strict order, refusal or functional fault.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open OCamlOrderExecution

abbrev valueTerm (actual : OCaml.Value) : Term := InferenceCettaWire.encodePattern (value actual)
abbrev fieldsTerm (actual : List OCaml.Value) : Term := InferenceCettaWire.encodePattern (valueList actual)

theorem fields_nil : fieldsTerm [] = .application "PApp" [.string "MlValueNil", .symbol "LNil"] := by
  simp only [fieldsTerm, valueList, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

theorem fields_cons (head : OCaml.Value) (tail : List OCaml.Value) :
    fieldsTerm (head :: tail) = .application "PApp" [.string "MlValueCons", encodeList id [valueTerm head, fieldsTerm tail]] := by
  simp only [fieldsTerm, valueList, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]

theorem value_cons (head tail : OCaml.Value) : valueTerm (.cons head tail) =
    .application "PApp" [.string "MlCons", encodeList id [valueTerm head, valueTerm tail]] := by
  simp only [valueTerm, value, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]

theorem value_tuple (fields : List OCaml.Value) : valueTerm (.tuple fields) =
    .application "PApp" [.string "MlTuple", encodeList id [fieldsTerm fields]] := by
  simp only [valueTerm, value, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]

theorem value_variant (typeId constructor : Nat) (fields : List OCaml.Value) : valueTerm (.variant typeId constructor fields) =
    .application "PApp" [.string "MlVariant", encodeList id [InferenceCettaWire.encodePattern (tag typeId constructor), fieldsTerm fields]] := by
  simp only [valueTerm, value, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]

theorem variable_match (bindings : Subst) (name : String) (actual : Atom) :
    SpaceSemantics.matchValue bindings (.var name) actual =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) actual := by
  rw [SpaceSemantics.matchValue.eq_def]

theorem view_continues (first later : OCaml.Compared) : view (OCaml.continueCompared first later) =
    match view first with | .symbol "MlEqualOrder" => view later | other => other := by
  cases first with
  | error error => rfl
  | ok result =>
    cases result with
    | error error => rfl
    | ok order => cases order <;> rfl

macro "ml_compare_eval" "[" facts:term,* "]" "unfolding" "[" defs:term,* "]" : tactic =>
  `(tactic| metta_eval [$facts,*] with OCamlControllerSource.checked unfolding
    [OCamlCompareWire.variable_match, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
     Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList, $defs,*])

#print axioms variable_match
#print axioms view_continues

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire
