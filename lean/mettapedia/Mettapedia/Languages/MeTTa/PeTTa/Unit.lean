import Mettapedia.Conformance.SimplePeTTa
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# PeTTa Unit Suite (69 Cases)

This file provides a compact but broad PeTTa unit suite:
- 53 runtime/spec checks reused from `Mettapedia.Conformance.SimplePeTTa`
- 16 additional small atomspace/matching checks (positive + negative)

Source attribution:
- Baseline fixture structure is adapted from `Mettapedia/Conformance/SimplePeTTa.lean`.
- Extra matching shapes are inspired by tiny patterns in:
  - `hyperon/PeTTa/examples/matchnested.metta`
  - `hyperon/PeTTa/examples/collapse.metta`
  - `hyperon/PeTTa/examples/cut.metta`
  - `hyperon/PeTTa/examples/he_math.metta`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.Unit

open Mettapedia.OSLF.MeTTaIL.Syntax

abbrev UnitCase := String × Bool

private def sym (s : String) : Pattern := .apply s []
private def app (f : String) (args : List Pattern) : Pattern := .apply f args

def baselineCases : List UnitCase :=
  Mettapedia.Conformance.SimplePeTTa.allChecks

private def rwFToB : RewriteRule :=
  { name := "f_to_b"
    typeContext := []
    premises := []
    left := app "f" [sym "a"]
    right := sym "b" }

private def sEmpty : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace := .empty

private def sColors : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace :=
  { facts := [app "color" [sym "red"], app "color" [sym "blue"]]
    rules := [] }

private def sFriends : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace :=
  { facts := [app "friend" [sym "tim", sym "tom"], app "friend" [sym "tim", sym "bob"]]
    rules := [] }

private def sFriendsShared : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace :=
  { facts :=
      [ app "friend" [sym "tim", sym "tom"]
      , app "friend" [sym "tim", sym "bob"]
      , app "friend" [sym "bob", sym "bob"]
      ]
    rules := [] }

private def sConj : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace :=
  { facts := [app "friend" [sym "tim", sym "tom"], app "friend" [sym "tom", sym "tam"]]
    rules := [] }

private def sDup : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace :=
  { facts := [sym "a", sym "a", sym "b"]
    rules := [] }

def extraCases : List UnitCase :=
  [ ("space_empty_facts", decide (sEmpty.facts = []))
  , ("space_empty_rules", decide (sEmpty.rules = []))
  , ("addAtom_prepends", decide ((sColors.addAtom (sym "green")).facts =
      sym "green" :: sColors.facts))
  , ("addRule_prepends_name",
      decide ((sEmpty.addRule rwFToB).rules.head?.map (fun r => r.name) = some "f_to_b"))
  , ("removeAtom_drops_all_duplicates", decide ((sDup.removeAtom (sym "a")).facts = [sym "b"]))
  , ("removeAtom_preserves_non_target", decide (sym "b" ∈ (sDup.removeAtom (sym "a")).facts))
  , ("spaceMatch_empty", decide (sEmpty.spaceMatch (sym "x") (sym "y") = []))
  , ("spaceMatch_exact_hit", decide (sColors.spaceMatch (app "color" [sym "red"]) (sym "hit") =
      [sym "hit"]))
  , ("spaceMatch_exact_miss", decide (sColors.spaceMatch (app "color" [sym "green"]) (sym "hit") =
      []))
  , ("spaceMatch_var_projection", decide (sColors.spaceMatch
      (app "color" [.fvar "x"]) (.fvar "x") = [sym "red", sym "blue"]))
  , ("spaceMatch_template_instantiation", decide (sColors.spaceMatch
      (app "color" [.fvar "x"]) (app "picked" [.fvar "x"]) =
      [app "picked" [sym "red"], app "picked" [sym "blue"]]))
  , ("spaceMatch_shared_var_miss", decide (sFriends.spaceMatch
      (app "friend" [.fvar "x", .fvar "x"]) (app "diag" [.fvar "x"]) = []))
  , ("spaceMatch_shared_var_hit", decide (sFriendsShared.spaceMatch
      (app "friend" [.fvar "x", .fvar "x"]) (app "diag" [.fvar "x"]) =
      [app "diag" [sym "bob"]]))
  , ("spaceMatch_template_share", decide (sFriends.spaceMatch
      (app "friend" [sym "tim", .fvar "b"]) (app "pair" [.fvar "b", .fvar "b"]) =
      [app "pair" [sym "tom", sym "tom"], app "pair" [sym "bob", sym "bob"]]))
  , ("spaceMatch_binary_projection", decide (sConj.spaceMatch
      (app "friend" [sym "tim", .fvar "x"]) (.fvar "x") = [sym "tom"]))
  , ("spaceMatch_addAtom_extends",
      let pat := app "color" [.fvar "x"]
      let tmpl := .fvar "x"
      let before := sColors.spaceMatch pat tmpl
      let after := (sColors.addAtom (app "color" [sym "green"])).spaceMatch pat tmpl
      decide (before.all (fun q => q ∈ after) && sym "green" ∈ after))
  ]

def unitCases : List UnitCase :=
  baselineCases ++ extraCases

def unitCaseCount : Nat :=
  unitCases.length

def unitAllPass : Bool :=
  unitCases.all (fun c => c.2)

def unitFailingCases : List String :=
  unitCases.filterMap fun c => if c.2 then none else some c.1

#eval ("petta_unit_case_count", unitCaseCount)
#eval ("petta_unit_all_pass", unitAllPass)
#eval ("petta_unit_failing_cases", unitFailingCases)
#eval unitCases

end Mettapedia.Languages.MeTTa.PeTTa.Unit
