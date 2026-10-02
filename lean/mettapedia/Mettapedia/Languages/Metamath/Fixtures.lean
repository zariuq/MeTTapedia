import Mettapedia.Languages.Metamath.GroundedSemantics
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-!
# Metamath Fixture-Driven Parity Checks

Small parser/checker fixtures that pin expected behavior at the grounded
`mm-lean4` boundary.
-/

namespace Mettapedia.Languages.Metamath.Fixtures

open Mettapedia.Languages.Metamath.GroundedSemantics

def emptyBytes : ByteArray := "".toUTF8

def minimalAxiomBytes : ByteArray :=
  "$c wff $. $v ph $. wph $f wff ph $. ax1 $a wff ph $.".toUTF8

def brokenIncludeBytes : ByteArray := "$[ bad.mm ".toUTF8

def brokenConstBytes : ByteArray := "$c wff ".toUTF8

attribute [local cbv_opaque] Std.HashMap.insert Std.HashSet.insert
  Std.HashMap.toList Std.HashSet.toList
attribute [local cbv_eval] Metamath.Verify.ParserState.feed.eq_def
attribute [local cbv_eval] Std.HashSet.forIn_eq_forIn_toList
attribute [local cbv_eval] Std.HashMap.toList_emptyWithCapacity
  Std.HashSet.toList_emptyWithCapacity

/-- Entry-wise tests of a registry insertion do not depend on bucket order. -/
@[local cbv_eval] theorem hashMap_insert_toList_all
    (objects : Std.HashMap String Metamath.Verify.Object) (key : String)
    (value : Metamath.Verify.Object) (predicate : String × Metamath.Verify.Object → Bool) :
    (objects.insert key value).toList.all predicate =
      (predicate (key, value) && objects.toList.all
        (fun entry => !(decide (¬(key == entry.1))) || predicate entry)) := by
  have hperm := Std.HashMap.toList_insert_perm
    (m := objects) (k := key) (v := value)
  simpa only [List.all_cons, List.all_filter] using
    hperm.all_eq (f := predicate)

/-- A singleton variable set has the same one-entry enumeration at every capacity. -/
@[local cbv_eval] theorem singletonHashSet_toList (capacity : Nat)
    (value : String) :
    ((Std.HashSet.emptyWithCapacity capacity : Std.HashSet String).insert value).toList =
      [value] := by
  have hperm := Std.HashSet.toList_insert_perm
    (m := (Std.HashSet.emptyWithCapacity capacity : Std.HashSet String))
    (k := value)
  have hperm' :
      ((Std.HashSet.emptyWithCapacity capacity : Std.HashSet String).insert value).toList.Perm
        [value] := by
    simpa using hperm
  exact hperm'.eq_singleton

def minimalAxiomFormula : Metamath.Verify.Formula := #[.const "wff", .var "ph"]

def minimalAxiomFrame : Metamath.Verify.Frame := ⟨#[], #["wph"]⟩

def minimalAxiomDB : Metamath.Verify.DB :=
  let objects : Std.HashMap String Metamath.Verify.Object := ∅
  let objects := objects.insert "wff" (.const "wff")
  let objects := objects.insert "ph" (.var "ph")
  let objects := objects.insert "wph" (.hyp false minimalAxiomFormula "wph")
  let objects := objects.insert "ax1" (.assert minimalAxiomFormula minimalAxiomFrame "ax1")
  { frame := minimalAxiomFrame
    scopes := #[]
    activeVars := #[("ph", 0)]
    objects := objects
    interrupt := false
    error? := none }

set_option maxRecDepth 10000 in
theorem minimalAxiomBytes_parsedDB_eq :
    checkBytesDB minimalAxiomBytes = minimalAxiomDB := by
  cbv

/- Positive fixtures: accepted, no parse/proof error code. -/
theorem emptyBytes_errorFree :
    (checkBytesDB emptyBytes).error = false := by decide +kernel
example : acceptsBytes emptyBytes := by
  exact (acceptsBytes_iff_noError emptyBytes).2 (by decide +kernel)
example : parseErrorCode? emptyBytes = none := by decide +kernel

theorem minimalAxiomBytes_errorFree :
    (checkBytesDB minimalAxiomBytes).error = false := by
  rw [minimalAxiomBytes_parsedDB_eq]
  rfl
example : acceptsBytes minimalAxiomBytes := by
  exact (acceptsBytes_iff_noError minimalAxiomBytes).2 minimalAxiomBytes_errorFree
example : parseErrorCode? minimalAxiomBytes = none := by
  unfold parseErrorCode?
  rw [minimalAxiomBytes_parsedDB_eq]
  rfl

/- Negative fixtures: rejected with concrete parser diagnostics. -/
example : (checkBytesDB brokenIncludeBytes).error = true := by decide +kernel
example : rejectsBytes brokenIncludeBytes := by
  exact (rejectsBytes_iff_error brokenIncludeBytes).2 (by decide +kernel)
example :
    parseErrorCode? brokenIncludeBytes =
      some Metamath.Verify.ParseErrorCode.notACommand := by
  decide +kernel

theorem brokenConstBytes_error :
    (checkBytesDB brokenConstBytes).error = true := by cbv
example : rejectsBytes brokenConstBytes := by
  exact (rejectsBytes_iff_error brokenConstBytes).2 brokenConstBytes_error
example :
    parseErrorCode? brokenConstBytes =
      some Metamath.Verify.ParseErrorCode.unclosedConst := by
  cbv

end Mettapedia.Languages.Metamath.Fixtures
