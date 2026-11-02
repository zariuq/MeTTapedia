import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.Languages.Erlang.SequentialExamples
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF

/-! Preparation and operational controls for actual indexed Erlang rules.
The reference source supplies expectations. Frozen primitive/guard answers
here test the declared query ports; the live service and universal compiler
agreement remain separate obligations. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation.Controls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

def prepared : List (String × Bool × Bool) := Erlang.SequentialExamples.examples.map fun sample =>
  match prepare sample.program with
  | .error _ => (sample.name, false, false)
  | .ok compiled => (sample.name, compiled.compiled.validate.isEmpty, (plan compiled).obligations.isEmpty)

#eval prepared
#guard prepared.length == 16
#guard prepared.all fun row => row.2.1 && row.2.2

def multiValueProgram := Erlang.SequentialExamples.multiValue
def multiValueVerdicts : Option Bool × Option Bool :=
  match prepare multiValueProgram with
  | .error _ => (none, none)
  | .ok compiled =>
      let expected := node "ErDone" [valueList [.tuple [.literal (.integer 1), .literal (.integer 2)]]]
      let wrong := node "ErDone" [valueList [.literal (.integer 1), .literal (.integer 2)]]
      (GoldOSLF.verdict (GoldOSLF.ask compiled.compiled provider 2 64 (GoldOSLF.reaches expected) (initial multiValueProgram)),
       GoldOSLF.verdict (GoldOSLF.ask compiled.compiled provider 2 64 (GoldOSLF.reaches wrong) (initial multiValueProgram)))

#eval multiValueVerdicts
#guard multiValueVerdicts == (some true, some false)

def badTupleProgram := Erlang.SequentialExamples.tupleIsNotMultiValue
def tupleArityVerdict : Option Bool :=
  match prepare badTupleProgram with
  | .error _ => none
  | .ok compiled =>
      let expected := node "ErInvalid" [node "ErReturnArity" [count 2,
        valueList [.tuple [.literal (.integer 1), .literal (.integer 2)]]]]
      GoldOSLF.verdict (GoldOSLF.ask compiled.compiled provider 2 64 (GoldOSLF.reaches expected) (initial badTupleProgram))

#guard tupleArityVerdict == some true

def closureProgram : Erlang.Program := Erlang.Assembly.assemble <|
  Erlang.Assembly.letValues 1 (Erlang.Assembly.integer 7) <|
    Erlang.Assembly.apply (Erlang.Assembly.lambda 2 (Erlang.Assembly.variableRef 2))
      [Erlang.Assembly.integer 1, Erlang.Assembly.integer 2]

def closureVerdicts : Option Bool × Option Bool :=
  match prepare closureProgram with
  | .error _ => (none, none)
  | .ok compiled =>
      let expected := node "ErDone" [valueList [.literal (.integer 7)]]
      let wrong := node "ErDone" [valueList [.literal (.integer 2)]]
      (GoldOSLF.verdict (GoldOSLF.ask compiled.compiled provider 2 64 (GoldOSLF.reaches expected) (initial closureProgram)),
       GoldOSLF.verdict (GoldOSLF.ask compiled.compiled provider 2 64 (GoldOSLF.reaches wrong) (initial closureProgram)))

#eval closureVerdicts
#guard closureVerdicts == (some true, some false)

#guard match prepare Erlang.SequentialExamples.sendRequest with
  | .error _ => true
  | _ => false
#guard match prepare Erlang.SequentialExamples.sendRequest 1 with
  | .ok _ => true
  | _ => false

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation.Controls
