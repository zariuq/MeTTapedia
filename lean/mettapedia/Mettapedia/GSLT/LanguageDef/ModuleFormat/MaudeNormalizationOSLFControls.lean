import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeNormalizationStage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF

/-! Front-door questions about the actual oriented Peano stage. Reachability
and one-step questions remain distinct. A bounded unanswered question keeps
its unknown result, even when the independent normalizer knows the answer. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.OSLFControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

def question (source : Maude.Term) (formula : Formula 0) (rounds : Nat := 16) : Option Bool :=
  GoldOSLF.verdict (GoldOSLF.ask (language peano) provider 16 rounds formula (encode source))

def reaches (source target : Maude.Term) : Option Bool := question source (GoldOSLF.reaches (encode target))

def wrongOneStep (source : Maude.Term) : Option Bool :=
  question source (.possibly .any (.is (encode (Maude.Examples.numeral "peano" 17))))

private def zero : Maude.Term := Maude.Examples.numeral "peano" 0
private def n : Maude.Term := .var "N"
private def sum (left right : Maude.Term) : Maude.Term := Maude.Examples.binary "peano.add" left right

def verdicts : List (String × Option Bool × Bool) := [
  ("open-equation", question (sum zero n) (.possibly .any (.is (encode n))), true),
  ("symbolic-stuck", question (sum n zero) (.possibly .any .top), false),
  ("zero-normal", question zero (.possibly .any .top), false),
  ("nested-equation", question (.app "peano.succ" [sum zero n])
    (.possibly .any (.is (encode (.app "peano.succ" [n])))), true),
  ("variable-identity", question (sum zero n) (.possibly .any (.is (encode (.var "M")))), false),
  ("addition-result", reaches (sum (Maude.Examples.numeral "peano" 2) (Maude.Examples.numeral "peano" 3))
    (Maude.Examples.numeral "peano" 5), true)]

def exhausted : Option Bool :=
  GoldOSLF.verdict (GoldOSLF.ask (language peano) provider 0 0
    (.possibly .any (.is (encode n))) (encode (sum zero n)))

def wrongReachability : Option Bool :=
  reaches (sum (Maude.Examples.numeral "peano" 2) (Maude.Examples.numeral "peano" 3))
    (Maude.Examples.numeral "peano" 6)

#guard verdicts.length == 6
#guard verdicts.all fun entry => entry.2.1 == some entry.2.2
#guard exhausted == none
#guard wrongReachability == some false

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.OSLFControls
