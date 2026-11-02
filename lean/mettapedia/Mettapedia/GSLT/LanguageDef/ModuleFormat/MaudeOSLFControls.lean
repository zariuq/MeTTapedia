import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
import Mettapedia.Languages.Maude.Examples
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF

/-! Questions about the actual compiled Maude IR. General certificate
search can establish direct rule firings without deciding the complete
equation theory. Questions needing equation-normalized representatives stay
open until the module's certified canonical forms are connected. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.OSLFControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

def provider : GeneralPremise.ProviderSnapshot := {signatures := [], rows := []}

def question (theory : Maude.Theory) (source : Maude.Term) (formula : Formula 0) : Option Bool :=
  match prepare theory with
  | .error _ => none
  | .ok prepared => GoldOSLF.verdict (GoldOSLF.ask prepared.language provider 3 8 formula (encode source))

def coffee : Option Bool := question Maude.Examples.vending (Maude.Examples.constant "vending.$")
  (.possibly (.rule 0) (.is (encode (Maude.Examples.constant "vending.c"))))

def apple : Option Bool := question Maude.Examples.vending (Maude.Examples.constant "vending.$")
  (.possibly (.rule 1) (.is (encode (Maude.Examples.binary "vending.merge"
    (Maude.Examples.constant "vending.a") (Maude.Examples.constant "vending.q")))))

def emptyCoffee : Option Bool := question Maude.Examples.vending (Maude.Examples.constant "vending.empty")
  (.possibly (.rule 0) .top)

def mutexAfterInitialization : Option Bool := question Maude.Examples.mutex (Maude.Examples.constant "mutex.init")
  (GoldOSLF.reaches (encode (Maude.Examples.binary "mutex.merge"
    (Maude.Examples.constant "mutex.crit1") (Maude.Examples.constant "mutex.idle2"))))

#eval [coffee, apple, emptyCoffee, mutexAfterInitialization]
#guard coffee == some true
#guard apple == some true
#guard emptyCoffee == none
#guard mutexAfterInitialization == none

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.OSLFControls
