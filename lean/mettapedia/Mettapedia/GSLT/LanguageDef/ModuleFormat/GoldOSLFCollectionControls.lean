import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRGroundKernel
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogQueryKernel

/-! Front-door probes for the existing CHR transaction and Datalog
kept-premise kernels. Their generated bag/set equations prevent using the
equation-free decider. Generic certificate search retains the intended
positive and negative questions for a certified equality reading; an unknown
answer is not a negative semantic verdict. No contextual-equivalence
decidability follows. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF.CollectionControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

def emptyProvider : GeneralPremise.ProviderSnapshot := {signatures := [], rows := []}

def kept : Pattern := CHRKernel.occurrence (.fvar "kept-id") (.fvar "same-constraint")
def removed : Pattern := CHRKernel.occurrence (.fvar "removed-id") (.fvar "same-constraint")
def firing : Pattern := CHRKernel.key (.fvar "rule") [.fvar "kept-id", .fvar "removed-id"]
def chrSource (available : List Pattern) : Pattern :=
  CHRKernel.application firing [kept] [removed] [] available
def chrTarget : Pattern := CHRKernel.applied firing [] [kept]

def chrVerdicts : List (String × Option Bool) := [
  ("chr-kept-occurrence", verdict (ask CHRKernel.language emptyProvider 8 8
    (.possibly .any (.is chrTarget)) (chrSource [kept, removed]))),
  ("chr-no-double-consume", verdict (ask CHRKernel.language emptyProvider 8 8
    (.possibly .any .top) (chrSource [kept]))),
  ("chr-kept-not-erased", verdict (ask CHRKernel.language emptyProvider 8 8
    (.possibly .any (.is (CHRKernel.applied firing [] []))) (chrSource [kept, removed])))]

def known : List Pattern := [.fvar "a", .fvar "b"]
def dlSource (premises : List Pattern) : Pattern :=
  SouffleDatalog.Kernel.groundApplication (.fvar "id") (.fvar "env") (.fvar "c") premises known
def dlTarget (premises : List Pattern) : Pattern :=
  SouffleDatalog.Kernel.groundResult (.fvar "id") (.fvar "env") (.fvar "c") premises known

def datalogVerdicts : List (String × Option Bool) := [
  ("datalog-kept-facts", verdict (ask SouffleDatalog.QueryKernel.language
    (SouffleDatalog.QueryKernel.provider known) 4 8
    (.possibly .any (.is (dlTarget known))) (dlSource known))),
  ("datalog-duplicate-premise", verdict (ask SouffleDatalog.QueryKernel.language
    (SouffleDatalog.QueryKernel.provider known) 4 8
    (.possibly .any (.is (dlTarget [.fvar "a", .fvar "a"]))) (dlSource [.fvar "a", .fvar "a"]))),
  ("datalog-missing-premise", verdict (ask SouffleDatalog.QueryKernel.language
    (SouffleDatalog.QueryKernel.provider known) 4 8
    (.possibly .any .top) (dlSource [.fvar "c"])))]

#eval chrVerdicts
#eval datalogVerdicts
theorem chr_not_equation_free : CHRKernel.language.isEquationFree = false := by decide +kernel
theorem datalog_not_equation_free : SouffleDatalog.QueryKernel.language.isEquationFree = false := by decide +kernel

#guard chrVerdicts.map Prod.snd == [some true, none, none]
#guard datalogVerdicts.map Prod.snd == [some true, some true, none]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF.CollectionControls
