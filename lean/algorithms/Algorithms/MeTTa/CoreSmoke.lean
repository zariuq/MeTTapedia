import MeTTailCore

namespace Algorithms.MeTTa.CoreSmoke

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Profile

def atomA : Pattern := .apply "A" []

def atomB : Pattern := .apply "B" []

def ruleAtoB : RewriteRule where
  name := "A_to_B"
  typeContext := []
  premises := []
  left := atomA
  right := atomB

def tinyLang : LanguageDef where
  name := "tiny"
  types := []
  terms := []
  equations := []
  rewrites := [ruleAtoB]
  congruenceCollections := []

def tinyBundle : SpecBundle where
  language := tinyLang

def tinyResult : Pattern :=
  SpecBundle.normalize tinyBundle atomA

def tinyResultMatches : Bool :=
  tinyResult == atomB

end Algorithms.MeTTa.CoreSmoke
