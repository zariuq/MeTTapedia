import Algorithms.MeTTa.Simple.Backend.RuleIndex

namespace Algorithms.MeTTa.Simple.Backend.RuleIndexContracts

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Backend.RuleIndex

theorem build_nil : build [] = [] := rfl

theorem aritiesForHead_empty
    (ctor : String) :
    aritiesForHead [] ctor = [] := rfl

theorem rewriteCountForHeadArity_empty
    (ctor : String) (arity : Nat) :
    rewriteCountForHeadArity [] ctor arity = 0 := rfl

theorem hasHead_def
    (idx : List HeadEntry) (ctor : String) :
    hasHead idx ctor = !(aritiesForHead idx ctor).isEmpty := rfl

theorem hasCompatHeadConstraintRule_empty
    (ctor : String) (arity : Nat) :
    hasCompatHeadConstraintRule [] ctor arity = false := rfl

end Algorithms.MeTTa.Simple.Backend.RuleIndexContracts
