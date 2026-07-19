import MeTTailCore.MeTTaIL.ContextualStep

namespace MeTTailCore.MeTTaIL.Profile

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.ContextualStep

abbrev BuiltinRelation :=
  String → List Pattern → List (List Pattern)

structure BuiltinTable where
  relation : BuiltinRelation := fun _ _ => []

namespace BuiltinTable

def toRelationEnv (builtins : BuiltinTable) (base : RelationEnv := RelationEnv.empty) :
    RelationEnv where
  tuples := fun rel args => base.tuples rel args ++ builtins.relation rel args

end BuiltinTable

structure RuntimePolicy where
  maxFuel : Nat := 1000
  maxContextDepth : Nat := 64
  normalizeToFixedPoint : Bool := true
deriving Repr, DecidableEq

structure SpecBundle where
  language : LanguageDef
  relationEnv : RelationEnv := RelationEnv.empty
  builtins : BuiltinTable := {}
  policy : RuntimePolicy := {}

namespace SpecBundle

def effectiveRelationEnv (bundle : SpecBundle) : RelationEnv :=
  BuiltinTable.toRelationEnv bundle.builtins bundle.relationEnv

def rewriteStep (bundle : SpecBundle) (term : Pattern) : List Pattern :=
  rewriteStepWithPremisesUsing (effectiveRelationEnv bundle) bundle.language term

def contextualReducts (bundle : SpecBundle) (term : Pattern) : List Pattern :=
  reductsUsing (effectiveRelationEnv bundle) bundle.language
    bundle.policy.maxContextDepth term

def normalize (bundle : SpecBundle) (term : Pattern) : Pattern :=
  normalizeFirstUsing
    (effectiveRelationEnv bundle)
    bundle.language
    bundle.policy.maxContextDepth
    bundle.policy.maxFuel
    term

def eval (bundle : SpecBundle) (term : Pattern) : List Pattern :=
  if bundle.policy.normalizeToFixedPoint then
    [normalize bundle term]
  else
    contextualReducts bundle term

end SpecBundle

end MeTTailCore.MeTTaIL.Profile
