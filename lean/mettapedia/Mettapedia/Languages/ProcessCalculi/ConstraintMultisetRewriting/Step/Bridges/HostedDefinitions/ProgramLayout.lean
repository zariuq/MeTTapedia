import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCore

/-!
# Stable rule-prefix locations for the public hosted query

The prefix consists of actual context rules. Its first two distinct sites and
a zero-arity hole of the second rule can also name a fresh query-local binder.
Equation calls copy names to fresh scopes; no additional runtime clause is
introduced merely to allocate a query key.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramLayout

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

abbrev Rule := ProgramBinders.Equation MSig [] ()

def rows (helpers authored : List Rule) : List Rule := ContextRules.fixed ++ helpers ++ authored

theorem at_least_two (helpers authored : List Rule) : 2 ≤ (rows helpers authored).length := by
  simp [rows, ContextRules.fixed, ContextRules.traversal, ContextRules.routing,
    ContextRules.binary, ContextRules.unary, ContextRules.identity, ContextRules.primitive, ContextRules.driver]

def querySite (helpers authored : List Rule) : Fin (rows helpers authored).length :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 2) (at_least_two helpers authored)⟩

def resultSite (helpers authored : List Rule) : Fin (rows helpers authored).length :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) (at_least_two helpers authored)⟩

theorem sites_distinct (helpers authored : List Rule) : querySite helpers authored ≠ resultSite helpers authored := by
  intro same
  have impossible := congrArg Fin.val same
  cases impossible

/-- This is the real resume-to-plug rule, not an unused allocator clause. -/
theorem result_rule (helpers authored : List Rule) :
    (rows helpers authored).get (resultSite helpers authored) = ContextRules.routing[1] := rfl

def resultHole (helpers authored : List Rule) :
    ((rows helpers authored).get (resultSite helpers authored)).Holes := (0 : Fin 3)

theorem result_arity (helpers authored : List Rule) :
    ((rows helpers authored).get (resultSite helpers authored)).arity (resultHole helpers authored) = ([], ()) := rfl

def resultKey (helpers authored : List Rule) : (BinderCore.keys (rows helpers authored)).Key :=
  ⟨resultSite helpers authored, resultHole helpers authored⟩

theorem key_arity (helpers authored : List Rule) :
    (BinderCore.keys (rows helpers authored)).arity (resultKey helpers authored) = ([], ()) := rfl

def resultDatum (helpers authored : List Rule) : Data (BinderCore.keys (rows helpers authored)) [] () :=
  .op (.inr (.mk ⟨[], resultKey helpers authored⟩)) .nil

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramLayout
