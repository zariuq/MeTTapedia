import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Reduction

/-!
# Recursive reflection and the executable COMM-only lookahead profile

The source is L. G. Meredith's *The MeTTa calculus* (F1R3FLY manuscript).
Its core rule table and its implementation discussion motivate the two
different reflection profiles compared here.

The displayed COMM/PAR/EQUIV/REFL rules determine a least relation once
their unification and structural-equivalence premises are declared. The
REFL premise uses that same relation, including earlier REFL derivations.
This differs from the existing executable profile, whose lookahead invokes
only COMM. No full alpha-equivalence or unifier completeness claim is made
by choosing the existing executable premises as a concrete instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.ReflectionClosure

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-- The four displayed source rules, with the two genuinely independent
premise contracts kept explicit. Reflection does not call an evaluator. -/
inductive Step (unifies : Term → Term → Bindings → Prop) (equivalent : Proc → Proc → Prop) :
    Proc → Proc → Prop where
  | comm (left right : Term) (channel : Name) (first second : Proc) (bindings : Bindings)
      (solves : unifies left right bindings) :
      Step unifies equivalent (par (pFor left channel first) (pFor right channel second))
        (par (applyDot bindings first) (applyDot bindings second))
  | parallel {source target : Proc} (surrounding : Proc) :
      Step unifies equivalent source target →
      Step unifies equivalent (par source surrounding) (par target surrounding)
  | congruence {source source' target' target : Proc} :
      equivalent source source' → Step unifies equivalent source' target' →
      equivalent target' target → Step unifies equivalent source target
  | reflect (channel : Name) {source target : Proc} :
      Step unifies equivalent source target →
      Step unifies equivalent (pReflect channel source) (pFor (tProc target) channel pZero)

/-- The same recursive reflection clause can be applied repeatedly. -/
theorem nested_reflection {unifies : Term → Term → Bindings → Prop} {equivalent : Proc → Proc → Prop}
    (first second : Name) {source target : Proc} (step : Step unifies equivalent source target) :
    Step unifies equivalent (pReflect first (pReflect second source))
      (pFor (tProc (pFor (tProc target) second pZero)) first pZero) :=
  .reflect first (.reflect second step)

def executableUnifier (first second : Term) (bindings : Bindings) : Prop :=
  unifyPattern? first second = some bindings

theorem existing_comm_example_is_a_source_root :
    Step executableUnifier SC demoCommSource demoCommTarget := by
  have solved : executableUnifier (.fvar "a") pZero [("a", pZero)] := by
    change unifyPattern? (.fvar "a") pZero = some [("a", pZero)]
    decide +kernel
  simpa [demoCommSource, demoCommTarget, par, applyDot, dotBindings, applyBindings] using
    (Step.comm (unifies := executableUnifier) (equivalent := SC)
      (.fvar "a") pZero demoChan (.fvar "a") (.fvar "a") [("a", pZero)] solved)

def nestedSource : Proc := pReflect demoChan demoReflectSource
def nestedTarget : Proc := pFor (tProc demoReflectTarget) demoChan pZero

theorem recursive_reflection_has_the_nested_step : Step executableUnifier SC nestedSource nestedTarget :=
  nested_reflection demoChan demoChan existing_comm_example_is_a_source_root

theorem current_comm_only_lookahead_has_no_nested_result : step nestedSource = [] := by
  decide +kernel

/-- Even with exactly the same unification premise, COMM-only lookahead
does not implement unrestricted recursive REFL. This is a profile boundary,
not an impossibility of encoding reflection through ordinary core rules. -/
theorem recursive_reflection_is_not_the_current_executable_profile :
    ¬ ∀ source target, Step executableUnifier SC source target → target ∈ step source := by
  intro simulation
  have result := simulation nestedSource nestedTarget recursive_reflection_has_the_nested_step
  rw [current_comm_only_lookahead_has_no_nested_result] at result
  exact List.not_mem_nil result

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.ReflectionClosure
