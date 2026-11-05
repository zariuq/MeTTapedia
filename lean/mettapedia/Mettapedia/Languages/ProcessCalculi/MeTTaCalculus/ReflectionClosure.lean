import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Reduction

/-!
# The displayed MeTTa-calculus rules as a relation, with recursive reflection

The source is L. G. Meredith's *The MeTTa calculus* (F1R3FLY manuscript).
`Step` reads its four displayed rules, COMM, PAR, EQUIV and REFL, literally,
with the unification premise and the structural equivalence as parameters.
The REFL premise is the same relation, including earlier REFL derivations, so
reflection is recursive.

Read literally, COMM substitutes into both continuations with no variable
convention, so one input's bound name can capture the other input's free
name. Even with a principal unifier and alpha-equivalence as the parameters,
the canary is related to its capturing reduct `@0 | @0`
(`Corrected.Controls.literal_rule_admits_capture`). The corrected relational
semantics `Corrected.Step` adds the convention to the admission of COMM and is
contained in this relation (`Corrected.step_toReflectionClosure`). Its
executable step has the nested reflection result
(`Corrected.Controls.corrected_nested`), which the naive reading's COMM-only
lookahead lacks (`Corrected.Controls.naive_step_misses_nested_reflection`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.ReflectionClosure

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-- The four displayed source rules, read literally, with the two genuinely
independent premise contracts kept explicit. COMM carries no variable
convention. Reflection does not call an evaluator. -/
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

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.ReflectionClosure
