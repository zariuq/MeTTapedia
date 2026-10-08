import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation

/-!
# Full source substitution in the open continuation interpretation

Names and arbitrary program terms are substituted independently in the source
presentation. Their interpreted environment retains a genuine return binder
for every program value. The comparison commutes with both source binders and
target substitution, including term variables beneath abstractions, persistent
definitions and one-shot carriers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

def Environment.pullback {Γ Ω : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Ω Δ) (ren : Ren NamePassing.Presentation.signature Γ Ω) :
    Environment Γ Δ where
  name := fun name => environment.name (ren _ name)
  program := fun term => environment.program (ren _ term)

theorem Environment.lift_pullback {Γ Ω : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Ω Δ) (ren : Ren NamePassing.Presentation.signature Γ Ω) :
    environment.lift.pullback (liftRen ren [.nm]) = (environment.pullback ren).lift := by
  apply Environment.ext
  · funext name
    cases name <;> rfl
  · funext term
    cases term
    rfl

theorem Environment.substitute_pullback {Γ Ω : Ctx NamePassing.Presentation.signature}
    {Δ Θ : Ctx sig} (environment : Environment Ω Δ)
    (ren : Ren NamePassing.Presentation.signature Γ Ω) (substitution : Sub sig Δ Θ) :
    (environment.substitute substitution).pullback ren =
      (environment.pullback ren).substitute substitution := rfl

theorem Environment.forget_new_name {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) :
    environment.lift.pullback (fun _ name => .succ name) = environment.substitute weakening := by
  apply Environment.ext
  · funext name
    exact (bind_var_eq_rename (fun _ position => .succ position) (environment.name name)).symm
  · funext term
    rfl

theorem interpretName_source_rename {Γ Ω : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (name : NamePassing.Presentation.Name Γ)
    (ren : Ren NamePassing.Presentation.signature Γ Ω) (environment : Environment Ω Δ) :
    interpretName (Mettapedia.OSLF.Binding.rename ren name) environment =
      interpretName name (environment.pullback ren) := by
  cases name with
  | var => rfl
  | op impossible => nomatch impossible

theorem interpret_source_rename : ∀ {Γ Ω : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (term : NamePassing.Presentation.Program Γ)
    (ren : Ren NamePassing.Presentation.signature Γ Ω)
    (environment : Environment Ω Δ) (result : Name Δ),
    interpret (Mettapedia.OSLF.Binding.rename ren term) environment result =
      interpret term (environment.pullback ren) result
  | _, _, _, .var term, ren, environment, result => by
      simp only [Mettapedia.OSLF.Binding.rename, interpret, Environment.pullback]
  | _, _, _, .op .reference (.cons name .nil), ren, environment, result => by
      simp only [Mettapedia.OSLF.Binding.rename, renameArgs]
      simp only [interpret]
      rw [interpretName_source_rename]
      rfl
  | _, _, _, .op .abstraction (.cons body .nil), ren, environment, result => by
      simp only [Mettapedia.OSLF.Binding.rename, renameArgs]
      simp only [interpret]
      rw [interpret_source_rename body, Environment.lift_pullback, Environment.substitute_pullback]
  | _, _, _, .op .application (.cons function (.cons argument .nil)), ren, environment, result => by
      simp only [Mettapedia.OSLF.Binding.rename, renameArgs]
      simp only [interpret]
      rw [interpret_source_rename function, Environment.substitute_pullback, interpretName_source_rename]
      rfl
  | _, _, _, .op .definition (.cons value (.cons body .nil)), ren, environment, result => by
      simp only [Mettapedia.OSLF.Binding.rename, renameArgs]
      simp only [interpret]
      rw [interpret_source_rename body, interpret_source_rename value, Environment.lift_pullback,
        Environment.substitute_pullback, Environment.substitute_pullback]
      rfl
  | _, _, _, .op .carrier (.cons name (.cons value (.cons body .nil))), ren, environment, result => by
      simp only [Mettapedia.OSLF.Binding.rename, renameArgs]
      simp only [interpret]
      rw [interpret_source_rename body, interpret_source_rename value,
        interpretName_source_rename, Environment.substitute_pullback]
      rfl
termination_by _ _ _ term _ _ _ => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Interpret a whole source substitution, retaining the return binder of
each independently supplied source program. -/
def Environment.sourceSubstitute {Γ Ω : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Ω Δ) (substitution : Sub NamePassing.Presentation.signature Γ Ω) :
    Environment Γ Δ where
  name := fun name => interpretName (substitution _ name) environment
  program := fun term => interpret (substitution _ term) (environment.substitute weakening) (.var .zero)

theorem interpret_open_result {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (term : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    inst (interpret term (environment.substitute weakening) (.var .zero)) result =
      interpret term environment result := by
  change Mettapedia.OSLF.Binding.bind (extend result)
    (interpret term (environment.substitute weakening) (.var .zero)) = _
  rw [interpret_target_substitution, Environment.substitute_composition]
  have identity : (fun s name => Mettapedia.OSLF.Binding.bind (extend result) (weakening s name)) =
      (fun s name => (Term.var name : Term sig Δ s)) := by
    funext s name
    rfl
  rw [identity, Environment.substitute_identity]
  rfl

theorem Environment.sourceSubstitute_target {Γ Ω : Ctx NamePassing.Presentation.signature}
    {Δ Θ : Ctx sig} (environment : Environment Ω Δ)
    (source : Sub NamePassing.Presentation.signature Γ Ω) (target : Sub sig Δ Θ) :
    (environment.sourceSubstitute source).substitute target =
      (environment.substitute target).sourceSubstitute source := by
  apply Environment.ext
  · funext name
    exact interpretName_substitute _ _ _
  · funext term
    change Mettapedia.OSLF.Binding.bind (liftSub target [.nm])
      (interpret (source _ term) (environment.substitute weakening) (.var .zero)) = _
    rw [interpret_target_substitution, Environment.weaken_substitute]
    rfl

theorem Environment.lift_sourceSubstitute {Γ Ω : Ctx NamePassing.Presentation.signature}
    {Δ : Ctx sig} (environment : Environment Ω Δ)
    (source : Sub NamePassing.Presentation.signature Γ Ω) :
    environment.lift.sourceSubstitute (liftSub source [.nm]) =
      (environment.sourceSubstitute source).lift := by
  apply Environment.ext
  · funext name
    cases name with
    | zero => rfl
    | succ name =>
        change interpretName (weaken (source _ name)) environment.lift =
          weaken (interpretName (source _ name) environment)
        rw [weaken, interpretName_source_rename, Environment.forget_new_name]
        exact (interpretName_substitute _ _ weakening).symm.trans
          (bind_var_eq_rename (fun _ name => .succ name) _)
  · funext term
    cases term with
    | succ term =>
        change interpret (Mettapedia.OSLF.Binding.rename (fun _ name => .succ name) (source _ term))
          (environment.lift.substitute weakening) (.var .zero) =
          Mettapedia.OSLF.Binding.bind (liftSub weakening [.nm])
            (interpret (source _ term) (environment.substitute weakening) (.var .zero))
        rw [interpret_source_rename, Environment.substitute_pullback, Environment.forget_new_name,
          interpret_target_substitution]
        have unused : ((environment.substitute weakening).substitute weakening) =
            (environment.substitute weakening).substitute (liftSub weakening [.nm]) := by
          rw [Environment.substitute_composition, Environment.substitute_composition]
          rfl
        rw [unused]
        rfl

theorem interpretName_source_substitution {Γ Ω : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (name : NamePassing.Presentation.Name Γ) (source : Sub NamePassing.Presentation.signature Γ Ω)
    (environment : Environment Ω Δ) :
    interpretName (Mettapedia.OSLF.Binding.bind source name) environment =
      interpretName name (environment.sourceSubstitute source) := by
  cases name with
  | var => rfl
  | op impossible => nomatch impossible

/-- Complete source substitution, including arbitrary term holes and every
stored or bound position, is interpreted by the independently built environment. -/
theorem interpret_source_substitution : ∀ {Γ Ω : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (term : NamePassing.Presentation.Program Γ) (source : Sub NamePassing.Presentation.signature Γ Ω)
    (environment : Environment Ω Δ) (result : Name Δ),
    interpret (Mettapedia.OSLF.Binding.bind source term) environment result =
      interpret term (environment.sourceSubstitute source) result
  | _, _, _, .var term, source, environment, result => by
      simpa only [Mettapedia.OSLF.Binding.bind, interpret, Environment.sourceSubstitute] using
        (interpret_open_result (source _ term) environment result).symm
  | _, _, _, .op .reference (.cons name .nil), source, environment, result => by
      simp only [Mettapedia.OSLF.Binding.bind, bindArgs]
      simp only [interpret]
      rw [interpretName_source_substitution]
      rfl
  | _, _, _, .op .abstraction (.cons body .nil), source, environment, result => by
      simp only [Mettapedia.OSLF.Binding.bind, bindArgs]
      simp only [interpret]
      rw [interpret_source_substitution body, Environment.lift_sourceSubstitute,
        ← Environment.sourceSubstitute_target]
  | _, _, _, .op .application (.cons function (.cons argument .nil)), source, environment, result => by
      simp only [Mettapedia.OSLF.Binding.bind, bindArgs]
      simp only [interpret]
      rw [interpret_source_substitution function, ← Environment.sourceSubstitute_target,
        interpretName_source_substitution]
      rfl
  | _, _, _, .op .definition (.cons value (.cons body .nil)), source, environment, result => by
      simp only [Mettapedia.OSLF.Binding.bind, bindArgs]
      simp only [interpret]
      rw [interpret_source_substitution body, interpret_source_substitution value,
        Environment.lift_sourceSubstitute, ← Environment.sourceSubstitute_target,
        ← Environment.sourceSubstitute_target]
      rfl
  | _, _, _, .op .carrier (.cons name (.cons value (.cons body .nil))), source, environment, result => by
      simp only [Mettapedia.OSLF.Binding.bind, bindArgs]
      simp only [interpret]
      rw [interpret_source_substitution body, interpret_source_substitution value,
        interpretName_source_substitution, ← Environment.sourceSubstitute_target]
      rfl
termination_by _ _ _ term _ _ _ => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation
