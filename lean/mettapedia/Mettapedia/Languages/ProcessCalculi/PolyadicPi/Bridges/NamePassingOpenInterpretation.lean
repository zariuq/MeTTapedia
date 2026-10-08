import Mettapedia.Languages.LambdaCalculus.NamePassingPresentation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Basic

/-!
# Continuation interpretation of the open name-passing presentation

An environment independently supplies names and programs. A supplied program
is an actual target process beneath its distinguished return-name binder.
Thus ordinary source term variables can depend on the return channel; they
are not silently converted to references or result-independent processes.

The constructor interpretation uses the five published clauses. All target
simultaneous substitutions commute with it, including substitutions in the
supplied program bodies and underneath every fresh name. The complete source
substitution comparison is constructed in the companion module.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

open Mettapedia.Languages.LambdaCalculus

/-- A program value has one distinguished bound return name. -/
structure Environment (Γ : Ctx NamePassing.Presentation.signature) (Δ : Ctx sig) where
  name : Var Γ .nm → Name Δ
  program : Var Γ .tm → Proc (.nm :: Δ)

@[ext] theorem Environment.ext {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    {first second : Environment Γ Δ}
    (names : first.name = second.name) (programs : first.program = second.program) :
    first = second := by
  cases first
  cases second
  cases names
  cases programs
  rfl

def weakening {Δ : Ctx sig} : Sub sig Δ (.nm :: Δ) :=
  fun _ name => .var (.succ name)

def Environment.substitute {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (environment : Environment Γ Δ) (substitution : Sub sig Δ Θ) : Environment Γ Θ where
  name := fun name => Mettapedia.OSLF.Binding.bind substitution (environment.name name)
  program := fun term => Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) (environment.program term)

/-- Extend the source reference binder. The program's return binder remains
first while the newly available reference is inserted immediately after it. -/
def Environment.lift {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) : Environment (.nm :: Γ) (.nm :: Δ) where
  name := fun name => match name with
    | .zero => .var .zero
    | .succ old => weaken (environment.name old)
  program := fun name => match name with
    | .succ old => Mettapedia.OSLF.Binding.bind (liftSub weakening [.nm]) (environment.program old)

theorem Environment.substitute_identity {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) :
    environment.substitute (fun _ name => .var name) = environment := by
  apply Environment.ext
  · funext name
    exact bind_id _
  · funext term
    simp only [substitute, liftSub_var, bind_id]

theorem Environment.substitute_composition {Γ : Ctx NamePassing.Presentation.signature}
    {Δ Θ Ξ : Ctx sig} (environment : Environment Γ Δ)
    (first : Sub sig Δ Θ) (second : Sub sig Θ Ξ) :
    (environment.substitute first).substitute second =
      environment.substitute (fun s name => Mettapedia.OSLF.Binding.bind second (first s name)) := by
  apply Environment.ext
  · funext name
    exact bind_comp _ _ _
  · funext term
    simp only [substitute, bind_comp]
    exact congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.program term))
      (liftSub_comp first second [.nm])

theorem weakening_substitute {Δ Θ : Ctx sig} (substitution : Sub sig Δ Θ) :
    (fun s name => Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) (weakening s name)) =
      (fun s name => Mettapedia.OSLF.Binding.bind weakening (substitution s name)) := by
  funext s name
  change weaken (substitution s name) = Mettapedia.OSLF.Binding.bind weakening (substitution s name)
  exact (bind_var_eq_rename (fun _ position => .succ position) _).symm

theorem Environment.lift_substitute {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (environment : Environment Γ Δ) (substitution : Sub sig Δ Θ) :
    (environment.lift).substitute (liftSub substitution [.nm]) =
      (environment.substitute substitution).lift := by
  apply Environment.ext
  · funext name
    cases name with
    | zero => rfl
    | succ name =>
        change Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) (weaken (environment.name name)) =
          weaken (Mettapedia.OSLF.Binding.bind substitution (environment.name name))
        simp only [weaken, bind_rename, rename_bind]
        apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.name name))
        funext s position
        rfl
  · funext term
    cases term with
    | succ term =>
        simp only [substitute, lift, bind_comp]
        apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.program term))
        exact (liftSub_comp weakening (liftSub substitution [.nm]) [.nm]).trans
          ((congrArg (fun assigned : Sub sig Δ (.nm :: Θ) => liftSub assigned [Srt.nm]) (weakening_substitute substitution)).trans
            (liftSub_comp substitution weakening [.nm]).symm)

/-- Reindex a supplied name term through the independently given environment. -/
def interpretName {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (term : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) : Name Δ :=
  environment.name (NamePassing.Presentation.nameVariable term)

def interpret : {Γ : Ctx NamePassing.Presentation.signature} → {Δ : Ctx sig} →
    NamePassing.Presentation.Program Γ → Environment Γ Δ → Name Δ → Proc Δ
  | _, _, .var term, environment, result => inst (environment.program term) result
  | _, _, .op .reference (.cons name .nil), environment, result =>
      out1 (interpretName name environment) result
  | _, _, .op .abstraction (.cons body .nil), environment, result =>
      inp2 result (interpret body (environment.substitute weakening).lift (.var (.succ .zero)))
  | _, _, .op .application (.cons function (.cons argument .nil)), environment, result =>
      nu (par (interpret function (environment.substitute weakening) (.var .zero))
        (out2 (.var .zero) (weaken (interpretName argument environment)) (weaken result)))
  | _, _, .op .definition (.cons value (.cons body .nil)), environment, result =>
      nu (par (interpret body environment.lift (weaken result))
        (rep (inp1 (.var .zero)
          (interpret value ((environment.substitute weakening).substitute weakening) (.var .zero)))))
  | _, _, .op .carrier (.cons name (.cons value (.cons body .nil))), environment, result =>
      par (interpret body environment result)
        (inp1 (interpretName name environment)
          (interpret value (environment.substitute weakening) (.var .zero)))
termination_by _ _ term _ _ => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem interpretName_substitute {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (term : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) (substitution : Sub sig Δ Θ) :
    Mettapedia.OSLF.Binding.bind substitution (interpretName term environment) =
      interpretName term (environment.substitute substitution) := rfl

private theorem inst_substitute {Δ Θ : Ctx sig} (body : Proc (.nm :: Δ))
    (result : Name Δ) (substitution : Sub sig Δ Θ) :
    Mettapedia.OSLF.Binding.bind substitution (inst body result) =
      inst (Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) body) (Mettapedia.OSLF.Binding.bind substitution result) := by
  simp only [inst, bind_comp]
  congr 1
  funext s name
  cases name with
  | zero => rfl
  | succ name =>
      change substitution s name = Mettapedia.OSLF.Binding.bind
        (extend (Mettapedia.OSLF.Binding.bind substitution result)) (weaken (substitution s name))
      simp only [weaken, bind_rename, extend]
      exact (bind_id (substitution s name)).symm

theorem Environment.weaken_substitute {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (environment : Environment Γ Δ) (substitution : Sub sig Δ Θ) :
    (environment.substitute weakening).substitute (liftSub substitution [.nm]) =
      (environment.substitute substitution).substitute weakening := by
  rw [Environment.substitute_composition, Environment.substitute_composition]
  exact congrArg (environment.substitute) (weakening_substitute substitution)

private theorem bind_inp1 {Δ Θ : Ctx sig} (substitution : Sub sig Δ Θ)
    (channel : Name Δ) (body : Proc (.nm :: Δ)) :
    Mettapedia.OSLF.Binding.bind substitution (inp1 channel body) =
      inp1 (Mettapedia.OSLF.Binding.bind substitution channel)
        (Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) body) := rfl

private theorem bind_inp2 {Δ Θ : Ctx sig} (substitution : Sub sig Δ Θ)
    (channel : Name Δ) (body : Proc (.nm :: .nm :: Δ)) :
    Mettapedia.OSLF.Binding.bind substitution (inp2 channel body) =
      inp2 (Mettapedia.OSLF.Binding.bind substitution channel)
        (Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm, .nm]) body) := rfl

private theorem bind_out2 {Δ Θ : Ctx sig} (substitution : Sub sig Δ Θ)
    (channel first second : Name Δ) :
    Mettapedia.OSLF.Binding.bind substitution (out2 channel first second) =
      out2 (Mettapedia.OSLF.Binding.bind substitution channel)
        (Mettapedia.OSLF.Binding.bind substitution first)
        (Mettapedia.OSLF.Binding.bind substitution second) := rfl

private theorem bind_par {Δ Θ : Ctx sig} (substitution : Sub sig Δ Θ) (first second : Proc Δ) :
    Mettapedia.OSLF.Binding.bind substitution (par first second) =
      par (Mettapedia.OSLF.Binding.bind substitution first)
        (Mettapedia.OSLF.Binding.bind substitution second) := rfl

private theorem bind_nu {Δ Θ : Ctx sig} (substitution : Sub sig Δ Θ) (body : Proc (.nm :: Δ)) :
    Mettapedia.OSLF.Binding.bind substitution (nu body) =
      nu (Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) body) := rfl

private theorem bind_rep {Δ Θ : Ctx sig} (substitution : Sub sig Δ Θ) (body : Proc Δ) :
    Mettapedia.OSLF.Binding.bind substitution (rep body) =
      rep (Mettapedia.OSLF.Binding.bind substitution body) := rfl

private theorem bind_weaken {Δ Θ : Ctx sig} {s : sig.Srt}
    (substitution : Sub sig Δ Θ) (term : Term sig Δ s) :
    Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) (weaken term) =
      weaken (Mettapedia.OSLF.Binding.bind substitution term) := by
  simp only [weaken, bind_rename, rename_bind]
  apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned term)
  funext s position
  rfl

private theorem liftSub_two {Δ Θ : Ctx sig} (substitution : Sub sig Δ Θ) :
    liftSub substitution [.nm, .nm] = liftSub (liftSub substitution [.nm]) [.nm] := by
  funext s position
  cases position with
  | zero => rfl
  | succ position =>
      cases position <;> rfl

theorem interpret_target_substitution : ∀ {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (term : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ) (result : Name Δ)
    (substitution : Sub sig Δ Θ),
    Mettapedia.OSLF.Binding.bind substitution (interpret term environment result) =
      interpret term (environment.substitute substitution) (Mettapedia.OSLF.Binding.bind substitution result)
  | _, _, _, .var term, environment, result, substitution => by
      simpa only [interpret, Environment.substitute] using
        inst_substitute (environment.program term) result substitution
  | _, _, _, .op .reference (.cons name .nil), environment, result, substitution => by
      simp only [interpret, out1, Mettapedia.OSLF.Binding.bind, bindArgs]
      rfl
  | _, _, _, .op .abstraction (.cons body .nil), environment, result, substitution => by
      rw [interpret, bind_inp2, interpret_target_substitution body]
      rw [liftSub_two]
      change inp2 (Mettapedia.OSLF.Binding.bind substitution result)
        (interpret body ((environment.substitute weakening).lift.substitute
          (liftSub (liftSub substitution [.nm]) [.nm])) (.var (.succ .zero))) = _
      rw [Environment.lift_substitute, Environment.weaken_substitute, interpret]
  | _, _, _, .op .application (.cons function (.cons argument .nil)), environment, result, substitution => by
      rw [interpret, bind_nu, bind_par, bind_out2, interpret_target_substitution function]
      rw [Environment.weaken_substitute, bind_weaken, bind_weaken, interpret]
      rfl
  | _, _, _, .op .definition (.cons value (.cons body .nil)), environment, result, substitution => by
      rw [interpret, bind_nu, bind_par, bind_rep, bind_inp1,
        interpret_target_substitution body, interpret_target_substitution value]
      rw [Environment.lift_substitute, bind_weaken]
      change nu (par (interpret body (environment.substitute substitution).lift
        (weaken (Mettapedia.OSLF.Binding.bind substitution result)))
        (rep (inp1 (.var .zero) (interpret value
          (((environment.substitute weakening).substitute weakening).substitute
            (liftSub (liftSub substitution [.nm]) [.nm])) (.var .zero))))) = _
      rw [Environment.weaken_substitute, Environment.weaken_substitute, interpret]
  | _, _, _, .op .carrier (.cons name (.cons value (.cons body .nil))), environment, result, substitution => by
      rw [interpret, bind_par, bind_inp1,
        interpret_target_substitution body, interpret_target_substitution value]
      rw [Environment.weaken_substitute, interpret]
      rfl
termination_by _ _ _ term _ _ _ => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation
