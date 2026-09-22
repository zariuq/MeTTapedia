import Mettapedia.OSLF.Syntax.VariableArgumentRecognition
import Mettapedia.GSLT.LanguageDef.PartialRenamingInstantiation

/-!
# Recognized contextual arguments recover instantiating bodies

The recognizer constructs the existing strengthening input from actual
metavariable argument syntax. Body traversal remains solely `strengthenT`.
This is a slot operation for future matcher integration, not another matcher.
Arguments and target here share the same ambient context. The existing matcher
instead has pattern scope `bs ++ Γ` and target scope `bs ++ []`; integrating
this operation requires an explicit bound-prefix projection, not erasure of
the ordinary rule-variable context `Γ`.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature} {M : List (MetaArity S)}

/-- Variable recognition uses no base operators, so its primitive inverse
applies unchanged to terms of the base signature. -/
def VariableArguments.baseInverse {dependencies ambient : Ctx S}
    {args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) ambient}
    (selected : VariableArguments args) : Strengthener (S := S) selected.rho where
  un := selected.inverse.un
  un_rho := selected.inverse.un_rho
  rho_un := selected.inverse.rho_un

/-- The actual recognized arguments are the selected existing identity spine. -/
theorem VariableArguments.spine_eq {dependencies ambient : Ctx S}
    {args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) ambient}
    (selected : VariableArguments args) :
    args = renameArgs selected.rho (idArgs dependencies) := by
  have realization : argsToSub args =
      fun s v => Term.var (S := withMetas S M) (selected.rho s v) :=
    funext fun s => funext fun v => selected.realizes s v
  calc
    args = bindArgs (argsToSub args) (idArgs dependencies) :=
      (bindArgs_argsToSub_idArgs dependencies args).symm
    _ = renameArgs selected.rho (idArgs dependencies) := by
      rw [realization, bindArgs_var_eq_renameArgs]

theorem VariableArguments.instantiate_bind_eq_rename {dependencies ambient : Ctx S}
    {args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) ambient}
    (selected : VariableArguments args)
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {s : S.Srt} (body : Term S dependencies s) :
    bind (argsToSub (instantiateArgs assignment args)) body =
      rename (S := S) selected.rho body := by
  have actual := congrArg (instantiateArgs assignment) selected.spine_eq
  rw [actual, bind_instantiate_selected]

variable [DecidableEq S.Srt]

/-- Recognize the injective variable profile, then use the existing body reader.
The two inputs share an ambient context. `none` can mean an unsupported
profile, not absence of every possible solution. -/
def recoverVariableArgumentBody {dependencies ambient : Ctx S} {s : S.Srt}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) ambient)
    (target : Term S ambient s) : Option (Term S dependencies s) :=
  match recognizeVariableArguments args with
  | none => none
  | some selected => strengthenT selected.baseInverse target

/-- On a recognized profile, recovery is exactly application at the actual spine. -/
theorem recoverVariableArgumentBody_eq_some_iff {dependencies ambient : Ctx S} {s : S.Srt}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) ambient)
    (selected : VariableArguments args)
    (recognized : recognizeVariableArguments args = some selected)
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (target : Term S ambient s) (body : Term S dependencies s) :
    recoverVariableArgumentBody args target = some body ↔
      bind (argsToSub (instantiateArgs assignment args)) body = target := by
  rw [recoverVariableArgumentBody, recognized, strengthenT_eq_some_iff,
    selected.instantiate_bind_eq_rename assignment body]

theorem recoverVariableArgumentBody_instantiate_iff (i : Fin M.length) {ambient : Ctx S}
    (args : Args (withMetas S M) ((M.get i).1.map (fun s => ([], s))) ambient)
    (selected : VariableArguments args)
    (recognized : recognizeVariableArguments args = some selected)
    (assignment : (j : Fin M.length) → Term S (M.get j).1 (M.get j).2)
    (target : Term S ambient (M.get i).2) :
    recoverVariableArgumentBody args target = some (assignment i) ↔
      instantiate assignment (.op (.inr (.mk i)) args) = target :=
  recoverVariableArgumentBody_eq_some_iff args selected recognized assignment target (assignment i)

/-- Within the recognized profile only, rejection really is absence of a body. -/
theorem recoverVariableArgumentBody_eq_none_iff {dependencies ambient : Ctx S} {s : S.Srt}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) ambient)
    (selected : VariableArguments args)
    (recognized : recognizeVariableArguments args = some selected)
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (target : Term S ambient s) :
    recoverVariableArgumentBody args target = none ↔
      ¬ ∃ body : Term S dependencies s,
        bind (argsToSub (instantiateArgs assignment args)) body = target := by
  rw [recoverVariableArgumentBody, recognized, strengthenT_eq_none_iff]
  simp only [selected.instantiate_bind_eq_rename assignment]

end Mettapedia.OSLF.Binding
