import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Contextual metavariable dependencies and ambient scope

Dependencies are the existing `MetaArity` argument context. An occurrence
selects its arguments by a typed renaming into its ambient context. Increasing
that ambient context therefore does not increase the metavariable's permitted
dependencies. No rule-authoring or permission-inference convention is chosen.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature} {M : List (MetaArity S)}

/-- Instantiating the existing identity argument spine yields the actual
identity substitution into the base signature. -/
theorem argsToSub_instantiate_idArgs
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var bs s),
      argsToSub (instantiateArgs body (idArgs bs)) s v = Term.var v
  | [], _, v => nomatch v
  | _ :: rest, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [idArgs, instantiateArgs, instantiate, instantiateArgs_renameArgs,
            argsToSub, argsToSub_renameArgs, argsToSub_instantiate_idArgs body rest s w,
            rename]

/-- Applying a declared metavariable to its own argument variables recovers
the supplied body, including any declared arguments that body does not use. -/
theorem instantiate_metaVar
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (i : Fin M.length) : instantiate body (metaVar i) = body i := by
  simp only [metaVar, instantiate]
  have identity : argsToSub (instantiateArgs body (idArgs (M.get i).1)) =
      (fun _ v => Term.var v) := by
    funext s v
    exact argsToSub_instantiate_idArgs body _ s v
  rw [identity, bind_id]

/-- An explicit typed argument selection gives the same metavariable a
coherent occurrence at any ambient depth. This follows from substitution,
not from reading or comparing the two depths. -/
theorem instantiate_metaVar_arguments
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (i : Fin M.length) {ambient : Ctx S}
    (arguments : Ren S (M.get i).1 ambient) :
    instantiate body (rename arguments (metaVar i)) = rename arguments (body i) := by
  rw [instantiate_rename, instantiate_metaVar]

/-- Enlarging the occurrence's ambient scope transports its chosen arguments
and its result together. The permission context remains `(M.get i).1`. -/
theorem instantiate_metaVar_arguments_comp
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (i : Fin M.length) {ambient larger : Ctx S}
    (arguments : Ren S (M.get i).1 ambient) (extension : Ren S ambient larger) :
    instantiate body (rename extension (rename arguments (metaVar i))) =
      rename (fun s v => extension s (arguments s v)) (body i) := by
  rw [instantiate_rename, instantiate_metaVar_arguments, rename_comp]

end Mettapedia.OSLF.Binding
