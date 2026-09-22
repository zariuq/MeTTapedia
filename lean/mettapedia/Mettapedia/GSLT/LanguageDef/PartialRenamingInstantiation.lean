import Mettapedia.OSLF.Syntax.PartialRenaming
import Mettapedia.GSLT.LanguageDef.MetaDependencyBoundary

/-!
# Recovered contextual bodies instantiate at their actual arguments

The existing strengthening operation is connected to the existing argument spines,
`argsToSub`, `instantiate`, and compositional `instInto`. All hypotheses concern
explicit variable maps. No authoring convention or dependency inference is
introduced, and assignments retain their existing representation.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature} {M N : List (MetaArity S)}

/-- The actual instantiated variable spine denotes the selected renaming. -/
theorem argsToSub_instantiate_selected
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (dependencies : Ctx S) {ambient : Ctx S} (rho : Ren S dependencies ambient) :
    argsToSub (instantiateArgs assignment (renameArgs rho (idArgs dependencies))) =
      fun s v => Term.var (rho s v) := by
  funext s v
  rw [instantiateArgs_renameArgs, argsToSub_renameArgs,
    argsToSub_instantiate_idArgs]
  rfl

theorem bind_instantiate_selected
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {dependencies ambient : Ctx S} {s : S.Srt} (rho : Ren S dependencies ambient)
    (body : Term S dependencies s) :
    bind (argsToSub (instantiateArgs assignment (renameArgs rho (idArgs dependencies)))) body =
      rename rho body := by
  rw [argsToSub_instantiate_selected, bind_var_eq_rename]

/-- Recovery gives exactly the body whose application reconstructs the target. -/
theorem recovered_body_instantiates
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {dependencies ambient : Ctx S} {s : S.Srt}
    (rho : Ren S dependencies ambient) (St : Strengthener rho)
    (target : Term S ambient s) (body : Term S dependencies s)
    (found : strengthenT St target = some body) :
    bind (argsToSub (instantiateArgs assignment (renameArgs rho (idArgs dependencies)))) body =
      target := by
  rw [bind_instantiate_selected]
  exact rename_strengthenT St target body found

/-- For the supplied assignment's argument spine, existence concerns this
metavariable's typed body. It does not conclude existence of a complete
assignment merely from that body's existence. -/
theorem recovered_body_exists_iff
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {dependencies ambient : Ctx S} {s : S.Srt}
    (rho : Ren S dependencies ambient) (St : Strengthener rho)
    (target : Term S ambient s) :
    (∃ body, strengthenT St target = some body) ↔
      ∃ body : Term S dependencies s,
        bind (argsToSub (instantiateArgs assignment (renameArgs rho (idArgs dependencies))))
          body = target := by
  simp only [bind_instantiate_selected,
    strengthenT_eq_some_iff St]

theorem strengthenT_instantiate_metaVar_iff
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (i : Fin M.length) {ambient : Ctx S}
    (rho : Ren S (M.get i).1 ambient) (St : Strengthener rho)
    (target : Term S ambient (M.get i).2) :
    strengthenT St target = some (assignment i) ↔
      instantiate assignment (rename rho (metaVar i)) = target := by
  rw [instantiate_metaVar_arguments,
    strengthenT_eq_some_iff St]

/-- Instantiation into another metavariable extension uses the same selected
arguments, retaining any unresolved metavariables in the recovered body. -/
theorem instInto_metaVar_arguments
    (assignment : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (i : Fin M.length) {ambient : Ctx S} (rho : Ren S (M.get i).1 ambient) :
    instInto assignment (rename rho (metaVar i)) =
      rename (S := withMetas S N) rho (assignment i) := by
  rw [instInto_rename, instInto_metaVar]

theorem strengthenT_instInto_metaVar_iff
    (assignment : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (i : Fin M.length) {ambient : Ctx S}
    (rho : Ren S (M.get i).1 ambient) (St : Strengthener (S := withMetas S N) rho)
    (target : Term (withMetas S N) ambient (M.get i).2) :
    strengthenT St target = some (assignment i) ↔
      instInto assignment (rename rho (metaVar i)) = target := by
  rw [instInto_metaVar_arguments,
    strengthenT_eq_some_iff St]

end Mettapedia.OSLF.Binding
