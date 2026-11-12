import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundaryControls

/-! # Stateful native dispatch, retained callers and shared-protocol dependencies

The audit covers source semantics and its protocol instance. It does not
certify a C callback or its physical binding/arena representation.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatch
  , `Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls
  , `Mettapedia.Languages.MeTTa.HE.NativeDispatchFocus
  , `Mettapedia.Languages.MeTTa.HE.NativeDispatchFocusControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundary
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundaryControls ]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  for root in roots do
    let mut checked : Nat := 0
    for (name, info) in env.constants.toList do
      if root.isPrefixOf name then
        match info with
        | .thmInfo _ =>
            checked := checked + 1
            let axioms ← liftCoreM (collectAxioms name)
            let bad := axioms.filter (· ∉ allowed)
            unless bad.isEmpty do throwError "{name}: unapproved axioms {bad.toList}"
        | _ => pure ()
    if checked == 0 then throwError "no retained native theorem declarations found under {root}"
    total := total + checked
  logInfo m!"Stateful native dispatch and retained protocol: {total} theorem declarations; standard axioms only"
