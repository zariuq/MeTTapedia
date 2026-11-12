import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionConsumerControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionHeldTypeRead
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeControls

/-!
# Authored collection components, fresh callers and numeric-consumer dependencies

The audit includes the existing generalized binary helpers, marked-data
ingress, actual outer-let capture, and complete authored-probe composition.
It does not establish correspondence with a native completed-fold shortcut.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Languages.MeTTa.HE.DeliveredArgumentPackets
  , `Mettapedia.Languages.MeTTa.HE.EquationProtectedNames
  , `Mettapedia.Languages.MeTTa.HE.ContextualAlias
  , `Mettapedia.Languages.MeTTa.HE.ContextualAliasControls
  , `Mettapedia.Languages.MeTTa.HE.ContextualUnificationFrame
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldEmission
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldReadback
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldNativeEntry
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldSourceLoop
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldFunction
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldParameterCapture
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldSourceFrontier
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionScopedFold
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControl
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFunction
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFrontier
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseSource
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericFold
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericSource
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionHeldTypeRead
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionConsumerControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionMarkedControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetCapture
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetFrontier
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionUnifySource
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetSource
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeSource
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeControls ]

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
    if checked == 0 then throwError "no collection composition theorem declarations found under {root}"
    total := total + checked
  logInfo m!"Authored collection source composition: {total} theorem declarations; standard axioms only"
