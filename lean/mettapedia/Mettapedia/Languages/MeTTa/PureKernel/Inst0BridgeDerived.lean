import Mettapedia.Languages.MeTTa.PureKernel.Inst0BridgeStaging

namespace Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- Default-binder compatibility bridge derived from the staged ambient proof family. -/
theorem inst0ApplyBridgeCompat_defaultBinderName :
    Inst0ApplyBridgeCompat defaultBinderName := by
  intro n k ρ a body hcompat
  have hambient : Scratch.inst0AmbientDistinctTargetEq 0 defaultBinderName 0 k ρ a body :=
    Scratch.inst0AmbientDistinctTargetEq_all defaultBinderName 0 0 k ρ a body hcompat
  have hbinder : Scratch.inst0BinderTargetEqDistinct defaultBinderName 0 k ρ a body :=
    (Scratch.inst0AmbientDistinctTargetEq_zero_iff defaultBinderName 0 k ρ a body).mp hambient
  simpa [Scratch.inst0BinderTargetEqDistinct, Scratch.inst0BinderClosedLhsDistinct,
    Scratch.inst0BinderClosedTargetDistinct, Scratch.closeAmbient, Scratch.buildEnv,
    Scratch.liftSubN, inst0, subst, subst0]
    using hbinder

/-- Default-binder open-form bridge derived from the staged apply-form theorem. -/
theorem inst0OpenBridgeCompat_defaultBinderName :
    Inst0OpenBridgeCompat defaultBinderName :=
  inst0ApplyBridgeCompat_to_openBridgeCompat inst0ApplyBridgeCompat_defaultBinderName

/-- Default-binder open-form `inst0` theorem without external bridge arguments. -/
theorem quoteTmWith_defaultBinderName_inst0_open_default
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat defaultBinderName k ρ)
    (a : PureTm n) (body : PureTm (n + 1)) :
    quoteTmWith defaultBinderName k ρ (inst0 a body) =
      openBVar 0 (quoteTmWith defaultBinderName k ρ a)
        (closeFVar 0 (defaultBinderName k)
          (quoteTmWith defaultBinderName (k + 1)
            (envCons (defaultBinderName k) ρ) body)) :=
  quoteTmWith_defaultBinderName_inst0_open_assuming_inst0Compat
    inst0ApplyBridgeCompat_defaultBinderName k ρ hcompat a body

end Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
