import Mettapedia.Languages.MeTTa.PureKernel.Inst0BridgeProof

namespace Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- Default-binder compatibility bridge derived from the staged ambient proof family. -/
theorem inst0ApplyBridgeCompat_defaultBinderName :
    Inst0ApplyBridgeCompat defaultBinderName := by
  intro n k ρ a body hcompat
  have hambient :
      Inst0BridgeProof.inst0AmbientDistinctTargetEq 0 defaultBinderName 0 k ρ a body :=
    Inst0BridgeProof.inst0AmbientDistinctTargetEq_all defaultBinderName 0 0 k ρ a body hcompat
  have hbinder :
      Inst0BridgeProof.inst0BinderTargetEqDistinct defaultBinderName 0 k ρ a body :=
    (Inst0BridgeProof.inst0AmbientDistinctTargetEq_zero_iff defaultBinderName 0 k ρ a body).mp
      hambient
  simpa [Inst0BridgeProof.inst0BinderTargetEqDistinct,
    Inst0BridgeProof.inst0BinderClosedLhsDistinct,
    Inst0BridgeProof.inst0BinderClosedTargetDistinct, Inst0BridgeProof.closeAmbient,
    Inst0BridgeProof.buildEnv, Inst0BridgeProof.liftSubN, inst0, subst, subst0]
    using hbinder

/-- Default-binder open-form bridge derived from the staged apply-form theorem. -/
theorem inst0OpenBridgeCompat_defaultBinderName :
    Inst0OpenBridgeCompat defaultBinderName :=
  inst0ApplyBridgeCompat_to_openBridgeCompat inst0ApplyBridgeCompat_defaultBinderName

/-- Default-binder apply-form `inst0` theorem without external bridge arguments. -/
theorem quoteTmWith_defaultBinderName_inst0_apply
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat defaultBinderName k ρ)
    (a : PureTm n) (body : PureTm (n + 1)) :
    quoteTmWith defaultBinderName k ρ (inst0 a body) =
      applySubst (SubstEnv.extend SubstEnv.empty (defaultBinderName k)
        (quoteTmWith defaultBinderName k ρ a))
        (quoteTmWith defaultBinderName (k + 1)
          (envCons (defaultBinderName k) ρ) body) :=
  inst0ApplyBridgeCompat_defaultBinderName k ρ a body hcompat

end Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
