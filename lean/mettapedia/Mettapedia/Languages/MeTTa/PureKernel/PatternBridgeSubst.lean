import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

/-!
# PatternBridgeSubst (Workbench)

This module is intentionally lightweight and non-imported.
It hosts bridge-oriented aliases and local scaffolding while the main
substitution transport theorem is developed directly in `PatternBridge.lean`.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- Workbench alias of the generic renaming bridge. -/
theorem quoteTmWith_rename_workbench
    (ν : Nat → String) {n m : Nat} (k : Nat)
    (ρdst : QuoteEnv m) (ρ : Ren n m) (t : PureTm n) :
    quoteTmWith ν k ρdst (rename ρ t) =
      quoteTmWith ν k (fun i => ρdst (ρ i)) t :=
  quoteTmWith_rename ν k ρdst ρ t

/-- Workbench alias for weakening through an `envCons` quote environment. -/
theorem quoteTmWith_rename_wk_envCons_workbench
    (ν : Nat → String) (k : Nat) (x : String) (ρ : QuoteEnv n) (t : PureTm n) :
    quoteTmWith ν k (envCons x ρ) (rename wk t) =
      quoteTmWith ν k ρ t :=
  quoteTmWith_rename_wk_envCons ν k x ρ t

end Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
