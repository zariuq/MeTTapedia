import Mettapedia.OSLF.Syntax.LinearContexts
import Mettapedia.OSLF.Syntax.ContextualRootEvents

/-!
# Ambient substitution of structurally linear contexts

An ambient substitution may replace or duplicate ordinary variables, but it
cannot replace the distinguished hole. Transporting a structural one-hole
context therefore leaves its unique location in place, including under
binding arguments. The comparison with the variable representation is proved
below; it is the law needed to reindex located operational events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualLinearSubstitution

variable {S : Signature}

mutual

/-- Substitute ambient variables while retaining the chosen hole. -/
def map {c : S.Srt} : {Γ Δ : Ctx S} → {s : S.Srt} →
    Sub S Γ Δ → LinCtx S c Γ s → LinCtx S c Δ s
  | _, _, _, _, .hole => .hole
  | _, _, _, sigma, .op o args => .op o (mapArgs sigma args)

/-- Substitute ordinary arguments; the one distinguished argument remains
structurally located. -/
def mapArgs {c : S.Srt} : {Γ Δ : Ctx S} →
    {arity : List (List S.Srt × S.Srt)} →
    Sub S Γ Δ → LinArgs S c Γ arity → LinArgs S c Δ arity
  | _, _, _, sigma, .here (bs := bs) K rest =>
      .here (map (liftSub sigma bs) K) (bindArgs sigma rest)
  | _, _, _, sigma, .there (bs := bs) head rest =>
      .there (bind (liftSub sigma bs) head) (mapArgs sigma rest)

end

/-- Plugging is natural in the ambient substitution when the distinguished
hole is held fixed. -/
theorem bind_inst {Γ Δ : Ctx S} {c s : S.Srt}
    (sigma : Sub S Γ Δ) (K : Term S (c :: Γ) s) (t : Term S Γ c) :
    bind sigma (inst K t) =
      inst (bind (liftSub sigma [c]) K) (bind sigma t) := by
  simp only [inst, bind_comp]
  congr 1
  funext r v
  cases v with
  | zero => rfl
  | succ w =>
      simp only [extend, liftSub, bind, weaken, bind_rename]
      exact (bind_id (sigma r w)).symm

/-- Moving an ambient substitution past the extra hole agrees on every
variable, including variables beneath an arbitrary binder prefix. -/
private theorem shift_liftSub_commute {Γ Δ : Ctx S} (c : S.Srt)
    (sigma : Sub S Γ Δ) (bs : Ctx S) :
    (fun (r : S.Srt) (v : Var (bs ++ Γ) r) =>
      rename (liftRen (LinCtx.shift S c) bs) (liftSub sigma bs r v)) =
    (fun r v => liftSub (liftSub sigma [c]) bs r
      (liftRen (LinCtx.shift S c) bs r v)) := by
  calc
    _ = liftSub (fun r v => rename (LinCtx.shift S c) (sigma r v)) bs :=
      liftSub_rename sigma (LinCtx.shift S c) bs
    _ = liftSub (fun r v => liftSub sigma [c] r (Var.succ v)) bs := rfl
    _ = _ := (liftSub_liftRen (LinCtx.shift S c) (liftSub sigma [c]) bs).symm

/-- Exchanging the distinguished hole past binders commutes with an ambient
substitution that leaves the hole untouched. -/
private theorem exch_liftSub_commute {Γ Δ : Ctx S} (c : S.Srt)
    (sigma : Sub S Γ Δ) (bs : Ctx S) :
    (fun (r : S.Srt) (v : Var (c :: (bs ++ Γ)) r) =>
      rename (LinCtx.exch c bs) (liftSub (liftSub sigma bs) [c] r v)) =
    (fun r v => liftSub (liftSub sigma [c]) bs r
      (LinCtx.exch c bs r v)) := by
  funext r v
  cases v with
  | zero =>
      simp only [liftSub, rename, LinCtx.exch]
      rw [ContextualAssignment.liftSub_weakenVar]
      rfl
  | succ w =>
      simp only [liftSub, LinCtx.exch, weaken, rename_comp]
      exact congrFun (congrFun (shift_liftSub_commute c sigma bs) r) w

mutual

/-- Structural substitution denotes ordinary substitution lifted past the
hole. The binder case uses the proved exchange law above. -/
theorem toTerm_map : ∀ {Γ Δ : Ctx S} {c s : S.Srt}
    (sigma : Sub S Γ Δ) (K : LinCtx S c Γ s),
    LinCtx.toTerm (map sigma K) =
      bind (liftSub sigma [c]) (LinCtx.toTerm K)
  | _, _, _, _, _, .hole => rfl
  | _, _, _, _, sigma, .op _ args => by
      simp only [map, LinCtx.toTerm, bind, toArgs_mapArgs sigma args]

theorem toArgs_mapArgs : ∀ {Γ Δ : Ctx S} {c : S.Srt}
    {arity : List (List S.Srt × S.Srt)}
    (sigma : Sub S Γ Δ) (args : LinArgs S c Γ arity),
    LinCtx.toArgs (mapArgs sigma args) =
      bindArgs (liftSub sigma [c]) (LinCtx.toArgs args)
  | _, _, c, _, sigma, .here (bs := bs) K rest => by
      have hhead :
          rename (LinCtx.exch c bs)
              (bind (liftSub (liftSub sigma bs) [c]) (LinCtx.toTerm K)) =
            bind (liftSub (liftSub sigma [c]) bs)
              (rename (LinCtx.exch c bs) (LinCtx.toTerm K)) := by
        rw [rename_bind, bind_rename]
        exact congrArg (fun f => bind f (LinCtx.toTerm K))
          (exch_liftSub_commute c sigma bs)
      have hrest :
          renameArgs (LinCtx.shift S c) (bindArgs sigma rest) =
            bindArgs (liftSub sigma [c])
              (renameArgs (LinCtx.shift S c) rest) := by
        rw [renameArgs_bind, bindArgs_rename]
        exact congrArg (fun f => bindArgs f rest)
          (shift_liftSub_commute c sigma [])
      simp only [mapArgs, LinCtx.toArgs, bindArgs,
        toTerm_map (liftSub sigma bs) K, hhead, hrest]
  | _, _, c, _, sigma, .there (bs := bs) head rest => by
      have hhead :
          rename (liftRen (LinCtx.shift S c) bs) (bind (liftSub sigma bs) head) =
            bind (liftSub (liftSub sigma [c]) bs)
              (rename (liftRen (LinCtx.shift S c) bs) head) := by
        rw [rename_bind, bind_rename]
        exact congrArg (fun f => bind f head)
          (shift_liftSub_commute c sigma bs)
      simp only [mapArgs, LinCtx.toArgs, bindArgs, hhead,
        toArgs_mapArgs sigma rest]

end

mutual

/-- Identity substitution acts identically on structurally linear contexts. -/
theorem map_id : ∀ {Γ : Ctx S} {c s : S.Srt} (K : LinCtx S c Γ s),
    map (fun _ v => .var v) K = K
  | _, _, _, .hole => rfl
  | _, _, _, .op _ args => by
      simp only [map, mapArgs_id args]

theorem mapArgs_id : ∀ {Γ : Ctx S} {c : S.Srt}
    {arity : List (List S.Srt × S.Srt)} (args : LinArgs S c Γ arity),
    mapArgs (fun _ v => .var v) args = args
  | _, _, _, .here (bs := bs) K rest => by
      simp only [mapArgs, liftSub_var bs, map_id K, bindArgs_id rest]
  | _, _, _, .there (bs := bs) head rest => by
      simp only [mapArgs, liftSub_var bs, bind_id head, mapArgs_id rest]

end

mutual

/-- Sequential substitutions act as their composite. -/
theorem map_comp : ∀ {Γ Δ Θ : Ctx S} {c s : S.Srt}
    (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ) (K : LinCtx S c Γ s),
    map tau (map sigma K) = map (fun s v => bind tau (sigma s v)) K
  | _, _, _, _, _, _, _, .hole => rfl
  | _, _, _, _, _, sigma, tau, .op _ args => by
      simp only [map, mapArgs_comp sigma tau args]

theorem mapArgs_comp : ∀ {Γ Δ Θ : Ctx S} {c : S.Srt}
    {arity : List (List S.Srt × S.Srt)}
    (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ) (args : LinArgs S c Γ arity),
    mapArgs tau (mapArgs sigma args) =
      mapArgs (fun s v => bind tau (sigma s v)) args
  | _, _, _, _, _, sigma, tau, .here (bs := bs) K rest => by
      simp only [mapArgs, map_comp (liftSub sigma bs) (liftSub tau bs) K,
        liftSub_comp sigma tau bs, bindArgs_comp sigma tau rest]
  | _, _, _, _, _, sigma, tau, .there (bs := bs) head rest => by
      simp only [mapArgs, bind_comp (liftSub sigma bs) (liftSub tau bs) head,
        liftSub_comp sigma tau bs, mapArgs_comp sigma tau rest]

end

end Mettapedia.OSLF.Binding.ContextualLinearSubstitution
