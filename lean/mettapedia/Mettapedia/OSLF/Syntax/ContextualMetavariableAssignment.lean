import Mettapedia.OSLF.Syntax.PartialRenaming

/-!
# Metavariable assignments with an ambient context

An assignment has two separate sources of variables: the metavariable's
declared arguments and the ambient context in which its value was obtained.
Occurrences still use `Term (withMetas S M)` and its explicit argument spine.
Instantiation substitutes the spine for the declared arguments and transports
the ambient variables under each argument's declared binders.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

/-- The declared dependency prefix and the ambient context are distinct.
In particular, a zero-argument metavariable can hold an ambient open value. -/
abbrev ContextualAssignment (S : Signature) (M : List (MetaArity S)) (Γ : Ctx S) :=
  (i : Fin M.length) → Term S ((M.get i).1 ++ Γ) (M.get i).2

namespace ContextualAssignment

variable {S : Signature} {M : List (MetaArity S)}

/-- Apply an ambient renaming while fixing the declared dependency prefix. -/
def mapRen {Γ Δ : Ctx S} (rho : Ren S Γ Δ) (body : ContextualAssignment S M Γ) :
    ContextualAssignment S M Δ :=
  fun i => rename (liftRen rho (M.get i).1) (body i)

/-- Apply an ambient substitution while fixing the declared dependency prefix. -/
def mapSub {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) (body : ContextualAssignment S M Γ) :
    ContextualAssignment S M Δ :=
  fun i => bind (liftSub sigma (M.get i).1) (body i)

theorem mapRen_id {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    mapRen (fun _ v => v) body = body := by
  funext i
  simp only [mapRen, liftRen_id, rename_id]

theorem mapRen_comp {Γ Δ Θ : Ctx S} (rho : Ren S Γ Δ) (rho' : Ren S Δ Θ)
    (body : ContextualAssignment S M Γ) :
    mapRen rho' (mapRen rho body) = mapRen (fun s v => rho' s (rho s v)) body := by
  funext i
  simp only [mapRen, rename_comp, liftRen_comp]

theorem mapSub_id {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    mapSub (fun _ v => .var v) body = body := by
  funext i
  simp only [mapSub, liftSub_var, bind_id]

theorem mapSub_comp {Γ Δ Θ : Ctx S} (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ)
    (body : ContextualAssignment S M Γ) :
    mapSub tau (mapSub sigma body) = mapSub (fun s v => bind tau (sigma s v)) body := by
  funext i
  simp only [mapSub, bind_comp, liftSub_comp]

theorem mapSub_var {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
    (body : ContextualAssignment S M Γ) :
    mapSub (fun s v => .var (rho s v)) body = mapRen rho body := by
  funext i
  simp only [mapSub, mapRen]
  have lifted := funext fun s => funext fun v => liftSub_var_comp rho (M.get i).1 s v
  rw [lifted, bind_var_eq_rename]

/-- Supply the declared arguments and ambient values by one ordinary
substitution. Both parts may contain arbitrary terms. -/
def joinSub : {dependencies Γ Δ : Ctx S} →
    Sub S dependencies Δ → Sub S Γ Δ → Sub S (dependencies ++ Γ) Δ
  | [], _, _, _, ambient => ambient
  | _ :: _, _, _, arguments, ambient => fun _ v => match v with
      | .zero => arguments _ .zero
      | .succ w => joinSub (fun s v => arguments s (.succ v)) ambient _ w

theorem joinSub_prefix {Γ Δ : Ctx S} : ∀ (dependencies : Ctx S)
    (arguments : Sub S dependencies Δ) (ambient : Sub S Γ Δ)
    (s : S.Srt) (v : Var dependencies s),
    joinSub arguments ambient s (injPrefix dependencies v) = arguments s v
  | [], _, _, _, v => nomatch v
  | _ :: _, _, _, _, .zero => rfl
  | _ :: dependencies, arguments, ambient, s, .succ v =>
      joinSub_prefix dependencies (fun r w => arguments r (.succ w)) ambient s v

theorem joinSub_ambient {Γ Δ : Ctx S} : ∀ (dependencies : Ctx S)
    (arguments : Sub S dependencies Δ) (ambient : Sub S Γ Δ)
    (s : S.Srt) (v : Var Γ s),
    joinSub arguments ambient s (weakenVar dependencies v) = ambient s v
  | [], _, _, _, _ => rfl
  | _ :: dependencies, arguments, ambient, s, v =>
      joinSub_ambient dependencies (fun r w => arguments r (.succ w)) ambient s v

theorem bind_joinSub {Γ Δ Θ : Ctx S} (sigma : Sub S Δ Θ) :
    ∀ (dependencies : Ctx S) (arguments : Sub S dependencies Δ) (ambient : Sub S Γ Δ),
      (fun s v => bind sigma (joinSub arguments ambient s v)) =
        joinSub (fun s v => bind sigma (arguments s v))
          (fun s v => bind sigma (ambient s v))
  | [], _, _ => rfl
  | _ :: dependencies, arguments, ambient => by
      funext s v
      cases v with
      | zero => rfl
      | succ w =>
          exact congrFun (congrFun
            (bind_joinSub sigma dependencies (fun r v => arguments r (.succ v)) ambient) s) w

/-- Weaken the codomain of a substitution; its source context stays fixed. -/
def weakenSub {Γ Δ : Ctx S} (bs : Ctx S) (sigma : Sub S Γ Δ) : Sub S Γ (bs ++ Δ) :=
  fun _ v => rename (fun _ w => weakenVar bs w) (sigma _ v)

theorem weakenSub_nil {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) :
    weakenSub [] sigma = sigma := by
  funext s v
  exact rename_id _

theorem weakenSub_cons {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) (bs : Ctx S) (b : S.Srt) :
    weakenSub (b :: bs) sigma = fun s v => weaken (weakenSub bs sigma s v) := by
  funext s v
  simp only [weakenSub, weaken, rename_comp, weakenVar]

theorem weakenSub_comp {Γ Δ Θ : Ctx S} (sigma : Sub S Γ Δ)
    (ambient : Sub S Δ Θ) (bs : Ctx S) :
    (fun s v => bind (weakenSub bs ambient) (sigma s v)) =
      weakenSub bs (fun s v => bind ambient (sigma s v)) := by
  funext s v
  exact (rename_bind ambient (fun _ w => weakenVar bs w) (sigma s v)).symm

theorem liftSub_weakenVar {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) :
    ∀ (bs : Ctx S) (s : S.Srt) (v : Var Γ s),
      liftSub sigma bs s (weakenVar bs v) = weakenSub bs sigma s v
  | [], _, _ => (rename_id _).symm
  | _ :: bs, s, v => by
      simp only [liftSub, weakenVar, liftSub_weakenVar sigma bs, weakenSub, weaken,
        rename_comp]

theorem bind_weakenSub {Γ Δ Θ : Ctx S} (sigma : Sub S Δ Θ)
    (ambient : Sub S Γ Δ) (bs : Ctx S) :
    (fun s v => bind (liftSub sigma bs) (weakenSub (S := S) bs ambient s v)) =
      weakenSub bs (fun s v => bind sigma (ambient s v)) := by
  funext s v
  simp only [weakenSub, bind_rename, rename_bind]
  congr 1
  funext r w
  exact liftSub_weakenVar sigma bs r w

theorem joinSub_liftSub {Γ Δ Θ : Ctx S} (sigma : Sub S Γ Δ) :
    ∀ (dependencies : Ctx S) (arguments : Sub S dependencies Θ) (ambient : Sub S Δ Θ),
      (fun s v => bind (joinSub arguments ambient) (liftSub sigma dependencies s v)) =
        joinSub arguments (fun s v => bind ambient (sigma s v))
  | [], _, _ => rfl
  | _ :: dependencies, arguments, ambient => by
      funext s v
      cases v with
      | zero => rfl
      | succ w =>
          simp only [liftSub, weaken, bind_rename]
          exact congrFun (congrFun
            (joinSub_liftSub sigma dependencies (fun r v => arguments r (.succ v)) ambient) s) w

/-- Instantiate one occurrence, with its explicit arguments and an ambient
substitution supplied independently. -/
def apply {Γ Δ : Ctx S} (body : ContextualAssignment S M Γ) (i : Fin M.length)
    (arguments : Sub S (M.get i).1 Δ) (ambient : Sub S Γ Δ) : Term S Δ (M.get i).2 :=
  bind (joinSub arguments ambient) (body i)

theorem bind_apply {Γ Δ Θ : Ctx S} (body : ContextualAssignment S M Γ)
    (i : Fin M.length) (arguments : Sub S (M.get i).1 Δ) (ambient : Sub S Γ Δ)
    (sigma : Sub S Δ Θ) :
    bind sigma (apply body i arguments ambient) =
      apply body i (fun s v => bind sigma (arguments s v))
        (fun s v => bind sigma (ambient s v)) := by
  simp only [apply, bind_comp, bind_joinSub]

theorem apply_mapSub {Γ Δ Θ : Ctx S} (body : ContextualAssignment S M Γ)
    (sigma : Sub S Γ Δ) (i : Fin M.length)
    (arguments : Sub S (M.get i).1 Θ) (ambient : Sub S Δ Θ) :
    apply (mapSub sigma body) i arguments ambient =
      apply body i arguments (fun s v => bind ambient (sigma s v)) := by
  simp only [apply, mapSub, bind_comp, joinSub_liftSub]

mutual
/-- Instantiate the existing schema syntax. The variable substitution is for
the schema context; the ambient substitution is for supplied metavariable
values. Under binders only the former acquires new source variables. -/
def instantiate {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    {Ξ Δ : Ctx S} → {s : S.Srt} → Sub S Γ Δ → Sub S Ξ Δ →
      Term (withMetas S M) Ξ s → Term S Δ s
  | _, _, _, _, valuation, .var v => valuation _ v
  | _, _, _, ambient, valuation, .op (.inl f) args =>
      .op f (instantiateArgs body ambient valuation args)
  | _, _, _, ambient, valuation, .op (.inr (.mk i)) args =>
      apply body i (argsToSub (instantiateArgs body ambient valuation args)) ambient

def instantiateArgs {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    {arity : List (List S.Srt × S.Srt)} → {Ξ Δ : Ctx S} →
    Sub S Γ Δ → Sub S Ξ Δ → Args (withMetas S M) arity Ξ → Args S arity Δ
  | _, _, _, _, _, .nil => .nil
  | _, _, _, ambient, valuation, .cons (bs := bs) head tail =>
      .cons (instantiate body (weakenSub (S := S) bs ambient)
        (liftSub valuation bs) head)
        (instantiateArgs body ambient valuation tail)
end

mutual
/-- Ordinary substitution after instantiation transports both the ambient
values and the schema variables, including beneath every declared binder. -/
theorem bind_instantiate {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    ∀ {Ξ Δ Θ : Ctx S} {s : S.Srt} (ambient : Sub S Γ Δ) (valuation : Sub S Ξ Δ)
      (sigma : Sub S Δ Θ) (t : Term (withMetas S M) Ξ s),
      bind sigma (instantiate body ambient valuation t) =
        instantiate body (fun s v => bind sigma (ambient s v))
          (fun s v => bind sigma (valuation s v)) t
  | _, _, _, _, _, _, _, .var _ => rfl
  | _, _, _, _, ambient, valuation, sigma, .op (.inl f) args => by
      simp only [instantiate, bind, bindArgs_instantiateArgs body ambient valuation sigma args]
  | _, _, _, _, ambient, valuation, sigma, .op (.inr (.mk i)) args => by
      simp only [instantiate, bind_apply, ← argsToSub_bindArgs,
        bindArgs_instantiateArgs body ambient valuation sigma args]

theorem bindArgs_instantiateArgs {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Ξ Δ Θ : Ctx S}
      (ambient : Sub S Γ Δ) (valuation : Sub S Ξ Δ) (sigma : Sub S Δ Θ)
      (args : Args (withMetas S M) arity Ξ),
      bindArgs sigma (instantiateArgs body ambient valuation args) =
        instantiateArgs body (fun s v => bind sigma (ambient s v))
          (fun s v => bind sigma (valuation s v)) args
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, ambient, valuation, sigma, .cons (bs := bs) head tail => by
      simp only [instantiateArgs, bindArgs,
        bind_instantiate body (weakenSub (S := S) bs ambient) (liftSub valuation bs)
          (liftSub sigma bs) head,
        bindArgs_instantiateArgs body ambient valuation sigma tail,
        bind_weakenSub, liftSub_comp]
end

mutual
/-- Base terms reuse the existing substitution algebra. -/
theorem instantiate_embed {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    ∀ {Ξ Δ : Ctx S} {s : S.Srt} (ambient : Sub S Γ Δ) (valuation : Sub S Ξ Δ)
      (t : Term S Ξ s),
      instantiate body ambient valuation (embed t) = bind valuation t
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, ambient, valuation, .op f args => by
      simp only [embed, instantiate, bind, instantiateArgs_embedArgs body ambient valuation args]

theorem instantiateArgs_embedArgs {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Ξ Δ : Ctx S}
      (ambient : Sub S Γ Δ) (valuation : Sub S Ξ Δ) (args : Args S arity Ξ),
      instantiateArgs body ambient valuation (embedArgs args) = bindArgs valuation args
  | _, _, _, _, _, .nil => rfl
  | _, _, _, ambient, valuation, .cons (bs := bs) head tail => by
      simp only [embedArgs, instantiateArgs, bindArgs,
        instantiate_embed body (weakenSub (S := S) bs ambient) (liftSub valuation bs) head,
        instantiateArgs_embedArgs body ambient valuation tail]
end

/-- Renaming is the variable-valued instance of the output substitution law. -/
theorem rename_instantiate {Γ Ξ Δ Θ : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (valuation : Sub S Ξ Δ) (rho : Ren S Δ Θ)
    {s : S.Srt} (t : Term (withMetas S M) Ξ s) :
    rename rho (instantiate body ambient valuation t) =
      instantiate body (fun s v => rename rho (ambient s v))
        (fun s v => rename rho (valuation s v)) t := by
  simpa only [bind_var_eq_rename] using
    bind_instantiate body ambient valuation (fun s v => .var (rho s v)) t

mutual
/-- Renaming schema variables composes their valuation; it does not rename
the independently supplied ambient context. -/
theorem instantiate_rename {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    ∀ {Ξ Ξ' Δ : Ctx S} {s : S.Srt} (ambient : Sub S Γ Δ) (valuation : Sub S Ξ' Δ)
      (rho : Ren S Ξ Ξ') (t : Term (withMetas S M) Ξ s),
      instantiate body ambient valuation (rename rho t) =
        instantiate body ambient (fun s v => valuation s (rho s v)) t
  | _, _, _, _, _, _, _, .var _ => rfl
  | _, _, _, _, ambient, valuation, rho, .op (.inl f) args => by
      simp only [rename, instantiate, instantiateArgs_renameArgs body ambient valuation rho args]
  | _, _, _, _, ambient, valuation, rho, .op (.inr (.mk i)) args => by
      simp only [rename, instantiate, instantiateArgs_renameArgs body ambient valuation rho args]

theorem instantiateArgs_renameArgs {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Ξ Ξ' Δ : Ctx S}
      (ambient : Sub S Γ Δ) (valuation : Sub S Ξ' Δ) (rho : Ren S Ξ Ξ')
      (args : Args (withMetas S M) arity Ξ),
      instantiateArgs body ambient valuation (renameArgs rho args) =
        instantiateArgs body ambient (fun s v => valuation s (rho s v)) args
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, ambient, valuation, rho, .cons (bs := bs) head tail => by
      simp only [renameArgs, instantiateArgs,
        instantiate_rename body (weakenSub (S := S) bs ambient)
          (liftSub valuation bs) (liftRen rho bs) head,
        instantiateArgs_renameArgs body ambient valuation rho tail, liftSub_liftRen]
end

theorem argsToSub_instantiateArgs {Γ Ξ Δ : Ctx S}
    (body : ContextualAssignment S M Γ) (ambient : Sub S Γ Δ) (valuation : Sub S Ξ Δ) :
    ∀ (dependencies : Ctx S)
      (args : Args (withMetas S M) (dependencies.map (fun b => ([], b))) Ξ)
      (s : S.Srt) (v : Var dependencies s),
      argsToSub (instantiateArgs body ambient valuation args) s v =
        instantiate body ambient valuation (argsToSub args s v)
  | [], .nil, _, v => nomatch v
  | _ :: _, .cons head _, _, .zero => by
      simp only [instantiateArgs, argsToSub, weakenSub_nil, liftSub]
  | _ :: dependencies, .cons _ tail, s, .succ v =>
      argsToSub_instantiateArgs body ambient valuation dependencies tail s v

/-- A metavariable's own argument variables read back as the supplied
schema-variable substitution, including non-variable argument values. -/
theorem instantiate_metaVar {Γ Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (i : Fin M.length) (arguments : Sub S (M.get i).1 Δ) :
    instantiate body ambient arguments (metaVar i) = apply body i arguments ambient := by
  simp only [metaVar, instantiate]
  congr 1
  funext s v
  simp only [argsToSub_instantiateArgs, argsToSub_idArgs, instantiate]

mutual
/-- Substitution into supplied ambient values agrees with composing the
explicit ambient substitution at each occurrence. -/
theorem instantiate_mapSub {Γ Γ' : Ctx S} (body : ContextualAssignment S M Γ)
    (sigma : Sub S Γ Γ') :
    ∀ {Ξ Δ : Ctx S} {s : S.Srt} (ambient : Sub S Γ' Δ) (valuation : Sub S Ξ Δ)
      (t : Term (withMetas S M) Ξ s),
      instantiate (mapSub sigma body) ambient valuation t =
        instantiate body (fun s v => bind ambient (sigma s v)) valuation t
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, ambient, valuation, .op (.inl f) args => by
      simp only [instantiate, instantiateArgs_mapSub body sigma ambient valuation args]
  | _, _, _, ambient, valuation, .op (.inr (.mk i)) args => by
      simp only [instantiate, instantiateArgs_mapSub body sigma ambient valuation args,
        apply_mapSub]

theorem instantiateArgs_mapSub {Γ Γ' : Ctx S} (body : ContextualAssignment S M Γ)
    (sigma : Sub S Γ Γ') :
    ∀ {arity : List (List S.Srt × S.Srt)} {Ξ Δ : Ctx S}
      (ambient : Sub S Γ' Δ) (valuation : Sub S Ξ Δ) (args : Args (withMetas S M) arity Ξ),
      instantiateArgs (mapSub sigma body) ambient valuation args =
        instantiateArgs body (fun s v => bind ambient (sigma s v)) valuation args
  | _, _, _, _, _, .nil => rfl
  | _, _, _, ambient, valuation, .cons (bs := bs) head tail => by
      simp only [instantiateArgs,
        instantiate_mapSub body sigma (weakenSub (S := S) bs ambient) (liftSub valuation bs) head,
        instantiateArgs_mapSub body sigma ambient valuation tail, weakenSub_comp]
end

/-- Lifted schema substitution fixes the new binders while transporting both
parts of an instantiation. -/
theorem instantiate_liftSub {Γ Ξ Ξ' Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (valuation : Sub S Ξ' Δ) (sigma : Sub (withMetas S M) Ξ Ξ') :
    ∀ (bs : Ctx S) (s : S.Srt) (v : Var (bs ++ Ξ) s),
      instantiate body (weakenSub bs ambient) (liftSub valuation bs) (liftSub sigma bs s v) =
        liftSub (fun s v => instantiate body ambient valuation (sigma s v)) bs s v
  | [], _, _ => by simp only [weakenSub_nil, liftSub]
  | b :: bs, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [liftSub, weaken, instantiate_rename, weakenSub_cons,
            ← instantiate_liftSub body ambient valuation sigma bs s w]
          exact (rename_instantiate body (weakenSub bs ambient) (liftSub valuation bs)
            (fun _ v => Var.succ (t := b) v) (liftSub sigma bs s w)).symm

mutual
/-- Instantiation respects the existing syntax substitution, including
substitution values that themselves contain metavariable occurrences. -/
theorem instantiate_bind {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    ∀ {Ξ Ξ' Δ : Ctx S} {s : S.Srt} (ambient : Sub S Γ Δ) (valuation : Sub S Ξ' Δ)
      (sigma : Sub (withMetas S M) Ξ Ξ') (t : Term (withMetas S M) Ξ s),
      instantiate body ambient valuation (bind sigma t) =
        instantiate body ambient (fun s v => instantiate body ambient valuation (sigma s v)) t
  | _, _, _, _, _, _, _, .var _ => rfl
  | _, _, _, _, ambient, valuation, sigma, .op (.inl f) args => by
      simp only [bind, instantiate, instantiateArgs_bindArgs body ambient valuation sigma args]
  | _, _, _, _, ambient, valuation, sigma, .op (.inr (.mk i)) args => by
      simp only [bind, instantiate, instantiateArgs_bindArgs body ambient valuation sigma args]

theorem instantiateArgs_bindArgs {Γ : Ctx S} (body : ContextualAssignment S M Γ) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Ξ Ξ' Δ : Ctx S}
      (ambient : Sub S Γ Δ) (valuation : Sub S Ξ' Δ) (sigma : Sub (withMetas S M) Ξ Ξ')
      (args : Args (withMetas S M) arity Ξ),
      instantiateArgs body ambient valuation (bindArgs sigma args) =
        instantiateArgs body ambient
          (fun s v => instantiate body ambient valuation (sigma s v)) args
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, ambient, valuation, sigma, .cons (bs := bs) head tail => by
      simp only [bindArgs, instantiateArgs,
        instantiate_bind body (weakenSub (S := S) bs ambient)
          (liftSub valuation bs) (liftSub sigma bs) head,
        instantiateArgs_bindArgs body ambient valuation sigma tail, instantiate_liftSub]
end

/-- Regard an existing closed-in-dependencies assignment as an ambient
assignment whose values do not use any ambient variable. -/
def ofClosed (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (Γ : Ctx S) : ContextualAssignment S M Γ :=
  fun i => rename (fun _ v => injPrefix (M.get i).1 v) (body i)

theorem apply_ofClosed
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {Γ Δ : Ctx S} (i : Fin M.length) (arguments : Sub S (M.get i).1 Δ)
    (ambient : Sub S Γ Δ) :
    apply (ofClosed body Γ) i arguments ambient = bind arguments (body i) := by
  simp only [apply, ofClosed, bind_rename, joinSub_prefix]

mutual
/-- The previous instantiator is recovered on its full domain, with an
arbitrary subsequent schema-variable substitution. -/
theorem instantiate_ofClosed
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) {Γ : Ctx S} :
    ∀ {Ξ Δ : Ctx S} {s : S.Srt} (ambient : Sub S Γ Δ) (valuation : Sub S Ξ Δ)
      (t : Term (withMetas S M) Ξ s),
      instantiate (ofClosed body Γ) ambient valuation t =
        bind valuation (Mettapedia.OSLF.Binding.instantiate body t)
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, ambient, valuation, .op (.inl f) args => by
      simp only [instantiate, Mettapedia.OSLF.Binding.instantiate, bind,
        instantiateArgs_ofClosed body ambient valuation args]
  | _, _, _, ambient, valuation, .op (.inr (.mk i)) args => by
      simp only [instantiate, Mettapedia.OSLF.Binding.instantiate,
        instantiateArgs_ofClosed body ambient valuation args, apply_ofClosed,
        bind_comp]
      congr 1
      funext s v
      exact argsToSub_bindArgs valuation (M.get i).1
        (Mettapedia.OSLF.Binding.instantiateArgs body args) s v

theorem instantiateArgs_ofClosed
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) {Γ : Ctx S} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Ξ Δ : Ctx S}
      (ambient : Sub S Γ Δ) (valuation : Sub S Ξ Δ) (args : Args (withMetas S M) arity Ξ),
      instantiateArgs (ofClosed body Γ) ambient valuation args =
        bindArgs valuation (Mettapedia.OSLF.Binding.instantiateArgs body args)
  | _, _, _, _, _, .nil => rfl
  | _, _, _, ambient, valuation, .cons (bs := bs) head tail => by
      simp only [instantiateArgs, Mettapedia.OSLF.Binding.instantiateArgs, bindArgs,
        instantiate_ofClosed body (weakenSub (S := S) bs ambient) (liftSub valuation bs) head,
        instantiateArgs_ofClosed body ambient valuation tail]
end

/-- Instantiate at the assignment's ambient context without further
substitution of schema variables. -/
def inContext {Γ : Ctx S} (body : ContextualAssignment S M Γ) {s : S.Srt}
    (t : Term (withMetas S M) Γ s) : Term S Γ s :=
  instantiate body (fun _ v => .var v) (fun _ v => .var v) t

theorem inContext_ofClosed
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S M) Γ s) :
    inContext (ofClosed body Γ) t = Mettapedia.OSLF.Binding.instantiate body t := by
  simp only [inContext, instantiate_ofClosed, bind_id]

theorem inContext_substitution {Γ Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (sigma : Sub S Γ Δ) {s : S.Srt} (t : Term (withMetas S M) Γ s) :
    bind sigma (inContext body t) =
      inContext (mapSub sigma body) (bind (fun s v => embed (sigma s v)) t) := by
  simp only [inContext, bind_instantiate, instantiate_mapSub, instantiate_bind,
    instantiate_embed, bind_id, bind]

theorem inContext_renaming {Γ Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (rho : Ren S Γ Δ) {s : S.Srt} (t : Term (withMetas S M) Γ s) :
    rename rho (inContext body t) = inContext (mapRen rho body) (rename rho t) := by
  simpa only [mapSub_var, embed, bind_var_eq_rename] using
    inContext_substitution body (fun s v => .var (rho s v)) t

end ContextualAssignment

end Mettapedia.OSLF.Binding
