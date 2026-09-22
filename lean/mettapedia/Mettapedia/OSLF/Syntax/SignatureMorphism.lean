import Mettapedia.OSLF.Syntax.RedexPositionIsExtraInput

/-!
# Morphisms of binding signatures

A language definition is a triple `(Sigma, E, R)`.  Changing the language means
changing the signature, and everything built over a signature has to travel
with it.  This module supplies the morphisms and proves what travels.

A morphism carries sorts to sorts and operators to operators, and must carry
each operator's arity across -- including which sorts each argument binds, so
binding structure is preserved on the nose rather than up to coherence.

The action on terms is indexed by a **context translation**: a morphism acts on
a term in context `Gamma` once told where each of `Gamma`'s variables goes.
That is the same shape renaming already has, and indeed the identity morphism
acting along a context translation *is* renaming. Indexing this way avoids
context-append transports under binders: under an argument binding `bs` the
translated body lives in `bs.map f ++ Delta`, which is exactly where the lifted
context translation lands, so no equation between `(bs ++ Gamma).map f` and
`bs.map f ++ Gamma.map f` is ever needed.

What is proved to travel forwards: renaming, substitution, hence plugging;
occurrence counts, hence the linearity of a chosen redex position; hence redex
positions themselves.  What is proved **not** to travel backwards: the carrier
of a position, because a morphism may collapse two sorts into one -- so the
distinction that makes the carrier extra input can be erased downstream even
though the position itself survives.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

/-! ## How a sort map acts on arities -/

/-- A sort map acts on one argument declaration: on the sorts the argument
binds, and on the sort the argument itself has. -/
def mapArity {A B : Type} (f : A → B) (a : List A × A) : List B × B := (a.1.map f, f a.2)

/-- A sort map acts on a whole arity. -/
def mapArities {A B : Type} (f : A → B) (as : List (List A × A)) : List (List B × B) :=
  as.map (mapArity f)

theorem mapSorts_id {A : Type} (l : List A) : l.map (fun s => s) = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ih]

theorem mapSorts_comp {A B C : Type} (f : A → B) (g : B → C) (l : List A) :
    (l.map f).map g = l.map (fun a => g (f a)) := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ih]

theorem mapArities_id {A : Type} (as : List (List A × A)) :
    mapArities (fun s => s) as = as := by
  induction as with
  | nil => rfl
  | cons _ _ ih =>
      simp only [mapArities, List.map_cons, mapArity, mapSorts_id, Prod.mk.eta] at ih ⊢
      rw [ih]

theorem mapArity_comp {A B C : Type} (f : A → B) (g : B → C) (a : List A × A) :
    mapArity g (mapArity f a) = mapArity (fun x => g (f x)) a := by
  simp only [mapArity, mapSorts_comp]

theorem mapArities_comp {A B C : Type} (f : A → B) (g : B → C) (as : List (List A × A)) :
    mapArities g (mapArities f as) = mapArities (fun a => g (f a)) as := by
  induction as with
  | nil => rfl
  | cons _ _ ih =>
      simp only [mapArities, List.map_cons, mapArity_comp] at ih ⊢
      rw [ih]

/-! ## The morphisms -/

/-- A **morphism of binding signatures**.  Sorts go to sorts, operators to
operators over the mapped sort, and every operator's arity is carried across --
so an argument that bound `bs` binds exactly `bs.map sortMap` downstream.

This is the strict operator-to-operator notion used by the action below.
It is not the most general interpretation of signatures: an operator can
instead be interpreted by a derived term or algebraic operation. Such an
interpretation needs its own substitution-compatible action and laws; it is
not supplied by this record. In particular, replacing a variadic operator
by a constructor over a sequence sort does not follow from `SigMor` alone. -/
structure SigMor (S T : Signature) where
  /-- Where each sort goes. -/
  sortMap : S.Srt → T.Srt
  /-- Where each operator goes.  Its result sort is forced. -/
  opMap : {s : S.Srt} → S.Op s → T.Op (sortMap s)
  /-- Binding structure is preserved on the nose. -/
  carriesArity : ∀ {s : S.Srt} (o : S.Op s),
    T.arity (opMap o) = mapArities sortMap (S.arity o)

variable {S T U : Signature}

/-- The identity morphism.  Reducible, so that `(SigMor.ident S).sortMap` is the
identity function to the elaborator and not merely propositionally equal to it. -/
@[reducible] def SigMor.ident (S : Signature) : SigMor S S where
  sortMap := fun s => s
  opMap := fun o => o
  carriesArity := fun o => (mapArities_id (S.arity o)).symm

/-- Morphisms compose.  Reducible for the same reason as `SigMor.ident`. -/
@[reducible] def SigMor.comp (F : SigMor S T) (G : SigMor T U) : SigMor S U where
  sortMap := fun s => G.sortMap (F.sortMap s)
  opMap := fun o => G.opMap (F.opMap o)
  carriesArity := fun o => by
    rw [G.carriesArity (F.opMap o), F.carriesArity o, mapArities_comp]

/-! ## Context translations -/

/-- A **context translation** along a sort map: where each variable of `Gamma`
goes in `Delta`.  With `f` the identity this is exactly a renaming. -/
abbrev VarMap {A B : Type} (f : A → B) (Γ : List A) (Δ : List B) : Type :=
  (s : A) → Var Γ s → Var Δ (f s)

/-- The canonical context translation: mapping the context pointwise keeps
every variable at its own position. -/
def mapVar {A B : Type} (f : A → B) : {Γ : List A} → (s : A) →
    Var Γ s → Var (Γ.map f) (f s)
  | _, _, .zero => .zero
  | _, _, .succ x => .succ (mapVar f _ x)

/-- Lift a context translation under the sorts bound by one argument.  The
translated binders are `bs.map f`, which is precisely the prefix the translated
body needs. Operator arities still use the explicit casts supplied by
`carriesArity`. -/
def liftVarMap {A B : Type} (f : A → B) {Γ : List A} {Δ : List B} (ν : VarMap f Γ Δ) :
    (bs : List A) → (s : A) → Var (bs ++ Γ) s → Var (bs.map f ++ Δ) (f s)
  | [], s, x => ν s x
  | _ :: _, _, .zero => .zero
  | _ :: bs, s, .succ w => .succ (liftVarMap f ν bs s w)

/-! ## The action on terms -/

mutual
/-- A morphism acts on a term along a context translation. -/
def mapTerm (F : SigMor S T) : {Γ : Ctx S} → {Δ : Ctx T} → VarMap F.sortMap Γ Δ →
    {s : S.Srt} → Term S Γ s → Term T Δ (F.sortMap s)
  | _, _, ν, _, .var x => .var (ν _ x)
  | _, _, ν, _, .op o args =>
      Term.op (S := T) (F.opMap o)
        (castArgsArity (T := T) (F.carriesArity o).symm (mapArgs F ν args))

def mapArgs (F : SigMor S T) : {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} → {Δ : Ctx T} →
    VarMap F.sortMap Γ Δ → Args S as Γ → Args T (mapArities F.sortMap as) Δ
  | _, _, _, _, .nil => .nil
  | _, _, _, ν, .cons (bs := bs) hd tl =>
      .cons (mapTerm F (liftVarMap F.sortMap ν bs) hd) (mapArgs F ν tl)
end

/-- The action along the canonical context translation. -/
abbrev SigMor.onTerm (F : SigMor S T) {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s) :
    Term T (Γ.map F.sortMap) (F.sortMap s) :=
  mapTerm F (mapVar F.sortMap) t

/-! ## Moving arities along an equation

Three small transport lemmas.  Each is stated over *variable* arity lists, so
`subst` discharges it; the uses below instantiate them at arities that are not
variables, where the transport could not be eliminated in place. -/

theorem bindArgs_castArgsArity {as bs : List (List T.Srt × T.Srt)} (h : as = bs)
    {Γ Δ : Ctx T} (tau : Sub T Γ Δ) (a : Args T as Γ) :
    bindArgs tau (castArgsArity (T := T) h a)
      = castArgsArity (T := T) h (bindArgs tau a) := by
  subst h; rfl

theorem renameArgs_castArgsArity {as bs : List (List T.Srt × T.Srt)} (h : as = bs)
    {Γ Δ : Ctx T} (rho : Ren T Γ Δ) (a : Args T as Γ) :
    renameArgs rho (castArgsArity (T := T) h a)
      = castArgsArity (T := T) h (renameArgs rho a) := by
  subst h; rfl

theorem countVarArgs_castArgsArity {as bs : List (List T.Srt × T.Srt)} (h : as = bs)
    {Γ : Ctx T} {c : T.Srt} (x : Var Γ c) (a : Args T as Γ) :
    countVarArgs x (castArgsArity (T := T) h a) = countVarArgs x a := by
  subst h; rfl

theorem castArgsArity_trans {as bs cs : List (List T.Srt × T.Srt)} (h : as = bs) (h' : bs = cs)
    {Γ : Ctx T} (a : Args T as Γ) :
    castArgsArity (T := T) h' (castArgsArity (T := T) h a)
      = castArgsArity (T := T) (h.trans h') a := by
  subst h; subst h'; rfl

theorem castArgsArity_cons {bs bs' : List T.Srt} {s : T.Srt}
    {as as' : List (List T.Srt × T.Srt)} {Γ : Ctx T}
    (hb : bs = bs') (has : as = as') (hd : Term T (bs ++ Γ) s) (tl : Args T as Γ) :
    castArgsArity (T := T) (congrArg₂ (fun b a => (b, s) :: a) hb has) (Args.cons hd tl)
      = Args.cons (castTermCtx (T := T) (congrArg (· ++ Γ) hb) hd)
          (castArgsArity (T := T) has tl) := by
  subst hb; subst has; rfl

/-! ## The action does not depend on more than the translation's values -/

theorem mapTerm_congr (F : SigMor S T) {Γ : Ctx S} {Δ : Ctx T} (ν ν' : VarMap F.sortMap Γ Δ)
    (h : ∀ (s : S.Srt) (x : Var Γ s), ν s x = ν' s x) {s : S.Srt} (t : Term S Γ s) :
    mapTerm F ν t = mapTerm F ν' t := by
  have hνν : ν = ν' := by funext r y; exact h r y
  rw [hνν]

/-- Equality of signature morphisms also transports the dependent variable
map required by their action on intrinsic terms. Heterogeneous equality is
necessary because both the variable-map and result-sort types mention the
morphism's sort map. -/
theorem mapTerm_heq_of_morphism_eq
    (first second : SigMor S T) (same : first = second)
    {Γ : Ctx S} {Δ : Ctx T} {sort : S.Srt}
    (firstVariables : VarMap first.sortMap Γ Δ)
    (secondVariables : VarMap second.sortMap Γ Δ)
    (sameVariables : HEq firstVariables secondVariables)
    (term : Term S Γ sort) :
    HEq (mapTerm first firstVariables term)
      (mapTerm second secondVariables term) := by
  cases same
  cases sameVariables
  rfl

#print axioms mapTerm_heq_of_morphism_eq

theorem mapArgs_congr (F : SigMor S T) {Γ : Ctx S} {Δ : Ctx T} (ν ν' : VarMap F.sortMap Γ Δ)
    (h : ∀ (s : S.Srt) (x : Var Γ s), ν s x = ν' s x)
    {as : List (List S.Srt × S.Srt)} (args : Args S as Γ) :
    mapArgs F ν args = mapArgs F ν' args := by
  have hνν : ν = ν' := by funext r y; exact h r y
  rw [hνν]

/-! ## Moving variables along an equation of contexts -/

/-- Move a variable along an equality of contexts. -/
def castVarCtx {A : Type} {Γ Δ : List A} (h : Γ = Δ) {s : A} (x : Var Γ s) : Var Δ s := h ▸ x

theorem castVarCtx_zero {A : Type} {Γ Δ : List A} (h : Γ = Δ) {s : A} :
    castVarCtx (congrArg (fun l => s :: l) h) (Var.zero : Var (s :: Γ) s) = Var.zero := by
  subst h; rfl

theorem castVarCtx_succ {A : Type} {Γ Δ : List A} (h : Γ = Δ) {s t : A} (x : Var Γ s) :
    castVarCtx (congrArg (fun l => t :: l) h) (Var.succ (t := t) x) = Var.succ (castVarCtx h x) := by
  subst h; rfl

theorem castArgsArity_self {as : List (List T.Srt × T.Srt)} (h : as = as) {Γ : Ctx T}
    (a : Args T as Γ) : castArgsArity (T := T) h a = a := rfl

theorem rename_castVarCtx {Γ Δ Δ' : Ctx S} (h : Δ = Δ') (rho : Ren S Γ Δ) {s : S.Srt}
    (t : Term S Γ s) :
    rename (fun r x => castVarCtx h (rho r x)) t = castTermCtx (T := S) h (rename rho t) := by
  subst h; rfl

theorem mapTerm_castVarCtx (F : SigMor S T) {Γ : Ctx S} {Δ Δ' : Ctx T} (h : Δ = Δ')
    (ν : VarMap F.sortMap Γ Δ) {s : S.Srt} (t : Term S Γ s) :
    mapTerm F (fun r x => castVarCtx h (ν r x)) t = castTermCtx (T := T) h (mapTerm F ν t) := by
  subst h; rfl

theorem mapArgs_castArgsArity (G : SigMor T U) {as bs : List (List T.Srt × T.Srt)} (h : as = bs)
    {Γ : Ctx T} {Δ : Ctx U} (ν : VarMap G.sortMap Γ Δ) (a : Args T as Γ) :
    mapArgs G ν (castArgsArity (T := T) h a)
      = castArgsArity (T := U) (congrArg (mapArities G.sortMap) h) (mapArgs G ν a) := by
  subst h; rfl

/-! ## Lifting a context translation is functorial -/

theorem liftVarMap_ident {A : Type} {Γ Δ : List A} (ν : (s : A) → Var Γ s → Var Δ s) :
    ∀ (bs : List A) (s : A) (x : Var (bs ++ Γ) s),
      liftVarMap (fun s => s) ν bs s x
        = castVarCtx (congrArg (fun l => l ++ Δ) (mapSorts_id bs).symm) (liftRen ν bs s x)
  | [], _, _ => rfl
  | b :: bs, s, x => by
      cases x with
      | zero =>
          exact (castVarCtx_zero (s := b)
            (congrArg (fun l => l ++ Δ) (mapSorts_id bs).symm)).symm
      | succ w =>
          rw [show liftVarMap (fun s => s) ν (b :: bs) s (Var.succ w)
                = Var.succ (liftVarMap (fun s => s) ν bs s w) from rfl,
            liftVarMap_ident ν bs s w]
          exact (castVarCtx_succ (t := b)
            (congrArg (fun l => l ++ Δ) (mapSorts_id bs).symm) _).symm

theorem liftVarMap_comp {A B C : Type} (f : A → B) (g : B → C) {Γ : List A} {Δ : List B}
    {Θ : List C} (ν : VarMap f Γ Δ) (ν' : VarMap g Δ Θ) :
    ∀ (bs : List A) (s : A) (x : Var (bs ++ Γ) s),
      liftVarMap g ν' (bs.map f) (f s) (liftVarMap f ν bs s x)
        = castVarCtx (congrArg (fun l => l ++ Θ) (mapSorts_comp f g bs).symm)
            (liftVarMap (fun a => g (f a)) (fun r y => ν' (f r) (ν r y)) bs s x)
  | [], _, _ => rfl
  | b :: bs, s, x => by
      cases x with
      | zero =>
          exact (castVarCtx_zero (s := g (f b))
            (congrArg (fun l => l ++ Θ) (mapSorts_comp f g bs).symm)).symm
      | succ w =>
          rw [show liftVarMap g ν' ((b :: bs).map f) (f s) (liftVarMap f ν (b :: bs) s (Var.succ w))
                = Var.succ (liftVarMap g ν' (bs.map f) (f s) (liftVarMap f ν bs s w)) from rfl,
            liftVarMap_comp f g ν ν' bs s w]
          exact (castVarCtx_succ (t := g (f b))
            (congrArg (fun l => l ++ Θ) (mapSorts_comp f g bs).symm) _).symm

/-! ## Signatures form a category and terms are a functor on it

The identity morphism, acting along a context translation, is renaming: so
renaming is not a separate notion bolted onto the syntax, it is what the
identity change of signature does. -/

mutual
theorem mapTerm_ident : ∀ {Γ Δ : Ctx S} (ν : Ren S Γ Δ) {s : S.Srt} (t : Term S Γ s),
    mapTerm (SigMor.ident S) ν t = rename ν t
  | _, _, _, _, .var _ => rfl
  | _, _, ν, _, .op o args => by
      rw [show mapTerm (SigMor.ident S) ν (Term.op o args)
            = Term.op (S := S) o (castArgsArity (T := S) ((SigMor.ident S).carriesArity o).symm
                (mapArgs (SigMor.ident S) ν args)) from rfl,
        mapArgs_ident ν args, castArgsArity_trans, castArgsArity_self]
      rfl

theorem mapArgs_ident : ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S} (ν : Ren S Γ Δ)
    (args : Args S as Γ),
    mapArgs (SigMor.ident S) ν args
      = castArgsArity (T := S) (mapArities_id as).symm (renameArgs ν args)
  | _, _, _, _, .nil => rfl
  | _, _, _, ν, .cons (bs := bs) hd tl => by
      rw [show mapArgs (SigMor.ident S) ν (Args.cons hd tl)
            = Args.cons (mapTerm (SigMor.ident S) (liftVarMap (fun s => s) ν bs) hd)
                (mapArgs (SigMor.ident S) ν tl) from rfl,
        mapTerm_congr (SigMor.ident S) _ _ (liftVarMap_ident ν bs) hd,
        mapTerm_ident _ hd, rename_castVarCtx, mapArgs_ident ν tl]
      exact (castArgsArity_cons (mapSorts_id bs).symm (mapArities_id _).symm _ _).symm
end

mutual
theorem mapTerm_comp (F : SigMor S T) (G : SigMor T U) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} {Θ : Ctx U} (ν : VarMap F.sortMap Γ Δ) (ν' : VarMap G.sortMap Δ Θ)
      {s : S.Srt} (t : Term S Γ s),
      mapTerm G ν' (mapTerm F ν t)
        = mapTerm (F.comp G) (fun r y => ν' (F.sortMap r) (ν r y)) t
  | _, _, _, _, _, _, .var _ => rfl
  | _, _, _, ν, ν', _, .op o args => by
      rw [show mapTerm F ν (Term.op o args)
            = Term.op (S := T) (F.opMap o) (castArgsArity (T := T) (F.carriesArity o).symm
                (mapArgs F ν args)) from rfl,
        show mapTerm G ν' (Term.op (S := T) (F.opMap o)
                (castArgsArity (T := T) (F.carriesArity o).symm (mapArgs F ν args)))
            = Term.op (S := U) (G.opMap (F.opMap o))
                (castArgsArity (T := U) (G.carriesArity (F.opMap o)).symm
                  (mapArgs G ν' (castArgsArity (T := T) (F.carriesArity o).symm
                    (mapArgs F ν args)))) from rfl,
        mapArgs_castArgsArity, castArgsArity_trans, mapArgs_comp F G ν ν' args,
        castArgsArity_trans]
      rfl

theorem mapArgs_comp (F : SigMor S T) (G : SigMor T U) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} {Θ : Ctx U} (ν : VarMap F.sortMap Γ Δ) (ν' : VarMap G.sortMap Δ Θ)
      {as : List (List S.Srt × S.Srt)} (args : Args S as Γ),
      mapArgs G ν' (mapArgs F ν args)
        = castArgsArity (T := U) (mapArities_comp F.sortMap G.sortMap as).symm
            (mapArgs (F.comp G) (fun r y => ν' (F.sortMap r) (ν r y)) args)
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, ν, ν', _, .cons (bs := bs) hd tl => by
      rw [show mapArgs G ν' (mapArgs F ν (Args.cons hd tl))
            = Args.cons (mapTerm G (liftVarMap G.sortMap ν' (bs.map F.sortMap))
                (mapTerm F (liftVarMap F.sortMap ν bs) hd))
                (mapArgs G ν' (mapArgs F ν tl)) from rfl,
        mapTerm_comp F G _ _ hd,
        mapTerm_congr (F.comp G) _ _ (liftVarMap_comp F.sortMap G.sortMap ν ν' bs) hd,
        mapTerm_castVarCtx, mapArgs_comp F G ν ν' tl]
      exact (castArgsArity_cons (mapSorts_comp F.sortMap G.sortMap bs).symm
        (mapArities_comp F.sortMap G.sortMap _).symm _ _).symm
end

/-! ## Renaming travels

A context translation absorbs a renaming on either side.  Both statements are
transport-free, which is the payoff of indexing the action by a translation
rather than by an equation between contexts. -/

theorem liftVarMap_liftRen {A B : Type} (f : A → B) {Γ Γ' : List A} {Δ : List B}
    (ν : VarMap f Γ' Δ) (rho : (s : A) → Var Γ s → Var Γ' s) :
    ∀ (bs : List A) (s : A) (x : Var (bs ++ Γ) s),
      liftVarMap f ν bs s (liftRen rho bs s x)
        = liftVarMap f (fun r y => ν r (rho r y)) bs s x
  | [], _, _ => rfl
  | b :: bs, s, x => by
      cases x with
      | zero => rfl
      | succ w =>
          show Var.succ (liftVarMap f ν bs s (liftRen rho bs s w)) = _
          rw [liftVarMap_liftRen f ν rho bs s w]
          rfl

theorem liftRen_liftVarMap {A B : Type} (f : A → B) {Γ : List A} {Δ Δ' : List B}
    (ν : VarMap f Γ Δ) (rho : (s : B) → Var Δ s → Var Δ' s) :
    ∀ (bs : List A) (s : A) (x : Var (bs ++ Γ) s),
      liftRen rho (bs.map f) (f s) (liftVarMap f ν bs s x)
        = liftVarMap f (fun r y => rho (f r) (ν r y)) bs s x
  | [], _, _ => rfl
  | b :: bs, s, x => by
      cases x with
      | zero => rfl
      | succ w =>
          show Var.succ (liftRen rho (bs.map f) (f s) (liftVarMap f ν bs s w)) = _
          rw [liftRen_liftVarMap f ν rho bs s w]
          rfl

mutual
theorem mapTerm_rename (F : SigMor S T) :
    ∀ {Γ Γ' : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ' Δ) (rho : Ren S Γ Γ')
      {s : S.Srt} (t : Term S Γ s),
      mapTerm F ν (rename rho t) = mapTerm F (fun r y => ν r (rho r y)) t
  | _, _, _, _, _, _, .var _ => rfl
  | _, _, _, ν, rho, _, .op o args => by
      show Term.op (S := T) (F.opMap o) (castArgsArity (T := T) (F.carriesArity o).symm
          (mapArgs F ν (renameArgs rho args))) = _
      rw [mapArgs_rename F ν rho args]
      rfl

theorem mapArgs_rename (F : SigMor S T) :
    ∀ {Γ Γ' : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ' Δ) (rho : Ren S Γ Γ')
      {as : List (List S.Srt × S.Srt)} (args : Args S as Γ),
      mapArgs F ν (renameArgs rho args) = mapArgs F (fun r y => ν r (rho r y)) args
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, ν, rho, _, .cons (bs := bs) hd tl => by
      show Args.cons (mapTerm F (liftVarMap F.sortMap ν bs) (rename (liftRen rho bs) hd))
          (mapArgs F ν (renameArgs rho tl)) = _
      rw [mapTerm_rename F _ (liftRen rho bs) hd,
        mapTerm_congr F _ _ (liftVarMap_liftRen F.sortMap ν rho bs) hd,
        mapArgs_rename F ν rho tl]
      rfl
end

mutual
theorem rename_mapTerm (F : SigMor S T) :
    ∀ {Γ : Ctx S} {Δ Δ' : Ctx T} (ν : VarMap F.sortMap Γ Δ) (rho : Ren T Δ Δ')
      {s : S.Srt} (t : Term S Γ s),
      rename rho (mapTerm F ν t) = mapTerm F (fun r y => rho (F.sortMap r) (ν r y)) t
  | _, _, _, _, _, _, .var _ => rfl
  | _, _, _, ν, rho, _, .op o args => by
      show Term.op (S := T) (F.opMap o) (renameArgs rho (castArgsArity (T := T)
          (F.carriesArity o).symm (mapArgs F ν args))) = _
      rw [renameArgs_castArgsArity, renameArgs_mapArgs F ν rho args]
      rfl

theorem renameArgs_mapArgs (F : SigMor S T) :
    ∀ {Γ : Ctx S} {Δ Δ' : Ctx T} (ν : VarMap F.sortMap Γ Δ) (rho : Ren T Δ Δ')
      {as : List (List S.Srt × S.Srt)} (args : Args S as Γ),
      renameArgs rho (mapArgs F ν args) = mapArgs F (fun r y => rho (F.sortMap r) (ν r y)) args
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, ν, rho, _, .cons (bs := bs) hd tl => by
      show Args.cons (rename (liftRen rho (bs.map F.sortMap))
          (mapTerm F (liftVarMap F.sortMap ν bs) hd)) (renameArgs rho (mapArgs F ν tl)) = _
      rw [rename_mapTerm F _ (liftRen rho (bs.map F.sortMap)) hd,
        mapTerm_congr F _ _ (liftRen_liftVarMap F.sortMap ν rho bs) hd,
        renameArgs_mapArgs F ν rho tl]
      rfl
end

/-! ## Substitution travels

A morphism carries a substitution to any substitution downstream that agrees
with it on the translated variables.  Stating the compatibility pointwise --
rather than pushing the substitution forward -- is what lets the sort map be
non-injective: there is nothing to invert. -/

theorem liftSub_compat (F : SigMor S T) {Γ Γ' : Ctx S} {Δ Δ' : Ctx T}
    (ν : VarMap F.sortMap Γ Δ') (ν' : VarMap F.sortMap Γ' Δ)
    (sigma : Sub S Γ Γ') (tau : Sub T Δ' Δ)
    (hc : ∀ (s : S.Srt) (x : Var Γ s), tau (F.sortMap s) (ν s x) = mapTerm F ν' (sigma s x)) :
    ∀ (bs : List S.Srt) (s : S.Srt) (x : Var (bs ++ Γ) s),
      liftSub tau (bs.map F.sortMap) (F.sortMap s) (liftVarMap F.sortMap ν bs s x)
        = mapTerm F (liftVarMap F.sortMap ν' bs) (liftSub sigma bs s x)
  | [], s, x => hc s x
  | b :: bs, s, x => by
      cases x with
      | zero => rfl
      | succ w =>
          show weaken (liftSub tau (bs.map F.sortMap) (F.sortMap s)
              (liftVarMap F.sortMap ν bs s w)) = _
          rw [liftSub_compat F ν ν' sigma tau hc bs s w]
          show rename (fun _ v => Var.succ v)
              (mapTerm F (liftVarMap F.sortMap ν' bs) (liftSub sigma bs s w))
            = mapTerm F (liftVarMap F.sortMap ν' (b :: bs))
                (rename (fun _ v => Var.succ v) (liftSub sigma bs s w))
          rw [rename_mapTerm F, mapTerm_rename F]
          exact mapTerm_congr F _ _ (fun _ _ => rfl) _

mutual
theorem mapTerm_bind (F : SigMor S T) :
    ∀ {Γ Γ' : Ctx S} {Δ Δ' : Ctx T} (ν : VarMap F.sortMap Γ Δ') (ν' : VarMap F.sortMap Γ' Δ)
      (sigma : Sub S Γ Γ') (tau : Sub T Δ' Δ)
      (_ : ∀ (r : S.Srt) (x : Var Γ r), tau (F.sortMap r) (ν r x) = mapTerm F ν' (sigma r x))
      {s : S.Srt} (t : Term S Γ s),
      mapTerm F ν' (bind sigma t) = bind tau (mapTerm F ν t)
  | _, _, _, _, ν, ν', sigma, tau, hc, _, .var x => (hc _ x).symm
  | _, _, _, _, ν, ν', sigma, tau, hc, _, .op o args => by
      show Term.op (S := T) (F.opMap o) (castArgsArity (T := T) (F.carriesArity o).symm
          (mapArgs F ν' (bindArgs sigma args)))
        = bind tau (Term.op (S := T) (F.opMap o) (castArgsArity (T := T)
            (F.carriesArity o).symm (mapArgs F ν args)))
      rw [show bind tau (Term.op (S := T) (F.opMap o) (castArgsArity (T := T)
              (F.carriesArity o).symm (mapArgs F ν args)))
            = Term.op (S := T) (F.opMap o) (bindArgs tau (castArgsArity (T := T)
                (F.carriesArity o).symm (mapArgs F ν args))) from rfl,
        bindArgs_castArgsArity, mapArgs_bind F ν ν' sigma tau hc args]

theorem mapArgs_bind (F : SigMor S T) :
    ∀ {Γ Γ' : Ctx S} {Δ Δ' : Ctx T} (ν : VarMap F.sortMap Γ Δ') (ν' : VarMap F.sortMap Γ' Δ)
      (sigma : Sub S Γ Γ') (tau : Sub T Δ' Δ)
      (_ : ∀ (r : S.Srt) (x : Var Γ r), tau (F.sortMap r) (ν r x) = mapTerm F ν' (sigma r x))
      {as : List (List S.Srt × S.Srt)} (args : Args S as Γ),
      mapArgs F ν' (bindArgs sigma args) = bindArgs tau (mapArgs F ν args)
  | _, _, _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, ν, ν', sigma, tau, hc, _, .cons (bs := bs) hd tl => by
      show Args.cons (mapTerm F (liftVarMap F.sortMap ν' bs) (bind (liftSub sigma bs) hd))
          (mapArgs F ν' (bindArgs sigma tl)) = _
      rw [mapTerm_bind F (liftVarMap F.sortMap ν bs) (liftVarMap F.sortMap ν' bs)
            (liftSub sigma bs) (liftSub tau (bs.map F.sortMap))
            (liftSub_compat F ν ν' sigma tau hc bs) hd,
        mapArgs_bind F ν ν' sigma tau hc tl]
      rfl
end

/-- **Plugging travels.**  A morphism carries a one-hole context and the term in
its hole to a one-hole context and the term in its hole. -/
theorem mapTerm_inst (F : SigMor S T) {Γ : Ctx S} {c s : S.Srt}
    (K : Term S (c :: Γ) s) (t : Term S Γ c) :
    F.onTerm (inst K t) = inst (F.onTerm K) (F.onTerm t) := by
  refine mapTerm_bind F (mapVar F.sortMap) (mapVar F.sortMap) (extend t)
    (extend (F.onTerm t)) ?_ K
  intro r x
  cases x with
  | zero => rfl
  | succ w => rfl

/-! ## Occurrence counts travel, so a position stays linear

A context translation that separates variables the way the source does carries
occurrence counts across unchanged.  The canonical translation does separate
them, because it keeps every variable at its own position. -/

theorem sameVar_mapVar (F : SigMor S T) : ∀ {Γ : Ctx S} {c r : S.Srt}
    (x : Var Γ c) (y : Var Γ r),
    sameVar (S := T) (mapVar F.sortMap c x) (mapVar F.sortMap r y) = sameVar (S := S) x y
  | _, _, _, .zero, .zero => rfl
  | _, _, _, .zero, .succ _ => rfl
  | _, _, _, .succ _, .zero => rfl
  | _, _, _, .succ x, .succ y => sameVar_mapVar F x y

theorem liftVarMap_weakenVar (F : SigMor S T) {Γ : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ Δ) :
    ∀ (bs : List S.Srt) {c : S.Srt} (x : Var Γ c),
      liftVarMap F.sortMap ν bs c (weakenVar (S := S) bs x)
        = weakenVar (S := T) (bs.map F.sortMap) (ν c x)
  | [], _, _ => rfl
  | _ :: bs, c, x => by
      show Var.succ (liftVarMap F.sortMap ν bs c (weakenVar (S := S) bs x)) = _
      rw [liftVarMap_weakenVar F ν bs x]
      rfl

theorem sameVar_lift (F : SigMor S T) {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ)
    {c : S.Srt} (x : Var Γ c)
    (hν : ∀ (r : S.Srt) (y : Var Γ r),
      sameVar (S := T) (ν c x) (ν r y) = sameVar (S := S) x y) :
    ∀ (bs : List S.Srt) (r : S.Srt) (y : Var (bs ++ Γ) r),
      sameVar (S := T) (liftVarMap F.sortMap ν bs c (weakenVar (S := S) bs x))
          (liftVarMap F.sortMap ν bs r y)
        = sameVar (S := S) (weakenVar (S := S) bs x) y
  | [], r, y => hν r y
  | _ :: bs, r, y => by
      cases y with
      | zero => rfl
      | succ w => exact sameVar_lift F ν x hν bs r w

mutual
theorem countVar_mapTerm (F : SigMor S T) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ) {c : S.Srt} (x : Var Γ c)
      (_ : ∀ (r : S.Srt) (y : Var Γ r),
        sameVar (S := T) (ν c x) (ν r y) = sameVar (S := S) x y)
      {s : S.Srt} (t : Term S Γ s),
      countVar (ν c x) (mapTerm F ν t) = countVar x t
  | _, _, ν, _, x, hν, _, .var y => by
      show (if sameVar (S := T) (ν _ x) (ν _ y) then 1 else 0) = _
      rw [hν]
      rfl
  | _, _, ν, _, x, hν, _, .op o args => by
      show countVarArgs (ν _ x) (castArgsArity (T := T) (F.carriesArity o).symm
          (mapArgs F ν args)) = _
      rw [countVarArgs_castArgsArity, countVarArgs_mapArgs F ν x hν args]
      rfl

theorem countVarArgs_mapArgs (F : SigMor S T) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ) {c : S.Srt} (x : Var Γ c)
      (_ : ∀ (r : S.Srt) (y : Var Γ r),
        sameVar (S := T) (ν c x) (ν r y) = sameVar (S := S) x y)
      {as : List (List S.Srt × S.Srt)} (args : Args S as Γ),
      countVarArgs (ν c x) (mapArgs F ν args) = countVarArgs x args
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, ν, _, x, hν, _, .cons (bs := bs) hd tl => by
      show countVar (weakenVar (S := T) (bs.map F.sortMap) (ν _ x))
            (mapTerm F (liftVarMap F.sortMap ν bs) hd)
          + countVarArgs (ν _ x) (mapArgs F ν tl) = _
      rw [← liftVarMap_weakenVar F ν bs x,
        countVar_mapTerm F (liftVarMap F.sortMap ν bs) (weakenVar (S := S) bs x)
          (sameVar_lift F ν x hν bs) hd,
        countVarArgs_mapArgs F ν x hν tl]
      rfl
end

/-- **The hole is still used exactly as often.** -/
theorem holeCount_mapTerm (F : SigMor S T) {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s) :
    holeCount (F.onTerm K) = holeCount K :=
  countVar_mapTerm F (mapVar F.sortMap) (Var.zero : Var (c :: Γ) c)
    (fun _ y => sameVar_mapVar F Var.zero y) K

/-! ## What the generator reads travels

A redex position is a factorisation, and both halves of the factorisation
travel, so the position does.  Note what this says and does not say: the
transport is *total* on positions, in contrast with carrying a position along
an instantiation, which is partial because a body may discard its argument and
erase the hole. -/

/-- A chosen occurrence in the source is a chosen occurrence downstream. -/
def SigMor.onPosition (F : SigMor S T) {Γ : Ctx S} {s : S.Srt} {L : Term S Γ s}
    (P : LinearRedexPosition S Γ s L) :
    LinearRedexPosition T (Γ.map F.sortMap) (F.sortMap s) (F.onTerm L) where
  carrier := F.sortMap P.carrier
  ctxt := F.onTerm P.ctxt
  redex := F.onTerm P.redex
  plugs := (mapTerm_inst F P.ctxt P.redex).symm.trans
    (congrArg (fun u => F.onTerm u) P.plugs)
  linear := (holeCount_mapTerm F P.ctxt).trans P.linear

/-- The generator's whole input travels: rule, both sides, and the chosen
occurrence inside the left-hand side. -/
def SigMor.onRewrite (F : SigMor S T) (P : PositionedRewrite S) : PositionedRewrite T where
  ctx := P.ctx.map F.sortMap
  sort := F.sortMap P.sort
  lhs := F.onTerm P.lhs
  rhs := F.onTerm P.rhs
  position := F.onPosition P.position

/-- The carrier of the transported rule is the transported carrier: the sort at
which the generated modality sits moves the way the sorts move. -/
theorem SigMor.onRewrite_carrier (F : SigMor S T) (P : PositionedRewrite S) :
    (F.onRewrite P).carrier = F.sortMap P.carrier := rfl

/-! ## Adjoining metavariables is a morphism

The embedding of a signature into the one with metavariables adjoined is a
signature morphism, and the embedding already in use is exactly its action.  So
the two notions are one notion, not two. -/

/-- Adjoining metavariables, as a morphism.  Reducible for the same reason as
`SigMor.ident`. -/
@[reducible] def metaInclusion (S : Signature) (M : List (MetaArity S)) : SigMor S (withMetas S M) where
  sortMap := fun s => s
  opMap := fun o => Sum.inl o
  carriesArity := fun o => (mapArities_id (S.arity o)).symm

theorem embed_castTermCtx {M : List (MetaArity S)} {Γ Δ : Ctx S} (h : Γ = Δ) {s : S.Srt}
    (t : Term S Γ s) :
    embed (M := M) (castTermCtx (T := S) h t)
      = castTermCtx (T := withMetas S M) h (embed (M := M) t) := by
  subst h; rfl

mutual
/-- **`embed` is the action of the inclusion morphism.** -/
theorem mapTerm_metaInclusion {M : List (MetaArity S)} :
    ∀ {Γ Δ : Ctx S} (ν : Ren S Γ Δ) {s : S.Srt} (t : Term S Γ s),
      mapTerm (metaInclusion S M) ν t = embed (M := M) (rename ν t)
  | _, _, _, _, .var _ => rfl
  | _, _, ν, _, .op o args => by
      show Term.op (S := withMetas S M) (Sum.inl o)
          (castArgsArity (T := withMetas S M) ((metaInclusion S M).carriesArity o).symm
            (mapArgs (metaInclusion S M) ν args)) = _
      rw [mapArgs_metaInclusion ν args, castArgsArity_trans, castArgsArity_self]
      rfl

theorem mapArgs_metaInclusion {M : List (MetaArity S)} :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S} (ν : Ren S Γ Δ) (args : Args S as Γ),
      mapArgs (metaInclusion S M) ν args
        = castArgsArity (T := withMetas S M) (mapArities_id as).symm
            (embedArgs (M := M) (renameArgs ν args))
  | _, _, _, _, .nil => rfl
  | _, _, _, ν, .cons (bs := bs) hd tl => by
      show Args.cons (mapTerm (metaInclusion S M) (liftVarMap (fun s => s) ν bs) hd)
          (mapArgs (metaInclusion S M) ν tl) = _
      rw [mapTerm_congr (metaInclusion S M) _ _ (liftVarMap_ident ν bs) hd,
        mapTerm_metaInclusion _ hd, rename_castVarCtx, embed_castTermCtx,
        mapArgs_metaInclusion ν tl]
      exact (castArgsArity_cons (T := withMetas S M) (mapSorts_id bs).symm
        (mapArities_id _).symm (embed (M := M) (rename (liftRen ν bs) hd))
        (embedArgs (M := M) (renameArgs ν tl))).symm
end

/-- Acting by the inclusion along the identity translation *is* `embed`. -/
theorem onTerm_metaInclusion {M : List (MetaArity S)} {Γ : Ctx S} {s : S.Srt}
    (t : Term S Γ s) :
    mapTerm (metaInclusion S M) (fun _ y => y) t = embed (M := M) t := by
  rw [mapTerm_metaInclusion (fun _ y => y) t, rename_id]

/-! ## What does not travel backwards

Two controls.  The first shows that a morphism may erase the very distinction
that makes the redex position extra input: the two positions of one left-hand
side whose carriers are different sorts have, downstream, the same carrier --
while remaining different positions.  So the transport is forward-only, and a
construction that reads the carrier after the collapse cannot recover which
occurrence was chosen.

The second shows that a morphism need not be faithful, so nothing downstream
may be read back as a statement about the source. -/

namespace SortCollapse

open RedexPositionWitness

/-- One sort, where the source had two. -/
inductive OneSrt where
  | all
  deriving DecidableEq

/-- The same two operators, now over that single sort. -/
inductive OneOp : OneSrt → Type where
  | out : OneOp OneSrt.all
  | aName : OneOp OneSrt.all

abbrev osig : Signature where
  Srt := OneSrt
  Op := OneOp
  arity := fun {_} o => match o with
    | .out => [([], OneSrt.all), ([], OneSrt.all)]
    | .aName => []

/-- Forgetting that names and processes are different sorts.  The arity
condition still holds: `out` still takes two non-binding arguments. -/
def collapse : SigMor sig osig where
  sortMap := fun _ => OneSrt.all
  opMap := fun {_} o => match o with
    | .out => OneOp.out
    | .aName => OneOp.aName
  carriesArity := by
    intro _ o
    cases o <;> rfl

/-- The action computes: the left-hand side arrives as the term it should. -/
theorem collapsed_lhs :
    collapse.onTerm lhs
      = Term.op (S := osig) OneOp.out
          (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)) := rfl

/-- The name position, carried across. -/
def nameCollapsed : LinearRedexPosition osig (G.map collapse.sortMap)
    (collapse.sortMap Srt.pr) (collapse.onTerm lhs) :=
  collapse.onPosition nameLinear

/-- The process position, carried across. -/
def procCollapsed : LinearRedexPosition osig (G.map collapse.sortMap)
    (collapse.sortMap Srt.pr) (collapse.onTerm lhs) :=
  collapse.onPosition procLinear

/-- **The carrier is not reflected.**  Upstream the two positions have
different carriers -- that was the obstruction to the generator's input being a
function of the rule.  Downstream of a sort collapse they have the same
carrier, so the obstruction is invisible there. -/
theorem carrier_not_reflected :
    nameLinear.carrier ≠ procLinear.carrier
      ∧ nameCollapsed.carrier = procCollapsed.carrier :=
  ⟨carrier_not_determined_by_lhs, rfl⟩

/-- **Only the carrier merges.**  The transported positions are still two
different positions: their one-hole contexts use different variables. -/
theorem transported_contexts_differ : nameCollapsed.ctxt ≠ procCollapsed.ctxt := by
  intro h
  have hn : countVar (Var.succ Var.zero :
      Var (OneSrt.all :: G.map collapse.sortMap) OneSrt.all) nameCollapsed.ctxt = 0 := rfl
  have hp : countVar (Var.succ Var.zero :
      Var (OneSrt.all :: G.map collapse.sortMap) OneSrt.all) procCollapsed.ctxt = 1 := rfl
  rw [h] at hn
  omega

/-- Both survive as genuine occurrences: collapsing sorts does not make a
position vacuous. -/
theorem transported_positions_are_linear :
    holeCount nameCollapsed.ctxt = 1 ∧ holeCount procCollapsed.ctxt = 1 :=
  ⟨nameCollapsed.linear, procCollapsed.linear⟩

end SortCollapse

namespace ConstantMerge

/-- Two constants at one sort. -/
inductive TwoOp : Unit → Type where
  | a : TwoOp ()
  | b : TwoOp ()

abbrev twoSig : Signature where
  Srt := Unit
  Op := TwoOp
  arity := fun {_} _ => []

/-- One constant at one sort. -/
inductive OneConst : Unit → Type where
  | c : OneConst ()

abbrev oneSig : Signature where
  Srt := Unit
  Op := OneConst
  arity := fun {_} _ => []

/-- Both constants go to the same one. -/
def merge : SigMor twoSig oneSig where
  sortMap := fun s => s
  opMap := fun _ => OneConst.c
  carriesArity := fun _ => rfl

def ta : Term twoSig [] () := Term.op (S := twoSig) TwoOp.a Args.nil
def tb : Term twoSig [] () := Term.op (S := twoSig) TwoOp.b Args.nil

/-- Which of the two constants a term has at its head. -/
def isA : Term twoSig [] () → Bool
  | .op TwoOp.a _ => true
  | _ => false

theorem ta_ne_tb : ta ≠ tb := by
  intro h
  have hb : isA ta = isA tb := congrArg isA h
  exact Bool.noConfusion hb

/-- **A morphism need not be faithful.**  So a statement proved downstream is
not, without further hypotheses, a statement about the source: transport is a
one-way street in the second sense too. -/
theorem onTerm_not_injective :
    ∃ t u : Term twoSig [] (), t ≠ u ∧ merge.onTerm t = merge.onTerm u :=
  ⟨ta, tb, ta_ne_tb, rfl⟩

end ConstantMerge

end Mettapedia.OSLF.Binding
