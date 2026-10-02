import Mettapedia.OSLF.Syntax.EquationTransport

/-!
# Strict signature maps on metavariable schemas

Metavariable interfaces are translated by their argument and result sorts.
Their identity is the declaration position; identifying sorts does not identify
distinct metavariable declarations.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S T U : Signature}

abbrev SigMor.mapMetas (F : SigMor S T) (M : List (MetaArity S)) : List (MetaArity T) :=
  mapArities F.sortMap M

def SigMor.mapMetaIndex (F : SigMor S T) {M : List (MetaArity S)}
    (i : Fin M.length) : Fin (F.mapMetas M).length :=
  ⟨i.val, by simp [SigMor.mapMetas, mapArities]⟩

theorem SigMor.get_mapMetas (F : SigMor S T) {M : List (MetaArity S)}
    (i : Fin M.length) :
    (F.mapMetas M).get (F.mapMetaIndex i) = mapArity F.sortMap (M.get i) := by
  simp [SigMor.mapMetas, SigMor.mapMetaIndex, mapArities, List.get_eq_getElem]

def SigMor.mapMetaOp (F : SigMor S T) {M : List (MetaArity S)} :
    {s : S.Srt} → MetaOp (S := S) M s → MetaOp (S := T) (F.mapMetas M) (F.sortMap s)
  | _, .mk i =>
      Eq.mp (congrArg (MetaOp (S := T) (F.mapMetas M))
        (congrArg Prod.snd (F.get_mapMetas i))) (MetaOp.mk (S := T) (F.mapMetaIndex i))

theorem SigMor.mapMetaOp_arity (F : SigMor S T) {M : List (MetaArity S)}
    {s : S.Srt} (m : MetaOp M s) :
    (withMetas T (F.mapMetas M)).arity (.inr (F.mapMetaOp m)) =
      mapArities F.sortMap ((withMetas S M).arity (.inr m)) := by
  cases m with
  | mk i =>
    have hc : ∀ {s t : T.Srt} (h : s = t) (m : MetaOp (S := T) (F.mapMetas M) s),
        (withMetas T (F.mapMetas M)).arity
          (.inr (Eq.mp (congrArg (MetaOp (S := T) (F.mapMetas M)) h) m)) =
          (withMetas T (F.mapMetas M)).arity (.inr m) := by
      intro s t h m
      subst h
      rfl
    exact (hc (congrArg Prod.snd (F.get_mapMetas i)) (MetaOp.mk (S := T) (F.mapMetaIndex i))).trans (by
      change ((F.mapMetas M).get (F.mapMetaIndex i)).1.map (fun b => ([], b)) = _
      rw [F.get_mapMetas i]
      simp [mapArity, mapArities, List.map_map, Function.comp_def])

/-- Extend a strict signature map to declaration-indexed metavariable operators. -/
@[reducible] def SigMor.withMetas (F : SigMor S T) (M : List (MetaArity S)) :
    SigMor (Binding.withMetas S M) (Binding.withMetas T (F.mapMetas M)) where
  sortMap := F.sortMap
  opMap := fun o => match o with
    | .inl o => .inl (F.opMap o)
    | .inr m => .inr (F.mapMetaOp m)
  carriesArity := fun o => by
    cases o with
    | inl o => exact F.carriesArity o
    | inr m => exact F.mapMetaOp_arity m

/-- Move a metavariable body along its declaration equality. -/
def castMetaBody {V : Signature} {a b : MetaArity V} (h : a = b)
    (t : Term V a.1 a.2) : Term V b.1 b.2 := h ▸ t

theorem castMetaBody_symm {V : Signature} {a b : MetaArity V} (h : a = b)
    (t : Term V b.1 b.2) : castMetaBody h (castMetaBody h.symm t) = t := by
  subst h
  rfl

def SigMor.unmapMetaIndex (F : SigMor S T) {M : List (MetaArity S)}
    (j : Fin (F.mapMetas M).length) : Fin M.length :=
  ⟨j.val, by simpa only [SigMor.mapMetas, mapArities, List.length_map] using j.isLt⟩

@[simp] theorem SigMor.map_unmapMetaIndex (F : SigMor S T) {M : List (MetaArity S)}
    (j : Fin (F.mapMetas M).length) : F.mapMetaIndex (F.unmapMetaIndex j) = j := rfl

@[simp] theorem SigMor.unmap_mapMetaIndex (F : SigMor S T) {M : List (MetaArity S)}
    (i : Fin M.length) : F.unmapMetaIndex (F.mapMetaIndex i) = i := rfl

/-- The same assigned bodies, translated into the mapped declaration interface. -/
def SigMor.mapMetaBody (F : SigMor S T) {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (j : Fin (F.mapMetas M).length) :
    Term T ((F.mapMetas M).get j).1 ((F.mapMetas M).get j).2 :=
  castMetaBody (F.get_mapMetas (F.unmapMetaIndex j)).symm (F.onTerm (body (F.unmapMetaIndex j)))

theorem SigMor.mapMetaBody_at (F : SigMor S T) {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) (i : Fin M.length) :
    castMetaBody (F.get_mapMetas i) (F.mapMetaBody body (F.mapMetaIndex i)) =
      F.onTerm (body i) := by
  unfold SigMor.mapMetaBody
  simp only [SigMor.unmap_mapMetaIndex]
  exact castMetaBody_symm (F.get_mapMetas i) _

theorem instantiateArgs_castArity {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {as bs : List (List S.Srt × S.Srt)} (h : as = bs) {Γ : Ctx S}
    (args : Args (Binding.withMetas S M) as Γ) :
    instantiateArgs body (castArgsArity (T := Binding.withMetas S M) h args) =
      castArgsArity (T := S) h (instantiateArgs body args) := by
  subst h
  rfl

/-- The operator cast forced by equality of metavariable declarations. -/
def castMetaOp {N : List (MetaArity T)} {a b : MetaArity T} (h : a = b)
    (m : MetaOp (S := T) N a.2) : MetaOp (S := T) N b.2 :=
  Eq.mp (congrArg (MetaOp (S := T) N) (congrArg Prod.snd h)) m

theorem castMetaOp_arity {N : List (MetaArity T)} (j : Fin N.length)
    {b : MetaArity T} (h : N.get j = b) :
    (Binding.withMetas T N).arity (.inr (castMetaOp h (.mk j))) =
      b.1.map (fun s => ([], s)) := by
  subst b
  rfl

/-- Instantiation respects the simultaneous argument/result transport of a
metavariable declaration. -/
theorem instantiate_castMetaOp {N : List (MetaArity T)}
    (body : (j : Fin N.length) → Term T (N.get j).1 (N.get j).2)
    (j : Fin N.length) {b : MetaArity T} (h : N.get j = b)
    {Γ : Ctx T} (args : Args (Binding.withMetas T N) (b.1.map (fun s => ([], s))) Γ) :
    instantiate body (Term.op (.inr (castMetaOp h (.mk j)))
      (castArgsArity (T := Binding.withMetas T N) (castMetaOp_arity j h).symm args)) =
      bind (argsToSub (instantiateArgs body args)) (castMetaBody h (body j)) := by
  subst b
  rfl

theorem mapFlatArity (f : S.Srt → T.Srt) (bs : List S.Srt) :
    mapArities f (bs.map (fun b => ([], b))) = (bs.map f).map (fun b => ([], b)) := by
  simp [mapArities, mapArity, List.map_map, Function.comp_def]

/-- Translate the argument list of a metavariable. -/
def mapFlatArgs (F : SigMor S T) {Γ : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ Δ) {bs : List S.Srt}
    (args : Args S (bs.map (fun b => ([], b))) Γ) :
    Args T ((bs.map F.sortMap).map (fun b => ([], b))) Δ :=
  castArgsArity (mapFlatArity F.sortMap bs) (mapArgs F ν args)

theorem mapFlatArgs_cons (F : SigMor S T) {Γ : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ Δ) {bs : List S.Srt} {s : S.Srt}
    (head : Term S Γ s) (tail : Args S (bs.map (fun b => ([], b))) Γ) :
    mapFlatArgs F ν (bs := s :: bs) (.cons (bs := []) head tail) =
      .cons (bs := []) (mapTerm F ν head) (mapFlatArgs F ν tail) :=
  castArgsArity_cons (T := T) rfl (mapFlatArity F.sortMap bs) _ _

theorem argsToSub_mapFlatArgs (F : SigMor S T) {Γ : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ Δ) :
    ∀ {bs : List S.Srt} (args : Args S (bs.map (fun b => ([], b))) Γ)
      (s : S.Srt) (x : Var bs s),
      argsToSub (mapFlatArgs F ν args) (F.sortMap s) (mapVar F.sortMap s x) =
        mapTerm F ν (argsToSub args s x)
  | [], _, _, x => nomatch x
  | _ :: _, .cons head tail, _, .zero => by rw [mapFlatArgs_cons]; rfl
  | _ :: _, .cons head tail, _, .succ x => by
      rw [mapFlatArgs_cons]
      exact argsToSub_mapFlatArgs F ν tail _ x

theorem SigMor.withMetas_mapTerm_meta (F : SigMor S T) (M : List (MetaArity S))
    {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ) (i : Fin M.length)
    (args : Args (Binding.withMetas S M) ((M.get i).1.map (fun s => ([], s))) Γ) :
    mapTerm (F.withMetas M) ν (Term.op (.inr (.mk i)) args) =
      Term.op (S := Binding.withMetas T (F.mapMetas M))
        (.inr (castMetaOp (F.get_mapMetas i) (.mk (F.mapMetaIndex i))))
        (castArgsArity (T := Binding.withMetas T (F.mapMetas M))
          (castMetaOp_arity (F.mapMetaIndex i) (F.get_mapMetas i)).symm
          (mapFlatArgs (F.withMetas M) ν args)) := by
  exact congrArg (Term.op (S := Binding.withMetas T (F.mapMetas M))
    (.inr (castMetaOp (F.get_mapMetas i) (.mk (F.mapMetaIndex i)))))
      (castArgsArity_trans (T := Binding.withMetas T (F.mapMetas M))
        (mapFlatArity F.sortMap (M.get i).1)
        (castMetaOp_arity (F.mapMetaIndex i) (F.get_mapMetas i)).symm
        (mapArgs (F.withMetas M) ν args)).symm

mutual
/-- Mapping a schema and its assigned bodies agrees with mapping its instance. -/
theorem SigMor.instantiate_mapTerm (F : SigMor S T) {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ)
      {s : S.Srt} (t : Term (Binding.withMetas S M) Γ s),
      instantiate (F.mapMetaBody body) (mapTerm (F.withMetas M) ν t) =
        mapTerm F ν (instantiate body t)
  | _, _, _, _, .var _ => rfl
  | _, _, ν, _, .op (.inl o) args => by
      change Term.op (F.opMap o)
        (instantiateArgs (F.mapMetaBody body)
          (castArgsArity (T := Binding.withMetas T (F.mapMetas M))
            (F.carriesArity o).symm (mapArgs (F.withMetas M) ν args))) = _
      rw [instantiateArgs_castArity, F.instantiateArgs_mapArgs body ν]
      rfl
  | _, _, ν, _, .op (.inr (.mk i)) args => by
      refine (congrArg (instantiate (F.mapMetaBody body)) (F.withMetas_mapTerm_meta M ν i args)).trans ?_
      refine (instantiate_castMetaOp (F.mapMetaBody body) (F.mapMetaIndex i)
        (F.get_mapMetas i) (mapFlatArgs (F.withMetas M) ν args)).trans ?_
      rw [F.mapMetaBody_at]
      have hargs : instantiateArgs (F.mapMetaBody body) (mapFlatArgs (F.withMetas M) ν args) =
          mapFlatArgs F ν (instantiateArgs body args) := by
        unfold mapFlatArgs
        rw [instantiateArgs_castArity, F.instantiateArgs_mapArgs body ν]
      refine (congrArg (fun a => bind (argsToSub a) (F.onTerm (body i))) hargs).trans ?_
      exact (mapTerm_bind F (mapVar F.sortMap) ν (argsToSub (instantiateArgs body args))
        (argsToSub (mapFlatArgs F ν (instantiateArgs body args)))
        (argsToSub_mapFlatArgs F ν (instantiateArgs body args)) (body i)).symm

theorem SigMor.instantiateArgs_mapArgs (F : SigMor S T) {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ)
      {as : List (List S.Srt × S.Srt)} (args : Args (Binding.withMetas S M) as Γ),
      instantiateArgs (F.mapMetaBody body) (mapArgs (F.withMetas M) ν args) =
        mapArgs F ν (instantiateArgs body args)
  | _, _, _, _, .nil => rfl
  | _, _, ν, _, .cons (bs := bs) head tail => by
      change Args.cons
        (instantiate (F.mapMetaBody body) (mapTerm (F.withMetas M) (liftVarMap F.sortMap ν bs) head))
        (instantiateArgs (F.mapMetaBody body) (mapArgs (F.withMetas M) ν tail)) = _
      rw [F.instantiate_mapTerm body, F.instantiateArgs_mapArgs body]
      rfl
end

/-- Transport a contextual body along equality of its declaration. -/
def castContextualMetaBody {V : Signature} {a b : MetaArity V} (h : a = b)
    {Θ : Ctx V} (t : Term V (a.1 ++ Θ) a.2) : Term V (b.1 ++ Θ) b.2 := h ▸ t

theorem castContextualMetaBody_symm {V : Signature} {a b : MetaArity V} (h : a = b)
    {Θ : Ctx V} (t : Term V (b.1 ++ Θ) b.2) :
    castContextualMetaBody h (castContextualMetaBody h.symm t) = t := by
  subst h
  rfl

/-- Translate the independent ambient variables while retaining each
metavariable declaration and its dependency prefix. -/
def SigMor.mapContextualBody (F : SigMor S T) {M : List (MetaArity S)}
    {Θ : Ctx S} {Θ' : Ctx T} (ρ : VarMap F.sortMap Θ Θ')
    (body : ContextualAssignment S M Θ) : ContextualAssignment T (F.mapMetas M) Θ' :=
  fun j => castContextualMetaBody (F.get_mapMetas (F.unmapMetaIndex j)).symm
    (mapTerm F (liftVarMap F.sortMap ρ (M.get (F.unmapMetaIndex j)).1)
      (body (F.unmapMetaIndex j)))

theorem SigMor.mapContextualBody_at (F : SigMor S T) {M : List (MetaArity S)}
    {Θ : Ctx S} {Θ' : Ctx T} (ρ : VarMap F.sortMap Θ Θ')
    (body : ContextualAssignment S M Θ) (i : Fin M.length) :
    castContextualMetaBody (F.get_mapMetas i) (F.mapContextualBody ρ body (F.mapMetaIndex i)) =
      mapTerm F (liftVarMap F.sortMap ρ (M.get i).1) (body i) := by
  unfold SigMor.mapContextualBody
  simp only [SigMor.unmap_mapMetaIndex]
  exact castContextualMetaBody_symm (F.get_mapMetas i) _

theorem contextualInstantiateArgs_castArity {M : List (MetaArity S)} {Θ Ξ Γ : Ctx S}
    (body : ContextualAssignment S M Θ) (ambient : Sub S Θ Γ) (ordinary : Sub S Ξ Γ)
    {as bs : List (List S.Srt × S.Srt)} (h : as = bs)
    (args : Args (Binding.withMetas S M) as Ξ) :
    ContextualAssignment.instantiateArgs body ambient ordinary
        (castArgsArity (T := Binding.withMetas S M) h args) =
      castArgsArity (T := S) h (ContextualAssignment.instantiateArgs body ambient ordinary args) := by
  subst h
  rfl

theorem contextualInstantiate_castMetaOp {N : List (MetaArity T)} {Θ Ξ Γ : Ctx T}
    (body : ContextualAssignment T N Θ) (ambient : Sub T Θ Γ) (ordinary : Sub T Ξ Γ)
    (j : Fin N.length) {b : MetaArity T} (h : N.get j = b)
    (args : Args (Binding.withMetas T N) (b.1.map (fun s => ([], s))) Ξ) :
    ContextualAssignment.instantiate body ambient ordinary
        (Term.op (.inr (castMetaOp h (.mk j)))
          (castArgsArity (T := Binding.withMetas T N) (castMetaOp_arity j h).symm args)) =
      bind (ContextualAssignment.joinSub
        (argsToSub (ContextualAssignment.instantiateArgs body ambient ordinary args)) ambient)
        (castContextualMetaBody h (body j)) := by
  subst b
  rfl

/-- Mapped dependency arguments and ambient environments combine without
requiring an inverse of the sort map. -/
theorem SigMor.joinSub_compat (F : SigMor S T) {Θ : Ctx S} {Θ' : Ctx T}
    {Γ : Ctx S} {Γ' : Ctx T} (ρ : VarMap F.sortMap Θ Θ') (ν : VarMap F.sortMap Γ Γ')
    (ambient : Sub S Θ Γ) (ambient' : Sub T Θ' Γ')
    (ambientCompat : ∀ s v, ambient' (F.sortMap s) (ρ s v) = mapTerm F ν (ambient s v)) :
    ∀ (dependencies : Ctx S) (arguments : Sub S dependencies Γ)
      (arguments' : Sub T (dependencies.map F.sortMap) Γ')
      (_argumentCompat : ∀ s v,
        arguments' (F.sortMap s) (mapVar F.sortMap s v) = mapTerm F ν (arguments s v))
      (s : S.Srt) (v : Var (dependencies ++ Θ) s),
      ContextualAssignment.joinSub arguments' ambient' (F.sortMap s)
          (liftVarMap F.sortMap ρ dependencies s v) =
        mapTerm F ν (ContextualAssignment.joinSub arguments ambient s v)
  | [], _, _, _, s, v => ambientCompat s v
  | b :: dependencies, _arguments, _arguments', hc, _, .zero => hc b (Var.zero (Γ := dependencies))
  | _ :: dependencies, arguments, arguments', hc, s, .succ v =>
      F.joinSub_compat ρ ν ambient ambient' ambientCompat dependencies
        (fun s v => arguments s (.succ v)) (fun s v => arguments' s (.succ v))
        (fun s v => hc s (.succ v)) s v

/-- Ambient values weaken through exactly the mapped binder list. -/
theorem SigMor.weakenSub_compat (F : SigMor S T) {Θ : Ctx S} {Θ' : Ctx T}
    {Γ : Ctx S} {Γ' : Ctx T} (ρ : VarMap F.sortMap Θ Θ') (ν : VarMap F.sortMap Γ Γ')
    (ambient : Sub S Θ Γ) (ambient' : Sub T Θ' Γ')
    (hc : ∀ s v, ambient' (F.sortMap s) (ρ s v) = mapTerm F ν (ambient s v))
    (bs : Ctx S) (s : S.Srt) (v : Var Θ s) :
    ContextualAssignment.weakenSub (S := T) (bs.map F.sortMap) ambient' (F.sortMap s) (ρ s v) =
      mapTerm F (liftVarMap F.sortMap ν bs) (ContextualAssignment.weakenSub (S := S) bs ambient s v) := by
  unfold ContextualAssignment.weakenSub
  rw [hc, rename_mapTerm, mapTerm_rename]
  exact mapTerm_congr F _ _ (fun s v => (liftVarMap_weakenVar F ν bs v).symm) _

mutual
/-- Signature transport commutes with actual contextual instantiation.
The three context maps and both environment comparisons are independent. -/
theorem SigMor.contextualInstantiate_mapTerm (F : SigMor S T) {M : List (MetaArity S)}
    {Θ : Ctx S} {Θ' : Ctx T} (ρ : VarMap F.sortMap Θ Θ')
    (body : ContextualAssignment S M Θ) :
    ∀ {Ξ : Ctx S} {Ξ' : Ctx T} (μ : VarMap F.sortMap Ξ Ξ')
      {Γ : Ctx S} {Γ' : Ctx T} (ν : VarMap F.sortMap Γ Γ')
      (ambient : Sub S Θ Γ) (ambient' : Sub T Θ' Γ')
      (ordinary : Sub S Ξ Γ) (ordinary' : Sub T Ξ' Γ')
      (_ha : ∀ s v, ambient' (F.sortMap s) (ρ s v) = mapTerm F ν (ambient s v))
      (_ho : ∀ s v, ordinary' (F.sortMap s) (μ s v) = mapTerm F ν (ordinary s v))
      {s : S.Srt} (term : Term (Binding.withMetas S M) Ξ s),
      ContextualAssignment.instantiate (F.mapContextualBody ρ body) ambient' ordinary'
          (mapTerm (F.withMetas M) μ term) =
        mapTerm F ν (ContextualAssignment.instantiate body ambient ordinary term)
  | _, _, _, _, _, _, _, _, _, _, _, ho, _, .var v => ho _ v
  | _, _, μ, _, _, ν, ambient, ambient', ordinary, ordinary', ha, ho, _, .op (.inl o) args => by
      change Term.op (F.opMap o)
        (ContextualAssignment.instantiateArgs (F.mapContextualBody ρ body) ambient' ordinary'
          (castArgsArity (T := Binding.withMetas T (F.mapMetas M))
            (F.carriesArity o).symm (mapArgs (F.withMetas M) μ args))) = _
      rw [contextualInstantiateArgs_castArity,
        F.contextualInstantiateArgs_mapArgs ρ body μ ν ambient ambient' ordinary ordinary' ha ho]
      rfl
  | _, _, μ, _, _, ν, ambient, ambient', ordinary, ordinary', ha, ho, _, .op (.inr (.mk i)) args => by
      refine (congrArg
        (ContextualAssignment.instantiate (F.mapContextualBody ρ body) ambient' ordinary')
        (F.withMetas_mapTerm_meta M μ i args)).trans ?_
      refine (contextualInstantiate_castMetaOp (F.mapContextualBody ρ body) ambient' ordinary'
        (F.mapMetaIndex i) (F.get_mapMetas i)
        (mapFlatArgs (F.withMetas M) μ args)).trans ?_
      rw [F.mapContextualBody_at]
      have hargs : ContextualAssignment.instantiateArgs (F.mapContextualBody ρ body) ambient' ordinary'
          (mapFlatArgs (F.withMetas M) μ args) =
          mapFlatArgs F ν (ContextualAssignment.instantiateArgs body ambient ordinary args) := by
        unfold mapFlatArgs
        rw [contextualInstantiateArgs_castArity,
          F.contextualInstantiateArgs_mapArgs ρ body μ ν ambient ambient' ordinary ordinary' ha ho]
      refine (congrArg (fun args => bind (ContextualAssignment.joinSub (argsToSub args) ambient')
        (mapTerm F (liftVarMap F.sortMap ρ (M.get i).1) (body i))) hargs).trans ?_
      exact (mapTerm_bind F (liftVarMap F.sortMap ρ (M.get i).1) ν
        (ContextualAssignment.joinSub
          (argsToSub (ContextualAssignment.instantiateArgs body ambient ordinary args)) ambient)
        (ContextualAssignment.joinSub
          (argsToSub (mapFlatArgs F ν (ContextualAssignment.instantiateArgs body ambient ordinary args))) ambient')
        (F.joinSub_compat ρ ν ambient ambient' ha (M.get i).1 _ _
          (argsToSub_mapFlatArgs F ν (ContextualAssignment.instantiateArgs body ambient ordinary args)))
        (body i)).symm

/-- The same comparison retains argument order and the local binder lift. -/
theorem SigMor.contextualInstantiateArgs_mapArgs (F : SigMor S T) {M : List (MetaArity S)}
    {Θ : Ctx S} {Θ' : Ctx T} (ρ : VarMap F.sortMap Θ Θ')
    (body : ContextualAssignment S M Θ) :
    ∀ {Ξ : Ctx S} {Ξ' : Ctx T} (μ : VarMap F.sortMap Ξ Ξ')
      {Γ : Ctx S} {Γ' : Ctx T} (ν : VarMap F.sortMap Γ Γ')
      (ambient : Sub S Θ Γ) (ambient' : Sub T Θ' Γ')
      (ordinary : Sub S Ξ Γ) (ordinary' : Sub T Ξ' Γ')
      (_ha : ∀ s v, ambient' (F.sortMap s) (ρ s v) = mapTerm F ν (ambient s v))
      (_ho : ∀ s v, ordinary' (F.sortMap s) (μ s v) = mapTerm F ν (ordinary s v))
      {as : List (List S.Srt × S.Srt)} (args : Args (Binding.withMetas S M) as Ξ),
      ContextualAssignment.instantiateArgs (F.mapContextualBody ρ body) ambient' ordinary'
          (mapArgs (F.withMetas M) μ args) =
        mapArgs F ν (ContextualAssignment.instantiateArgs body ambient ordinary args)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, μ, _, _, ν, ambient, ambient', ordinary, ordinary', ha, ho, _,
      .cons (bs := bs) head tail => by
      change Args.cons
        (ContextualAssignment.instantiate (F.mapContextualBody ρ body)
          (ContextualAssignment.weakenSub (S := T) (bs.map F.sortMap) ambient')
          (liftSub ordinary' (bs.map F.sortMap))
          (mapTerm (F.withMetas M) (liftVarMap F.sortMap μ bs) head))
        (ContextualAssignment.instantiateArgs (F.mapContextualBody ρ body) ambient' ordinary'
          (mapArgs (F.withMetas M) μ tail)) = _
      rw [F.contextualInstantiate_mapTerm ρ body (liftVarMap F.sortMap μ bs)
        (liftVarMap F.sortMap ν bs)
        (ContextualAssignment.weakenSub (S := S) bs ambient)
        (ContextualAssignment.weakenSub (S := T) (bs.map F.sortMap) ambient')
        (liftSub ordinary bs) (liftSub ordinary' (bs.map F.sortMap))
        (F.weakenSub_compat ρ ν ambient ambient' ha bs)
        (liftSub_compat F μ ν ordinary ordinary' ho bs),
        F.contextualInstantiateArgs_mapArgs ρ body μ ν ambient ambient' ordinary ordinary' ha ho]
      rfl
end

/-- Translate an authored equation schema, including its metavariable interface. -/
def SigMor.mapEqAxiom (F : SigMor S T) {M : List (MetaArity S)}
    (e : EqAxiom S M) : EqAxiom T (F.mapMetas M) where
  ctx := e.ctx.map F.sortMap
  sort := F.sortMap e.sort
  lhs := (F.withMetas M).onTerm e.lhs
  rhs := (F.withMetas M).onTerm e.rhs

/-- The mapped equation list supplies its own generator compatibility proof. -/
theorem SigMor.respectsEquations_map (F : SigMor S T) {M : List (MetaArity S)}
    (E : List (EqAxiom S M)) : F.RespectsEquations E (E.map F.mapEqAxiom) := by
  intro i Θ Γ body ambient ordinary
  let j : Fin (E.map F.mapEqAxiom).length :=
    ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  let mappedBody := F.mapContextualBody (mapVar F.sortMap) body
  let mappedAmbient := F.mapSub (mapVar F.sortMap) ambient
  let mappedOrdinary := F.mapSub (mapVar F.sortMap) ordinary
  have hj : (E.map F.mapEqAxiom).get j = F.mapEqAxiom (E.get i) := by
    simp [j, List.get_eq_getElem]
  have admitted : ∀ close : Sub T (F.mapEqAxiom (E.get i)).ctx (Γ.map F.sortMap),
      EqClosure (E.map F.mapEqAxiom)
        (ContextualAssignment.instantiate mappedBody mappedAmbient close (F.mapEqAxiom (E.get i)).lhs)
        (ContextualAssignment.instantiate mappedBody mappedAmbient close (F.mapEqAxiom (E.get i)).rhs) := by
    rw [← hj]
    intro close
    exact EqClosure.ax (E := E.map F.mapEqAxiom) j mappedBody mappedAmbient close
  have generator := admitted mappedOrdinary
  dsimp only [SigMor.mapEqAxiom] at generator
  have left := F.contextualInstantiate_mapTerm (mapVar F.sortMap) body
    (mapVar F.sortMap) (mapVar F.sortMap) ambient mappedAmbient ordinary mappedOrdinary
    (F.mapSub_mapVar (mapVar F.sortMap) ambient)
    (F.mapSub_mapVar (mapVar F.sortMap) ordinary) (E.get i).lhs
  have right := F.contextualInstantiate_mapTerm (mapVar F.sortMap) body
    (mapVar F.sortMap) (mapVar F.sortMap) ambient mappedAmbient ordinary mappedOrdinary
    (F.mapSub_mapVar (mapVar F.sortMap) ambient)
    (F.mapSub_mapVar (mapVar F.sortMap) ordinary) (E.get i).rhs
  dsimp only [SigMor.onTerm] at generator ⊢
  rw [left, right] at generator
  exact generator

/-- Equation closure is preserved by the schema translation, without a
user-supplied equation-preservation field. -/
theorem SigMor.eqClosure_mapEquations (F : SigMor S T) {M : List (MetaArity S)}
    {E : List (EqAxiom S M)} {Γ : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ Δ) {s : S.Srt} {t u : Term S Γ s}
    (h : EqClosure E t u) :
    EqClosure (E.map F.mapEqAxiom) (mapTerm F ν t) (mapTerm F ν u) :=
  F.eqClosure_map (F.respectsEquations_map E) ν h

theorem SigMor.mapMetas_ident (M : List (MetaArity S)) :
    (SigMor.ident S).mapMetas M = M := mapArities_id M

theorem SigMor.mapMetas_comp (F : SigMor S T) (G : SigMor T U) (M : List (MetaArity S)) :
    G.mapMetas (F.mapMetas M) = (F.comp G).mapMetas M :=
  mapArities_comp F.sortMap G.sortMap M

/-- Identity schema translation induces the original instance (or its chosen
renaming), without reassigning its metavariables. -/
theorem SigMor.instantiate_mapTerm_ident {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {Γ Δ : Ctx S} (ν : Ren S Γ Δ) {s : S.Srt}
    (t : Term (Binding.withMetas S M) Γ s) :
    instantiate ((SigMor.ident S).mapMetaBody body)
      (mapTerm ((SigMor.ident S).withMetas M) ν t) = rename ν (instantiate body t) :=
  ((SigMor.ident S).instantiate_mapTerm body ν t).trans (mapTerm_ident ν _)

/-- Successive schema/body translations and composite native translation
compute the same instance, including under mapped contexts. -/
theorem SigMor.instantiate_mapTerm_comp (F : SigMor S T) (G : SigMor T U)
    {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {Γ : Ctx S} {Δ : Ctx T} {Θ : Ctx U}
    (ν : VarMap F.sortMap Γ Δ) (ν' : VarMap G.sortMap Δ Θ)
    {s : S.Srt} (t : Term (Binding.withMetas S M) Γ s) :
    instantiate (G.mapMetaBody (F.mapMetaBody body))
      (mapTerm (G.withMetas (F.mapMetas M)) ν' (mapTerm (F.withMetas M) ν t)) =
      mapTerm (F.comp G) (fun r x => ν' (F.sortMap r) (ν r x)) (instantiate body t) :=
  (G.instantiate_mapTerm (F.mapMetaBody body) ν' _).trans
    ((congrArg (mapTerm G ν') (F.instantiate_mapTerm body ν t)).trans
      (mapTerm_comp F G ν ν' _))

namespace MetavariableTransportControls

open ConstantMerge EquationTransportControls

abbrev unaryMetas : List (MetaArity twoSig) := [([()], ())]

def unaryEquation : EqAxiom twoSig unaryMetas where
  ctx := []
  sort := ()
  lhs := .op (.inr (.mk 0)) (.cons (.op (.inl .a) .nil) .nil)
  rhs := .op (.inl .b) .nil

def identityBody (i : Fin unaryMetas.length) :
    Term twoSig (unaryMetas.get i).1 (unaryMetas.get i).2 := by
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact .var .zero

theorem source_instance : EqClosure [unaryEquation] ta tb := by
  have h := EqClosure.ax_closed (E := [unaryEquation]) (Γ := []) 0 identityBody
    (fun _ x => nomatch x)
  exact h

/-- A metavariable really consumes the translated argument. -/
theorem mapped_instance_uses_argument :
    instantiate (swap.mapMetaBody identityBody) (swap.mapEqAxiom unaryEquation).lhs = tb := by
  exact swap.instantiate_mapTerm identityBody (mapVar swap.sortMap) unaryEquation.lhs

theorem mapped_instance_not_original :
    instantiate (swap.mapMetaBody identityBody) (swap.mapEqAxiom unaryEquation).lhs ≠ ta := by
  rw [mapped_instance_uses_argument]
  exact Ne.symm ta_ne_tb

/-- The authored schema image discharges the generator obligation automatically. -/
theorem transported_schema_equation :
    EqClosure ([unaryEquation].map swap.mapEqAxiom) tb ta :=
  swap.eqClosure_mapEquations (mapVar swap.sortMap) source_instance

/-- The metavariable depends on the independent ambient variable and ignores
its declared argument. This instance requires contextual axiom admission. -/
def ambientUnaryBody : ContextualAssignment twoSig unaryMetas [()] := by
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact .var (.succ .zero)

theorem contextual_source_instance :
    EqClosure [unaryEquation] (.var .zero : Term twoSig [()] ()) (.op .b .nil) := by
  have h := EqClosure.ax (E := [unaryEquation]) 0 ambientUnaryBody
    (fun _ v => Term.var v) (fun _ v => nomatch v)
  exact h

/-- The same contextual instance crosses a nonidentity signature map;
the ambient variable stays variable while the constant symbol is exchanged. -/
theorem transported_contextual_schema_equation :
    EqClosure ([unaryEquation].map swap.mapEqAxiom)
      (.var .zero : Term twoSig [()] ()) (.op .a .nil) :=
  swap.eqClosure_mapEquations (mapVar swap.sortMap) contextual_source_instance

/-- Without authored equations, that ambient variable and constant remain
separate syntax. The positive instance is supplied by the real generator. -/
theorem contextual_instance_requires_equation :
    ¬ EqClosure ([] : List (EqAxiom twoSig unaryMetas))
      (.var .zero : Term twoSig [()] ()) (.op .b .nil) := by
  intro h
  cases eqClosure_empty_eq h

abbrev distinctSortMetas : List (MetaArity RedexPositionWitness.sig) :=
  [([], RedexPositionWitness.Srt.nm), ([], RedexPositionWitness.Srt.pr)]

/-- Sort collapse does not merge declaration positions or their assigned roles. -/
theorem collapsed_sorts_keep_distinct_metas :
    SortCollapse.collapse.mapMetaOp (M := distinctSortMetas) (.mk 0) ≠
      SortCollapse.collapse.mapMetaOp (M := distinctSortMetas) (.mk 1) := by
  intro h
  change MetaOp.mk (S := SortCollapse.osig) (M := SortCollapse.collapse.mapMetas distinctSortMetas)
    ⟨0, by decide⟩ = MetaOp.mk ⟨1, by decide⟩ at h
  cases h

end MetavariableTransportControls

end Mettapedia.OSLF.Binding
