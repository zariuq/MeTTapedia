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
  intro i body
  let j : Fin (E.map F.mapEqAxiom).length := ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  have h := EqClosure.ax (E := E.map F.mapEqAxiom) j (F.mapMetaBody body)
    (fun _ x => Term.var x)
  have hj : (E.map F.mapEqAxiom).get j = F.mapEqAxiom (E.get i) := by
    simp [j, List.get_eq_getElem]
  simp only [bind_id] at h
  rw [hj] at h
  simp only [SigMor.mapEqAxiom, SigMor.onTerm, F.instantiate_mapTerm] at h
  exact h

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
  have h := EqClosure.ax (E := [unaryEquation]) (Γ := []) 0 identityBody
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
