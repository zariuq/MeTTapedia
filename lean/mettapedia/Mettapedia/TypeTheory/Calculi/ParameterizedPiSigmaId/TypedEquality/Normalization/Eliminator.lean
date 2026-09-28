import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Spines

/-!
# The based identity eliminator

The eliminator `J` is a declared constant of arity six, computing on its last
argument, declared at

`Π (A : U) (x : A) (P : Π (y : A). Id A x y → V) (d : P x (refl x)) (y : A)
  (p : Id A x y). P y p`

with the linear computation rule `J A x P d y (refl z) ⟶ d`. The rule does
not compare `z` with `x` or `y`: in the model a reducible proof of `Id A x y`
that reduces to `refl z` has `z` reducibly equal to both endpoints, so the
method's type `P x (refl x)` and the result type `P y p` have the same pack.
That is why the endpoint comparisons are redundant for typed applications.

The eliminator is semantic: at a reducible path it reduces to its method, and
at a neutral path it is neutral. Its computation rule preserves typing given the
facts about the weak-head forms of types, by injectivity of identity types.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## The declaration -/

/-- The first five entries of the eliminator's telescope. -/
def elimPrefix (u v : Head) : Ctx Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil (.head u))
    (.var 0))
    (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head v))))
    (.app (.app (.var 0) (.var 1)) (.refl (.var 1))))
    (.var 3)

/-- The telescope of the eliminator, with carrier universe `u` and motive
universe `v`: `A`, `x`, `P`, `d`, `y`, `p`. -/
def elimTelescope (u v : Head) : Ctx Head 6 :=
  .snoc (elimPrefix u v) (.id (.var 4) (.var 3) (.var 0))

/-- The result type `P y p`. -/
def elimBody : Tm Head 6 := .app (.app (.var 3) (.var 1)) (.var 0)

/-- The declared type of the eliminator. -/
def elimType (u v : Head) : Tm Head 0 := closeType (elimTelescope u v) elimBody

/-- The rule package with the same universes and no constants or computations. -/
def constantFreeRules (R : Rules Head) : Rules Head :=
  { R with constantType := fun _ => none, computation := RootComputation.empty }

theorem RulesSub.constantFree (R : Rules Head) : RulesSub (constantFreeRules R) R where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => nomatch declared
  computation := fun step => nomatch step

variable {S : Setting Head L}

/-- The rule package declares the eliminator `J` at carrier universe `u` and
motive universe `v`, with its linear computation rule, and its declared type
is typed in a universe without using any constant. -/
structure DeclaresEliminator (S : Setting Head L) (J : DeclName) (u v : Head) : Prop where
  role : S.roles J = .computes 6 (.split 5 .constructor fun _ => .leaf)
  declared : S.R.constantType J = some (elimType u v)
  rule : ∀ {n : Nat} {a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head n},
    S.R.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl a₅]) a₃
  hu : S.R.isUniverse u
  hv : S.R.isUniverse v
  typed : ∃ w, S.R.isUniverse w ∧ Typed (constantFreeRules S.R) .nil (elimType u v) (.head w)

theorem SemanticConstantsOf.constantFree : SemanticConstantsOf S (constantFreeRules S.R) :=
  fun declared => nomatch declared

/-! ## Applications of the eliminator -/

theorem applyClosed_elim {J : DeclName} {u v : Head} {m : Nat} (σ : Sub Head 6 m) :
    applyClosed (elimTelescope u v) σ (.const J : Tm Head m) =
      appSpine (.const J) [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0] := by
  rw [applyClosed_eq_appSpine]
  rfl

theorem applyClosed_elimPrefix {J : DeclName} {u v : Head} {m : Nat} (σ : Sub Head 5 m) :
    applyClosed (elimPrefix u v) σ (.const J : Tm Head m) =
      appSpine (.const J) [σ 4, σ 3, σ 2, σ 1, σ 0] := by
  rw [applyClosed_eq_appSpine]
  rfl

section Typing

variable {J : DeclName} {u v : Head} (decl : DeclaresEliminator S J u v)
include decl

/-- The eliminator at its declared type, in every context. -/
theorem DeclaresEliminator.closed {m : Nat} {Δ : Ctx Head m} :
    Typed S.R Δ (.const J) (liftClosed (elimType u v)) := by
  obtain ⟨w, hw, typed⟩ := decl.typed
  exact .const decl.declared (Derivable.mono (RulesSub.constantFree S.R) typed) hw

/-- The full application of the eliminator to a typed substitution. -/
theorem DeclaresEliminator.typed_app {m : Nat} {Δ : Ctx Head m} {σ : Sub Head 6 m}
    (typed : SubstMor S.R (elimTelescope u v) Δ σ) :
    Typed S.R Δ (appSpine (.const J) [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
      (.app (.app (σ 3) (σ 1)) (σ 0)) := by
  have h := Typed.telescope_apply typed (decl.closed (Δ := Δ))
  rw [applyClosed_elim] at h
  exact h

/-- The application of the eliminator to all but its path. -/
theorem DeclaresEliminator.typed_partial {m : Nat} {Δ : Ctx Head m} {σ : Sub Head 6 m}
    (typed : SubstMor S.R (elimTelescope u v) Δ σ) :
    Typed S.R Δ (appSpine (.const J) [σ 5, σ 4, σ 3, σ 2, σ 1])
      (.pi (.id (σ 5) (σ 4) (σ 1))
        (.app (.app (Presentation.rename wk (σ 3)) (Presentation.rename wk (σ 1))) (.var 0))) := by
  have h := Typed.telescope_apply (Θ := elimPrefix u v)
    (X := .pi (.id (.var 4) (.var 3) (.var 0)) elimBody) (SubstMor.tail typed)
    (decl.closed (Δ := Δ))
  rw [applyClosed_elimPrefix] at h
  exact h

end Typing

/-! ## Motives -/

/-- The type of motives over a carrier `a` and a base point `x`, valued in `v`. -/
def motiveType {m : Nat} (a x : Tm Head m) (v : Head) : Tm Head m :=
  .pi a (.pi (.id (Presentation.rename wk a) (Presentation.rename wk x) (.var 0)) (.head v))

theorem inst0_motiveCod {m : Nat} (a x y : Tm Head m) (v : Head) :
    inst0 y (.pi (.id (Presentation.rename wk a) (Presentation.rename wk x) (.var 0)) (.head v)) =
      .pi (.id a x y) (.head v) := by
  show Tm.pi (.id (inst0 y (Presentation.rename wk a)) (inst0 y (Presentation.rename wk x)) y)
    (.head v) = _
  rw [inst0_rename_wk, inst0_rename_wk]

theorem inst0_motiveBody {m : Nat} (f y p : Tm Head m) :
    inst0 p (.app (.app (Presentation.rename wk f) (Presentation.rename wk y)) (.var 0)) =
      .app (.app f y) p := by
  show Tm.app (.app (inst0 p (Presentation.rename wk f)) (inst0 p (Presentation.rename wk y))) p = _
  rw [inst0_rename_wk, inst0_rename_wk]

/-- A motive applied to reducibly equal endpoints and paths: the application is
a reducible type, and both applications have the same pack. -/
theorem motive_pack (laws : S.E.Laws S.R S.roles) {m : Nat} {Δ : Ctx Head m}
    (formed : CtxFormed S.R Δ) {a x f : Tm Head m} {v : Head} (hv : S.R.isUniverse v)
    {PF : Pack Head m} (rF : Reducible S Δ (motiveType a x v) PF) (hf : PF.redTm f)
    {y y' q q' : Tm Head m} (hy : (packOf S Δ a).redTm y) (hy' : (packOf S Δ a).redTm y')
    (hyy : (packOf S Δ a).eqTm y y') (hq : (packOf S Δ (.id a x y)).redTm q)
    (hq' : (packOf S Δ (.id a x y)).redTm q') (hqq : (packOf S Δ (.id a x y)).eqTm q q') :
    Reducible S Δ (.app (.app f y) q) (packOf S Δ (.app (.app f y) q)) ∧
      packOf S Δ (.app (.app f y) q) = packOf S Δ (.app (.app f y') q') := by
  have hff := rF.reflexive.eqTm hf
  obtain ⟨parts, same, _⟩ := Reducible.pi_view laws rF
  rw [same] at hff
  have e₁ := parts.app_eqTm laws formed hff hy hy' hyy
  have rCod := parts.cod_self formed hy
  rw [inst0_motiveCod] at e₁ rCod
  obtain ⟨parts₂, same₂, _⟩ := Reducible.pi_view laws rCod
  rw [same₂] at e₁
  have e₂ := parts₂.app_eqTm laws formed e₁ hq hq' hqq
  change (packOf S Δ (.head v)).eqTm _ _ at e₂
  have rU := (universe_logRel (S := S) hv formed).reducible
  rw [← rU.eq_packOf laws] at e₂
  obtain ⟨_, ⟨Q, lower⟩, eqTy⟩ := universe_equal laws hv formed e₂
  obtain ⟨_, member'⟩ := rU.eqTm_redTm laws e₂
  obtain ⟨Q', lower'⟩ := universePack_redTm_logRel (LevelOrder.lt_succ _) member'
  have r₁ := lower.reducible.packOf_self laws
  exact ⟨r₁, r₁.conv laws (lower'.reducible.packOf_self laws) eqTy⟩

/-! ## Stuck applications -/

/-- Validly equal substitutions give a valid type equal types. -/
theorem ValidTy.typeEq_at (laws : S.E.Laws S.R S.roles) {n m : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} (valid : ValidTy S Γ A) {Δ : Ctx Head m} {σ σ' : Sub Head n m}
    (vσ : ValidSubst S Γ Δ σ) (vσ' : ValidSubst S Γ Δ σ') (e : EqSubst S Γ Δ σ σ') :
    TypeEq S.R Δ (Presentation.subst σ A) (Presentation.subst σ' A) := by
  obtain ⟨P, r⟩ := valid.red vσ
  exact laws.convTy_sound ((r.escape laws).eqTy (valid.ext vσ vσ' e r))

/-! ## Computation of the eliminator -/

section Computation

variable {J : DeclName} {u v : Head} (decl : DeclaresEliminator S J u v)
include decl

/-- Reducing the path of a full application of the eliminator, at a type equal
to its result type. -/
theorem DeclaresEliminator.scrutinee_red {m : Nat} {Δ : Ctx Head m}
    {a x f d y p q T : Tm Head m}
    (prefixTyping : Typed S.R Δ (appSpine (.const J) [a, x, f, d, y])
      (.pi (.id a x y) (.app (.app (Presentation.rename wk f) (Presentation.rename wk y)) (.var 0))))
    (motive : Typed S.R Δ (.app f y) (.pi (.id a x y) (.head v)))
    (red : RedTm S.R S.roles Δ p q (.id a x y)) (result : TypeEq S.R Δ (.app (.app f y) p) T) :
    RedTm S.R S.roles Δ (appSpine (.const J) [a, x, f, d, y, p])
      (appSpine (.const J) [a, x, f, d, y, q]) T := by
  have change : TypeEq S.R Δ (.app (.app f y) q) T :=
    TypeEq.trans S.levels ⟨v, decl.hv, .appCong (.refl motive) (.symm red.equal)⟩ result
  have source := Derivable.appElim prefixTyping red.source
  have target := Derivable.appElim prefixTyping red.target
  have equal := Derivable.appCong (.refl prefixTyping) red.equal
  rw [inst0_motiveBody] at source target equal
  exact ⟨WhRed.scrutinee (before := [a, x, f, d, y]) (after := []) decl.role rfl red.red,
    Typed.convType source result, Typed.convType target change, Equal.convType equal result⟩

/-- The computation rule at reflexivity, as a typed reduction. -/
theorem DeclaresEliminator.root_red {m : Nat} {Δ : Ctx Head m} {a x f d y z T : Tm Head m}
    (source : Typed S.R Δ (appSpine (.const J) [a, x, f, d, y, .refl z]) T)
    (method : Typed S.R Δ d T) :
    RedTm S.R S.roles Δ (appSpine (.const J) [a, x, f, d, y, .refl z]) d T :=
  ⟨.single (.root decl.rule), source, method, .root decl.rule source method⟩

end Computation

/-! ## The eliminator is semantic -/

section Semantics

variable (laws : S.E.Laws S.R S.roles) {J : DeclName} {u v : Head}
  (decl : DeclaresEliminator S J u v)
include laws decl

/-- At validly equal substitutions of its telescope, the full applications of the
eliminator are reducibly equal at the result type. -/
theorem DeclaresEliminator.rel {m : Nat} {Δ : Ctx Head m} {σ σ' : Sub Head 6 m}
    (validΘ : ValidCtx S (elimTelescope u v)) (validBody : ValidTy S (elimTelescope u v) elimBody)
    (vσ : ValidSubst S (elimTelescope u v) Δ σ) (vσ' : ValidSubst S (elimTelescope u v) Δ σ')
    (e : EqSubst S (elimTelescope u v) Δ σ σ') {P : Pack Head m}
    (r : Reducible S Δ (.app (.app (σ 3) (σ 1)) (σ 0)) P) :
    P.eqTm (appSpine (.const J) [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
      (appSpine (.const J) [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) := by
  have formed := vσ.formed
  have typed := vσ.substMor laws
  have typed' := vσ'.substMor laws
  /- The arguments at `σ`. -/
  obtain ⟨Qx, rX, hx⟩ : ∃ Q, Reducible S Δ (σ 5) Q ∧ Q.redTm (σ 4) := vσ.lookup 4
  obtain ⟨Qf, rF, hf⟩ : ∃ Q, Reducible S Δ (motiveType (σ 5) (σ 4) v) Q ∧ Q.redTm (σ 3) :=
    vσ.lookup 3
  obtain ⟨Qd, rD, hd⟩ : ∃ Q, Reducible S Δ (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) Q ∧
      Q.redTm (σ 2) := vσ.lookup 2
  obtain ⟨Qy, rY, hy⟩ : ∃ Q, Reducible S Δ (σ 5) Q ∧ Q.redTm (σ 1) := vσ.lookup 1
  obtain ⟨Qp, rId, hp⟩ : ∃ Q, Reducible S Δ (.id (σ 5) (σ 4) (σ 1)) Q ∧ Q.redTm (σ 0) :=
    vσ.lookup 0
  obtain ⟨Qe, rIdE, epp⟩ : ∃ Q, Reducible S Δ (.id (σ 5) (σ 4) (σ 1)) Q ∧
      Q.eqTm (σ 0) (σ' 0) := e.lookup 0
  obtain ⟨Qde, rDE, edd⟩ : ∃ Q, Reducible S Δ (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) Q ∧
      Q.eqTm (σ 2) (σ' 2) := e.lookup 2
  have rA := rX.packOf_self laws
  have hx' : (packOf S Δ (σ 5)).redTm (σ 4) := by rw [← rX.eq_packOf laws]; exact hx
  have hy' : (packOf S Δ (σ 5)).redTm (σ 1) := by rw [← rY.eq_packOf laws]; exact hy
  have eA := rA.escape laws
  have tx := (eA.redTm hx').1
  obtain ⟨tyPack, sameId, _, rTy, _, _⟩ := Reducible.id_view rId
  have sameTy : tyPack = packOf S Δ (σ 5) := rTy.eq_packOf laws
  subst sameTy
  have e₁ : Qe = Qp := rIdE.unique laws rId
  subst e₁
  rw [sameId] at epp
  obtain ⟨nf, nf', redp, redp', convPP, prop⟩ := epp
  /- The types at `σ'` are equal to the types at `σ`. -/
  have resultEq : TypeEq S.R Δ (.app (.app (σ 3) (σ 1)) (σ 0))
      (.app (.app (σ' 3) (σ' 1)) (σ' 0)) := validBody.typeEq_at laws vσ vσ' e
  have pathEq : TypeEq S.R Δ (.id (σ 5) (σ 4) (σ 1)) (.id (σ' 5) (σ' 4) (σ' 1)) :=
    (validΘ.lookup 0).typeEq_at laws vσ vσ' e
  /- The motive applied to `y`, at both substitutions. -/
  have motive : Typed S.R Δ (.app (σ 3) (σ 1)) (.pi (.id (σ 5) (σ 4) (σ 1)) (.head v)) := by
    have t₃ : Typed S.R Δ (σ 3) (motiveType (σ 5) (σ 4) v) := typed 3
    have t₁ : Typed S.R Δ (σ 1) (σ 5) := typed 1
    have h := Derivable.appElim t₃ t₁
    rwa [inst0_motiveCod] at h
  have motive' : Typed S.R Δ (.app (σ' 3) (σ' 1)) (.pi (.id (σ' 5) (σ' 4) (σ' 1)) (.head v)) := by
    have t₃ : Typed S.R Δ (σ' 3) (motiveType (σ' 5) (σ' 4) v) := typed' 3
    have t₁ : Typed S.R Δ (σ' 1) (σ' 5) := typed' 1
    have h := Derivable.appElim t₃ t₁
    rwa [inst0_motiveCod] at h
  have prefixTyping := decl.typed_partial typed
  have prefixTyping' := decl.typed_partial typed'
  have rT := r.packOf_self laws
  rw [r.eq_packOf laws]
  rcases prop with ⟨z, z', rfl, rfl, tz, tz', hxz, hxz', hyz, hyz'⟩ | ⟨nN, nN', convN⟩
  · /- Both paths reduce to reflexivity: both applications compute to their methods. -/
    have hxy : (packOf S Δ (σ 5)).eqTm (σ 4) (σ 1) := rA.eqTm_trans laws hxz (rA.eqTm_symm laws hyz)
    have rIdxx := rA.ident laws hx' hx'
    have rIdxy := rA.ident laws hx' hy'
    have idEq : idPack S Δ (σ 5) (σ 4) (σ 1) (packOf S Δ (σ 5)) =
        idPack S Δ (σ 5) (σ 4) (σ 4) (packOf S Δ (σ 5)) :=
      rIdxy.conv laws rIdxx (idPack_eqTy laws rA rA hx' hx' rA.reflexive.eqTy
        (rA.reflexive.eqTm hx') (rA.eqTm_symm laws hxy))
    have reflX : (idPack S Δ (σ 5) (σ 4) (σ 4) (packOf S Δ (σ 5))).redTm (.refl (σ 4)) :=
      ⟨_, RedTm.refl (.reflIntro tx), laws.convTm_refl (eA.redTm hx').2,
        .inl ⟨_, rfl, tx, rA.reflexive.eqTm hx', rA.reflexive.eqTm hx'⟩⟩
    have hp₁ : (idPack S Δ (σ 5) (σ 4) (σ 4) (packOf S Δ (σ 5))).redTm (σ 0) := by
      rw [← idEq, ← sameId]; exact hp
    have tzId : Typed S.R Δ (.refl z) (.id (σ 5) (σ 4) (σ 4)) :=
      Typed.convType redp.target ((rIdxy.escape laws).eqTy
        (by rw [idEq]; exact rIdxx.reflexive.eqTy) |> laws.convTy_sound)
    have reflZ : (idPack S Δ (σ 5) (σ 4) (σ 4) (packOf S Δ (σ 5))).eqTm (.refl (σ 4)) (.refl z) :=
      idPack_refl_eqTm laws rA (rA.reflexive.eqTm hx') hxz (rA.reflexive.eqTm hx') hxz hxz tzId
    have pZ : (idPack S Δ (σ 5) (σ 4) (σ 4) (packOf S Δ (σ 5))).eqTm (σ 0) (.refl z) := by
      rw [← idEq]
      exact (rIdxy.redTm_expand redp (by rw [idEq]; exact (rIdxx.eqTm_redTm laws reflZ).2)).2
    have motivePack := motive_pack laws formed decl.hv rF hf hx' hy' hxy
      (by rw [← rIdxx.eq_packOf laws]; exact reflX)
      (by rw [← rIdxx.eq_packOf laws]; exact hp₁)
      (by rw [← rIdxx.eq_packOf laws]; exact rIdxx.eqTm_trans laws reflZ (rIdxx.eqTm_symm laws pZ))
    obtain ⟨rMethod, samePack⟩ := motivePack
    have methodType : TypeEq S.R Δ (.app (.app (σ 3) (σ 4)) (.refl (σ 4)))
        (.app (.app (σ 3) (σ 1)) (σ 0)) :=
      laws.convTy_sound ((rMethod.escape laws).eqTy (by rw [samePack]; exact rT.reflexive.eqTy))
    have hdd : (packOf S Δ (.app (.app (σ 3) (σ 4)) (.refl (σ 4)))).eqTm (σ 2) (σ' 2) := by
      rw [← rDE.eq_packOf laws]; exact edd
    have td := ((rMethod.escape laws).redTm (rMethod.eqTm_redTm laws hdd).1).1
    have td' := ((rMethod.escape laws).redTm (rMethod.eqTm_redTm laws hdd).2).1
    have resultType : IsType S.R Δ (.app (.app (σ 3) (σ 1)) (σ 0)) :=
      ⟨v, decl.hv, .appElim motive redp.source⟩
    have red₁ := decl.scrutinee_red prefixTyping motive redp resultType.refl
    have redJ := red₁.trans (decl.root_red red₁.target (Typed.convType td methodType))
    have red₁' := decl.scrutinee_red prefixTyping' motive' (redp'.conv pathEq) (TypeEq.symm resultEq)
    have redJ' := red₁'.trans (decl.root_red red₁'.target (Typed.convType td' methodType))
    rw [samePack] at hdd
    exact rT.eqTm_expand laws redJ redJ' hdd
  · /- Both paths are neutral: both applications are stuck and convertible. -/
    have resultType : IsType S.R Δ (.app (.app (σ 3) (σ 1)) (σ 0)) :=
      ⟨v, decl.hv, .appElim motive redp.source⟩
    have redN := decl.scrutinee_red prefixTyping motive redp resultType.refl
    have redN' := decl.scrutinee_red prefixTyping' motive' (redp'.conv pathEq) (TypeEq.symm resultEq)
    have hN : Neutral S.roles (appSpine (.const J) ([σ 5, σ 4, σ 3, σ 2, σ 1] ++ nf :: [])) :=
      .stuck_single decl.role rfl nN
    have hN' : Neutral S.roles
        (appSpine (.const J) ([σ' 5, σ' 4, σ' 3, σ' 2, σ' 1] ++ nf' :: [])) :=
      .stuck_single decl.role rfl nN'
    have conv : ∀ i, S.E.convTm Δ (consSub nf (tailSub σ) i) (consSub nf' (tailSub σ') i)
        (Presentation.subst (consSub nf (tailSub σ)) (Ctx.lookup (elimTelescope u v) i)) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact laws.convTm_of_convNe (.inl nN) (.inl nN') convN
      · obtain ⟨Q, rQ, eQ⟩ := e.lookup j.succ
        have h := (rQ.escape laws).eqTm eQ
        have shape : Ctx.lookup (elimTelescope u v) j.succ =
            Presentation.rename wk (Ctx.lookup (elimPrefix u v) j) := rfl
        rw [shape, subst_rename_wk] at h
        rw [shape, subst_consSub_rename_wk]
        exact h
    have spine := convNe_telescope_apply laws (Θ := elimTelescope u v) (X := elimBody) conv
      (laws.convNe_const J decl.closed)
    rw [applyClosed_elim, applyClosed_elim] at spine
    have pathChange : TypeEq S.R Δ (.app (.app (σ 3) (σ 1)) nf)
        (.app (.app (σ 3) (σ 1)) (σ 0)) :=
      ⟨v, decl.hv, .appCong (.refl motive) (.symm redp.equal)⟩
    have neutralEq := (rT.reflects laws).eqTm hN hN' redN.target redN'.target
      (laws.convNe_conv spine pathChange)
    exact rT.eqTm_expand laws redN redN' neutralEq

/-- The declared type of the eliminator is a valid term of a universe, and its
telescope a valid context. -/
theorem DeclaresEliminator.valid_type :
    ∃ w, S.R.isUniverse w ∧ Typed S.R .nil (elimType u v) (.head w) ∧
      ValidTm S .nil (elimType u v) (.head w) := by
  obtain ⟨w, hw, typed⟩ := decl.typed
  exact ⟨w, hw, Derivable.mono (RulesSub.constantFree S.R) typed,
    Derivable.valid_sub laws (RulesSub.constantFree S.R) SemanticConstantsOf.constantFree typed
      trivial⟩

/-- The full application of the eliminator is valid in its telescope. -/
theorem DeclaresEliminator.valid_full :
    ValidTm S (elimTelescope u v) (applyClosed (elimTelescope u v) ids (.const J)) elimBody := by
  obtain ⟨w, hw, _, validType⟩ := decl.valid_type laws
  obtain ⟨validΘ, validBody⟩ := ValidTy.telescope laws (elimTelescope u v)
    (validType.validTy laws hw)
  refine ⟨validBody, fun {m Δ σ} vσ P r => ?_, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  · have h := decl.rel laws validΘ validBody vσ vσ vσ.refl r
    show P.redTm (appSpine (.const J) [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
    exact (r.eqTm_redTm laws h).1
  · show P.eqTm (appSpine (.const J) [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
      (appSpine (.const J) [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0])
    exact decl.rel laws validΘ validBody vσ vσ' e r

/-- The eliminator is a semantic constant. -/
theorem DeclaresEliminator.semantic : SemanticConstant S J (elimType u v) := by
  obtain ⟨w, hw, typed, validType⟩ := decl.valid_type laws
  exact SemanticConstant.of_telescope laws (.inr ⟨_, decl.role⟩) (Θ := elimTelescope u v) (C := elimBody)
    decl.closed (validType.validTy laws hw) (decl.valid_full laws)

end Semantics

/-! ## The linear rule preserves typing -/

/-- The substitution of the eliminator's telescope by six terms. -/
def elimArgs {n : Nat} (a x f d y p : Tm Head n) : Sub Head 6 n :=
  consSub p (consSub y (consSub d (consSub f (consSub x (consSub a fun i => Fin.elim0 i)))))

section Preservation

variable {S₀ : Setting Head L} (facts : FormFacts S.R S.roles) {J : DeclName}
  {u v : Head} (decl : DeclaresEliminator S₀ J u v) (sub : RulesSub S₀.R S.R)
include facts decl sub

/-- In a typed application of the eliminator at reflexivity, in every package
containing the declaring one, the subject of the reflexivity proof and the
endpoint are equal to the point at the carrier: the
comparisons that a rule with repeated variables makes before firing hold in the
typed equality, by injectivity of identity types. -/
theorem DeclaresEliminator.endpoints {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {a x f d y z T : Tm Head n}
    (typing : Typed S.R Γ (appSpine (.const J) [a, x, f, d, y, .refl z]) T) :
    Equal S.R Γ z x a ∧ Equal S.R Γ y x a := by
  have shape : appSpine (.const J) [a, x, f, d, y, .refl z] =
      applyClosed (elimTelescope u v) (elimArgs a x f d y (.refl z)) (.const J) := by
    rw [applyClosed_elim]
    rfl
  rw [shape] at typing
  obtain ⟨mor, _, _⟩ := Typed.telescope_inv facts formed (elimTelescope u v) elimBody
    (sub.constantType decl.declared) typing
  have tPath : Typed S.R Γ (.refl z) (.id a x y) := mor 0
  obtain ⟨A', tz, leId⟩ := Typed.generation tPath
  have idEqual := TypeLe.id_eq facts leId (Typed.isType tPath formed) formed
  obtain ⟨eA, ezx, ezy⟩ := TypeEq.id_injective facts idEqual formed
  have ezx' := Equal.convType ezx eA
  have ezy' := Equal.convType ezy eA
  exact ⟨ezx', .trans (.symm ezy') ezx'⟩

/-- The linear computation rule of the eliminator preserves typing, in every
package containing the declaring one: in a typed application at reflexivity, the
method has the result type. The comparisons of
the reflexivity subject with the endpoints, which the rule omits, follow from
the typing by injectivity of identity types. -/
theorem DeclaresEliminator.rule_preserves {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {a x f d y z T : Tm Head n}
    (typing : Typed S.R Γ (appSpine (.const J) [a, x, f, d, y, .refl z]) T) :
    Typed S.R Γ d T := by
  obtain ⟨ezx, eyx⟩ := decl.endpoints facts sub formed typing
  have shape : appSpine (.const J) [a, x, f, d, y, .refl z] =
      applyClosed (elimTelescope u v) (elimArgs a x f d y (.refl z)) (.const J) := by
    rw [applyClosed_elim]
    rfl
  rw [shape] at typing
  obtain ⟨mor, _, le⟩ := Typed.telescope_inv facts formed (elimTelescope u v) elimBody
    (sub.constantType decl.declared) typing
  have tMethod : Typed S.R Γ d (.app (.app f x) (.refl x)) := mor 2
  have tMotive : Typed S.R Γ f (motiveType a x v) := mor 3
  /- The method's type is the result type. -/
  have motiveEq := Derivable.appCong (.refl tMotive) (.symm eyx)
  rw [inst0_motiveCod] at motiveEq
  have resultEq : TypeEq S.R Γ (.app (.app f x) (.refl x)) (.app (.app f y) (.refl z)) :=
    ⟨v, sub.isUniverse decl.hv, .appCong motiveEq (.reflCong (.symm ezx))⟩
  exact Typed.subsume (Typed.convType tMethod resultEq) le

end Preservation

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
