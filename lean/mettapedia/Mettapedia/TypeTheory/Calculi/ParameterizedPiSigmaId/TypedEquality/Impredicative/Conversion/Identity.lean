import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Telescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Motives

/-!
# Identity elimination by transport in the conversion model

On the value side identity elimination transports its method along the motive,
`J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`; on the realizer side it is
declared as an eliminator (`DeclaresEliminator`) and computes only at
reflexivity, to its method.

**Validity** (`ValidTmN.transportEliminator`). The values are those of the
transport, as over every realizer algebra. The realizers are read from the
path's realizers, which the identity candidate of the endpoints' relation
relates:

* paths reaching neutral terms make both applications reach neutral spines,
  which the generic equality compares argument by argument;
* paths reaching reflexivity witness that the endpoints are related, so the
  motive's instances have one pack and one shape and the transport has the
  realizers of its method; on the realizer side both applications compute to
  their methods, typed at the result type since a reflexivity proof typed at an
  identity type has its subject equal to both endpoints there
  (`RealizerSide.refl_endpoints`).

**The typed computation step** (`ValidEqN.transportStep`, `TypedRootN.transport`).
At a redex `J a₀ a₁ a₂ a₃ a₄ (refl z)` with the typing facts of its spine, the
path's realizer reaches reflexivity, so the endpoints are related, the redex
computes on the value side to a transport related to the method, and the
declared result's relation is included in that of the redex's type. On the
realizer side the step is a step of the realizer side's computation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open TelescopeAbstraction (closeType applyClosed liftClosed_zero)
open ValueSide (SLe)

variable {Head L : Type} [LevelOrder L]

/-! ## Reflexivity on the realizer side -/

namespace RealizerSide

variable {T : RealizerSide Head L}

/-- **A reflexivity proof typed at an identity type of a formed context has its
subject equal to both endpoints**, on the realizer side: its generated type is
an identity type, usable only at types equal to it, and equal identity types
have equal carriers and endpoints. -/
theorem refl_endpoints {n : Nat} {Γ : Ctx Head n} {z D x y : Tm Head n}
    (formed : CtxFormed T.R Γ) (typeId : IsType T.R Γ (.id D x y))
    (typing : Typed T.R Γ (.refl z) (.id D x y)) :
    Equal T.R Γ z x D ∧ Equal T.R Γ z y D := by
  obtain ⟨A, _, le⟩ := Typed.generation typing
  have form : IsTypeForm T.roles (Tm.id A z z) := .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  have eId : TypeEq T.R Γ (.id A z z) (.id D x y) :=
    Normalization.Below.rigid (S := T.toSetting) (TypeLe.toBelow le typeId) formed
      (fun u _ e => by
        obtain ⟨_, _, _, e', -⟩ := (T.facts.forms e formed form (.inl ⟨u, rfl⟩)).id_left
        cases e')
      (fun B C e => by
        obtain ⟨_, _, _, e', -⟩ := (T.facts.forms e formed form (.inr (.inl ⟨B, C, rfl⟩))).id_left
        cases e')
      (fun B C e => by
        obtain ⟨_, _, _, e', -⟩ :=
          (T.facts.forms e formed form (.inr (.inr (.inl ⟨B, C, rfl⟩)))).id_left
        cases e')
  obtain ⟨_, _, _, e', eA, ezx, ezy⟩ :=
    (T.facts.forms eId formed form (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))).id_left
  cases e'
  exact ⟨Equal.convType ezx eA, Equal.convType ezy eA⟩

end RealizerSide

variable {M : NModel Head L}

/-! ## The typed computation step -/

/-- An argument at the head of a spine whose declared partial type is a
dependent function type, written under a substitution: it is a valid input of
the substituted domain, and the facts continue at the codomain under the
extended substitution. -/
theorem SpineOKN.pi_cons (laws : M.Laws) {m r k : Nat} {ξ : World M.reading m}
    {Δ : Ctx Head r} {τ : Sub Head k m} {D : Tm Head k} {C : Tm Head (k + 1)} {a : Tm Head m}
    {as : List (Tm Head m)} {s : Tm Head r} {ss : List (Tm Head r)} {X : Tm Head m}
    (ok : SpineOKN M ξ Δ (Presentation.subst τ (.pi D C)) (a :: as) (s :: ss) X) :
    (∃ P : NPack M m, DenN M ξ (Presentation.subst τ D) P ∧ P.Val a ∧
        ∃ Y, (P.real a).rel Δ Y s s) ∧
      SpineOKN M ξ Δ (Presentation.subst (consSub a τ) C) as ss X := by
  obtain ⟨A, B, red, val, rest⟩ := ok
  have e : Tm.pi A B = .pi (Presentation.subst τ D) (Presentation.subst (liftSub τ) C) :=
    Consistency.WhRed.of_whnf (Normalization.pi_whnf laws.value.shape _ _) red
  cases e
  rw [Normalization.inst0_subst_liftSub] at rest
  exact ⟨val, rest⟩

/-- **The typed step of identity elimination.** A redex
`J a₀ a₁ a₂ a₃ a₄ (refl z)` with the typing facts of its spine, of an eliminator
declared at `elimType u w`, is validly equal to its method `a₃` at every type at
which both are valid terms, when on the value side the eliminator transports its
method along its motive and the transport table holds, and on the realizer side
it computes at reflexivity to its method. -/
theorem ValidEqN.transportStep (laws : M.Laws) {R : Rules Head} {J coe : DeclName} {u w : Head}
    (hw : M.rules.isUniverse w) (declared : R.constantType J = some (elimType u w))
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      M.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (ValueSide.coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    (transport : ValueSide.CoeRules M.value coe)
    (jRule : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ z : Tm Head m),
      M.side.R.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃)
    {n : Nat} {Γ : Ctx Head n} {a₀ a₁ a₂ a₃ a₄ z A : Tm Head n}
    (facts : SpineFactsN R M Γ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) A)
    (validL : ValidTmN M Γ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) A)
    (validR : ValidTmN M Γ a₃ A) :
    ValidEqN M Γ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃ A := by
  have vlaws := laws.value
  refine ⟨validL, validR, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  have hr := (validR.2 e den).1
  have related : P.rel (Presentation.subst σ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]))
      (Presentation.subst σ' a₃) := by
    rcases facts rfl declared e with ok | total
    swap
    · exact ValueSide.Shape.total_rel (DenN.facts laws) total den _ _
    -- The arguments are valid inputs of the declared telescope, in order.
    let τ₀ : Sub Head 0 m := fun i => Fin.elim0 i
    rw [← TelescopeAbstraction.subst_empty τ₀,
      show elimType u w = .pi (.head u) (.pi (.var 0) (.pi (.pi (.var 1)
        (.pi (.id (.var 2) (.var 1) (.var 0)) (.head w)))
        (.pi (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
          (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0))
            (.app (.app (.var 3) (.var 1)) (.var 0))))))) from rfl] at ok
    obtain ⟨-, ok⟩ := SpineOKN.pi_cons laws ok
    obtain ⟨⟨RA, hRA, h₁, -⟩, ok⟩ := SpineOKN.pi_cons laws ok
    obtain ⟨⟨RF, hRF, h₂, -⟩, ok⟩ := SpineOKN.pi_cons laws ok
    obtain ⟨⟨Q, hQ, h₃, -⟩, ok⟩ := SpineOKN.pi_cons laws ok
    obtain ⟨⟨RA', hRA', -, -⟩, ok⟩ := SpineOKN.pi_cons laws ok
    obtain ⟨⟨PE, hPE, -, Y, real⟩, ok⟩ := SpineOKN.pi_cons laws ok
    change DenN M ξ (Presentation.subst σ a₀) RA at hRA
    change DenN M ξ (motiveType (Presentation.subst σ a₀) (Presentation.subst σ a₁) w) RF
      at hRF
    change DenN M ξ (.app (.app (Presentation.subst σ a₂) (Presentation.subst σ a₁))
      (.refl (Presentation.subst σ a₁))) Q at hQ
    change DenN M ξ (Presentation.subst σ a₀) RA' at hRA'
    change DenN M ξ (.id (Presentation.subst σ a₀) (Presentation.subst σ a₁)
      (Presentation.subst σ a₄)) PE at hPE
    change (PE.real (.refl (Presentation.subst σ z))).rel Δ Y (.refl (Presentation.subst ς z))
      (.refl (Presentation.subst ς z)) at real
    change SLe M.value ξ (.app (.app (Presentation.subst σ a₂) (Presentation.subst σ a₄))
      (.refl (Presentation.subst σ z))) (Presentation.subst σ A) at ok
    obtain rfl := ValueSide.DenS.deterministic vlaws hRA hRA'
    -- The path's realizer is a reflexivity proof: the endpoints are related.
    have endpoints : RA.rel (Presentation.subst σ a₁) (Presentation.subst σ a₄) :=
      DenN.id_endpoints laws hPE hRA real (RedTm.refl ((PE.real _).typed real).1)
    -- The motive's instances have one pack and one shape; the transport is related
    -- to the method.
    obtain ⟨Q', same⟩ := ValueSide.idMotive_shapePair vlaws hw hRF h₂
      (p := .refl (Presentation.subst σ a₁)) (q := .refl (Presentation.subst σ z))
      fun d => ValueSide.DenS.deterministic vlaws d hRA ▸ endpoints
    obtain rfl := ValueSide.DenS.deterministic vlaws ⟨_, same.left⟩ hQ
    have coherent := ValueSide.coe_coherent vlaws (ValueSide.InterpAt.facts vlaws _) transport
      same h₃
    -- The declared result is included in the redex's type.
    have included := ValueSide.SLe.rel vlaws ok ⟨_, same.right⟩ den coherent
    -- The redex computes to the transport on the value side.
    have red : WhRed M.rules M.roles
        (Presentation.subst σ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]))
        (ValueSide.coeApp coe (.app (.app (Presentation.subst σ a₂) (Presentation.subst σ a₁))
            (.refl (Presentation.subst σ a₁)))
          (.app (.app (Presentation.subst σ a₂) (Presentation.subst σ a₄))
            (.refl (Presentation.subst σ z))) (Presentation.subst σ a₃)) := by
      rw [Normalization.subst_appSpine]
      exact .single (.root (jStep _ _ _ _ _ _))
    exact ValueSide.DenS.trans vlaws den ((ValueSide.DenS.expansive vlaws den).left red included)
      hr
  exact ⟨related, ValidEqN.root_real laws (jRule _ _ _ _ _ _) validL validR e den related⟩

/-- **The typed root obligation of identity elimination holds**: at every redex
`J a₀ a₁ a₂ a₃ a₄ (refl z)` of an eliminator declared at `elimType u w`, read
with the typing facts of its spine. -/
theorem TypedRootN.transport (laws : M.Laws) {R : Rules Head} {J coe : DeclName} {u w : Head}
    (hw : M.rules.isUniverse w) (declared : R.constantType J = some (elimType u w))
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      M.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (ValueSide.coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    (transport : ValueSide.CoeRules M.value coe)
    (jRule : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ z : Tm Head m),
      M.side.R.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃)
    {n : Nat} {a₀ a₁ a₂ a₃ a₄ z : Tm Head n} :
    TypedRootN R M (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃ :=
  fun facts validL validR =>
    ValidEqN.transportStep laws hw declared jStep transport jRule facts validL validR

/-! ## Identity elimination -/

/-- **Identity elimination by transport is a valid term of the eliminator's
type at every carrier universe `u` and every motive universe `w`**, when that
type is valid with valid parts. On the value side it computes to the transport
of its method along its motive, and the transport table holds; on the realizer
side it is declared as an eliminator at the same universes. -/
theorem ValidTmN.transportEliminator (laws : M.Laws) {J coe : DeclName} {u w : Head}
    (hw : M.rules.isUniverse w)
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      M.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (ValueSide.coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    (transport : ValueSide.CoeRules M.value coe)
    (decl : DeclaresEliminator M.side.toSetting J u w)
    (validType : ValidTyN M .nil (elimType u w))
    (partsType : StructuredN M .nil (elimType u w)) :
    ValidTmN M .nil (.const J) (elimType u w) := by
  have vlaws := laws.value
  have facts := ValueSide.InterpAt.facts vlaws (M.levels.level w)
  obtain ⟨ctx, validC, _⟩ := ValidTyN.close_parts (elimTelescope u w) (C := elimBody)
    validType partsType
  -- The full application, and its computation to the transport on the value side.
  have app : ∀ {k : Nat} (τ : Sub Head 6 k),
      Presentation.subst τ (applyClosed (elimTelescope u w) ids (liftClosed (.const J))) =
        appSpine (.const J) [τ 5, τ 4, τ 3, τ 2, τ 1, τ 0] := fun _ => rfl
  have red : ∀ {k : Nat} (τ : Sub Head 6 k), WhRed M.rules M.roles
      (Presentation.subst τ (applyClosed (elimTelescope u w) ids (liftClosed (.const J))))
      (ValueSide.coeApp coe (.app (.app (τ 3) (τ 4)) (.refl (τ 4)))
        (.app (.app (τ 3) (τ 1)) (τ 0)) (τ 2)) := fun τ => by
    rw [app τ]
    exact .single (.root (jStep _ _ _ _ _ _))
  have typedJ : Typed M.side.R .nil (.const J) (elimType u w) := by
    have h := decl.closed (Δ := .nil)
    rwa [liftClosed_zero] at h
  refine ValidTmN.close laws (elimTelescope u w) (C := elimBody) (f := .const J) validType
    partsType typedJ (fun args short => .inr (.inr ⟨J, args, 6, .inr ⟨_, decl.role⟩, short, rfl⟩))
    ⟨validC, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  have e₀ := e
  obtain ⟨⟨⟨⟨⟨⟨-, RU, -, -, rU⟩, RA, denA, hx, rx⟩, RP, denP, hP, rP⟩, Rd, dend, hd, rd⟩,
    RA', denA', hy, ry⟩, Re, denE, -, re⟩ := e₀
  change DenN M ξ (σ 5) RA at denA
  change RA.rel (σ 4) (σ' 4) at hx
  change DenN M ξ (motiveType (σ 5) (σ 4) w) RP at denP
  change RP.rel (σ 3) (σ' 3) at hP
  change DenN M ξ (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) Rd at dend
  change Rd.rel (σ 2) (σ' 2) at hd
  change (Rd.real (σ 2)).rel Δ (.app (.app (ς 3) (ς 4)) (.refl (ς 4))) (ς 2) (ς' 2) at rd
  change DenN M ξ (σ 5) RA' at denA'
  change RA'.rel (σ 1) (σ' 1) at hy
  change DenN M ξ (.id (σ 5) (σ 4) (σ 1)) Re at denE
  change (Re.real (σ 0)).rel Δ (.id (ς 5) (ς 4) (ς 1)) (ς 0) (ς' 0) at re
  change DenN M ξ (.app (.app (σ 3) (σ 1)) (σ 0)) P at den
  rw [ValueSide.DenS.deterministic vlaws denA' denA] at hy
  have uniq : ∀ {RA'' : NPack M m}, DenN M ξ (σ 5) RA'' → RA'' = RA :=
    fun d => ValueSide.DenS.deterministic vlaws d denA
  -- Values: the instances at the base point, and at the endpoint, form pairs of
  -- one shape with one pack, and the transport respects related methods.
  obtain ⟨Q, sources⟩ := ValueSide.idMotive_shapePair vlaws hw denP hP (p := .refl (σ 4))
    (q := .refl (σ' 4)) fun d => uniq d ▸ hx
  obtain ⟨Q', targets⟩ := ValueSide.idMotive_shapePair vlaws hw denP hP (p := σ 0) (q := σ' 0)
    fun d => uniq d ▸ hy
  obtain rfl := ValueSide.DenS.deterministic vlaws dend ⟨_, sources.left⟩
  obtain rfl := ValueSide.DenS.deterministic vlaws den ⟨_, targets.left⟩
  have value := ValueSide.coe_congr vlaws facts transport sources targets hd
  have expansive := ValueSide.DenS.expansive vlaws den
  refine ⟨expansive.left (red σ) (expansive.right (red σ') value), ?_⟩
  -- Realizers: the realizers of the application are those of the transport.
  have toTransport := expansive.left (red σ) (ValueSide.DenS.refl_left vlaws den value)
  rw [ValueSide.DenS.real_eq_of_rel vlaws den toTransport, app ς, app ς']
  -- Typings on the realizer side.
  have formed := e.formed
  have typed := e.substMor
  have typed' := EqSubstN.substMor_right laws ctx.valid e
  have motive : Typed M.side.R Δ (.app (ς 3) (ς 1)) (.pi (.id (ς 5) (ς 4) (ς 1)) (.head w)) := by
    have t₃ : Typed M.side.R Δ (ς 3) (motiveType (ς 5) (ς 4) w) := typed 3
    have t₁ : Typed M.side.R Δ (ς 1) (ς 5) := typed 1
    have h := Derivable.appElim t₃ t₁
    rwa [inst0_motiveCod] at h
  have motive' : Typed M.side.R Δ (.app (ς' 3) (ς' 1))
      (.pi (.id (ς' 5) (ς' 4) (ς' 1)) (.head w)) := by
    have t₃ : Typed M.side.R Δ (ς' 3) (motiveType (ς' 5) (ς' 4) w) := typed' 3
    have t₁ : Typed M.side.R Δ (ς' 1) (ς' 5) := typed' 1
    have h := Derivable.appElim t₃ t₁
    rwa [inst0_motiveCod] at h
  have prefixTyping := decl.typed_partial typed
  have prefixTyping' := decl.typed_partial typed'
  -- The two instances of the path's type and of the result type are equal.
  have e₅ : Equal M.side.R Δ (ς 5) (ς' 5) (.head u) := (RU.real _).equal rU
  have e₄ : Equal M.side.R Δ (ς 4) (ς' 4) (ς 5) := (RA.real _).equal rx
  have e₁ : Equal M.side.R Δ (ς 1) (ς' 1) (ς 5) := (RA'.real _).equal ry
  have pathEq : TypeEq M.side.R Δ (.id (ς 5) (ς 4) (ς 1)) (.id (ς' 5) (ς' 4) (ς' 1)) :=
    ⟨u, decl.hu, .idCong e₅ decl.hu e₄ e₁⟩
  obtain ⟨-, -, -, types⟩ := validC e
  have resultEq : TypeEq M.side.R Δ (.app (.app (ς 3) (ς 1)) (ς 0))
      (.app (.app (ς' 3) (ς' 1)) (ς' 0)) := types.typeEq
  rw [ValueSide.DenS.id_real vlaws denE denA (σ 0)] at re
  rcases re with ⟨w₀, w₀', r₀, r₀', nw, nw', cv⟩ | ⟨⟨_, _, _, hId⟩, ⟨z, r₀⟩, ⟨z', r₀'⟩, -, endpoints⟩
  · -- Paths reaching neutral terms: both applications reach neutral spines.
    have resultType : IsType M.side.R Δ (.app (.app (ς 3) (ς 1)) (ς 0)) :=
      ⟨w, decl.hv, .appElim motive r₀.source⟩
    have redN := decl.scrutinee_red prefixTyping motive r₀ resultType.refl
    have redN' := decl.scrutinee_red prefixTyping' motive' (r₀'.conv pathEq) resultEq.symm
    have hN : Neutral M.side.roles
        (appSpine (.const J) ([ς 5, ς 4, ς 3, ς 2, ς 1] ++ w₀ :: [])) :=
      .stuck_single decl.role rfl nw
    have hN' : Neutral M.side.roles
        (appSpine (.const J) ([ς' 5, ς' 4, ς' 3, ς' 2, ς' 1] ++ w₀' :: [])) :=
      .stuck_single decl.role rfl nw'
    have conv : ∀ i, M.side.E.convTm Δ (consSub w₀ (tailSub ς) i) (consSub w₀' (tailSub ς') i)
        (Presentation.subst (consSub w₀ (tailSub ς)) (Ctx.lookup (elimTelescope u w) i)) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact M.side.laws.convTm_of_convNe (.inl nw) (.inl nw') cv
      · obtain ⟨Pj, -, -, hj⟩ := e.lookup j.succ
        have h := (Pj.real _).escape hj
        have shape : Ctx.lookup (elimTelescope u w) j.succ =
            Presentation.rename wk (Ctx.lookup (elimPrefix u w) j) := rfl
        rw [shape, subst_rename_wk] at h
        rw [shape, subst_consSub_rename_wk]
        exact h
    have spine := convNe_telescope_apply M.side.laws (Θ := elimTelescope u w) (X := elimBody)
      conv (M.side.laws.convNe_const J decl.closed)
    rw [applyClosed_elim, applyClosed_elim] at spine
    have pathChange : TypeEq M.side.R Δ (.app (.app (ς 3) (ς 1)) w₀)
        (.app (.app (ς 3) (ς 1)) (ς 0)) :=
      ⟨w, decl.hv, .appCong (.refl motive) (.symm r₀.equal)⟩
    exact ECand.expand _ redN redN'
      (ECand.neutral _ hN hN' redN.target redN'.target (M.side.laws.convNe_conv spine pathChange))
  · -- Paths reaching reflexivity: the endpoints are related, the transport has the
    -- realizers of the method, and both applications compute to their methods.
    obtain ⟨Q'', same⟩ := ValueSide.idMotive_shapePair vlaws hw denP
      (ValueSide.DenS.refl_left vlaws denP hP) (p := .refl (σ 4)) (q := σ 0)
      fun d => uniq d ▸ endpoints
    obtain rfl := ValueSide.DenS.deterministic vlaws ⟨_, same.left⟩ ⟨_, sources.left⟩
    rw [ValueSide.coe_realAt vlaws transport same (ValueSide.DenS.refl_left vlaws dend hd)
      ⟨_, targets.left⟩]
    -- On the realizer side the subject of the reflexivity proof is equal to both
    -- endpoints, so the method's type is the result type.
    have t₅ : Typed M.side.R Δ (ς 5) (.head u) := typed 5
    obtain ⟨ez₄, ez₁⟩ := RealizerSide.refl_endpoints formed hId.sourceType r₀.target
    have e₄₁ : Equal M.side.R Δ (ς 4) (ς 1) (ς 5) := .trans (.symm ez₄) ez₁
    have idEq : TypeEq M.side.R Δ (.id (ς 5) z z) (.id (ς 5) (ς 4) (ς 1)) :=
      ⟨u, decl.hu, .idCong (.refl t₅) decl.hu ez₄ ez₁⟩
    have idEq' : TypeEq M.side.R Δ (.id (ς 5) (ς 4) (ς 1)) (.id (ς 5) (ς 4) (ς 4)) :=
      ⟨u, decl.hu, .idCong (.refl t₅) decl.hu (.refl (typed 4)) (.symm e₄₁)⟩
    have pathRefl : Equal M.side.R Δ (ς 0) (.refl (ς 4)) (.id (ς 5) (ς 4) (ς 4)) :=
      Equal.convType (.trans r₀.equal (Equal.convType (.reflCong ez₄) idEq)) idEq'
    have t₃ : Typed M.side.R Δ (ς 3) (motiveType (ς 5) (ς 4) w) := typed 3
    have motiveEq := Derivable.appCong (.refl t₃) e₄₁
    rw [inst0_motiveCod] at motiveEq
    have methodType : TypeEq M.side.R Δ (.app (.app (ς 3) (ς 4)) (.refl (ς 4)))
        (.app (.app (ς 3) (ς 1)) (ς 0)) :=
      ⟨w, decl.hv, .appCong motiveEq (.symm pathRefl)⟩
    obtain ⟨td, td'⟩ := ECand.typed _ rd
    have resultType : IsType M.side.R Δ (.app (.app (ς 3) (ς 1)) (ς 0)) :=
      ⟨w, decl.hv, .appElim motive r₀.source⟩
    have red₁ := decl.scrutinee_red prefixTyping motive r₀ resultType.refl
    have redJ := red₁.trans (decl.root_red red₁.target (Typed.convType td methodType))
    have red₁' := decl.scrutinee_red prefixTyping' motive' (r₀'.conv pathEq) resultEq.symm
    have redJ' := red₁'.trans (decl.root_red red₁'.target (Typed.convType td' methodType))
    exact ECand.expand _ redJ redJ' (ECand.conv _ formed methodType rd)

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
