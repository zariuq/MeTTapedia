import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Motives
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Eliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Spines

/-!
# Identity elimination by transport, at every level

On the value side identity elimination transports its method along the
motive, `J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`; on the realizer side it
computes only at reflexivity, to its method. Such an eliminator is a valid term
of `elimType u w` for every carrier universe `u` and every motive universe `w`,
when that type is valid with valid parts (`ValidTmS.transportEliminator`).

* **Values.** A motive related to another sends related points and any two
  paths to types related in the motive's universe: one pack and one shape
  (`ValueSide.idMotive_universe`). So the motive's instances at the base point with
  reflexivity form a pair of one shape with one pack, and so do its instances
  at the endpoint with the path, and the transport respects related methods
  between such pairs (`ValueSide.coe_congr`).
* **Realizers.** A realizer of the path reduces to reflexivity only when the
  endpoints are related. Then the motive has one pack and one shape at both of
  its instances, the transport between them has the realizers of its method
  (`ValueSide.coe_realAt`), and the realizer of the method realizes the value.

No premise is placed on the carrier's universe: the transport reads the
motive's instances, which the universe relation relates with one shape at every
level. A cast returns its method whatever those instances are, so it needs them
to agree.

This is term validity. The object package's own computation rule
`J A x P d y (refl z) ⟶ d` is a different matter: it is not a step of the value
side, and read without its typing its root obligation can fail, at a redex whose
path `refl z` is no path from the base point.

## The typed computation step

At a typed redex the rule holds (`ValidEqS.transportStep`,
`TypedRootS.transport`). The typing facts of the spine
`J a₀ a₁ a₂ a₃ a₄ (refl z)` make its arguments, under related valuations, valid
inputs of the declared telescope, and put the declared result `a₂ a₄ (refl z)`
structurally below the type of the redex; or that type relates every pair.

* The path `refl z` is valid at `Id a₀ a₁ a₄`, with its realizer: the realizer
  reduces to reflexivity, so `a₁` and `a₄` are related at the carrier
  (`DenS.id_endpoints`).
* The motive then gives one pack and one shape for `a₂ a₁ (refl a₁)` and
  `a₂ a₄ (refl z)` (`ValueSide.idMotive_shapePair`), and the transport between them is
  related to the method (`ValueSide.coe_coherent`).
* The redex computes to that transport on the value side, and the declared
  result's relation is included in that of the redex's type (`ValueSide.SLe.rel`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization (WhRed WhStep appSpine elimType elimTelescope elimBody motiveType
  inst0_motiveCod)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open TelescopeAbstraction (applyClosed)
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SModel Head L}

/-! ## Identity elimination -/

/-- **Identity elimination by transport is a valid term of the eliminator's
type at every carrier universe `u` and every motive universe `w`**, when that
type is valid with valid parts. On the value side it computes to the transport
of its method along its motive, and the transport table holds; on the realizer
side it computes only at reflexivity, to its method. -/
theorem ValidTmS.transportEliminator (laws : M.Laws) {J coe : DeclName} {u w : Head}
    (hw : M.rules.isUniverse w)
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      M.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    (transport : CoeRules M.value coe)
    (role : M.realizers.roles J = .computes 6 (.split 5 .constructor fun _ => .leaf))
    (jRoot : ∀ {m : Nat} {a₀ a₁ a₂ a₃ a₄ a₅ r : Tm Head m},
      M.realizers.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅]) r →
        ∃ c, a₅ = .refl c ∧ r = a₃)
    (validType : ValidTyS M .nil (elimType u w))
    (partsType : StructuredS M .nil (elimType u w)) :
    ValidTmS M .nil (.const J) (elimType u w) := by
  have vlaws := laws.value
  have facts := InterpAt.facts vlaws (M.levels.level w)
  obtain ⟨_, validC, _⟩ := ValidTyS.close_parts (elimTelescope u w) (C := elimBody)
    validType partsType
  -- The full application, and its computation to the transport on the value side.
  have app : ∀ {k : Nat} (τ : Sub Head 6 k),
      Presentation.subst τ (applyClosed (elimTelescope u w) ids (liftClosed (.const J))) =
        appSpine (.const J) [τ 5, τ 4, τ 3, τ 2, τ 1, τ 0] := fun _ => rfl
  have red : ∀ {k : Nat} (τ : Sub Head 6 k), WhRed M.rules M.roles
      (Presentation.subst τ (applyClosed (elimTelescope u w) ids (liftClosed (.const J))))
      (coeApp coe (.app (.app (τ 3) (τ 4)) (.refl (τ 4))) (.app (.app (τ 3) (τ 1)) (τ 0))
        (τ 2)) := fun τ => by
    rw [app τ]
    exact .single (.root (jStep _ _ _ _ _ _))
  refine ValidTmS.close laws (elimTelescope u w) (C := elimBody) (f := .const J) validType
    partsType ⟨validC, fun {m r ξ σ σ' ς} e {P} den => ?_⟩
  have sn := e.real_sn
  obtain ⟨⟨⟨⟨⟨⟨-, -, -, -, -⟩, RA, denA, hx, -⟩, RP, denP, hP, -⟩, Rd, dend, hd, rd⟩,
    RA', denA', hy, -⟩, Re, denE, -, re⟩ := e
  change DenS M.value ξ (σ 5) RA at denA
  change RA.rel (σ 4) (σ' 4) at hx
  change DenS M.value ξ (motiveType (σ 5) (σ 4) w) RP at denP
  change RP.rel (σ 3) (σ' 3) at hP
  change DenS M.value ξ (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) Rd at dend
  change Rd.rel (σ 2) (σ' 2) at hd
  change (Rd.real (σ 2)).mem (ς 2) at rd
  change DenS M.value ξ (σ 5) RA' at denA'
  change RA'.rel (σ 1) (σ' 1) at hy
  change DenS M.value ξ (.id (σ 5) (σ 4) (σ 1)) Re at denE
  change (Re.real (σ 0)).mem (ς 0) at re
  change DenS M.value ξ (.app (.app (σ 3) (σ 1)) (σ 0)) P at den
  rw [DenS.deterministic vlaws denA' denA] at hy
  have uniq : ∀ {RA'' : Pack M.value m}, DenS M.value ξ (σ 5) RA'' → RA'' = RA :=
    fun d => DenS.deterministic vlaws d denA
  -- Values: the instances at the base point, and at the endpoint, form pairs of
  -- one shape with one pack, and the transport respects related methods.
  obtain ⟨Q, sources⟩ := idMotive_shapePair laws.value hw denP hP (p := .refl (σ 4))
    (q := .refl (σ' 4)) fun d => uniq d ▸ hx
  obtain ⟨Q', targets⟩ := idMotive_shapePair laws.value hw denP hP (p := σ 0) (q := σ' 0)
    fun d => uniq d ▸ hy
  obtain rfl := DenS.deterministic vlaws dend ⟨_, sources.left⟩
  obtain rfl := DenS.deterministic vlaws den ⟨_, targets.left⟩
  have value := coe_congr vlaws facts transport sources targets hd
  have expansive := DenS.expansive vlaws den
  refine ⟨expansive.left (red σ) (expansive.right (red σ') value), ?_⟩
  -- Realizers: the path's realizer reduces to reflexivity only at related
  -- endpoints, where the transport has the realizers of the method.
  have toTransport := expansive.left (red σ) (DenS.refl_left vlaws den value)
  rw [app ς, DenS.real_eq_of_rel vlaws den toTransport]
  rw [DenS.id_real vlaws denE denA (σ 0)] at re
  refine KCand.eliminator_mem M.realizers.shape M.realizers.reflects _ role jRoot (sn 5) (sn 4)
    (sn 3) (sn 2) (sn 1) re fun related => ?_
  obtain ⟨Q'', same⟩ := idMotive_shapePair laws.value hw denP (DenS.refl_left vlaws denP hP)
    (p := .refl (σ 4)) (q := σ 0) fun d => uniq d ▸ related
  obtain rfl := DenS.deterministic vlaws ⟨_, same.left⟩ dend
  rw [coe_realAt laws.value transport same (DenS.refl_left vlaws dend hd) den]
  exact rd

/-! ## The typed computation step -/

/-- The declared type of the eliminator, as nested dependent function types. -/
theorem elimType_eq (u w : Head) : elimType u w =
    .pi (.head u) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head w)))
      (.pi (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
        (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0))
          (.app (.app (.var 3) (.var 1)) (.var 0))))))) :=
  rfl

/-- An argument at the head of a spine whose declared partial type is a
dependent function type, written under a substitution: it is a valid input of
the substituted domain, and the facts continue at the codomain under the
extended substitution. -/
theorem SpineOK.pi_cons (laws : M.Laws) {m r k : Nat} {ξ : World M.reading m}
    {τ : Sub Head k m} {D : Tm Head k} {C : Tm Head (k + 1)} {a : Tm Head m}
    {as : List (Tm Head m)} {s : Tm Head r} {ss : List (Tm Head r)} {X : Tm Head m}
    (ok : SpineOK M ξ (Presentation.subst τ (.pi D C)) (a :: as) (s :: ss) X) :
    (∃ P, DenS M.value ξ (Presentation.subst τ D) P ∧ P.Val a ∧ (P.real a).mem s) ∧
      SpineOK M ξ (Presentation.subst (consSub a τ) C) as ss X := by
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
method along its motive and the transport table holds. -/
theorem ValidEqS.transportStep (laws : M.Laws) {R : Rules Head} {J coe : DeclName} {u w : Head}
    (hw : M.rules.isUniverse w) (declared : R.constantType J = some (elimType u w))
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      M.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    (transport : CoeRules M.value coe) {n : Nat} {Γ : Ctx Head n}
    {a₀ a₁ a₂ a₃ a₄ z A : Tm Head n}
    (facts : SpineFacts R M Γ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) A)
    (validL : ValidTmS M Γ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) A)
    (validR : ValidTmS M Γ a₃ A) :
    ValidEqS M Γ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃ A := by
  have vlaws := laws.value
  refine ⟨validL, validR, fun {m r ξ σ σ' ς} e {P} den => ?_⟩
  have hr := (validR.2 e den).1
  rcases facts rfl declared e with ok | total
  swap
  · exact Shape.total_rel (DenS.facts vlaws) total den _ _
  -- The arguments are valid inputs of the declared telescope, in order.
  let τ₀ : Sub Head 0 m := fun i => Fin.elim0 i
  rw [← TelescopeAbstraction.subst_empty τ₀, elimType_eq] at ok
  obtain ⟨-, ok⟩ := SpineOK.pi_cons laws ok
  obtain ⟨⟨RA, hRA, h₁, -⟩, ok⟩ := SpineOK.pi_cons laws ok
  obtain ⟨⟨RF, hRF, h₂, -⟩, ok⟩ := SpineOK.pi_cons laws ok
  obtain ⟨⟨Q, hQ, h₃, -⟩, ok⟩ := SpineOK.pi_cons laws ok
  obtain ⟨⟨RA', hRA', h₄, -⟩, ok⟩ := SpineOK.pi_cons laws ok
  obtain ⟨⟨PE, hPE, -, real⟩, ok⟩ := SpineOK.pi_cons laws ok
  change DenS M.value ξ (Presentation.subst σ a₀) RA at hRA
  change DenS M.value ξ (motiveType (Presentation.subst σ a₀) (Presentation.subst σ a₁) w) RF
    at hRF
  change DenS M.value ξ (.app (.app (Presentation.subst σ a₂) (Presentation.subst σ a₁))
    (.refl (Presentation.subst σ a₁))) Q at hQ
  change DenS M.value ξ (Presentation.subst σ a₀) RA' at hRA'
  change DenS M.value ξ (.id (Presentation.subst σ a₀) (Presentation.subst σ a₁)
    (Presentation.subst σ a₄)) PE at hPE
  change (PE.real (.refl (Presentation.subst σ z))).mem (.refl (Presentation.subst ς z)) at real
  change SLe M ξ (.app (.app (Presentation.subst σ a₂) (Presentation.subst σ a₄))
    (.refl (Presentation.subst σ z))) (Presentation.subst σ A) at ok
  obtain rfl := DenS.deterministic vlaws hRA hRA'
  -- The path's realizer reduces to reflexivity: the endpoints are related.
  have related : RA.rel (Presentation.subst σ a₁) (Presentation.subst σ a₄) :=
    DenS.id_endpoints laws hPE hRA real .refl
  -- The motive's instances have one pack and one shape; the transport is related
  -- to the method.
  obtain ⟨Q', same⟩ :=
    idMotive_shapePair laws.value hw hRF h₂ (p := .refl (Presentation.subst σ a₁))
      (q := .refl (Presentation.subst σ z))
      fun d => DenS.deterministic vlaws d hRA ▸ related
  obtain rfl := DenS.deterministic vlaws ⟨_, same.left⟩ hQ
  have coherent := coe_coherent vlaws (InterpAt.facts vlaws _) transport same h₃
  -- The declared result is included in the redex's type.
  have included := SLe.rel laws.value ok ⟨_, same.right⟩ den coherent
  -- The redex computes to the transport on the value side.
  have red : WhRed M.rules M.roles
      (Presentation.subst σ (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]))
      (coeApp coe (.app (.app (Presentation.subst σ a₂) (Presentation.subst σ a₁))
          (.refl (Presentation.subst σ a₁)))
        (.app (.app (Presentation.subst σ a₂) (Presentation.subst σ a₄))
          (.refl (Presentation.subst σ z))) (Presentation.subst σ a₃)) := by
    rw [Normalization.subst_appSpine]
    exact .single (.root (jStep _ _ _ _ _ _))
  exact den.trans vlaws ((DenS.expansive vlaws den).left red included) hr

/-- **The typed root obligation of identity elimination holds**: at every redex
`J a₀ a₁ a₂ a₃ a₄ (refl z)` of an eliminator declared at `elimType u w`, read
with the typing facts of its spine. -/
theorem TypedRootS.transport (laws : M.Laws) {R : Rules Head} {J coe : DeclName} {u w : Head}
    (hw : M.rules.isUniverse w) (declared : R.constantType J = some (elimType u w))
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      M.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    (transport : CoeRules M.value coe) {n : Nat} {a₀ a₁ a₂ a₃ a₄ z : Tm Head n} :
    TypedRootS R M (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃ :=
  fun facts validL validR =>
    ValidEqS.transportStep laws hw declared jStep transport facts validL validR

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
