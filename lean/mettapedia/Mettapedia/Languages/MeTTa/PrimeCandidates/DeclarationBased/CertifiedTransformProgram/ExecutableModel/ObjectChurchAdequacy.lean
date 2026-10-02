import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchForms

/-!
# Adequacy of the object package's constants: the sets, the codes and the definitions

**The sets are observed by nothing.** No token is typed at a ground type
(`not_typedAt_groundI`): the typing of a token names a universe, the numbers, a dependent
type or an identity type among the tags of its type, and a ground type has only its own
tag. So every term of type `set` is adequate there, and the power set `Power : set → set`
and the iterated power set `pow : num → set → set` are adequate through their spines
(`constAdequateAt_power`, `constAdequateAt_pow`).

**The codes are adequate through their decodings.** A code is adequate at `prop` when its
decoding, reached by one root step of the decoder, is an adequate type whose denotation
contains the code's typed tokens (`Adequate.ofDecoding`). The decoder applied to a code
variable is an adequate type (`adequateType_holdsVar`); so the decoder
(`constAdequateAt_holds`), implication, decoded as `holds p → holds q`
(`constAdequateAt_imp`), and the equation at every simple type, decoded as the identity
type `Id A x y` (`constAdequateAt_eq`), are adequate through their spines.

**The definitions by one equation** are adequate: their applications reduce to their right
sides by one root step, and each right side is typed within constants already adequate, so
the fundamental lemma within those constants makes it adequate.

* `transportCert` and `composeCert` (`constAdequateAt_transport`, `constAdequateAt_compose`):
  their right sides use no constant;
* `returnIter` (`constAdequateAt_returnIter`): its right side, five abstractions over the
  iterator's spine, uses the numbers and the iterator;
* `sucStep` (`constAdequateAt_sucStep`): its right side, `transportCert` at the numbers,
  `eqAt`, the successor and the successor move, uses those constants.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal
  (projT TypedAt principal codesIdeal univIdeal groundI)
open TelescopeAbstraction (applyClosed)
open FormationSensitiveHOLInterface (typeAt)
open Package (transportName composeName transportTelescope composeTelescope)
open Mettapedia.Logic

namespace CodeModel

/-! ## Nothing is typed at a ground type -/

/-- **No token is typed by the ground element**: every clause of the typing of a token
names the universe, the universe of codes, the numbers, a dependent type or an identity
type among the tags of its type. -/
theorem not_tyTok_ground (t : Tok) : ¬ TyTok Elem.ground t := by
  have nmem : ∀ {k : Kind}, k ≠ .ground → Tok.tag k ∉ Elem.ground := fun hk h =>
    hk (Tok.tag.inj (List.mem_singleton.1 h))
  have nuniv : ¬ IsUniv Elem.ground := fun h =>
    h.elim (nmem (by decide)) (nmem (by decide))
  intro ht
  cases t with
  | tag k =>
      rcases tag_cases k with hk | rfl | rfl | rfl | rfl | rfl
      · exact nuniv ((tyTok_tag_former hk).1 ht)
      · exact nmem (by decide) (tyTok_tag_zero.1 ht)
      · exact nmem (by decide) (tyTok_tag_succ.1 ht)
      · exact nmem (by decide) (tyTok_tag_refl.1 ht)
      · exact tyTok_tag_lam ht
      · exact tyTok_tag_pair ht
  | arg k i C s =>
      rcases Decidable.em ((k, i) ∈ argSlots) with hs | hother
      swap
      · exact tyTok_arg_other hother ht
      simp only [argSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact nuniv ((tyTok_dom (.inl rfl)).1 ht).1
      · exact nuniv ((tyTok_dom (.inr (.inl rfl))).1 ht).1
      · exact nuniv ((tyTok_dom (.inr (.inr rfl))).1 ht).1
      · exact nuniv ((tyTok_endpoint (.inl rfl)).1 ht).1
      · exact nuniv ((tyTok_endpoint (.inr rfl)).1 ht).1
      · exact nmem (by decide) (tyTok_pred.1 ht).1
      · exact nmem (by decide) (tyTok_reflPoint.1 ht).1
      · exact nmem (by decide) (tyTok_fst.1 ht).1
      · exact nmem (by decide) (tyTok_snd.1 ht).1
  | fn k C X Y =>
      rcases fn_cases k with hk | rfl | hother
      · exact nuniv ((tyTok_family hk).1 ht).1
      · exact nmem (by decide) (tyTok_lam.1 ht).1
      · exact tyTok_fn_other hother ht

/-- **No token is typed at a ground type**: a compact type below a ground type is entailed
by the ground element, and typing is monotone in the type. -/
theorem not_typedAt_groundI (t : Tok) : ¬ TypedAt groundI t := by
  rintro ⟨a, ha, -, ht⟩
  exact not_tyTok_ground t (TyTok.mono (fun s hs => Ideal.mem_principal.1 (ha s hs)) ht)

/-- **Every term of type `set` is adequate there**: no token is typed at the sets. -/
theorem adequate_cset {k : Nat} {Θ : CCtx Tower.Head k} (t : CTm Tower.Head k) :
    Adequate objectChurchReading objectHeadReduction Θ t cset := by
  intro ρ _ m Δ σ σ' _ _ s _ hsT
  rw [cinterp_cset] at hsT
  exact (not_typedAt_groundI s hsT).elim

/-- **The power set is adequate**, through its spine at a variable of type `set`. -/
theorem constAdequateAt_power : ConstAdequateAt objectChurchReading objectHeadReduction powerN :=
  ConstAdequateAt.of_spine (Θ := .snoc .nil cset) (T := cset) ConvRules.objectLevels
    objectChurch_soundnessFacts
    (objectChurch_declared (c := powerN) (T := powerType) (by decide) rfl)
    (.appElim (B := cset) cpowerConst_typed (.var 0)) (adequate_cset _)

/-- **The iterated power set is adequate**, through its spine at a number and a set. -/
theorem constAdequateAt_pow : ConstAdequateAt objectChurchReading objectHeadReduction powN :=
  ConstAdequateAt.of_spine (Θ := .snoc (.snoc .nil cnum) cset) (T := cset) ConvRules.objectLevels
    objectChurch_soundnessFacts (objectChurch_declared (c := powN) (T := powType) (by decide) rfl)
    (CDerivable.appElim (CDerivable.appElim (cpowConst_typed (Γ := .snoc (.snoc .nil cnum) cset))
      (.var 1)) (.var 0)) (adequate_cset _)

/-! ## Codes through their decodings -/

section Codes

variable {k : Nat} {Θ : CCtx Tower.Head k}

/-- The type of proposition codes reduces to itself, in every context. -/
theorem propRed {m : Nat} {Δ : CCtx Tower.Head m} :
    CRedTy objectHeadReduction Δ (.const propN) (.const propN) :=
  CRedTy.refl ⟨_, .sort _, const_U0_typed (by decide)⟩

/-- **The decoder applied to a code variable is an adequate type**: a type token of the
decoded value is entailed by typed code tokens of the variable's value, at which the
substituted codes are related; their decodings are then related as types. -/
theorem adequateType_holdsVar (i : Fin k) (hi : Θ.lookup i = .const propN) :
    AdequateType objectChurchReading objectHeadReduction Θ (.app (.const holdsN) (.var i)) := by
  intro ρ _ m Δ σ σ' _ hσ r hr _
  change (Ideal.app (objectChurchReading.const holdsN) (ρ i)).Mem r at hr
  rw [objectChurchReading_holds, Ideal.app_holdsConst_eq] at hr
  obtain ⟨v, hv, hvT, e⟩ := Ideal.projT_eq_iSup.1 hr
  refine RT.closed' e fun g hg => ?_
  have hgU : TyTok Elem.univ g := Ideal.typedAt_codes_iff.1 (hvT g hg)
  have rel := (hσ.2 i).2.2 g (hv g hg) (by rw [hi, cinterp_propT]; exact hvT g hg)
  rw [hi] at rel
  exact RT.toCodes (typeKind_of_tyTok_univ hgU) propRed rel

/-- **A code is adequate through its decoding.** Let the code `c` be typed at `prop`, its
decoding `D` be typed at `U₀`, the decoder applied to every instance of `c` take a root
step to the instance of `D`, admitted at the typed instances, `D` be an adequate type, and the code's typed tokens lie in
the decoding's denotation. Then `c` is adequate at `prop`: its instances are related by
the clause of the codes, their decodings head-expanded along the root steps. -/
theorem Adequate.ofDecoding {c D : CTm Tower.Head k}
    (tc : CTyped objectChurch Θ c (.const propN)) (tD : CTyped objectChurch Θ D cU0)
    (step : ∀ {m : Nat} (σ : CSub Tower.Head k m),
      objectChurch.computation.step (.app (.const holdsN) (c.subst σ)) (D.subst σ))
    (admits : ∀ {m : Nat} {Δ : CCtx Tower.Head m} {σ : CSub Tower.Head k m},
      CSubstMor objectChurch Θ Δ σ →
        objectChurch.Admits Δ (.app (.const holdsN) (c.subst σ)) (D.subst σ))
    (hD : AdequateType objectChurchReading objectHeadReduction Θ D)
    (den : ∀ ρ, Fits objectChurchReading Θ ρ → ∀ s, (cinterp objectChurchReading c ρ).Mem s →
      TyTok Elem.univ s → (cinterp objectChurchReading D ρ).Mem s) :
    Adequate objectChurchReading objectHeadReduction Θ c (.const propN) := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsT
  rw [cinterp_propT] at hsT
  have hsU := Ideal.typedAt_codes_iff.1 hsT
  have red : ∀ {τ : CSub Tower.Head k m}, CSubstMor objectChurch Θ Δ τ →
      CRedTy objectHeadReduction Δ (.app (.const holdsN) (c.subst τ)) (D.subst τ) := fun mor =>
    ⟨.single (objectHeadReduction.root (step _)), _, .sort _,
      .rootAdmitted (step _) (admits mor) (holds_app_typed (tc.substitute mor))
        (tD.substitute mor)⟩
  exact RT.ofCodes (typeKind_of_tyTok_univ hsU) propRed
    (RT.expand_ty ConvRules.objectLevels (red hσ.1.1) (red (hσ.symm ConvRules.objectLevels formed).1.1)
      (hD ρ fits formed hσ s (den ρ fits s hs hsU) hsU))

end Codes

/-! ## The decoder -/

/-- **The decoder is adequate**, through its spine at a code variable: the decoded
variable is an adequate type, hence adequate at `U₀`. -/
theorem constAdequateAt_holds : ConstAdequateAt objectChurchReading objectHeadReduction holdsN :=
  ConstAdequateAt.of_spine (Θ := .snoc .nil (.const propN)) (T := cU0) ConvRules.objectLevels
    objectChurch_soundnessFacts
    (objectChurch_declared (c := holdsN) (T := programCodes.holdsType) (by decide) rfl)
    (holds_app_typed (.var 0))
    ((adequateType_holdsVar 0 rfl).adequate ConvRules.objectLevels objectChurch_soundnessFacts
      (.sort Tower.zero))

/-! ## Implication -/

/-- The context of implication's spine: two codes. -/
abbrev cImpTele : CCtx Tower.Head 2 := .snoc (.snoc .nil (.const propN)) (.const propN)

/-- The decoding of implication at two code variables: `holds p → holds q`. -/
abbrev cImpDecoding : CTm Tower.Head 2 :=
  .pi (.app (.const holdsN) (.var 1)) (.app (.const holdsN) (.var 1))

/-- **Decoding an implication is an annotated root step**:
`holds (imp p q) ⟶ holds p → holds q`. -/
theorem objectChurch_decodeImp {n : Nat} (p q : CTm Tower.Head n) :
    objectChurch.computation.step (.app (.const holdsN) (.app (.app (.const impN) p) q))
      (.pi (.app (.const holdsN) p) (.app (.const holdsN) (q.rename wk))) := by
  have s := objectChurch_step_of_decoder (Or.inl rfl) (CTm.consSub q (CTm.consSub p
    fun i => .var (Fin.elim0 i)))
  have eh : programCodes.decoders.holds = holdsN := rfl
  have ei : programCodes.decoders.imp = impN := rfl
  rw [eh, ei, elabLeft_firstOrder objectDecls (rfl : firstOrder
      (.app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0)) : Tower.Tm 2) = true),
    elabRight, elab_lamFree _ rfl] at s
  exact s

/-- **Decoding an implication is admitted where its two arguments are codes.** -/
theorem objectChurch_decodeImp_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {n : Nat}
    {Γ : CCtx Tower.Head n} {p q : CTm Tower.Head n} (tp : CTyped Q Γ p (.const propN))
    (tq : CTyped Q Γ q (.const propN))
    (same : Q.computation = objectChurch.computation := by rfl) :
    Q.Admits Γ (.app (.const holdsN) (.app (.app (.const impN) p) q))
      (.pi (.app (.const holdsN) p) (.app (.const holdsN) (q.rename wk))) := by
  have a := objectChurch_admits_of_decoder same (Or.inl rfl) (Γ := Γ)
    (CTm.consSub q (CTm.consSub p fun i => .var (Fin.elim0 i)))
    (CSubstMor.patternTypings imp_knowledge (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact tq
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        exact tp))
    (fun e member => by
      change e ∈ patternEquations objectDecls none impLeft at member
      rw [imp_equations] at member
      cases member)
  have eh : programCodes.decoders.holds = holdsN := rfl
  have ei : programCodes.decoders.imp = impN := rfl
  rw [eh, ei, elabLeft_firstOrder objectDecls (rfl : firstOrder
      (.app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0)) : Tower.Tm 2) = true),
    elabRight, elab_lamFree _ rfl] at a
  exact a

/-- The implication constant at its declared type, in every context. -/
theorem cimp_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectChurch Γ (.const impN)
      (.pi (.const propN) (.pi (.const propN) (.const propN))) :=
  const_typed (T := programCodes.impType) (by decide) rfl
    (cpiT (const_U0_typed (by decide)) (cpiT (const_U0_typed (by decide))
      (const_U0_typed (by decide)))) (.sort _)

/-- The spine of implication at the two codes of its context is typed at `prop`. -/
theorem cimpSpine_typed :
    CTyped objectChurch cImpTele (.app (.app (.const impN) (.var 1)) (.var 0)) (.const propN) :=
  CDerivable.appElim (A := .const propN) (B := .const propN)
    (CDerivable.appElim (A := .const propN) (B := .pi (.const propN) (.const propN)) cimp_typed
      (.var 1)) (.var 0)

/-- The decoding of implication is an adequate type over two codes. -/
theorem adequateType_impDecoding :
    AdequateType objectChurchReading objectHeadReduction cImpTele cImpDecoding :=
  AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts
    ⟨_, .sort _, .piForm (holds_app_typed (.var 1)) (.sort _) (holds_app_typed (.var 1)) (.sort _)
      (.sorts _ _)⟩
    (adequateType_holdsVar 1 rfl) (adequateType_holdsVar 1 rfl)

/-- The typed tokens of implication at two codes are tokens of its decoding: the
implication of two codes is the code of the dependent function type with a constant
family, projected onto the codes. -/
theorem impDecoding_den : ∀ ρ, Fits objectChurchReading cImpTele ρ → ∀ s,
    (cinterp objectChurchReading (.app (.app (.const impN) (.var 1)) (.var 0) : CTm Tower.Head 2)
      ρ).Mem s → TyTok Elem.univ s → (cinterp objectChurchReading cImpDecoding ρ).Mem s := by
  intro ρ _ s hs _
  change (Ideal.appSpine (objectChurchReading.const impN) [ρ 1, ρ 0]).Mem s at hs
  rw [objectChurchReading_imp, Ideal.appSpine_impConst] at hs
  have hs' := Ideal.projT_le _ _ s hs
  change (Ideal.cpi (Ideal.app (objectChurchReading.const holdsN) (ρ 1))
    fun _ => Ideal.app (objectChurchReading.const holdsN) (ρ 0)).Mem s
  rw [objectChurchReading_holds, Ideal.app_holdsConst_eq, Ideal.app_holdsConst_eq]
  exact hs'

/-- **Implication is adequate**, through its spine at two code variables: its decoding
`holds p → holds q` is an adequate type, and the implication's typed tokens are tokens of
the decoding's denotation. -/
theorem constAdequateAt_imp : ConstAdequateAt objectChurchReading objectHeadReduction impN :=
  ConstAdequateAt.of_spine (Θ := cImpTele) (T := .const propN) ConvRules.objectLevels
    objectChurch_soundnessFacts
    (objectChurch_declared (c := impN) (T := programCodes.impType) (by decide) rfl) cimpSpine_typed
    (Adequate.ofDecoding cimpSpine_typed
      (.sub (.piForm (holds_app_typed (.var 1)) (.sort _) (holds_app_typed (.var 1)) (.sort _)
        (.sorts _ _)) (.subUniv cumulative_max_zero))
      (fun σ => objectChurch_decodeImp (σ 1) (σ 0))
      (fun mor => objectChurch_decodeImp_admits (mor 1) (mor 0)) adequateType_impDecoding
      impDecoding_den)

/-! ## The equations -/

section Equations

variable (type : HOL.Ty SetProfile.SetBase)

/-- A simple type, annotated and renamed, is the simple type of the larger context. -/
theorem liftTm_typeAt_rename {n m : Nat} (ξ : Ren n m) :
    (liftTm (typeAt SetProfile.types n type)).rename ξ =
      (liftTm (typeAt SetProfile.types m type) : CTm Tower.Head m) := by
  rw [← liftTm_rename, FormationSensitiveHOLInterface.typeAt_rename]

/-- The context of the equation's spine: two elements of the simple type. -/
abbrev cEqTele : CCtx Tower.Head 2 :=
  .snoc (.snoc .nil (liftTm (typeAt SetProfile.types 0 type)))
    (liftTm (typeAt SetProfile.types 1 type))

theorem cEqTele_lookup (i : Fin 2) :
    (cEqTele type).lookup i = liftTm (typeAt SetProfile.types 2 type) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact liftTm_typeAt_rename type wk
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    change ((liftTm (typeAt SetProfile.types 0 type)).rename wk).rename wk = _
    rw [liftTm_typeAt_rename, liftTm_typeAt_rename]

/-- The equation's decoding at two variables: the identity type between them. -/
abbrev cEqDecoding : CTm Tower.Head 2 := .id (liftTm (typeAt SetProfile.types 2 type)) (.var 1) (.var 0)

/-- **Decoding an equation is an annotated root step**: `holds (eq@A x y) ⟶ Id A x y`. -/
theorem objectChurch_decodeEq {n : Nat} (x y : CTm Tower.Head n) :
    objectChurch.computation.step
      (.app (.const holdsN) (.app (.app (.const (SetProfile.eqName type)) x) y))
      (.id (liftTm (typeAt SetProfile.types n type)) x y) := by
  have carrier : programCodes.decoders.eqCarrier (SetProfile.eqName type) = some (typeTerm type) := by
    change (if true = true then (SetProfile.eqInstance? (SetProfile.eqName type)).map typeTerm
      else none) = some (typeTerm type)
    rw [if_pos rfl, SetProfile.eqInstance?_eqName]
    rfl
  have s := objectChurch_step_of_decoder
    (Or.inr (Or.inr ⟨SetProfile.eqName type, typeTerm type, carrier, rfl⟩))
    (CTm.consSub y (CTm.consSub x fun i => .var (Fin.elim0 i)))
  have lf : lamFree (Tm.id (Presentation.liftClosed (typeTerm type)) (.var 1) (.var 0) :
      Tower.Tm 2) = true := by
    simp only [lamFree, Presentation.liftClosed, typeTerm,
      FormationSensitiveHOLInterface.typeAt_rename, lamFree_typeAt, Bool.and_self]
  have eh : programCodes.decoders.holds = holdsN := rfl
  rw [eh, elabLeft_firstOrder objectDecls (rfl : firstOrder
      (.app (.const holdsN) (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0)) :
        Tower.Tm 2) = true), elabRight, elab_lamFree _ lf] at s
  have hA : (liftTm (Presentation.liftClosed (typeTerm type)) : CTm Tower.Head 2) =
      liftTm (typeAt SetProfile.types 2 type) := by
    unfold Presentation.liftClosed typeTerm
    rw [FormationSensitiveHOLInterface.typeAt_rename]
  have e : (liftTm (Tm.id (Presentation.liftClosed (typeTerm type)) (.var 1) (.var 0) :
      Tower.Tm 2)).subst (CTm.consSub y (CTm.consSub x fun i => .var (Fin.elim0 i))) =
      .id (liftTm (typeAt SetProfile.types n type)) x y := by
    show CTm.id ((liftTm (Presentation.liftClosed (typeTerm type))).subst _) x y = _
    rw [hA, subst_liftTm_typeAt]
  rw [e] at s
  exact s

/-- **Decoding an equation is admitted where its two sides are elements of the simple
type.** -/
theorem objectChurch_decodeEq_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {n : Nat}
    {Γ : CCtx Tower.Head n} {x y : CTm Tower.Head n}
    (tx : CTyped Q Γ x (liftTm (typeAt SetProfile.types n type)))
    (ty : CTyped Q Γ y (liftTm (typeAt SetProfile.types n type)))
    (same : Q.computation = objectChurch.computation := by rfl) :
    Q.Admits Γ (.app (.const holdsN) (.app (.app (.const (SetProfile.eqName type)) x) y))
      (.id (liftTm (typeAt SetProfile.types n type)) x y) := by
  have carrier : programCodes.decoders.eqCarrier (SetProfile.eqName type) = some (typeTerm type) := by
    change (if true = true then (SetProfile.eqInstance? (SetProfile.eqName type)).map typeTerm
      else none) = some (typeTerm type)
    rw [if_pos rfl, SetProfile.eqInstance?_eqName]
    rfl
  have a := objectChurch_admits_of_decoder same
    (Or.inr (Or.inr ⟨SetProfile.eqName type, typeTerm type, carrier, rfl⟩)) (Γ := Γ)
    (CTm.consSub y (CTm.consSub x fun i => .var (Fin.elim0 i)))
    (CSubstMor.patternTypings (eq_knowledge type) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [liftCtx_lookup, Ctx.lookup_snoc_zero, FormationSensitiveHOLInterface.typeAt_rename,
          subst_liftTm_typeAt]
        exact ty
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        rw [liftCtx_lookup]
        change CTyped Q Γ x ((liftTm (Presentation.rename wk (Presentation.rename wk
          (typeAt SetProfile.types 0 type)))).subst _)
        rw [FormationSensitiveHOLInterface.typeAt_rename,
          FormationSensitiveHOLInterface.typeAt_rename, subst_liftTm_typeAt]
        exact tx))
    (fun e member => by
      have noEquations : patternEquations objectDecls none (eqLeft type) = [] := rfl
      change e ∈ patternEquations objectDecls none (eqLeft type) at member
      rw [noEquations] at member
      cases member)
  have lf : lamFree (Tm.id (Presentation.liftClosed (typeTerm type)) (.var 1) (.var 0) :
      Tower.Tm 2) = true := by
    simp only [lamFree, Presentation.liftClosed, typeTerm,
      FormationSensitiveHOLInterface.typeAt_rename, lamFree_typeAt, Bool.and_self]
  have eh : programCodes.decoders.holds = holdsN := rfl
  rw [eh, elabLeft_firstOrder objectDecls (rfl : firstOrder
      (.app (.const holdsN) (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0)) :
        Tower.Tm 2) = true), elabRight, elab_lamFree _ lf] at a
  have hA : (liftTm (Presentation.liftClosed (typeTerm type)) : CTm Tower.Head 2) =
      liftTm (typeAt SetProfile.types 2 type) := by
    unfold Presentation.liftClosed typeTerm
    rw [FormationSensitiveHOLInterface.typeAt_rename]
  have e : (liftTm (Tm.id (Presentation.liftClosed (typeTerm type)) (.var 1) (.var 0) :
      Tower.Tm 2)).subst (CTm.consSub y (CTm.consSub x fun i => .var (Fin.elim0 i))) =
      .id (liftTm (typeAt SetProfile.types n type)) x y := by
    show CTm.id ((liftTm (Presentation.liftClosed (typeTerm type))).subst _) x y = _
    rw [hA, subst_liftTm_typeAt]
  rw [e] at a
  exact a

/-- The equation constant at its declared type, in every context. -/
theorem ceq_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectChurch Γ (.const (SetProfile.eqName type))
      (.pi (liftTm (typeAt SetProfile.types n type))
        (.pi (liftTm (typeAt SetProfile.types (n + 1) type)) (.const propN))) := by
  rw [← liftClosed_liftTm_eqType]
  exact .const (objectDecls_eqName type) (typeAt_formed (.arr type (.arr type .prop)) .nil) (.sort _)

/-- The spine of the equation at the two variables of its context is typed at `prop`. -/
theorem ceqSpine_typed :
    CTyped objectChurch (cEqTele type)
      (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0)) (.const propN) := by
  have t1 : CTyped objectChurch (cEqTele type) (.var 1) (liftTm (typeAt SetProfile.types 2 type)) := by
    rw [← cEqTele_lookup type 1]
    exact .var 1
  have t0 : CTyped objectChurch (cEqTele type) (.var 0) (liftTm (typeAt SetProfile.types 2 type)) := by
    rw [← cEqTele_lookup type 0]
    exact .var 0
  have a1 := CDerivable.appElim (ceq_typed type (Γ := cEqTele type)) t1
  have e1 : CTm.inst0 (.var 1) (.pi (liftTm (typeAt SetProfile.types 3 type)) (.const propN) :
      CTm Tower.Head 3) = .pi (liftTm (typeAt SetProfile.types 2 type)) (.const propN) := by
    show CTm.pi ((liftTm (typeAt SetProfile.types 3 type)).subst _) _ = _
    rw [subst_liftTm_typeAt]
    rfl
  rw [e1] at a1
  exact CDerivable.appElim a1 t0

/-- The decoding of the equation is an adequate type over two elements of the simple type:
an identity type of an adequate carrier between adequate variables. -/
theorem adequateType_eqDecoding :
    AdequateType objectChurchReading objectHeadReduction (cEqTele type) (cEqDecoding type) := by
  have t1 : CTyped objectChurch (cEqTele type) (.var 1) (liftTm (typeAt SetProfile.types 2 type)) := by
    rw [← cEqTele_lookup type 1]
    exact .var 1
  have t0 : CTyped objectChurch (cEqTele type) (.var 0) (liftTm (typeAt SetProfile.types 2 type)) := by
    rw [← cEqTele_lookup type 0]
    exact .var 0
  have v1 : Adequate objectChurchReading objectHeadReduction (cEqTele type) (.var 1)
      (liftTm (typeAt SetProfile.types 2 type)) := by
    rw [← cEqTele_lookup type 1]
    exact (CStatement.Valid.var 1).1
  have v0 : Adequate objectChurchReading objectHeadReduction (cEqTele type) (.var 0)
      (liftTm (typeAt SetProfile.types 2 type)) := by
    rw [← cEqTele_lookup type 0]
    exact (CStatement.Valid.var 0).1
  exact AdequateType.ident ConvRules.objectLevels (.sort _) (typeAt_formed type _) t1 t0
    (adequateType_typeAt type _) v1 v0

/-- The typed tokens of the equation at two elements are tokens of its decoding, the
identity type between them. -/
theorem eqDecoding_den : ∀ ρ, Fits objectChurchReading (cEqTele type) ρ → ∀ s,
    (cinterp objectChurchReading
      (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0) : CTm Tower.Head 2) ρ).Mem s →
    TyTok Elem.univ s → (cinterp objectChurchReading (cEqDecoding type) ρ).Mem s := by
  intro ρ fits s hs _
  change (Ideal.appSpine (objectChurchReading.const (SetProfile.eqName type)) [ρ 1, ρ 0]).Mem s at hs
  rw [objectChurchReading_eq, Ideal.appSpine_eqConst] at hs
  have hs' := Ideal.projT_le _ _ s hs
  have f1 : projT (simpleI type) (ρ 1) = ρ 1 := by
    have h := (fits.1.2.2 : projT _ (ρ 1) = ρ 1)
    rwa [cinterp_objectTypeAt] at h
  have f0 : projT (simpleI type) (ρ 0) = ρ 0 := by
    have h := (fits.2.2 : projT _ (ρ 0) = ρ 0)
    rwa [cinterp_objectTypeAt] at h
  rw [f1, f0] at hs'
  change (Ideal.ident (cinterp objectChurchReading (liftTm (typeAt SetProfile.types 2 type)) ρ)
    (ρ 1) (ρ 0)).Mem s
  rw [cinterp_objectTypeAt]
  exact hs'

/-- **The equation's spine is adequate at `prop`**, through its decoding. -/
theorem adequate_eqSpine : Adequate objectChurchReading objectHeadReduction (cEqTele type)
    (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0)) (.const propN) := by
  have t1 : CTyped objectChurch (cEqTele type) (.var 1) (liftTm (typeAt SetProfile.types 2 type)) := by
    rw [← cEqTele_lookup type 1]
    exact .var 1
  have t0 : CTyped objectChurch (cEqTele type) (.var 0) (liftTm (typeAt SetProfile.types 2 type)) := by
    rw [← cEqTele_lookup type 0]
    exact .var 0
  exact Adequate.ofDecoding (ceqSpine_typed type) (.idForm (typeAt_formed type _) (.sort _) t1 t0)
    (fun σ => by
      have h := objectChurch_decodeEq type (σ 1) (σ 0)
      rwa [← subst_liftTm_typeAt σ type] at h)
    (fun {m Δ σ} mor => by
      have s1 : CTyped objectChurch Δ (σ 1) (liftTm (typeAt SetProfile.types m type)) := by
        have h := mor 1
        rwa [cEqTele_lookup, subst_liftTm_typeAt] at h
      have s0 : CTyped objectChurch Δ (σ 0) (liftTm (typeAt SetProfile.types m type)) := by
        have h := mor 0
        rwa [cEqTele_lookup, subst_liftTm_typeAt] at h
      have h := objectChurch_decodeEq_admits type s1 s0
      rwa [← subst_liftTm_typeAt σ type] at h)
    (adequateType_eqDecoding type) (eqDecoding_den type)

/-- The equation at a simple type is declared at `A → A → prop`. -/
theorem eq_declared : objectChurch.constantType (SetProfile.eqName type) =
    some (pisCtx (cEqTele type) (.const propN)) :=
  (objectChurch_constantType _).trans (objectDecls_eqName type)

/-- **The equation at a simple type is adequate**, through its spine at two variables: its
decoding, the identity type between them, is an adequate type, and the equation's typed
tokens are tokens of that identity type. -/
theorem constAdequateAt_eq :
    ConstAdequateAt objectChurchReading objectHeadReduction (SetProfile.eqName type) :=
  ConstAdequateAt.of_spine (Θ := cEqTele type) (T := .const propN) ConvRules.objectLevels
    objectChurch_soundnessFacts (eq_declared type) (ceqSpine_typed type) (adequate_eqSpine type)

end Equations

/-! ## Typings within allowed constants -/

section Within

variable {A : DeclName → Bool} {n : Nat} {Γ : CCtx Tower.Head n}

theorem csigmaT_within {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr Nat}
    (domain : CTyped (objectChurch.restrict A) Γ D (CU l))
    (codomain : CTyped (objectChurch.restrict A) (.snoc Γ D) B (CU l)) :
    CTyped (objectChurch.restrict A) Γ (.sigma D B) (CU l) :=
  CDerivable.cumul (.sigmaForm domain (.sort l) codomain (.sort l) (.sorts l l))
    (fun valuation => by simp [LevelExpr.eval])

/-- The step type `Π x : A. P x → Σ y : A. P y` over the context `A, P`, with no constant. -/
theorem cstepFamily_formed_within {Δ : CCtx Tower.Head n} :
    CTyped (objectChurch.restrict A) (.snoc (.snoc Δ cU0) (.pi (.var 0) cU0))
      (.pi (.var 1) (.pi (.app (.var 1) (.var 0))
        (.sigma (.var 3) (.app (.var 3) (.var 0))))) cU0 :=
  cpiT_within (.var 1) (cpiT_within (.appElim (B := cU0) (.var 1) (.var 0))
    (csigmaT_within (.var 3) (.appElim (B := cU0) (.var 3) (.var 0))))

/-- The declared type of the iterator, formed within the numbers. -/
theorem citerType_formed_within (hn : A numN = true) :
    CTyped (objectChurch.restrict A) .nil (liftTm Package.iterType) cU1 := by
  show CTyped (objectChurch.restrict A) .nil
    (.pi cnum (.pi cU0 (.pi (.pi (.var 0) cU0)
      (.pi (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.sigma (.var 3) (.app (.var 3) (.var 0)))))
        (.pi (.var 2) (.pi (.app (.var 2) (.var 0))
          (.sigma (.var 4) (.app (.var 4) (.var 0))))))))) cU1
  exact cpiT_within (craise_within (cnum_typed_within hn)) (cpiT_within cU0_typed_within
    (cpiT_within (cpiT_within (craise_within (.var 0)) cU0_typed_within)
      (cpiT_within (craise_within cstepFamily_formed_within)
        (cpiT_within (craise_within (.var 2))
          (cpiT_within (craise_within (.appElim (B := cU0) (.var 2) (.var 0)))
            (craise_within (csigmaT_within (.var 4) (.appElim (B := cU0) (.var 4) (.var 0)))))))))

theorem citer_typed_within (hn : A numN = true) (hi : A Package.iterName = true) :
    CTyped (objectChurch.restrict A) Γ (.const Package.iterName)
      (liftTm Package.iterType).liftClosed :=
  cconst_within Package.iterType hi (by decide) (by decide) (citerType_formed_within hn)

/-- The declared type of `transportCert`, formed with no constant. -/
theorem ctransportType_formed_within :
    CTyped (objectChurch.restrict A) .nil (liftTm Package.transportType) cU1 := by
  show CTyped (objectChurch.restrict A) .nil
    (.pi cU0 (.pi (.pi (.var 0) cU0)
      (.pi (.pi (.var 1) (.var 2))
        (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 2) (.var 1)))))
          (.pi (.var 3) (.pi (.app (.var 3) (.var 0))
            (.sigma (.var 5) (.app (.var 5) (.var 0))))))))) cU1
  exact cpiT_within cU0_typed_within (cpiT_within (cpiT_within (craise_within (.var 0))
    cU0_typed_within)
    (cpiT_within (craise_within (cpiT_within (.var 1) (.var 2)))
      (cpiT_within
        (craise_within (cpiT_within (.var 2)
          (cpiT_within (.appElim (B := cU0) (.var 2) (.var 0))
            (.appElim (B := cU0) (.var 3) (.appElim (B := .var 5) (.var 2) (.var 1))))))
        (cpiT_within (craise_within (.var 3))
          (cpiT_within (craise_within (.appElim (B := cU0) (.var 3) (.var 0)))
            (craise_within (csigmaT_within (.var 5) (.appElim (B := cU0) (.var 5) (.var 0)))))))))

theorem ctransport_typed_within (ht : A transportName = true) :
    CTyped (objectChurch.restrict A) Γ (.const transportName)
      (liftTm Package.transportType).liftClosed :=
  cconst_within Package.transportType ht (by decide) (by decide) ctransportType_formed_within

theorem ceqAtConst_typed_within (he : A Package.eqAtName = true) (hn : A numN = true) :
    CTyped (objectChurch.restrict A) Γ (.const Package.eqAtName) (.pi cnum cU0) :=
  cconst_within Package.eqAtType (l := .succ Tower.zero) he (by decide) (by decide)
    (cpiT_within (craise_within (cnum_typed_within hn)) cU0_typed_within)

theorem csucConst_typed_within (hs : A sucN = true) (hn : A numN = true) :
    CTyped (objectChurch.restrict A) Γ (.const sucN) (.pi cnum cnum) :=
  cconst_within (c := sucN) (.pi Package.numT Package.numT) (l := Tower.zero) hs (by decide)
    (by decide) (cpiT_within (cnum_typed_within hn) (cnum_typed_within hn))

theorem csucMove_typed_within (hm : A Package.sucMoveName = true) (he : A Package.eqAtName = true)
    (hs : A sucN = true) (hn : A numN = true) :
    CTyped (objectChurch.restrict A) Γ (.const Package.sucMoveName)
      (liftTm Package.sucMoveType).liftClosed :=
  cconst_within Package.sucMoveType (l := Tower.zero) hm (by decide) (by decide)
    (cpiT_within (cnum_typed_within hn) (cpiT_within (ceqAt_typed_within he hn (.var 0))
      (ceqAt_typed_within he hn (csuc_typed_within hs hn (.var 1)))))

end Within

/-! ## `transportCert` -/

section Transport

/-- The codomain of `transportCert`: `Σ (y : A). P y`. -/
abbrev cTransportCod : CTm Tower.Head 6 := .sigma (.var 5) (.app (.var 5) (.var 0))

/-- The right side of `transportCert`: `(f x, move x e)`. -/
abbrev cTransportRhs : CTm Tower.Head 6 :=
  .pair (.app (.var 3) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0))

/-- The right side of `transportCert` is typed with no constant. -/
theorem ctransportRhs_typed_within {A : DeclName → Bool} :
    CTyped (objectChurch.restrict A) cTransportTele cTransportRhs cTransportCod := by
  have value := CDerivable.appElim (B := .var 6)
    (CDerivable.var (P := objectChurch.restrict A) (Γ := cTransportTele) 3) (.var 1)
  have moved := CDerivable.appElim
    (CDerivable.appElim (CDerivable.var (P := objectChurch.restrict A) (Γ := cTransportTele) 2)
      (.var 1)) (.var 0)
  exact .pairIntro (csigmaT_within (.var 5) (.appElim (B := cU0) (.var 5) (.var 0)))
    (.sort Tower.zero) value moved

/-- The telescope of `transportCert` is formed. -/
theorem cTransportTele_formed : CCtxFormed objectChurch cTransportTele :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, .sort _, cU0_typed⟩)
    ⟨_, .sort _, cpiT (craise (.var 0)) cU0_typed⟩)
    ⟨_, .sort _, cpiT (.var 1) (.var 2)⟩)
    ⟨_, .sort _, cpiT (.var 2) (cpiT (.appElim (B := cU0) (.var 2) (.var 0))
      (.appElim (B := cU0) (.var 3) (.appElim (B := .var 5) (.var 2) (.var 1))))⟩)
    ⟨_, .sort _, .var 3⟩)
    ⟨_, .sort _, .appElim (B := cU0) (.var 3) (.var 0)⟩

theorem transport_declared :
    objectChurch.constantType transportName = some (pisCtx cTransportTele cTransportCod) :=
  objectChurch_declared (T := Package.transportType) (by decide) (by decide)

/-- `transportCert` denotes the abstraction of its right side, projected onto its declared
type. -/
theorem objectChurchReading_transport :
    objectChurchReading.const transportName =
      defConst objectChurchReading cTransportTele cTransportCod cTransportRhs := by
  have h := objectChurchReading_def (f := transportName) (tag := .transport) (by decide)
    (Θ := transportTelescope) (rhs := transportRhs) (T := cTransportCod) (by decide) rfl
  have e : defRhs transportName transportTelescope transportRhs = cTransportRhs := by
    decide
  rw [h, e]
  rfl

/-- The spine of `transportCert` at the variables of its telescope is typed at its
codomain. -/
theorem ctransportSpine_typed :
    CTyped objectChurch cTransportTele
      (CTm.appSpine (.const transportName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0])
      cTransportCod := by
  have t₁ := CDerivable.appElim (ctransport_typed (Γ := cTransportTele)) (CDerivable.var 5)
  have t₂ := CDerivable.appElim t₁ (CDerivable.var 4)
  have t₃ := CDerivable.appElim t₂ (CDerivable.var 3)
  have t₄ := CDerivable.appElim t₃ (CDerivable.var 2)
  have t₅ := CDerivable.appElim t₄ (CDerivable.var 1)
  exact CDerivable.appElim t₅ (CDerivable.var 0)

/-- **The applications of `transportCert` reduce to its right side**, by its root step. -/
theorem transport_teleReduces {m : Nat} {Δ : CCtx Tower.Head m} :
    TeleReduces objectHeadReduction Δ (CCtx.toTele cTransportTele) cTransportCod cTransportRhs
      (.const transportName) fun i => .var (Fin.elim0 i) := by
  intro A tA P tP f tf mv tmv x tx e te
  have mor : CSubstMor objectChurch cTransportTele Δ (CTm.consSub e (CTm.consSub x
      (CTm.consSub mv (CTm.consSub f (CTm.consSub P (CTm.consSub A
        fun i => .var (Fin.elim0 i))))))) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact te
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tx
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tmv
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tf
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tP
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tA
    exact i.elim0
  have eL : elabLeft objectDecls
      (applyClosed transportTelescope Presentation.ids (.const transportName)) =
      (CTm.appSpine (.const transportName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0] :
        CTm Tower.Head 6) := by
    decide
  have eR : elabRight objectDecls
      (applyClosed transportTelescope Presentation.ids (.const transportName)) transportRhs =
      cTransportRhs := by
    decide
  have step : objectChurch.computation.step
      ((CTm.appSpine (.const transportName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0] :
        CTm Tower.Head 6).subst (CTm.consSub e (CTm.consSub x (CTm.consSub mv (CTm.consSub f
          (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i))))))))
      (cTransportRhs.subst (CTm.consSub e (CTm.consSub x (CTm.consSub mv (CTm.consSub f
        (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i)))))))) := by
    have s := objectChurch_step_of_spec
      (List.getElem_mem (l := computationSpecs) (n := 7) (by decide))
      (L := applyClosed transportTelescope Presentation.ids (.const transportName))
      (R := transportRhs) rfl
      (CTm.consSub e (CTm.consSub x (CTm.consSub mv (CTm.consSub f (CTm.consSub P
        (CTm.consSub A fun i => .var (Fin.elim0 i)))))))
    rw [eL, eR] at s
    exact s
  have admits : objectChurch.Admits Δ
      ((CTm.appSpine (.const transportName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0] :
        CTm Tower.Head 6).subst (CTm.consSub e (CTm.consSub x (CTm.consSub mv (CTm.consSub f
          (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i))))))))
      (cTransportRhs.subst (CTm.consSub e (CTm.consSub x (CTm.consSub mv (CTm.consSub f
        (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i)))))))) := by
    have a := objectChurch_admits_of_mor rfl
      (List.getElem_mem (l := computationSpecs) (n := 7) (by decide))
      (L := applyClosed transportTelescope Presentation.ids (.const transportName))
      (R := transportRhs) rfl
      (CTm.consSub e (CTm.consSub x (CTm.consSub mv (CTm.consSub f (CTm.consSub P
        (CTm.consSub A fun i => .var (Fin.elim0 i))))))) (by decide) (by decide) mor
    rw [eL, eR] at a
    exact a
  exact ⟨.single (objectHeadReduction.root step), .rootAdmitted step admits (ctransportSpine_typed.substitute mor)
    (CTyped.substitute (CDerivable.mono ChurchRules.restrict_sub
      (ctransportRhs_typed_within (A := fun _ => false))) mor)⟩

/-- **`transportCert` is adequate**: its right side is typed with no constant, hence
adequate by the fundamental lemma, and its applications reduce to it. -/
theorem constAdequateAt_transport :
    ConstAdequateAt objectChurchReading objectHeadReduction transportName :=
  ConstAdequateAt.ofDefinition ConvRules.objectLevels objectChurch_soundnessFacts transport_declared
    objectChurchReading_transport
    (objectChurch_valid (allowed := fun _ => false) (fun h => absurd h Bool.false_ne_true)
      ctransportRhs_typed_within cTransportTele_formed).1
    fun _ => transport_teleReduces

end Transport

/-! ## `composeCert` -/

section Compose

/-- The codomain of `composeCert`: `Σ (y : A). P y`. -/
abbrev cComposeCod : CTm Tower.Head 6 := .sigma (.var 5) (.app (.var 5) (.var 0))

/-- The right side of `composeCert`, as elaborated: the second step at the components of
the first step's pack. -/
abbrev cComposeRhs : CTm Tower.Head 6 :=
  .app (.lam (.sigma (.var 5) (.app (.var 5) (.var 0)))
      (.app (.app (.var 3) (.fst (.var 0))) (.snd (.var 0))))
    (.app (.app (.var 3) (.var 1)) (.var 0))

/-- The right side of `composeCert` is typed with no constant. -/
theorem ccomposeRhs_typed_within {A : DeclName → Bool} :
    CTyped (objectChurch.restrict A) cComposeTele cComposeRhs cComposeCod := by
  have sigmaTyped : CTyped (objectChurch.restrict A) cComposeTele
      (.sigma (.var 5) (.app (.var 5) (.var 0))) cU0 :=
    csigmaT_within (.var 5) (.appElim (B := cU0) (.var 5) (.var 0))
  have package := CDerivable.appElim
    (CDerivable.appElim (CDerivable.var (P := objectChurch.restrict A) (Γ := cComposeTele) 3)
      (.var 1)) (.var 0)
  have pkg : CTyped (objectChurch.restrict A)
      (.snoc cComposeTele (.sigma (.var 5) (.app (.var 5) (.var 0))))
      (.var 0) (.sigma (.var 6) (.app (.var 6) (.var 0))) := .var 0
  have b1 := CDerivable.appElim
    (CDerivable.var (P := objectChurch.restrict A)
      (Γ := .snoc cComposeTele (.sigma (.var 5) (.app (.var 5) (.var 0)))) 3)
    (CDerivable.fstElim pkg)
  have b2 := CDerivable.appElim b1 (CDerivable.sndElim pkg)
  have arrow : CTyped (objectChurch.restrict A) cComposeTele
      (.pi (.sigma (.var 5) (.app (.var 5) (.var 0))) (.sigma (.var 6) (.app (.var 6) (.var 0))))
      cU0 :=
    cpiT_within sigmaTyped (CTyped.weaken sigmaTyped)
  have closure := CDerivable.lamIntro sigmaTyped (.sort _) arrow (.sort _) b2
  exact CDerivable.appElim closure package

/-- The declared type of `composeCert`, formed with no constant. -/
theorem ccomposeType_formed_within {A : DeclName → Bool} :
    CTyped (objectChurch.restrict A) .nil (liftTm Package.composeType) cU1 := by
  show CTyped (objectChurch.restrict A) .nil
    (.pi cU0 (.pi (.pi (.var 0) cU0)
      (.pi (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.sigma (.var 3) (.app (.var 3) (.var 0)))))
        (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0)))))
          (.pi (.var 3) (.pi (.app (.var 3) (.var 0))
            (.sigma (.var 5) (.app (.var 5) (.var 0))))))))) cU1
  exact cpiT_within cU0_typed_within (cpiT_within (cpiT_within (craise_within (.var 0))
    cU0_typed_within)
    (cpiT_within (craise_within cstepFamily_formed_within)
      (cpiT_within (craise_within (CTyped.weaken cstepFamily_formed_within))
        (cpiT_within (craise_within (.var 3))
          (cpiT_within (craise_within (.appElim (B := cU0) (.var 3) (.var 0)))
            (craise_within (csigmaT_within (.var 5) (.appElim (B := cU0) (.var 5) (.var 0)))))))))

/-- `composeCert` at its declared type, in every context. -/
theorem ccompose_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectChurch Γ (.const composeName) (liftTm Package.composeType).liftClosed :=
  CDerivable.mono ChurchRules.restrict_sub
    (cconst_within (A := fun _ => true) Package.composeType rfl (by decide) (by decide)
      ccomposeType_formed_within)

/-- The telescope of `composeCert` is formed. -/
theorem cComposeTele_formed : CCtxFormed objectChurch cComposeTele :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, .sort _, cU0_typed⟩)
    ⟨_, .sort _, cpiT (craise (.var 0)) cU0_typed⟩)
    ⟨_, .sort _, cstepFamily_formed (Δ := .nil)⟩)
    ⟨_, .sort _, CTyped.weaken (cstepFamily_formed (Δ := .nil))⟩)
    ⟨_, .sort _, .var 3⟩)
    ⟨_, .sort _, .appElim (B := cU0) (.var 3) (.var 0)⟩

theorem compose_declared :
    objectChurch.constantType composeName = some (pisCtx cComposeTele cComposeCod) :=
  objectChurch_declared (T := Package.composeType) (by decide) (by decide)

/-- `composeCert` denotes the abstraction of its right side, projected onto its declared
type. -/
theorem objectChurchReading_compose :
    objectChurchReading.const composeName =
      defConst objectChurchReading cComposeTele cComposeCod cComposeRhs := by
  have h := objectChurchReading_def (f := composeName) (tag := .compose) (by decide)
    (Θ := composeTelescope) (rhs := composeRhs) (T := cComposeCod) (by decide) rfl
  have e : defRhs composeName composeTelescope composeRhs = cComposeRhs := by
    decide
  rw [h, e]
  rfl

/-- The spine of `composeCert` at the variables of its telescope is typed at its
codomain. -/
theorem ccomposeSpine_typed :
    CTyped objectChurch cComposeTele
      (CTm.appSpine (.const composeName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0])
      cComposeCod := by
  have t₁ := CDerivable.appElim (ccompose_typed (Γ := cComposeTele)) (CDerivable.var 5)
  have t₂ := CDerivable.appElim t₁ (CDerivable.var 4)
  have t₃ := CDerivable.appElim t₂ (CDerivable.var 3)
  have t₄ := CDerivable.appElim t₃ (CDerivable.var 2)
  have t₅ := CDerivable.appElim t₄ (CDerivable.var 1)
  exact CDerivable.appElim t₅ (CDerivable.var 0)

/-- **The applications of `composeCert` reduce to its right side**, by its root step. -/
theorem compose_teleReduces {m : Nat} {Δ : CCtx Tower.Head m} :
    TeleReduces objectHeadReduction Δ (CCtx.toTele cComposeTele) cComposeCod cComposeRhs
      (.const composeName) fun i => .var (Fin.elim0 i) := by
  intro A tA P tP f tf g tg x tx e te
  have mor : CSubstMor objectChurch cComposeTele Δ (CTm.consSub e (CTm.consSub x
      (CTm.consSub g (CTm.consSub f (CTm.consSub P (CTm.consSub A
        fun i => .var (Fin.elim0 i))))))) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact te
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tx
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tg
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tf
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tP
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tA
    exact i.elim0
  have eL : elabLeft objectDecls
      (applyClosed composeTelescope Presentation.ids (.const composeName)) =
      (CTm.appSpine (.const composeName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0] :
        CTm Tower.Head 6) := by
    decide
  have eR : elabRight objectDecls
      (applyClosed composeTelescope Presentation.ids (.const composeName)) composeRhs =
      cComposeRhs := by
    decide
  have step : objectChurch.computation.step
      ((CTm.appSpine (.const composeName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0] :
        CTm Tower.Head 6).subst (CTm.consSub e (CTm.consSub x (CTm.consSub g (CTm.consSub f
          (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i))))))))
      (cComposeRhs.subst (CTm.consSub e (CTm.consSub x (CTm.consSub g (CTm.consSub f
        (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i)))))))) := by
    have s := objectChurch_step_of_spec
      (List.getElem_mem (l := computationSpecs) (n := 8) (by decide))
      (L := applyClosed composeTelescope Presentation.ids (.const composeName))
      (R := composeRhs) rfl
      (CTm.consSub e (CTm.consSub x (CTm.consSub g (CTm.consSub f (CTm.consSub P
        (CTm.consSub A fun i => .var (Fin.elim0 i)))))))
    rw [eL, eR] at s
    exact s
  have admits : objectChurch.Admits Δ
      ((CTm.appSpine (.const composeName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0] :
        CTm Tower.Head 6).subst (CTm.consSub e (CTm.consSub x (CTm.consSub g (CTm.consSub f
          (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i))))))))
      (cComposeRhs.subst (CTm.consSub e (CTm.consSub x (CTm.consSub g (CTm.consSub f
        (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i)))))))) := by
    have a := objectChurch_admits_of_mor rfl
      (List.getElem_mem (l := computationSpecs) (n := 8) (by decide))
      (L := applyClosed composeTelescope Presentation.ids (.const composeName))
      (R := composeRhs) rfl
      (CTm.consSub e (CTm.consSub x (CTm.consSub g (CTm.consSub f (CTm.consSub P
        (CTm.consSub A fun i => .var (Fin.elim0 i))))))) (by decide) (by decide) mor
    rw [eL, eR] at a
    exact a
  exact ⟨.single (objectHeadReduction.root step), .rootAdmitted step admits (ccomposeSpine_typed.substitute mor)
    (CTyped.substitute (CDerivable.mono ChurchRules.restrict_sub
      (ccomposeRhs_typed_within (A := fun _ => false))) mor)⟩

/-- **`composeCert` is adequate**: its right side is typed with no constant, hence
adequate by the fundamental lemma, and its applications reduce to it. -/
theorem constAdequateAt_compose :
    ConstAdequateAt objectChurchReading objectHeadReduction composeName :=
  ConstAdequateAt.ofDefinition ConvRules.objectLevels objectChurch_soundnessFacts compose_declared
    objectChurchReading_compose
    (objectChurch_valid (allowed := fun _ => false) (fun h => absurd h Bool.false_ne_true)
      ccomposeRhs_typed_within cComposeTele_formed).1
    fun _ => compose_teleReduces

end Compose

/-! ## `returnIter` -/

section ReturnIter

open Package (returnIterName iterName)

/-- The codomain of `returnIter` after its carrier. -/
abbrev cReturnIterCod : CTm Tower.Head 1 := liftTm Package.returnIterResult

/-- The right side of `returnIter`, as elaborated: five abstractions over the iterator's
spine with its count moved first. -/
abbrev cReturnIterRhs : CTm Tower.Head 1 :=
  .lam (.pi (.var 0) cU0) (.lam cnum
    (.lam (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0)))))
      (.lam (.var 3) (.lam (.app (.var 3) (.var 0))
        (.app (.app (.app (.app (.app (.app (.const iterName) (.var 3)) (.var 5)) (.var 4))
          (.var 2)) (.var 1)) (.var 0))))))

variable {A : DeclName → Bool}

/-- The codomain of `returnIter` is formed within the numbers. -/
theorem creturnIterCod_formed_within (hn : A numN = true) :
    CTyped (objectChurch.restrict A) (.snoc .nil cU0) cReturnIterCod cU1 := by
  have tStep : CTyped (objectChurch.restrict A) (.snoc (.snoc (.snoc .nil cU0) (.pi (.var 0) cU0)) cnum)
      (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0))))) cU0 :=
    CTyped.weaken (cstepFamily_formed_within (Δ := .nil))
  have fe : CTyped (objectChurch.restrict A)
      (.snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.pi (.var 0) cU0)) cnum)
        (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0))))))
        (.var 3))
      (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0)))) cU0 :=
    cpiT_within (.appElim (B := cU0) (.var 3) (.var 0))
      (csigmaT_within (.var 5) (.appElim (B := cU0) (.var 5) (.var 0)))
  have fx := cpiT_within (.var 3) fe
  have fs := cpiT_within tStep fx
  have fn := cpiT_within (cnum_typed_within hn) fs
  have tMotive : CTyped (objectChurch.restrict A) (.snoc .nil cU0) (.pi (.var 0) cU0) cU1 :=
    cpiT_within (craise_within (.var 0)) cU0_typed_within
  exact cpiT_within tMotive (craise_within fn)

/-- The right side of `returnIter` is typed within the numbers and the iterator. -/
theorem creturnIterRhs_typed_within (hn : A numN = true) (hi : A iterName = true) :
    CTyped (objectChurch.restrict A) (.snoc .nil cU0) cReturnIterRhs cReturnIterCod := by
  let c1 : CCtx Tower.Head 1 := .snoc .nil cU0
  let c2 : CCtx Tower.Head 2 := .snoc c1 (.pi (.var 0) cU0)
  let c3 : CCtx Tower.Head 3 := .snoc c2 cnum
  let c4 : CCtx Tower.Head 4 :=
    .snoc c3 (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0)))))
  let c5 : CCtx Tower.Head 5 := .snoc c4 (.var 3)
  let c6 : CCtx Tower.Head 6 := .snoc c5 (.app (.var 3) (.var 0))
  show CTyped (objectChurch.restrict A) c1 _ _
  have i1 := CDerivable.appElim (citer_typed_within hn hi (Γ := c6)) (CDerivable.var 3)
  have i2 := CDerivable.appElim i1 (CDerivable.var 5)
  have i3 := CDerivable.appElim i2 (CDerivable.var 4)
  have i4 := CDerivable.appElim i3 (CDerivable.var 2)
  have i5 := CDerivable.appElim i4 (CDerivable.var 1)
  have body := CDerivable.appElim i5 (CDerivable.var 0)
  have tStep : CTyped (objectChurch.restrict A) c3
      (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0))))) cU0 :=
    CTyped.weaken (cstepFamily_formed_within (Δ := .nil))
  have fe : CTyped (objectChurch.restrict A) c5
      (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0)))) cU0 :=
    cpiT_within (.appElim (B := cU0) (.var 3) (.var 0))
      (csigmaT_within (.var 5) (.appElim (B := cU0) (.var 5) (.var 0)))
  have fx : CTyped (objectChurch.restrict A) c4
      (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0))))) cU0 :=
    cpiT_within (.var 3) fe
  have fs : CTyped (objectChurch.restrict A) c3
      (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0)))))
        (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0))))))
      cU0 :=
    cpiT_within tStep fx
  have fn : CTyped (objectChurch.restrict A) c2
      (.pi cnum (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0))
          (.sigma (.var 4) (.app (.var 4) (.var 0)))))
        (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0)))))))
      cU0 :=
    cpiT_within (cnum_typed_within hn) fs
  have tMotive : CTyped (objectChurch.restrict A) c1 (.pi (.var 0) cU0) cU1 :=
    cpiT_within (craise_within (.var 0)) cU0_typed_within
  have fp := cpiT_within tMotive (craise_within fn)
  exact .lamIntro tMotive (.sort _) fp (.sort _)
    (.lamIntro (cnum_typed_within hn) (.sort _) fn (.sort _)
      (.lamIntro tStep (.sort _) fs (.sort _)
        (.lamIntro (.var 3) (.sort _) fx (.sort _)
          (.lamIntro (.appElim (B := cU0) (.var 3) (.var 0)) (.sort _) fe (.sort _) body))))

/-- `returnIter` at its declared type, in every context. -/
theorem creturnIter_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectChurch Γ (.const returnIterName) (liftTm Package.returnIterType).liftClosed :=
  CDerivable.mono ChurchRules.restrict_sub
    (cconst_within (A := fun _ => true) Package.returnIterType rfl (by decide) (by decide)
      (cpiT_within cU0_typed_within (creturnIterCod_formed_within rfl)))

theorem returnIter_declared :
    objectChurch.constantType returnIterName = some (pisCtx (.snoc .nil cU0) cReturnIterCod) :=
  objectChurch_declared (T := Package.returnIterType) (by decide) (by decide)

/-- `returnIter` denotes the abstraction of its right side, projected onto its declared
type. -/
theorem objectChurchReading_returnIter :
    objectChurchReading.const returnIterName =
      defConst objectChurchReading (.snoc .nil cU0) cReturnIterCod cReturnIterRhs := by
  have h := objectChurchReading_def (f := returnIterName) (tag := .returnIter) (by decide)
    (Θ := returnIterTele) (rhs := returnIterRhs) (T := cReturnIterCod) (by decide) rfl
  have e : defRhs returnIterName returnIterTele returnIterRhs = cReturnIterRhs := by
    decide
  rw [h, e]
  rfl

/-- **The applications of `returnIter` reduce to its right side**, by its root step. -/
theorem returnIter_teleReduces {m : Nat} {Δ : CCtx Tower.Head m} :
    TeleReduces objectHeadReduction Δ (CCtx.toTele (.snoc .nil cU0)) cReturnIterCod cReturnIterRhs
      (.const returnIterName) fun i => .var (Fin.elim0 i) := by
  intro C tC
  have mor : CSubstMor objectChurch (.snoc .nil cU0) Δ
      (CTm.consSub C fun i => .var (Fin.elim0 i)) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tC
    exact i.elim0
  have eL : elabLeft objectDecls
      (applyClosed returnIterTele Presentation.ids (.const returnIterName)) =
      (.app (.const returnIterName) (.var 0) : CTm Tower.Head 1) := by
    decide
  have eR : elabRight objectDecls
      (applyClosed returnIterTele Presentation.ids (.const returnIterName)) returnIterRhs =
      cReturnIterRhs := by
    decide
  have step : objectChurch.computation.step
      ((.app (.const returnIterName) (.var 0) : CTm Tower.Head 1).subst
        (CTm.consSub C fun i => .var (Fin.elim0 i)))
      (cReturnIterRhs.subst (CTm.consSub C fun i => .var (Fin.elim0 i))) := by
    have s := objectChurch_step_of_spec
      (List.getElem_mem (l := computationSpecs) (n := 10) (by decide))
      (L := applyClosed returnIterTele Presentation.ids (.const returnIterName))
      (R := returnIterRhs) rfl (CTm.consSub C fun i => .var (Fin.elim0 i))
    rw [eL, eR] at s
    exact s
  have admits : objectChurch.Admits Δ
      ((.app (.const returnIterName) (.var 0) : CTm Tower.Head 1).subst
        (CTm.consSub C fun i => .var (Fin.elim0 i)))
      (cReturnIterRhs.subst (CTm.consSub C fun i => .var (Fin.elim0 i))) := by
    have a := objectChurch_admits_of_mor rfl
      (List.getElem_mem (l := computationSpecs) (n := 10) (by decide))
      (L := applyClosed returnIterTele Presentation.ids (.const returnIterName))
      (R := returnIterRhs) rfl (CTm.consSub C fun i => .var (Fin.elim0 i)) (by decide) (by decide) mor
    rw [eL, eR] at a
    exact a
  have tl : CTyped objectChurch (.snoc .nil cU0) (.app (.const returnIterName) (.var 0))
      cReturnIterCod :=
    CDerivable.appElim (creturnIter_typed (Γ := .snoc .nil cU0)) (.var 0)
  exact ⟨.single (objectHeadReduction.root step), .rootAdmitted step admits (tl.substitute mor)
    (CTyped.substitute (CDerivable.mono ChurchRules.restrict_sub
      (creturnIterRhs_typed_within (A := fun _ => true) rfl rfl)) mor)⟩

/-- **`returnIter` is adequate**: its right side is typed within the numbers and the
iterator, both adequate, so the fundamental lemma makes it adequate; its applications
reduce to it. -/
theorem constAdequateAt_returnIter :
    ConstAdequateAt objectChurchReading objectHeadReduction returnIterName :=
  ConstAdequateAt.ofDefinition ConvRules.objectLevels objectChurch_soundnessFacts
    returnIter_declared objectChurchReading_returnIter
    (objectChurch_valid (allowed := allowedIn [numN, iterName])
      (consts_allowedIn fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact constAdequateAt_num
        · exact constAdequateAt_iter)
      (creturnIterRhs_typed_within rfl rfl) (.snoc .nil ⟨_, .sort _, cU0_typed⟩)).1
    fun _ => returnIter_teleReduces

end ReturnIter

/-! ## `sucStep` -/

section SucStep

open Package (sucStepName eqAtName sucMoveName eqAtTelescope)

/-- The codomain of `sucStep`: `Σ (m : num). eqAt m`. -/
abbrev cSucStepCod : CTm Tower.Head 2 := .sigma cnum (ceqAt (.var 0))

/-- The right side of `sucStep`: `transportCert num eqAt suc sucMove n e`. -/
abbrev cSucStepRhs : CTm Tower.Head 2 :=
  .app (.app (.app (.app (.app (.app (.const transportName) cnum) (.const eqAtName))
    (.const sucN)) (.const sucMoveName)) (.var 1)) (.var 0)

variable {A : DeclName → Bool}

/-- The right side of `sucStep` is typed within the numbers, the successor, `eqAt`, the
successor move and `transportCert`. -/
theorem csucStepRhs_typed_within (hn : A numN = true) (hs : A sucN = true)
    (he : A eqAtName = true) (hm : A sucMoveName = true) (ht : A transportName = true) :
    CTyped (objectChurch.restrict A) cEqAtTele cSucStepRhs cSucStepCod := by
  have t1 := CDerivable.appElim (ctransport_typed_within ht (Γ := cEqAtTele)) (cnum_typed_within hn)
  have t2 := CDerivable.appElim t1 (ceqAtConst_typed_within he hn)
  have t3 := CDerivable.appElim t2 (csucConst_typed_within hs hn)
  have t4 := CDerivable.appElim t3 (csucMove_typed_within hm he hs hn)
  have t5 := CDerivable.appElim t4 (CDerivable.var 1)
  exact CDerivable.appElim t5 (CDerivable.var 0)

/-- `sucStep` at its declared type, in every context. -/
theorem csucStep_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectChurch Γ (.const sucStepName) (liftTm Package.sucStepType).liftClosed :=
  CDerivable.mono ChurchRules.restrict_sub
    (cconst_within (A := fun _ => true) Package.sucStepType (l := Tower.zero) rfl (by decide)
      (by decide)
      (cpiT_within (cnum_typed_within rfl) (cpiT_within (ceqAt_typed_within rfl rfl (.var 0))
        (csigmaT_within (cnum_typed_within rfl) (ceqAt_typed_within rfl rfl (.var 0))))))

theorem sucStep_declared :
    objectChurch.constantType sucStepName = some (pisCtx cEqAtTele cSucStepCod) :=
  objectChurch_declared (T := Package.sucStepType) (by decide) (by decide)

/-- `sucStep` denotes the abstraction of its right side, projected onto its declared
type. -/
theorem objectChurchReading_sucStep :
    objectChurchReading.const sucStepName =
      defConst objectChurchReading cEqAtTele cSucStepCod cSucStepRhs := by
  have h := objectChurchReading_def (f := sucStepName) (tag := .sucStep) (by decide)
    (Θ := eqAtTelescope) (rhs := sucStepRhs) (T := cSucStepCod) (by decide) rfl
  have e : defRhs sucStepName eqAtTelescope sucStepRhs = cSucStepRhs := by
    decide
  rw [h, e]
  rfl

/-- **The applications of `sucStep` reduce to its right side**, by its root step. -/
theorem sucStep_teleReduces {m : Nat} {Δ : CCtx Tower.Head m} :
    TeleReduces objectHeadReduction Δ (CCtx.toTele cEqAtTele) cSucStepCod cSucStepRhs
      (.const sucStepName) fun i => .var (Fin.elim0 i) := by
  intro N tN e te
  have mor : CSubstMor objectChurch cEqAtTele Δ
      (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i))) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact te
    · obtain rfl : j = 0 := Subsingleton.elim j 0
      exact tN
  have eL : elabLeft objectDecls
      (applyClosed eqAtTelescope Presentation.ids (.const sucStepName)) =
      (.app (.app (.const sucStepName) (.var 1)) (.var 0) : CTm Tower.Head 2) := by
    decide
  have eR : elabRight objectDecls
      (applyClosed eqAtTelescope Presentation.ids (.const sucStepName)) sucStepRhs =
      cSucStepRhs := by
    decide
  have step : objectChurch.computation.step
      ((.app (.app (.const sucStepName) (.var 1)) (.var 0) : CTm Tower.Head 2).subst
        (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i))))
      (cSucStepRhs.subst (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i)))) := by
    have s := objectChurch_step_of_spec
      (List.getElem_mem (l := computationSpecs) (n := 11) (by decide))
      (L := applyClosed eqAtTelescope Presentation.ids (.const sucStepName))
      (R := sucStepRhs) rfl (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i)))
    rw [eL, eR] at s
    exact s
  have admits : objectChurch.Admits Δ
      ((.app (.app (.const sucStepName) (.var 1)) (.var 0) : CTm Tower.Head 2).subst
        (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i))))
      (cSucStepRhs.subst (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i)))) := by
    have a := objectChurch_admits_of_mor rfl
      (List.getElem_mem (l := computationSpecs) (n := 11) (by decide))
      (L := applyClosed eqAtTelescope Presentation.ids (.const sucStepName))
      (R := sucStepRhs) rfl (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i))) (by decide) (by decide) mor
    rw [eL, eR] at a
    exact a
  have tl : CTyped objectChurch cEqAtTele (.app (.app (.const sucStepName) (.var 1)) (.var 0))
      cSucStepCod :=
    CDerivable.appElim (CDerivable.appElim (csucStep_typed (Γ := cEqAtTele)) (.var 1)) (.var 0)
  exact ⟨.single (objectHeadReduction.root step), .rootAdmitted step admits (tl.substitute mor)
    (CTyped.substitute (CDerivable.mono ChurchRules.restrict_sub
      (csucStepRhs_typed_within (A := fun _ => true) rfl rfl rfl rfl rfl)) mor)⟩

/-- **`sucStep` is adequate**: its right side is typed within the numbers, the successor,
`eqAt`, the successor move and `transportCert`, all adequate, so the fundamental lemma makes
it adequate; its applications reduce to it. -/
theorem constAdequateAt_sucStep :
    ConstAdequateAt objectChurchReading objectHeadReduction sucStepName :=
  ConstAdequateAt.ofDefinition ConvRules.objectLevels objectChurch_soundnessFacts
    sucStep_declared objectChurchReading_sucStep
    (objectChurch_valid (allowed := allowedIn [numN, sucN, eqAtName, sucMoveName, transportName])
      (consts_allowedIn fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        · exact constAdequateAt_num
        · exact constAdequateAt_suc
        · exact constAdequateAt_eqAt
        · exact constAdequateAt_sucMove'
        · exact constAdequateAt_transport)
      (csucStepRhs_typed_within rfl rfl rfl rfl rfl) cEqAtTele_formed).1
    fun _ => sucStep_teleReduces

end SucStep

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
