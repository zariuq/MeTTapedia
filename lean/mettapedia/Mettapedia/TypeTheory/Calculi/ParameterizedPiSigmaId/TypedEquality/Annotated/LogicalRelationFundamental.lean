import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationRules

/-!
# The fundamental lemma of the relation, relative to the constants a derivation uses

**Sub-packages** (`ChurchRulesSub`): an annotated package whose universe rules, declared
constants and root computations are among those of another. Derivations persist into
the larger package (`CDerivable.mono`).

**Restricting the declared constants** (`Rules.restrict`, `ChurchRules.restrict`): the
package with only the allowed constants declared, and the same universe rules and root
computations. A derivation in `P.restrict allowed` is a derivation of `P` all of whose
constant leaves, those of the declared types' formations included, are allowed
constants. It is a derivation of `P` (`ChurchRules.restrict_sub`); larger sets of allowed
constants keep it (`ChurchRules.restrict_mono`); and every derivation of `P` is one within
all its declared constants (`ChurchRules.sub_restrict`).

**Constants through their spines.** A token of a term typed at the dependent function
type over a telescope is a token of the abstraction, over the telescope, of the term
applied to the telescope's variables (`mem_lams_etaBody`, the η token lemma along a
telescope). A term reduces in no step to that application at typed arguments
(`TeleReduces.eta`). So a constant is adequate when its term is adequate at its declared
type in the empty context (`ConstAdequateAt.of_adequate`), or when its spine at the
variables of its telescope is typed and adequate (`ConstAdequateAt.of_spine`).

**The fundamental lemma** (`CDerivable.valid_sub`, `CDerivable.valid`): for a valid
reading, a head reduction and rigid types satisfying the package conditions (the heads
that are not universes are rigid ground types, head equality is trivial on them, and the
decoder is stuck at universes), every statement derivable in a sub-package whose
declared constants are adequate is valid over a formed context. In particular every
statement derivable within a set of allowed constants that are adequate is valid; the
constants outside the set need not be adequate. With every constant adequate, every
derivable statement is valid (`CDerivable.valid_of_constAdequate`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-- **The rule package with only the allowed constants declared**, its universe rules and
root computation unchanged. -/
def Rules.restrict {Head : Type} (R : Rules Head) (allowed : DeclName → Bool) : Rules Head :=
  { R with constantType := fun c => if allowed c then R.constantType c else none }

namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypedAt principal)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type}

/-! ## Sub-packages -/

/-- **An annotated package contained in another**: its universe rules, declared constants
and root computations are among the other's, and the other requires no more premises of a
step. -/
structure ChurchRulesSub {R R' : Rules Head} (Q : ChurchRules R) (Q' : ChurchRules R') :
    Prop where
  headTyping : ∀ {h u : Head}, R.headTyping h u → R'.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → R'.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → R'.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → R'.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → R'.headEq h h'
  constantType : ∀ {c : DeclName} {D : CTm Head 0}, Q.constantType c = some D →
    Q'.constantType c = some D
  computation : ∀ {n : Nat} {l r : CTm Head n}, Q.computation.step l r → Q'.computation.step l r
  requires : ∀ {n : Nat} {l r : CTm Head n} {premises : List (CPremise Head n)},
    Q.computation.step l r → Q.computation.requires l r premises →
      ∃ premises', Q'.computation.requires l r premises' ∧ ∀ premise ∈ premises', premise ∈ premises

/-- Every package is contained in itself. -/
theorem ChurchRulesSub.refl {R : Rules Head} (Q : ChurchRules R) : ChurchRulesSub Q Q :=
  ⟨id, id, id, id, id, id, id, fun _ requires => ⟨_, requires, fun _ member => member⟩⟩

/-- **A package is contained in the package without its premises**: forgetting the premises
of the steps keeps every derivation (`CDerivable.mono`). -/
theorem ChurchRulesSub.withoutPremises {R : Rules Head} (Q : ChurchRules R) :
    ChurchRulesSub Q Q.withoutPremises :=
  ⟨id, id, id, id, id, id, id,
    fun _ _ => ⟨[], rfl, fun _ member => absurd member List.not_mem_nil⟩⟩

/-- **Derivations persist into a larger package.** -/
theorem CDerivable.mono {R R' : Rules Head} {Q : ChurchRules R} {Q' : ChurchRules R'}
    (sub : ChurchRulesSub Q Q') {J : CStatement Head} (derivation : CDerivable Q J) :
    CDerivable Q' J := by
  induction derivation with
  | headType h => exact .headType (sub.headTyping h)
  | var i => exact .var i
  | const declared _ hu ih => exact .const (sub.constantType declared) ih (sub.isUniverse hu)
  | piForm _ hu _ hv join ihA ihB =>
      exact .piForm ihA (sub.isUniverse hu) ihB (sub.isUniverse hv) (sub.join join)
  | sigmaForm _ hu _ hv join ihA ihB =>
      exact .sigmaForm ihA (sub.isUniverse hu) ihB (sub.isUniverse hv) (sub.join join)
  | lamIntro _ hw _ hu _ ihA ihPi ihBody =>
      exact .lamIntro ihA (sub.isUniverse hw) ihPi (sub.isUniverse hu) ihBody
  | appElim _ _ ihF ihA => exact .appElim ihF ihA
  | pairIntro _ hu _ _ ihS iha ihb => exact .pairIntro ihS (sub.isUniverse hu) iha ihb
  | fstElim _ ih => exact .fstElim ih
  | sndElim _ ih => exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb => exact .idForm ihA (sub.isUniverse hu) iha ihb
  | reflIntro _ ih => exact .reflIntro ih
  | sub _ _ ihT ihLe => exact .sub ihT ihLe
  | conv _ _ hu ihT ihE => exact .conv ihT ihE (sub.isUniverse hu)
  | refl _ ih => exact .refl ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihE => exact .convEq ih ihE (sub.isUniverse hu)
  | subEq _ _ ih ihLe => exact .subEq ih ihLe
  | headEq same _ _ ih ih' => exact .headEq (sub.headEq same) ih ih'
  | piCong _ hu _ hv join ihA ihB =>
      exact .piCong ihA (sub.isUniverse hu) ihB (sub.isUniverse hv) (sub.join join)
  | sigmaCong _ hu _ hv join ihA ihB =>
      exact .sigmaCong ihA (sub.isUniverse hu) ihB (sub.isUniverse hv) (sub.join join)
  | idCong _ hu _ _ ihA iha ihb => exact .idCong ihA (sub.isUniverse hu) iha ihb
  | lamCong _ hw _ hu _ ihA ihPi ihBody =>
      exact .lamCong ihA (sub.isUniverse hw) ihPi (sub.isUniverse hu) ihBody
  | appCong _ _ ihF ihA => exact .appCong ihF ihA
  | pairCong _ hu _ _ ihS iha ihb => exact .pairCong ihS (sub.isUniverse hu) iha ihb
  | fstCong _ ih => exact .fstCong ih
  | sndCong _ ih => exact .sndCong ih
  | reflCong _ ih => exact .reflCong ih
  | betaPi _ hu _ _ ihPi ihBody iha => exact .betaPi ihPi (sub.isUniverse hu) ihBody iha
  | betaFst _ hu _ _ ihS iha ihb => exact .betaFst ihS (sub.isUniverse hu) iha ihb
  | betaSnd _ hu _ _ ihS iha ihb => exact .betaSnd ihS (sub.isUniverse hu) iha ihb
  | root step requires _ _ _ ihPremises ihL ihR =>
      obtain ⟨premises', requires', among⟩ := sub.requires step requires
      exact .root (sub.computation step) requires'
        (fun premise member => ihPremises premise (among premise member)) ihL ihR
  | etaPi _ _ _ ihF ihG ihBody => exact .etaPi ihF ihG ihBody
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd => exact .etaSigma ihP ihQ ihFst ihSnd
  | subEqual _ hu ih => exact .subEqual ih (sub.isUniverse hu)
  | subUniv c => exact .subUniv (sub.cumulative c)
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      exact .subPi ihPi (sub.isUniverse hu) ihPi' (sub.isUniverse hu') ihA (sub.isUniverse hw) ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      exact .subSigma ihS (sub.isUniverse hu) ihS' (sub.isUniverse hu') ihA ihB
  | subTrans _ _ ih₁ ih₂ => exact .subTrans ih₁ ih₂

/-! ## Restricting the declared constants -/

section Restrict

variable {R : Rules Head}

/-- **The annotated package with only the allowed constants declared**, its root
computation unchanged. -/
def ChurchRules.restrict (P : ChurchRules R) (allowed : DeclName → Bool) :
    ChurchRules (R.restrict allowed) where
  constantType c := if allowed c then P.constantType c else none
  computation := P.computation
  erase_constantType c := by
    show Option.map CTm.erase (if allowed c then P.constantType c else none) =
      (if allowed c then R.constantType c else none)
    cases allowed c
    · rfl
    · exact P.erase_constantType c
  erase_step step := P.erase_step step

variable {P : ChurchRules R} {allowed : DeclName → Bool}

/-- A constant declared in the restricted package is allowed and declared at the same
type. -/
theorem ChurchRules.restrict_declared {c : DeclName} {D : CTm Head 0}
    (h : (P.restrict allowed).constantType c = some D) :
    allowed c = true ∧ P.constantType c = some D := by
  change (if allowed c then P.constantType c else none) = some D at h
  cases e : allowed c
  · rw [e] at h
    cases h
  · rw [e] at h
    exact ⟨rfl, h⟩

/-- An allowed constant is declared in the restricted package at its type. -/
theorem ChurchRules.restrict_constantType {c : DeclName} (h : allowed c = true) :
    (P.restrict allowed).constantType c = P.constantType c := by
  change (if allowed c then P.constantType c else none) = _
  rw [h]
  rfl

/-- A constant that is not allowed is not declared in the restricted package. -/
theorem ChurchRules.restrict_undeclared {c : DeclName} (h : allowed c = false) :
    (P.restrict allowed).constantType c = none := by
  change (if allowed c then P.constantType c else none) = _
  rw [h]
  rfl

/-- **The restricted package is inside the package.** -/
theorem ChurchRules.restrict_sub : ChurchRulesSub (P.restrict allowed) P :=
  ⟨id, id, id, id, id, fun h => (ChurchRules.restrict_declared h).2, id,
    fun _ requires => ⟨_, requires, fun _ member => member⟩⟩

/-- **More allowed constants keep the derivations.** -/
theorem ChurchRules.restrict_mono {allowed' : DeclName → Bool}
    (le : ∀ c, allowed c = true → allowed' c = true) :
    ChurchRulesSub (P.restrict allowed) (P.restrict allowed') :=
  ⟨id, id, id, id, id, fun h => by
    obtain ⟨hc, h⟩ := ChurchRules.restrict_declared h
    rw [ChurchRules.restrict_constantType (le _ hc)]
    exact h, id, fun _ requires => ⟨_, requires, fun _ member => member⟩⟩

/-- **Every derivation is one within its declared constants**, when all of them are
allowed. -/
theorem ChurchRules.sub_restrict
    (all : ∀ {c : DeclName} {D : CTm Head 0}, P.constantType c = some D → allowed c = true) :
    ChurchRulesSub P (P.restrict allowed) :=
  ⟨id, id, id, id, id, fun h => by rw [ChurchRules.restrict_constantType (all h)]; exact h, id,
    fun _ requires => ⟨_, requires, fun _ member => member⟩⟩

end Restrict

/-! ## Constants through their spines -/

/-- **The η-body of a term along a telescope**: the term, weakened, applied to the
telescope's variables in the extended context. -/
def CTele.etaBody : {n m : Nat} → CTele Head n m → CTm Head n → CTm Head m
  | _, _, .nil, h => h
  | _, _, .cons _ rest, h => etaBody rest (.app (h.rename wk) (.var 0))

/-- **The η token lemma along a telescope**: a token of a term typed at the dependent
function type over a telescope is a token of the abstraction, over the telescope, of the
term applied to the telescope's variables. At each entry, the outputs of a typed entry of
the term are tokens of its value at the projection of the entry's input
(`typed_fnEntry_app`). -/
theorem mem_lams_etaBody (Rd : Reading Head) : ∀ {n m : Nat} (tele : CTele Head n m)
    {T : CTm Head m} (h : CTm Head n) (ρ : Env n) {s : Tok}, (cinterp Rd h ρ).Mem s →
      TypedAt (cinterp Rd (tele.pis T) ρ) s → (cinterp Rd (tele.lams (tele.etaBody h)) ρ).Mem s
  | _, _, .nil, _, _, _, _, hs, _ => hs
  | _, _, .cons A rest, T, h, ρ, s, hs, hsT => by
      obtain ⟨b, hb, hbu, hbt⟩ := hsT
      have hbF : Ideal.Below b (Ideal.former .pi (cinterp Rd A ρ) fun X =>
          cinterp Rd (rest.pis T) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := hb
      obtain ⟨X, Y, rfl, -, -⟩ := Ideal.tyTok_below_pi hbF hbt
      have hmono : Ideal.Monotone fun X =>
          cinterp Rd (rest.lams (rest.etaBody (.app (h.rename wk) (.var 0))))
            (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h' =>
        (cinterp_envCont Rd _).mono (Env.Le.cons (Ideal.projT_mono (principal_mono h'))
          (Env.Le.refl ρ))
      show (Ideal.lam fun X => cinterp Rd (rest.lams (rest.etaBody (.app (h.rename wk) (.var 0))))
        (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)).Mem (.fn .lam [] X Y)
      refine (Ideal.mem_lam_fn hmono).2 fun y hy => ?_
      obtain ⟨hyApp, hyT⟩ := typed_fnEntry_app (cinterp_cont_cons Rd (rest.pis T) ρ) hs
        ⟨b, hb, hbu, hbt⟩ y hy
      refine mem_lams_etaBody Rd rest (.app (h.rename wk) (.var 0)) _ ?_ hyT
      show (Ideal.app (cinterp Rd (h.rename wk) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ))
        (projT (cinterp Rd A ρ) (principal X))).Mem y
      rw [cinterp_rename_wk]
      exact hyApp

section Spines

variable {R : Rules Head} {P : ChurchRules R} {K : RigidTypes P}

/-- **A term reduces, in no step, to its η-body along a telescope**: applied to arguments
typed along the telescope, a substituted term is its η-body at the substitution extended
by the arguments, typed at the codomain when the η-body is typed over the extended
context. -/
theorem TeleReduces.eta (H : HeadReduction P K) : ∀ {n m : Nat} (tele : CTele Head n m)
    {Γ : CCtx Head n} {T : CTm Head m} {h : CTm Head n},
    CTyped P (tele.extend Γ) (tele.etaBody h) T → ∀ {k : Nat} {Δ : CCtx Head k}
    {σ : CSub Head n k}, CSubstMor P Γ Δ σ → TeleReduces H Δ tele T (tele.etaBody h) (h.subst σ) σ
  | _, _, .nil, _, _, _, typed, _, _, _, mσ => CRedTm.refl (typed.substitute mσ)
  | _, _, .cons A rest, Γ, T, h, typed, k, Δ, σ, mσ => by
      intro N tN
      have mσ' : CSubstMor P (.snoc Γ A) Δ (CTm.consSub N σ) :=
        (CSubstEq.cons ⟨mσ, fun i => .refl (mσ i)⟩ tN (.refl tN)).1
      have r := TeleReduces.eta H rest (Γ := .snoc Γ A) (h := .app (h.rename wk) (.var 0)) typed mσ'
      have e : (CTm.app (h.rename wk) (.var 0)).subst (CTm.consSub N σ) = .app (h.subst σ) N := by
        show CTm.app ((h.rename wk).subst (CTm.consSub N σ)) N = _
        rw [CTm.subst_consSub_wk]
      rw [e] at r
      exact r

variable {Rd : Reading Head} {H : HeadReduction P K} {L : Type} [LevelOrder L]
  (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

/-- **A constant is adequate when its term is, in the empty context**, at its declared
type. -/
theorem ConstAdequateAt.of_adequate {c : DeclName} {D : CTm Head 0}
    (declared : P.constantType c = some D) (h : Adequate Rd H .nil (.const c) D) :
    ConstAdequateAt Rd H c := by
  intro D' u declared' _ _ _ m Δ formed s hs hsT
  obtain rfl : D = D' := Option.some.inj (declared.symm.trans declared')
  have r := h Env.nil trivial formed SubstRel.nil s hs hsT
  rwa [CTm.subst_closed] at r

include levels sound in
/-- **A constant is adequate when its spine is**: a constant declared at the dependent
function type over a context is adequate when the constant applied to the context's
variables is typed and adequate at the codomain. Its tokens typed at its declared type
are tokens of the abstraction of that spine (`mem_lams_etaBody`), and the constant
reduces, in no step, to the spine at related arguments (`TeleReduces.eta`), so the
relation at a telescope (`RT.telescope`) relates it to itself. -/
theorem ConstAdequateAt.of_spine {c : DeclName} {k : Nat} {Θ : CCtx Head k} {T : CTm Head k}
    (declared : P.constantType c = some (pisCtx Θ T))
    (typed : CTyped P Θ ((CCtx.toTele Θ).etaBody (.const c)) T)
    (spine : Adequate Rd H Θ ((CCtx.toTele Θ).etaBody (.const c)) T) :
    ConstAdequateAt Rd H c := by
  intro D u declared' hu tD hD m Δ formed s hs hsT
  obtain rfl : pisCtx Θ T = D := Option.some.inj (declared.symm.trans declared')
  have typed' : CTyped P ((CCtx.toTele Θ).extend .nil) ((CCtx.toTele Θ).etaBody (.const c)) T := by
    rw [CCtx.extend_toTele]
    exact typed
  have red : TeleReduces H Δ (CCtx.toTele Θ) T ((CCtx.toTele Θ).etaBody (.const c)) (.const c)
      fun i => .var (Fin.elim0 i) :=
    TeleReduces.eta H (CCtx.toTele Θ) typed' (σ := fun i => .var (Fin.elim0 i)) fun i => i.elim0
  have hsT' : TypedAt (cinterp Rd ((CCtx.toTele Θ).pis T) Env.nil) s := by
    rw [CCtx.pis_toTele]
    exact hsT
  have hs' := mem_lams_etaBody Rd (CCtx.toTele Θ) (.const c) Env.nil hs hsT'
  have tele := RT.telescope levels sound (CCtx.toTele Θ) (Γ := .nil)
    (by rw [CCtx.pis_toTele]; exact ⟨u, hu, tD⟩) (by rw [CCtx.pis_toTele]; exact hD)
    (by rw [CCtx.extend_toTele]; exact spine) Env.nil trivial formed
    SubstRel.nil red red s hs' hsT'
  rw [CCtx.pis_toTele, CTm.subst_var_comp] at tele
  exact tele

end Spines

/-! ## The fundamental lemma -/

/-- The context of a statement is formed. -/
def CStatement.CtxFormed {R : Rules Head} (P : ChurchRules R) : CStatement Head → Prop
  | .typing Γ _ _ => CCtxFormed P Γ
  | .equality Γ _ _ _ => CCtxFormed P Γ
  | .sub Γ _ _ => CCtxFormed P Γ

section Fundamental

variable {R : Rules Head} {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P}
  {H : HeadReduction P K} {L : Type} [LevelOrder L]

/-- **The fundamental lemma, for a sub-package whose declared constants are adequate.**
For a valid reading, rigid ground heads, head equality trivial on them and the decoder
stuck at universes, every statement derivable in a sub-package of `P` whose declared
constants are adequate is valid over a formed context. -/
theorem CDerivable.valid_sub (levels : LevelModel R L) (valid : ReadingValid Rd P)
    (heads : K.GroundHeads Rd) (ground : GroundHeadEq R) (stuck : H.DecoderStuckAtUniverses)
    {R' : Rules Head} {Q : ChurchRules R'} (sub : ChurchRulesSub Q P)
    (consts : ∀ {c : DeclName} {D : CTm Head 0}, Q.constantType c = some D →
      ConstAdequateAt Rd H c)
    {J : CStatement Head} (derivation : CDerivable Q J) : J.CtxFormed P → J.Valid Rd H := by
  have sound := valid.soundnessFacts
  induction derivation with
  | headType h => exact fun _ => CStatement.Valid.headType levels sound heads (sub.headTyping h)
  | var i => exact fun _ => CStatement.Valid.var i
  | const declared tType hu ihType =>
      exact fun _ => CStatement.Valid.constAt levels sound (consts declared)
        (sub.constantType declared) (ihType CCtxFormed.nil) (tType.mono sub) (sub.isUniverse hu)
  | piForm tA hu tB hv join ihA ihB =>
      intro formed
      have tA' := tA.mono sub
      exact CStatement.Valid.piForm levels sound (ihA formed) (sub.isUniverse hu)
        (ihB (.snoc formed ⟨_, sub.isUniverse hu, tA'⟩)) (sub.isUniverse hv) (sub.join join) tA'
        (tB.mono sub)
  | sigmaForm tA hu tB hv join ihA ihB =>
      intro formed
      have tA' := tA.mono sub
      exact CStatement.Valid.sigmaForm levels sound (ihA formed) (sub.isUniverse hu)
        (ihB (.snoc formed ⟨_, sub.isUniverse hu, tA'⟩)) (sub.isUniverse hv) (sub.join join) tA'
        (tB.mono sub)
  | lamIntro tA hw tPi hu tb ihA ihPi ihBody =>
      intro formed
      have tA' := tA.mono sub
      exact CStatement.Valid.lamIntro levels sound (ihA formed) (sub.isUniverse hw) (ihPi formed)
        (sub.isUniverse hu) (ihBody (.snoc formed ⟨_, sub.isUniverse hw, tA'⟩)) tA' (tPi.mono sub)
        (tb.mono sub)
  | appElim tg ta ihF ihA =>
      exact fun formed => CStatement.Valid.appElim levels sound (ihF formed) (ihA formed)
        (tg.mono sub) (ta.mono sub)
  | pairIntro tS hu ta tb ihS iha ihb =>
      exact fun formed => CStatement.Valid.pairIntro levels sound (ihS formed) (sub.isUniverse hu)
        (iha formed) (ihb formed) (tS.mono sub) (ta.mono sub) (tb.mono sub)
  | fstElim tp ih => exact fun formed => CStatement.Valid.fstElim levels (ih formed) (tp.mono sub)
  | sndElim tp ih =>
      exact fun formed => CStatement.Valid.sndElim levels sound formed (ih formed) (tp.mono sub)
  | idForm tA hu ta tb ihA iha ihb =>
      exact fun formed => CStatement.Valid.idForm levels sound (ihA formed) (sub.isUniverse hu)
        (iha formed) (ihb formed) (tA.mono sub) (ta.mono sub) (tb.mono sub)
  | reflIntro ta ih =>
      exact fun formed => CStatement.Valid.reflIntro levels formed (ih formed) (ta.mono sub)
  | sub _ le ihT ihLe =>
      exact fun formed => CStatement.Valid.sub levels valid (ihT formed) (ihLe formed) (le.mono sub)
  | conv _ e hu ihT ihE =>
      exact fun formed => CStatement.Valid.conv levels sound (ihT formed) (ihE formed)
        (sub.isUniverse hu) (e.mono sub)
  | refl _ ih => exact fun formed => CStatement.Valid.refl (ih formed)
  | symm e ih => exact fun formed => CStatement.Valid.symm levels sound (ih formed) (e.mono sub)
  | trans e₁ _ ih₁ ih₂ =>
      exact fun formed => CStatement.Valid.trans levels sound (ih₁ formed) (ih₂ formed)
        (e₁.mono sub)
  | convEq _ eAB hu ih ihE =>
      exact fun formed => CStatement.Valid.convEq levels sound (ih formed) (ihE formed)
        (sub.isUniverse hu) (eAB.mono sub)
  | subEq _ le ih ihLe =>
      exact fun formed => CStatement.Valid.subEq levels valid (ih formed) (ihLe formed)
        (le.mono sub)
  | headEq same _ _ ih ih' =>
      exact fun formed => CStatement.Valid.headEq levels sound ground stuck (sub.headEq same)
        (ih formed) (ih' formed)
  | piCong eA hu eB hv join ihA ihB =>
      intro formed
      have eA' := eA.mono sub
      exact CStatement.Valid.piCong levels sound formed (ihA formed) (sub.isUniverse hu)
        (ihB (.snoc formed ⟨_, sub.isUniverse hu, (CEqual.typed levels eA' formed).1⟩))
        (sub.isUniverse hv) (sub.join join) eA' (eB.mono sub)
  | sigmaCong eA hu eB hv join ihA ihB =>
      intro formed
      have eA' := eA.mono sub
      exact CStatement.Valid.sigmaCong levels sound formed (ihA formed) (sub.isUniverse hu)
        (ihB (.snoc formed ⟨_, sub.isUniverse hu, (CEqual.typed levels eA' formed).1⟩))
        (sub.isUniverse hv) (sub.join join) eA' (eB.mono sub)
  | idCong eA hu ea eb ihA iha ihb =>
      exact fun formed => CStatement.Valid.idCong levels sound formed (ihA formed)
        (sub.isUniverse hu) (iha formed) (ihb formed) (eA.mono sub) (ea.mono sub) (eb.mono sub)
  | lamCong eA hw tPi hu eb ihA ihPi ihBody =>
      intro formed
      have eA' := eA.mono sub
      exact CStatement.Valid.lamCong levels sound formed (ihA formed) (sub.isUniverse hw)
        (ihPi formed) (sub.isUniverse hu)
        (ihBody (.snoc formed ⟨_, sub.isUniverse hw, (CEqual.typed levels eA' formed).1⟩)) eA'
        (tPi.mono sub) (eb.mono sub)
  | appCong ef ea ihF ihA =>
      exact fun formed => CStatement.Valid.appCong levels sound formed (ihF formed) (ihA formed)
        (ef.mono sub) (ea.mono sub)
  | pairCong tS hu ea eb ihS iha ihb =>
      exact fun formed => CStatement.Valid.pairCong levels sound formed (ihS formed)
        (sub.isUniverse hu) (iha formed) (ihb formed) (tS.mono sub) (ea.mono sub) (eb.mono sub)
  | fstCong e ih =>
      exact fun formed => CStatement.Valid.fstCong levels formed (ih formed) (e.mono sub)
  | sndCong e ih =>
      exact fun formed => CStatement.Valid.sndCong levels sound formed (ih formed) (e.mono sub)
  | reflCong e ih =>
      exact fun formed => CStatement.Valid.reflCong levels sound formed (ih formed) (e.mono sub)
  | betaPi tPi hu tb ta ihPi ihBody iha =>
      intro formed
      have tPi' := tPi.mono sub
      exact CStatement.Valid.betaPi levels sound formed (ihPi formed) (sub.isUniverse hu)
        (ihBody (.snoc formed (CIsType.pi_parts ⟨_, sub.isUniverse hu, tPi'⟩).1)) (iha formed) tPi'
        (tb.mono sub) (ta.mono sub)
  | betaFst tS hu ta tb ihS iha ihb =>
      exact fun formed => CStatement.Valid.betaFst levels sound (ihS formed) (sub.isUniverse hu)
        (iha formed) (ihb formed) (tS.mono sub) (ta.mono sub) (tb.mono sub)
  | betaSnd tS hu ta tb _ _ ihb =>
      exact fun formed => CStatement.Valid.betaSnd levels sound formed (sub.isUniverse hu)
        (ihb formed) (tS.mono sub) (ta.mono sub) (tb.mono sub)
  | root step requires derivable tl tr _ ihL ihR =>
      obtain ⟨premises', requires', among⟩ := sub.requires step requires
      exact fun formed => CStatement.Valid.root levels sound (sub.computation step)
        ⟨premises', requires',
          fun premise member => (derivable premise (among premise member)).mono sub⟩
        (ihL formed) (ihR formed) (tl.mono sub) (tr.mono sub)
  | etaPi tf tg eapp ihF ihG ihApp =>
      intro formed
      have tf' := tf.mono sub
      exact CStatement.Valid.etaPi levels sound formed (ihF formed) (ihG formed)
        (ihApp (.snoc formed (CIsType.pi_parts (CTyped.isType levels tf' formed)).1)) tf'
        (tg.mono sub) (eapp.mono sub)
  | etaSigma tp _ efst _ ihP ihQ ihFst ihSnd =>
      exact fun formed => CStatement.Valid.etaSigma levels sound formed (ihP formed) (ihQ formed)
        (ihFst formed) (ihSnd formed) (tp.mono sub) (efst.mono sub)
  | subEqual _ hu ih =>
      exact fun formed => CStatement.Valid.subEqual levels sound (ih formed) (sub.isUniverse hu)
  | subUniv c => exact fun _ => CStatement.Valid.subUniv levels sound (sub.cumulative c)
  | subPi tPi hu tPi' hu' eA hw leB ihPi ihPi' ihA ihB =>
      intro formed
      have tPiL := tPi.mono sub
      exact CStatement.Valid.subPi levels sound formed (ihPi formed) (sub.isUniverse hu)
        (ihPi' formed) (sub.isUniverse hu') (ihA formed) (sub.isUniverse hw)
        (ihB (.snoc formed (CIsType.pi_parts ⟨_, sub.isUniverse hu, tPiL⟩).1)) tPiL
        (tPi'.mono sub) (eA.mono sub) (leB.mono sub)
  | subSigma tS hu tS' hu' leA leB ihS ihS' ihA ihB =>
      intro formed
      have tSL := tS.mono sub
      exact CStatement.Valid.subSigma levels sound valid (ihS formed) (sub.isUniverse hu)
        (ihS' formed) (sub.isUniverse hu') (ihA formed)
        (ihB (.snoc formed (CIsType.sigma_parts ⟨_, sub.isUniverse hu, tSL⟩).1)) tSL
        (tS'.mono sub) (leA.mono sub) (leB.mono sub)
  | subTrans le₁ _ ih₁ ih₂ =>
      exact fun formed => CStatement.Valid.subTrans levels valid (ih₁ formed) (ih₂ formed)
        (le₁.mono sub)

/-- **The fundamental lemma, relative to the constants a derivation uses.** For a valid
reading, rigid ground heads, head equality trivial on them and the decoder stuck at
universes: if every allowed constant is adequate, every statement derivable within the
allowed constants is valid over a formed context. -/
theorem CDerivable.valid (levels : LevelModel R L) (valid : ReadingValid Rd P)
    (heads : K.GroundHeads Rd) (ground : GroundHeadEq R) (stuck : H.DecoderStuckAtUniverses)
    {allowed : DeclName → Bool}
    (consts : ∀ {c : DeclName}, allowed c = true → ConstAdequateAt Rd H c)
    {J : CStatement Head} (derivation : CDerivable (P.restrict allowed) J) :
    J.CtxFormed P → J.Valid Rd H :=
  CDerivable.valid_sub levels valid heads ground stuck ChurchRules.restrict_sub
    (fun declared => consts (ChurchRules.restrict_declared declared).1) derivation

/-- **The fundamental lemma, with every constant adequate**: every derivable statement is
valid over a formed context. -/
theorem CDerivable.valid_of_constAdequate (levels : LevelModel R L) (valid : ReadingValid Rd P)
    (heads : K.GroundHeads Rd) (ground : GroundHeadEq R) (stuck : H.DecoderStuckAtUniverses)
    (consts : ConstAdequate Rd H) {J : CStatement Head} (derivation : CDerivable P J) :
    J.CtxFormed P → J.Valid Rd H :=
  CDerivable.valid_sub levels valid heads ground stuck
    (ChurchRulesSub.refl P) (fun _ => consts) derivation

end Fundamental

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
