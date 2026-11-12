import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinTyping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralRules

/-!
# The join widening for η-long normal forms, and what it forces at a flex–flex equation

* **η-long forms are normal** (`long_normal_at`): with rigid constants, an η-long β-normal form has no reduction step.
* **The join widening** (`long_type_join`): a type that is η-long over `Γ₁` and over `Γ₂` is η-long over their join
  (heads compared by equality); without that hypothesis it is still a type there (`isType_join`), and an η-long term
  of a type over both telescopes has that type over the join (`typed_long_join`).
* **What the join forces** (`joinK_forced`): over `F : Π (x̄ : U_{p̄F}). U_c` and `G : Π (x̄ : U_{p̄G}). U_c`, every
  solution of `λ x̄. F x̄ ≐ λ x̄. G x̄` sends `F` and `G` to the η-expansions of one family of the join
  `Π (x̄ : U_{p̄F ⊔ p̄G}). U_c`. The domains need not be comparable. The family is the η-long normal form of the
  values' common body: the equation makes the two normal forms the same over the annotation's binders, and that form
  is typed over the binders of `F` and over those of `G`, hence over their join.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative ContextualDependentEtaLong
open ContextualDependentNormalChecking

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## η-long forms are normal -/

section Normal

variable {S : Setting Head L}

/-- What an η-long form gives: a normal type, a normal term, a normal spine that is not an introduction. -/
@[reducible] def LongNormal (S : Setting Head L) : LongStatement Head → Prop
  | .type _ V => Normal (S := S) V
  | .term _ v _ => Normal (S := S) v
  | .spine _ t _ => Normal (S := S) t ∧ (∀ b, t ≠ .lam b) ∧ (∀ a b, t ≠ .pair a b)

variable (rigid : ∀ name, S.roles name = .rigid)

include rigid in
/-- With rigid constants there is no root computation step. -/
theorem no_root_step {n : Nat} {t u : Tm Head n} (step : S.R.computation.step t u) : False := by
  obtain ⟨c, _, _, _, computes, _, _, _⟩ := S.shape.spine step
  rw [rigid c] at computes
  cases computes

include rigid in
/-- **η-long forms are normal.** -/
theorem long_normal_at {st : LongStatement Head} (long : Long S.R S.roles st) : LongNormal S st := by
  induction long with
  | head _ =>
      intro target step
      cases step with
      | head e => exact e
      | root r => exact no_root_step rigid r
  | pi _ _ _ ihA ihB =>
      intro target step
      cases step with
      | congPiDom s => exact ihA _ s
      | congPiCod s => exact ihB _ s
      | root r => exact no_root_step rigid r
  | sigma _ _ _ ihA ihB =>
      intro target step
      cases step with
      | congSigmaDom s => exact ihA _ s
      | congSigmaCod s => exact ihB _ s
      | root r => exact no_root_step rigid r
  | id _ _ _ _ ihA ihx ihy =>
      intro target step
      cases step with
      | congIdTy s => exact ihA _ s
      | congIdLeft s => exact ihx _ s
      | congIdRight s => exact ihy _ s
      | root r => exact no_root_step rigid r
  | neutralType _ _ _ ih => exact ih.1
  | univ _ _ _ _ ih => exact ih
  | lam _ _ _ _ ih =>
      intro target step
      cases step with
      | congLam s => exact ih _ s
      | root r => exact no_root_step rigid r
  | pair _ _ _ _ iha ihb =>
      intro target step
      cases step with
      | congPairFst s => exact iha _ s
      | congPairSnd s => exact ihb _ s
      | root r => exact no_root_step rigid r
  | refl _ _ _ ih =>
      intro target step
      cases step with
      | congRefl s => exact ih _ s
      | root r => exact no_root_step rigid r
  | neutral _ _ _ _ ih => exact ih.1
  | var i _ =>
      refine ⟨fun target step => ?_, (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
      cases step with
      | root r => exact no_root_step rigid r
  | const _ _ _ _ =>
      refine ⟨fun target step => ?_, (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
      cases step with
      | root r => exact no_root_step rigid r
  | app _ _ _ _ ihf iha =>
      refine ⟨fun target step => ?_, (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
      cases step with
      | betaPi body _ => exact ihf.2.1 body rfl
      | congAppFun s => exact ihf.1 _ s
      | congAppArg s => exact iha _ s
      | root r => exact no_root_step rigid r
  | fst _ _ _ ih =>
      refine ⟨fun target step => ?_, (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
      cases step with
      | betaSigmaFst => exact ih.2.2 _ _ rfl
      | congFst s => exact ih.1 _ s
      | root r => exact no_root_step rigid r
  | snd _ _ _ ih =>
      refine ⟨fun target step => ?_, (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
      cases step with
      | betaSigmaSnd => exact ih.2.2 _ _ rfl
      | congSnd s => exact ih.1 _ s
      | root r => exact no_root_step rigid r

include rigid in
theorem long_type_normal {n : Nat} {Γ : Ctx Head n} {V : Tm Head n} (long : Long S.R S.roles (.type Γ V)) :
    Normal (S := S) V :=
  long_normal_at rigid long

include rigid in
theorem long_term_normal {n : Nat} {Γ : Ctx Head n} {v T : Tm Head n} (long : Long S.R S.roles (.term Γ v T)) :
    Normal (S := S) v :=
  long_normal_at rigid long

end Normal

/-! ## Joins of telescopes and of lists of universes -/

section Lists

theorem JoinOf.refl (R : Rules Head) : ∀ {n : Nat} (Γ : Ctx Head n), JoinOf R Γ Γ Γ
  | _, .nil => .nil
  | _, .snoc Γ A => .same A (JoinOf.refl R Γ)

/-- **Pointwise least upper bounds** of two lists of universes. -/
inductive JoinsK (R : Rules Head) : List Head → List Head → List Head → Prop where
  | nil : JoinsK R [] [] []
  | cons {p p' w : Head} {ps ps' ws : List Head} : R.isUniverse w → IsLub R w p p' → JoinsK R ps ps' ws →
      JoinsK R (p :: ps) (p' :: ps') (w :: ws)

variable {S : Setting Head L}

theorem JoinsK.left {ps ps' ws : List Head} (joins : JoinsK S.R ps ps' ws) : List.Forall₂ S.R.cumulative ps ws := by
  induction joins with
  | nil => exact .nil
  | cons _ lub _ ih => exact .cons lub.1 ih

theorem JoinsK.right {ps ps' ws : List Head} (joins : JoinsK S.R ps ps' ws) :
    List.Forall₂ S.R.cumulative ps' ws := by
  induction joins with
  | nil => exact .nil
  | cons _ lub _ ih => exact .cons lub.2.1 ih

theorem JoinsK.universes {ps ps' ws : List Head} (joins : JoinsK S.R ps ps' ws) : AllUniverses S.R ws := by
  induction joins with
  | nil => intro _ member; cases member
  | cons hw _ _ ih =>
      intro w member
      rcases List.mem_cons.mp member with rfl | member
      · exact hw
      · exact ih w member

end Lists

/-! ## The join widening for η-long forms -/

section LongJoin

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')

include facts roots heads algebra rigid complete headsTyped in
/-- **A type η-long over two telescopes is a type over their join.** -/
theorem isType_join {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (j : JoinOf S.R Γ₁ Γ₂ J) (formed₁ : CtxFormed S.R Γ₁)
    (formed₂ : CtxFormed S.R Γ₂) (formedJ : CtxFormed S.R J) {V : Tm Head n}
    (long₁ : Long S.R S.roles (.type Γ₁ V)) (long₂ : Long S.R S.roles (.type Γ₂ V)) : IsType S.R J V := by
  obtain ⟨u₁, hu₁, t₁⟩ : IsType S.R Γ₁ V := long₁.sound
  obtain ⟨u₂, hu₂, t₂⟩ : IsType S.R Γ₂ V := long₂.sound
  obtain ⟨w, joined⟩ := S.levels.join_exists hu₁ hu₂
  have hw := (S.levels.join_level joined).1
  exact ⟨w, hw, typed_join facts roots heads algebra rigid complete headsTyped j formed₁ formed₂ formedJ
    (long_type_normal rigid long₁) (Derivable.cumul t₁ (S.levels.join_upper joined).1)
    (Derivable.cumul t₂ (S.levels.join_upper joined).2) (IsType.head_of_universe hw)⟩

include facts roots heads algebra rigid complete headsTyped in
/-- **The join widening for η-long types**: a type η-long over `Γ₁` and over `Γ₂` is η-long over their join, when
heads are compared by equality. -/
theorem long_type_join (discrete : ∀ {h h' : Head}, S.R.headEq h h' → h = h') {n : Nat} {Γ₁ Γ₂ J : Ctx Head n}
    (j : JoinOf S.R Γ₁ Γ₂ J) (formed₁ : CtxFormed S.R Γ₁) (formed₂ : CtxFormed S.R Γ₂) (formedJ : CtxFormed S.R J)
    {V : Tm Head n} (long₁ : Long S.R S.roles (.type Γ₁ V)) (long₂ : Long S.R S.roles (.type Γ₂ V)) :
    Long S.R S.roles (.type J V) := by
  have isJ := isType_join facts roots heads algebra rigid complete headsTyped j formed₁ formed₂ formedJ long₁ long₂
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formedJ isJ
  obtain ⟨u, hu, tJ⟩ := isJ
  obtain ⟨_, eZ⟩ := atZ hu tJ
  have narrowed := Long.type_narrow facts lZ j.narrows_left formedJ formed₁
  have same := long_type_unique facts roots heads algebra complete formed₁ long₁ narrowed
    ⟨u, hu, equal_narrow j.narrows_left eZ⟩
  rw [same.eq_of_discrete discrete]
  exact lZ

include facts roots heads algebra rigid complete headsTyped in
/-- **An η-long term of a type over two telescopes has it over their join.** -/
theorem typed_long_join {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (j : JoinOf S.R Γ₁ Γ₂ J) (formed₁ : CtxFormed S.R Γ₁)
    (formed₂ : CtxFormed S.R Γ₂) (formedJ : CtxFormed S.R J) {v E : Tm Head n}
    (long₁ : Long S.R S.roles (.term Γ₁ v E)) (long₂ : Long S.R S.roles (.term Γ₂ v E)) (isE : IsType S.R J E) :
    Typed S.R J v E :=
  typed_join facts roots heads algebra rigid complete headsTyped j formed₁ formed₂ formedJ
    (long_term_normal rigid long₁) long₁.sound long₂.sound isE

end LongJoin

/-! ## What the join forces -/

section Forcing

variable {S : Setting Head L}

/-- β at an argument of a smaller universe than the abstraction's domain. -/
theorem beta_open_below {n : Nat} {Γ : Ctx Head n} {w p u : Head} {B N : Tm Head (n + 1)}
    (tPi : Typed S.R Γ (.pi (.head w) B) (.head u)) (hu : S.R.isUniverse u)
    (body : Typed S.R (.snoc Γ (.head w)) N B) (below : S.R.cumulative p w) :
    Equal S.R (.snoc Γ (.head p)) (.app (Presentation.rename wk (.lam N)) (.var 0)) N B := by
  have step := Derivable.betaPi (tPi.rename (CtxRen.wk Γ (.head p))) hu
    (body.rename ((CtxRen.wk Γ (.head p)).snoc (.head w))) (Derivable.cumul (var_head_typed Γ p) below)
  rw [Products.fresh_instantiation, Products.fresh_instantiation] at step
  exact step

variable (facts : FormFacts S.R S.roles)

include facts in
/-- **One side of the join, one binder**: a function whose opening is the η-expansion of `h'` is the η-expansion of
`λ x. h'`. -/
theorem eta_join_side {n : Nat} {F J : Ctx Head n} (nJ : CtxNarrows S.R J F) (formedF : CtxFormed S.R F)
    {pF pJ c cJ : Head} {psF psJ : List Head} (below : S.R.cumulative pF pJ)
    (rest : List.Forall₂ S.R.cumulative psF psJ) (univF : AllUniverses S.R (pF :: psF))
    (univJ : AllUniverses S.R (pJ :: psJ)) (hc : S.R.isUniverse c) (hcJ : S.R.isUniverse cJ)
    (codomain : S.R.cumulative cJ c) {f : Tm Head n} {h' : Tm Head (n + 1)}
    (tf : Typed S.R F f (famCode (pF :: psF) c)) (th : Typed S.R J (.lam h') (famCode (pJ :: psJ) cJ))
    (inner : Equal S.R (.snoc F (.head pF)) (.app (Presentation.rename wk f) (.var 0)) (etaExp psF.length h')
      (famCode psF c)) :
    Equal S.R F f (etaExp (pF :: psF).length (.lam h')) (famCode (pF :: psF) c) := by
  have formedF' : CtxFormed S.R (.snoc F (.head pF)) := formedF.snoc (IsType.head_of_universe univF.head)
  have thF : Typed S.R F (.lam h') (famCode (pJ :: psJ) cJ) := typed_narrow nJ th
  have tEta := raisedK_typed (.cons below rest) univF hc codomain formedF thF
  have thPi : Typed S.R F (.lam h') (.pi (.head pJ) (famCode psJ cJ)) := thF
  have thBody : Typed S.R (.snoc F (.head pJ)) h' (famCode psJ cJ) := Typed.lam_inv facts thPi formedF
  obtain ⟨uJ, huJ, tPiJ⟩ := famCode_isType (pJ :: psJ) univJ hcJ formedF
  have tPiJ' : Typed S.R F (.pi (.head pJ) (famCode psJ cJ)) (.head uJ) := tPiJ
  have betaJ := beta_open_below tPiJ' huJ thBody below
  have congr := etaExpK_congr rest univF.tail hc codomain formedF' betaJ
  obtain ⟨uF, huF, tPiF⟩ := famCode_isType (pF :: psF) univF hc formedF
  have tPiF' : Typed S.R F (.pi (.head pF) (famCode psF c)) (.head uF) := tPiF
  have bodyTyped := raisedK_typed rest univF.tail hc codomain formedF' (openK_typed thF below)
  have betaF := beta_open tPiF' huF bodyTyped
  exact Derivable.etaPi tf tEta (inner.trans (congr.symm.trans betaF.symm))

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')

include facts roots heads algebra rigid complete headsTyped in
/-- **The join of two bodies**: types of `U_c` over two telescopes, equal over a common narrowing, are equal to one
type of `U_c` over their join: the η-long normal form. -/
theorem join_body {n : Nat} {A F G J : Ctx Head n} (nF : CtxNarrows S.R F A) (nG : CtxNarrows S.R G A)
    (j : JoinOf S.R F G J) (formedA : CtxFormed S.R A) (formedF : CtxFormed S.R F) (formedG : CtxFormed S.R G)
    (formedJ : CtxFormed S.R J) {f g : Tm Head n} {c q : Head} (hc : S.R.isUniverse c) (hq : S.R.isUniverse q)
    (cq : S.R.cumulative c q) (tf : Typed S.R F f (.head c)) (tg : Typed S.R G g (.head c))
    (equal : Equal S.R A f g (.head q)) :
    ∃ Z, Typed S.R J Z (.head c) ∧ Equal S.R F f Z (.head c) ∧ Equal S.R G g Z (.head c) := by
  obtain ⟨Zf, lZf, atZf⟩ := long_type_exists facts roots heads algebra rigid complete formedF ⟨c, hc, tf⟩
  obtain ⟨tZf, eZf⟩ := atZf hc tf
  obtain ⟨Zg, lZg, atZg⟩ := long_type_exists facts roots heads algebra rigid complete formedG ⟨c, hc, tg⟩
  obtain ⟨tZg, eZg⟩ := atZg hc tg
  have lZfA := Long.type_narrow facts lZf nF formedF formedA
  have lZgA := Long.type_narrow facts lZg nG formedG formedA
  have eA : TypeEq S.R A Zg Zf :=
    ⟨q, hq, (Derivable.cumulEq (equal_narrow nG eZg) cq).symm.trans
      (equal.symm.trans (Derivable.cumulEq (equal_narrow nF eZf) cq))⟩
  have same := long_type_unique facts roots heads algebra complete formedA lZgA lZfA eA
  have eG : Equal S.R G Zg Zf (.head c) := Long.sameEqual facts heads lZg formedG same hc tZg
  have tZfG : Typed S.R G Zf (.head c) := (Equal.typed eG formedG).2
  have tJ := typed_join facts roots heads algebra rigid complete headsTyped j formedF formedG formedJ
    (long_type_normal rigid lZf) tZf tZfG (IsType.head_of_universe hc)
  exact ⟨Zf, tJ, eZf, eZg.trans eG⟩

include facts roots heads algebra rigid complete headsTyped in
/-- **What the join forces, under the binders**: two families of the same codomain over two telescopes whose
η-expansions are equal at an annotation over a common narrowing are the η-expansions of one family of the join, over
the join of the telescopes. -/
theorem joinK_open : ∀ {ps psF : List Head}, List.Forall₂ S.R.cumulative ps psF →
    ∀ {psG : List Head}, List.Forall₂ S.R.cumulative ps psG → ∀ {psJ : List Head}, JoinsK S.R psF psG psJ →
    ∀ {n : Nat} {A F G J : Ctx Head n}, CtxNarrows S.R F A → CtxNarrows S.R G A → JoinOf S.R F G J →
      CtxFormed S.R A → CtxFormed S.R F → CtxFormed S.R G → CtxFormed S.R J →
      ∀ {f g : Tm Head n} {c q : Head}, AllUniverses S.R ps → AllUniverses S.R psF → AllUniverses S.R psG →
      S.R.isUniverse c → S.R.isUniverse q → S.R.cumulative c q →
      Typed S.R F f (famCode psF c) → Typed S.R G g (famCode psG c) →
      Equal S.R A (etaExp ps.length f) (etaExp ps.length g) (famCode ps q) →
      ∃ h, Typed S.R J h (famCode psJ c) ∧ Equal S.R F f (etaExp psF.length h) (famCode psF c) ∧
        Equal S.R G g (etaExp psG.length h) (famCode psG c) := by
  intro ps psF annF
  induction annF with
  | nil =>
      intro psG annG psJ joins n A F G J nF nG j formedA formedF formedG formedJ f g c q _ _ _ hc hq cq tf tg equal
      cases annG
      cases joins
      exact join_body facts roots heads algebra rigid complete headsTyped nF nG j formedA formedF formedG formedJ hc hq
        cq tf tg equal
  | @cons p pF ps' psF' belowF restF ih =>
      intro psG annG psJ joins n A F G J nF nG j formedA formedF formedG formedJ f g c q univ univF univG hc hq cq
        tf tg equal
      cases annG with
      | @cons _ pG _ psG' belowG restG =>
          cases joins with
          | @cons _ _ pJ _ _ psJ' hpJ lub restJ =>
              have hp := univ.head
              have hpF := univF.head
              have hpG := univG.head
              have univJ : AllUniverses S.R (pJ :: psJ') := JoinsK.universes (.cons hpJ lub restJ)
              have formedA' : CtxFormed S.R (.snoc A (.head p)) := formedA.snoc (IsType.head_of_universe hp)
              have formedF' : CtxFormed S.R (.snoc F (.head pF)) := formedF.snoc (IsType.head_of_universe hpF)
              have formedG' : CtxFormed S.R (.snoc G (.head pG)) := formedG.snoc (IsType.head_of_universe hpG)
              have formedJ' : CtxFormed S.R (.snoc J (.head pJ)) := formedJ.snoc (IsType.head_of_universe hpJ)
              change Equal S.R A (.lam (etaExp ps'.length (.app (Presentation.rename wk f) (.var 0))))
                (.lam (etaExp ps'.length (.app (Presentation.rename wk g) (.var 0)))) (.pi (.head p) (famCode ps' q))
                at equal
              -- Open the equation at `x : U_p` over the annotation's telescope.
              have opened := equal_of_lam_left facts formedA equal
              have tgA : Typed S.R A g (famCode (pG :: psG') c) := typed_narrow nG tg
              have gBody := raisedK_typed restG univ.tail hq cq formedA' (openK_typed tgA belowG)
              obtain ⟨uP, huP, tPiP⟩ := famCode_isType (p :: ps') univ hq formedA
              have tPiP' : Typed S.R A (.pi (.head p) (famCode ps' q)) (.head uP) := tPiP
              have narrowEq := opened.trans (beta_open tPiP' huP gBody)
              -- The induction, over the four telescopes extended by their binders.
              obtain ⟨h', th', eF', eG'⟩ := ih restG restJ (.lower nF belowF) (.lower nG belowG)
                (.join j hpF hpG hpJ lub) formedA' formedF' formedG' formedJ' univ.tail univF.tail univG.tail hc hq
                cq (openK_typed tf (S.levels.cumulative_refl hpF)) (openK_typed tg (S.levels.cumulative_refl hpG))
                narrowEq
              -- The family of the join, `λ x. h'`.
              obtain ⟨uJ, huJ, tPiJ⟩ := famCode_isType (pJ :: psJ') univJ hc formedJ
              have tPiJ' : Typed S.R J (.pi (.head pJ) (famCode psJ' c)) (.head uJ) := tPiJ
              have th : Typed S.R J (.lam h') (famCode (pJ :: psJ') c) := Derivable.lamIntro tPiJ' huJ th'
              refine ⟨.lam h', th, ?_, ?_⟩
              · exact eta_join_side facts j.narrows_left formedF lub.1 restJ.left univF univJ hc hc
                  (S.levels.cumulative_refl hc) tf th eF'
              · exact eta_join_side facts j.narrows_right formedG lub.2.1 restJ.right univG univJ hc hc
                  (S.levels.cumulative_refl hc) tg th eG'

include facts roots heads algebra rigid complete headsTyped in
/-- **What the join forces at a flex–flex equation**: over `F : Π (x̄ : U_{p̄F}). U_c` and `G : Π (x̄ : U_{p̄G}). U_c`,
every solution sends `F` and `G` to the η-expansions of one family of `Π (x̄ : U_{p̄F ⊔ p̄G}). U_c`. The domains need
not be comparable. -/
theorem joinK_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (same : v.cl = v.cr)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) (f : Δ ⟶ Θ) (solved : (frames S.levels).Solves f e) :
    ∃ h, Typed S.R Δ.raw h (famCode psJ v.cr) ∧
      Equal S.R Δ.raw (f.substitution v.left) (etaExp v.psl.length h) (famCode v.psl v.cl) ∧
      Equal S.R Δ.raw (f.substitution v.right) (etaExp v.psr.length h) (famCode v.psr v.cr) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
    (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at equal
  rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst] at equal
  have tF : Typed S.R Δ.raw (f.substitution v.left) (famCode v.psl v.cr) := by
    have typed := f.typed v.left
    rw [v.declared_left, famCode_subst, same] at typed
    exact typed
  have tG : Typed S.R Δ.raw (f.substitution v.right) (famCode v.psr v.cr) := by
    have typed := f.typed v.right
    rw [v.declared_right, famCode_subst] at typed
    exact typed
  obtain ⟨h, th, eF, eG⟩ := joinK_open facts roots heads algebra rigid complete headsTyped v.domain_left v.domain_right
    joins (CtxNarrows.refl Δ.raw) (CtxNarrows.refl Δ.raw) (JoinOf.refl S.R Δ.raw) Δ.formed Δ.formed Δ.formed
    Δ.formed v.universes v.universes_left v.universes_right v.universe_cr v.universe_q v.codomain_right tF tG equal
  refine ⟨h, th, ?_, eG⟩
  rw [same]
  exact eF

end Forcing

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
