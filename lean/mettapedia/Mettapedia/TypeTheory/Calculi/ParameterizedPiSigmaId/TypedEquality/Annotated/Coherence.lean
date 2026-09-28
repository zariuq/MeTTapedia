import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Inversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Measure

/-!
# Coherence of annotations

**Coherence** (`coherence`): two annotated terms with one erasure, typed at one
type in one formed context, are equal at that type. Equivalently, typed at two
types one of which is usable at the other, they are equal at the larger one
(`coherence_below`); typed at equal types, they are equal (`coherence_typeEq`).

It is proved from two facts about the annotated calculus, bundled in
`CoherenceFacts`, and from the universe laws of the rule package (a level model
and the cumulativity algebra):

* **normalization**: the erasure of a typed term of a formed context is
  strongly normalizing for the rule package's directed reduction. For a rule
  package whose typed terms are strongly normalizing, this holds through the
  erasure of derivations (`CoherenceFacts.normalizing_of_sn`);
* **injectivity and no-confusion of the type formers** (`CFormerFacts`).

Subject reduction of the head steps it uses is derived from these
(`CWhStep.equal`).

The proof is a well-founded induction on the order of head reducts and immediate
subterms (`CSmaller`), which never enters a domain:

* a term with a β-redex or a projection of a pair at its head is equal to its
  head reduct, and the other term takes the corresponding step (`CWhStep.lockstep`);
* an elimination of a variable or a constant has a principal type determined by
  its head, the variable's type in the context or the constant's declared type;
  the two terms are compared argument by argument, each argument at the
  parameter type the principal type gives. Declared constants that compute
  (definitions, recursors, the identity eliminator) are compared this way: their
  root steps are never taken;
* an abstraction is compared through the dependent function type the common
  type is equal to: both domains are equal to its domain, and the bodies are
  compared at its codomain;
* pairs are compared componentwise at the dependent pair type the common type
  is equal to; reflexivity proofs through the identity type, whose injectivity
  gives the equality of the two points directly;
* type formers are compared at the universe the common type is equal to, into
  which both terms' components are raised by cumulativity;
* stuck terms are not typed (`CStuck.not_typed`).

Neither η-rule is used: coherence holds because annotations are compared only
where a type determines them, and the only places where no type determines them
are head redexes, which are contracted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (LevelModel HeadSame CumulativeAlgebra)
open StrongNormalization (SN)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {R : Rules Head}

/-! ## The facts -/

/-- **The facts coherence is proved from**: injectivity and no-confusion of the
type formers of the annotated calculus, and normalization of the erasures of
its typed terms. -/
structure CoherenceFacts (P : ChurchRules R) : Prop extends CFormerFacts P where
  normalizing : ∀ {n : Nat} {Γ : CCtx Head n} {t A : CTm Head n}, CCtxFormed P Γ →
    CTyped P Γ t A → SN R t.erase

/-- A formed annotated context erases to a formed context. -/
theorem CCtxFormed.erase {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n}
    (formed : CCtxFormed P Γ) : Normalization.CtxFormed R Γ.erase := by
  induction formed with
  | nil => exact .nil
  | snoc _ type ih =>
      obtain ⟨u, hu, t⟩ := type
      exact .snoc ih ⟨u, hu, CDerivable.erase t⟩

/-- Normalization of the annotated calculus follows from strong normalization of
the rule package's typed terms, through erasure. -/
theorem CoherenceFacts.normalizing_of_sn {P : ChurchRules R}
    (sn : ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, Normalization.CtxFormed R Γ →
      Typed R Γ t A → SN R t)
    {n : Nat} {Γ : CCtx Head n} {t A : CTm Head n} (formed : CCtxFormed P Γ)
    (typing : CTyped P Γ t A) : SN R t.erase :=
  sn formed.erase (CDerivable.erase typing)

/-- The facts, from the facts about the formers and strong normalization of the
rule package. -/
theorem CoherenceFacts.ofSN {P : ChurchRules R} (formers : CFormerFacts P)
    (sn : ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, Normalization.CtxFormed R Γ →
      Typed R Γ t A → SN R t) : CoherenceFacts P :=
  { formers with normalizing := CoherenceFacts.normalizing_of_sn sn }

/-! ## The statements proved by induction -/

/-- Two terms equal at a common type that is usable at every type of either. -/
def PrincipalEq (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (s s' : CTm Head n) : Prop :=
  ∃ S, CTyped P Γ s S ∧ CTyped P Γ s' S ∧ CEqual P Γ s s' S ∧
    (∀ T, CTyped P Γ s T → CBelow P Γ S T) ∧ (∀ T, CTyped P Γ s' T → CBelow P Γ S T)

/-- Coherence at a term. -/
def CoherentAt (P : ChurchRules R) (x : Σ n, CTm Head n) : Prop :=
  ∀ {Γ : CCtx Head x.1} {t' A : CTm Head x.1}, CCtxFormed P Γ → CTyped P Γ x.2 A →
    CTyped P Γ t' A → x.2.erase = t'.erase → CEqual P Γ x.2 t' A

/-- Coherence at a spine, with a principal type. -/
def SpineCoherentAt (P : ChurchRules R) (x : Σ n, CTm Head n) : Prop :=
  CSpine x.2 → ∀ {Γ : CCtx Head x.1} {t' T T' : CTm Head x.1}, CCtxFormed P Γ →
    CTyped P Γ x.2 T → CTyped P Γ t' T' → x.2.erase = t'.erase → PrincipalEq P Γ x.2 t'

section Proof

variable {P : ChurchRules R} (facts : CoherenceFacts P) (levels : LevelModel R L)
  (algebra : CumulativeAlgebra R)
include facts levels algebra

omit algebra in
/-- Coherence at a spine, from coherence at its immediate subterms. -/
private theorem spine_step {n : Nat} {t : CTm Head n}
    (sub : ∀ {m : Nat} {s : CTm Head m}, CImmSub ⟨m, s⟩ ⟨n, t⟩ →
      CoherentAt P ⟨m, s⟩ ∧ SpineCoherentAt P ⟨m, s⟩) :
    SpineCoherentAt P ⟨n, t⟩ := by
  have former := facts.toCFormerFacts
  intro hs Γ t' T T' formed typing typing' same
  dsimp only at hs Γ t' T T' formed typing typing' same
  cases hs with
  | var i =>
      have e := CTm.erase_eq_var same.symm
      subst e
      refine ⟨Γ.lookup i, .var i, .var i, .refl (.var i), ?_, ?_⟩ <;>
        exact fun T₂ typing₂ =>
          CTypeLe.toBelow typing₂.generation (CTyped.isType levels typing₂ formed)
  | const c =>
      have e := CTm.erase_eq_const same.symm
      subst e
      obtain ⟨type, u, declared, tType, hu, _⟩ := typing.generation
      have tc : CTyped P Γ (.const c) type.liftClosed := .const declared tType hu
      have principal : ∀ T₂, CTyped P Γ (.const c) T₂ → CBelow P Γ type.liftClosed T₂ := by
        intro T₂ typing₂
        obtain ⟨type₂, _, declared₂, _, _, le₂⟩ := typing₂.generation
        rw [declared] at declared₂
        cases declared₂
        exact CTypeLe.toBelow le₂ (CTyped.isType levels typing₂ formed)
      exact ⟨_, tc, tc, .refl tc, principal, principal⟩
  | @app f a hf =>
      obtain ⟨f', a', rfl, ef, ea⟩ := CTm.erase_eq_app same.symm
      obtain ⟨A, B, tf, ta, _⟩ := typing.generation
      obtain ⟨A', B', tf', ta', _⟩ := typing'.generation
      obtain ⟨S, tS, tS', eS, prin, prin'⟩ := (sub (.appFun f a)).2 hf formed tf tf' ef.symm
      obtain ⟨B₀, C₀, eS₀, eB₀, _⟩ := CBelow.pi_inv former levels (prin _ tf) formed
        (CIsType.refl (CTyped.isType levels tf formed))
      obtain ⟨eB₀', _⟩ := CBelow.pi_parts former levels (.subTrans eS₀.symm.below (prin' _ tf'))
        formed
      have ta₀ : CTyped P Γ a B₀ := CTyped.convType ta eB₀.symm
      have ta₀' : CTyped P Γ a' B₀ := CTyped.convType ta' eB₀'.symm
      have ea₀ : CEqual P Γ a a' B₀ := (sub (.appArg f a)).1 formed ta₀ ta₀' ea.symm
      obtain ⟨_, familyC₀⟩ := CIsType.pi_parts (CTypeEq.isType levels eS₀ formed).2
      have eC : CTypeEq P Γ (CTm.inst0 a C₀) (CTm.inst0 a' C₀) :=
        CIsType.instantiateEq familyC₀ ta₀ ea₀
      refine ⟨CTm.inst0 a C₀, .appElim (CTyped.convType tS eS₀) ta₀,
        CTyped.convType (.appElim (CTyped.convType tS' eS₀) ta₀') eC.symm,
        .appCong (CEqual.convType eS eS₀) ea₀, ?_, ?_⟩
      · intro T₂ typing₂
        obtain ⟨A₂, B₂, tf₂, _, le₂⟩ := typing₂.generation
        obtain ⟨_, leC₂⟩ := CBelow.pi_parts former levels
          (.subTrans eS₀.symm.below (prin _ tf₂)) formed
        exact .subTrans (CBelow.instantiate leC₂ ta₀)
          (CTypeLe.toBelow le₂ (CTyped.isType levels typing₂ formed))
      · intro T₂ typing₂
        obtain ⟨A₂, B₂, tf₂, _, le₂⟩ := typing₂.generation
        obtain ⟨_, leC₂⟩ := CBelow.pi_parts former levels
          (.subTrans eS₀.symm.below (prin' _ tf₂)) formed
        exact .subTrans eC.below (.subTrans (CBelow.instantiate leC₂ ta₀')
          (CTypeLe.toBelow le₂ (CTyped.isType levels typing₂ formed)))
  | @fst p hp =>
      obtain ⟨p', rfl, ep⟩ := CTm.erase_eq_fst same.symm
      obtain ⟨A, B, tp, _⟩ := typing.generation
      obtain ⟨A', B', tp', _⟩ := typing'.generation
      obtain ⟨S, tS, tS', eS, prin, prin'⟩ := (sub (.fst p)).2 hp formed tp tp' ep.symm
      obtain ⟨B₀, C₀, eS₀, _, _⟩ := CBelow.sigma_inv former levels (prin _ tp) formed
        (CIsType.refl (CTyped.isType levels tp formed))
      refine ⟨B₀, .fstElim (CTyped.convType tS eS₀), .fstElim (CTyped.convType tS' eS₀),
        .fstCong (CEqual.convType eS eS₀), ?_, ?_⟩
      · intro T₂ typing₂
        obtain ⟨A₂, B₂, tp₂, le₂⟩ := typing₂.generation
        obtain ⟨leB, _⟩ := CBelow.sigma_parts former levels
          (.subTrans eS₀.symm.below (prin _ tp₂)) formed
        exact .subTrans leB (CTypeLe.toBelow le₂ (CTyped.isType levels typing₂ formed))
      · intro T₂ typing₂
        obtain ⟨A₂, B₂, tp₂, le₂⟩ := typing₂.generation
        obtain ⟨leB, _⟩ := CBelow.sigma_parts former levels
          (.subTrans eS₀.symm.below (prin' _ tp₂)) formed
        exact .subTrans leB (CTypeLe.toBelow le₂ (CTyped.isType levels typing₂ formed))
  | @snd p hp =>
      obtain ⟨p', rfl, ep⟩ := CTm.erase_eq_snd same.symm
      obtain ⟨A, B, tp, _⟩ := typing.generation
      obtain ⟨A', B', tp', _⟩ := typing'.generation
      obtain ⟨S, tS, tS', eS, prin, prin'⟩ := (sub (.snd p)).2 hp formed tp tp' ep.symm
      obtain ⟨B₀, C₀, eS₀, _, _⟩ := CBelow.sigma_inv former levels (prin _ tp) formed
        (CIsType.refl (CTyped.isType levels tp formed))
      have tp₀ : CTyped P Γ p (.sigma B₀ C₀) := CTyped.convType tS eS₀
      have tp₀' : CTyped P Γ p' (.sigma B₀ C₀) := CTyped.convType tS' eS₀
      have ep₀ : CEqual P Γ p p' (.sigma B₀ C₀) := CEqual.convType eS eS₀
      obtain ⟨_, familyC₀⟩ := CIsType.sigma_parts (CTypeEq.isType levels eS₀ formed).2
      have eC : CTypeEq P Γ (CTm.inst0 (.fst p) C₀) (CTm.inst0 (.fst p') C₀) :=
        CIsType.instantiateEq familyC₀ (.fstElim tp₀) (.fstCong ep₀)
      refine ⟨CTm.inst0 (.fst p) C₀, .sndElim tp₀, CTyped.convType (.sndElim tp₀') eC.symm,
        .sndCong ep₀, ?_, ?_⟩
      · intro T₂ typing₂
        obtain ⟨A₂, B₂, tp₂, le₂⟩ := typing₂.generation
        obtain ⟨_, leC⟩ := CBelow.sigma_parts former levels
          (.subTrans eS₀.symm.below (prin _ tp₂)) formed
        exact .subTrans (CBelow.instantiate leC (.fstElim tp₀))
          (CTypeLe.toBelow le₂ (CTyped.isType levels typing₂ formed))
      · intro T₂ typing₂
        obtain ⟨A₂, B₂, tp₂, le₂⟩ := typing₂.generation
        obtain ⟨_, leC⟩ := CBelow.sigma_parts former levels
          (.subTrans eS₀.symm.below (prin' _ tp₂)) formed
        exact .subTrans eC.below (.subTrans (CBelow.instantiate leC (.fstElim tp₀'))
          (CTypeLe.toBelow le₂ (CTyped.isType levels typing₂ formed)))

/-- Coherence at an introduction or a type former, from coherence at its
immediate subterms. -/
private theorem intro_step {n : Nat} {t : CTm Head n}
    (sub : ∀ {m : Nat} {s : CTm Head m}, CImmSub ⟨m, s⟩ ⟨n, t⟩ →
      CoherentAt P ⟨m, s⟩ ∧ SpineCoherentAt P ⟨m, s⟩)
    (intro : CIntro t) : CoherentAt P ⟨n, t⟩ := by
  have former := facts.toCFormerFacts
  intro Γ t' A formed typing typing' same
  dsimp only at Γ t' A formed typing typing' same
  have typeA := CTyped.isType levels typing formed
  cases intro with
  | head h =>
      have e := CTm.erase_eq_head same.symm
      subst e
      exact .refl typing
  | pi D E =>
      obtain ⟨D', E', rfl, eD, eE⟩ := CTm.erase_eq_pi same.symm
      obtain ⟨u, v, w, tD, hu, tE, hv, join, le⟩ := typing.generation
      obtain ⟨u', v', w', tD', hu', tE', hv', join', le'⟩ := typing'.generation
      have hw := (levels.join_level join).1
      have hw' := (levels.join_level join').1
      obtain ⟨i, hi, eAi, cwi⟩ := CBelow.universe_cumulative former levels algebra
        (CTypeLe.toBelow le typeA) formed hw (CIsType.refl (CIsType.head_of_universe levels hw))
      obtain ⟨i', _, eAi', cwi'⟩ := CBelow.universe_cumulative former levels algebra
        (CTypeLe.toBelow le' typeA) formed hw' (CIsType.refl (CIsType.head_of_universe levels hw'))
      have cw'i : R.cumulative w' i := algebra.same_right cwi'
        (CTypeEq.head_injective former (CTypeEq.trans levels eAi'.symm eAi) formed)
      have tDi : CTyped P Γ D (.head i) :=
        CDerivable.cumul tD (algebra.trans (levels.join_upper join).1 cwi)
      have tDi' : CTyped P Γ D' (.head i) :=
        CDerivable.cumul tD' (algebra.trans (levels.join_upper join').1 cw'i)
      have eDD : CEqual P Γ D D' (.head i) := (sub (.piDom D E)).1 formed tDi tDi' eD.symm
      have tEi : CTyped P (.snoc Γ D) E (.head i) :=
        CDerivable.cumul tE (algebra.trans (levels.join_upper join).2 cwi)
      have tEi' : CTyped P (.snoc Γ D) E' (.head i) :=
        CTyped.ctxConv (CDerivable.cumul tE' (algebra.trans (levels.join_upper join').2 cw'i))
          ⟨i, hi, .symm eDD⟩
      have eEE : CEqual P (.snoc Γ D) E E' (.head i) :=
        (sub (.piCod D E)).1 (.snoc formed ⟨u, hu, tD⟩) tEi tEi' eE.symm
      obtain ⟨j, joinJ⟩ := levels.join_exists hi hi
      have cji : R.cumulative j i :=
        algebra.join_least joinJ (levels.cumulative_refl hi) (levels.cumulative_refl hi)
      exact CEqual.convType (CDerivable.cumulEq (.piCong eDD hi eEE hi joinJ) cji) eAi.symm
  | sigma D E =>
      obtain ⟨D', E', rfl, eD, eE⟩ := CTm.erase_eq_sigma same.symm
      obtain ⟨u, v, w, tD, hu, tE, hv, join, le⟩ := typing.generation
      obtain ⟨u', v', w', tD', hu', tE', hv', join', le'⟩ := typing'.generation
      have hw := (levels.join_level join).1
      have hw' := (levels.join_level join').1
      obtain ⟨i, hi, eAi, cwi⟩ := CBelow.universe_cumulative former levels algebra
        (CTypeLe.toBelow le typeA) formed hw (CIsType.refl (CIsType.head_of_universe levels hw))
      obtain ⟨i', _, eAi', cwi'⟩ := CBelow.universe_cumulative former levels algebra
        (CTypeLe.toBelow le' typeA) formed hw' (CIsType.refl (CIsType.head_of_universe levels hw'))
      have cw'i : R.cumulative w' i := algebra.same_right cwi'
        (CTypeEq.head_injective former (CTypeEq.trans levels eAi'.symm eAi) formed)
      have tDi : CTyped P Γ D (.head i) :=
        CDerivable.cumul tD (algebra.trans (levels.join_upper join).1 cwi)
      have tDi' : CTyped P Γ D' (.head i) :=
        CDerivable.cumul tD' (algebra.trans (levels.join_upper join').1 cw'i)
      have eDD : CEqual P Γ D D' (.head i) := (sub (.sigmaDom D E)).1 formed tDi tDi' eD.symm
      have tEi : CTyped P (.snoc Γ D) E (.head i) :=
        CDerivable.cumul tE (algebra.trans (levels.join_upper join).2 cwi)
      have tEi' : CTyped P (.snoc Γ D) E' (.head i) :=
        CTyped.ctxConv (CDerivable.cumul tE' (algebra.trans (levels.join_upper join').2 cw'i))
          ⟨i, hi, .symm eDD⟩
      have eEE : CEqual P (.snoc Γ D) E E' (.head i) :=
        (sub (.sigmaCod D E)).1 (.snoc formed ⟨u, hu, tD⟩) tEi tEi' eE.symm
      obtain ⟨j, joinJ⟩ := levels.join_exists hi hi
      have cji : R.cumulative j i :=
        algebra.join_least joinJ (levels.cumulative_refl hi) (levels.cumulative_refl hi)
      exact CEqual.convType (CDerivable.cumulEq (.sigmaCong eDD hi eEE hi joinJ) cji) eAi.symm
  | id C x y =>
      obtain ⟨C', x', y', rfl, eC, ex, ey⟩ := CTm.erase_eq_id same.symm
      obtain ⟨u, tC, hu, tx, ty, le⟩ := typing.generation
      obtain ⟨u', tC', hu', tx', ty', le'⟩ := typing'.generation
      obtain ⟨i, hi, eAi, cui⟩ := CBelow.universe_cumulative former levels algebra
        (CTypeLe.toBelow le typeA) formed hu (CIsType.refl (CIsType.head_of_universe levels hu))
      obtain ⟨i', _, eAi', cui'⟩ := CBelow.universe_cumulative former levels algebra
        (CTypeLe.toBelow le' typeA) formed hu' (CIsType.refl (CIsType.head_of_universe levels hu'))
      have cu'i : R.cumulative u' i := algebra.same_right cui'
        (CTypeEq.head_injective former (CTypeEq.trans levels eAi'.symm eAi) formed)
      have eCC : CEqual P Γ C C' (.head i) :=
        (sub (.idType C x y)).1 formed (CDerivable.cumul tC cui) (CDerivable.cumul tC' cu'i) eC.symm
      have exx : CEqual P Γ x x' C :=
        (sub (.idLeft C x y)).1 formed tx (.conv tx' (.symm eCC) hi) ex.symm
      have eyy : CEqual P Γ y y' C :=
        (sub (.idRight C x y)).1 formed ty (.conv ty' (.symm eCC) hi) ey.symm
      exact CEqual.convType (.idCong eCC hi exx eyy) eAi.symm
  | lam D b =>
      obtain ⟨D', b', rfl, eb⟩ := CTm.erase_eq_lam same.symm
      obtain ⟨E, u, w, tD, hw, tPi, hu, tb, le⟩ := typing.generation
      obtain ⟨E', u', w', _, _, tPi', hu', tb', le'⟩ := typing'.generation
      obtain ⟨B, C, eA, eDB, leEC⟩ := CBelow.pi_source former levels (CTypeLe.toBelow le typeA)
        formed (CIsType.refl ⟨u, hu, tPi⟩)
      obtain ⟨B', C', eA', eDB', leEC'⟩ := CBelow.pi_source former levels
        (CTypeLe.toBelow le' typeA) formed (CIsType.refl ⟨u', hu', tPi'⟩)
      obtain ⟨eBB', eCC'⟩ :=
        CTypeEq.pi_injective former (CTypeEq.trans levels eA.symm eA') formed
      have eD'B : CTypeEq P Γ D' B := CTypeEq.trans levels eDB' eBB'.symm
      have tbC : CTyped P (.snoc Γ B) b C := CTyped.ctxConv (.sub tb leEC) eDB
      have tbC' : CTyped P (.snoc Γ B) b' C :=
        CTyped.convType (CTyped.ctxConv (.sub tb' leEC') eD'B) eCC'.symm
      have formedB : CCtxFormed P (.snoc Γ B) :=
        .snoc formed (CTypeEq.isType levels eDB formed).2
      have ebb : CEqual P (.snoc Γ B) b b' C := (sub (.lamBody D b)).1 formedB tbC tbC' eb.symm
      obtain ⟨z, hz, eDD'⟩ := CTypeEq.trans levels eDB eD'B.symm
      obtain ⟨_, typeC⟩ := CIsType.pi_parts (CTypeEq.isType levels eA formed).2
      obtain ⟨v, hv, tC⟩ := typeC
      have tCD : CTyped P (.snoc Γ D) C (.head v) := CTyped.ctxConv tC eDB.symm
      obtain ⟨j, joinJ⟩ := levels.join_exists hw hv
      have e₀ : CEqual P Γ (.lam D b) (.lam D' b') (.pi D C) :=
        .lamCong eDD' hz (.piForm tD hw tCD hv joinJ) (levels.join_level joinJ).1
          (CEqual.ctxConv ebb eDB.symm)
      obtain ⟨y, hy, eDBy⟩ := id eDB
      obtain ⟨k, joinK⟩ := levels.join_exists hy hv
      have ePi : CTypeEq P Γ (.pi D C) A :=
        CTypeEq.trans levels ⟨k, (levels.join_level joinK).1, .piCong eDBy hy (.refl tCD) hv joinK⟩
          eA.symm
      exact CEqual.convType e₀ ePi
  | pair a b =>
      obtain ⟨a', b', rfl, ea, eb⟩ := CTm.erase_eq_pair same.symm
      obtain ⟨D, E, u, tS, hu, ta, tb, le⟩ := typing.generation
      obtain ⟨D', E', u', tS', hu', ta', tb', le'⟩ := typing'.generation
      obtain ⟨B, C, eA, leDB, leEC⟩ := CBelow.sigma_source former levels
        (CTypeLe.toBelow le typeA) formed (CIsType.refl ⟨u, hu, tS⟩)
      obtain ⟨B', C', eA', leDB', leEC'⟩ := CBelow.sigma_source former levels
        (CTypeLe.toBelow le' typeA) formed (CIsType.refl ⟨u', hu', tS'⟩)
      obtain ⟨eBB', eCC'⟩ :=
        CTypeEq.sigma_injective former (CTypeEq.trans levels eA.symm eA') formed
      have taB : CTyped P Γ a B := .sub ta leDB
      have taB' : CTyped P Γ a' B := CTyped.convType (.sub ta' leDB') eBB'.symm
      have eaa : CEqual P Γ a a' B := (sub (.pairFst a b)).1 formed taB taB' ea.symm
      have typeSigma := (CTypeEq.isType levels eA formed).2
      obtain ⟨_, familyC⟩ := CIsType.sigma_parts typeSigma
      have tbC : CTyped P Γ b (CTm.inst0 a C) := .sub tb (CBelow.instantiate leEC ta)
      have tbC' : CTyped P Γ b' (CTm.inst0 a C) :=
        CTyped.convType (CTyped.convType (.sub tb' (CBelow.instantiate leEC' ta'))
          (CTypeEq.instantiate eCC'.symm taB')) (CIsType.instantiateEq familyC taB eaa).symm
      have ebb : CEqual P Γ b b' (CTm.inst0 a C) := (sub (.pairSnd a b)).1 formed tbC tbC' eb.symm
      obtain ⟨z, hz, tSBC⟩ := typeSigma
      exact CEqual.convType (.pairCong tSBC hz eaa ebb) eA.symm
  | refl a =>
      obtain ⟨a', rfl, _⟩ := CTm.erase_eq_refl same.symm
      obtain ⟨D, ta, le⟩ := typing.generation
      obtain ⟨D', ta', le'⟩ := typing'.generation
      have eId : CTypeEq P Γ A (.id D a a) := CBelow.id_eq former levels
        (CTypeLe.toBelow le typeA) formed
        (CIsType.refl (CTyped.isType levels (.reflIntro ta) formed))
      have eId' : CTypeEq P Γ A (.id D' a' a') := CBelow.id_eq former levels
        (CTypeLe.toBelow le' typeA) formed
        (CIsType.refl (CTyped.isType levels (.reflIntro ta') formed))
      obtain ⟨_, eaa, _⟩ := CTypeEq.id_injective former (CTypeEq.trans levels eId.symm eId') formed
      exact CEqual.convType (.reflCong eaa) eId.symm

/-- Coherence, and coherence with principal types at spines, at every term from
which the order of head reducts and immediate subterms is accessible. -/
theorem coherent_of_acc (x : Σ n, CTm Head n) (acc : Acc CSmaller x) :
    CoherentAt P x ∧ SpineCoherentAt P x := by
  induction acc with
  | intro x _ ih =>
      obtain ⟨n, t⟩ := x
      have sub : ∀ {m : Nat} {s : CTm Head m}, CImmSub ⟨m, s⟩ ⟨n, t⟩ →
          CoherentAt P ⟨m, s⟩ ∧ SpineCoherentAt P ⟨m, s⟩ := fun h => ih _ (.sub h)
      have spine : SpineCoherentAt P ⟨n, t⟩ := spine_step facts levels sub
      refine ⟨?_, spine⟩
      intro Γ t' A formed typing typing' same
      dsimp only at Γ t' A formed typing typing' same
      rcases CTm.classify t with ⟨u, step⟩ | hs | stuck | intro
      · obtain ⟨u', step', eu⟩ := step.lockstep same
        have e₁ := CWhStep.equal facts.toCFormerFacts levels formed step typing
        have e₂ := CWhStep.equal facts.toCFormerFacts levels formed step' typing'
        have eu' := (ih _ (.step step)).1 formed (CEqual.typed levels e₁ formed).2
          (CEqual.typed levels e₂ formed).2 eu
        exact .trans e₁ (.trans eu' (.symm e₂))
      · obtain ⟨S, _, _, eS, prin, _⟩ := spine hs formed typing typing' same
        exact .subEq eS (prin _ typing)
      · exact (CStuck.not_typed facts.toCFormerFacts levels algebra formed stuck typing).elim
      · exact intro_step facts levels algebra sub intro formed typing typing' same

end Proof

/-! ## Coherence -/

section Coherence

variable {P : ChurchRules R} (facts : CoherenceFacts P) (levels : LevelModel R L)
  (algebra : CumulativeAlgebra R)
include facts levels algebra

/-- **Coherence of annotations**: two annotated terms with one erasure, typed at
one type in one formed context, are equal at that type. -/
theorem coherence {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ) {t t' A : CTm Head n}
    (typing : CTyped P Γ t A) (typing' : CTyped P Γ t' A) (same : t.erase = t'.erase) :
    CEqual P Γ t t' A :=
  (coherent_of_acc facts levels algebra ⟨n, t⟩
    (CSmaller.acc_of_sn (R := R) (facts.normalizing formed typing))).1 formed typing typing' same

/-- Coherence at two types, the first usable at the second. -/
theorem coherence_below {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {t t' A A' : CTm Head n} (typing : CTyped P Γ t A) (typing' : CTyped P Γ t' A')
    (le : CBelow P Γ A A') (same : t.erase = t'.erase) : CEqual P Γ t t' A' :=
  coherence facts levels algebra formed (.sub typing le) typing' same

/-- Coherence at equal types. -/
theorem coherence_typeEq {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {t t' A A' : CTm Head n} (typing : CTyped P Γ t A) (typing' : CTyped P Γ t' A')
    (equal : CTypeEq P Γ A A') (same : t.erase = t'.erase) : CEqual P Γ t t' A :=
  coherence facts levels algebra formed typing (CTyped.convType typing' equal.symm) same

/-- **Principal types of spines**: two eliminations of a variable or a constant
with one erasure, each typed, are equal at a common type usable at every type of
either. -/
theorem spine_principal {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {s s' T T' : CTm Head n} (spine : CSpine s) (typing : CTyped P Γ s T)
    (typing' : CTyped P Γ s' T') (same : s.erase = s'.erase) : PrincipalEq P Γ s s' :=
  (coherent_of_acc facts levels algebra ⟨n, s⟩
    (CSmaller.acc_of_sn (R := R) (facts.normalizing formed typing))).2 spine formed typing
      typing' same

end Coherence

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
