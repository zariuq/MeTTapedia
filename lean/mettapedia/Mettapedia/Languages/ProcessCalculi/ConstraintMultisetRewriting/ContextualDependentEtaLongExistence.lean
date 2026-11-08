import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongUnique

/-!
# Every typed term has an η-long normal form

A derivation of the algorithmic equality between two terms is read back as an η-long β-normal
form typed-equal to both (`extract_of_algorithmic`). The read-back follows the comparison:

* at a dependent function type the two applications to a fresh variable have a common normal
  form `z`, and `λ. z` is the normal form of both functions, by function η and β;
* at a dependent pair type the projections have common normal forms, and their pair is the
  normal form of both, by pair η and the two projection β rules;
* at an identity type reflexivity proofs are read back at their points;
* at a universe the two types are read back as a normal type, at every universe at which both are
  typed;
* elsewhere the two spines are read back argument by argument, at the types the head assigns,
  and the result is used at the compared type through the principal type of the head.

Completeness of the algorithmic equality then gives every typed term a normal form and every
equal pair of typed terms a common one (`long_exists`, `long_common`). Constants are required to
be rigid; inductive types and computing constants are outside this fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaLong

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- A normal type `Z` of two types, at every universe at which both are typed. -/
def AtUniverses (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (A B Z : Tm Head n) : Prop :=
  ∀ {u : Head}, S.R.isUniverse u → Typed S.R Γ A (.head u) → Typed S.R Γ B (.head u) →
    Typed S.R Γ Z (.head u) ∧ Equal S.R Γ A Z (.head u) ∧ Equal S.R Γ B Z (.head u)

/-- What reading back a derivation of the algorithmic equality gives. -/
def ExtractAt (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A B => CtxFormed S.R Γ →
      ∃ Z, Long S.R S.roles (.type Γ Z) ∧ AtUniverses S Γ A B Z
  | .typesW Γ A B => CtxFormed S.R Γ →
      ∃ Z, Long S.R S.roles (.type Γ Z) ∧ AtUniverses S Γ A B Z
  | .terms Γ t u A => CtxFormed S.R Γ →
      ∃ z, Long S.R S.roles (.term Γ z A) ∧ Equal S.R Γ t z A ∧ Equal S.R Γ u z A
  | .termsW Γ t u A => CtxFormed S.R Γ →
      ∃ z, Long S.R S.roles (.term Γ z A) ∧ Equal S.R Γ t z A ∧ Equal S.R Γ u z A
  | .spines Γ t u U => CtxFormed S.R Γ →
      ∃ z, Long S.R S.roles (.spine Γ z U) ∧ Equal S.R Γ t z U ∧ Equal S.R Γ u z U
  | .spinesW Γ t u U => CtxFormed S.R Γ →
      ∃ z, Long S.R S.roles (.spine Γ z U) ∧ Equal S.R Γ t z U ∧ Equal S.R Γ u z U

/-- Applying a function to a fresh variable. -/
theorem typed_apply_fresh {n : Nat} {Γ : Ctx Head n} {f A : Tm Head n} {B : Tm Head (n + 1)}
    (tf : Typed S.R Γ f (.pi A B)) :
    Typed S.R (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0)) B := by
  have tw : Typed S.R (.snoc Γ A) (Presentation.rename wk f)
      (.pi (Presentation.rename wk A) (Presentation.rename (liftRen wk) B)) := Typed.weaken tf
  have tapp := Derivable.appElim tw (.var 0 : Typed S.R (.snoc Γ A) (.var 0) _)
  rwa [inst0_var_rename_liftRen_wk] at tapp

/-- Two types in a formed context are typed at one universe. -/
theorem common_universe {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (isA : IsType S.R Γ A)
    (isB : IsType S.R Γ B) :
    ∃ w, S.R.isUniverse w ∧ Typed S.R Γ A (.head w) ∧ Typed S.R Γ B (.head w) := by
  obtain ⟨u, hu, tA⟩ := isA
  obtain ⟨v, hv, tB⟩ := isB
  obtain ⟨w, join⟩ := S.levels.join_exists hu hv
  obtain ⟨cu, cv⟩ := S.levels.join_upper join
  exact ⟨w, (S.levels.join_level join).1, .cumul tA cu, .cumul tB cv⟩

section Extraction

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
include facts roots heads algebra rigid

omit facts roots heads rigid in
/-- The join of a universe with itself is below it. -/
theorem self_join {u : Head} (hu : S.R.isUniverse u) :
    ∃ j, S.R.join u u j ∧ S.R.cumulative j u := by
  obtain ⟨j, join⟩ := S.levels.join_exists hu hu
  exact ⟨j, join, algebra.join_least join (S.levels.cumulative_refl hu)
    (S.levels.cumulative_refl hu)⟩

/-- **Reading back a derivation of the algorithmic equality.** -/
theorem extract_of_algorithmic {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : ExtractAt S st := by
  have soundTerms := fun {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n} (formed : CtxFormed S.R Γ)
      (d : Algorithmic S.R S.roles (.terms Γ t u A)) =>
    Algorithmic.sound_terms facts roots heads algebra formed d
  have soundTypes := fun {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (formed : CtxFormed S.R Γ)
      (d : Algorithmic S.R S.roles (.types Γ A B)) =>
    Algorithmic.sound_types facts roots heads algebra formed d
  induction derivation with
  | types rA rB _ _ _ ih =>
      intro formed
      obtain ⟨Z, lZ, at'⟩ := ih formed
      refine ⟨Z, lZ, fun hu tA tB => ?_⟩
      obtain ⟨tA', eA⟩ := WhRed.preserve facts roots formed rA.red tA
      obtain ⟨tB', eB⟩ := WhRed.preserve facts roots formed rB.red tB
      obtain ⟨tZ, eAZ, eBZ⟩ := at' hu tA' tB'
      exact ⟨tZ, .trans eA eAZ, .trans eB eBZ⟩
  | @heads n Γ h h' u₀ same tA tB hu₀ =>
      intro formed
      refine ⟨.head h, .head ⟨u₀, hu₀, tA⟩, fun hu tA' tB' => ⟨tA', .refl tA', ?_⟩⟩
      exact Algorithmic.sound facts roots heads algebra
        (Algorithmic.heads (roles := S.roles) (HeadSame.symm S.levels same) tB tA hu₀)
        formed hu tB' tA'
  | @pi n Γ A₁ A₂ B₁ B₂ isA dA dB ihA ihB =>
      intro formed
      have formedA : CtxFormed S.R (.snoc Γ A₁) := .snoc formed isA
      obtain ⟨Z₁, lZ₁, at₁⟩ := ihA formed
      obtain ⟨Z₂, lZ₂, at₂⟩ := ihB formedA
      have eA₁₂ := soundTypes formed dA
      obtain ⟨isB₁, isB₂⟩ := dB.types_isType
      obtain ⟨w, hw, tA₁, tA₂⟩ := common_universe dA.types_isType.1 dA.types_isType.2
      obtain ⟨v, hv, tB₁, tB₂⟩ := common_universe isB₁ isB₂
      obtain ⟨tZ₁, eZ₁, _⟩ := at₁ hw tA₁ tA₂
      obtain ⟨tZ₂, _, _⟩ := at₂ hv tB₁ tB₂
      have eAZ : TypeEq S.R Γ A₁ Z₁ := ⟨w, hw, eZ₁⟩
      obtain ⟨there, back⟩ := ctxEq_last formed eAZ
      obtain ⟨j, join⟩ := S.levels.join_exists hw hv
      refine ⟨.pi Z₁ Z₂, .pi lZ₁ ((lZ₂.stable S.levels) there back)
        ⟨j, (S.levels.join_level join).1, .piForm tZ₁ hw (Typed.ctxConv tZ₂ eAZ) hv join⟩, ?_⟩
      intro u hu tPi₁ tPi₂
      obtain ⟨uA₁, uB₁⟩ := Typed.pi_universe facts algebra formed tPi₁
      obtain ⟨uA₂, uB₂⟩ := Typed.pi_universe facts algebra formed tPi₂
      obtain ⟨uZ₁, uA₁Z, uA₂Z⟩ := at₁ hu uA₁ uA₂
      obtain ⟨uZ₂, uB₁Z, uB₂Z⟩ := at₂ hu uB₁ (Typed.ctxConv uB₂ eA₁₂.symm)
      obtain ⟨k, joinK, below⟩ := self_join algebra hu
      refine ⟨.cumul (.piForm uZ₁ hu (Typed.ctxConv uZ₂ ⟨u, hu, uA₁Z⟩) hu joinK) below,
        .cumulEq (.piCong uA₁Z hu uB₁Z hu joinK) below,
        .cumulEq (.piCong uA₂Z hu (Equal.ctxConv uB₂Z eA₁₂) hu joinK) below⟩
  | @sigma n Γ A₁ A₂ B₁ B₂ isA dA dB ihA ihB =>
      intro formed
      have formedA : CtxFormed S.R (.snoc Γ A₁) := .snoc formed isA
      obtain ⟨Z₁, lZ₁, at₁⟩ := ihA formed
      obtain ⟨Z₂, lZ₂, at₂⟩ := ihB formedA
      have eA₁₂ := soundTypes formed dA
      obtain ⟨isB₁, isB₂⟩ := dB.types_isType
      obtain ⟨w, hw, tA₁, tA₂⟩ := common_universe dA.types_isType.1 dA.types_isType.2
      obtain ⟨v, hv, tB₁, tB₂⟩ := common_universe isB₁ isB₂
      obtain ⟨tZ₁, eZ₁, _⟩ := at₁ hw tA₁ tA₂
      obtain ⟨tZ₂, _, _⟩ := at₂ hv tB₁ tB₂
      have eAZ : TypeEq S.R Γ A₁ Z₁ := ⟨w, hw, eZ₁⟩
      obtain ⟨there, back⟩ := ctxEq_last formed eAZ
      obtain ⟨j, join⟩ := S.levels.join_exists hw hv
      refine ⟨.sigma Z₁ Z₂, .sigma lZ₁ ((lZ₂.stable S.levels) there back)
        ⟨j, (S.levels.join_level join).1, .sigmaForm tZ₁ hw (Typed.ctxConv tZ₂ eAZ) hv join⟩, ?_⟩
      intro u hu tSigma₁ tSigma₂
      obtain ⟨uA₁, uB₁⟩ := Typed.sigma_universe facts algebra formed tSigma₁
      obtain ⟨uA₂, uB₂⟩ := Typed.sigma_universe facts algebra formed tSigma₂
      obtain ⟨uZ₁, uA₁Z, uA₂Z⟩ := at₁ hu uA₁ uA₂
      obtain ⟨uZ₂, uB₁Z, uB₂Z⟩ := at₂ hu uB₁ (Typed.ctxConv uB₂ eA₁₂.symm)
      obtain ⟨k, joinK, below⟩ := self_join algebra hu
      refine ⟨.cumul (.sigmaForm uZ₁ hu (Typed.ctxConv uZ₂ ⟨u, hu, uA₁Z⟩) hu joinK) below,
        .cumulEq (.sigmaCong uA₁Z hu uB₁Z hu joinK) below,
        .cumulEq (.sigmaCong uA₂Z hu (Equal.ctxConv uB₂Z eA₁₂) hu joinK) below⟩
  | @id n Γ C C' x x' y y' dA dx dy ihA ihx ihy =>
      intro formed
      obtain ⟨ZC, lZC, atC⟩ := ihA formed
      obtain ⟨zx, lzx, ex, ex'⟩ := ihx formed
      obtain ⟨zy, lzy, ey, ey'⟩ := ihy formed
      have eCC' := soundTypes formed dA
      obtain ⟨w, hw, tC, tC'⟩ := common_universe dA.types_isType.1 dA.types_isType.2
      obtain ⟨tZC, eCZ, _⟩ := atC hw tC tC'
      have eCZ' : TypeEq S.R Γ C ZC := ⟨w, hw, eCZ⟩
      have tzx := Typed.convType (Equal.typed ex formed).2 eCZ'
      have tzy := Typed.convType (Equal.typed ey formed).2 eCZ'
      refine ⟨.id ZC zx zy, .id lZC (lzx.convType S.levels eCZ') (lzy.convType S.levels eCZ')
        ⟨w, hw, .idForm tZC hw tzx tzy⟩, ?_⟩
      intro u hu tId tId'
      obtain ⟨uC, _, _⟩ := Typed.id_universe facts algebra formed tId
      obtain ⟨uC', _, _⟩ := Typed.id_universe facts algebra formed tId'
      obtain ⟨uZ, uCZ, uC'Z⟩ := atC hu uC uC'
      exact ⟨.idForm uZ hu tzx tzy, .idCong uCZ hu ex ey,
        .idCong uC'Z hu (Equal.convType ex' eCC') (Equal.convType ey' eCC')⟩
  | inductiveType role _ =>
      intro _
      rw [rigid] at role
      cases role
  | neutralTypes _ _ hu₀ d ih =>
      intro formed
      obtain ⟨z, lz, eA, eB⟩ := ih formed
      refine ⟨z, .neutralType lz hu₀ (IsType.below_refl (IsType.head_of_universe hu₀)),
        fun hu tA tB => ?_⟩
      cases d with
      | spinesW d' r _ =>
      obtain ⟨tA₀, tB₀, _⟩ := Algorithmic.sound facts roots heads algebra d' formed
      obtain ⟨_, _, _, principalA, principalB⟩ :=
        Algorithm.sound facts roots heads algebra d'.refines formed tA₀ tB₀
      obtain ⟨s, hs, eU⟩ := r.typeEq.symm
      have leA : TypeLe S.R _ _ (.head _) := .conv eU hs (principalA tA)
      have leB : TypeLe S.R _ _ (.head _) := .conv eU hs (principalB tB)
      exact ⟨Typed.subsume (Equal.typed eA formed).2 leA, Equal.subsume eA leA,
        Equal.subsume eB leB⟩
  | terms rA _ rt ru _ ih =>
      intro formed
      obtain ⟨z, lz, et, eu⟩ := ih formed
      exact ⟨z, lz.convType S.levels rA.typeEq.symm,
        Equal.convType (.trans rt.equal et) rA.typeEq.symm,
        Equal.convType (.trans ru.equal eu) rA.typeEq.symm⟩
  | univ hu tt tu _ ih =>
      intro formed
      obtain ⟨Z, lZ, at'⟩ := ih formed
      obtain ⟨tZ, et, eu⟩ := at' hu tt tu
      exact ⟨Z, .univ hu (IsType.refl (IsType.head_of_universe hu)) tZ lZ, et, eu⟩
  | @eta n Γ f g A B isA tf _ tg _ _ ih =>
      intro formed
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed isA
      obtain ⟨z, lz, ef, eg⟩ := ih formedA
      have isPi := Typed.isType tf formed
      obtain ⟨s, hs, tPi⟩ := isPi
      have tLam : Typed S.R Γ (.lam z) (.pi A B) := .lamIntro tPi hs (Equal.typed ef formedA).2
      have back := (WhRed.preserve facts roots formedA (whRed_eta_lam z) (typed_apply_fresh tLam)).2
      exact ⟨.lam z, .lam (IsType.refl ⟨s, hs, tPi⟩) isA tLam lz,
        .etaPi tf tLam (.trans ef (.symm back)), .etaPi tg tLam (.trans eg (.symm back))⟩
  | @sigmaEta n Γ p q A B tp _ tq _ d₁ _ ih₁ ih₂ =>
      intro formed
      obtain ⟨z₁, lz₁, ep₁, eq₁⟩ := ih₁ formed
      obtain ⟨z₂, lz₂, ep₂, eq₂⟩ := ih₂ formed
      obtain ⟨s, hs, tSigma⟩ := Typed.isType tp formed
      obtain ⟨_, ⟨v, hv, family⟩⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
      have tFstP : Typed S.R Γ (.fst p) A := .fstElim tp
      have tFstQ : Typed S.R Γ (.fst q) A := .fstElim tq
      have tz₁ := (Equal.typed ep₁ formed).2
      have toZ : TypeEq S.R Γ (inst0 (.fst p) B) (inst0 z₁ B) :=
        TypeEq.of_instantiateEq family hv tFstP ep₁
      have tz₂ : Typed S.R Γ z₂ (inst0 z₁ B) := Typed.convType (Equal.typed ep₂ formed).2 toZ
      have tPair : Typed S.R Γ (.pair z₁ z₂) (.sigma A B) := .pairIntro tSigma hs tz₁ tz₂
      have fstPair := (Typed.fstPair_preserve facts formed (.fstElim tPair)).2
      have sndPair := (Typed.sndPair_preserve facts formed (.sndElim tPair)).2
      have fromPair : TypeEq S.R Γ (inst0 (.fst (.pair z₁ z₂)) B) (inst0 (.fst p) B) :=
        TypeEq.of_instantiateEq family hv (.fstElim tPair) (.trans fstPair (.symm ep₁))
      have pq : Equal S.R Γ (.fst p) (.fst q) A := soundTerms formed d₁
      have toQ : TypeEq S.R Γ (inst0 (.fst p) B) (inst0 (.fst q) B) :=
        TypeEq.of_instantiateEq family hv tFstP pq
      have sndP : Equal S.R Γ (.snd p) (.snd (.pair z₁ z₂)) (inst0 (.fst p) B) :=
        .trans ep₂ (.symm (Equal.convType sndPair fromPair))
      have sndQ : Equal S.R Γ (.snd q) (.snd (.pair z₁ z₂)) (inst0 (.fst q) B) :=
        Equal.convType (.trans eq₂ (.symm (Equal.convType sndPair fromPair))) toQ
      exact ⟨.pair z₁ z₂, .pair (IsType.refl ⟨s, hs, tSigma⟩) tPair lz₁ (lz₂.convType S.levels toZ),
        .etaSigma tp tPair (.trans ep₁ (.symm fstPair)) sndP,
        .etaSigma tq tPair (.trans eq₁ (.symm fstPair)) sndQ⟩
  | @refl n Γ x x' A a b tx tx' _ ih =>
      intro formed
      obtain ⟨z, lz, ex, ex'⟩ := ih formed
      obtain ⟨s, hs, tId⟩ := Typed.isType tx formed
      obtain ⟨uA, _, _⟩ := Typed.id_universe facts algebra formed tId
      obtain ⟨A₀, tx₀, le⟩ := tx.generation
      have eId := TypeLe.id_eq facts le ⟨s, hs, tId⟩ formed
      obtain ⟨eA₀, exa, exb⟩ := TypeEq.id_injective facts eId formed
      have exa' := Equal.convType exa eA₀
      have exb' := Equal.convType exb eA₀
      have tz := (Equal.typed ex formed).2
      have zId : TypeEq S.R Γ (.id A z z) (.id A a b) :=
        ⟨s, hs, .idCong (.refl uA) hs (.trans (.symm ex) exa') (.trans (.symm ex) exb')⟩
      have xId : TypeEq S.R Γ (.id A x x) (.id A a b) := ⟨s, hs, .idCong (.refl uA) hs exa' exb'⟩
      have x'Id : TypeEq S.R Γ (.id A x' x') (.id A a b) :=
        ⟨s, hs, .idCong (.refl uA) hs (.trans (.trans ex' (.symm ex)) exa')
          (.trans (.trans ex' (.symm ex)) exb')⟩
      have tRefl : Typed S.R Γ (.refl z) (.id A a b) := Typed.convType (.reflIntro tz) zId
      exact ⟨.refl z, .refl (IsType.refl ⟨s, hs, tId⟩) tRefl lz,
        Equal.convType (.reflCong ex) xId, Equal.convType (.reflCong ex') x'Id⟩
  | spine sA _ _ tt tu d ih =>
      intro formed
      obtain ⟨z, lz, et, eu⟩ := ih formed
      cases d with
      | spinesW d' r _ =>
      obtain ⟨tt₀, tu₀, _⟩ := Algorithmic.sound facts roots heads algebra d' formed
      obtain ⟨_, _, _, principalT, principalU⟩ :=
        Algorithm.sound facts roots heads algebra d'.refines formed tt₀ tu₀
      obtain ⟨s, hs, eU⟩ := r.typeEq.symm
      have isA := Typed.isType tt formed
      have leT : TypeLe S.R _ _ _ := .conv eU hs (principalT tt)
      have leU : TypeLe S.R _ _ _ := .conv eU hs (principalU tu)
      have base : Base S.R _ _ :=
        ⟨fun A B e => SpineType.not_pi (SpineType.of_typeEq facts sA e formed
            (.inr (.inl ⟨A, B, rfl⟩))),
          fun A B e => SpineType.not_sigma (SpineType.of_typeEq facts sA e formed
            (.inr (.inr (.inl ⟨A, B, rfl⟩))))⟩
      exact ⟨z, .neutral lz (TypeLe.toBelow leT isA) (Typed.subsume (Equal.typed et formed).2 leT)
          base, Equal.subsume et leT, Equal.subsume eu leU⟩
  | @var n Γ i =>
      intro formed
      have typed : Typed S.R Γ (.var i) (Ctx.lookup Γ i) := .var i
      exact ⟨.var i, .var i (IsType.refl (Typed.isType typed formed)), .refl typed, .refl typed⟩
  | @const n Γ c type declared typed =>
      intro formed
      exact ⟨.const c, .const (rigid c) declared typed (IsType.refl (Typed.isType typed formed)),
        .refl typed, .refl typed⟩
  | @app n Γ f g a b A B _ da ihf iha =>
      intro formed
      obtain ⟨zf, lzf, ef, eg⟩ := ihf formed
      obtain ⟨za, lza, ea, eb⟩ := iha formed
      have tf := (Equal.typed ef formed).1
      have isPi := Typed.isType tf formed
      obtain ⟨_, ⟨v, hv, family⟩⟩ := IsType.pi_parts isPi
      have ta := (Equal.typed ea formed).1
      have tb := (Equal.typed eb formed).1
      have toZ : TypeEq S.R Γ (inst0 a B) (inst0 za B) := TypeEq.of_instantiateEq family hv ta ea
      have fromB : TypeEq S.R Γ (inst0 b B) (inst0 a B) :=
        TypeEq.of_instantiateEq family hv tb (.trans eb (.symm ea))
      exact ⟨.app zf za, .app lzf (IsType.refl isPi) lza toZ, .appCong ef ea,
        Equal.convType (.appCong eg eb) fromB⟩
  | @fst n Γ p q A B _ ih =>
      intro formed
      obtain ⟨zp, lzp, ep, eq⟩ := ih formed
      have isSigma := Typed.isType (Equal.typed ep formed).1 formed
      obtain ⟨⟨w, hw, tA⟩, _⟩ := IsType.sigma_parts isSigma
      exact ⟨.fst zp, .fst lzp (IsType.refl isSigma) (IsType.refl ⟨w, hw, tA⟩), .fstCong ep,
        .fstCong eq⟩
  | @snd n Γ p q A B _ ih =>
      intro formed
      obtain ⟨zp, lzp, ep, eq⟩ := ih formed
      have tp := (Equal.typed ep formed).1
      have isSigma := Typed.isType tp formed
      obtain ⟨_, ⟨v, hv, family⟩⟩ := IsType.sigma_parts isSigma
      have toZ : TypeEq S.R Γ (inst0 (.fst p) B) (inst0 (.fst zp) B) :=
        TypeEq.of_instantiateEq family hv (.fstElim tp) (.fstCong ep)
      have fromQ : TypeEq S.R Γ (inst0 (.fst q) B) (inst0 (.fst p) B) :=
        TypeEq.of_instantiateEq family hv (.fstElim (Equal.typed eq formed).1)
          (.fstCong (.trans eq (.symm ep)))
      exact ⟨.snd zp, .snd lzp (IsType.refl isSigma) toZ, .sndCong ep,
        Equal.convType (.sndCong eq) fromQ⟩
  | spinesW _ rU _ ih =>
      intro formed
      obtain ⟨z, lz, et, eu⟩ := ih formed
      exact ⟨z, lz.spine_convType S.levels rU.typeEq, Equal.convType et rU.typeEq,
        Equal.convType eu rU.typeEq⟩

variable (complete : AlgorithmicComplete S.R S.roles)
include complete

/-- **Every typed term of a formed context has an η-long normal form.** -/
theorem long_exists {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t A : Tm Head n}
    (typed : Typed S.R Γ t A) : ∃ v, NormalForm S.R S.roles Γ t v A := by
  obtain ⟨v, lv, e, _⟩ :=
    extract_of_algorithmic facts roots heads algebra rigid (complete formed (.refl typed)) formed
  exact ⟨v, lv, e⟩

/-- **Equal terms have a common η-long normal form.** -/
theorem long_common {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t u A : Tm Head n}
    (equal : Equal S.R Γ t u A) :
    ∃ v, NormalForm S.R S.roles Γ t v A ∧ NormalForm S.R S.roles Γ u v A := by
  obtain ⟨v, lv, et, eu⟩ :=
    extract_of_algorithmic facts roots heads algebra rigid (complete formed equal) formed
  exact ⟨v, ⟨lv, et⟩, ⟨lv, eu⟩⟩

/-- Every type of a formed context has an η-long normal form, equal to it at every universe at
which it is typed. -/
theorem long_type_exists {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A : Tm Head n}
    (isType : IsType S.R Γ A) :
    ∃ Z, Long S.R S.roles (.type Γ Z) ∧ ∀ {u : Head}, S.R.isUniverse u →
      Typed S.R Γ A (.head u) → Typed S.R Γ Z (.head u) ∧ Equal S.R Γ A Z (.head u) := by
  obtain ⟨Z, lZ, at'⟩ := extract_of_algorithmic facts roots heads algebra rigid
    (complete.types (IsType.refl isType) formed) formed
  exact ⟨Z, lZ, fun hu tA => ⟨(at' hu tA tA).1, (at' hu tA tA).2.1⟩⟩

end Extraction

end ContextualDependentEtaLong
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
