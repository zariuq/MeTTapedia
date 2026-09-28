import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Generation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.WrittenDomains

/-!
# Typing terms with written domains

`ATyped R Γ t A` reads every typing rule of the calculus on the term with
written domains `t`. A λ with a written domain `W` is typed at `Π A B` only
when `W` is a type equal to `A`: the written domain is a contract, checked
against the domain the λ is checked at. Types stay terms of the calculus.

Erasing an annotated typing gives a typing of the erased term, and a typing
of a term of the calculus is an annotated typing of the same term with no
domain written.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

variable {Head : Type}

/-- Typing of terms with written domains. -/
inductive ATyped (R : Rules Head) : {n : Nat} → Ctx Head n → ATm Head n → Tm Head n → Prop where
  | headType {n : Nat} {Γ : Ctx Head n} {h u : Head} :
      R.headTyping h u → ATyped R Γ (.head h) (.head u)
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      ATyped R Γ (.var i) (Ctx.lookup Γ i)
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} {u : Head} :
      R.constantType name = some type → Typed R .nil type (.head u) → R.isUniverse u →
      ATyped R Γ (.const name) (liftClosed type)
  | piForm {n : Nat} {Γ : Ctx Head n} {A : ATm Head n} {B : ATm Head (n + 1)}
      {u v w : Head} :
      ATyped R Γ A (.head u) → R.isUniverse u →
      ATyped R (.snoc Γ A.erase) B (.head v) → R.isUniverse v →
      R.join u v w → ATyped R Γ (.pi A B) (.head w)
  | sigmaForm {n : Nat} {Γ : Ctx Head n} {A : ATm Head n} {B : ATm Head (n + 1)}
      {u v w : Head} :
      ATyped R Γ A (.head u) → R.isUniverse u →
      ATyped R (.snoc Γ A.erase) B (.head v) → R.isUniverse v →
      R.join u v w → ATyped R Γ (.sigma A B) (.head w)
  /-- A λ without a written domain takes its domain from its type. -/
  | lamBare {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {body : ATm Head (n + 1)}
      {B : Tm Head (n + 1)} {u : Head} :
      Typed R Γ (.pi A B) (.head u) → R.isUniverse u →
      ATyped R (.snoc Γ A) body B →
      ATyped R Γ (.lamBare body) (.pi A B)
  /-- A written domain is a type equal to the domain the λ is checked at. -/
  | lamTyped {n : Nat} {Γ : Ctx Head n} {W : ATm Head n} {A : Tm Head n}
      {body : ATm Head (n + 1)} {B : Tm Head (n + 1)} {u v : Head} :
      ATyped R Γ W (.head v) → R.isUniverse v →
      Equal R Γ W.erase A (.head v) →
      Typed R Γ (.pi A B) (.head u) → R.isUniverse u →
      ATyped R (.snoc Γ A) body B →
      ATyped R Γ (.lamTyped W body) (.pi A B)
  | appElim {n : Nat} {Γ : Ctx Head n} {g a : ATm Head n} {A : Tm Head n}
      {B : Tm Head (n + 1)} :
      ATyped R Γ g (.pi A B) → ATyped R Γ a A →
      ATyped R Γ (.app g a) (inst0 a.erase B)
  | pairIntro {n : Nat} {Γ : Ctx Head n} {a b : ATm Head n} {A : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} :
      Typed R Γ (.sigma A B) (.head u) → R.isUniverse u →
      ATyped R Γ a A → ATyped R Γ b (inst0 a.erase B) →
      ATyped R Γ (.pair a b) (.sigma A B)
  | fstElim {n : Nat} {Γ : Ctx Head n} {p : ATm Head n} {A : Tm Head n}
      {B : Tm Head (n + 1)} :
      ATyped R Γ p (.sigma A B) → ATyped R Γ (.fst p) A
  | sndElim {n : Nat} {Γ : Ctx Head n} {p : ATm Head n} {A : Tm Head n}
      {B : Tm Head (n + 1)} :
      ATyped R Γ p (.sigma A B) → ATyped R Γ (.snd p) (inst0 (.fst p.erase) B)
  | idForm {n : Nat} {Γ : Ctx Head n} {A a b : ATm Head n} {u : Head} :
      ATyped R Γ A (.head u) → R.isUniverse u →
      ATyped R Γ a A.erase → ATyped R Γ b A.erase →
      ATyped R Γ (.id A a b) (.head u)
  | reflIntro {n : Nat} {Γ : Ctx Head n} {a : ATm Head n} {A : Tm Head n} :
      ATyped R Γ a A → ATyped R Γ (.refl a) (.id A a.erase a.erase)
  | conv {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A B : Tm Head n} {u : Head} :
      ATyped R Γ t A → Equal R Γ A B (.head u) → R.isUniverse u → ATyped R Γ t B
  | sub {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A B : Tm Head n} :
      ATyped R Γ t A → Below R Γ A B → ATyped R Γ t B

variable {R : Rules Head}

/-- An annotated term of a universe is one of every universe above it. -/
theorem ATyped.cumul {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {u v : Head}
    (typing : ATyped R Γ t (.head u)) (c : R.cumulative u v) : ATyped R Γ t (.head v) :=
  .sub typing (.subUniv c)

/-- Erasing the written domains of an annotated typing types the erased term. -/
theorem ATyped.erase {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A : Tm Head n}
    (typing : ATyped R Γ t A) : Typed R Γ t.erase A := by
  induction typing with
  | headType h => exact .headType h
  | var i => exact .var i
  | const d t hu => exact .const d t hu
  | piForm _ hu _ hv join ihA ihB => exact .piForm ihA hu ihB hv join
  | sigmaForm _ hu _ hv join ihA ihB => exact .sigmaForm ihA hu ihB hv join
  | lamBare tPi hu _ ih => exact .lamIntro tPi hu ih
  | lamTyped _ _ _ tPi hu _ _ ih => exact .lamIntro tPi hu ih
  | appElim _ _ ihg iha => exact .appElim ihg iha
  | pairIntro tSigma hu _ _ iha ihb => exact .pairIntro tSigma hu iha ihb
  | fstElim _ ih => exact .fstElim ih
  | sndElim _ ih => exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb => exact .idForm ihA hu iha ihb
  | reflIntro _ ih => exact .reflIntro ih
  | conv _ e hu ih => exact .conv ih e hu
  | sub _ le ih => exact .sub ih le

/-- What a derivation gives a term with no domain written. -/
def Statement.Lifts (R : Rules Head) : Statement Head → Prop
  | .typing Γ t T => ATyped R Γ (ATm.ofTm t) T
  | .equality _ _ _ _ => True
  | .sub _ _ _ => True

theorem Derivable.lifts {st : Statement Head} (derivation : Derivable R st) :
    st.Lifts R := by
  induction derivation with
  | headType h => exact .headType h
  | var i => exact .var i
  | const d t hu _ => exact .const d t hu
  | piForm _ hu _ hv join ihA ihB =>
      simp only [Statement.Lifts, ATm.ofTm] at ihA ihB ⊢
      exact .piForm ihA hu (by simpa only [ATm.erase_ofTm] using ihB) hv join
  | sigmaForm _ hu _ hv join ihA ihB =>
      simp only [Statement.Lifts, ATm.ofTm] at ihA ihB ⊢
      exact .sigmaForm ihA hu (by simpa only [ATm.erase_ofTm] using ihB) hv join
  | lamIntro tPi hu _ _ ih =>
      simp only [Statement.Lifts, ATm.ofTm] at ih ⊢
      exact .lamBare tPi hu ih
  | appElim _ _ ihg iha =>
      simp only [Statement.Lifts, ATm.ofTm] at ihg iha ⊢
      have typed := ATyped.appElim ihg iha
      simpa only [ATm.erase_ofTm] using typed
  | pairIntro tSigma hu _ _ _ iha ihb =>
      simp only [Statement.Lifts, ATm.ofTm] at iha ihb ⊢
      exact .pairIntro tSigma hu iha (by simpa only [ATm.erase_ofTm] using ihb)
  | fstElim _ ih =>
      simp only [Statement.Lifts, ATm.ofTm] at ih ⊢
      exact .fstElim ih
  | sndElim _ ih =>
      simp only [Statement.Lifts, ATm.ofTm] at ih ⊢
      have typed := ATyped.sndElim ih
      simpa only [ATm.erase_ofTm] using typed
  | idForm _ hu _ _ ihA iha ihb =>
      simp only [Statement.Lifts, ATm.ofTm] at ihA iha ihb ⊢
      exact .idForm ihA hu (by simpa only [ATm.erase_ofTm] using iha)
        (by simpa only [ATm.erase_ofTm] using ihb)
  | reflIntro _ ih =>
      simp only [Statement.Lifts, ATm.ofTm] at ih ⊢
      have typed := ATyped.reflIntro ih
      simpa only [ATm.erase_ofTm] using typed
  | conv _ e hu ih _ =>
      simp only [Statement.Lifts] at ih ⊢
      exact .conv ih e hu
  | sub _ le ih _ =>
      simp only [Statement.Lifts] at ih ⊢
      exact .sub ih le
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | convEq => trivial
  | headEq => trivial
  | piCong => trivial
  | sigmaCong => trivial
  | idCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | pairCong => trivial
  | fstCong => trivial
  | sndCong => trivial
  | reflCong => trivial
  | betaPi => trivial
  | betaFst => trivial
  | betaSnd => trivial
  | root => trivial
  | etaPi => trivial
  | etaSigma => trivial
  | subEq => trivial
  | subEqual => trivial
  | subUniv => trivial
  | subPi => trivial
  | subSigma => trivial
  | subTrans => trivial

/-- A typed term of the calculus, with no domain written, is typed. -/
theorem ATyped.ofTyped {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typed R Γ t A) : ATyped R Γ (ATm.ofTm t) A :=
  Derivable.lifts typing

/-- Annotated typing is stable under conversion of the type. -/
theorem ATyped.convType {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A B : Tm Head n}
    {u : Head} (typing : ATyped R Γ t A) (equal : Equal R Γ A B (.head u))
    (hu : R.isUniverse u) : ATyped R Γ t B :=
  .conv typing equal hu

/-! ## Writing every domain -/

/-- What a derivation gives a term with every domain written. -/
def Statement.Annotates (R : Rules Head) : Statement Head → Prop
  | .typing Γ t T => ∃ written : ATm Head _, written.erase = t ∧ written.Written ∧
      ATyped R Γ written T
  | .equality _ _ _ _ => True
  | .sub _ _ _ => True

theorem Derivable.annotates {st : Statement Head} (derivation : Derivable R st) :
    st.Annotates R := by
  induction derivation with
  | @headType _ _ hd _ typing => exact ⟨.head hd, rfl, trivial, .headType typing⟩
  | var i => exact ⟨.var i, rfl, trivial, .var i⟩
  | @const _ _ name _ _ d t hu _ => exact ⟨.const name, rfl, trivial, .const d t hu⟩
  | piForm _ hu _ hv join ihA ihB =>
      obtain ⟨A', eA, wA, tA⟩ := ihA
      obtain ⟨B', eB, wB, tB⟩ := ihB
      subst eA eB
      exact ⟨.pi A' B', rfl, ⟨wA, wB⟩, .piForm tA hu tB hv join⟩
  | sigmaForm _ hu _ hv join ihA ihB =>
      obtain ⟨A', eA, wA, tA⟩ := ihA
      obtain ⟨B', eB, wB, tB⟩ := ihB
      subst eA eB
      exact ⟨.sigma A' B', rfl, ⟨wA, wB⟩, .sigmaForm tA hu tB hv join⟩
  | @lamIntro _ _ A _ _ _ tPi hu _ _ ih =>
      obtain ⟨body', eb, wb, tb⟩ := ih
      subst eb
      obtain ⟨u', _, _, tA, hu', _⟩ := tPi.generation
      refine ⟨.lamTyped (ATm.ofTm A) body', rfl, wb, ?_⟩
      exact .lamTyped (ATyped.ofTyped tA) hu'
        (by simpa only [ATm.erase_ofTm] using Derivable.refl tA) tPi hu tb
  | appElim _ _ ihg iha =>
      obtain ⟨g', eg, wg, tg⟩ := ihg
      obtain ⟨a', ea, wa, ta⟩ := iha
      subst eg ea
      exact ⟨.app g' a', rfl, ⟨wg, wa⟩, .appElim tg ta⟩
  | pairIntro tSigma hu _ _ _ iha ihb =>
      obtain ⟨a', ea, wa, ta⟩ := iha
      obtain ⟨b', eb, wb, tb⟩ := ihb
      subst ea eb
      exact ⟨.pair a' b', rfl, ⟨wa, wb⟩, .pairIntro tSigma hu ta tb⟩
  | fstElim _ ih =>
      obtain ⟨p', ep, wp, tp⟩ := ih
      subst ep
      exact ⟨.fst p', rfl, wp, .fstElim tp⟩
  | sndElim _ ih =>
      obtain ⟨p', ep, wp, tp⟩ := ih
      subst ep
      exact ⟨.snd p', rfl, wp, .sndElim tp⟩
  | idForm _ hu _ _ ihA iha ihb =>
      obtain ⟨A', eA, wA, tA⟩ := ihA
      obtain ⟨a', ea, wa, ta⟩ := iha
      obtain ⟨b', eb, wb, tb⟩ := ihb
      subst eA ea eb
      exact ⟨.id A' a' b', rfl, ⟨wA, wa, wb⟩, .idForm tA hu ta tb⟩
  | reflIntro _ ih =>
      obtain ⟨a', ea, wa, ta⟩ := ih
      subst ea
      exact ⟨.refl a', rfl, wa, .reflIntro ta⟩
  | sub _ le ih _ =>
      obtain ⟨t', et, wt, tt⟩ := ih
      exact ⟨t', et, wt, .sub tt le⟩
  | conv _ e hu ih _ =>
      obtain ⟨t', et, wt, tt⟩ := ih
      exact ⟨t', et, wt, .conv tt e hu⟩
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | convEq => trivial
  | headEq => trivial
  | piCong => trivial
  | sigmaCong => trivial
  | idCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | pairCong => trivial
  | fstCong => trivial
  | sndCong => trivial
  | reflCong => trivial
  | betaPi => trivial
  | betaFst => trivial
  | betaSnd => trivial
  | root => trivial
  | etaPi => trivial
  | etaSigma => trivial
  | subEq => trivial
  | subEqual => trivial
  | subUniv => trivial
  | subPi => trivial
  | subSigma => trivial
  | subTrans => trivial

/-- Every typed term of the calculus is the erasure of a typed term in which
every λ carries the domain it is checked at. -/
theorem Typed.annotate {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typed R Γ t A) :
    ∃ written : ATm Head n, written.erase = t ∧ written.Written ∧ ATyped R Γ written A :=
  Derivable.annotates typing

/-! ## Renaming -/

/-- Annotated typing is stable under renaming along a compatible context map. -/
theorem ATyped.rename {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A : Tm Head n}
    (typing : ATyped R Γ t A) :
    ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, CtxRen Γ Δ ρ →
      ATyped R Δ (ATm.rename ρ t) (Presentation.rename ρ A) := by
  induction typing with
  | headType h =>
      intro m Δ ρ _
      exact .headType h
  | var i =>
      intro m Δ ρ compatible
      simpa only [ATm.rename, compatible i] using (ATyped.var (R := R) (Γ := Δ) (ρ i))
  | const d t hu =>
      intro m Δ ρ _
      simpa only [ATm.rename, rename_liftClosed] using (ATyped.const (Γ := Δ) d t hu)
  | piForm _ hu _ hv join ihA ihB =>
      intro m Δ ρ compatible
      have tB := ihB (compatible.snoc _)
      rw [← ATm.erase_rename] at tB
      exact .piForm (ihA compatible) hu tB hv join
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro m Δ ρ compatible
      have tB := ihB (compatible.snoc _)
      rw [← ATm.erase_rename] at tB
      exact .sigmaForm (ihA compatible) hu tB hv join
  | lamBare tPi hu _ ih =>
      intro m Δ ρ compatible
      exact .lamBare (tPi.rename compatible) hu (ih (compatible.snoc _))
  | lamTyped _ hv agree tPi hu _ ihW ih =>
      intro m Δ ρ compatible
      have agree' := agree.rename compatible
      rw [← ATm.erase_rename] at agree'
      exact .lamTyped (ihW compatible) hv agree' (tPi.rename compatible) hu
        (ih (compatible.snoc _))
  | appElim _ _ ihg iha =>
      intro m Δ ρ compatible
      have typed := ATyped.appElim (ihg compatible) (iha compatible)
      simpa only [ATm.rename, rename_inst0, ATm.erase_rename] using typed
  | pairIntro tSigma hu _ _ iha ihb =>
      intro m Δ ρ compatible
      have tb := ihb compatible
      rw [rename_inst0, ← ATm.erase_rename] at tb
      exact .pairIntro (tSigma.rename compatible) hu (iha compatible) tb
  | fstElim _ ih =>
      intro m Δ ρ compatible
      exact .fstElim (ih compatible)
  | sndElim _ ih =>
      intro m Δ ρ compatible
      have typed := ATyped.sndElim (ih compatible)
      simpa only [ATm.rename, rename_inst0, Presentation.rename, ATm.erase_rename] using typed
  | idForm _ hu _ _ ihA iha ihb =>
      intro m Δ ρ compatible
      have ta := iha compatible
      have tb := ihb compatible
      rw [← ATm.erase_rename] at ta tb
      exact .idForm (ihA compatible) hu ta tb
  | reflIntro _ ih =>
      intro m Δ ρ compatible
      have typed := ATyped.reflIntro (ih compatible)
      simpa only [ATm.rename, Presentation.rename, ATm.erase_rename] using typed
  | conv _ e hu ih =>
      intro m Δ ρ compatible
      exact .conv (ih compatible) (e.rename compatible) hu
  | sub _ le ih =>
      intro m Δ ρ compatible
      exact .sub (ih compatible) (Derivable.renames le compatible)

theorem ATyped.weaken {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A extension : Tm Head n}
    (typing : ATyped R Γ t A) :
    ATyped R (.snoc Γ extension) (ATm.rename wk t) (Presentation.rename wk A) :=
  typing.rename (fun _ => rfl)

/-! ## Substitution -/

/-- A substitution of terms with written domains, typed by the annotated
judgment; the types are substituted by its erasure. -/
def ASubstMor (R : Rules Head) {n m : Nat} (Γ : Ctx Head n) (Δ : Ctx Head m)
    (σ : ATm.ASub Head n m) : Prop :=
  ∀ index, ATyped R Δ (σ index) (subst (ATm.eraseSub σ) (Ctx.lookup Γ index))

/-- The erasure of a typed substitution is typed. -/
theorem ASubstMor.erase {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : ATm.ASub Head n m} (typed : ASubstMor R Γ Δ σ) : SubstMor R Γ Δ (ATm.eraseSub σ) :=
  fun index => (typed index).erase

theorem ASubstMor.lift {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : ATm.ASub Head n m} (typed : ASubstMor R Γ Δ σ) (A : Tm Head n) :
    ASubstMor R (.snoc Γ A) (.snoc Δ (subst (ATm.eraseSub σ) A)) (ATm.liftSub σ) := by
  intro index
  rw [ATm.erase_liftSub]
  refine Fin.cases ?_ ?_ index
  · simpa only [ATm.liftSub, Fin.cases_zero, liftSub_zero, Ctx.lookup_snoc_zero,
      subst_liftSub_wk] using
      (ATyped.var (R := R) (Γ := .snoc Δ (subst (ATm.eraseSub σ) A)) (0 : Fin (m + 1)))
  · intro prior
    simpa only [ATm.liftSub, Fin.cases_succ, Ctx.lookup_snoc_succ, subst_liftSub_wk] using
      (ATyped.weaken (extension := subst (ATm.eraseSub σ) A) (typed prior))

/-- Annotated typing is stable under a typed substitution. -/
theorem ATyped.substitute {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A : Tm Head n}
    (typing : ATyped R Γ t A) :
    ∀ {m : Nat} {Δ : Ctx Head m} {σ : ATm.ASub Head n m}, ASubstMor R Γ Δ σ →
      ATyped R Δ (ATm.subst σ t) (subst (ATm.eraseSub σ) A) := by
  induction typing with
  | headType h =>
      intro m Δ σ _
      exact .headType h
  | var i =>
      intro m Δ σ typed
      exact typed i
  | const d t hu =>
      intro m Δ σ _
      simpa only [ATm.subst, subst_liftClosed] using (ATyped.const (Γ := Δ) d t hu)
  | piForm _ hu _ hv join ihA ihB =>
      intro m Δ σ typed
      have tB := ihB (typed.lift _)
      rw [← ATm.erase_subst] at tB
      exact .piForm (ihA typed) hu tB hv join
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro m Δ σ typed
      have tB := ihB (typed.lift _)
      rw [← ATm.erase_subst] at tB
      exact .sigmaForm (ihA typed) hu tB hv join
  | lamBare tPi hu _ ih =>
      intro m Δ σ typed
      have tb := ih (typed.lift _)
      rw [ATm.erase_liftSub] at tb
      exact .lamBare (tPi.substitute typed.erase) hu tb
  | lamTyped _ hv agree tPi hu _ ihW ih =>
      intro m Δ σ typed
      have agree' := agree.substitute typed.erase
      rw [← ATm.erase_subst] at agree'
      have tb := ih (typed.lift _)
      rw [ATm.erase_liftSub] at tb
      exact .lamTyped (ihW typed) hv agree' (tPi.substitute typed.erase) hu tb
  | appElim _ _ ihg iha =>
      intro m Δ σ typed
      have typed' := ATyped.appElim (ihg typed) (iha typed)
      simpa only [ATm.subst, subst_inst0, ATm.erase_subst] using typed'
  | pairIntro tSigma hu _ _ iha ihb =>
      intro m Δ σ typed
      have tb := ihb typed
      rw [subst_inst0, ← ATm.erase_subst] at tb
      exact .pairIntro (tSigma.substitute typed.erase) hu (iha typed) tb
  | fstElim _ ih =>
      intro m Δ σ typed
      exact .fstElim (ih typed)
  | sndElim _ ih =>
      intro m Δ σ typed
      have typed' := ATyped.sndElim (ih typed)
      simpa only [ATm.subst, subst_inst0, Presentation.subst, ATm.erase_subst] using typed'
  | idForm _ hu _ _ ihA iha ihb =>
      intro m Δ σ typed
      have ta := iha typed
      have tb := ihb typed
      rw [← ATm.erase_subst] at ta tb
      exact .idForm (ihA typed) hu ta tb
  | reflIntro _ ih =>
      intro m Δ σ typed
      have typed' := ATyped.reflIntro (ih typed)
      simpa only [ATm.subst, Presentation.subst, ATm.erase_subst] using typed'
  | conv _ e hu ih =>
      intro m Δ σ typed
      exact .conv (ih typed) (e.substitute typed.erase) hu
  | sub _ le ih =>
      intro m Δ σ typed
      exact .sub (ih typed) (Derivable.substitutes le typed.erase)

/-- The substitution opening one binder at a typed argument. -/
theorem ASubstMor.single {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {argument : ATm Head n}
    (typing : ATyped R Γ argument A) :
    ASubstMor R (.snoc Γ A) Γ (ATm.subst0 argument) := by
  intro index
  rw [ATm.erase_subst0]
  refine Fin.cases ?_ ?_ index
  · change ATyped R Γ argument (inst0 argument.erase (Presentation.rename wk A))
    rw [inst0_rename_wk]
    exact typing
  · intro prior
    change ATyped R Γ (.var prior)
      (inst0 argument.erase (Presentation.rename wk (Ctx.lookup Γ prior)))
    rw [inst0_rename_wk]
    exact .var prior

/-- Opening a binder at a typed argument. -/
theorem ATyped.instantiate {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {argument : ATm Head n}
    {body : ATm Head (n + 1)} {B : Tm Head (n + 1)}
    (bodyTyping : ATyped R (.snoc Γ A) body B) (argumentTyping : ATyped R Γ argument A) :
    ATyped R Γ (ATm.inst0 argument body) (inst0 argument.erase B) := by
  have typed := bodyTyping.substitute (ASubstMor.single argumentTyping)
  rwa [ATm.erase_subst0] at typed

/-! ## Generation -/

/-- A typing extends along the closure of conversion and universe raising. -/
theorem ATyped.subsume {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A B : Tm Head n}
    (typing : ATyped R Γ t A) (le : TypeLe R Γ A B) : ATyped R Γ t B := by
  induction le generalizing t with
  | refl => exact typing
  | conv e hu _ ih => exact ih (.conv typing e hu)
  | cumul c _ ih => exact ih (.cumul typing c)
  | sub le _ ih => exact ih (.sub typing le)

/-- What an annotated typing of a term says, by the term's former. -/
def AGenerationAt (R : Rules Head) {n : Nat} (Γ : Ctx Head n) : ATm Head n → Tm Head n → Prop
  | .var i, T => TypeLe R Γ (Ctx.lookup Γ i) T
  | .const name, T => ∃ type u, R.constantType name = some type ∧
      Typed R .nil type (.head u) ∧ R.isUniverse u ∧ TypeLe R Γ (liftClosed type) T
  | .head h, T => ∃ u, R.headTyping h u ∧ TypeLe R Γ (.head u) T
  | .pi A B, T => ∃ u v w, ATyped R Γ A (.head u) ∧ R.isUniverse u ∧
      ATyped R (.snoc Γ A.erase) B (.head v) ∧ R.isUniverse v ∧ R.join u v w ∧
      TypeLe R Γ (.head w) T
  | .sigma A B, T => ∃ u v w, ATyped R Γ A (.head u) ∧ R.isUniverse u ∧
      ATyped R (.snoc Γ A.erase) B (.head v) ∧ R.isUniverse v ∧ R.join u v w ∧
      TypeLe R Γ (.head w) T
  | .id A a b, T => ∃ u, ATyped R Γ A (.head u) ∧ R.isUniverse u ∧ ATyped R Γ a A.erase ∧
      ATyped R Γ b A.erase ∧ TypeLe R Γ (.head u) T
  | .lamBare body, T => ∃ A B u, Typed R Γ (.pi A B) (.head u) ∧ R.isUniverse u ∧
      ATyped R (.snoc Γ A) body B ∧ TypeLe R Γ (.pi A B) T
  | .lamTyped W body, T => ∃ A B u v, ATyped R Γ W (.head v) ∧ R.isUniverse v ∧
      Equal R Γ W.erase A (.head v) ∧ Typed R Γ (.pi A B) (.head u) ∧ R.isUniverse u ∧
      ATyped R (.snoc Γ A) body B ∧ TypeLe R Γ (.pi A B) T
  | .app f a, T => ∃ A B, ATyped R Γ f (.pi A B) ∧ ATyped R Γ a A ∧
      TypeLe R Γ (inst0 a.erase B) T
  | .pair a b, T => ∃ A B u, Typed R Γ (.sigma A B) (.head u) ∧ R.isUniverse u ∧
      ATyped R Γ a A ∧ ATyped R Γ b (inst0 a.erase B) ∧ TypeLe R Γ (.sigma A B) T
  | .fst p, T => ∃ A B, ATyped R Γ p (.sigma A B) ∧ TypeLe R Γ A T
  | .snd p, T => ∃ A B, ATyped R Γ p (.sigma A B) ∧ TypeLe R Γ (inst0 (.fst p.erase) B) T
  | .refl a, T => ∃ A, ATyped R Γ a A ∧ TypeLe R Γ (.id A a.erase a.erase) T

/-- Generation is stable along the closure. -/
theorem AGenerationAt.mono {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {T T' : Tm Head n}
    (generation : AGenerationAt R Γ t T) (le : TypeLe R Γ T T') : AGenerationAt R Γ t T' := by
  cases t with
  | var i => exact TypeLe.trans generation le
  | const name =>
      obtain ⟨type, u, d, typing, hu, le'⟩ := generation
      exact ⟨type, u, d, typing, hu, le'.trans le⟩
  | head h =>
      obtain ⟨u, typing, le'⟩ := generation
      exact ⟨u, typing, le'.trans le⟩
  | pi A B =>
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le'⟩ := generation
      exact ⟨u, v, w, tA, hu, tB, hv, join, le'.trans le⟩
  | sigma A B =>
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le'⟩ := generation
      exact ⟨u, v, w, tA, hu, tB, hv, join, le'.trans le⟩
  | id A a b =>
      obtain ⟨u, tA, hu, ta, tb, le'⟩ := generation
      exact ⟨u, tA, hu, ta, tb, le'.trans le⟩
  | lamBare body =>
      obtain ⟨A, B, u, tPi, hu, tb, le'⟩ := generation
      exact ⟨A, B, u, tPi, hu, tb, le'.trans le⟩
  | lamTyped W body =>
      obtain ⟨A, B, u, v, tW, hv, agree, tPi, hu, tb, le'⟩ := generation
      exact ⟨A, B, u, v, tW, hv, agree, tPi, hu, tb, le'.trans le⟩
  | app f a =>
      obtain ⟨A, B, tf, ta, le'⟩ := generation
      exact ⟨A, B, tf, ta, le'.trans le⟩
  | pair a b =>
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le'⟩ := generation
      exact ⟨A, B, u, tSigma, hu, ta, tb, le'.trans le⟩
  | fst p =>
      obtain ⟨A, B, tp, le'⟩ := generation
      exact ⟨A, B, tp, le'.trans le⟩
  | snd p =>
      obtain ⟨A, B, tp, le'⟩ := generation
      exact ⟨A, B, tp, le'.trans le⟩
  | refl a =>
      obtain ⟨A, ta, le'⟩ := generation
      exact ⟨A, ta, le'.trans le⟩

/-- Generation for every annotated typing. -/
theorem ATyped.generation {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {T : Tm Head n}
    (typing : ATyped R Γ t T) : AGenerationAt R Γ t T := by
  induction typing with
  | headType typing => exact ⟨_, typing, .refl _⟩
  | var i => exact .refl _
  | const declared typing hu => exact ⟨_, _, declared, typing, hu, .refl _⟩
  | piForm tA hu tB hv join => exact ⟨_, _, _, tA, hu, tB, hv, join, .refl _⟩
  | sigmaForm tA hu tB hv join => exact ⟨_, _, _, tA, hu, tB, hv, join, .refl _⟩
  | lamBare tPi hu tb => exact ⟨_, _, _, tPi, hu, tb, .refl _⟩
  | lamTyped tW hv agree tPi hu tb => exact ⟨_, _, _, _, tW, hv, agree, tPi, hu, tb, .refl _⟩
  | appElim tf ta => exact ⟨_, _, tf, ta, .refl _⟩
  | pairIntro tSigma hu ta tb => exact ⟨_, _, _, tSigma, hu, ta, tb, .refl _⟩
  | fstElim tp => exact ⟨_, _, tp, .refl _⟩
  | sndElim tp => exact ⟨_, _, tp, .refl _⟩
  | idForm tA hu ta tb => exact ⟨_, tA, hu, ta, tb, .refl _⟩
  | reflIntro ta => exact ⟨_, ta, .refl _⟩
  | conv _ e hu ih => exact AGenerationAt.mono ih (.of_equal e hu)
  | sub _ le ih => exact AGenerationAt.mono ih (.of_below le)

/-! ## Equality of terms with written domains -/

/-- Two terms with written domains are equal at a type when both are typed at
it and their erasures are equal there. -/
def AEqual (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (t s : ATm Head n) (A : Tm Head n) :
    Prop :=
  ATyped R Γ t A ∧ ATyped R Γ s A ∧ Equal R Γ t.erase s.erase A

theorem AEqual.refl {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A : Tm Head n}
    (typing : ATyped R Γ t A) : AEqual R Γ t t A :=
  ⟨typing, typing, .refl typing.erase⟩

theorem AEqual.symm {n : Nat} {Γ : Ctx Head n} {t s : ATm Head n} {A : Tm Head n}
    (equal : AEqual R Γ t s A) : AEqual R Γ s t A :=
  ⟨equal.2.1, equal.1, .symm equal.2.2⟩

theorem AEqual.trans {n : Nat} {Γ : Ctx Head n} {t s r : ATm Head n} {A : Tm Head n}
    (first : AEqual R Γ t s A) (second : AEqual R Γ s r A) : AEqual R Γ t r A :=
  ⟨first.1, second.2.1, .trans first.2.2 second.2.2⟩

/-- Equality extends along the closure of conversion and universe raising. -/
theorem AEqual.subsume {n : Nat} {Γ : Ctx Head n} {t s : ATm Head n} {A B : Tm Head n}
    (equal : AEqual R Γ t s A) (le : TypeLe R Γ A B) : AEqual R Γ t s B :=
  ⟨equal.1.subsume le, equal.2.1.subsume le, equal.2.2.subsume le⟩

/-- Terms whose erasures coincide are equal at every type at which both are
typed. -/
theorem AEqual.of_erase_eq {n : Nat} {Γ : Ctx Head n} {t s : ATm Head n} {A : Tm Head n}
    (tTyped : ATyped R Γ t A) (sTyped : ATyped R Γ s A) (same : t.erase = s.erase) :
    AEqual R Γ t s A :=
  ⟨tTyped, sTyped, same ▸ .refl tTyped.erase⟩

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
