import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.Respect

/-!
# Coherence of generated transport along reflexivity

Along the reflexivity evidence `reflE = λX. (λp. p, λp. p) : setEq S S` (the closed term of
`SetTheory.setEq_refl`), the generated transport of every code of `Respect.FamCode`, in both
directions, is the identity **in the knowledge** (`tr_refl`): `tr c S S reflE x ≡ x` by typed βη.

The proof follows the codes: membership computes by β on the evidence (`mem_refl_fwd_universal`,
`mem_refl_bwd_universal`); a function transports by a β-redex under λ that the two inductive
hypotheses reduce to `λy. x y`, and function η gives `x` (`eta_lam`); pairs and dependent pairs
reduce componentwise and pair η gives `x` (`eta_pair`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Options.Respect

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

/-! ## Reflexivity evidence -/

/-- **The reflexivity evidence** `λX. (λp. p, λp. p)`, in any context. -/
def reflE {m : Nat} : Tower.Tm m := .lam (.pair (.lam (.var 0)) (.lam (.var 0)))

theorem reflE_typed {m : Nat} {Δ : Tower.Ctx m} {S : Tower.Tm m} (hS : Typed Tower.rules Δ S setType) :
    Typed Tower.rules Δ reflE (setEq S S) :=
  SetTheory.setEq_refl.substitute ((noSub_typed Δ).cons setType hS)

/-! ## Two η laws -/

/-- **Function η**: `λy. f y ≡ f`. -/
theorem eta_lam {m : Nat} {Δ : Tower.Ctx m} {f A : Tower.Tm m} {B : Tower.Tm (m + 1)} {u : Tower.Head}
    (formed : Typed Tower.rules Δ (.pi A B) (.head u)) (hu : Tower.rules.isUniverse u)
    (hf : Typed Tower.rules Δ f (.pi A B)) :
    Equal Tower.rules Δ (.lam (.app (Presentation.rename wk f) (.var 0))) f (.pi A B) := by
  have fw : Typed Tower.rules (.snoc Δ A) (Presentation.rename wk f)
      (.pi (Presentation.rename wk A) (Presentation.rename (liftRen wk) B)) := hf.weaken
  have body : Typed Tower.rules (.snoc Δ A) (.app (Presentation.rename wk f) (.var 0)) B := by
    have applied := Derivable.appElim fw (Derivable.var 0)
    rw [open_weakened] at applied
    exact applied
  have lamTyped : Typed Tower.rules Δ (.lam (.app (Presentation.rename wk f) (.var 0))) (.pi A B) :=
    .lamIntro formed hu body
  refine Derivable.etaPi lamTyped hf ?_
  have bodyRen : Typed Tower.rules (.snoc (.snoc Δ A) (Presentation.rename wk A))
      (Presentation.rename (liftRen wk) (.app (Presentation.rename wk f) (.var 0)))
      (Presentation.rename (liftRen wk) B) :=
    body.rename ((show CtxRen Δ (.snoc Δ A) wk from fun _ => rfl).snoc A)
  have formedW : Typed Tower.rules (.snoc Δ A)
      (.pi (Presentation.rename wk A) (Presentation.rename (liftRen wk) B)) (.head u) := formed.weaken
  have beta := Derivable.betaPi formedW hu bodyRen (Derivable.var 0)
  rw [open_weakened, open_weakened] at beta
  exact beta

/-- **Pair η**: `(fst p, snd p) ≡ p`, for a dependent pair type. -/
theorem eta_pair {m : Nat} {Δ : Tower.Ctx m} {p A : Tower.Tm m} {B : Tower.Tm (m + 1)} {u : Tower.Head}
    (formed : Typed Tower.rules Δ (.sigma A B) (.head u)) (hu : Tower.rules.isUniverse u)
    (familyFormed : Typed Tower.rules (.snoc Δ A) B (.head u))
    (hp : Typed Tower.rules Δ p (.sigma A B)) :
    Equal Tower.rules Δ (.pair (.fst p) (.snd p)) p (.sigma A B) := by
  have first : Typed Tower.rules Δ (.fst p) A := Derivable.fstElim hp
  have second : Typed Tower.rules Δ (.snd p) (inst0 (.fst p) B) := Derivable.sndElim hp
  have pairTyped : Typed Tower.rules Δ (.pair (.fst p) (.snd p)) (.sigma A B) := .pairIntro formed hu first second
  have fstEq : Equal Tower.rules Δ (.fst (.pair (.fst p) (.snd p))) (.fst p) A := .betaFst formed hu first second
  have sndEq : Equal Tower.rules Δ (.snd (.pair (.fst p) (.snd p))) (.snd p) (inst0 (.fst p) B) :=
    .betaSnd formed hu first second
  have typesEq : Equal Tower.rules Δ (inst0 (.fst p) B) (inst0 (.fst (.pair (.fst p) (.snd p))) B) (.head u) :=
    Typed.instantiateEq familyFormed first (.symm fstEq)
  exact .etaSigma pairTyped hp fstEq (.convEq sndEq typesEq hu)

/-! ## Membership along reflexivity, in the universal frame -/

/-- The frame `S : U0 → U0, a : U0, x : S a`. -/
abbrev reflMemCtx : Tower.Ctx 3 := .snoc (.snoc (.snoc .nil setType) U0) (.app (.var 1) (.var 0))

theorem reflMem_parts :
    Typed Tower.rules reflMemCtx (.pi (.app (.var 2) (.var 1)) (.app (.var 3) (.var 2))) U0 ∧
      Typed Tower.rules reflMemCtx (.lam (.var 0)) (.pi (.app (.var 2) (.var 1)) (.app (.var 3) (.var 2))) ∧
      Equal Tower.rules reflMemCtx (.app reflE (.var 1)) (.pair (.lam (.var 0)) (.lam (.var 0)))
        (.sigma (.pi (.app (.var 2) (.var 1)) (.app (.var 3) (.var 2)))
          (.pi (.app (.var 3) (.var 2)) (.app (.var 4) (.var 3)))) ∧
      Typed Tower.rules reflMemCtx (.sigma (.pi (.app (.var 2) (.var 1)) (.app (.var 3) (.var 2)))
          (.pi (.app (.var 3) (.var 2)) (.app (.var 4) (.var 3)))) U0 := by
  have tS : Typed Tower.rules reflMemCtx (.var 2) setType := Derivable.var 2
  have ta : Typed Tower.rules reflMemCtx (.var 1) U0 := Derivable.var 1
  have Sa : Typed Tower.rules reflMemCtx (.app (.var 2) (.var 1)) U0 := Run.app_small tS ta
  have Sa' : Typed Tower.rules (.snoc reflMemCtx (.app (.var 2) (.var 1))) (.app (.var 3) (.var 2)) U0 :=
    Run.app_small (Derivable.var 3) (Derivable.var 2)
  have arrowFormed : Typed Tower.rules reflMemCtx (.pi (.app (.var 2) (.var 1)) (.app (.var 3) (.var 2))) U0 :=
    .cumul (.piForm Sa (.sort _) Sa' (.sort _) (.sorts _ _)) collapse
  have identity : Typed Tower.rules reflMemCtx (.lam (.var 0)) (.pi (.app (.var 2) (.var 1)) (.app (.var 3) (.var 2))) :=
    .lamIntro arrowFormed (.sort _) (Derivable.var 0)
  -- the body of `reflE`, over `X : U0`
  have identityX := Derivable.lamIntro (setEqForward_formed tS tS) (.sort _)
    (Derivable.var (R := Tower.rules)
      (Γ := .snoc (.snoc reflMemCtx U0) (.app (Presentation.rename wk (.var 2)) (.var 0))) 0)
  have bodyTyped := Derivable.pairIntro (setEqBody_formed tS tS) (.sort _) identityX identityX
  have beta := Derivable.betaPi (setEq_formed tS tS) (.sort _) bodyTyped ta
  have sigmaFormed := (setEqBody_formed tS tS).instantiate ta
  exact ⟨arrowFormed, identity, beta, sigmaFormed⟩

/-- **Forward membership along reflexivity is the identity**: `fst (reflE a) x ≡ x`. -/
theorem mem_refl_fwd_universal :
    Equal Tower.rules reflMemCtx (.app (.fst (.app reflE (.var 1))) (.var 0)) (.var 0) (.app (.var 2) (.var 1)) := by
  obtain ⟨arrowFormed, identity, beta, sigmaFormed⟩ := reflMem_parts
  have fstEq : Equal Tower.rules reflMemCtx (.fst (.app reflE (.var 1))) (.lam (.var 0))
      (.pi (.app (.var 2) (.var 1)) (.app (.var 3) (.var 2))) :=
    .trans (.fstCong beta) (.betaFst sigmaFormed (.sort _) identity identity)
  have x : Typed Tower.rules reflMemCtx (.var 0) (.app (.var 2) (.var 1)) := Derivable.var 0
  have applied := Derivable.appCong fstEq (.refl x)
  have reduced := Derivable.betaPi arrowFormed (.sort _)
    (Derivable.var (R := Tower.rules) (Γ := .snoc reflMemCtx (.app (.var 2) (.var 1))) 0) x
  exact .trans applied reduced

/-- **Backward membership along reflexivity is the identity**: `snd (reflE a) x ≡ x`. -/
theorem mem_refl_bwd_universal :
    Equal Tower.rules reflMemCtx (.app (.snd (.app reflE (.var 1))) (.var 0)) (.var 0) (.app (.var 2) (.var 1)) := by
  obtain ⟨arrowFormed, identity, beta, sigmaFormed⟩ := reflMem_parts
  have sndEq : Equal Tower.rules reflMemCtx (.snd (.app reflE (.var 1))) (.lam (.var 0))
      (.pi (.app (.var 2) (.var 1)) (.app (.var 3) (.var 2))) :=
    .trans (.sndCong beta) (.betaSnd sigmaFormed (.sort _) identity identity)
  have x : Typed Tower.rules reflMemCtx (.var 0) (.app (.var 2) (.var 1)) := Derivable.var 0
  have applied := Derivable.appCong sndEq (.refl x)
  have reduced := Derivable.betaPi arrowFormed (.sort _)
    (Derivable.var (R := Tower.rules) (Γ := .snoc reflMemCtx (.app (.var 2) (.var 1))) 0) x
  exact .trans applied reduced

/-! ## Every generated transport is the identity along reflexivity -/

/-- **Coherence along reflexivity** for a code at a substitution and a set. -/
def ReflCoherent {n m : Nat} (c : FamCode n) (Δ : Tower.Ctx m) (σ : Presentation.Sub Tower.Head n m)
    (S : Tower.Tm m) : Prop :=
  (∀ {x : Tower.Tm m}, Typed Tower.rules Δ x (inst c σ S) →
      Equal Tower.rules Δ (tr true c σ S S reflE x) x (inst c σ S)) ∧
    (∀ {x : Tower.Tm m}, Typed Tower.rules Δ x (inst c σ S) →
      Equal Tower.rules Δ (tr false c σ S S reflE x) x (inst c σ S))

/-- **Along reflexivity, the generated transport is the identity in the knowledge**, in both
directions, for every well-formed code at every typed substitution and set. -/
theorem tr_refl {n : Nat} (c : FamCode n) :
    ∀ {Γ : Tower.Ctx n}, WF Γ c → ∀ {m : Nat} {Δ : Tower.Ctx m} {σ : Presentation.Sub Tower.Head n m},
      SubstMor Tower.rules Γ Δ σ → ∀ {S : Tower.Tm m}, Typed Tower.rules Δ S setType → ReflCoherent c Δ σ S := by
  induction c with
  | mem a =>
      intro Γ wf m Δ σ hσ S hS
      have wfa : Typed Tower.rules Γ a U0 := wf
      have ha : Typed Tower.rules Δ (subst σ a) U0 := wfa.substitute hσ
      have base := ((noSub_typed Δ).cons setType hS).cons U0 ha
      exact ⟨fun hx => mem_refl_fwd_universal.substitute (base.cons _ hx),
        fun hx => mem_refl_bwd_universal.substitute (base.cons _ hx)⟩
  | const B =>
      intro Γ wf m Δ σ hσ S hS
      exact ⟨fun hx => .refl hx, fun hx => .refl hx⟩
  | arrow F G ihF ihG =>
      intro Γ wf m Δ σ hσ S hS
      have formedS := inst_formed (.arrow F G) wf hσ hS
      obtain ⟨wfF, wfG⟩ := wf
      have hσ' := substMor_wk hσ (inst F σ S)
      have hS' : Typed Tower.rules (.snoc Δ (inst F σ S)) (Presentation.rename wk S) setType := hS.weaken
      have hE' : Typed Tower.rules (.snoc Δ (inst F σ S)) reflE
          (setEq (Presentation.rename wk S) (Presentation.rename wk S)) := reflE_typed hS'
      have RF := ihF wfF hσ' hS'
      have RG := ihG wfG hσ' hS'
      have TF := tr_typed F wfF hσ' hS' hS' hE'
      have TG := tr_typed G wfG hσ' hS' hS' hE'
      have y0 : Typed Tower.rules (.snoc Δ (inst F σ S)) (.var 0) (inst F (wkSub σ) (Presentation.rename wk S)) := by
        have v : Typed Tower.rules (.snoc Δ (inst F σ S)) (.var 0) (Presentation.rename wk (inst F σ S)) :=
          Derivable.var 0
        rw [inst_rename] at v
        exact v
      have step : ∀ (d : Bool) {x : Tower.Tm m}, Typed Tower.rules Δ x (inst (.arrow F G) σ S) →
          (Typed Tower.rules (.snoc Δ (inst F σ S)) (tr (!d) F (wkSub σ) (Presentation.rename wk S)
              (Presentation.rename wk S) reflE (.var 0)) (inst F (wkSub σ) (Presentation.rename wk S))) →
          Equal Tower.rules (.snoc Δ (inst F σ S)) (tr (!d) F (wkSub σ) (Presentation.rename wk S)
              (Presentation.rename wk S) reflE (.var 0)) (.var 0) (inst F (wkSub σ) (Presentation.rename wk S)) →
          (∀ {y : Tower.Tm (m + 1)}, Typed Tower.rules (.snoc Δ (inst F σ S)) y (inst G (wkSub σ) (Presentation.rename wk S)) →
            Equal Tower.rules (.snoc Δ (inst F σ S)) (tr d G (wkSub σ) (Presentation.rename wk S)
              (Presentation.rename wk S) reflE y) y (inst G (wkSub σ) (Presentation.rename wk S))) →
          Equal Tower.rules Δ (tr d (.arrow F G) σ S S reflE x) x (inst (.arrow F G) σ S) := by
        intro d x hx back backEq forward
        have xw : Typed Tower.rules (.snoc Δ (inst F σ S)) (Presentation.rename wk x)
            (.pi (inst F (wkSub σ) (Presentation.rename wk S))
              (Presentation.rename wk (inst G (wkSub σ) (Presentation.rename wk S)))) := by
          have w : Typed Tower.rules (.snoc Δ (inst F σ S)) (Presentation.rename wk x)
              (.pi (Presentation.rename wk (inst F σ S))
                (Presentation.rename (liftRen wk) (Presentation.rename wk (inst G σ S)))) := hx.weaken
          rw [rename_liftRen_wk, inst_rename F σ wk S, inst_rename G σ wk S] at w
          exact w
        have appEq := Derivable.appCong (.refl xw) backEq
        rw [inst0_rename_wk] at appEq
        have appT := Derivable.appElim xw back
        rw [inst0_rename_wk] at appT
        have chain := Derivable.trans (forward appT) appEq
        have chain' : Equal Tower.rules (.snoc Δ (inst F σ S))
            (tr d G (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk S) reflE
              (.app (Presentation.rename wk x)
                (tr (!d) F (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk S) reflE (.var 0))))
            (.app (Presentation.rename wk x) (.var 0)) (Presentation.rename wk (inst G σ S)) := by
          rw [inst_rename]
          exact chain
        have lamEq := Derivable.lamCong formedS (.sort _) chain'
        exact .trans lamEq (eta_lam formedS (.sort _) hx)
      exact ⟨fun hx => step true hx (TF.2 y0) (RF.2 y0) (fun hy => RG.1 hy),
        fun hx => step false hx (TF.1 y0) (RF.1 y0) (fun hy => RG.2 hy)⟩
  | prod F G ihF ihG =>
      intro Γ wf m Δ σ hσ S hS
      have formedS := inst_formed (.prod F G) wf hσ hS
      obtain ⟨wfF, wfG⟩ := wf
      have RF := ihF wfF hσ hS
      have RG := ihG wfG hσ hS
      have familyFormed : Typed Tower.rules (.snoc Δ (inst F σ S)) (Presentation.rename wk (inst G σ S)) (.head large) :=
        (inst_formed G wfG hσ hS).weaken
      have step : ∀ (d : Bool) {x : Tower.Tm m}, Typed Tower.rules Δ x (inst (.prod F G) σ S) →
          (∀ {y : Tower.Tm m}, Typed Tower.rules Δ y (inst F σ S) → Equal Tower.rules Δ (tr d F σ S S reflE y) y (inst F σ S)) →
          (∀ {y : Tower.Tm m}, Typed Tower.rules Δ y (inst G σ S) → Equal Tower.rules Δ (tr d G σ S S reflE y) y (inst G σ S)) →
          Equal Tower.rules Δ (tr d (.prod F G) σ S S reflE x) x (inst (.prod F G) σ S) := by
        intro d x hx eqF eqG
        have hx' : Typed Tower.rules Δ x (.sigma (inst F σ S) (Presentation.rename wk (inst G σ S))) := hx
        have first : Typed Tower.rules Δ (.fst x) (inst F σ S) := Derivable.fstElim hx'
        have second := Derivable.sndElim hx'
        rw [inst0_rename_wk] at second
        have secondEq : Equal Tower.rules Δ (tr d G σ S S reflE (.snd x)) (.snd x)
            (inst0 (tr d F σ S S reflE (.fst x)) (Presentation.rename wk (inst G σ S))) := by
          rw [inst0_rename_wk]
          exact eqG second
        have pairEq := Derivable.pairCong formedS (.sort _) (eqF first) secondEq
        exact .trans pairEq (eta_pair formedS (.sort _) familyFormed hx')
      exact ⟨fun hx => step true hx RF.1 RG.1, fun hx => step false hx RF.2 RG.2⟩
  | pi A F ihF =>
      intro Γ wf m Δ σ hσ S hS
      have formedS := inst_formed (.pi A F) wf hσ hS
      obtain ⟨_, wfF⟩ := wf
      have RF := ihF wfF (hσ.lift A) hS.weaken
      have step : ∀ (d : Bool) {x : Tower.Tm m}, Typed Tower.rules Δ x (inst (.pi A F) σ S) →
          (∀ {y : Tower.Tm (m + 1)}, Typed Tower.rules (.snoc Δ (subst σ A)) y (inst F (liftSub σ) (Presentation.rename wk S)) →
            Equal Tower.rules (.snoc Δ (subst σ A)) (tr d F (liftSub σ) (Presentation.rename wk S) (Presentation.rename wk S)
              reflE y) y (inst F (liftSub σ) (Presentation.rename wk S))) →
          Equal Tower.rules Δ (tr d (.pi A F) σ S S reflE x) x (inst (.pi A F) σ S) := by
        intro d x hx eqF
        have w : Typed Tower.rules (.snoc Δ (subst σ A)) (Presentation.rename wk x)
            (.pi (Presentation.rename wk (subst σ A))
              (Presentation.rename (liftRen wk) (inst F (liftSub σ) (Presentation.rename wk S)))) := hx.weaken
        have arg := Derivable.appElim w (Derivable.var 0)
        rw [open_weakened] at arg
        have lamEq := Derivable.lamCong formedS (.sort _) (eqF arg)
        exact .trans lamEq (eta_lam formedS (.sort _) hx)
      exact ⟨fun hx => step true hx RF.1, fun hx => step false hx RF.2⟩
  | sigma A F ihF =>
      intro Γ wf m Δ σ hσ S hS
      have formedS := inst_formed (.sigma A F) wf hσ hS
      obtain ⟨_, wfF⟩ := wf
      have familyFormed : Typed Tower.rules (.snoc Δ (subst σ A)) (inst F (liftSub σ) (Presentation.rename wk S))
          (.head large) := inst_formed F wfF (hσ.lift A) hS.weaken
      have step : ∀ (d : Bool) {x : Tower.Tm m}, Typed Tower.rules Δ x (inst (.sigma A F) σ S) →
          (∀ {u y : Tower.Tm m}, Typed Tower.rules Δ u (subst σ A) → Typed Tower.rules Δ y (inst F (consSub u σ) S) →
            Equal Tower.rules Δ (tr d F (consSub u σ) S S reflE y) y (inst F (consSub u σ) S)) →
          Equal Tower.rules Δ (tr d (.sigma A F) σ S S reflE x) x (inst (.sigma A F) σ S) := by
        intro d x hx eqF
        have hx' : Typed Tower.rules Δ x (.sigma (subst σ A) (inst F (liftSub σ) (Presentation.rename wk S))) := hx
        have first : Typed Tower.rules Δ (.fst x) (subst σ A) := Derivable.fstElim hx'
        have second := Derivable.sndElim hx'
        rw [inst0_inst] at second
        have secondEq : Equal Tower.rules Δ (tr d F (consSub (.fst x) σ) S S reflE (.snd x)) (.snd x)
            (inst0 (.fst x) (inst F (liftSub σ) (Presentation.rename wk S))) := by
          rw [inst0_inst]
          exact eqF first second
        have pairEq := Derivable.pairCong formedS (.sort _) (.refl first) secondEq
        exact .trans pairEq (eta_pair formedS (.sort _) familyFormed hx')
      exact ⟨fun hx => step true hx (fun hu hy => (ihF wfF (hσ.cons A hu) hS).1 hy),
        fun hx => step false hx (fun hu hy => (ihF wfF (hσ.cons A hu) hS).2 hy)⟩

/-- **The generated respect term is the identity along reflexivity**: for a code over `Γ`, a set
`S` and a member `m` of its family at `S`, `respOf c S S reflE m ≡ m` in the knowledge. -/
theorem respOf_refl {n : Nat} {Γ : Tower.Ctx n} {c : FamCode n} (wf : WF Γ c) {S M : Tower.Tm n}
    (hS : Typed Tower.rules Γ S setType) (hM : Typed Tower.rules Γ M (inst c ids S)) :
    Equal Tower.rules Γ (tr true c ids S S reflE M) M (inst c ids S) :=
  (tr_refl c wf (SubstMor.identity Γ) hS).1 hM

end EqualityOnTheStep.Options.Respect

#print axioms EqualityOnTheStep.Options.Respect.reflE_typed
#print axioms EqualityOnTheStep.Options.Respect.eta_lam
#print axioms EqualityOnTheStep.Options.Respect.eta_pair
#print axioms EqualityOnTheStep.Options.Respect.mem_refl_fwd_universal
#print axioms EqualityOnTheStep.Options.Respect.mem_refl_bwd_universal
#print axioms EqualityOnTheStep.Options.Respect.tr_refl
#print axioms EqualityOnTheStep.Options.Respect.respOf_refl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
