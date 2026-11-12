import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.RespectCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.BetaApplication

/-!
# Coherence of generated transport along transitivity

The composite of evidence `e : setEq S T` and `e' : setEq T U` is `compE e e'`, the closed term of
`SetTheory.setEq_trans` applied (`compE_typed`). Along it, the generated transport of a code is the
composite of the two transports **in the knowledge** (`tr_comp`): forward,
`tr c S U (compE e e') x ≡ tr c T U e' (tr c S T e x)`, and backward,
`tr c S U (compE e e') x ≡ tr c S T e (tr c T U e' x)`.

Three facts about the generator carry the proof:

* **substitution passes through it** (`tr_subst`), so a transport opened at a term is the transport
  of that term (`tr_open`);
* **it respects the knowledge's equality of its argument** (`tr_congr`), by functionality of
  substitution (`Typed.instantiateEq`);
* **it respects the knowledge's equality of a parameter and the argument together**
  (`tr_functional`), by `Typed.functional` on the transport opened at both.

Membership composes by β on the composite evidence (`mem_comp_fwd_universal`,
`mem_comp_bwd_universal`); functions compose through a β-redex that substitution reduces
(`beta_wk`, `arrow_reopen`); pairs and quantifiers compose componentwise; a dependent pair composes
through `tr_functional`, since its second component's parameter is its first component.

**The row a transport firing makes** is `respOf c S T E M` (`Respect.transport_by_code`). It
computes to `tr c S T E M` (`respOf_computes`), so it is the member along reflexivity
(`made_row_refl`) and the composite of the made rows along composite evidence (`made_row_comp`).

**The control** (`incoherent_respect`): typing does not force coherence. For the constant family
`Ground` over `p p' : Ground`, `λS T e m. p` is a respect term, and along reflexivity it does not
return the member `p'`, while the generated respect term does.
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

/-! ## Substitution passes through the generator -/

theorem proj_subst {m k : Nat} (τ : Presentation.Sub Tower.Head m k) (d : Bool) (p : Tower.Tm m) :
    subst τ (proj d p) = proj d (subst τ p) := by
  cases d
  · rfl
  · rfl

theorem subComp_liftSub_wkSub {n m k : Nat} (τ : Presentation.Sub Tower.Head m k)
    (σ : Presentation.Sub Tower.Head n m) : subComp (liftSub τ) (wkSub σ) = wkSub (subComp τ σ) :=
  funext fun i => subst_liftSub_wk τ (σ i)

theorem subComp_consSub {n m k : Nat} (τ : Presentation.Sub Tower.Head m k) (u : Tower.Tm m)
    (σ : Presentation.Sub Tower.Head n m) : subComp τ (consSub u σ) = consSub (subst τ u) (subComp τ σ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- **Substitution passes through the generator.** -/
theorem tr_subst {n : Nat} (c : FamCode n) :
    ∀ (d : Bool) {m k : Nat} (σ : Presentation.Sub Tower.Head n m) (τ : Presentation.Sub Tower.Head m k)
      (S T e x : Tower.Tm m),
      subst τ (tr d c σ S T e x) = tr d c (subComp τ σ) (subst τ S) (subst τ T) (subst τ e) (subst τ x) := by
  induction c with
  | mem a =>
      intro d m k σ τ S T e x
      simp only [tr, subst, proj_subst, subst_subComp]
  | const B =>
      intro d m k σ τ S T e x
      rfl
  | arrow F G ihF ihG =>
      intro d m k σ τ S T e x
      simp only [tr, subst, ihF, ihG, subComp_liftSub_wkSub, subst_liftSub_wk, liftSub_zero]
  | prod F G ihF ihG =>
      intro d m k σ τ S T e x
      simp only [tr, subst, ihF, ihG]
  | pi A F ihF =>
      intro d m k σ τ S T e x
      simp only [tr, subst, ihF, liftSub_subComp, subst_liftSub_wk, liftSub_zero]
  | sigma A F ihF =>
      intro d m k σ τ S T e x
      simp only [tr, subst, ihF, subComp_consSub]

/-- Opening an instance under a weakened substitution at a term. -/
theorem inst0_wk_inst {n m : Nat} (c : FamCode n) (σ : Presentation.Sub Tower.Head n m) (u S : Tower.Tm m) :
    inst0 u (inst c (wkSub σ) (Presentation.rename wk S)) = inst c σ S := by
  have same : subComp (subst0 u) (wkSub σ) = σ := funext fun i => inst0_rename_wk u (σ i)
  have back : subst (subst0 u) (Presentation.rename wk S) = S := inst0_rename_wk u S
  show subst (subst0 u) (inst c (wkSub σ) (Presentation.rename wk S)) = inst c σ S
  rw [inst_subst, same, back]

/-- **A transport opened at a term is the transport of that term.** -/
theorem tr_open {n m : Nat} (d : Bool) (c : FamCode n) (σ : Presentation.Sub Tower.Head n m)
    (S T e x : Tower.Tm m) :
    inst0 x (tr d c (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk T) (Presentation.rename wk e) (.var 0)) =
      tr d c σ S T e x := by
  have same : subComp (subst0 x) (wkSub σ) = σ := funext fun i => inst0_rename_wk x (σ i)
  show subst (subst0 x) (tr d c (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk T)
    (Presentation.rename wk e) (.var 0)) = tr d c σ S T e x
  have back : ∀ t : Tower.Tm m, subst (subst0 x) (Presentation.rename wk t) = t := fun t => inst0_rename_wk x t
  rw [tr_subst, same, back S, back T, back e]
  rfl

/-- **The generator respects the knowledge's equality of its argument.** -/
theorem tr_congr {n : Nat} (c : FamCode n) {Γ : Tower.Ctx n} (wf : WF Γ c) {m : Nat} {Δ : Tower.Ctx m}
    {σ : Presentation.Sub Tower.Head n m} (hσ : SubstMor Tower.rules Γ Δ σ) {S T e : Tower.Tm m}
    (hS : Typed Tower.rules Δ S setType) (hT : Typed Tower.rules Δ T setType)
    (he : Typed Tower.rules Δ e (setEq S T)) :
    (∀ {x x' : Tower.Tm m}, Typed Tower.rules Δ x (inst c σ S) → Equal Tower.rules Δ x x' (inst c σ S) →
      Equal Tower.rules Δ (tr true c σ S T e x) (tr true c σ S T e x') (inst c σ T)) ∧
    (∀ {x x' : Tower.Tm m}, Typed Tower.rules Δ x (inst c σ T) → Equal Tower.rules Δ x x' (inst c σ T) →
      Equal Tower.rules Δ (tr false c σ S T e x) (tr false c σ S T e x') (inst c σ S)) := by
  constructor
  · intro x x' hx same
    have v : Typed Tower.rules (.snoc Δ (inst c σ S)) (.var 0) (Presentation.rename wk (inst c σ S)) :=
      Derivable.var 0
    rw [inst_rename] at v
    have body := (tr_typed c wf (substMor_wk hσ (inst c σ S)) hS.weaken hT.weaken (evidence_weaken he)).1 v
    have moved := Typed.instantiateEq body hx same
    rw [tr_open, tr_open, inst0_wk_inst] at moved
    exact moved
  · intro x x' hx same
    have v : Typed Tower.rules (.snoc Δ (inst c σ T)) (.var 0) (Presentation.rename wk (inst c σ T)) :=
      Derivable.var 0
    rw [inst_rename] at v
    have body := (tr_typed c wf (substMor_wk hσ (inst c σ T)) hS.weaken hT.weaken (evidence_weaken he)).2 v
    have moved := Typed.instantiateEq body hx same
    rw [tr_open, tr_open, inst0_wk_inst] at moved
    exact moved

/-! ## The composite evidence -/

/-- **The composite of two pieces of evidence**:
`λX. (λp. fst (e' X) (fst (e X) p), λq. snd (e X) (snd (e' X) q))`. -/
def compE {m : Nat} (e e' : Tower.Tm m) : Tower.Tm m :=
  .lam (.pair
    (.lam (.app (.fst (.app (Presentation.rename wk (Presentation.rename wk e')) (.var 1)))
      (.app (.fst (.app (Presentation.rename wk (Presentation.rename wk e)) (.var 1))) (.var 0))))
    (.lam (.app (.snd (.app (Presentation.rename wk (Presentation.rename wk e)) (.var 1)))
      (.app (.snd (.app (Presentation.rename wk (Presentation.rename wk e')) (.var 1))) (.var 0)))))

theorem compE_rename {m k : Nat} (ρ : Presentation.Ren m k) (e e' : Tower.Tm m) :
    Presentation.rename ρ (compE e e') = compE (Presentation.rename ρ e) (Presentation.rename ρ e') := by
  simp only [compE, Presentation.rename, rename_liftRen_wk]
  rfl

/-- `S T U : U0 → U0, e : setEq S T, e' : setEq T U, a : U0`. -/
abbrev compCtx : Tower.Ctx 6 := .snoc SetTheory.transCtx5 U0

/-- And `x : S a`. -/
abbrev compFwdCtx : Tower.Ctx 7 := .snoc compCtx (.app (Presentation.rename wk (.var 4)) (.var 0))

/-- And `x : U a`. -/
abbrev compBwdCtx : Tower.Ctx 7 := .snoc compCtx (.app (Presentation.rename wk (.var 2)) (.var 0))

/-- `fst (e' a) (fst (e a) x)`. -/
def compFwdBody : Tower.Tm 7 := .app (.fst (.app (.var 2) (.var 1))) (.app (.fst (.app (.var 3) (.var 1))) (.var 0))

/-- `snd (e a) (snd (e' a) x)`. -/
def compBwdBody : Tower.Tm 7 := .app (.snd (.app (.var 3) (.var 1))) (.app (.snd (.app (.var 2) (.var 1))) (.var 0))

theorem compFwdBody_typed : Typed Tower.rules compFwdCtx compFwdBody (.app (.var 4) (.var 1)) := by
  have e1 := Derivable.var (R := Tower.rules) (Γ := compFwdCtx) 3
  have e2 := Derivable.var (R := Tower.rules) (Γ := compFwdCtx) 2
  have x1 := Derivable.var (R := Tower.rules) (Γ := compFwdCtx) 1
  have p0 := Derivable.var (R := Tower.rules) (Γ := compFwdCtx) 0
  have toT := Derivable.appElim (Derivable.fstElim (Derivable.appElim e1 x1)) p0
  exact Derivable.appElim (Derivable.fstElim (Derivable.appElim e2 x1)) toT

theorem compBwdBody_typed : Typed Tower.rules compBwdCtx compBwdBody (.app (.var 6) (.var 1)) := by
  have e1 := Derivable.var (R := Tower.rules) (Γ := compBwdCtx) 3
  have e2 := Derivable.var (R := Tower.rules) (Γ := compBwdCtx) 2
  have x1 := Derivable.var (R := Tower.rules) (Γ := compBwdCtx) 1
  have q0 := Derivable.var (R := Tower.rules) (Γ := compBwdCtx) 0
  have backT := Derivable.appElim (Derivable.sndElim (Derivable.appElim e2 x1)) q0
  exact Derivable.appElim (Derivable.sndElim (Derivable.appElim e1 x1)) backT

theorem compS_typed : Typed Tower.rules SetTheory.transCtx5 (.var 4) setType := Derivable.var 4

theorem compU_typed : Typed Tower.rules SetTheory.transCtx5 (.var 2) setType := Derivable.var 2

theorem compFirst_typed : Typed Tower.rules compCtx (.lam compFwdBody)
    (.pi (.app (.var 5) (.var 0)) (.app (.var 4) (.var 1))) :=
  .lamIntro (setEqForward_formed compS_typed compU_typed) (.sort _) compFwdBody_typed

theorem compSecond_typed : Typed Tower.rules compCtx (.lam compBwdBody)
    (.pi (.app (.var 3) (.var 0)) (.app (.var 6) (.var 1))) :=
  .lamIntro (setEqForward_formed compU_typed compS_typed) (.sort _) compBwdBody_typed

theorem compPair_typed : Typed Tower.rules compCtx (.pair (.lam compFwdBody) (.lam compBwdBody))
    (.sigma (.pi (.app (.var 5) (.var 0)) (.app (.var 4) (.var 1)))
      (.pi (.app (.var 4) (.var 1)) (.app (.var 7) (.var 2)))) :=
  .pairIntro (setEqBody_formed compS_typed compU_typed) (.sort _) compFirst_typed compSecond_typed

/-- **The composite evidence is typed**, in the universal frame. -/
theorem compE_universal : Typed Tower.rules SetTheory.transCtx5 (compE (.var 1) (.var 0)) (setEq (.var 4) (.var 2)) :=
  .lamIntro (setEq_formed compS_typed compU_typed) (.sort _) compPair_typed

/-- The substitution of the universal frame by three sets and two pieces of evidence. -/
theorem compSubst {m : Nat} {Δ : Tower.Ctx m} {S T U e e' : Tower.Tm m} (hS : Typed Tower.rules Δ S setType)
    (hT : Typed Tower.rules Δ T setType) (hU : Typed Tower.rules Δ U setType)
    (he : Typed Tower.rules Δ e (setEq S T)) (he' : Typed Tower.rules Δ e' (setEq T U)) :
    SubstMor Tower.rules SetTheory.transCtx5 Δ (consSub e' (consSub e (consSub U (consSub T (consSub S noSub))))) :=
  (((((noSub_typed Δ).cons setType hS).cons setType hT).cons setType hU).cons (setEq (.var 2) (.var 1)) he).cons
    (setEq (.var 2) (.var 1)) he'

/-- **The composite evidence is typed**: `compE e e' : setEq S U`. -/
theorem compE_typed {m : Nat} {Δ : Tower.Ctx m} {S T U e e' : Tower.Tm m} (hS : Typed Tower.rules Δ S setType)
    (hT : Typed Tower.rules Δ T setType) (hU : Typed Tower.rules Δ U setType)
    (he : Typed Tower.rules Δ e (setEq S T)) (he' : Typed Tower.rules Δ e' (setEq T U)) :
    Typed Tower.rules Δ (compE e e') (setEq S U) :=
  compE_universal.substitute (compSubst hS hT hU he he')

/-! ## Membership composes, in the universal frame -/

/-- The variables of the universal frame, read two binders further. -/
theorem compShift {Δx : Tower.Ctx 7} (formedAt : Δx = compFwdCtx ∨ Δx = compBwdCtx) :
    SubstMor Tower.rules SetTheory.transCtx5 Δx (wkSub (wkSub ids)) := by
  rcases formedAt with rfl | rfl
  · exact substMor_wk (substMor_wk (SubstMor.identity _) _) _
  · exact substMor_wk (substMor_wk (SubstMor.identity _) _) _

/-- The frame `compCtx` read in `Δx` at `a`. -/
theorem compAt {Δx : Tower.Ctx 7} (formedAt : Δx = compFwdCtx ∨ Δx = compBwdCtx) :
    SubstMor Tower.rules compCtx Δx (consSub (.var 1) (wkSub (wkSub ids))) := by
  have shifted := compShift formedAt
  rcases formedAt with rfl | rfl
  · exact shifted.cons U0 (Derivable.var 1)
  · exact shifted.cons U0 (Derivable.var 1)

/-- **β on the composite evidence at `a`.** -/
theorem comp_beta {Δx : Tower.Ctx 7} (formedAt : Δx = compFwdCtx ∨ Δx = compBwdCtx) :
    Equal Tower.rules Δx (.app (compE (.var 3) (.var 2)) (.var 1))
      (.pair (.lam (.app (.fst (.app (.var 3) (.var 2))) (.app (.fst (.app (.var 4) (.var 2))) (.var 0))))
        (.lam (.app (.snd (.app (.var 4) (.var 2))) (.app (.snd (.app (.var 3) (.var 2))) (.var 0)))))
      (.sigma (.pi (.app (.var 6) (.var 1)) (.app (.var 5) (.var 2)))
        (.pi (.app (.var 5) (.var 2)) (.app (.var 8) (.var 3)))) := by
  have shifted := compShift formedAt
  have body : Typed Tower.rules (.snoc Δx U0)
      (subst (liftSub (wkSub (wkSub ids))) (.pair (.lam compFwdBody) (.lam compBwdBody)))
      (subst (liftSub (wkSub (wkSub ids)))
        (.sigma (.pi (.app (.var 5) (.var 0)) (.app (.var 4) (.var 1)))
          (.pi (.app (.var 4) (.var 1)) (.app (.var 7) (.var 2))))) :=
    compPair_typed.substitute (shifted.lift U0)
  have formed : Typed Tower.rules Δx (setEq (.var 6) (.var 4)) (.head large) :=
    setEq_formed (compS_typed.substitute shifted) (compU_typed.substitute shifted)
  rcases formedAt with rfl | rfl
  · exact Derivable.betaPi formed (.sort _) body (Derivable.var 1)
  · exact Derivable.betaPi formed (.sort _) body (Derivable.var 1)

/-- **Forward membership along the composite is the composite**: `fst (compE e e' a) x ≡
fst (e' a) (fst (e a) x)`. -/
theorem mem_comp_fwd_universal :
    Equal Tower.rules compFwdCtx (.app (.fst (.app (compE (.var 3) (.var 2)) (.var 1))) (.var 0)) compFwdBody
      (.app (.var 4) (.var 1)) := by
  have at1 := compAt (Or.inl rfl)
  have firstT := compFirst_typed.substitute at1
  have secondT := compSecond_typed.substitute at1
  have sigmaFormed : Typed Tower.rules compFwdCtx
      (.sigma (.pi (.app (.var 6) (.var 1)) (.app (.var 5) (.var 2)))
        (.pi (.app (.var 5) (.var 2)) (.app (.var 8) (.var 3)))) (.head large) :=
    (setEqBody_formed compS_typed compU_typed).substitute at1 |>.cumul small_large
  have fstEq := Derivable.trans (Derivable.fstCong (comp_beta (Or.inl rfl)))
    (Derivable.betaFst sigmaFormed (.sort _) firstT secondT)
  have x : Typed Tower.rules compFwdCtx (.var 0) (.app (.var 6) (.var 1)) := Derivable.var 0
  have applied := Derivable.appCong fstEq (.refl x)
  have innerT : Typed Tower.rules (.snoc compFwdCtx (.app (.var 6) (.var 1)))
      (subst (liftSub (consSub (.var 1) (wkSub (wkSub ids)))) compFwdBody)
      (subst (liftSub (consSub (.var 1) (wkSub (wkSub ids)))) (.app (.var 4) (.var 1))) :=
    compFwdBody_typed.substitute (at1.lift _)
  have arrowFormed : Typed Tower.rules compFwdCtx (.pi (.app (.var 6) (.var 1)) (.app (.var 5) (.var 2))) U0 :=
    (setEqForward_formed compS_typed compU_typed).substitute at1
  have reduced := Derivable.betaPi arrowFormed (.sort _) innerT x
  exact .trans applied reduced

/-- **Backward membership along the composite is the composite**: `snd (compE e e' a) x ≡
snd (e a) (snd (e' a) x)`. -/
theorem mem_comp_bwd_universal :
    Equal Tower.rules compBwdCtx (.app (.snd (.app (compE (.var 3) (.var 2)) (.var 1))) (.var 0)) compBwdBody
      (.app (.var 6) (.var 1)) := by
  have at1 := compAt (Or.inr rfl)
  have firstT := compFirst_typed.substitute at1
  have secondT := compSecond_typed.substitute at1
  have sigmaFormed : Typed Tower.rules compBwdCtx
      (.sigma (.pi (.app (.var 6) (.var 1)) (.app (.var 5) (.var 2)))
        (.pi (.app (.var 5) (.var 2)) (.app (.var 8) (.var 3)))) (.head large) :=
    (setEqBody_formed compS_typed compU_typed).substitute at1 |>.cumul small_large
  have sndEq := Derivable.trans (Derivable.sndCong (comp_beta (Or.inr rfl)))
    (Derivable.betaSnd sigmaFormed (.sort _) firstT secondT)
  have x : Typed Tower.rules compBwdCtx (.var 0) (.app (.var 4) (.var 1)) := Derivable.var 0
  have applied := Derivable.appCong sndEq (.refl x)
  have innerT : Typed Tower.rules (.snoc compBwdCtx (.app (.var 4) (.var 1)))
      (subst (liftSub (consSub (.var 1) (wkSub (wkSub ids)))) compBwdBody)
      (subst (liftSub (consSub (.var 1) (wkSub (wkSub ids)))) (.app (.var 6) (.var 1))) :=
    compBwdBody_typed.substitute (at1.lift _)
  have arrowFormed : Typed Tower.rules compBwdCtx (.pi (.app (.var 4) (.var 1)) (.app (.var 7) (.var 2))) U0 :=
    (setEqForward_formed compU_typed compS_typed).substitute at1
  have reduced := Derivable.betaPi arrowFormed (.sort _) innerT x
  exact .trans applied reduced

/-! ## β on a weakened abstraction -/

/-- Opening a body weakened under its binder at a term `z` substitutes `z` for the bound variable. -/
theorem inst0_rename_liftRen {m : Nat} (z : Tower.Tm (m + 1)) (t : Tower.Tm (m + 1)) :
    inst0 z (Presentation.rename (liftRen wk) t) = subst (consSub z (wkSub (ids : Presentation.Sub Tower.Head m m))) t := by
  have same : (fun i => subst0 z (liftRen wk i)) = consSub z (wkSub (ids : Presentation.Sub Tower.Head m m)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  show subst (subst0 z) (Presentation.rename (liftRen wk) t) = _
  rw [subst_rename, same]

theorem subst_reopen {m : Nat} (z : Tower.Tm (m + 1)) (t : Tower.Tm m) :
    subst (consSub z (wkSub (ids : Presentation.Sub Tower.Head m m))) (Presentation.rename wk t) =
      Presentation.rename wk t := by
  rw [subst_consSub_rename_wk, ← rename_wk_eq]

theorem subComp_reopen {n m : Nat} (z : Tower.Tm (m + 1)) (σ : Presentation.Sub Tower.Head n m) :
    subComp (consSub z (wkSub (ids : Presentation.Sub Tower.Head m m))) (wkSub σ) = wkSub σ :=
  funext fun i => subst_reopen z (σ i)

/-- **The body of a generated function transport, reopened at a term.** -/
theorem arrow_reopen {n m : Nat} (d₁ d₂ : Bool) (F G : FamCode n) (σ : Presentation.Sub Tower.Head n m)
    (S T e x : Tower.Tm m) (z : Tower.Tm (m + 1)) :
    subst (consSub z (wkSub (ids : Presentation.Sub Tower.Head m m)))
        (tr d₁ G (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk T) (Presentation.rename wk e)
          (.app (Presentation.rename wk x)
            (tr d₂ F (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk T) (Presentation.rename wk e)
              (.var 0)))) =
      tr d₁ G (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk T) (Presentation.rename wk e)
        (.app (Presentation.rename wk x)
          (tr d₂ F (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk T) (Presentation.rename wk e) z)) := by
  simp only [tr_subst, subst, subComp_reopen, subst_reopen, consSub_zero]

/-- An instance at a weakened substitution and set is the weakened instance. -/
theorem inst_wk {n m : Nat} (c : FamCode n) (σ : Presentation.Sub Tower.Head n m) (S : Tower.Tm m) :
    inst c (wkSub σ) (Presentation.rename wk S) = Presentation.rename wk (inst c σ S) :=
  (inst_rename c σ wk S).symm

/-- **β on a weakened abstraction at a term.** -/
theorem beta_wk {m : Nat} {Δ : Tower.Ctx m} {A A' : Tower.Tm m} {D : Tower.Tm (m + 1)} {body : Tower.Tm (m + 1)}
    {u : Tower.Head} (formed : Typed Tower.rules Δ (.pi A D) (.head u)) (hu : Tower.rules.isUniverse u)
    (hB : Typed Tower.rules (.snoc Δ A) body D) {z : Tower.Tm (m + 1)}
    (hz : Typed Tower.rules (.snoc Δ A') z (Presentation.rename wk A)) :
    Equal Tower.rules (.snoc Δ A') (.app (Presentation.rename wk (.lam body)) z)
      (subst (consSub z (wkSub (ids : Presentation.Sub Tower.Head m m))) body)
      (inst0 z (Presentation.rename (liftRen wk) D)) := by
  have formedW : Typed Tower.rules (.snoc Δ A')
      (.pi (Presentation.rename wk A) (Presentation.rename (liftRen wk) D)) (.head u) := formed.weaken
  have bodyRen : Typed Tower.rules (.snoc (.snoc Δ A') (Presentation.rename wk A))
      (Presentation.rename (liftRen wk) body) (Presentation.rename (liftRen wk) D) :=
    hB.rename ((show CtxRen Δ (.snoc Δ A') wk from fun _ => rfl).snoc A)
  have beta := Derivable.betaPi formedW hu bodyRen hz
  rw [inst0_rename_liftRen z body] at beta
  exact beta

/-! ## Composition of generated transports -/

/-- **The generator respects the knowledge's equality of a parameter and of the argument**: for a
code under one more parameter `u : A`, the transports at `u` and at an equal `u'`, of equal
arguments, are equal. -/
theorem tr_functional {n : Nat} {A : Tower.Tm n} (F : FamCode (n + 1)) {Γ : Tower.Ctx n}
    (wfF : WF (.snoc Γ A) F) {m : Nat} {Δ : Tower.Ctx m} {σ : Presentation.Sub Tower.Head n m}
    (hσ : SubstMor Tower.rules Γ Δ σ) {S T e : Tower.Tm m} (hS : Typed Tower.rules Δ S setType)
    (hT : Typed Tower.rules Δ T setType) (he : Typed Tower.rules Δ e (setEq S T)) {u u' : Tower.Tm m}
    (hu : Typed Tower.rules Δ u (subst σ A)) (uu : Equal Tower.rules Δ u u' (subst σ A)) :
    (∀ {y y' : Tower.Tm m}, Typed Tower.rules Δ y (inst F (consSub u σ) S) →
        Equal Tower.rules Δ y y' (inst F (consSub u σ) S) →
        Equal Tower.rules Δ (tr true F (consSub u σ) S T e y) (tr true F (consSub u' σ) S T e y')
          (inst F (consSub u σ) T)) ∧
      (∀ {y y' : Tower.Tm m}, Typed Tower.rules Δ y (inst F (consSub u σ) T) →
        Equal Tower.rules Δ y y' (inst F (consSub u σ) T) →
        Equal Tower.rules Δ (tr false F (consSub u σ) S T e y) (tr false F (consSub u' σ) S T e y')
          (inst F (consSub u σ) S)) := by
  have hσA : SubstMor Tower.rules (.snoc Γ A) (.snoc Δ (subst σ A)) (liftSub σ) := hσ.lift A
  have reopenSub : ∀ w z : Tower.Tm m,
      subComp (consSub z (consSub w (ids : Presentation.Sub Tower.Head m m))) (wkSub (liftSub σ)) = consSub w σ := by
    intro w z
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · show subst (consSub z (consSub w ids)) (Presentation.rename wk (Presentation.rename wk (σ j))) = σ j
      rw [subst_consSub_rename_wk, subst_consSub_rename_wk, subst_ids]
  have reopenTerm : ∀ w z t : Tower.Tm m,
      subst (consSub z (consSub w (ids : Presentation.Sub Tower.Head m m)))
        (Presentation.rename wk (Presentation.rename wk t)) = t := by
    intro w z t
    rw [subst_consSub_rename_wk, subst_consSub_rename_wk, subst_ids]
  have openSub : ∀ w : Tower.Tm m,
      subComp (consSub w (ids : Presentation.Sub Tower.Head m m)) (liftSub σ) = consSub w σ := by
    intro w
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · show subst (consSub w ids) (Presentation.rename wk (σ j)) = σ j
      rw [subst_consSub_rename_wk, subst_ids]
  have openType : ∀ w X : Tower.Tm m,
      subst (consSub w (ids : Presentation.Sub Tower.Head m m)) (inst F (liftSub σ) (Presentation.rename wk X)) =
        inst F (consSub w σ) X := by
    intro w X
    rw [inst_subst, openSub, subst_consSub_rename_wk, subst_ids]
  have reopenType : ∀ w z X : Tower.Tm m,
      subst (consSub z (consSub w (ids : Presentation.Sub Tower.Head m m)))
        (inst F (wkSub (liftSub σ)) (Presentation.rename wk (Presentation.rename wk X))) = inst F (consSub w σ) X := by
    intro w z X
    rw [inst_subst, reopenSub, reopenTerm]
  have reopenTr : ∀ (d : Bool) (w z : Tower.Tm m),
      subst (consSub z (consSub w (ids : Presentation.Sub Tower.Head m m)))
        (tr d F (wkSub (liftSub σ)) (Presentation.rename wk (Presentation.rename wk S))
          (Presentation.rename wk (Presentation.rename wk T)) (Presentation.rename wk (Presentation.rename wk e))
          (.var 0)) = tr d F (consSub w σ) S T e z := by
    intro d w z
    rw [tr_subst, reopenSub, reopenTerm, reopenTerm, reopenTerm]
    rfl
  have pairEq : ∀ {X y y' : Tower.Tm m}, Typed Tower.rules Δ y (inst F (consSub u σ) X) →
      Equal Tower.rules Δ y y' (inst F (consSub u σ) X) →
      SubstEq Tower.rules (.snoc (.snoc Δ (subst σ A)) (inst F (liftSub σ) (Presentation.rename wk X))) Δ
        (consSub y (consSub u ids)) (consSub y' (consSub u' ids)) := by
    intro X y y' hy yy
    have first : SubstEq Tower.rules (.snoc Δ (subst σ A)) Δ (consSub u ids) (consSub u' ids) :=
      (SubstEq.reflexive (SubstMor.identity Δ)).cons (subst σ A) (by rw [subst_ids]; exact hu)
        (by rw [subst_ids]; exact uu)
    exact first.cons _ (by rw [openType]; exact hy) (by rw [openType]; exact yy)
  constructor
  · intro y y' hy yy
    have v : Typed Tower.rules (.snoc (.snoc Δ (subst σ A)) (inst F (liftSub σ) (Presentation.rename wk S))) (.var 0)
        (inst F (wkSub (liftSub σ)) (Presentation.rename wk (Presentation.rename wk S))) := by
      have v0 : Typed Tower.rules (.snoc (.snoc Δ (subst σ A)) (inst F (liftSub σ) (Presentation.rename wk S))) (.var 0)
          (Presentation.rename wk (inst F (liftSub σ) (Presentation.rename wk S))) := Derivable.var 0
      rw [inst_rename] at v0
      exact v0
    have body := (tr_typed F wfF (substMor_wk hσA _) hS.weaken.weaken hT.weaken.weaken
      (evidence_weaken (evidence_weaken he))).1 v
    have moved := body.functional (pairEq hy yy)
    rw [reopenTr, reopenTr, reopenType] at moved
    exact moved
  · intro y y' hy yy
    have v : Typed Tower.rules (.snoc (.snoc Δ (subst σ A)) (inst F (liftSub σ) (Presentation.rename wk T))) (.var 0)
        (inst F (wkSub (liftSub σ)) (Presentation.rename wk (Presentation.rename wk T))) := by
      have v0 : Typed Tower.rules (.snoc (.snoc Δ (subst σ A)) (inst F (liftSub σ) (Presentation.rename wk T))) (.var 0)
          (Presentation.rename wk (inst F (liftSub σ) (Presentation.rename wk T))) := Derivable.var 0
      rw [inst_rename] at v0
      exact v0
    have body := (tr_typed F wfF (substMor_wk hσA _) hS.weaken.weaken hT.weaken.weaken
      (evidence_weaken (evidence_weaken he))).2 v
    have moved := body.functional (pairEq hy yy)
    rw [reopenTr, reopenTr, reopenType] at moved
    exact moved

/-- **Coherence along composition** for a code at a substitution, three sets and two pieces of
evidence. -/
def CompCoherent {n m : Nat} (c : FamCode n) (Δ : Tower.Ctx m) (σ : Presentation.Sub Tower.Head n m)
    (S T U e e' : Tower.Tm m) : Prop :=
  (∀ {x : Tower.Tm m}, Typed Tower.rules Δ x (inst c σ S) →
      Equal Tower.rules Δ (tr true c σ S U (compE e e') x) (tr true c σ T U e' (tr true c σ S T e x)) (inst c σ U)) ∧
    (∀ {x : Tower.Tm m}, Typed Tower.rules Δ x (inst c σ U) →
      Equal Tower.rules Δ (tr false c σ S U (compE e e') x) (tr false c σ S T e (tr false c σ T U e' x)) (inst c σ S))

/-- The type `inst c σ S` read one binder further. -/
theorem var_inst {n m : Nat} (c : FamCode n) {Δ : Tower.Ctx m} (σ : Presentation.Sub Tower.Head n m)
    (S A : Tower.Tm m) (same : A = inst c σ S) :
    Typed Tower.rules (.snoc Δ A) (.var 0) (inst c (wkSub σ) (Presentation.rename wk S)) := by
  subst same
  have v : Typed Tower.rules (.snoc Δ (inst c σ S)) (.var 0) (Presentation.rename wk (inst c σ S)) := Derivable.var 0
  rw [inst_rename] at v
  exact v

/-- A function of `inst (arrow F G)`, read one binder further. -/
theorem fun_weaken {n m : Nat} (F G : FamCode n) {Δ : Tower.Ctx m} (σ : Presentation.Sub Tower.Head n m)
    (S A : Tower.Tm m) {x : Tower.Tm m} (hx : Typed Tower.rules Δ x (inst (.arrow F G) σ S)) :
    Typed Tower.rules (.snoc Δ A) (Presentation.rename wk x)
      (.pi (inst F (wkSub σ) (Presentation.rename wk S))
        (Presentation.rename wk (inst G (wkSub σ) (Presentation.rename wk S)))) := by
  have w : Typed Tower.rules (.snoc Δ A) (Presentation.rename wk x)
      (.pi (Presentation.rename wk (inst F σ S))
        (Presentation.rename (liftRen wk) (Presentation.rename wk (inst G σ S)))) := hx.weaken
  rw [rename_liftRen_wk, inst_rename F σ wk S, inst_rename G σ wk S] at w
  exact w

/-- **Along the composite of two pieces of evidence, the generated transport of every code is the
composite of the two transports**, in the knowledge, in both directions. -/
theorem tr_comp {n : Nat} (c : FamCode n) :
    ∀ {Γ : Tower.Ctx n}, WF Γ c → ∀ {m : Nat} {Δ : Tower.Ctx m} {σ : Presentation.Sub Tower.Head n m},
      SubstMor Tower.rules Γ Δ σ → ∀ {S T U e e' : Tower.Tm m}, Typed Tower.rules Δ S setType →
        Typed Tower.rules Δ T setType → Typed Tower.rules Δ U setType → Typed Tower.rules Δ e (setEq S T) →
          Typed Tower.rules Δ e' (setEq T U) → CompCoherent c Δ σ S T U e e' := by
  induction c with
  | sigma A F ihF =>
      intro Γ wf m Δ σ hσ S T U e e' hS hT hU he he'
      have formedS := inst_formed (.sigma A F) wf hσ hS
      have formedT := inst_formed (.sigma A F) wf hσ hT
      have formedU := inst_formed (.sigma A F) wf hσ hU
      obtain ⟨_, wfF⟩ := wf
      constructor
      · intro x hx
        have hx' : Typed Tower.rules Δ x (.sigma (subst σ A) (inst F (liftSub σ) (Presentation.rename wk S))) := hx
        have first : Typed Tower.rules Δ (.fst x) (subst σ A) := Derivable.fstElim hx'
        have second := Derivable.sndElim hx'
        rw [inst0_inst] at second
        have hσx := hσ.cons A first
        have y1T := (tr_typed F wfF hσx hS hT he).1 second
        have y1T' : Typed Tower.rules Δ (tr true F (consSub (.fst x) σ) S T e (.snd x))
            (inst0 (.fst x) (inst F (liftSub σ) (Presentation.rename wk T))) := by
          rw [inst0_inst]
          exact y1T
        have fstM := Derivable.betaFst formedT (.sort _) first y1T'
        have sndM := Derivable.betaSnd formedT (.sort _) first y1T'
        rw [inst0_inst] at sndM
        have funct := (tr_functional F wfF hσ hT hU he' first (.symm fstM)).1 y1T (.symm sndM)
        have eq2 := Derivable.trans ((ihF wfF hσx hS hT hU he he').1 second) funct
        have eq2' : Equal Tower.rules Δ (tr true F (consSub (.fst x) σ) S U (compE e e') (.snd x))
            (tr true F (consSub (.fst (tr true (.sigma A F) σ S T e x)) σ) T U e'
              (.snd (tr true (.sigma A F) σ S T e x)))
            (inst0 (.fst x) (inst F (liftSub σ) (Presentation.rename wk U))) := by
          rw [inst0_inst]
          exact eq2
        exact Derivable.pairCong formedU (.sort _) (.symm fstM) eq2'
      · intro x hx
        have hx' : Typed Tower.rules Δ x (.sigma (subst σ A) (inst F (liftSub σ) (Presentation.rename wk U))) := hx
        have first : Typed Tower.rules Δ (.fst x) (subst σ A) := Derivable.fstElim hx'
        have second := Derivable.sndElim hx'
        rw [inst0_inst] at second
        have hσx := hσ.cons A first
        have y1T := (tr_typed F wfF hσx hT hU he').2 second
        have y1T' : Typed Tower.rules Δ (tr false F (consSub (.fst x) σ) T U e' (.snd x))
            (inst0 (.fst x) (inst F (liftSub σ) (Presentation.rename wk T))) := by
          rw [inst0_inst]
          exact y1T
        have fstM := Derivable.betaFst formedT (.sort _) first y1T'
        have sndM := Derivable.betaSnd formedT (.sort _) first y1T'
        rw [inst0_inst] at sndM
        have funct := (tr_functional F wfF hσ hS hT he first (.symm fstM)).2 y1T (.symm sndM)
        have eq2 := Derivable.trans ((ihF wfF hσx hS hT hU he he').2 second) funct
        have eq2' : Equal Tower.rules Δ (tr false F (consSub (.fst x) σ) S U (compE e e') (.snd x))
            (tr false F (consSub (.fst (tr false (.sigma A F) σ T U e' x)) σ) S T e
              (.snd (tr false (.sigma A F) σ T U e' x)))
            (inst0 (.fst x) (inst F (liftSub σ) (Presentation.rename wk S))) := by
          rw [inst0_inst]
          exact eq2
        exact Derivable.pairCong formedS (.sort _) (.symm fstM) eq2'
  | mem a =>
      intro Γ wf m Δ σ hσ S T U e e' hS hT hU he he'
      have wfa : Typed Tower.rules Γ a U0 := wf
      have base := (compSubst hS hT hU he he').cons U0 (wfa.substitute hσ)
      exact ⟨fun hx => mem_comp_fwd_universal.substitute (base.cons _ hx),
        fun hx => mem_comp_bwd_universal.substitute (base.cons _ hx)⟩
  | const B =>
      intro Γ wf m Δ σ hσ S T U e e' hS hT hU he he'
      exact ⟨fun hx => .refl hx, fun hx => .refl hx⟩
  | prod F G ihF ihG =>
      intro Γ wf m Δ σ hσ S T U e e' hS hT hU he he'
      have formedS := inst_formed (.prod F G) wf hσ hS
      have formedT := inst_formed (.prod F G) wf hσ hT
      have formedU := inst_formed (.prod F G) wf hσ hU
      obtain ⟨wfF, wfG⟩ := wf
      have CF := ihF wfF hσ hS hT hU he he'
      have CG := ihG wfG hσ hS hT hU he he'
      constructor
      · intro x hx
        have hx' : Typed Tower.rules Δ x (.sigma (inst F σ S) (Presentation.rename wk (inst G σ S))) := hx
        have f1 : Typed Tower.rules Δ (.fst x) (inst F σ S) := Derivable.fstElim hx'
        have s1 := Derivable.sndElim hx'
        rw [inst0_rename_wk] at s1
        have a1 := (tr_typed F wfF hσ hS hT he).1 f1
        have b1 := (tr_typed G wfG hσ hS hT he).1 s1
        have b1' : Typed Tower.rules Δ (tr true G σ S T e (.snd x))
            (inst0 (tr true F σ S T e (.fst x)) (Presentation.rename wk (inst G σ T))) := by
          rw [inst0_rename_wk]
          exact b1
        have betaF := Derivable.betaFst formedT (.sort _) a1 b1'
        have betaG := Derivable.betaSnd formedT (.sort _) a1 b1'
        rw [inst0_rename_wk] at betaG
        have eq1 := Derivable.trans (CF.1 f1) ((tr_congr F wfF hσ hT hU he').1 a1 (.symm betaF))
        have eq2 := Derivable.trans (CG.1 s1) ((tr_congr G wfG hσ hT hU he').1 b1 (.symm betaG))
        have eq2' : Equal Tower.rules Δ (tr true G σ S U (compE e e') (.snd x))
            (tr true G σ T U e' (.snd (tr true (.prod F G) σ S T e x)))
            (inst0 (tr true F σ S U (compE e e') (.fst x)) (Presentation.rename wk (inst G σ U))) := by
          rw [inst0_rename_wk]
          exact eq2
        exact Derivable.pairCong formedU (.sort _) eq1 eq2'
      · intro x hx
        have hx' : Typed Tower.rules Δ x (.sigma (inst F σ U) (Presentation.rename wk (inst G σ U))) := hx
        have f1 : Typed Tower.rules Δ (.fst x) (inst F σ U) := Derivable.fstElim hx'
        have s1 := Derivable.sndElim hx'
        rw [inst0_rename_wk] at s1
        have a1 := (tr_typed F wfF hσ hT hU he').2 f1
        have b1 := (tr_typed G wfG hσ hT hU he').2 s1
        have b1' : Typed Tower.rules Δ (tr false G σ T U e' (.snd x))
            (inst0 (tr false F σ T U e' (.fst x)) (Presentation.rename wk (inst G σ T))) := by
          rw [inst0_rename_wk]
          exact b1
        have betaF := Derivable.betaFst formedT (.sort _) a1 b1'
        have betaG := Derivable.betaSnd formedT (.sort _) a1 b1'
        rw [inst0_rename_wk] at betaG
        have eq1 := Derivable.trans (CF.2 f1) ((tr_congr F wfF hσ hS hT he).2 a1 (.symm betaF))
        have eq2 := Derivable.trans (CG.2 s1) ((tr_congr G wfG hσ hS hT he).2 b1 (.symm betaG))
        have eq2' : Equal Tower.rules Δ (tr false G σ S U (compE e e') (.snd x))
            (tr false G σ S T e (.snd (tr false (.prod F G) σ T U e' x)))
            (inst0 (tr false F σ S U (compE e e') (.fst x)) (Presentation.rename wk (inst G σ S))) := by
          rw [inst0_rename_wk]
          exact eq2
        exact Derivable.pairCong formedS (.sort _) eq1 eq2'
  | pi A F ihF =>
      intro Γ wf m Δ σ hσ S T U e e' hS hT hU he he'
      have formedS := inst_formed (.pi A F) wf hσ hS
      have formedT := inst_formed (.pi A F) wf hσ hT
      have formedU := inst_formed (.pi A F) wf hσ hU
      obtain ⟨_, wfF⟩ := wf
      have hσ' := hσ.lift A
      have he₁ := evidence_weaken (A := subst σ A) he
      have he₂ := evidence_weaken (A := subst σ A) he'
      have CF := ihF wfF hσ' hS.weaken hT.weaken hU.weaken he₁ he₂
      constructor
      · intro x hx
        have w : Typed Tower.rules (.snoc Δ (subst σ A)) (Presentation.rename wk x)
            (.pi (Presentation.rename wk (subst σ A))
              (Presentation.rename (liftRen wk) (inst F (liftSub σ) (Presentation.rename wk S)))) := hx.weaken
        have arg := Derivable.appElim w (Derivable.var 0)
        rw [open_weakened] at arg
        have hB := (tr_typed F wfF hσ' hS.weaken hT.weaken he₁).1 arg
        have beta := beta_wk formedT (.sort _) hB
          (Derivable.var 0 : Typed Tower.rules (.snoc Δ (subst σ A)) (.var 0) (Presentation.rename wk (subst σ A)))
        rw [show consSub (.var 0 : Tower.Tm (m + 1)) (wkSub (ids : Presentation.Sub Tower.Head m m)) = ids from
          funext fun i => Fin.cases rfl (fun _ => rfl) i, subst_ids, open_weakened] at beta
        have step := Derivable.trans (CF.1 arg)
          ((tr_congr F wfF hσ' hT.weaken hU.weaken he₂).1 hB (.symm beta))
        rw [← compE_rename] at step
        exact Derivable.lamCong formedU (.sort _) step
      · intro x hx
        have w : Typed Tower.rules (.snoc Δ (subst σ A)) (Presentation.rename wk x)
            (.pi (Presentation.rename wk (subst σ A))
              (Presentation.rename (liftRen wk) (inst F (liftSub σ) (Presentation.rename wk U)))) := hx.weaken
        have arg := Derivable.appElim w (Derivable.var 0)
        rw [open_weakened] at arg
        have hB := (tr_typed F wfF hσ' hT.weaken hU.weaken he₂).2 arg
        have beta := beta_wk formedT (.sort _) hB
          (Derivable.var 0 : Typed Tower.rules (.snoc Δ (subst σ A)) (.var 0) (Presentation.rename wk (subst σ A)))
        rw [show consSub (.var 0 : Tower.Tm (m + 1)) (wkSub (ids : Presentation.Sub Tower.Head m m)) = ids from
          funext fun i => Fin.cases rfl (fun _ => rfl) i, subst_ids, open_weakened] at beta
        have step := Derivable.trans (CF.2 arg)
          ((tr_congr F wfF hσ' hS.weaken hT.weaken he₁).2 hB (.symm beta))
        rw [← compE_rename] at step
        exact Derivable.lamCong formedS (.sort _) step
  | arrow F G ihF ihG =>
      intro Γ wf m Δ σ hσ S T U e e' hS hT hU he he'
      have formedS := inst_formed (.arrow F G) wf hσ hS
      have formedT := inst_formed (.arrow F G) wf hσ hT
      have formedU := inst_formed (.arrow F G) wf hσ hU
      obtain ⟨wfF, wfG⟩ := wf
      constructor
      · intro x hx
        -- the frame of the bodies: `Δ, y : F U`
        have hσ' := substMor_wk hσ (inst F σ U)
        have hS' : Typed Tower.rules (.snoc Δ (inst F σ U)) (Presentation.rename wk S) setType := hS.weaken
        have hT' : Typed Tower.rules (.snoc Δ (inst F σ U)) (Presentation.rename wk T) setType := hT.weaken
        have hU' : Typed Tower.rules (.snoc Δ (inst F σ U)) (Presentation.rename wk U) setType := hU.weaken
        have he₁ := evidence_weaken (A := inst F σ U) he
        have he₂ := evidence_weaken (A := inst F σ U) he'
        have hE := compE_typed hS' hT' hU' he₁ he₂
        have CF := ihF wfF hσ' hS' hT' hU' he₁ he₂
        have CG := ihG wfG hσ' hS' hT' hU' he₁ he₂
        have v0 := var_inst F σ U (inst F σ U) rfl (Δ := Δ)
        have zT := (tr_typed F wfF hσ' hT' hU' he₂).2 v0
        have xw := fun_weaken F G σ S (inst F σ U) hx
        -- the left side's argument
        have leftArgT := Derivable.appElim xw ((tr_typed F wfF hσ' hS' hU' hE).2 v0)
        rw [inst0_rename_wk] at leftArgT
        -- the composite's argument
        have innerT := (tr_typed F wfF hσ' hS' hT' he₁).2 zT
        have YT := Derivable.appElim xw innerT
        rw [inst0_rename_wk] at YT
        have appEq := Derivable.appCong (.refl xw) (CF.2 v0)
        rw [inst0_rename_wk] at appEq
        have k1 := (tr_congr G wfG hσ' hS' hU' hE).1 leftArgT appEq
        have cG := CG.1 YT
        -- the body of the middle transport, over `Δ, y : F T`
        have hσT := substMor_wk hσ (inst F σ T)
        have he₁T := evidence_weaken (A := inst F σ T) he
        have v0T := var_inst F σ T (inst F σ T) rfl (Δ := Δ)
        have xwT := fun_weaken F G σ S (inst F σ T) hx
        have midArgT := Derivable.appElim xwT ((tr_typed F wfF hσT hS.weaken hT.weaken he₁T).2 v0T)
        rw [inst0_rename_wk] at midArgT
        have hB := (tr_typed G wfG hσT hS.weaken hT.weaken he₁T).1 midArgT
        rw [inst_wk] at hB
        have zT' : Typed Tower.rules (.snoc Δ (inst F σ U))
            (tr false F (wkSub σ) (Presentation.rename wk T) (Presentation.rename wk U) (Presentation.rename wk e') (.var 0))
            (Presentation.rename wk (inst F σ T)) := by
          rw [inst_rename]
          exact zT
        have beta := beta_wk formedT (.sort _) hB zT'
        rw [arrow_reopen, rename_liftRen_wk, inst0_rename_wk, inst_rename] at beta
        have QT := (tr_typed G wfG hσ' hS' hT' he₁).1 YT
        have k2 := (tr_congr G wfG hσ' hT' hU' he₂).1 QT (.symm beta)
        have chain := Derivable.trans k1 (Derivable.trans cG k2)
        rw [inst_wk, ← compE_rename] at chain
        exact Derivable.lamCong formedU (.sort _) chain
      · intro x hx
        have hσ' := substMor_wk hσ (inst F σ S)
        have hS' : Typed Tower.rules (.snoc Δ (inst F σ S)) (Presentation.rename wk S) setType := hS.weaken
        have hT' : Typed Tower.rules (.snoc Δ (inst F σ S)) (Presentation.rename wk T) setType := hT.weaken
        have hU' : Typed Tower.rules (.snoc Δ (inst F σ S)) (Presentation.rename wk U) setType := hU.weaken
        have he₁ := evidence_weaken (A := inst F σ S) he
        have he₂ := evidence_weaken (A := inst F σ S) he'
        have hE := compE_typed hS' hT' hU' he₁ he₂
        have CF := ihF wfF hσ' hS' hT' hU' he₁ he₂
        have CG := ihG wfG hσ' hS' hT' hU' he₁ he₂
        have v0 := var_inst F σ S (inst F σ S) rfl (Δ := Δ)
        have zT := (tr_typed F wfF hσ' hS' hT' he₁).1 v0
        have xw := fun_weaken F G σ U (inst F σ S) hx
        have leftArgT := Derivable.appElim xw ((tr_typed F wfF hσ' hS' hU' hE).1 v0)
        rw [inst0_rename_wk] at leftArgT
        have innerT := (tr_typed F wfF hσ' hT' hU' he₂).1 zT
        have YT := Derivable.appElim xw innerT
        rw [inst0_rename_wk] at YT
        have appEq := Derivable.appCong (.refl xw) (CF.1 v0)
        rw [inst0_rename_wk] at appEq
        have k1 := (tr_congr G wfG hσ' hS' hU' hE).2 leftArgT appEq
        have cG := CG.2 YT
        have hσT := substMor_wk hσ (inst F σ T)
        have he₂T := evidence_weaken (A := inst F σ T) he'
        have v0T := var_inst F σ T (inst F σ T) rfl (Δ := Δ)
        have xwT := fun_weaken F G σ U (inst F σ T) hx
        have midArgT := Derivable.appElim xwT ((tr_typed F wfF hσT hT.weaken hU.weaken he₂T).1 v0T)
        rw [inst0_rename_wk] at midArgT
        have hB := (tr_typed G wfG hσT hT.weaken hU.weaken he₂T).2 midArgT
        rw [inst_wk] at hB
        have zT' : Typed Tower.rules (.snoc Δ (inst F σ S))
            (tr true F (wkSub σ) (Presentation.rename wk S) (Presentation.rename wk T) (Presentation.rename wk e) (.var 0))
            (Presentation.rename wk (inst F σ T)) := by
          rw [inst_rename]
          exact zT
        have beta := beta_wk formedT (.sort _) hB zT'
        rw [arrow_reopen, rename_liftRen_wk, inst0_rename_wk, inst_rename] at beta
        have QT := (tr_typed G wfG hσ' hT' hU' he₂).2 YT
        have k2 := (tr_congr G wfG hσ' hS' hT' he₁).2 QT (.symm beta)
        have chain := Derivable.trans k1 (Derivable.trans cG k2)
        rw [inst_wk, ← compE_rename] at chain
        exact Derivable.lamCong formedS (.sort _) chain

/-- **The generated respect term composes**: for a code without dependent pairs over `Γ`, sets
`S`, `T`, `U`, evidence `e`, `e'` and a member `M` at `S`, transporting along `compE e e'` is
transporting along `e` and then along `e'`, in the knowledge. -/
theorem respOf_comp {n : Nat} {Γ : Tower.Ctx n} {c : FamCode n} (wf : WF Γ c)
    {S T U e e' M : Tower.Tm n} (hS : Typed Tower.rules Γ S setType) (hT : Typed Tower.rules Γ T setType)
    (hU : Typed Tower.rules Γ U setType) (he : Typed Tower.rules Γ e (setEq S T))
    (he' : Typed Tower.rules Γ e' (setEq T U)) (hM : Typed Tower.rules Γ M (inst c ids S)) :
    Equal Tower.rules Γ (tr true c ids S U (compE e e') M) (tr true c ids T U e' (tr true c ids S T e M))
      (inst c ids U) :=
  (tr_comp c wf (SubstMor.identity Γ) hS hT hU he he').1 hM

/-! ## The row a transport firing makes computes, and is coherent -/

/-- **The generated respect term computes to the generator**: applied to sets `S`, `T`, evidence
`E` and a member `M` of the family at `S`, `respOf c` is the transport `tr c S T E M`, in the
knowledge. -/
theorem respOf_computes {n : Nat} {Γ : Tower.Ctx n} {c : FamCode n} (wf : WF Γ c) {S T E M : Tower.Tm n}
    (hS : Typed Tower.rules Γ S setType) (hT : Typed Tower.rules Γ T setType)
    (hE : Typed Tower.rules Γ E (setEq S T)) (hM : Typed Tower.rules Γ M (.app (famOf c) S)) :
    Equal Tower.rules Γ (.app (.app (.app (.app (respOf c) S) T) E) M) (tr true c ids S T E M)
      (.app (famOf c) T) := by
  have tP := famOf_typed wf
  have three := betaPi_three (respType_formed tP) (.sort _) (respSecond_formed tP) (.sort _)
    (respThird_formed tP) (.sort _)
    (Derivable.lamIntro (respInner_formed tP) (.sort _) (respOf_body_typed wf)) hS hT hE
  have ρtyped : SubstMor Tower.rules (.snoc (.snoc (.snoc Γ setType) setType) (setEq (.var 1) (.var 0))) Γ
      (consSub E (consSub T (consSub S ids))) :=
    (((SubstMor.identity Γ).cons setType hS).cons setType hT).cons (setEq (.var 1) (.var 0)) hE
  have atS : subst (consSub E (consSub T (consSub S ids)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf c)))) (.var 2)) =
        .app (famOf c) S := by
    show Presentation.Tm.app (subst (consSub E (consSub T (consSub S ids)))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf c))))) S = .app (famOf c) S
    rw [subst_consSub_rename_wk, subst_consSub_rename_wk, subst_consSub_rename_wk, subst_ids]
  have hM' : Typed Tower.rules Γ M (subst (consSub E (consSub T (consSub S ids)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf c)))) (.var 2))) := by
    rw [atS]
    exact hM
  have fourth := Derivable.betaPi ((respInner_formed tP).substitute ρtyped) (.sort _)
    ((respOf_body_typed wf).substitute (ρtyped.lift _)) hM'
  have chain := Derivable.trans (Derivable.appCong three (.refl hM')) fourth
  rw [← subst_consSub, ← subst_consSub, tr_subst] at chain
  have shifted : subComp (consSub M (consSub E (consSub T (consSub S ids)))) (shift4 (n := n)) = ids := by
    funext i
    rfl
  have atT : subst (consSub M (consSub E (consSub T (consSub S ids))))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf c)))))
        (.var 2)) = .app (famOf c) T := by
    show Presentation.Tm.app (subst (consSub M (consSub E (consSub T (consSub S ids))))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf c)))))) T =
        .app (famOf c) T
    rw [subst_consSub_rename_wk, subst_consSub_rename_wk, subst_consSub_rename_wk, subst_consSub_rename_wk,
      subst_ids]
  rw [shifted, atT] at chain
  exact chain

/-- The family of a code applied to a set is its instance at the identity substitution. -/
theorem famOf_app {n : Nat} {Γ : Tower.Ctx n} {c : FamCode n} (wf : WF Γ c) {S : Tower.Tm n}
    (hS : Typed Tower.rules Γ S setType) :
    Equal Tower.rules Γ (.app (famOf c) S) (inst c ids S) (.head large) := by
  have same := famOf_subst_app wf (SubstMor.identity Γ) hS
  rw [subst_ids] at same
  exact same

/-- **Along reflexivity, the row the transport firing makes is the member**, in the knowledge. -/
theorem made_row_refl {n : Nat} {Γ : Tower.Ctx n} {c : FamCode n} (wf : WF Γ c) {S M : Tower.Tm n}
    (hS : Typed Tower.rules Γ S setType) (hM : Typed Tower.rules Γ M (.app (famOf c) S)) :
    Equal Tower.rules Γ (.app (.app (.app (.app (respOf c) S) S) reflE) M) M (.app (famOf c) S) := by
  have typeEq := famOf_app wf hS
  have computes := respOf_computes wf hS hS (reflE_typed hS) hM
  have identity := (tr_refl c wf (SubstMor.identity Γ) hS).1 (.conv hM typeEq (.sort _))
  exact .trans computes (.convEq identity (.symm typeEq) (.sort _))

/-- **Along composite evidence, the row the transport firing makes is the composite of the rows
made along the two pieces of evidence**, in the knowledge, over a formed context. -/
theorem made_row_comp {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) {c : FamCode n}
    (wf : WF Γ c) {S T U e e' M : Tower.Tm n} (hS : Typed Tower.rules Γ S setType)
    (hT : Typed Tower.rules Γ T setType) (hU : Typed Tower.rules Γ U setType)
    (he : Typed Tower.rules Γ e (setEq S T)) (he' : Typed Tower.rules Γ e' (setEq T U))
    (hM : Typed Tower.rules Γ M (.app (famOf c) S)) :
    Equal Tower.rules Γ (.app (.app (.app (.app (respOf c) S) U) (compE e e')) M)
      (.app (.app (.app (.app (respOf c) T) U) e') (.app (.app (.app (.app (respOf c) S) T) e) M))
      (.app (famOf c) U) := by
  have typeS := famOf_app wf hS
  have typeT := famOf_app wf hT
  have typeU := famOf_app wf hU
  have hM' : Typed Tower.rules Γ M (inst c ids S) := .conv hM typeS (.sort _)
  have inner := respOf_computes wf hS hT he hM
  have innerTyped := (Derivable.presupposed setting.levels inner formed).1
  have outer := respOf_computes wf hT hU he' innerTyped
  have left := respOf_computes wf hS hU (compE_typed hS hT hU he he') hM
  have composed := (tr_comp c wf (SubstMor.identity Γ) hS hT hU he he').1 hM'
  have trST := (tr_typed c wf (SubstMor.identity Γ) hS hT he).1 hM'
  have innerEq : Equal Tower.rules Γ (tr true c ids S T e M) (.app (.app (.app (.app (respOf c) S) T) e) M)
      (inst c ids T) := .convEq (.symm inner) typeT (.sort _)
  have congr := (tr_congr c wf (SubstMor.identity Γ) hT hU he').1 trST innerEq
  have chainU := Derivable.trans composed congr
  exact .trans left (.trans (.convEq chainU (.symm typeU) (.sort _)) (.symm outer))

/-! ## The control: a typed respect term need not be coherent -/

/-- The frame `p p' : Ground`. -/
abbrev twoPoints : Context Tower.rules := extend point (groundType _)

/-- The constant family `Ground`, over `p p' : Ground`. -/
def groundCode : FamCode twoPoints.arity := .const ground

theorem groundCode_wf : WF twoPoints.raw groundCode :=
  (Derivable.cumul (ground_typed _) small_large : Typed Tower.rules twoPoints.raw ground (.head large))

/-- `λS T e m. p`: a term that ignores the member and the evidence. -/
def badRespect : Tower.Tm twoPoints.arity := .lam (.lam (.lam (.lam (.var 5))))

/-- Its body is typed: `p : Ground`, and the family at `T` is `Ground` in the knowledge. -/
theorem badBody_typed :
    Typed Tower.rules
      (.snoc (.snoc (.snoc (.snoc twoPoints.raw setType) setType) (setEq (.var 1) (.var 0)))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf groundCode)))) (.var 2)))
      (.var 5)
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (famOf groundCode))))) (.var 2)) := by
  have hσ : SubstMor Tower.rules twoPoints.raw
      (.snoc (.snoc (.snoc (.snoc twoPoints.raw setType) setType) (setEq (.var 1) (.var 0)))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf groundCode)))) (.var 2)))
      shift4 :=
    substMor_wk (substMor_wk (substMor_wk (substMor_wk (SubstMor.identity _) _) _) _) _
  have hT : Typed Tower.rules
      (.snoc (.snoc (.snoc (.snoc twoPoints.raw setType) setType) (setEq (.var 1) (.var 0)))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf groundCode)))) (.var 2)))
      (.var 2) setType := Derivable.var 2
  have atT := famOf_subst_app groundCode_wf hσ hT
  rw [← rename_four] at atT
  have p : Typed Tower.rules
      (.snoc (.snoc (.snoc (.snoc twoPoints.raw setType) setType) (setEq (.var 1) (.var 0)))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf groundCode)))) (.var 2)))
      (.var 5) ground := Derivable.var 5
  exact .conv p (.symm atT) (.sort _)

/-- **`λS T e m. p` is a respect term** of the constant family `Ground`. -/
theorem badRespect_typed : Typed Tower.rules twoPoints.raw badRespect (respType (famOf groundCode)) := by
  have tP := famOf_typed groundCode_wf
  exact .lamIntro (respType_formed tP) (.sort _) (.lamIntro (respSecond_formed tP) (.sort _)
    (.lamIntro (respThird_formed tP) (.sort _) (.lamIntro (respInner_formed tP) (.sort _) badBody_typed)))

/-- **Along reflexivity it returns `p`, whatever the member.** -/
theorem badRespect_computes :
    Equal Tower.rules twoPoints.raw (.app (.app (.app (.app badRespect sCode) sCode) reflE) (.var 0)) (.var 1)
      (.app (famOf groundCode) sCode) := by
  have tP := famOf_typed groundCode_wf
  have hS : Typed Tower.rules twoPoints.raw sCode setType := s_typed _
  have hE : Typed Tower.rules twoPoints.raw reflE (setEq sCode sCode) := reflE_typed hS
  have hM : Typed Tower.rules twoPoints.raw (.var 0) (.app (famOf groundCode) sCode) :=
    .conv (Derivable.var 0) (.symm (famOf_app groundCode_wf hS)) (.sort _)
  have three := betaPi_three (respType_formed tP) (.sort _) (respSecond_formed tP) (.sort _)
    (respThird_formed tP) (.sort _) (Derivable.lamIntro (respInner_formed tP) (.sort _) badBody_typed) hS hS hE
  have ρtyped : SubstMor Tower.rules (.snoc (.snoc (.snoc twoPoints.raw setType) setType) (setEq (.var 1) (.var 0)))
      twoPoints.raw (consSub reflE (consSub sCode (consSub sCode ids))) :=
    (((SubstMor.identity _).cons setType hS).cons setType hS).cons (setEq (.var 1) (.var 0)) hE
  have atS : subst (consSub reflE (consSub sCode (consSub sCode ids)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf groundCode)))) (.var 2)) =
        .app (famOf groundCode) sCode := by
    show Presentation.Tm.app (subst (consSub reflE (consSub sCode (consSub sCode ids)))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf groundCode))))) sCode =
        .app (famOf groundCode) sCode
    rw [subst_consSub_rename_wk, subst_consSub_rename_wk, subst_consSub_rename_wk, subst_ids]
  have hM' : Typed Tower.rules twoPoints.raw (.var 0) (subst (consSub reflE (consSub sCode (consSub sCode ids)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (famOf groundCode)))) (.var 2))) := by
    rw [atS]
    exact hM
  have fourth := Derivable.betaPi ((respInner_formed tP).substitute ρtyped) (.sort _)
    (badBody_typed.substitute (ρtyped.lift _)) hM'
  have chain := Derivable.trans (Derivable.appCong three (.refl hM')) fourth
  rw [← subst_consSub, ← subst_consSub] at chain
  have atT : subst (consSub (.var 0) (consSub reflE (consSub sCode (consSub sCode ids))))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (famOf groundCode))))) (.var 2)) = .app (famOf groundCode) sCode := by
    show Presentation.Tm.app (subst (consSub (.var 0) (consSub reflE (consSub sCode (consSub sCode ids))))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (famOf groundCode)))))) sCode = .app (famOf groundCode) sCode
    rw [subst_consSub_rename_wk, subst_consSub_rename_wk, subst_consSub_rename_wk, subst_consSub_rename_wk,
      subst_ids]
  rw [atT] at chain
  exact chain

/-- **A typed respect term need not be coherent**: `λS T e m. p` is a respect term of the constant
family `Ground` over `p p' : Ground`, and along reflexivity it does not return the member `p'`; the
generated respect term of the same family does (`made_row_refl`). Coherence is a property of the
generated terms, not a consequence of typing. -/
theorem incoherent_respect :
    Typed Tower.rules twoPoints.raw badRespect (respType (famOf groundCode)) ∧
      ¬ Equal Tower.rules twoPoints.raw (.app (.app (.app (.app badRespect sCode) sCode) reflE) (.var 0)) (.var 0)
          (.app (famOf groundCode) sCode) ∧
      Equal Tower.rules twoPoints.raw (.app (.app (.app (.app (respOf groundCode) sCode) sCode) reflE) (.var 0)) (.var 0)
          (.app (famOf groundCode) sCode) := by
  have hS : Typed Tower.rules twoPoints.raw sCode setType := s_typed _
  have hM : Typed Tower.rules twoPoints.raw (.var 0) (.app (famOf groundCode) sCode) :=
    .conv (Derivable.var 0) (.symm (famOf_app groundCode_wf hS)) (.sort _)
  refine ⟨badRespect_typed, fun coherent => ?_, made_row_refl groundCode_wf hS hM⟩
  have both := Derivable.trans (.symm badRespect_computes) coherent
  have atGround : Equal Tower.rules twoPoints.raw (.var 1) (.var 0) ground :=
    .convEq both (famOf_app groundCode_wf hS) (.sort _)
  exact Quotient.vars_apart twoPoints.formed (by decide) atGround

end EqualityOnTheStep.Options.Respect

#print axioms EqualityOnTheStep.Options.Respect.arrow_reopen
#print axioms EqualityOnTheStep.Options.Respect.beta_wk
#print axioms EqualityOnTheStep.Options.Respect.tr_functional
#print axioms EqualityOnTheStep.Options.Respect.tr_comp
#print axioms EqualityOnTheStep.Options.Respect.respOf_comp
#print axioms EqualityOnTheStep.Options.Respect.respOf_computes
#print axioms EqualityOnTheStep.Options.Respect.made_row_refl
#print axioms EqualityOnTheStep.Options.Respect.made_row_comp
#print axioms EqualityOnTheStep.Options.Respect.badRespect_typed
#print axioms EqualityOnTheStep.Options.Respect.badRespect_computes
#print axioms EqualityOnTheStep.Options.Respect.incoherent_respect
#print axioms EqualityOnTheStep.Options.Respect.tr_subst
#print axioms EqualityOnTheStep.Options.Respect.tr_open
#print axioms EqualityOnTheStep.Options.Respect.tr_congr
#print axioms EqualityOnTheStep.Options.Respect.compE_typed
#print axioms EqualityOnTheStep.Options.Respect.mem_comp_fwd_universal
#print axioms EqualityOnTheStep.Options.Respect.mem_comp_bwd_universal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
