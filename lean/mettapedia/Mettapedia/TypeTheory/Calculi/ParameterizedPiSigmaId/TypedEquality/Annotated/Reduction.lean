import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Judgment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Candidates

/-!
# Reduction of annotated terms, and its erasure

`CStepCore` is one contextual step of annotated terms: β for functions and both
projections of pairs, the declared annotated root steps and head equality,
under every former, including inside the domain of an abstraction. Erasure maps
a step to one step of the rule package, or to no step when the step is inside a
domain (`CStepCore.erase`); annotated conversion therefore erases to the rule
package's conversion (`CConv.erase`).

`CWhStep` contracts a β-redex or a projection of a pair at the head of a term:
in function position of applications and under projections. It is the only
reduction coherence of annotations needs. It erases to a weak-head step of every
rule package (`CWhStep.erase_whStep`) and to one step of its directed reduction
(`CWhStep.erase_reduces`). Two terms with one erasure take such steps in
lockstep (`CWhStep.lockstep`).

Every annotated term has a head redex of this kind, or is an elimination of a
variable or a constant (`CSpine`), an introduction or a type former (`CIntro`),
or an elimination of an introduction of the wrong kind (`CStuck`): `CTm.classify`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (WhStep)

variable {Head : Type}

/-! ## Contextual steps -/

/-- One contextual step of annotated terms. -/
inductive CStepCore (root : CRootComputation Head) (headEq : Head → Head → Prop) :
    {n : Nat} → CTm Head n → CTm Head n → Prop
  | betaPi {n : Nat} (A : CTm Head n) (body : CTm Head (n + 1)) (a : CTm Head n) :
      CStepCore root headEq (.app (.lam A body) a) (CTm.inst0 a body)
  | betaSigmaFst {n : Nat} (a b : CTm Head n) : CStepCore root headEq (.fst (.pair a b)) a
  | betaSigmaSnd {n : Nat} (a b : CTm Head n) : CStepCore root headEq (.snd (.pair a b)) b
  | head {n : Nat} {l r : Head} : headEq l r →
      CStepCore root headEq (.head l : CTm Head n) (.head r)
  | root {n : Nat} {l r : CTm Head n} : root.step l r → CStepCore root headEq l r
  | congPiDom {n : Nat} {A A' : CTm Head n} {B : CTm Head (n + 1)} :
      CStepCore root headEq A A' → CStepCore root headEq (.pi A B) (.pi A' B)
  | congPiCod {n : Nat} {A : CTm Head n} {B B' : CTm Head (n + 1)} :
      CStepCore root headEq B B' → CStepCore root headEq (.pi A B) (.pi A B')
  | congSigmaDom {n : Nat} {A A' : CTm Head n} {B : CTm Head (n + 1)} :
      CStepCore root headEq A A' → CStepCore root headEq (.sigma A B) (.sigma A' B)
  | congSigmaCod {n : Nat} {A : CTm Head n} {B B' : CTm Head (n + 1)} :
      CStepCore root headEq B B' → CStepCore root headEq (.sigma A B) (.sigma A B')
  | congIdTy {n : Nat} {A A' a b : CTm Head n} :
      CStepCore root headEq A A' → CStepCore root headEq (.id A a b) (.id A' a b)
  | congIdLeft {n : Nat} {A a a' b : CTm Head n} :
      CStepCore root headEq a a' → CStepCore root headEq (.id A a b) (.id A a' b)
  | congIdRight {n : Nat} {A a b b' : CTm Head n} :
      CStepCore root headEq b b' → CStepCore root headEq (.id A a b) (.id A a b')
  /-- A step inside the domain of an abstraction. -/
  | congLamDom {n : Nat} {A A' : CTm Head n} {body : CTm Head (n + 1)} :
      CStepCore root headEq A A' → CStepCore root headEq (.lam A body) (.lam A' body)
  | congLam {n : Nat} {A : CTm Head n} {body body' : CTm Head (n + 1)} :
      CStepCore root headEq body body' → CStepCore root headEq (.lam A body) (.lam A body')
  | congAppFun {n : Nat} {f f' a : CTm Head n} :
      CStepCore root headEq f f' → CStepCore root headEq (.app f a) (.app f' a)
  | congAppArg {n : Nat} {f a a' : CTm Head n} :
      CStepCore root headEq a a' → CStepCore root headEq (.app f a) (.app f a')
  | congPairFst {n : Nat} {a a' b : CTm Head n} :
      CStepCore root headEq a a' → CStepCore root headEq (.pair a b) (.pair a' b)
  | congPairSnd {n : Nat} {a b b' : CTm Head n} :
      CStepCore root headEq b b' → CStepCore root headEq (.pair a b) (.pair a b')
  | congFst {n : Nat} {p p' : CTm Head n} :
      CStepCore root headEq p p' → CStepCore root headEq (.fst p) (.fst p')
  | congSnd {n : Nat} {p p' : CTm Head n} :
      CStepCore root headEq p p' → CStepCore root headEq (.snd p) (.snd p')
  | congRefl {n : Nat} {a a' : CTm Head n} :
      CStepCore root headEq a a' → CStepCore root headEq (.refl a) (.refl a')

/-- Annotated conversion: the equivalence closure of the contextual steps. -/
abbrev CConv (root : CRootComputation Head) (headEq : Head → Head → Prop) {n : Nat}
    (l r : CTm Head n) : Prop :=
  Relation.EqvGen (CStepCore root headEq) l r

private theorem reflGen_map {α β : Type} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (h : ∀ {a b}, r a b → s (f a) (f b)) {a b : α} (g : Relation.ReflGen r a b) :
    Relation.ReflGen s (f a) (f b) := by
  cases g with
  | refl => exact .refl
  | single step => exact .single (h step)

private theorem reflGen_eqvGen {α : Type} {r : α → α → Prop} {a b : α}
    (g : Relation.ReflGen r a b) : Relation.EqvGen r a b := by
  cases g with
  | refl => exact .refl _
  | single step => exact .rel _ _ step

variable {R : Rules Head}

/-- **Erasure of a step**: one step of the rule package, or none for a step
inside a domain. -/
theorem CStepCore.erase {P : ChurchRules R} {headEq : Head → Head → Prop} {n : Nat}
    {t u : CTm Head n} (step : CStepCore P.computation headEq t u) :
    Relation.ReflGen (StepCore R.computation headEq) t.erase u.erase := by
  induction step with
  | betaPi A body a =>
      rw [CTm.erase_inst0]
      exact .single (.betaPi _ _)
  | betaSigmaFst a b => exact .single (.betaSigmaFst _ _)
  | betaSigmaSnd a b => exact .single (.betaSigmaSnd _ _)
  | head e => exact .single (.head e)
  | root s => exact .single (.root (P.erase_step s))
  | congPiDom _ ih => exact reflGen_map (fun X => Tm.pi X _) .congPiDom ih
  | congPiCod _ ih => exact reflGen_map (fun X => Tm.pi _ X) .congPiCod ih
  | congSigmaDom _ ih => exact reflGen_map (fun X => Tm.sigma X _) .congSigmaDom ih
  | congSigmaCod _ ih => exact reflGen_map (fun X => Tm.sigma _ X) .congSigmaCod ih
  | congIdTy _ ih => exact reflGen_map (fun X => Tm.id X _ _) .congIdTy ih
  | congIdLeft _ ih => exact reflGen_map (fun X => Tm.id _ X _) .congIdLeft ih
  | congIdRight _ ih => exact reflGen_map (fun X => Tm.id _ _ X) .congIdRight ih
  | congLamDom _ _ => exact .refl
  | congLam _ ih => exact reflGen_map (fun X => Tm.lam X) .congLam ih
  | congAppFun _ ih => exact reflGen_map (fun X => Tm.app X _) .congAppFun ih
  | congAppArg _ ih => exact reflGen_map (fun X => Tm.app _ X) .congAppArg ih
  | congPairFst _ ih => exact reflGen_map (fun X => Tm.pair X _) .congPairFst ih
  | congPairSnd _ ih => exact reflGen_map (fun X => Tm.pair _ X) .congPairSnd ih
  | congFst _ ih => exact reflGen_map (fun X => Tm.fst X) .congFst ih
  | congSnd _ ih => exact reflGen_map (fun X => Tm.snd X) .congSnd ih
  | congRefl _ ih => exact reflGen_map (fun X => Tm.refl X) .congRefl ih

/-- Annotated conversion erases to the rule package's conversion. -/
theorem CConv.erase {P : ChurchRules R} {headEq : Head → Head → Prop} {n : Nat}
    {t u : CTm Head n} (conv : CConv P.computation headEq t u) :
    Conv headEq t.erase u.erase R.computation := by
  induction conv with
  | rel _ _ step => exact reflGen_eqvGen step.erase
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- A step inside a domain has no erasure: the identity at two convertible
domains erases to one term. -/
theorem CStepCore.erase_congLamDom {P : ChurchRules R} {headEq : Head → Head → Prop} {n : Nat}
    {A A' : CTm Head n} {body : CTm Head (n + 1)} (_step : CStepCore P.computation headEq A A') :
    (CTm.lam A body).erase = (CTm.lam A' body).erase :=
  rfl

/-! ## Head steps of functions and pairs -/

/-- A β-redex or a projection of a pair contracted at the head: in function
position of applications and under projections. No root step. -/
inductive CWhStep : {n : Nat} → CTm Head n → CTm Head n → Prop
  | beta {n : Nat} (A : CTm Head n) (body : CTm Head (n + 1)) (a : CTm Head n) :
      CWhStep (.app (.lam A body) a) (CTm.inst0 a body)
  | fstPair {n : Nat} (a b : CTm Head n) : CWhStep (.fst (.pair a b)) a
  | sndPair {n : Nat} (a b : CTm Head n) : CWhStep (.snd (.pair a b)) b
  | appFun {n : Nat} {f f' a : CTm Head n} : CWhStep f f' → CWhStep (.app f a) (.app f' a)
  | fst {n : Nat} {p p' : CTm Head n} : CWhStep p p' → CWhStep (.fst p) (.fst p')
  | snd {n : Nat} {p p' : CTm Head n} : CWhStep p p' → CWhStep (.snd p) (.snd p')

namespace CWhStep

/-- A head step is a contextual step. -/
theorem stepCore {root : CRootComputation Head} {headEq : Head → Head → Prop} {n : Nat}
    {t u : CTm Head n} (step : CWhStep t u) : CStepCore root headEq t u := by
  induction step with
  | beta A body a => exact .betaPi A body a
  | fstPair a b => exact .betaSigmaFst a b
  | sndPair a b => exact .betaSigmaSnd a b
  | appFun _ ih => exact .congAppFun ih
  | fst _ ih => exact .congFst ih
  | snd _ ih => exact .congSnd ih

/-- A head step erases to a weak-head step of every rule package. -/
theorem erase_whStep {roles : Normalization.Roles Head} {n : Nat} {t u : CTm Head n}
    (step : CWhStep t u) : WhStep R roles t.erase u.erase := by
  induction step with
  | beta A body a =>
      rw [CTm.erase_inst0]
      exact .beta _ _
  | fstPair a b => exact .fstPair _ _
  | sndPair a b => exact .sndPair _ _
  | appFun _ ih => exact .appFun ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

/-- A head step erases to one step of the directed reduction of every rule
package. -/
theorem erase_reduces {n : Nat} {t u : CTm Head n} (step : CWhStep t u) :
    StrongNormalization.Reduces R t.erase u.erase := by
  induction step with
  | beta A body a =>
      rw [CTm.erase_inst0]
      exact .betaPi _ _
  | fstPair a b => exact .betaSigmaFst _ _
  | sndPair a b => exact .betaSigmaSnd _ _
  | appFun _ ih => exact .congAppFun ih
  | fst _ ih => exact .congFst ih
  | snd _ ih => exact .congSnd ih

/-- **Lockstep**: a term with the erasure of a term taking a head step takes a
head step to a term with the erasure of the other's reduct. -/
theorem lockstep {n : Nat} {t u t' : CTm Head n} (step : CWhStep t u)
    (same : t.erase = t'.erase) : ∃ u', CWhStep t' u' ∧ u.erase = u'.erase := by
  induction step generalizing t' with
  | beta A body a =>
      obtain ⟨f', a', rfl, ef, ea⟩ := CTm.erase_eq_app same.symm
      obtain ⟨A', body', rfl, eb⟩ := CTm.erase_eq_lam ef
      refine ⟨_, .beta A' body' a', ?_⟩
      simp only [CTm.erase_inst0, eb, ea]
  | fstPair a b =>
      obtain ⟨p', rfl, ep⟩ := CTm.erase_eq_fst same.symm
      obtain ⟨a', b', rfl, ea, _⟩ := CTm.erase_eq_pair ep
      exact ⟨_, .fstPair a' b', ea.symm⟩
  | sndPair a b =>
      obtain ⟨p', rfl, ep⟩ := CTm.erase_eq_snd same.symm
      obtain ⟨a', b', rfl, _, eb⟩ := CTm.erase_eq_pair ep
      exact ⟨_, .sndPair a' b', eb.symm⟩
  | appFun _ ih =>
      obtain ⟨f', a', rfl, ef, ea⟩ := CTm.erase_eq_app same.symm
      obtain ⟨f'', step, e⟩ := ih ef.symm
      refine ⟨_, .appFun step, ?_⟩
      simp only [CTm.erase, e, ea]
  | fst _ ih =>
      obtain ⟨p', rfl, ep⟩ := CTm.erase_eq_fst same.symm
      obtain ⟨p'', step, e⟩ := ih ep.symm
      exact ⟨_, .fst step, by simp only [CTm.erase, e]⟩
  | snd _ ih =>
      obtain ⟨p', rfl, ep⟩ := CTm.erase_eq_snd same.symm
      obtain ⟨p'', step, e⟩ := ih ep.symm
      exact ⟨_, .snd step, by simp only [CTm.erase, e]⟩

end CWhStep

/-! ## The shapes of annotated terms -/

/-- Eliminations of a variable or a constant: applications and projections
whose head is a variable or a constant. -/
inductive CSpine : {n : Nat} → CTm Head n → Prop
  | var {n : Nat} (i : Fin n) : CSpine (.var i)
  | const {n : Nat} (c : DeclName) : CSpine (.const c : CTm Head n)
  | app {n : Nat} {f a : CTm Head n} : CSpine f → CSpine (.app f a)
  | fst {n : Nat} {p : CTm Head n} : CSpine p → CSpine (.fst p)
  | snd {n : Nat} {p : CTm Head n} : CSpine p → CSpine (.snd p)

/-- Introductions and type formers: the terms that are not eliminations. -/
inductive CIntro : {n : Nat} → CTm Head n → Prop
  | head {n : Nat} (h : Head) : CIntro (.head h : CTm Head n)
  | pi {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) : CIntro (.pi A B)
  | sigma {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) : CIntro (.sigma A B)
  | id {n : Nat} (A a b : CTm Head n) : CIntro (.id A a b)
  | lam {n : Nat} (A : CTm Head n) (b : CTm Head (n + 1)) : CIntro (.lam A b)
  | pair {n : Nat} (a b : CTm Head n) : CIntro (.pair a b)
  | refl {n : Nat} (a : CTm Head n) : CIntro (.refl a)

/-- Eliminations that are stuck on an introduction they do not eliminate: an
application of anything but an abstraction, a projection of anything but a
pair. -/
inductive CStuck : {n : Nat} → CTm Head n → Prop
  | app {n : Nat} {f a : CTm Head n} : CIntro f → (∀ A b, f ≠ .lam A b) → CStuck (.app f a)
  | fst {n : Nat} {p : CTm Head n} : CIntro p → (∀ a b, p ≠ .pair a b) → CStuck (.fst p)
  | snd {n : Nat} {p : CTm Head n} : CIntro p → (∀ a b, p ≠ .pair a b) → CStuck (.snd p)
  | appStuck {n : Nat} {f a : CTm Head n} : CStuck f → CStuck (.app f a)
  | fstStuck {n : Nat} {p : CTm Head n} : CStuck p → CStuck (.fst p)
  | sndStuck {n : Nat} {p : CTm Head n} : CStuck p → CStuck (.snd p)

/-- Every term has a head redex, or is a spine, stuck, or an introduction. -/
theorem CTm.classify {n : Nat} (t : CTm Head n) :
    (∃ u, CWhStep t u) ∨ CSpine t ∨ CStuck t ∨ CIntro t := by
  induction t with
  | var i => exact .inr (.inl (.var i))
  | const c => exact .inr (.inl (.const c))
  | head h => exact .inr (.inr (.inr (.head h)))
  | pi A B => exact .inr (.inr (.inr (.pi A B)))
  | sigma A B => exact .inr (.inr (.inr (.sigma A B)))
  | id A a b => exact .inr (.inr (.inr (.id A a b)))
  | lam A b => exact .inr (.inr (.inr (.lam A b)))
  | pair a b => exact .inr (.inr (.inr (.pair a b)))
  | refl a => exact .inr (.inr (.inr (.refl a)))
  | app f a ihf _ =>
      rcases ihf with ⟨f', step⟩ | spine | stuck | intro
      · exact .inl ⟨_, .appFun step⟩
      · exact .inr (.inl (.app spine))
      · exact .inr (.inr (.inl (.appStuck stuck)))
      · cases intro with
        | lam A b => exact .inl ⟨_, .beta A b a⟩
        | head h => exact .inr (.inr (.inl (.app (.head h) (fun _ _ e => by cases e))))
        | pi A B => exact .inr (.inr (.inl (.app (.pi A B) (fun _ _ e => by cases e))))
        | sigma A B => exact .inr (.inr (.inl (.app (.sigma A B) (fun _ _ e => by cases e))))
        | id A x y => exact .inr (.inr (.inl (.app (.id A x y) (fun _ _ e => by cases e))))
        | pair x y => exact .inr (.inr (.inl (.app (.pair x y) (fun _ _ e => by cases e))))
        | refl x => exact .inr (.inr (.inl (.app (.refl x) (fun _ _ e => by cases e))))
  | fst p ih =>
      rcases ih with ⟨p', step⟩ | spine | stuck | intro
      · exact .inl ⟨_, .fst step⟩
      · exact .inr (.inl (.fst spine))
      · exact .inr (.inr (.inl (.fstStuck stuck)))
      · cases intro with
        | pair x y => exact .inl ⟨_, .fstPair x y⟩
        | head h => exact .inr (.inr (.inl (.fst (.head h) (fun _ _ e => by cases e))))
        | pi A B => exact .inr (.inr (.inl (.fst (.pi A B) (fun _ _ e => by cases e))))
        | sigma A B => exact .inr (.inr (.inl (.fst (.sigma A B) (fun _ _ e => by cases e))))
        | id A x y => exact .inr (.inr (.inl (.fst (.id A x y) (fun _ _ e => by cases e))))
        | lam A b => exact .inr (.inr (.inl (.fst (.lam A b) (fun _ _ e => by cases e))))
        | refl x => exact .inr (.inr (.inl (.fst (.refl x) (fun _ _ e => by cases e))))
  | snd p ih =>
      rcases ih with ⟨p', step⟩ | spine | stuck | intro
      · exact .inl ⟨_, .snd step⟩
      · exact .inr (.inl (.snd spine))
      · exact .inr (.inr (.inl (.sndStuck stuck)))
      · cases intro with
        | pair x y => exact .inl ⟨_, .sndPair x y⟩
        | head h => exact .inr (.inr (.inl (.snd (.head h) (fun _ _ e => by cases e))))
        | pi A B => exact .inr (.inr (.inl (.snd (.pi A B) (fun _ _ e => by cases e))))
        | sigma A B => exact .inr (.inr (.inl (.snd (.sigma A B) (fun _ _ e => by cases e))))
        | id A x y => exact .inr (.inr (.inl (.snd (.id A x y) (fun _ _ e => by cases e))))
        | lam A b => exact .inr (.inr (.inl (.snd (.lam A b) (fun _ _ e => by cases e))))
        | refl x => exact .inr (.inr (.inl (.snd (.refl x) (fun _ _ e => by cases e))))

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
