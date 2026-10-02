import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.FormFacts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RootPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Coherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Facts

/-!
# From the annotated facts to the facts about the weak-head forms of a package's types

The facts about the weak-head forms of a rule package's types (`Normalization.FormFacts`)
follow from the annotated facts (`CFormFacts`) of an annotation of the package whose root
steps preserve types and whose typed terms have strongly normalizing erasures, given three
properties relating the package to its annotation:

* **types lift**: every type of a formed context of the package is the erasure of a type
  of a formed annotated context erasing to it;
* **equations of types lift**: likewise for two equal types, at one annotated context;
* **annotated types progress**: a type of a universe of a formed annotated context takes an
  annotated weak-head step, or its erasure is in weak-head form.

The transfer (`FormFacts.ofAnnotated`):

* **matching annotated forms erase to matching forms** (`CFormsMatch.erase`), which gives
  the matching of equal types in weak-head form;
* an annotated weak-head step erases to a step of the package's directed reduction
  (`CWhStepR.erase_reduces`), so annotated weak-head steps from a term with a strongly
  normalizing erasure terminate (`CWhStepR.acc_of_sn`);
* an annotated weak-head step of a typed term is an equality at its type
  (`CWhStepR.equal`), given the injectivity and no-confusion of the annotated type formers
  and the preservation of types by root steps;
* so a type of a universe reduces, typed, to a type whose erasure is in weak-head form
  (`CTyped.reduces_typeForm`), and the reduction erases to a typed weak-head reduction of
  the package.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (Roles IsTypeForm FormsMatch FormFacts RedTy TypeEq IsType CtxFormed WhStep
  LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## Matching forms erase to matching forms -/

section Erasure

variable {P : ChurchRules R} {roles : Roles Head} {n : Nat} {Γ : CCtx Head n}

/-- Equal annotated types erase to equal types. -/
theorem CTypeEq.erase {A B : CTm Head n} (equal : CTypeEq P Γ A B) :
    TypeEq R Γ.erase A.erase B.erase := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, hu, CDerivable.erase e⟩

/-- **Matching annotated forms erase to matching forms**: formers with equal components,
one type constant of an inductive type, or two neutral types. -/
theorem CFormsMatch.erase {A B : CTm Head n} (m : CFormsMatch P roles Γ A B) :
    FormsMatch R roles Γ.erase A.erase B.erase := by
  rcases m with m | ⟨T, ctors, role, rfl, rfl⟩ | ⟨nA, nB⟩
  · rcases m with ⟨h, h', rfl, rfl, same⟩ | ⟨A₁, B₁, A₂, B₂, rfl, rfl, eA, eB⟩ |
      ⟨A₁, B₁, A₂, B₂, rfl, rfl, eA, eB⟩ | ⟨C, x, y, C', x', y', rfl, rfl, eC, ex, ey⟩
    · exact .inl ⟨h, h', rfl, rfl, same⟩
    · exact .inr (.inl ⟨_, _, _, _, rfl, rfl, eA.erase, eB.erase⟩)
    · exact .inr (.inr (.inl ⟨_, _, _, _, rfl, rfl, eA.erase, eB.erase⟩))
    · exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, eC.erase, CDerivable.erase ex,
        CDerivable.erase ey⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨T, ctors, role, rfl, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨nA, nB⟩))))

end Erasure

/-! ## Annotated weak-head steps terminate -/

section Termination

variable {P : ChurchRules R} {roles : Roles Head}

/-- A step of the directed reduction in the function position of a spine. -/
theorem reduces_appSpine {n : Nat} : ∀ (args : List (Tm Head n)) {f f' : Tm Head n},
    StrongNormalization.Reduces R f f' → StrongNormalization.Reduces R (Normalization.appSpine f args) (Normalization.appSpine f' args)
  | [], _, _, step => step
  | _ :: args, _, _, step => reduces_appSpine args (.congAppFun step)

/-- A step of the directed reduction at one argument of a spine. -/
theorem reduces_appSpine_arg {n : Nat} {f : Tm Head n} (before after : List (Tm Head n))
    {x y : Tm Head n} (step : StrongNormalization.Reduces R x y) :
    StrongNormalization.Reduces R (Normalization.appSpine f (before ++ x :: after))
      (Normalization.appSpine f (before ++ y :: after)) := by
  rw [Normalization.appSpine_append, Normalization.appSpine_append]
  exact reduces_appSpine after (.congAppArg step)

/-- **An annotated weak-head step erases to one step of the package's directed
reduction.** -/
theorem CWhStepR.erase_reduces {n : Nat} {t u : CTm Head n} (step : CWhStepR P roles t u) :
    StrongNormalization.Reduces R t.erase u.erase := by
  induction step with
  | beta A body a =>
      rw [CTm.erase_inst0]
      exact .betaPi _ _
  | fstPair a b => exact .betaSigmaFst _ _
  | sndPair a b => exact .betaSigmaSnd _ _
  | root s => exact .root (P.erase_step s)
  | appFun _ ih => exact .congAppFun ih
  | fst _ ih => exact .congFst ih
  | snd _ ih => exact .congSnd ih
  | scrutinee _ _ _ ih =>
      rw [CTm.erase_appSpine, CTm.erase_appSpine, List.map_append, List.map_append,
        List.map_cons, List.map_cons]
      exact reduces_appSpine_arg _ _ ih

/-- **Annotated weak-head steps from a term with a strongly normalizing erasure
terminate.** -/
theorem CWhStepR.acc_of_sn {n : Nat} {t : CTm Head n} (sn : StrongNormalization.SN R t.erase) :
    Acc (fun u t => CWhStepR P roles t u) t :=
  Subrelation.accessible (fun step => CWhStepR.erase_reduces step)
    (InvImage.accessible CTm.erase sn)

end Termination

/-! ## Subject reduction of annotated weak-head steps -/

/-- A spine at a list with an argument in the middle is the spine at the arguments after
it of the application of the spine before it. -/
theorem CTm.appSpine_append_cons {n : Nat} (f : CTm Head n) (before after : List (CTm Head n))
    (a : CTm Head n) :
    CTm.appSpine f (before ++ a :: after) = CTm.appSpine (.app (CTm.appSpine f before) a) after := by
  simp [CTm.appSpine, List.foldl_append]

section SubjectReduction

variable {L : Type} [LevelOrder L] {P : ChurchRules R} {roles : Roles Head}

/-- Terms whose instances in an application are equal wherever typed have equal spines at
every further list of arguments, wherever typed. -/
theorem CEqual.appSpine_congr {n : Nat} {Γ : CCtx Head n} :
    ∀ (args : List (CTm Head n)) {g g' T : CTm Head n},
      (∀ {S : CTm Head n}, CTyped P Γ g S → CEqual P Γ g g' S) →
      CTyped P Γ (CTm.appSpine g args) T →
        CEqual P Γ (CTm.appSpine g args) (CTm.appSpine g' args) T
  | [], _, _, _, hyp, typing => hyp typing
  | a :: args, g, g', _, hyp, typing =>
      CEqual.appSpine_congr args (g := .app g a) (g' := .app g' a) (fun {S} tS => by
        obtain ⟨A, B, tf, ta, le⟩ := tS.generation
        exact CEqual.subsume (.appCong (hyp tf) (.refl ta)) le) typing

variable (facts : CFormerFacts P) (levels : LevelModel R L) (admitted : CRootAdmitted P)
include facts levels admitted

/-- **Subject reduction of annotated weak-head steps**: a step of a typed term of a formed
context is an equality at its type. -/
theorem CWhStepR.equal {n : Nat} {Γ : CCtx Head n} {t u T : CTm Head n}
    (formed : CCtxFormed P Γ) (step : CWhStepR P roles t u) (typing : CTyped P Γ t T) :
    CEqual P Γ t u T := by
  induction step generalizing T with
  | beta D body a => exact CTyped.beta_equal facts levels formed typing
  | fstPair a b => exact CTyped.fstPair_equal facts levels formed typing
  | sndPair a b => exact CTyped.sndPair_equal facts levels formed typing
  | root s => exact admitted formed s typing
  | appFun _ ih =>
      obtain ⟨A, B, tf, ta, le⟩ := typing.generation
      exact CEqual.subsume (.appCong (ih tf) (.refl ta)) le
  | fst _ ih =>
      obtain ⟨A, B, tp, le⟩ := typing.generation
      exact CEqual.subsume (.fstCong (ih tp)) le
  | snd _ ih =>
      obtain ⟨A, B, tp, le⟩ := typing.generation
      exact CEqual.subsume (.sndCong (ih tp)) le
  | @scrutinee c arity before after a a' _ _ _ ih =>
      rw [CTm.appSpine_append_cons, CTm.appSpine_append_cons] at *
      exact CEqual.appSpine_congr after (fun {S} tS => by
        obtain ⟨A, B, tf, ta, le⟩ := tS.generation
        exact CEqual.subsume (.appCong (.refl tf) (ih ta)) le) typing

/-- **A type of a universe reduces, typed, to a type whose erasure is in weak-head form**,
when the annotated weak-head steps from it terminate and every type of the universe takes
a step or has an erasure in weak-head form. -/
theorem CTyped.reduces_typeForm {n : Nat} {Γ : CCtx Head n} {u : Head} (formed : CCtxFormed P Γ)
    (progress : ∀ {A : CTm Head n}, CTyped P Γ A (.head u) →
      (∃ A', CWhStepR P roles A A') ∨ IsTypeForm roles A.erase) :
    ∀ {A : CTm Head n}, Acc (fun v t => CWhStepR P roles t v) A → CTyped P Γ A (.head u) →
      ∃ A', Relation.ReflTransGen (CWhStepR P roles) A A' ∧ CTyped P Γ A' (.head u) ∧
        CEqual P Γ A A' (.head u) ∧ IsTypeForm roles A'.erase := by
  intro A acc
  induction acc with
  | intro A _ ih =>
      intro tA
      rcases progress tA with ⟨A₁, step⟩ | form
      · have e := CWhStepR.equal facts levels admitted formed step tA
        have tA₁ := (CEqual.typed levels e formed).2
        obtain ⟨A', red, tA', e', form⟩ := ih A₁ step tA₁
        exact ⟨A', .head step red, tA', .trans e e', form⟩
      · exact ⟨A, .refl, tA, .refl tA, form⟩

end SubjectReduction

end Annotated

/-! ## The transfer -/

namespace Normalization

open Annotated
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head} {L : Type} [LevelOrder L] {P : ChurchRules R}
  {roles : Roles Head}

/-- **The facts about the weak-head forms of a package's types, from the annotated facts.**
Let the annotation `P` of the package have the annotated facts, root steps that preserve
types, and typed terms with strongly normalizing erasures. If the package's types and
equations of types lift to `P`, and the types of `P` progress, the package has the facts
about the weak-head forms of its types. -/
theorem FormFacts.ofAnnotated (levels : LevelModel R L) (facts : CFormFacts P roles)
    (admitted : CRootAdmitted P)
    (sn : ∀ {n : Nat} {Γ : CCtx Head n} {t A : CTm Head n}, CCtxFormed P Γ → CTyped P Γ t A →
      StrongNormalization.SN R t.erase)
    (liftType : ∀ {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}, CtxFormed R Γ → IsType R Γ A →
      ∃ (Γ' : CCtx Head n) (A' : CTm Head n), CCtxFormed P Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧
        CIsType P Γ' A')
    (liftTypeEq : ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}, CtxFormed R Γ →
      TypeEq R Γ A B → ∃ (Γ' : CCtx Head n) (A' B' : CTm Head n), CCtxFormed P Γ' ∧
        Γ'.erase = Γ ∧ A'.erase = A ∧ B'.erase = B ∧ CTypeEq P Γ' A' B')
    (progress : ∀ {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {u : Head}, CCtxFormed P Γ →
      R.isUniverse u → CTyped P Γ A (.head u) →
        (∃ A', CWhStepR P roles A A') ∨ IsTypeForm roles A.erase) :
    FormFacts R roles where
  typeForm := by
    intro n Γ A isA formed
    obtain ⟨Γ', A', formed', rfl, rfl, u, hu, tA⟩ := liftType formed isA
    obtain ⟨A'', red, tA'', e, form⟩ := CTyped.reduces_typeForm facts.formers levels admitted
      formed' (fun tB => progress formed' hu tB) (CWhStepR.acc_of_sn (sn formed' tA)) tA
    exact ⟨A''.erase, ⟨Relation.ReflTransGen.lift CTm.erase (fun _ _ h => CWhStepR.erase h) _ _ red,
      u, hu, CDerivable.erase tA, CDerivable.erase tA'', CDerivable.erase e⟩, form⟩
  forms := by
    intro n Γ A B equal formed formA formB
    obtain ⟨Γ', A', B', formed', rfl, rfl, rfl, equal'⟩ := liftTypeEq formed equal
    exact (facts.forms equal' formed' formA formB).erase

end Normalization

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
