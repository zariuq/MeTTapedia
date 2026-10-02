import Mettapedia.GSLT.Scope.SimpleFragmentExecutable
import Mettapedia.GSLT.Scope.Interaction
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSpineLift
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectConfluence

/-!
# Beck–Chevalley squares on the simple fragment

Erasure translates the simple fragment into the candidate's raw terms.  With
an observer on each side, a square of scope changes is formed: translating
(preimage along erasure) and forgetting (saturating by an observer).  The
scope algebra's law (`forget_translate_comm_iff`) says the square commutes
for every class exactly when erasure satisfies the forth and back laws for
the two observers; the back law is Beck–Chevalley for the observer views
(`forget_translate_views_comm_iff`) and the weak-pullback condition
(`back_iff_isWeakPullback`).  `square_of_laws` and `square_fails_of_back`
read a square in all three forms at once.

**Which squares commute.**

| simple observer | raw observer | raw terms | forth | back |
|---|---|---|---|---|
| β | the tower's conversion | all | yes | no (`back_beta_raw_fails`) |
| β | the package's conversion | all | yes | no (`back_beta_rawExec_fails`) |
| β | the tower's conversion | erasures of every type | yes | no (`back_beta_slice_fails`) |
| β | the tower's conversion | erasures of the type | yes | yes (`beta_typedSlice_comm`) |
| β | the package's conversion | erasures of the type | yes | yes (`beta_typedSliceExec_comm`) |
| βη | typed η-equality | typed raw terms | yes | no (`back_betaEta_typedRaw_fails`) |
| βη | typed η-equality | erasures of the type | yes | yes (`betaEta_typedSlice_comm`) |
| β | typed η-equality | erasures of the type | yes | no (`back_beta_equal_fails`) |
| βη | the tower's conversion | erasures of the type | no (`forth_betaEta_conv_fails`) | — |

The witnesses:
* the self-application `(λx. x x) (λy. y)` converts to the erased identity and
  erases no simple term of any type (`selfApplication_not_erasure`);
* `λy. (λx. y) (λw. y w)` erases a simple term of type
  `(atom → atom) → (atom → atom)` and reduces to the erased identity, but
  erases no simple term of type `atom → atom`: subject expansion fails
  (`expansion_not_erasure`);
* `fst (pair id id)` is typed at the erased type and typed-equal to the
  erased identity, and is not an erasure (`fstPair_not_erasure`);
* the η pair is typed-equal and not β-convertible (`eta_not_betaConv`).

**Conservativity without choice.**  Two simple terms of one type with one
erasure are β-convertible (`betaConv_of_erase_eq`): strong normalization
pulled back from the executable package, and the back law of erasure.  With
the executable package's Church–Rosser theorem this gives the conservativity
of the tower's conversion (`towerConv_iff_betaConv'`) and of the package's
directed conversion (`execConv_iff_betaConv`) on erasures of one type,
without the choice used by the normalizer. For the package with its
proposition codes, the package's proved Church–Rosser theorem gives the same
unconditional conservativity (`betaConv_of_objectConv`).

**The typed η-equality on erasures is βη** (`equal_iff_betaEtaConv`).
Soundness holds for every package with the simple formation rules
(`equal_of_betaEtaConv`).  Completeness: the executable package's
conversion algorithm is complete for its typed equality, and on erasures at
an erased type it can only compare as the βη-algorithm of the simple
fragment does (`algorithm_erasure`).  For the package with its proposition
codes, completeness follows from the facts about the weak-head forms of its
types (`betaEtaConv_of_equal_object`).

**Forgetting on both sides.**  Forgetting from β to βη on the simple side and
from the candidate's conversion to the typed η-equality on the raw side
commutes with translating (`forget_translate_both`).  Forgetting on one side
only breaks the back law or the forth law, both at the η pair.  Descent
transfers along the commuting squares (`observable_preimage`,
`observable_of_preimage`): the raw predicate "the simple preimage has
β-normal form `t`" is visible to the candidate's conversion
(`sliceNormalForm_observable_conv`) and not to its typed η-equality
(`sliceNormalForm_not_observable_equal`), the raw counterpart of
`normalFormPredicate_not_observable_betaEta`; the β-class gives the same
split without choice (`sliceBetaClass_observable_conv`,
`sliceBetaClass_not_observable_equal`), and the denotation is visible to the
typed η-equality (`sliceDenotation_observable_equal`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.SimpleFragmentBeckChevalley

open Set
open Mettapedia.Logic.TheoryModel
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
  (Derivable Typed Equal Algorithm AlgorithmStatement)
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TypedEqualityEmbedding
open Mettapedia.GSLT.Scope.SimpleFragment
open Mettapedia.GSLT.Scope.SimpleFragmentExecutable

/-- Extensional (βη) conversion of intrinsic simple terms. -/
abbrev BetaEtaConv {Γ : List Ty} {A : Ty} (left right : Term Γ A) : Prop :=
  Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Conv left right

/-! ## Shapes of spines -/

section Shapes

variable {n : ℕ}

/-- A constant or an application. -/
def ConstOrApp (t : Presentation.Tower.Tm n) : Prop :=
  (∃ c, t = .const c) ∨ ∃ f a, t = .app f a

theorem constOrApp_foldl :
    ∀ (args : List (Presentation.Tower.Tm n)) {f : Presentation.Tower.Tm n},
      ConstOrApp f → ConstOrApp (args.foldl Presentation.Tm.app f)
  | [], _, shape => shape
  | a :: rest, f, _ => constOrApp_foldl rest (.inr ⟨f, a, rfl⟩)

theorem constOrApp_appSpine (c : Presentation.DeclName) (args : List (Presentation.Tower.Tm n)) :
    ConstOrApp (Presentation.TypedEquality.Normalization.appSpine (.const c) args) :=
  constOrApp_foldl args (.inl ⟨c, rfl⟩)

end Shapes

/-! ## Erased types do not move -/

section Types

variable {R : Presentation.Rules Presentation.Tower.Head}

/-- **An erased simple type takes no step other than to itself**, in a package
whose root steps start at applications of constants and whose head equality
relates the ground head only to itself. -/
theorem eraseTypeAt_step (spine : Presentation.TypedEquality.StrongNormalization.SpineHeaded R)
    (ground : ∀ h, R.headEq .legacyGround h → h = .legacyGround) :
    ∀ (A : Ty) {n : ℕ} {T : Presentation.Tower.Tm n},
      Presentation.StepCore R.computation R.headEq (eraseTypeAt n A) T → T = eraseTypeAt n A
  | .atom, n, T, step => by
      cases step with
      | head related => rw [ground _ related]; rfl
      | root rootStep =>
          obtain ⟨c, args, same⟩ := spine rootStep
          rcases constOrApp_appSpine c args with ⟨_, e⟩ | ⟨_, _, e⟩ <;> rw [e] at same <;> cases same
  | .arr domain codomain, n, T, step => by
      cases step with
      | root rootStep =>
          obtain ⟨c, args, same⟩ := spine rootStep
          rcases constOrApp_appSpine c args with ⟨_, e⟩ | ⟨_, _, e⟩ <;> rw [e] at same <;> cases same
      | congPiDom inner =>
          rw [eraseTypeAt_step spine ground domain inner]
          rfl
      | congPiCod inner =>
          rw [eraseTypeAt_step spine ground codomain inner]
          rfl

theorem eraseTypeAt_steps (spine : Presentation.TypedEquality.StrongNormalization.SpineHeaded R)
    (ground : ∀ h, R.headEq .legacyGround h → h = .legacyGround) (A : Ty) {n : ℕ}
    {T : Presentation.Tower.Tm n}
    (steps : Relation.ReflTransGen (Presentation.StepCore R.computation R.headEq)
      (eraseTypeAt n A) T) : T = eraseTypeAt n A := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact eraseTypeAt_step spine ground A step

end Types

/-! ## Reduction of erasures -/

section Lift

universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop} {f : α → β}

/-- A bounded morphism reflects finite reduction sequences. -/
theorem lift_star_of_isBoundedMorphism (bounded : IsBoundedMorphism r s f) {a : α} {b : β}
    (steps : Relation.ReflTransGen s (f a) b) : ∃ a', Relation.ReflTransGen r a a' ∧ f a' = b := by
  induction steps with
  | refl => exact ⟨a, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨a', steps', rfl⟩ := ih
      obtain ⟨a'', step', rfl⟩ := bounded.lift step
      exact ⟨a'', steps'.tail step', rfl⟩

end Lift

theorem betaConv_of_betaStar {Γ : List Ty} {A : Ty} {l l' : Term Γ A}
    (steps : Relation.ReflTransGen BetaStep l l') : BetaConv l l' := by
  induction steps with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

theorem betaEtaConv_of_betaStar {Γ : List Ty} {A : Ty} {l l' : Term Γ A}
    (steps : Relation.ReflTransGen BetaStep l l') : BetaEtaConv l l' := by
  induction steps with
  | refl => exact .refl _
  | tail _ step ih =>
      exact .trans _ _ _ ih (.rel _ _
        (Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Equation.ofBetaStep step))

/-! ## What the conversion algorithm says about erasures -/

section Algorithm

variable {R : Presentation.Rules Presentation.Tower.Head}

/-- The reading of the conversion algorithm's statements on erasures: compared
erasures at an erased type are βη-convertible, compared neutral erasures have
one simple type, the one the algorithm assigns, and are βη-convertible, and
compared erased types are erasures of one simple type. -/
def ErasureReading : AlgorithmStatement Presentation.Tower.Head → Prop
  | @AlgorithmStatement.compare _ n Δ a b T =>
      ∀ (Γ : List Ty) (A : Ty) (l r : Term Γ A) (same : Γ.length = n),
        (same ▸ eraseContext Γ : Presentation.Tower.Ctx n) = Δ →
        (same ▸ eraseTerm l : Presentation.Tower.Tm n) = a →
        (same ▸ eraseTerm r : Presentation.Tower.Tm n) = b →
        (same ▸ eraseTypeAt Γ.length A : Presentation.Tower.Tm n) = T →
          BetaEtaConv l r
  | @AlgorithmStatement.neutral _ n Δ a b U =>
      ∀ (Γ : List Ty) (A B : Ty) (l : Term Γ A) (r : Term Γ B) (same : Γ.length = n),
        (same ▸ eraseContext Γ : Presentation.Tower.Ctx n) = Δ →
        (same ▸ eraseTerm l : Presentation.Tower.Tm n) = a →
        (same ▸ eraseTerm r : Presentation.Tower.Tm n) = b →
          ∃ equal : A = B,
            (same ▸ eraseTypeAt Γ.length A : Presentation.Tower.Tm n) = U ∧
              BetaEtaConv (equal ▸ l) r
  | @AlgorithmStatement.types _ n _ X Y =>
      ∀ (A B : Ty), eraseTypeAt n A = X → eraseTypeAt n B = Y → A = B

/-- η for intrinsic terms: two functions are βη-convertible when their
applications to a fresh variable are. -/
theorem betaEtaConv_of_expansions {Γ : List Ty} {X Y : Ty} {l r : Term Γ (.arr X Y)}
    (conv : BetaEtaConv (.app (l.rename (weakening (B := X))) (.var .zero))
      (.app (r.rename (weakening (B := X))) (.var .zero))) : BetaEtaConv l r :=
  .trans _ _ _ (.symm _ _ (.rel _ _
      (Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Equation.eta l)))
    (.trans _ _ _ (Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Conv.lam conv)
      (.rel _ _ (Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Equation.eta r)))

/-- A de Bruijn position determines the type and the typed variable, without
choice. -/
theorem eraseVar_type_eq : ∀ {Γ : List Ty} {A B : Ty} (v : Var Γ A) (w : Var Γ B),
    eraseVar v = eraseVar w → A = B ∧ HEq v w
  | _, _, _, .zero, .zero, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .zero, .succ _, h => absurd h (Fin.succ_ne_zero _).symm
  | _, _, _, .succ _, .zero, h => absurd h (Fin.succ_ne_zero _)
  | _, _, _, .succ v, .succ w, h => by
      obtain ⟨rfl, same⟩ := eraseVar_type_eq v w (Fin.succ_injective _ h)
      cases same
      exact ⟨rfl, HEq.rfl⟩

/-- Weakening commutes with erasure. -/
theorem eraseTerm_weaken {Γ : List Ty} (X : Ty) {B : Ty} (t : Term Γ B) :
    Presentation.rename Presentation.wk (eraseTerm t) = eraseTerm (t.rename (weakening (B := X))) := by
  rw [SubstitutionTranslation.eraseTerm_rename, SubstitutionTranslation.eraseRenaming_weakening]

/-- **What the conversion algorithm derives about erasures**: in a package whose
root steps start at applications of constants, whose head equality relates
the ground head only to itself, and in which the ground head is not a
universe, every comparison of erasures at an erased type is a βη-conversion. -/
theorem algorithm_erasure (spine : Presentation.TypedEquality.StrongNormalization.SpineHeaded R)
    (ground : ∀ h, R.headEq .legacyGround h → h = .legacyGround)
    (notUniverse : ¬ R.isUniverse .legacyGround) :
    ∀ {st : AlgorithmStatement Presentation.Tower.Head}, Algorithm R st → ErasureReading st := by
  intro st derivation
  induction derivation with
  | pi reducesT _ ih =>
      intro Γ A l r same hΔ ha hb hT
      subst same; subst hΔ; subst ha; subst hb; subst hT
      have shape := eraseTypeAt_steps spine ground A reducesT
      cases A with
      | atom => cases shape
      | arr X Y =>
          obtain ⟨hX, hY⟩ := Presentation.Tm.pi.inj shape
          subst hX; subst hY
          refine betaEtaConv_of_expansions
            (ih (X :: Γ) Y (.app (l.rename weakening) (.var .zero))
              (.app (r.rename weakening) (.var .zero)) rfl rfl ?_ ?_ rfl)
          · change Presentation.Tm.app (eraseTerm (l.rename weakening)) (.var 0) = _
            rw [← eraseTerm_weaken X]
          · change Presentation.Tm.app (eraseTerm (r.rename weakening)) (.var 0) = _
            rw [← eraseTerm_weaken X]
  | sigma reducesT _ _ _ _ =>
      intro Γ A l r same _ _ _ hT
      subst same; subst hT
      have shape := eraseTypeAt_steps spine ground A reducesT
      cases A <;> cases shape
  | sort reducesT isUniverse _ _ =>
      intro Γ A l r same _ _ _ hT
      subst same; subst hT
      have shape := eraseTypeAt_steps spine ground A reducesT
      cases A with
      | atom =>
          have hu := Presentation.Tm.head.inj shape
          subst hu
          exact absurd isUniverse notUniverse
      | arr _ _ => cases shape
  | reflexivity reducesT _ _ _ _ =>
      intro Γ A l r same _ _ _ hT
      subst same; subst hT
      have shape := eraseTypeAt_steps spine ground A reducesT
      cases A <;> cases shape
  | neutralAt reducesA reducesB _ ih =>
      intro Γ A l r same hΔ ha hb _
      subst same; subst hΔ; subst ha; subst hb
      have bounded := erase_isBoundedMorphism_of_rootFree (headEq := R.headEq)
        (RootFree.of_spineHeaded spine) Γ A
      obtain ⟨l', stepsL, rfl⟩ := lift_star_of_isBoundedMorphism bounded reducesA
      obtain ⟨r', stepsR, rfl⟩ := lift_star_of_isBoundedMorphism bounded reducesB
      obtain ⟨_, _, conv⟩ := ih Γ A A l' r' rfl rfl rfl rfl
      exact .trans _ _ _ (betaEtaConv_of_betaStar stepsL)
        (.trans _ _ _ conv (.symm _ _ (betaEtaConv_of_betaStar stepsR)))
  | var i =>
      intro Γ A B l r same hΔ ha hb
      subst same; subst hΔ
      cases l with
      | var v =>
          cases r with
          | var w =>
              have hv : eraseVar v = i := Presentation.Tm.var.inj ha
              have hw : eraseVar w = i := Presentation.Tm.var.inj hb
              obtain ⟨rfl, same⟩ := eraseVar_type_eq v w (hv.trans hw.symm)
              cases same
              refine ⟨rfl, ?_, .refl _⟩
              change eraseTypeAt Γ.length A = Presentation.Ctx.lookup (eraseContext Γ) i
              rw [← hv, lookup_eraseContext]
          | lam _ => cases hb
          | app _ _ => cases hb
      | lam _ => cases ha
      | app _ _ => cases ha
  | const _ =>
      intro Γ A B l r same _ ha _
      subst same
      cases l <;> cases ha
  | app _ reducesU _ ihFG ihAB =>
      intro Γ C D l r same hΔ hl hr
      subst same; subst hΔ
      cases l with
      | app lf la =>
          cases r with
          | app rf ra =>
              obtain ⟨hf, ha⟩ := Presentation.Tm.app.inj hl
              obtain ⟨hg, hb⟩ := Presentation.Tm.app.inj hr
              subst hf; subst ha; subst hg; subst hb
              obtain ⟨equal, hU, convF⟩ := ihFG Γ _ _ lf rf rfl rfl rfl rfl
              injection equal with hXY hCD
              subst hXY; subst hCD
              subst hU
              have shape := eraseTypeAt_steps spine ground _ reducesU
              obtain ⟨hA, hB⟩ := Presentation.Tm.pi.inj shape
              subst hA; subst hB
              have convA := ihAB Γ _ la ra rfl rfl rfl rfl rfl
              refine ⟨rfl, ?_, Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Conv.app convF convA⟩
              exact (eraseTypeAt_subst C _).symm
          | var _ => cases hr
          | lam _ => cases hr
      | var _ => cases hl
      | lam _ => cases hl
  | fst _ _ _ =>
      intro Γ A B l r same _ ha _
      subst same
      cases l <;> cases ha
  | snd _ _ _ =>
      intro Γ A B l r same _ ha _
      subst same
      cases l <;> cases ha
  | heads reducesX reducesY _ =>
      intro A B hA hB
      subst hA; subst hB
      have shapeA := eraseTypeAt_steps spine ground A reducesX
      have shapeB := eraseTypeAt_steps spine ground B reducesY
      cases A with
      | arr _ _ => cases shapeA
      | atom =>
          cases B with
          | atom => rfl
          | arr _ _ => cases shapeB
  | piTypes reducesX reducesY _ _ ihDomain ihCodomain =>
      intro A B hA hB
      subst hA; subst hB
      have shapeA := eraseTypeAt_steps spine ground A reducesX
      have shapeB := eraseTypeAt_steps spine ground B reducesY
      cases A with
      | atom => cases shapeA
      | arr A₁ A₂ =>
          cases B with
          | atom => cases shapeB
          | arr B₁ B₂ =>
              obtain ⟨hA₁, hA₂⟩ := Presentation.Tm.pi.inj shapeA
              obtain ⟨hB₁, hB₂⟩ := Presentation.Tm.pi.inj shapeB
              rw [ihDomain A₁ B₁ hA₁.symm hB₁.symm, ihCodomain A₂ B₂ hA₂.symm hB₂.symm]
  | sigmaTypes reducesX _ _ _ _ _ =>
      intro A B hA _
      subst hA
      have shapeA := eraseTypeAt_steps spine ground A reducesX
      cases A <;> cases shapeA
  | idTypes reducesX _ _ _ _ _ _ _ =>
      intro A B hA _
      subst hA
      have shapeA := eraseTypeAt_steps spine ground A reducesX
      cases A <;> cases shapeA
  | neutralTypes reducesX _ neutral _ =>
      intro A B hA _
      subst hA
      have shapeA := eraseTypeAt_steps spine ground A reducesX
      subst shapeA
      cases A <;> cases neutral

end Algorithm

/-! ## Erasure collisions are β-conversions, without choice -/

section Collision

/-- Every intrinsic term has a β-step or is β-normal, constructively. -/
theorem step_or_normal : ∀ {Γ : List Ty} {A : Ty} (t : Term Γ A),
    (∃ t', BetaStep t t') ∨ Normal t
  | _, _, .var v => .inr (.neutral (.var v))
  | _, _, .lam body =>
      match step_or_normal body with
      | .inl ⟨_, step⟩ => .inl ⟨_, .lam step⟩
      | .inr normal => .inr (.lam normal)
  | _, _, .app f a =>
      match step_or_normal f with
      | .inl ⟨_, step⟩ => .inl ⟨_, .appLeft step⟩
      | .inr normalF =>
          match step_or_normal a with
          | .inl ⟨_, step⟩ => .inl ⟨_, .appRight step⟩
          | .inr normalA =>
              match f, normalF with
              | _, .neutral neutralF => .inr (.neutral (.app neutralF normalA))
              | .lam body, .lam _ => .inl ⟨_, .beta body a⟩

private theorem erasure_properties {Γ : List Ty} {A : Ty} (left : Term Γ A) :
    (∀ (right : Term Γ A), Normal left → Normal right →
      eraseTerm left = eraseTerm right → left = right) ∧
    (∀ {B : Ty} (right : Term Γ B), Neutral left → Neutral right →
      eraseTerm left = eraseTerm right → A = B ∧ HEq left right) := by
  induction left with
  | @var Γ A v =>
      have neutralCase : ∀ {B : Ty} (right : Term Γ B), Neutral right →
          eraseTerm (.var v) = eraseTerm right → A = B ∧ HEq (Term.var v) right := by
        intro B right rightNeutral equal
        cases rightNeutral with
        | var w =>
            obtain ⟨rfl, same⟩ := eraseVar_type_eq v w (Presentation.Tm.var.inj equal)
            cases same
            exact ⟨rfl, HEq.rfl⟩
        | app _ _ => cases equal
      constructor
      · intro right _ rightNormal equal
        cases rightNormal with
        | neutral rightNeutral => exact eq_of_heq (neutralCase _ rightNeutral equal).2
        | lam _ => cases equal
      · intro B right _ rightNeutral equal
        exact neutralCase right rightNeutral equal
  | @lam Γ A B body ih =>
      constructor
      · intro right leftNormal rightNormal equal
        cases leftNormal with
        | neutral neutral => cases neutral
        | lam leftBody =>
            cases rightNormal with
            | neutral rightNeutral => cases rightNeutral <;> cases equal
            | lam rightBody =>
                exact congrArg Term.lam (ih.1 _ leftBody rightBody
                  (Presentation.Tm.lam.inj equal))
      · intro C right leftNeutral
        cases leftNeutral
  | @app Γ A B function argument functionIH argumentIH =>
      have neutralCase : ∀ {C : Ty} (right : Term Γ C),
          Neutral (.app function argument) → Neutral right →
          eraseTerm (.app function argument) = eraseTerm right →
          B = C ∧ HEq (Term.app function argument) right := by
        intro C right leftNeutral rightNeutral equal
        cases leftNeutral with
        | app leftFunction leftArgument =>
            cases rightNeutral with
            | var _ => cases equal
            | app rightFunction rightArgument =>
                obtain ⟨functions, arguments⟩ := Presentation.Tm.app.inj equal
                obtain ⟨types, sameFunctions⟩ :=
                  functionIH.2 _ leftFunction rightFunction functions
                obtain ⟨domain, codomain⟩ := Ty.arr.inj types
                cases domain
                cases codomain
                have sameArguments := argumentIH.1 _ leftArgument rightArgument arguments
                cases sameFunctions
                cases sameArguments
                exact ⟨rfl, HEq.rfl⟩
      constructor
      · intro right leftNormal rightNormal equal
        cases leftNormal with
        | neutral leftNeutral =>
            cases rightNormal with
            | neutral rightNeutral =>
                exact eq_of_heq (neutralCase _ leftNeutral rightNeutral equal).2
            | lam _ => cases equal
      · exact neutralCase

/-- β-normal terms of one type with one erasure are equal, without choice. -/
theorem normal_eq_of_erase_eq {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (leftNormal : Normal left) (rightNormal : Normal right)
    (equal : eraseTerm left = eraseTerm right) : left = right :=
  (erasure_properties left).1 right leftNormal rightNormal equal

/-- **Erasure collisions are β-conversions**: two simple terms of one type with
one erasure are β-convertible.  The proof uses strong normalization pulled
back from the executable package and the back law of erasure, and no
choice. -/
theorem betaConv_of_erase_eq {Γ : List Ty} {A : Ty} (left : Term Γ A) :
    ∀ right : Term Γ A, eraseTerm left = eraseTerm right → BetaConv left right := by
  induction betaStep_sn left with
  | intro left _ ih =>
      intro right same
      rcases step_or_normal left with ⟨left', step⟩ | leftNormal
      · have moved : TowerStep Γ.length (eraseTerm right) (eraseTerm left') :=
          same ▸ BetaStep.erase step
        obtain ⟨right', stepR, same'⟩ := erase_liftStep right moved
        exact .trans _ _ _ (.rel _ _ step)
          (.trans _ _ _ (ih left' step right' same'.symm) (.symm _ _ (.rel _ _ stepR)))
      · rcases step_or_normal right with ⟨right', stepR⟩ | rightNormal
        · have moved : TowerStep Γ.length (eraseTerm left) (eraseTerm right') :=
            same.symm ▸ BetaStep.erase stepR
          obtain ⟨left'', stepL, _⟩ := erase_liftStep left moved
          exact absurd stepL (leftNormal.no_betaStep _)
        · rw [normal_eq_of_erase_eq leftNormal rightNormal same]
          exact .refl _

end Collision

/-! ## Conservativity through the executable package's confluence -/

section Conservativity

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel

/-- A presentation with more root steps and more head equalities has more
steps. -/
theorem StepCore.mono {Head : Type} {root root' : Presentation.RootComputation Head}
    {headEq headEq' : Head → Head → Prop}
    (rootSub : ∀ {n : ℕ} {t u : Presentation.Tm Head n}, root.step t u → root'.step t u)
    (headSub : ∀ {h h' : Head}, headEq h h' → headEq' h h') {n : ℕ}
    {t u : Presentation.Tm Head n} (step : Presentation.StepCore root headEq t u) :
    Presentation.StepCore root' headEq' t u := by
  induction step with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | head related => exact .head (headSub related)
  | root rootStep => exact .root (rootSub rootStep)
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

/-- Conversion of the executable package (without codes), with its head
equality. -/
abbrev RulesConv {n : ℕ} (t u : Presentation.Tower.Tm n) : Prop :=
  Presentation.Conv rules.headEq t u rules.computation

/-- **Conversion of the executable package is conservative on erasures of one
type**: erasures convertible in the package are β-convertible.  Church–Rosser
of the package gives a common reduct; erasure reflects the reduction
sequences; the collision lemma closes the square. -/
theorem betaConv_of_rulesConv {Γ : List Ty} {A : Ty} {l r : Term Γ A}
    (conv : RulesConv (eraseTerm l) (eraseTerm r)) : BetaConv l r := by
  obtain ⟨common, stepsL, stepsR⟩ := churchRosser conv
  have bounded := erase_isBoundedMorphism_of_rootFree (headEq := rules.headEq)
    rulesRootFree Γ A
  obtain ⟨l', reducesL, rfl⟩ := lift_star_of_isBoundedMorphism bounded stepsL
  obtain ⟨r', reducesR, same⟩ := lift_star_of_isBoundedMorphism bounded stepsR
  exact .trans _ _ _ (betaConv_of_betaStar reducesL)
    (.trans _ _ _ (betaConv_of_erase_eq l' r' same.symm)
      (.symm _ _ (betaConv_of_betaStar reducesR)))

/-- A step of the sealed tower is a step of the executable package. -/
theorem rulesStep_of_towerStep {n : ℕ} {t u : Presentation.Tower.Tm n}
    (step : Presentation.StepCore Presentation.RootComputation.empty Presentation.Tower.HeadEq t u) :
    Presentation.StepCore rules.computation rules.headEq t u :=
  StepCore.mono (root := Presentation.RootComputation.empty) (fun impossible => impossible.elim)
    id step

/-- A directed step of the executable package is a step with its head
equality. -/
theorem rulesStep_of_execStep {n : ℕ} {t u : Presentation.Tower.Tm n}
    (step : Presentation.TypedEquality.StrongNormalization.Reduces rules t u) :
    Presentation.StepCore rules.computation rules.headEq t u :=
  StepCore.mono (headEq := Presentation.TypedEquality.StrongNormalization.noHeadSteps) id
    (fun impossible => impossible.elim) step

/-- The sealed tower's conversion lies inside the executable package's. -/
theorem rulesConv_of_towerConv {n : ℕ} {t u : Presentation.Tower.Tm n}
    (conv : Presentation.Conv Presentation.Tower.HeadEq t u) : RulesConv t u := by
  induction conv with
  | rel _ _ step => exact .rel _ _ (rulesStep_of_towerStep step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

/-- **The sealed tower's conversion is conservative on erasures of one type,
without choice**: the conservativity of `towerConv_iff_betaConv`, proved
through the executable package's Church–Rosser theorem. -/
theorem towerConv_iff_betaConv' {Γ : List Ty} {A : Ty} (l r : Term Γ A) :
    Presentation.Conv Presentation.Tower.HeadEq (eraseTerm l) (eraseTerm r) ↔ BetaConv l r :=
  ⟨fun conv => betaConv_of_rulesConv (rulesConv_of_towerConv conv), BetaConv.erase⟩

/-- The executable package's directed conversion, without its codes. -/
abbrev ExecConv {n : ℕ} (t u : Presentation.Tower.Tm n) : Prop :=
  Relation.EqvGen (Presentation.TypedEquality.StrongNormalization.Reduces rules) t u

theorem rulesConv_of_execConv {n : ℕ} {t u : Presentation.Tower.Tm n} (conv : ExecConv t u) :
    RulesConv t u := by
  induction conv with
  | rel _ _ step => exact .rel _ _ (rulesStep_of_execStep step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

/-- **The executable package's directed conversion is conservative on erasures
of one type.** -/
theorem execConv_iff_betaConv {Γ : List Ty} {A : Ty} (l r : Term Γ A) :
    ExecConv (eraseTerm l) (eraseTerm r) ↔ BetaConv l r := by
  constructor
  · intro conv
    exact betaConv_of_rulesConv (rulesConv_of_execConv conv)
  · intro conv
    have bounded := erase_isBoundedMorphism_of_rootFree
      (headEq := Presentation.TypedEquality.StrongNormalization.noHeadSteps) rulesRootFree Γ A
    induction conv with
    | rel _ _ step => exact .rel _ _ (bounded.map step)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

/-- Directed object conversion is contained in conversion with universe-head
equality. -/
theorem objectConv_of_execConv {n : ℕ} {t u : Presentation.Tower.Tm n}
    (conv : Relation.EqvGen (Presentation.TypedEquality.StrongNormalization.Reduces
      CodeModel.objectRules) t u) :
    Presentation.Conv CodeModel.objectRules.headEq t u CodeModel.objectRules.computation := by
  induction conv with
  | rel _ _ step =>
      exact .rel _ _ (StepCore.mono
        (headEq := Presentation.TypedEquality.StrongNormalization.noHeadSteps)
        id (fun impossible => impossible.elim) step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

theorem betaConv_of_objectConversion
    {Γ : List Ty} {A : Ty} {l r : Term Γ A}
    (conv : Presentation.Conv CodeModel.objectRules.headEq (eraseTerm l) (eraseTerm r)
      CodeModel.objectRules.computation) : BetaConv l r := by
  obtain ⟨common, stepsL, stepsR⟩ := CodeModel.objectChurchRosser conv
  have bounded := erase_isBoundedMorphism_of_rootFree (headEq := CodeModel.objectRules.headEq)
    objectRootFree Γ A
  obtain ⟨l', reducesL, rfl⟩ := lift_star_of_isBoundedMorphism bounded stepsL
  obtain ⟨r', reducesR, same⟩ := lift_star_of_isBoundedMorphism bounded stepsR
  exact .trans _ _ _ (betaConv_of_betaStar reducesL)
    (.trans _ _ _ (betaConv_of_erase_eq l' r' same.symm)
      (.symm _ _ (betaConv_of_betaStar reducesR)))

/-- The actual object conversion is conservative on erasures of one simple
type, including the proposition-code decoders and universe-head equality. -/
theorem objectConversion_iff_betaConv {Γ : List Ty} {A : Ty} (l r : Term Γ A) :
    Presentation.Conv CodeModel.objectRules.headEq (eraseTerm l) (eraseTerm r)
      CodeModel.objectRules.computation ↔ BetaConv l r := by
  constructor
  · exact betaConv_of_objectConversion
  · intro conv
    have bounded := erase_isBoundedMorphism_of_rootFree
      (headEq := CodeModel.objectRules.headEq) objectRootFree Γ A
    induction conv with
    | rel _ _ step => exact .rel _ _ (bounded.map step)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

/-- The directed object conversion is conservative without any unproved
Church--Rosser assumption. -/
theorem betaConv_of_objectConv {Γ : List Ty} {A : Ty} {l r : Term Γ A}
    (conv : Relation.EqvGen (Presentation.TypedEquality.StrongNormalization.Reduces
      CodeModel.objectRules) (eraseTerm l) (eraseTerm r)) : BetaConv l r :=
  betaConv_of_objectConversion (objectConv_of_execConv conv)

end Conservativity

/-! ## The typed η-equality on erasures -/

section Extensional

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel

variable {R : Presentation.Rules Presentation.Tower.Head} (heads : HeadRules R)

/-- An η-expansion applied to the fresh variable β-reduces to the weakened
function applied to it. -/
theorem etaExpansion_apply_betaConv {Γ : List Ty} {X Y : Ty} (f : Term Γ (.arr X Y)) :
    BetaConv
      (.app ((Term.lam (.app (f.rename (weakening (B := X))) (.var .zero))).rename
        (weakening (B := X))) (.var .zero))
      (.app (f.rename (weakening (B := X))) (.var .zero)) := by
  have key : ((Term.app (f.rename (weakening (B := X))) (.var .zero)).rename
      (liftRenaming (B := X) (weakening (B := X)))).instantiateNewest (.var .zero) =
        .app (f.rename (weakening (B := X))) (.var .zero) := by
    simp only [Term.instantiateNewest, Term.rename, Term.substitute]
    congr 1
    rw [Term.substitute_rename, Term.substitute_rename]
    conv_rhs => rw [← Term.substitute_id (f.rename weakening), Term.substitute_rename]
    rfl
  have step := BetaStep.beta ((Term.app (f.rename (weakening (B := X))) (.var .zero)).rename
    (liftRenaming (B := X) (weakening (B := X)))) (.var (.zero : Var (X :: Γ) X))
  rw [key] at step
  exact .rel _ _ step

include heads in
/-- **The typed equality validates η on erasures.** -/
theorem equal_eta {Γ : List Ty} {X Y : Ty} (f : Term Γ (.arr X Y)) :
    Equal R (eraseContext Γ) (eraseTerm (.lam (.app (f.rename (weakening (B := X))) (.var .zero))))
      (eraseTerm f) (eraseTypeAt Γ.length (.arr X Y)) := by
  refine Derivable.etaPi (term_typed heads _) (term_typed heads f) ?_
  rw [eraseTerm_weaken X, eraseTerm_weaken X]
  exact conversion_equal heads (etaExpansion_apply_betaConv f)

include heads in
/-- One βη-equation of intrinsic terms is a typed equality of their erasures. -/
theorem equal_of_equation {Γ : List Ty} {A : Ty} {l r : Term Γ A}
    (equation : Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Equation l r) :
    Equal R (eraseContext Γ) (eraseTerm l) (eraseTerm r) (eraseTypeAt Γ.length A) := by
  induction equation with
  | beta body argument => exact beta_equal heads body argument
  | eta f => exact equal_eta heads f
  | @lam Γ A B body body' _ ih =>
      exact .lamCong (type_formed heads (.arr A B) (eraseContext Γ)) (heads.universes _) ih
  | appLeft _ ih =>
      simpa only [eraseTerm, eraseTypeAt, Presentation.inst0, eraseTypeAt_subst] using
        (Derivable.appCong ih (.refl (term_typed heads _)))
  | @appRight Γ A B f a a' _ ih =>
      simpa only [eraseTerm, eraseTypeAt, Presentation.inst0, eraseTypeAt_subst] using
        (Derivable.appCong (.refl (term_typed heads f)) ih)

include heads in
/-- **βη-conversion is sound for the typed equality**, for every package with the
formation rules of the simple fragment. -/
theorem equal_of_betaEtaConv {Γ : List Ty} {A : Ty} {l r : Term Γ A}
    (conv : BetaEtaConv l r) :
    Equal R (eraseContext Γ) (eraseTerm l) (eraseTerm r) (eraseTypeAt Γ.length A) := by
  induction conv with
  | rel _ _ equation => exact equal_of_equation heads equation
  | refl t => exact .refl (term_typed heads t)
  | symm _ _ _ ih => exact .symm ih
  | trans _ _ _ _ _ ih ih' => exact .trans ih ih'

/-- The executable package (without codes) has the formation rules of the
simple fragment. -/
theorem rulesHeads : HeadRules rules :=
  ⟨.legacyGround, fun _ => .sort _, fun _ _ => .sorts _ _⟩

theorem rulesSpine : Presentation.TypedEquality.StrongNormalization.SpineHeaded rules :=
  Presentation.TypedEquality.StrongNormalization.RootShape.spineHeaded shape

theorem objectSpine : Presentation.TypedEquality.StrongNormalization.SpineHeaded CodeModel.objectRules :=
  Presentation.TypedEquality.StrongNormalization.RootShape.spineHeaded CodeModel.objectShape

/-- The tower's head equality relates the ground head only to itself. -/
theorem towerHeadEq_ground (h : Presentation.Tower.Head)
    (related : Presentation.Tower.HeadEq .legacyGround h) : h = .legacyGround := by
  cases h with
  | legacyGround => rfl
  | sort _ => exact related.elim

/-- The ground head is not a universe. -/
theorem ground_not_universe : ¬ Presentation.Tower.IsUniverse .legacyGround :=
  fun isUniverse => by cases isUniverse

/-- **The typed η-equality of the executable package is complete for βη on
erasures**: typed-equal erasures of one simple type are βη-convertible.  The
package's conversion algorithm is complete, and on erasures it can only
compare as the βη-algorithm of the simple fragment does. -/
theorem betaEtaConv_of_equal {Γ : List Ty} {A : Ty} {l r : Term Γ A}
    (equal : Equal rules (eraseContext Γ) (eraseTerm l) (eraseTerm r) (eraseTypeAt Γ.length A)) :
    BetaEtaConv l r :=
  algorithm_erasure rulesSpine towerHeadEq_ground ground_not_universe
    (algorithm_complete (context_formed rulesHeads Γ) equal) Γ A l r rfl rfl rfl rfl rfl

/-- **Typed-equal erased simple types are erasures of one simple type.** -/
theorem ty_eq_of_typeEq {Γ : List Ty} {A B : Ty}
    (equal : Presentation.TypedEquality.Normalization.TypeEq rules (eraseContext Γ)
      (eraseTypeAt Γ.length A)
      (eraseTypeAt Γ.length B)) : A = B :=
  algorithm_erasure rulesSpine towerHeadEq_ground ground_not_universe
    (Presentation.TypedEquality.Normalization.TypeEq.algorithm (S := setting fun _ => 0) complete
      equal (context_formed rulesHeads Γ)) A B rfl rfl

/-- **On erasures of one type, the executable package's typed equality is
exactly βη-conversion.** -/
theorem equal_iff_betaEtaConv {Γ : List Ty} {A : Ty} (l r : Term Γ A) :
    Equal rules (eraseContext Γ) (eraseTerm l) (eraseTerm r) (eraseTypeAt Γ.length A) ↔
      BetaEtaConv l r :=
  ⟨betaEtaConv_of_equal, equal_of_betaEtaConv rulesHeads⟩

/-- βη-convertible terms have one denotation in every function space. -/
theorem BetaEtaConv.denote {Γ : List Ty} {A : Ty} {l r : Term Γ A} (conv : BetaEtaConv l r)
    {Ground : Type} (environment : Environment Ground Γ) :
    l.denote environment = r.denote environment := by
  induction conv with
  | rel _ _ equation => exact betaEtaEquation_denote equation environment
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- `s z`, in the context `s : atom → atom, z : atom`. -/
def successorOfZero : Term [.arr .atom .atom, .atom] .atom :=
  .app (.var .zero) (.var (.succ .zero))

/-- `z`, in the same context. -/
def zeroVariable : Term [.arr .atom .atom, .atom] .atom :=
  .var (.succ .zero)

/-- `s z` and `z` are not βη-convertible: they denote differently at
`s := not`, `z := true`. -/
theorem successorOfZero_not_betaEtaConv : ¬ BetaEtaConv successorOfZero zeroVariable := by
  intro conv
  let environment : Environment Bool [.arr .atom .atom, .atom] :=
    Environment.extend (A := .arr .atom .atom) (fun b : Bool => !b)
      (Environment.extend (A := .atom) true ⟨fun v => nomatch v⟩)
  exact Bool.noConfusion (conv.denote environment)

/-- **Control: the typed η-equality refutes `s z = z`**, through its
completeness on erasures. -/
theorem successorOfZero_not_equal :
    ¬ Equal rules (eraseContext [.arr .atom .atom, .atom]) (eraseTerm successorOfZero)
      (eraseTerm zeroVariable) (eraseTypeAt 2 .atom) :=
  fun equal => successorOfZero_not_betaEtaConv (betaEtaConv_of_equal equal)

/-- **For the package with its proposition codes, completeness follows from the
facts about the weak-head forms of its types**, the hypothesis of the object
package's conversion completeness. -/
theorem betaEtaConv_of_equal_object (facts : Presentation.TypedEquality.Normalization.FormFacts
      CodeModel.objectRules CodeModel.objectRoles)
    {Γ : List Ty} {A : Ty} {l r : Term Γ A}
    (equal : Equal CodeModel.objectRules (eraseContext Γ) (eraseTerm l) (eraseTerm r)
      (eraseTypeAt Γ.length A)) :
    BetaEtaConv l r :=
  algorithm_erasure objectSpine towerHeadEq_ground ground_not_universe
    (Presentation.TypedEquality.Normalization.Equal.algorithm
      (S := CodeModel.ConvRules.objectSetting)
      (CodeModel.ConvRules.object_algorithmicComplete_of_facts facts) equal
      (context_formed simpleHeadRules Γ)) Γ A l r rfl rfl rfl rfl rfl

end Extensional

/-! ## Commuting and failing squares, in the forms of the scope algebra -/

section Laws

open Mettapedia.GSLT.Scope
open Mettapedia.GSLT.AdmissibleContextCongruence

universe u u'

variable {Str : Type u} {Str' : Type u'} {reduct : Str' → Str} {E : Setoid Str}
  {E' : Setoid Str'}

/-- **A square with the forth and back laws commutes** in each of its three
readings: forgetting and translating commute for every class, Beck–Chevalley
holds for the observer views, and the square of views is a weak pullback. -/
theorem square_of_laws (forth : Forth reduct E E') (back : Back reduct E E') :
    (∀ K : Set Str, reduct ⁻¹' saturation E K = saturation E' (reduct ⁻¹' K)) ∧
      (∀ φ : Set Str, viewMap forth ⁻¹' (Quotient.mk E '' φ) =
        Quotient.mk E' '' (reduct ⁻¹' φ)) ∧
      IsWeakPullback reduct (Quotient.mk E') (Quotient.mk E) (viewMap forth) :=
  ⟨forget_translate_comm_iff.mpr ⟨forth, back⟩, (forget_translate_views_comm_iff forth).mpr back,
    (back_iff_isWeakPullback forth).mp back⟩

/-- **A square whose back law fails** fails in each of the three readings. -/
theorem square_fails_of_back (forth : Forth reduct E E') (fails : ¬ Back reduct E E') :
    (¬ ∀ K : Set Str, reduct ⁻¹' saturation E K = saturation E' (reduct ⁻¹' K)) ∧
      (¬ ∀ φ : Set Str, viewMap forth ⁻¹' (Quotient.mk E '' φ) =
        Quotient.mk E' '' (reduct ⁻¹' φ)) ∧
      ¬ IsWeakPullback reduct (Quotient.mk E') (Quotient.mk E) (viewMap forth) :=
  ⟨fun comm => fails (forget_translate_comm_iff.mp comm).2,
    fun views => fails ((forget_translate_views_comm_iff forth).mp views),
    fun weak => fails ((back_iff_isWeakPullback forth).mpr weak)⟩

/-- A square whose forth law fails does not commute. -/
theorem square_fails_of_forth (fails : ¬ Forth reduct E E') :
    ¬ ∀ K : Set Str, reduct ⁻¹' saturation E K = saturation E' (reduct ⁻¹' K) :=
  fun comm => fails (forget_translate_comm_iff.mp comm).1

/-- **Descent is preserved along the forth law**: a class the target observer
cannot split pulls back to a class the source observer cannot split. -/
theorem observable_preimage (forth : Forth reduct E E') {P : Set Str}
    (visible : P ∈ observable predicateSat E) : reduct ⁻¹' P ∈ observable predicateSat E' :=
  fun _ _ related => visible (forth related)

/-- **Descent is reflected along the back law** of a surjective reduct. -/
theorem observable_of_preimage (back : Back reduct E E') (surjective : Function.Surjective reduct)
    {P : Set Str} (visible : reduct ⁻¹' P ∈ observable predicateSat E') :
    P ∈ observable predicateSat E := by
  intro s s' related
  obtain ⟨m, rfl⟩ := surjective s
  obtain ⟨m', related', rfl⟩ := back related
  exact visible related'

end Laws

/-! ## The squares on the simple fragment -/

section Squares

open Mettapedia.GSLT.Scope
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel

variable (Γ : List Ty) (A : Ty)

/-- The typed slice at `A`: raw terms that are erasures of simple terms of
type `A`. -/
def typedSlice : Set (Presentation.Tower.Tm Γ.length) :=
  Set.range (eraseTerm (context := Γ) (selectedType := A))

/-- Erasure onto the typed slice. -/
def toTypedSlice (t : Term Γ A) : typedSlice Γ A :=
  ⟨eraseTerm t, t, rfl⟩

theorem toTypedSlice_surjective : Function.Surjective (toTypedSlice Γ A) := by
  intro s
  obtain ⟨x, t, same⟩ := s
  subst same
  exact ⟨t, rfl⟩

/-- Erasure onto the slice of all erasures in the context, of every type. -/
def toSlice (t : Term Γ A) : sliceTerms Γ :=
  ⟨eraseTerm t, A, t, rfl⟩

/-- The executable package's directed conversion, as an observer on raw
terms. -/
def execConvSetoid (n : ℕ) : Setoid (Presentation.Tower.Tm n) :=
  ⟨ExecConv, Relation.EqvGen.is_equivalence _⟩

/-- The executable package's typed η-equality at the erased context and type,
on the typed slice. -/
def sliceEqual : Setoid (typedSlice Γ A) where
  r s t := Equal rules (eraseContext Γ) s.1 t.1 (eraseTypeAt Γ.length A)
  iseqv := ⟨fun s => by
      obtain ⟨_, t, same⟩ := s
      subst same
      exact .refl (term_typed rulesHeads t),
    fun related => .symm related, fun related related' => .trans related related'⟩

/-- Raw terms typed at the erased context and type in the executable package. -/
def TypedRaw : Type :=
  {t : Presentation.Tower.Tm Γ.length // Typed rules (eraseContext Γ) t (eraseTypeAt Γ.length A)}

/-- The executable package's typed η-equality on its typed raw terms. -/
def typedEqual : Setoid (TypedRaw Γ A) where
  r s t := Equal rules (eraseContext Γ) s.1 t.1 (eraseTypeAt Γ.length A)
  iseqv := ⟨fun s => .refl s.2, fun related => .symm related,
    fun related related' => .trans related related'⟩

/-- Erasure into the typed raw terms. -/
def toTypedRaw (t : Term Γ A) : TypedRaw Γ A :=
  ⟨eraseTerm t, term_typed rulesHeads t⟩

/-! ### The β square -/

/-- **Forth for β, on all raw terms**: erasure maps β-conversion into the
candidate's conversion. -/
theorem forth_beta_raw :
    Forth (@eraseTerm Γ A) (towerConversionSetoid Γ.length) (betaObserver Γ A) :=
  fun _ _ conv => BetaConv.erase conv

/-- The self-application `(λx. x x) (λy. y)`. -/
def selfApplication : Presentation.Tower.Tm 0 :=
  .app (.lam (.app (.var 0) (.var 0))) (.lam (.var 0))

/-- **The self-application converts to the erased identity.** -/
theorem selfApplication_conv :
    Presentation.Conv Presentation.Tower.HeadEq
      (eraseTerm ErasureBoundary.identityTerm) selfApplication :=
  .symm _ _ (.trans _ _ _
    (.rel _ _ (Presentation.StepCore.betaPi (.app (.var 0) (.var 0)) (.lam (.var 0))))
    (.rel _ _ (Presentation.StepCore.betaPi (.var 0) (.lam (.var 0)))))

/-- An arrow type is never its own domain. -/
theorem arr_ne_domain : ∀ (X Y : Ty), Ty.arr X Y ≠ X
  | .atom, _, same => by cases same
  | .arr X₁ X₂, _, same => arr_ne_domain X₁ X₂ (Ty.arr.inj same).1

/-- **The self-application is not the erasure of any simple term**, of any
type: the variable would have to be a function on its own type. -/
theorem selfApplication_not_erasure (B : Ty) (t : Term [] B) : eraseTerm t ≠ selfApplication := by
  intro same
  cases t with
  | var v => cases v
  | lam _ => cases same
  | app f _ =>
      have hf := (Presentation.Tm.app.inj same).1
      cases f with
      | var v => cases v
      | app _ _ => cases hf
      | lam body =>
          have hb := Presentation.Tm.lam.inj hf
          cases body with
          | var _ => cases hb
          | lam _ => cases hb
          | app g h =>
              obtain ⟨hg, hh⟩ := Presentation.Tm.app.inj hb
              cases g with
              | lam _ => cases hg
              | app _ _ => cases hg
              | var v =>
                  cases h with
                  | lam _ => cases hh
                  | app _ _ => cases hh
                  | var w =>
                      obtain ⟨functionType, -⟩ :=
                        eraseVar_type_eq v .zero (Presentation.Tm.var.inj hg)
                      obtain ⟨argumentType, -⟩ :=
                        eraseVar_type_eq w .zero (Presentation.Tm.var.inj hh)
                      rw [argumentType] at functionType
                      exact arr_ne_domain _ _ functionType

/-- **Control: the back law fails on all raw terms**: a raw term convertible
with an erasure need not be an erasure. -/
theorem back_beta_raw_fails :
    ¬ Back (@eraseTerm [] (.arr .atom .atom)) (towerConversionSetoid 0)
      (betaObserver [] (.arr .atom .atom)) := by
  intro back
  obtain ⟨_, _, same⟩ := back (m := ErasureBoundary.identityTerm) selfApplication_conv
  exact selfApplication_not_erasure _ _ same

/-- **The β square fails on all raw terms**: forgetting and translating do not
commute. -/
theorem beta_raw_square_fails :
    ¬ ∀ K : Set (Presentation.Tower.Tm 0),
      @eraseTerm [] (.arr .atom .atom) ⁻¹' saturation (towerConversionSetoid 0) K =
        saturation (betaObserver [] (.arr .atom .atom)) (@eraseTerm [] (.arr .atom .atom) ⁻¹' K) :=
  (square_fails_of_back (forth_beta_raw [] (.arr .atom .atom)) back_beta_raw_fails).1

/-- Forth for β into the executable package's conversion, on all raw terms. -/
theorem forth_beta_rawExec :
    Forth (@eraseTerm Γ A) (execConvSetoid Γ.length) (betaObserver Γ A) :=
  fun l r conv => (execConv_iff_betaConv l r).mpr conv

/-- The same control for the executable package's conversion. -/
theorem back_beta_rawExec_fails :
    ¬ Back (@eraseTerm [] (.arr .atom .atom)) (execConvSetoid 0)
      (betaObserver [] (.arr .atom .atom)) := by
  intro back
  have conv : ExecConv (eraseTerm ErasureBoundary.identityTerm) selfApplication :=
    .symm _ _ (.trans _ _ _
      (.rel _ _ (Presentation.StepCore.betaPi (.app (.var 0) (.var 0)) (.lam (.var 0))))
      (.rel _ _ (Presentation.StepCore.betaPi (.var 0) (.lam (.var 0)))))
  obtain ⟨_, _, same⟩ := back (m := ErasureBoundary.identityTerm) conv
  exact selfApplication_not_erasure _ _ same

/-- `λy. (λx. y) (λw. y w)` at `(atom → atom) → (atom → atom)`: its discarded
argument uses `y` as a function. -/
def expansionTerm : Term [] (.arr (.arr .atom .atom) (.arr .atom .atom)) :=
  .lam (.app (.lam (.var (.succ .zero)) : Term [.arr .atom .atom]
      (.arr (.arr .atom .atom) (.arr .atom .atom)))
    (.lam (.app (.var (.succ .zero)) (.var .zero))))

/-- It β-reduces to the erased identity. -/
theorem expansion_towerStep :
    TowerStep 0 (eraseTerm expansionTerm) (eraseTerm ErasureBoundary.identityTerm) :=
  .congLam (Presentation.StepCore.betaPi (.var 1) (.lam (.app (.var 1) (.var 0))))

/-- **Failure of subject expansion**: the expansion is not the erasure of any
simple term of type `atom → atom`. -/
theorem expansion_not_erasure (t : Term [] (.arr .atom .atom)) :
    eraseTerm t ≠ eraseTerm expansionTerm := by
  intro same
  cases t with
  | var v => cases v
  | app _ _ => cases same
  | lam body =>
      have hb := Presentation.Tm.lam.inj same
      cases body with
      | var _ => cases hb
      | app _ a =>
          have ha := (Presentation.Tm.app.inj hb).2
          cases a with
          | var _ => cases ha
          | app _ _ => cases ha
          | lam aBody =>
              have hab := Presentation.Tm.lam.inj ha
              cases aBody with
              | var _ => cases hab
              | lam _ => cases hab
              | app g _ =>
                  have hg := (Presentation.Tm.app.inj hab).1
                  cases g with
                  | lam _ => cases hg
                  | app _ _ => cases hg
                  | var v =>
                      obtain ⟨wrongType, -⟩ :=
                        eraseVar_type_eq v (.succ .zero : Var (_ :: [.atom]) .atom)
                          (Presentation.Tm.var.inj hg)
                      cases wrongType

/-- **Control: the back law fails on the slice of erasures of every type**:
subject expansion fails for simple types, so a slice term convertible with an
erasure of type `A` need not be an erasure of type `A`. -/
theorem back_beta_slice_fails :
    ¬ Back (toSlice [] (.arr .atom .atom)) ((towerConversionSetoid 0).comap Subtype.val)
      (betaObserver [] (.arr .atom .atom)) := by
  intro back
  obtain ⟨_, _, same⟩ := back (m := ErasureBoundary.identityTerm)
    (s := ⟨eraseTerm expansionTerm, _, expansionTerm, rfl⟩)
    (.symm _ _ (.rel _ _ expansion_towerStep))
  exact expansion_not_erasure _ (congrArg Subtype.val same)

theorem forth_beta_slice :
    Forth (toSlice Γ A) ((towerConversionSetoid Γ.length).comap Subtype.val) (betaObserver Γ A) :=
  fun _ _ conv => BetaConv.erase conv

/-- **The β square fails on the slice of all types**: forgetting and
translating do not commute. -/
theorem beta_slice_square_fails :
    ¬ ∀ K : Set (sliceTerms []),
      toSlice [] (.arr .atom .atom) ⁻¹' saturation ((towerConversionSetoid 0).comap Subtype.val) K =
        saturation (betaObserver [] (.arr .atom .atom)) (toSlice [] (.arr .atom .atom) ⁻¹' K) :=
  (square_fails_of_back (forth_beta_slice [] (.arr .atom .atom)) back_beta_slice_fails).1

theorem forth_beta_typedSlice :
    Forth (toTypedSlice Γ A) ((towerConversionSetoid Γ.length).comap Subtype.val)
      (betaObserver Γ A) :=
  fun _ _ conv => BetaConv.erase conv

/-- **Back for β on the typed slice**: the candidate's conversion between
erasures of one type is β-conversion. -/
theorem back_beta_typedSlice :
    Back (toTypedSlice Γ A) ((towerConversionSetoid Γ.length).comap Subtype.val)
      (betaObserver Γ A) := by
  rintro m ⟨_, t, rfl⟩ related
  exact ⟨t, (towerConv_iff_betaConv' m t).mp related, rfl⟩

/-- **The β square commutes on the typed slice**: forgetting and translating
commute for every class. -/
theorem beta_typedSlice_comm (K : Set (typedSlice Γ A)) :
    toTypedSlice Γ A ⁻¹' saturation ((towerConversionSetoid Γ.length).comap Subtype.val) K =
      saturation (betaObserver Γ A) (toTypedSlice Γ A ⁻¹' K) :=
  (square_of_laws (forth_beta_typedSlice Γ A) (back_beta_typedSlice Γ A)).1 K

/-- **Beck–Chevalley for the β square on the typed slice.** -/
theorem beta_typedSlice_beckChevalley (φ : Set (typedSlice Γ A)) :
    viewMap (forth_beta_typedSlice Γ A) ⁻¹'
        (Quotient.mk ((towerConversionSetoid Γ.length).comap Subtype.val) '' φ) =
      Quotient.mk (betaObserver Γ A) '' (toTypedSlice Γ A ⁻¹' φ) :=
  (square_of_laws (forth_beta_typedSlice Γ A) (back_beta_typedSlice Γ A)).2.1 φ

theorem forth_beta_typedSliceExec :
    Forth (toTypedSlice Γ A) ((execConvSetoid Γ.length).comap Subtype.val) (betaObserver Γ A) :=
  fun l r conv => (execConv_iff_betaConv l r).mpr conv

theorem back_beta_typedSliceExec :
    Back (toTypedSlice Γ A) ((execConvSetoid Γ.length).comap Subtype.val) (betaObserver Γ A) := by
  rintro m ⟨_, t, rfl⟩ related
  exact ⟨t, (execConv_iff_betaConv m t).mp related, rfl⟩

/-- **The β square commutes on the typed slice for the executable package's
conversion too.** -/
theorem beta_typedSliceExec_comm (K : Set (typedSlice Γ A)) :
    toTypedSlice Γ A ⁻¹' saturation ((execConvSetoid Γ.length).comap Subtype.val) K =
      saturation (betaObserver Γ A) (toTypedSlice Γ A ⁻¹' K) :=
  (square_of_laws (forth_beta_typedSliceExec Γ A) (back_beta_typedSliceExec Γ A)).1 K

/-! ### The βη square -/

/-- **Forth for βη**: βη-convertible terms have typed-equal erasures. -/
theorem forth_betaEta_typedRaw :
    Forth (toTypedRaw Γ A) (typedEqual Γ A) (betaEtaObserver Γ A) :=
  fun _ _ conv => equal_of_betaEtaConv rulesHeads conv

/-- `fst (pair id id)`, with `id` the erased identity. -/
def fstPair : Presentation.Tower.Tm 0 :=
  .fst (.pair (eraseTerm ErasureBoundary.identityTerm) (eraseTerm ErasureBoundary.identityTerm))

/-- The pair type of two functions on the ground type. -/
theorem pairType_typed :
    Typed rules .nil (.sigma (eraseTypeAt 0 (.arr .atom .atom)) (eraseTypeAt 1 (.arr .atom .atom)))
      (.head (.sort (.max (levelOf (.arr .atom .atom)) (levelOf (.arr .atom .atom))))) :=
  .sigmaForm (type_formed rulesHeads (.arr .atom .atom) .nil) (rulesHeads.universes _)
    (type_formed rulesHeads (.arr .atom .atom) _) (rulesHeads.universes _)
    (rulesHeads.product _ _)

/-- **`fst (pair id id)` is typed at the erased type `atom → atom`.** -/
theorem fstPair_typed : Typed rules (eraseContext []) fstPair (eraseTypeAt 0 (.arr .atom .atom)) :=
  .fstElim (.pairIntro pairType_typed (rulesHeads.universes _)
    (term_typed rulesHeads ErasureBoundary.identityTerm)
    (term_typed rulesHeads ErasureBoundary.identityTerm))

/-- **It is typed-equal to the erased identity**, by the pair's β-rule. -/
theorem fstPair_equal :
    Equal rules (eraseContext []) (eraseTerm ErasureBoundary.identityTerm) fstPair
      (eraseTypeAt 0 (.arr .atom .atom)) :=
  .symm (.betaFst pairType_typed (rulesHeads.universes _)
    (term_typed rulesHeads ErasureBoundary.identityTerm)
    (term_typed rulesHeads ErasureBoundary.identityTerm))

theorem fstPair_not_erasure (B : Ty) (t : Term [] B) : eraseTerm t ≠ fstPair := by
  intro same
  cases t <;> cases same

/-- **Control: the back law for βη fails on typed raw terms**: a typed raw term
equal to an erasure need not be an erasure. -/
theorem back_betaEta_typedRaw_fails :
    ¬ Back (toTypedRaw [] (.arr .atom .atom)) (typedEqual [] (.arr .atom .atom))
      (betaEtaObserver [] (.arr .atom .atom)) := by
  intro back
  obtain ⟨_, _, same⟩ := back (m := ErasureBoundary.identityTerm)
    (s := ⟨fstPair, fstPair_typed⟩) fstPair_equal
  exact fstPair_not_erasure _ _ (congrArg Subtype.val same)

/-- **The βη square fails on typed raw terms**: forgetting and translating do
not commute. -/
theorem betaEta_typedRaw_square_fails :
    ¬ ∀ K : Set (TypedRaw [] (.arr .atom .atom)),
      toTypedRaw [] (.arr .atom .atom) ⁻¹' saturation (typedEqual [] (.arr .atom .atom)) K =
        saturation (betaEtaObserver [] (.arr .atom .atom)) (toTypedRaw [] (.arr .atom .atom) ⁻¹' K) :=
  (square_fails_of_back (forth_betaEta_typedRaw [] (.arr .atom .atom))
    back_betaEta_typedRaw_fails).1

theorem forth_betaEta_typedSlice :
    Forth (toTypedSlice Γ A) (sliceEqual Γ A) (betaEtaObserver Γ A) :=
  fun _ _ conv => equal_of_betaEtaConv rulesHeads conv

/-- **Back for βη on the typed slice**: typed-equal erasures of one type are
βη-convertible. -/
theorem back_betaEta_typedSlice :
    Back (toTypedSlice Γ A) (sliceEqual Γ A) (betaEtaObserver Γ A) := by
  rintro m ⟨_, t, rfl⟩ related
  exact ⟨t, betaEtaConv_of_equal related, rfl⟩

/-- **The βη square commutes on the typed slice**: forgetting and translating
commute for every class. -/
theorem betaEta_typedSlice_comm (K : Set (typedSlice Γ A)) :
    toTypedSlice Γ A ⁻¹' saturation (sliceEqual Γ A) K =
      saturation (betaEtaObserver Γ A) (toTypedSlice Γ A ⁻¹' K) :=
  (square_of_laws (forth_betaEta_typedSlice Γ A) (back_betaEta_typedSlice Γ A)).1 K

/-- **Beck–Chevalley for the βη square on the typed slice.** -/
theorem betaEta_typedSlice_beckChevalley (φ : Set (typedSlice Γ A)) :
    viewMap (forth_betaEta_typedSlice Γ A) ⁻¹' (Quotient.mk (sliceEqual Γ A) '' φ) =
      Quotient.mk (betaEtaObserver Γ A) '' (toTypedSlice Γ A ⁻¹' φ) :=
  (square_of_laws (forth_betaEta_typedSlice Γ A) (back_betaEta_typedSlice Γ A)).2.1 φ

end Squares

/-! ## The forgetting arrow β → βη on both sides -/

section Forgetting

open Mettapedia.GSLT.Scope
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel
open ConversionDecision (etaVariable etaExpansion eta_not_betaConvertible)

/-- A pure λ-term without β-redex takes no step in a package that does not fire
at pure λ-terms. -/
theorem no_step_of_pure_redexFree {root : Presentation.RootComputation Presentation.Tower.Head}
    {headEq : Presentation.Tower.Head → Presentation.Tower.Head → Prop} (free : RootFree root)
    {n : ℕ} {t u : Presentation.Tower.Tm n} (pure : PureLambda t) (redexFree : RedexFree t) :
    ¬ Presentation.StepCore root headEq t u := fun step =>
  RedexFree.no_step (root := Presentation.RootComputation.empty)
    (headEq := fun _ _ => False) (fun impossible => impossible) redexFree
    (StepCore.transfer free step pure)

/-- **The η pair is not β-convertible**, without choice: the executable
package's Church–Rosser theorem, and neither erasure takes a step. -/
theorem eta_not_betaConv : ¬ BetaConv etaVariable etaExpansion := by
  intro conv
  obtain ⟨common, stepsL, stepsR⟩ := churchRosser (rulesConv_of_towerConv conv.erase)
  have stays : ∀ {t c : Presentation.Tower.Tm 1}, PureLambda t → RedexFree t →
      Relation.ReflTransGen (Presentation.StepCore rules.computation rules.headEq) t c → c = t := by
    intro t c pure redexFree steps
    induction steps with
    | refl => rfl
    | tail _ step ih =>
        subst ih
        exact (no_step_of_pure_redexFree rulesRootFree pure redexFree step).elim
  have left := stays (eraseTerm_pure etaVariable) (.var 0) stepsL
  have right := stays (eraseTerm_pure etaExpansion)
    (.lam (.app (.var 1) (fun _ same => by cases same) (.var 0))) stepsR
  rw [left] at right
  cases right

/-- Adding every proposition-code decoder does not turn the simple eta pair
into a definitional conversion. -/
theorem eta_not_objectConversion :
    ¬ Presentation.Conv CodeModel.objectRules.headEq
      (eraseTerm etaVariable) (eraseTerm etaExpansion) CodeModel.objectRules.computation :=
  fun conversion => eta_not_betaConv (betaConv_of_objectConversion conversion)

/-- **Forgetting only on the raw side breaks the back law**: β on the simple
side against the typed η-equality on the typed slice.  The η pair is
typed-equal and not β-convertible. -/
theorem back_beta_equal_fails :
    ¬ Back (toTypedSlice [.arr .atom .atom] (.arr .atom .atom))
      (sliceEqual [.arr .atom .atom] (.arr .atom .atom))
      (betaObserver [.arr .atom .atom] (.arr .atom .atom)) := by
  intro back
  obtain ⟨m, conv, same⟩ := back (m := etaVariable)
    (s := toTypedSlice _ _ etaExpansion)
    (equal_of_betaEtaConv rulesHeads (.symm _ _ eta_related))
  exact eta_not_betaConv (.trans _ _ _ conv (betaConv_of_erase_eq m etaExpansion
    (congrArg Subtype.val same)))

theorem forth_beta_equal :
    Forth (toTypedSlice [.arr .atom .atom] (.arr .atom .atom))
      (sliceEqual [.arr .atom .atom] (.arr .atom .atom))
      (betaObserver [.arr .atom .atom] (.arr .atom .atom)) :=
  fun _ _ conv => equal_of_betaEtaConv rulesHeads
    (Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Conv.ofBetaConv conv)

/-- **Forgetting only on the simple side breaks the forth law**: βη on the
simple side against the candidate's conversion on the typed slice. -/
theorem forth_betaEta_conv_fails :
    ¬ Forth (toTypedSlice [.arr .atom .atom] (.arr .atom .atom))
      ((towerConversionSetoid 1).comap Subtype.val)
      (betaEtaObserver [.arr .atom .atom] (.arr .atom .atom)) := fun forth =>
  eta_not_betaConv (.symm _ _ ((towerConv_iff_betaConv' etaExpansion etaVariable).mp
    (forth eta_related)))

/-- **Forgetting on both sides commutes with translating**: on the typed slice,
translating along the β square and then forgetting to βη is forgetting to the
typed η-equality and then translating along the βη square. -/
theorem forget_translate_both (Γ : List Ty) (A : Ty) (K : Set (typedSlice Γ A)) :
    saturation (betaEtaObserver Γ A)
        (toTypedSlice Γ A ⁻¹' saturation ((towerConversionSetoid Γ.length).comap Subtype.val) K) =
      toTypedSlice Γ A ⁻¹' saturation (sliceEqual Γ A) K := by
  rw [beta_typedSlice_comm, saturation_saturation beta_le_betaEta, betaEta_typedSlice_comm]

/-- The typed-slice terms whose simple preimages have the β-normal form
`target`. -/
def sliceNormalForm (Γ : List Ty) (A : Ty) (target : Term Γ A) : Set (typedSlice Γ A) :=
  {s | ∃ t, eraseTerm t = s.1 ∧ normalForm t = target}

theorem preimage_sliceNormalForm {Γ : List Ty} {A : Ty} (target : Term Γ A) :
    toTypedSlice Γ A ⁻¹' sliceNormalForm Γ A target = normalFormPredicate target := by
  ext t
  constructor
  · rintro ⟨t', same, normal⟩
    change normalForm t = target
    rw [← normal]
    exact ((ConversionDecision.normalize_eq_iff_betaConv t t').mpr
      (.symm _ _ (betaConv_of_erase_eq t' t same)))
  · intro normal
    exact ⟨t, rfl, normal⟩

/-- **The raw normal-form predicate is visible to the candidate's conversion**
on the typed slice: descent is reflected along the commuting β square. -/
theorem sliceNormalForm_observable_conv {Γ : List Ty} {A : Ty} (target : Term Γ A) :
    sliceNormalForm Γ A target ∈
      observable predicateSat ((towerConversionSetoid Γ.length).comap Subtype.val) :=
  observable_of_preimage (back_beta_typedSlice Γ A) (toTypedSlice_surjective Γ A)
    ((preimage_sliceNormalForm target).symm ▸ normalFormPredicate_observable_beta target)

/-- **Control: it is not visible to the typed η-equality**: descent along the
forth law of the βη square would make the simple normal-form predicate
visible to βη, which `normalFormPredicate_not_observable_betaEta` refutes. -/
theorem sliceNormalForm_not_observable_equal :
    sliceNormalForm [.arr .atom .atom] (.arr .atom .atom) etaVariable ∉
      observable predicateSat (sliceEqual [.arr .atom .atom] (.arr .atom .atom)) := by
  intro visible
  have pulled := observable_preimage (forth_betaEta_typedSlice _ _) visible
  rw [preimage_sliceNormalForm] at pulled
  exact normalFormPredicate_not_observable_betaEta pulled

/-- The typed-slice terms whose simple preimages are β-convertible to
`target`: the β-class of `target`, read on raw terms. -/
def sliceBetaClass (Γ : List Ty) (A : Ty) (target : Term Γ A) : Set (typedSlice Γ A) :=
  {s | ∃ t, eraseTerm t = s.1 ∧ BetaConv t target}

theorem preimage_sliceBetaClass {Γ : List Ty} {A : Ty} (target : Term Γ A) :
    toTypedSlice Γ A ⁻¹' sliceBetaClass Γ A target = {t | BetaConv t target} := by
  ext t
  constructor
  · rintro ⟨t', same, conv⟩
    exact .trans _ _ _ (betaConv_of_erase_eq t t' same.symm) conv
  · intro conv
    exact ⟨t, rfl, conv⟩

/-- **The β-class of a term, read on the typed slice, is visible to the
candidate's conversion**, without choice. -/
theorem sliceBetaClass_observable_conv {Γ : List Ty} {A : Ty} (target : Term Γ A) :
    sliceBetaClass Γ A target ∈
      observable predicateSat ((towerConversionSetoid Γ.length).comap Subtype.val) := by
  refine observable_of_preimage (back_beta_typedSlice Γ A) (toTypedSlice_surjective Γ A) ?_
  rw [preimage_sliceBetaClass]
  intro t t' conv
  exact ⟨fun toTarget => .trans _ _ _ (.symm _ _ conv) toTarget,
    fun toTarget => .trans _ _ _ conv toTarget⟩

/-- **Control, without choice: the β-class of the η-variable is not visible to
the typed η-equality.** -/
theorem sliceBetaClass_not_observable_equal :
    sliceBetaClass [.arr .atom .atom] (.arr .atom .atom) etaVariable ∉
      observable predicateSat (sliceEqual [.arr .atom .atom] (.arr .atom .atom)) := by
  intro visible
  have pulled := observable_preimage (forth_betaEta_typedSlice _ _) visible
  rw [preimage_sliceBetaClass] at pulled
  exact eta_not_betaConv (.symm _ _ ((pulled eta_related).mpr (.refl _)))

/-- The simple terms with the denotation of `target` in every function space. -/
def denotationClass {Γ : List Ty} {A : Ty} (target : Term Γ A) : Set (Term Γ A) :=
  {t | ∀ (Ground : Type) (environment : Environment Ground Γ),
    t.denote environment = target.denote environment}

theorem denotationClass_observable_betaEta {Γ : List Ty} {A : Ty} (target : Term Γ A) :
    denotationClass target ∈ observable predicateSat (betaEtaObserver Γ A) := by
  intro t t' conv
  exact ⟨fun denotes Ground environment => (conv.denote environment).symm.trans
      (denotes Ground environment),
    fun denotes Ground environment => (conv.denote environment).trans (denotes Ground environment)⟩

/-- The typed-slice terms whose simple preimages denote as `target` does. -/
def sliceDenotation (Γ : List Ty) (A : Ty) (target : Term Γ A) : Set (typedSlice Γ A) :=
  {s | ∃ t, eraseTerm t = s.1 ∧ t ∈ denotationClass target}

theorem preimage_sliceDenotation {Γ : List Ty} {A : Ty} (target : Term Γ A) :
    toTypedSlice Γ A ⁻¹' sliceDenotation Γ A target = denotationClass target := by
  ext t
  constructor
  · rintro ⟨t', same, denotes⟩ Ground environment
    exact ((betaConv_of_erase_eq t t' same.symm).denote environment).trans
      (denotes Ground environment)
  · intro denotes
    exact ⟨t, rfl, denotes⟩

/-- **Positive control: the denotation, read on the typed slice, is visible to
the typed η-equality**: descent is reflected along the commuting βη square,
which needs the completeness of the typed equality on erasures. -/
theorem sliceDenotation_observable_equal {Γ : List Ty} {A : Ty} (target : Term Γ A) :
    sliceDenotation Γ A target ∈ observable predicateSat (sliceEqual Γ A) :=
  observable_of_preimage (back_betaEta_typedSlice Γ A) (toTypedSlice_surjective Γ A)
    ((preimage_sliceDenotation target).symm ▸ denotationClass_observable_betaEta target)

end Forgetting

end Mettapedia.GSLT.Scope.SimpleFragmentBeckChevalley
