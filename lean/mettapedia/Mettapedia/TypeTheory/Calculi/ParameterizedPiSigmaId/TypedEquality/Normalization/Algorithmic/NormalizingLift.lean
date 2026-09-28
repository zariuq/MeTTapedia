import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Lift
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Renaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.NeutralSubstitution

/-!
# Lifting spine comparisons by strong normalization of types

Spine comparisons lift to comparisons at the type (`SpineLift`) in every rule
package whose types are strongly normalizing, given the facts about the
weak-head forms of its types, when substituting neutral terms creates no
weak-head redex and liftable values have the shapes of their types
(`LiftableForms`): constructor spines are functions at dependent function
types and never values of universes or dependent pair types, and type
constants of inductive types are values only of universes
(`SpineLift.ofNormalizing`). No reducibility model is used.

The proof is by well-founded induction on the components of a type
(`TypeComponent`): the domain and the codomain of the dependent function or pair
type it weakly head reduces to. Components are well founded on strongly
normalizing terms (`TypeComponent.acc`), by induction on strong normalization
and, for the parts of a type former, on their structure: a reduction of a part
of a type former is a reduction of the former.

A codomain is used at an argument: at the fresh variable for a dependent
function type, and at the first projection of a neutral term for a dependent
pair type. So the statement is proved at every instance of a type by neutral
terms (`LiftsAt`). Such an instance reduces as the type does, since
substituting neutral terms creates no weak-head redex (`WhRed.of_neutralSub`);
its weak-head form is the instance of the type's, and the arguments extend the
substitution by neutral terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Weak-head steps are steps of the directed reduction -/

section Directed

variable {root : RootComputation Head} {headEq : Head → Head → Prop}

/-- A step of the function of a spine is a step of the spine. -/
theorem StepCore.appSpine_fun {n : Nat} :
    ∀ (args : List (Tm Head n)) {f f' : Tm Head n},
      StepCore root headEq f f' → StepCore root headEq (appSpine f args) (appSpine f' args)
  | [], _, _, step => step
  | _ :: args, _, _, step => StepCore.appSpine_fun args (.congAppFun step)

/-- A step of one argument of a spine is a step of the spine. -/
theorem StepCore.appSpine_arg {n : Nat} {f : Tm Head n} (before after : List (Tm Head n))
    {x y : Tm Head n} (step : StepCore root headEq x y) :
    StepCore root headEq (appSpine f (before ++ x :: after)) (appSpine f (before ++ y :: after)) := by
  rw [appSpine_append, appSpine_append]
  exact StepCore.appSpine_fun _ (.congAppArg step)

/-- A weak-head step is a step of the directed reduction. -/
theorem WhStep.directed {R : Rules Head} {roles : Roles Head} {n : Nat} {t u : Tm Head n}
    (step : WhStep R roles t u) : StrongNormalization.Reduces R t u := by
  induction step with
  | beta body a => exact .betaPi body a
  | fstPair a b => exact .betaSigmaFst a b
  | sndPair a b => exact .betaSigmaSnd a b
  | root step => exact .root step
  | appFun _ ih => exact .congAppFun ih
  | fst _ ih => exact .congFst ih
  | snd _ ih => exact .congSnd ih
  | scrutinee _ _ focus _ ih =>
      obtain ⟨before, after, x, y, rfl, rfl, step⟩ :=
        focus.lift (fun _ before after {_ _} step => StepCore.appSpine_arg before after step)
          (.congRefl ·) ih
      exact StepCore.appSpine_arg before after step

/-- A weak-head reduction is empty or begins with a step. -/
theorem WhRed.cases_head {R : Rules Head} {roles : Roles Head} {n : Nat} {t w : Tm Head n}
    (red : WhRed R roles t w) : t = w ∨ ∃ t₁, WhStep R roles t t₁ ∧ WhRed R roles t₁ w := by
  induction red using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl rfl
  | head step rest _ => exact .inr ⟨_, step, rest⟩

end Directed

/-! ## The components of types -/

/-- The parts of the type formers: the domain and the codomain of a dependent
function or pair type. -/
inductive TypePart : (Σ k, Tm Head k) → (Σ k, Tm Head k) → Prop where
  | piDom {k : Nat} (A : Tm Head k) (B : Tm Head (k + 1)) : TypePart ⟨k, A⟩ ⟨k, .pi A B⟩
  | piCod {k : Nat} (A : Tm Head k) (B : Tm Head (k + 1)) : TypePart ⟨k + 1, B⟩ ⟨k, .pi A B⟩
  | sigmaDom {k : Nat} (A : Tm Head k) (B : Tm Head (k + 1)) :
      TypePart ⟨k, A⟩ ⟨k, .sigma A B⟩
  | sigmaCod {k : Nat} (A : Tm Head k) (B : Tm Head (k + 1)) :
      TypePart ⟨k + 1, B⟩ ⟨k, .sigma A B⟩

/-- The parts of type formers are well founded. -/
theorem TypePart.acc : ∀ x : Σ k, Tm Head k, Acc TypePart x := by
  rintro ⟨k, A⟩
  induction A with
  | var => exact .intro _ fun _ part => by cases part
  | const => exact .intro _ fun _ part => by cases part
  | head => exact .intro _ fun _ part => by cases part
  | pi A B ihA ihB => exact .intro _ fun _ part => by cases part <;> assumption
  | sigma A B ihA ihB => exact .intro _ fun _ part => by cases part <;> assumption
  | id => exact .intro _ fun _ part => by cases part
  | lam => exact .intro _ fun _ part => by cases part
  | app => exact .intro _ fun _ part => by cases part
  | pair => exact .intro _ fun _ part => by cases part
  | fst => exact .intro _ fun _ part => by cases part
  | snd => exact .intro _ fun _ part => by cases part
  | refl => exact .intro _ fun _ part => by cases part

/-- A step of a part of a type former is a step of the former. -/
theorem TypePart.reduces {R : Rules Head} {y x : Σ k, Tm Head k} (part : TypePart y x)
    {y' : Tm Head y.1} (step : StrongNormalization.Reduces R y.2 y') :
    ∃ x' : Tm Head x.1, StrongNormalization.Reduces R x.2 x' ∧ TypePart ⟨y.1, y'⟩ ⟨x.1, x'⟩ := by
  cases part with
  | piDom A B => exact ⟨_, .congPiDom step, .piDom _ _⟩
  | piCod A B => exact ⟨_, .congPiCod step, .piCod _ _⟩
  | sigmaDom A B => exact ⟨_, .congSigmaDom step, .sigmaDom _ _⟩
  | sigmaCod A B => exact ⟨_, .congSigmaCod step, .sigmaCod _ _⟩

/-- A step of an iterated part of a term is a step of the term. -/
theorem TypePart.star_reduces {R : Rules Head} {y x : Σ k, Tm Head k}
    (parts : Relation.ReflTransGen TypePart y x) :
    ∀ {y' : Tm Head y.1}, StrongNormalization.Reduces R y.2 y' →
      ∃ x' : Tm Head x.1, StrongNormalization.Reduces R x.2 x' ∧
        Relation.ReflTransGen TypePart ⟨y.1, y'⟩ ⟨x.1, x'⟩ := by
  induction parts using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun step => ⟨_, step, .refl⟩
  | head part _ ih =>
      intro y' step
      obtain ⟨b', stepB, partB⟩ := part.reduces step
      obtain ⟨x', stepX, rest⟩ := ih stepB
      exact ⟨x', stepX, .head partB rest⟩

/-- The components of a term: the parts of the type former it weakly head
reduces to. -/
def TypeComponent (R : Rules Head) (roles : Roles Head) (x y : Σ k, Tm Head k) : Prop :=
  ∃ z : Tm Head y.1, WhRed R roles y.2 z ∧ TypePart x ⟨y.1, z⟩

/-- **The components of a strongly normalizing term are well founded.** -/
theorem TypeComponent.acc {R : Rules Head} {roles : Roles Head} {k : Nat} {A : Tm Head k}
    (sn : StrongNormalization.SN R A) : Acc (TypeComponent R roles) ⟨k, A⟩ := by
  suffices key : ∀ {k : Nat} {A : Tm Head k}, StrongNormalization.SN R A →
      ∀ y, Relation.ReflTransGen TypePart y ⟨k, A⟩ → Acc (TypeComponent R roles) y from
    key sn _ .refl
  intro k A sn
  induction sn with
  | intro A _ ihA =>
      intro y parts
      induction TypePart.acc y with
      | intro y _ ihY =>
          refine .intro y fun z ⟨w, red, part⟩ => ?_
          rcases WhRed.cases_head red with rfl | ⟨y₁, step, rest⟩
          · exact ihY z part (.head part parts)
          · obtain ⟨A', stepA, parts'⟩ := TypePart.star_reduces parts (WhStep.directed step)
            exact (ihA A' stepA _ parts').inv ⟨w, rest, part⟩

/-! ## The shapes of liftable values -/

variable {S : Setting Head L}

/-- The shapes of liftable values at the weak-head forms of their types:
constructor spines are functions at dependent function types, and never values
of universes or of dependent pair types; type constants of inductive types are
values only of universes. -/
structure LiftableForms (S : Setting Head L) : Prop where
  constructor_universe : ∀ {n : Nat} {Γ : Ctx Head n} {k : DeclName} {arity : Nat}
    {args : List (Tm Head n)} {u : Head}, CtxFormed S.R Γ → S.roles k = .constructor arity →
      S.R.isUniverse u → ¬ Typed S.R Γ (appSpine (.const k) args) (.head u)
  constructor_pi : ∀ {n : Nat} {Γ : Ctx Head n} {k : DeclName} {arity : Nat}
    {args : List (Tm Head n)} {A : Tm Head n} {B : Tm Head (n + 1)}, CtxFormed S.R Γ →
      S.roles k = .constructor arity → Typed S.R Γ (appSpine (.const k) args) (.pi A B) →
        args.length < arity
  constructor_sigma : ∀ {n : Nat} {Γ : Ctx Head n} {k : DeclName} {arity : Nat}
    {args : List (Tm Head n)} {A : Tm Head n} {B : Tm Head (n + 1)}, CtxFormed S.R Γ →
      S.roles k = .constructor arity → ¬ Typed S.R Γ (appSpine (.const k) args) (.sigma A B)
  inductive_universe : ∀ {n : Nat} {Γ : Ctx Head n} {T : DeclName}
    {ctors : List (DeclName × List (Field Head))} {A : Tm Head n}, CtxFormed S.R Γ →
      S.roles T = .inductive ctors → Typed S.R Γ (.const T) A → IsTypeForm S.roles A →
        ∃ u, A = .head u ∧ S.R.isUniverse u

/-! ## Lifting at every instance of a type by neutral terms -/

/-- Liftable terms equal at an instance of `C` by neutral terms and compared as
spines in every formed world are compared at it. -/
def LiftsAt (S : Setting Head L) {k : Nat} (C : Tm Head k) : Prop :=
  ∀ ⦃m : Nat⦄ ⦃Γ : Ctx Head m⦄ ⦃σ : Sub Head k m⦄, NeutralSub S.roles σ → CtxFormed S.R Γ →
    ∀ ⦃t u : Tm Head m⦄, Liftable S.roles t → Liftable S.roles u →
      Equal S.R Γ t u (Presentation.subst σ C) →
        SpinesEverywhere S Γ t u (Presentation.subst σ C) →
          Algorithmic S.R S.roles (.terms Γ t u (Presentation.subst σ C))

section Lift

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (forms : LiftableForms S) (reflecting : NeutralReflecting S.R S.roles)
include facts roots heads algebra forms reflecting

/-- **Spine comparisons lift at every instance by neutral terms of a type whose
components are well founded**, by induction on the components. -/
theorem liftsAt_of_acc {x : Σ k, Tm Head k} (acc : Acc (TypeComponent S.R S.roles) x) :
    LiftsAt S x.2 := by
  have sound := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.sound facts roots heads algebra d
  have conv := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.converts facts roots heads algebra d
  induction acc with
  | intro x _ ih =>
  obtain ⟨k, C⟩ := x
  intro m Γ σ neutral formed t s lt ls equal spines
  obtain ⟨tt, ts⟩ := Equal.typed equal formed
  obtain ⟨A', red, form⟩ := facts.typeForm (Typed.isType tt formed) formed
  obtain ⟨C', redC, hC'⟩ := WhRed.of_neutralSub S.shape reflecting neutral red.red
  have tt' := Typed.convType tt red.typeEq
  have ts' := Typed.convType ts red.typeEq
  have equal' := Equal.convType equal red.typeEq
  obtain ⟨U, dU, leU⟩ := spines.here formed
  obtain ⟨U', dW, eU, fU⟩ := Algorithmic.spinesW_of_spines facts roots heads algebra formed dU
  have spineForm : ∀ {v : Tm Head m}, Liftable S.roles v → Typed S.R Γ v A' →
      (∀ u, A' = .head u → ¬ S.R.isUniverse u) → SpineForm S.roles v := by
    intro v lv tv notUniverse
    rcases lv with nv | ⟨k', arity, args, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
    · exact .inl nv
    · exact .inr ⟨k', arity, args, role, rfl⟩
    · obtain ⟨u, e, hu⟩ := forms.inductive_universe formed role tv form
      exact absurd hu (notUniverse u e)
  rcases form with ⟨h, rfl⟩ | ⟨D', E', rfl⟩ | ⟨D', E', rfl⟩ | ⟨X, a, b, rfl⟩ | neutralA |
    ⟨T, ctors, role, rfl⟩
  · -- A head: a universe, compared as types, or a head compared as spines.
    rcases S.levels.universe_decided h with hu | notUniverse
    · have le' := (eU.symm).toLe.trans (leU.trans red.typeEq.toLe)
      obtain ⟨v, rfl, hv⟩ :=
        TypeLe.universe_form facts formed le' hu ((TypeEq.isType eU formed).2) fU
      rcases lt with nt | ⟨k', arity, args, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
      · have ns : Neutral S.roles s := by
          rcases ls with ns | ⟨k', arity, args, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
          · exact ns
          · exact absurd ts' (forms.constructor_universe formed role hu)
          · cases dU with
            | const => exact absurd rfl (nt.ne_inductive role)
        exact .terms red (.inl ⟨h, rfl⟩) (RedTm.refl tt') (RedTm.refl ts')
          (.univ hu tt' ts' (.neutralTypes nt ns hv dW))
      · exact absurd tt' (forms.constructor_universe formed role hu)
      · cases dU with
        | const =>
            exact .terms red (.inl ⟨h, rfl⟩) (RedTm.refl tt') (RedTm.refl ts')
              (.univ hu tt' ts' (.inductiveType role ⟨h, hu, tt'⟩))
    · have notHead : ∀ u, (.head h : Tm Head m) = .head u → ¬ S.R.isUniverse u := by
        intro u e hu
        cases e
        exact notUniverse hu
      exact .terms red (.inl ⟨h, rfl⟩) (RedTm.refl tt') (RedTm.refl ts')
        (.spine (.inr (.inr (.inr ⟨h, rfl, notUniverse⟩))) (spineForm lt tt' notHead)
          (spineForm ls ts' notHead) tt' ts' dW)
  · -- A dependent function type: compared at the fresh variable.
    rcases subst_eq_pi_or_var hC'.symm with ⟨i, rfl⟩ | ⟨D, E, rfl, rfl, rfl⟩
    · exact absurd hC'.symm ((neutral i).not_former.2.1 _ _)
    have ihD : LiftsAt S D := ih ⟨k, D⟩ ⟨_, redC, .piDom D E⟩
    have ihE : LiftsAt S E := ih ⟨k + 1, E⟩ ⟨_, redC, .piCod D E⟩
    have isPi : IsType S.R Γ
        (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) E)) := red.targetType
    obtain ⟨domType, -⟩ := IsType.pi_parts isPi
    have isFun : ∀ {v : Tm Head m}, Liftable S.roles v →
        Typed S.R Γ v (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) E)) →
          IsFun S.roles v := by
      intro v lv tv
      rcases lv with nv | ⟨k', arity, args, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
      · exact .inr (.inl nv)
      · exact .inr (.inr ⟨k', args, arity, .inl role, forms.constructor_pi formed role tv, rfl⟩)
      · obtain ⟨u, e, -⟩ := forms.inductive_universe formed role tv (.inr (.inl ⟨_, _, rfl⟩))
        cases e
    have funT := isFun lt tt'
    have funS := isFun ls ts'
    have formedD : CtxFormed S.R (.snoc Γ (Presentation.subst σ D)) := .snoc formed domType
    -- the domain at the fresh variable
    have eD : Presentation.subst (fun i => Presentation.rename wk (σ i)) D =
        Presentation.rename wk (Presentation.subst σ D) := (rename_subst wk σ D).symm
    have dVar₀ : Algorithmic S.R S.roles (.terms (.snoc Γ (Presentation.subst σ D)) (.var 0)
        (.var 0) (Presentation.rename wk (Presentation.subst σ D))) := by
      have d := ihD (neutral.rename wk) formedD (.inl (.var 0)) (.inl (.var 0))
        (by rw [eD]; exact .refl (.var 0)) (by rw [eD]; exact SpinesEverywhere.var (S := S) 0)
      rwa [eD] at d
    -- the applications to the fresh variable, compared as spines in every world
    have spines₁ : SpinesEverywhere S (.snoc Γ (Presentation.subst σ D))
        (.app (Presentation.rename wk t) (.var 0)) (.app (Presentation.rename wk s) (.var 0))
        (Presentation.subst (liftSub σ) E) := by
      intro m' Θ ρ' w'
      have w'' : World S Γ Θ (fun i => ρ' (wk i)) := (World.fresh formed domType).comp w'
      have formedΘ := w'.2
      obtain ⟨U, dU, leU⟩ := spines w''
      have eA := red.typeEq.rename w''.1
      obtain ⟨A₂, B₂, dW, eDom, leCod⟩ := Algorithmic.spinesW_pi facts roots heads
        algebra formedΘ dU (leU.trans eA.toLe) ((TypeEq.isType eA formedΘ).2)
      have lookupVar : Ctx.lookup Θ (ρ' 0) =
          Presentation.rename (fun i => ρ' (wk i)) (Presentation.subst σ D) := by
        rw [w'.1 0]
        exact rename_rename wk ρ' _
      have tv : Typed S.R Θ (.var (ρ' 0))
          (Presentation.rename (fun i => ρ' (wk i)) (Presentation.subst σ D)) := by
        rw [← lookupVar]
        exact .var _
      have dVar : Algorithmic S.R S.roles (.terms Θ (.var (ρ' 0)) (.var (ρ' 0))
          (Presentation.rename (fun i => ρ' (wk i)) (Presentation.subst σ D))) := by
        have d := Algorithmic.rename dVar₀ w'.1
        rw [rename_rename] at d
        exact d
      have dVar' := conv dVar (CtxEq.refl Θ formedΘ) formedΘ eDom
      show ∃ U, Algorithmic S.R S.roles
          (.spines Θ (.app (Presentation.rename ρ' (Presentation.rename wk t)) (.var (ρ' 0)))
            (.app (Presentation.rename ρ' (Presentation.rename wk s)) (.var (ρ' 0))) U) ∧
        TypeLe S.R Θ U (Presentation.rename ρ' (Presentation.subst (liftSub σ) E))
      rw [rename_rename, rename_rename]
      refine ⟨_, .app dW dVar', ?_⟩
      have e := Derivable.substitutes leCod (SubstMor.single tv)
      change Below S.R Θ (inst0 (.var (ρ' 0)) B₂)
        (inst0 (.var (ρ' 0)) (Presentation.rename (liftRen (fun i => ρ' (wk i)))
          (Presentation.subst (liftSub σ) E))) at e
      rw [inst0_var_rename_liftRen_comp] at e
      exact .sub e (.refl _)
    have equal₁ : Equal S.R (.snoc Γ (Presentation.subst σ D))
        (.app (Presentation.rename wk t) (.var 0)) (.app (Presentation.rename wk s) (.var 0))
        (Presentation.subst (liftSub σ) E) := by
      have e := Derivable.appCong (Equal.weaken (extension := Presentation.subst σ D) equal')
        (.refl (.var 0))
      rwa [inst0_var_rename_liftRen_wk] at e
    have d₁ := ihE neutral.lift formedD (lt.appFresh funT) (ls.appFresh funS) equal₁ spines₁
    exact .terms red (.inr (.inl ⟨_, _, rfl⟩)) (RedTm.refl tt') (RedTm.refl ts')
      (.eta domType tt' funT ts' funS d₁)
  · -- A dependent pair type: compared by the projections.
    rcases subst_eq_sigma_or_var hC'.symm with ⟨i, rfl⟩ | ⟨D, E, rfl, rfl, rfl⟩
    · exact absurd hC'.symm ((neutral i).not_former.2.2.1 _ _)
    have ihD : LiftsAt S D := ih ⟨k, D⟩ ⟨_, redC, .sigmaDom D E⟩
    have ihE : LiftsAt S E := ih ⟨k + 1, E⟩ ⟨_, redC, .sigmaCod D E⟩
    have isNeutral : ∀ {v : Tm Head m}, Liftable S.roles v →
        Typed S.R Γ v (.sigma (Presentation.subst σ D) (Presentation.subst (liftSub σ) E)) →
          Neutral S.roles v := by
      intro v lv tv
      rcases lv with nv | ⟨k', arity, args, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
      · exact nv
      · exact absurd tv (forms.constructor_sigma formed role)
      · obtain ⟨u, e, -⟩ :=
          forms.inductive_universe formed role tv (.inr (.inr (.inl ⟨_, _, rfl⟩)))
        cases e
    have nt := isNeutral lt tt'
    have ns := isNeutral ls ts'
    -- the first projections
    have spinesFst : SpinesEverywhere S Γ (.fst t) (.fst s) (Presentation.subst σ D) := by
      intro m' Θ ρ w
      obtain ⟨U, dU, leU⟩ := spines w
      have eA := red.typeEq.rename w.1
      obtain ⟨A₂, B₂, dW, leDom, _⟩ := Algorithmic.spinesW_sigma facts roots heads
        algebra w.2 dU (leU.trans eA.toLe) ((TypeEq.isType eA w.2).2)
      exact ⟨_, .fst dW, .sub leDom (.refl _)⟩
    have dFst : Algorithmic S.R S.roles (.terms Γ (.fst t) (.fst s) (Presentation.subst σ D)) :=
      ihD neutral formed (.inl (.fst nt)) (.inl (.fst ns)) (.fstCong equal') spinesFst
    -- the second projections, at the codomain instantiated by the first projection
    have spinesSnd : SpinesEverywhere S Γ (.snd t) (.snd s)
        (inst0 (.fst t) (Presentation.subst (liftSub σ) E)) := by
      intro m' Θ ρ w
      obtain ⟨U, dU, leU⟩ := spines w
      have eA := red.typeEq.rename w.1
      obtain ⟨A₂, B₂, dW, _, leCod⟩ := Algorithmic.spinesW_sigma facts roots heads
        algebra w.2 dU (leU.trans eA.toLe) ((TypeEq.isType eA w.2).2)
      obtain ⟨tW, _⟩ := sound dW w.2
      refine ⟨_, .snd dW, ?_⟩
      rw [rename_inst0]
      exact .sub (Derivable.substitutes leCod (SubstMor.single (.fstElim tW))) (.refl _)
    have eE : inst0 (.fst t) (Presentation.subst (liftSub σ) E) =
        Presentation.subst (consSub (.fst t) σ) E := inst0_subst_liftSub _ σ E
    have dSnd := ihE (neutral.cons (.fst nt)) formed (.inl (.snd nt)) (.inl (.snd ns))
      (by rw [← eE]; exact .sndCong equal') (by rw [← eE]; exact spinesSnd)
    rw [← eE] at dSnd
    exact .terms red (.inr (.inr (.inl ⟨_, _, rfl⟩))) (RedTm.refl tt') (RedTm.refl ts')
      (.sigmaEta tt' (.inr nt) ts' (.inr ns) dFst dSnd)
  · -- An identity type: compared as spines.
    exact .terms red (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (RedTm.refl tt') (RedTm.refl ts')
      (.spine (.inl ⟨_, _, _, rfl⟩) (spineForm lt tt' fun _ e => nomatch e)
        (spineForm ls ts' fun _ e => nomatch e) tt' ts' dW)
  · -- A neutral type: compared as spines.
    exact .terms red (.inr (.inr (.inr (.inr (.inl neutralA))))) (RedTm.refl tt')
      (RedTm.refl ts') (.spine (.inr (.inl neutralA))
        (spineForm lt tt' fun u e => absurd e (neutralA.not_former.1 u))
        (spineForm ls ts' fun u e => absurd e (neutralA.not_former.1 u)) tt' ts' dW)
  · -- The type constant of an inductive type: compared as spines.
    exact .terms red (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩))))) (RedTm.refl tt')
      (RedTm.refl ts') (.spine (.inr (.inr (.inl ⟨T, ctors, role, rfl⟩)))
        (spineForm lt tt' fun _ e => nomatch e) (spineForm ls ts' fun _ e => nomatch e)
        tt' ts' dW)

/-- **Spine comparisons lift in a rule package whose types are strongly
normalizing**, given the facts about the weak-head forms of its types, when
substituting neutral terms creates no weak-head redex and liftable values have
the shapes of their types. -/
theorem SpineLift.ofNormalizing
    (normalizing : ∀ {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}, CtxFormed S.R Γ →
      IsType S.R Γ A → StrongNormalization.SN S.R A) :
    SpineLift S := by
  intro n Γ t u A formed lt lu equal spines
  obtain ⟨tt, _⟩ := Equal.typed equal formed
  have lifts : LiftsAt S A := liftsAt_of_acc facts roots heads algebra forms reflecting
    (TypeComponent.acc (normalizing formed (Typed.isType tt formed)))
  have d := lifts (NeutralSub.ids (roles := S.roles)) formed lt lu
    (by rw [subst_ids]; exact equal) (by rw [subst_ids]; exact spines)
  rwa [subst_ids] at d

end Lift

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
