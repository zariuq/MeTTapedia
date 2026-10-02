import Mettapedia.OSLF.Framework.ObserverNativeTypes
import Mettapedia.GSLT.Scope.Arrows

/-!
# The native type of a program, and how scope changes act on it

OSLF generates a type system from a language: native predicates on programs,
with step modalities.  This module reads that type system at the level of one
program `P` of a GSLT (in particular of `langGSLT lang` for a `LanguageDef`).

**The native type of a program** (`nativeTypeOf`) is its equation class, the
least native predicate it satisfies.
* `P` satisfies a native predicate exactly when its native type implies it
  (`sat_iff_nativeTypeOf_implies`): the native type is principal.
* The **native theory** of `P` (`programTheory`), the native predicates it
  satisfies, is W3's `theoryOf` for native satisfaction.  Its models are the
  programs equal to `P` modulo the equations (`models_programTheory`), and two
  programs have the same native theory exactly when they are equal modulo the
  equations (`programTheory_eq_iff`).
* The **modal theory** of `P` (`modalTheory`), the Hennessy–Milner formulas it
  satisfies, is coarser: it is determined by the native theory
  (`modalTheory_eq_of_equiv`) and, for image-finite systems, characterises
  bisimilarity (`modalTheory_eq_iff_bisimilar`).
* **Programs in context.**  Plugging into a context respects the equations
  (`plugMap`), and the context-decorated modality `⟨K⟩φ` ("plugged into `K`,
  the program can step into `φ`") is the pullback of the step-future along the
  plugging (`contextDiamond`, `contextDiamond_apply`); it composes with
  contexts (`contextDiamond_compose`).

**Scope changes.**
* **Translation** along an equation-respecting map `f` is a scope translation
  in W11's sense, with native predicates translated backward by pullback and
  programs reduced forward by `f` (`nativeTranslation`).  The direct image of
  the native type of `P` is the native type of `f P`
  (`directImage_nativeTypeOf`).  Pullback commutes with the step-future modality
  exactly when `f` is a bounded morphism of the step relations
  (`pullback_diamond_iff`).  Controls: a translation that adds a step breaks
  the commutation (`AddedStep.diamond_not_natural`), and a translation that
  identifies programs does not pull native types back to native types
  (`pullback_nativeTypeOf_iff`, `Forgetting.pullback_not_nativeTypeOf`).
* **Observing** a program through the observers of an admissible class `D`
  is such a translation (`observeMap`): the program's **behavioural native
  type**, its native type in W5's observed GSLT, is the direct image of its
  native type, its `D`-behaviour class (`observe_directImage_nativeTypeOf`).
* **Forgetting** to a coarser observer (W5's `forgetMap`) is such a
  translation: the forgotten native type of a program is the direct image of
  its finer one (`forget_directImage_nativeTypeOf`), observing then forgetting
  is observing coarsely (`forget_observe_nativeTypeOf`), and pulling back is
  strictly weaker in general (`Forgetting.pullback_not_nativeTypeOf`).
* **Restriction** to a fragment closed under equations and steps
  (`Fragment`) preserves and reflects every step-future formula
  (`Fragment.pullback_diamond`), but can gain step-past formulas
  (`Fragment.box_of_pullback_box`; control `Restriction.box_gained`): a
  program of the fragment may lose predecessors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Programs

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.ObserverNativeTypes
open Mettapedia.Logic.TheoryModel

universe u uContext uRule uAtom uLabel

/-! ## The native type of a program -/

section NativeType

variable (S : GSLT.{u})

/-- Native satisfaction: a program satisfies a native predicate. -/
def NativeSat (P : S.Term) (φ : EquationPredicate S) : Prop :=
  φ.1 P

/-- **The native type of a program**: its equation class, the least native
predicate it satisfies. -/
def nativeTypeOf (P : S.Term) : EquationPredicate S :=
  saturatePredicate S (· = P)

variable {S}

theorem nativeTypeOf_apply {P Q : S.Term} : (nativeTypeOf S P).1 Q ↔ S.Equiv Q P := by
  constructor
  · rintro ⟨_, equivalent, rfl⟩
    exact equivalent
  · intro equivalent
    exact ⟨P, equivalent, rfl⟩

theorem nativeTypeOf_self (P : S.Term) : (nativeTypeOf S P).1 P :=
  nativeTypeOf_apply.mpr (S.equations.iseqv.refl P)

/-- **The native type is principal**: a program satisfies a native predicate
exactly when every program of its native type does. -/
theorem sat_iff_nativeTypeOf_implies {P : S.Term} {φ : EquationPredicate S} :
    φ.1 P ↔ ∀ Q, (nativeTypeOf S P).1 Q → φ.1 Q :=
  ⟨fun holds _ member => (φ.2 (nativeTypeOf_apply.mp member)).mpr holds,
    fun implies => implies P (nativeTypeOf_self P)⟩

/-- The same statement in the pointwise order of native predicates (the order
that instance search finds on the subtype `EquationPredicate S`). -/
theorem nativeTypeOf_le_iff {P : S.Term} {φ : EquationPredicate S} :
    nativeTypeOf S P ≤ φ ↔ φ.1 P := by
  rw [sat_iff_nativeTypeOf_implies]
  exact ⟨fun le Q member => le Q member, fun implies Q member => implies Q member⟩

/-- The native theory of a program: the native predicates it satisfies. -/
def programTheory (S : GSLT.{u}) (P : S.Term) : Set (EquationPredicate S) :=
  theoryOf (NativeSat S) {P}

theorem mem_programTheory {P : S.Term} {φ : EquationPredicate S} :
    φ ∈ programTheory S P ↔ φ.1 P :=
  ⟨fun member => member rfl, fun holds _ equal => equal ▸ holds⟩

/-- **The models of a program's native theory are the programs equal to it
modulo the equations.** -/
theorem models_programTheory (P : S.Term) :
    models (NativeSat S) (programTheory S P) = {Q | S.Equiv Q P} := by
  ext Q
  constructor
  · intro model
    exact nativeTypeOf_apply.mp (model (mem_programTheory.mpr (nativeTypeOf_self P)))
  · intro equivalent φ member
    exact (φ.2 equivalent).mpr (mem_programTheory.mp member)

/-- **Native theories separate programs exactly up to the equations.** -/
theorem programTheory_eq_iff {P Q : S.Term} :
    programTheory S P = programTheory S Q ↔ S.Equiv P Q := by
  constructor
  · intro equal
    have member : nativeTypeOf S Q ∈ programTheory S P := by
      rw [equal]
      exact mem_programTheory.mpr (nativeTypeOf_self Q)
    exact nativeTypeOf_apply.mp (mem_programTheory.mp member)
  · intro equivalent
    ext φ
    rw [mem_programTheory, mem_programTheory]
    exact φ.2 equivalent

/-- The modal theory of a program: the Hennessy–Milner formulas it satisfies. -/
def modalTheory (M : System.{uAtom, uLabel} S) (P : S.Term) : Set (Formula M.Atom M.Label) :=
  theoryOf (fun term formula => M.sat formula term) {P}

theorem mem_modalTheory (M : System.{uAtom, uLabel} S) {P : S.Term}
    {formula : Formula M.Atom M.Label} : formula ∈ modalTheory M P ↔ M.sat formula P :=
  ⟨fun member => member rfl, fun holds _ equal => equal ▸ holds⟩

/-- A formula is in the modal theory exactly when its native predicate is in
the native theory. -/
theorem mem_modalTheory_iff_formulaPredicate (M : System.{uAtom, uLabel} S) {P : S.Term}
    {formula : Formula M.Atom M.Label} :
    formula ∈ modalTheory M P ↔
      Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaPredicate M formula ∈
        programTheory S P := by
  rw [mem_modalTheory, mem_programTheory]
  rfl

/-- The native theory determines the modal theory. -/
theorem modalTheory_eq_of_equiv (M : System.{uAtom, uLabel} S) {P Q : S.Term}
    (equivalent : S.Equiv P Q) : modalTheory M P = modalTheory M Q := by
  ext formula
  rw [mem_modalTheory, mem_modalTheory]
  exact M.sat_resp formula equivalent

/-- **For image-finite systems the modal theory characterises
bisimilarity** (Hennessy–Milner). -/
theorem modalTheory_eq_iff_bisimilar (M : System.{uAtom, uLabel} S)
    (finite : M.ImageFiniteModulo) {P Q : S.Term} :
    modalTheory M P = modalTheory M Q ↔ M.Bisimilar P Q := by
  rw [← M.logicallyEquivalent_iff_bisimilar finite P Q]
  constructor
  · intro equal formula
    rw [← mem_modalTheory, ← mem_modalTheory, equal]
  · intro equivalent
    ext formula
    rw [mem_modalTheory, mem_modalTheory]
    exact equivalent formula

end NativeType

/-! ## Programs in context -/

section Context

variable {S : GSLT.{u}} (rules : ContextualRules.{uContext, uRule} S)

/-- Plugging into a context respects the equations. -/
def plugMap (K : rules.Context) : EquationRespectingMap S S where
  toFun := rules.plug K
  map_equiv := rules.plug_resp K

/-- **The context-decorated modality** `⟨K⟩φ`: plugged into `K`, the program
can take a step into `φ`.  It is the pullback of the step-future along the
plugging. -/
def contextDiamond (K : rules.Context) (φ : EquationPredicate S) : EquationPredicate S :=
  (plugMap rules K).pullback (semanticDiamond S φ)

theorem contextDiamond_apply (K : rules.Context) (φ : EquationPredicate S) (P : S.Term) :
    (contextDiamond rules K φ).1 P ↔ ∃ Q, S.Step (rules.plug K P) Q ∧ φ.1 Q :=
  gsltDiamond_spec S φ.1 (rules.plug K P)

/-- The context-decorated modality composes with contexts. -/
theorem contextDiamond_compose (outer inner : rules.Context) (φ : EquationPredicate S)
    (P : S.Term) :
    (contextDiamond rules (rules.compose outer inner) φ).1 P ↔
      (contextDiamond rules outer φ).1 (rules.plug inner P) :=
  (semanticDiamond S φ).2 (rules.plug_compose outer inner P)

/-- A least-enabler transition is a context-decorated step. -/
theorem contextDiamond_of_act {K : rules.Context} {P Q : S.Term} (act : rules.Act K P Q)
    {φ : EquationPredicate S} (holds : φ.1 Q) : (contextDiamond rules K φ).1 P :=
  (contextDiamond_apply rules K φ P).mpr ⟨Q, rules.act_step act, holds⟩

end Context

/-! ## Translation -/

section Translation

variable {S S' : GSLT.{u}} (f : EquationRespectingMap S S')

theorem pullback_apply (φ : EquationPredicate S') (P : S.Term) :
    (f.pullback φ).1 P ↔ φ.1 (f.toFun P) :=
  Iff.rfl

theorem directImage_apply (ψ : EquationPredicate S) (Q : S'.Term) :
    (f.directImage ψ).1 Q ↔ ∃ P, S'.Equiv (f.toFun P) Q ∧ ψ.1 P := by
  constructor
  · rintro ⟨c, equal, holds⟩
    induction c using Quotient.inductionOn with
    | _ P => exact ⟨P, Quotient.exact equal, holds⟩
  · rintro ⟨P, equivalent, holds⟩
    exact ⟨Quotient.mk S.equations P, Quotient.sound equivalent, holds⟩

/-- **The direct image of a program's native type is the native type of its
translation.** -/
theorem directImage_nativeTypeOf (P : S.Term) (Q : S'.Term) :
    (f.directImage (nativeTypeOf S P)).1 Q ↔ (nativeTypeOf S' (f.toFun P)).1 Q := by
  rw [directImage_apply, nativeTypeOf_apply]
  constructor
  · rintro ⟨P', equivalent, member⟩
    exact S'.equations.iseqv.trans (S'.equations.iseqv.symm equivalent)
      (f.map_equiv (nativeTypeOf_apply.mp member))
  · intro equivalent
    exact ⟨P, S'.equations.iseqv.symm equivalent, nativeTypeOf_self P⟩

/-- **A translation of programs is a scope translation**: native predicates
are translated backward by pullback, programs are reduced forward by `f`. -/
def nativeTranslation : Mettapedia.GSLT.Scope.Translation (NativeSat S') (NativeSat S) where
  translate := f.pullback
  reduct := f.toFun
  sat_iff _ _ := Iff.rfl

/-- The native theory of a translated program is the pullback-preimage of the
native theory of the source. -/
theorem programTheory_translate (P : S.Term) (φ : EquationPredicate S') :
    φ ∈ programTheory S' (f.toFun P) ↔ f.pullback φ ∈ programTheory S P := by
  rw [mem_programTheory, mem_programTheory]
  rfl

/-- The pullback of the native type of a translated program collects every
program with an equal translation. -/
theorem pullback_nativeTypeOf_apply (P Q : S.Term) :
    (f.pullback (nativeTypeOf S' (f.toFun P))).1 Q ↔ S'.Equiv (f.toFun Q) (f.toFun P) :=
  nativeTypeOf_apply

/-- **Pulling a native type back gives a native type exactly when the
translation reflects the equations at that program.** -/
theorem pullback_nativeTypeOf_iff (P : S.Term) :
    (∀ Q, (f.pullback (nativeTypeOf S' (f.toFun P))).1 Q ↔ (nativeTypeOf S P).1 Q) ↔
      ∀ Q, S'.Equiv (f.toFun Q) (f.toFun P) → S.Equiv Q P := by
  constructor
  · intro same Q equivalent
    exact nativeTypeOf_apply.mp ((same Q).mp (nativeTypeOf_apply.mpr equivalent))
  · intro reflects Q
    rw [pullback_nativeTypeOf_apply, nativeTypeOf_apply]
    exact ⟨reflects Q, f.map_equiv⟩

/-- `f` preserves steps. -/
def Forth : Prop :=
  ∀ ⦃P Q : S.Term⦄, S.Step P Q → S'.Step (f.toFun P) (f.toFun Q)

/-- `f` reflects steps, up to the equations of the target. -/
def Back : Prop :=
  ∀ ⦃P : S.Term⦄ ⦃Q' : S'.Term⦄, S'.Step (f.toFun P) Q' →
    ∃ Q, S.Step P Q ∧ S'.Equiv (f.toFun Q) Q'

/-- **Pullback commutes with the step-future modality exactly when the
translation is a bounded morphism of the step relations.** -/
theorem pullback_diamond_iff :
    (∀ (φ : EquationPredicate S') (P : S.Term),
        (f.pullback (semanticDiamond S' φ)).1 P ↔ (semanticDiamond S (f.pullback φ)).1 P) ↔
      Forth f ∧ Back f := by
  constructor
  · intro commutes
    constructor
    · intro P Q step
      have holds : (semanticDiamond S (f.pullback (nativeTypeOf S' (f.toFun Q)))).1 P :=
        (gsltDiamond_spec S _ P).mpr ⟨Q, step, nativeTypeOf_self _⟩
      obtain ⟨X, step', member⟩ :=
        (gsltDiamond_spec S' _ (f.toFun P)).mp ((commutes _ P).mpr holds)
      exact S'.rewrites_resp_right step' (nativeTypeOf_apply.mp member)
    · intro P Q' step
      have holds : (f.pullback (semanticDiamond S' (nativeTypeOf S' Q'))).1 P :=
        (gsltDiamond_spec S' _ (f.toFun P)).mpr ⟨Q', step, nativeTypeOf_self _⟩
      obtain ⟨Q, step', member⟩ := (gsltDiamond_spec S _ P).mp ((commutes _ P).mp holds)
      exact ⟨Q, step', nativeTypeOf_apply.mp member⟩
  · rintro ⟨forth, back⟩ φ P
    change gsltDiamond S' φ.1 (f.toFun P) ↔ gsltDiamond S (f.pullback φ).1 P
    rw [gsltDiamond_spec, gsltDiamond_spec]
    constructor
    · rintro ⟨X, step, holds⟩
      obtain ⟨Q, step', equivalent⟩ := back step
      exact ⟨Q, step', (φ.2 equivalent).mpr holds⟩
    · rintro ⟨Q, step, holds⟩
      exact ⟨f.toFun Q, forth step, holds⟩

end Translation

/-! ### Control: a translation that adds a step -/

namespace AddedStep

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Two inert programs. -/
abbrev inert : GSLT.{0} :=
  equalityGSLT Bool fun _ _ => False

/-- The same programs, where `true` steps to `false`. -/
abbrev stepping : GSLT.{0} :=
  equalityGSLT Bool fun source target => source = true ∧ target = false

/-- The identity translation from the inert programs into the stepping
ones. -/
def inclusion : EquationRespectingMap inert stepping where
  toFun := id
  map_equiv := id

/-- The translation preserves steps, vacuously. -/
theorem forth : Forth inclusion :=
  fun _ _ step => step.elim

/-- **Negative control**: it does not reflect steps. -/
theorem not_back : ¬ Back inclusion := by
  intro back
  obtain ⟨_, step, _⟩ := back (P := true) (Q' := false) ⟨rfl, rfl⟩
  exact step

/-- **Negative control**: the pullback of "can step" holds at `true`, while
"can step" of the pullback does not. -/
theorem diamond_not_natural :
    (inclusion.pullback (semanticDiamond stepping (nativeTypeOf stepping false))).1 true ∧
      ¬ (semanticDiamond inert (inclusion.pullback (nativeTypeOf stepping false))).1 true := by
  refine ⟨(gsltDiamond_spec stepping _ true).mpr ⟨false, ⟨rfl, rfl⟩, nativeTypeOf_self _⟩, ?_⟩
  intro holds
  obtain ⟨_, step, _⟩ := (gsltDiamond_spec inert _ true).mp holds
  exact step

/-- Positive control: the identity translation of the stepping programs into
themselves is a bounded morphism. -/
theorem identity_bounded :
    Forth (⟨id, id⟩ : EquationRespectingMap stepping stepping) ∧
      Back (⟨id, id⟩ : EquationRespectingMap stepping stepping) :=
  ⟨fun _ _ step => step, fun _ Q' step => ⟨Q', step, rfl⟩⟩

end AddedStep

/-! ## Forgetting -/

section Forgetting

variable {S : GSLT.{u}} {rules : ContextualRules.{uContext, uRule} S}
variable (observations : ContextualRules.Observations.{uAtom} S)

/-- **Forgetting a program's native type is its direct image**: the
`A`-native type of `P` is the direct image of its `B`-native type along W5's
forgetting map. -/
theorem forget_directImage_nativeTypeOf {A B : AdmissibleClass rules} (le : A ≤ B)
    (P Q : S.Term) :
    ((forgetMap observations le).directImage (nativeTypeOf (observedGSLT observations B) P)).1 Q ↔
      (nativeTypeOf (observedGSLT observations A) P).1 Q :=
  directImage_nativeTypeOf (forgetMap observations le) P Q

/-- Observing through the observers of `D` respects the equations. -/
def observeMap (D : AdmissibleClass rules) :
    EquationRespectingMap S (observedGSLT observations D) where
  toFun := id
  map_equiv := fun equivalent => D.relEquiv_of_equiv observations equivalent

/-- **The behavioural native type of a program**: the direct image of its
native type along observation is its `D`-behaviour class. -/
theorem observe_directImage_nativeTypeOf (D : AdmissibleClass rules) (P Q : S.Term) :
    ((observeMap observations D).directImage (nativeTypeOf S P)).1 Q ↔
      D.RelEquiv observations Q P :=
  (directImage_nativeTypeOf (observeMap observations D) P Q).trans nativeTypeOf_apply

/-- Observing finely and then forgetting is observing coarsely. -/
theorem forget_observe_nativeTypeOf {A B : AdmissibleClass rules} (le : A ≤ B) (P Q : S.Term) :
    ((forgetMap observations le).directImage
        ((observeMap observations B).directImage (nativeTypeOf S P))).1 Q ↔
      ((observeMap observations A).directImage (nativeTypeOf S P)).1 Q := by
  refine (directImage_apply (forgetMap observations le) _ Q).trans ?_
  refine Iff.trans ?_ (observe_directImage_nativeTypeOf observations A P Q).symm
  constructor
  · rintro ⟨R, related, member⟩
    have fine : B.RelEquiv observations R P := (observe_directImage_nativeTypeOf observations B P R).mp member
    exact A.relEquiv_trans observations (A.relEquiv_symm observations related)
      (AdmissibleClass.relEquiv_antitone observations le fine)
  · intro related
    exact ⟨P, A.relEquiv_symm observations related,
      (observe_directImage_nativeTypeOf observations B P P).mpr (B.relEquiv_refl observations P)⟩

/-- Pulling the coarse native type back gives the fine native type exactly when
the coarse observers already make the fine distinctions at `P`. -/
theorem forget_pullback_nativeTypeOf_iff {A B : AdmissibleClass rules} (le : A ≤ B)
    (P : S.Term) :
    (∀ Q, ((forgetMap observations le).pullback
        (nativeTypeOf (observedGSLT observations A) P)).1 Q ↔
          (nativeTypeOf (observedGSLT observations B) P).1 Q) ↔
      ∀ Q, A.RelEquiv observations Q P → B.RelEquiv observations Q P :=
  pullback_nativeTypeOf_iff (forgetMap observations le) P

end Forgetting

namespace Forgetting

open Mettapedia.GSLT.AdmissibleContextCongruence.ObserverPresheafControls
open Mettapedia.GSLT.AdmissibleContextCongruence.ObserverPresheafControls.InertFunctions
open Mettapedia.GSLT.AdmissibleContextCongruence.ObserverPresheafControls.Incompatible

/-- **Negative control**: in W5's incompatible-observers fixture, forgetting
from `B` to `A` merges `p3` into the class of `p1`, so the pullback of the
coarse native type of `p1` is strictly weaker than its fine native type. -/
theorem pullback_not_nativeTypeOf :
    ((forgetMap (hits Pt .yes) A_le_B).pullback
        (nativeTypeOf (observedGSLT (hits Pt .yes) A) Pt.p1)).1 Pt.p3 ∧
      ¬ (nativeTypeOf (observedGSLT (hits Pt .yes) B) Pt.p1).1 Pt.p3 := by
  refine ⟨nativeTypeOf_apply.mpr
    (show A.RelEquiv (hits Pt .yes) Pt.p3 Pt.p1 from (A_relEquiv_iff Pt.p3 Pt.p1).mpr (by decide)),
    fun member => ?_⟩
  have related := (B_relEquiv_iff _ _).mp (nativeTypeOf_apply.mp member)
  exact absurd related.2 (by decide)

/-- Positive control: forgetting along the identity loses nothing. -/
theorem pullback_refl_nativeTypeOf (P Q : Pt) :
    ((forgetMap (hits Pt .yes) (le_refl A)).pullback
        (nativeTypeOf (observedGSLT (hits Pt .yes) A) P)).1 Q ↔
      (nativeTypeOf (observedGSLT (hits Pt .yes) A) P).1 Q :=
  Iff.rfl

end Forgetting

/-! ## Restriction to a fragment -/

/-- A **fragment** of a GSLT: a class of programs closed under the equations
and under steps. -/
structure Fragment (S : GSLT.{u}) where
  /-- Membership in the fragment. -/
  mem : S.Term → Prop
  /-- Closure under the equations. -/
  mem_equiv : ∀ ⦃P Q : S.Term⦄, S.Equiv P Q → mem P → mem Q
  /-- Closure under steps. -/
  mem_step : ∀ ⦃P Q : S.Term⦄, S.Step P Q → mem P → mem Q

namespace Fragment

variable {S : GSLT.{u}} (F : Fragment S)

/-- The GSLT of the fragment's programs. -/
def gslt : GSLT.{u} where
  Term := {P : S.Term // F.mem P}
  equations :=
    { r := fun P Q => S.Equiv P.1 Q.1
      iseqv := ⟨fun P => S.equations.iseqv.refl P.1, fun h => S.equations.iseqv.symm h,
        fun h h' => S.equations.iseqv.trans h h'⟩ }
  rewrites P Q := S.Step P.1 Q.1
  rewrites_resp_left := by
    rintro P P' Q equivalent step
    obtain ⟨Q', step', equivalent'⟩ := S.rewrites_resp_left equivalent step
    exact ⟨⟨Q', F.mem_step step' P'.2⟩, step', equivalent'⟩
  rewrites_resp_right := fun step equivalent => S.rewrites_resp_right step equivalent

/-- The inclusion of the fragment. -/
def incl : EquationRespectingMap F.gslt S where
  toFun := Subtype.val
  map_equiv := id

/-- The inclusion of a fragment is a bounded morphism. -/
theorem incl_bounded : Forth F.incl ∧ Back F.incl :=
  ⟨fun _ _ step => step, fun P Q' step =>
    ⟨⟨Q', F.mem_step step P.2⟩, step, S.equations.iseqv.refl Q'⟩⟩

/-- **Restriction preserves and reflects every step-future formula.** -/
theorem pullback_diamond (φ : EquationPredicate S) (P : F.gslt.Term) :
    (F.incl.pullback (semanticDiamond S φ)).1 P ↔
      (semanticDiamond F.gslt (F.incl.pullback φ)).1 P :=
  (pullback_diamond_iff F.incl).mpr F.incl_bounded φ P

/-- **Restriction can only gain step-past formulas**: a program of the
fragment has no more predecessors in the fragment than in the whole. -/
theorem box_of_pullback_box (φ : EquationPredicate S) (P : F.gslt.Term)
    (holds : (F.incl.pullback (semanticBox S φ)).1 P) :
    (semanticBox F.gslt (F.incl.pullback φ)).1 P := by
  change gsltBox S φ.1 P.1 at holds
  change gsltBox F.gslt (F.incl.pullback φ).1 P
  rw [gsltBox_spec] at holds
  rw [gsltBox_spec]
  intro Q step
  exact holds Q.1 step

end Fragment

namespace Restriction

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- `false` steps to `true`. -/
abbrev programs : GSLT.{0} :=
  equalityGSLT Bool fun source target => source = false ∧ target = true

/-- The fragment `{true}`: closed under steps because `true` has none. -/
def trueFragment : Fragment programs where
  mem P := P = true
  mem_equiv _ _ equal member := equal ▸ member
  mem_step _ _ step _ := step.2

/-- "Has no predecessor", as a step-past formula. -/
def noPredecessor (S : GSLT.{0}) : EquationPredicate S :=
  semanticBox S ⟨fun _ => False, fun _ _ _ => Iff.rfl⟩

/-- **Negative control: restriction gains a step-past formula.**  In the
fragment, `true` has no predecessor; in the whole, `false` precedes it. -/
theorem box_gained :
    (noPredecessor trueFragment.gslt).1 ⟨true, rfl⟩ ∧ ¬ (noPredecessor programs).1 true := by
  refine ⟨(gsltBox_spec _ _ _).mpr fun Q step => ?_, fun holds => ?_⟩
  · have isFalse : Q.1 = false := step.1
    have isTrue : Q.1 = true := Q.2
    rw [isFalse] at isTrue
    exact Bool.false_ne_true isTrue
  · exact (gsltBox_spec _ _ _).mp holds false ⟨rfl, rfl⟩

end Restriction

end Mettapedia.OSLF.Programs
