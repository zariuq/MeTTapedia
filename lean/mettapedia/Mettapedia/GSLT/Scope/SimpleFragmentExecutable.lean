import Mettapedia.GSLT.Scope.SimpleFragment
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSteps

/-!
# One reduction relation for normalization and bisimulation on the simple fragment

The candidate has two one-step reduction relations on raw terms:

* the sealed tower's steps (`TowerStep`): β for functions and pairs, and the
  equalities of universe heads read as steps, with no declared computation;
* the executable package's directed reduction (`ExecStep`, the relation
  `Reduces objectRules` of its strong normalization theorem): β for
  functions and pairs, and the root computations of the package (the
  recursor, addition, the iterated power set, identity elimination, the
  definitions, the iterator and the decoding of proposition codes), with no
  head steps.

**Pure λ-terms.**  Both relations are instances of `StepCore root headEq`.  A
root computation whose steps start at applications of constants never fires
at a pure λ-term, a raw term built from variables, abstraction and
application only (`RootFree`).  Every step out of a pure λ-term is then a
β-step or a congruence step into a pure part, whatever the package and the
head equality (`StepCore.transfer`), and pure λ-terms are closed under such
steps (`PureLambda.of_step`).  So on pure λ-terms the two relations coincide
(`towerStep_iff_execStep`), and the identity is a bisimulation between them
(`pure_isBisimulation`).  Erasures of simple terms are pure
(`eraseTerm_pure`), so the same holds on the slice (`slice_isBisimulation`).

**Erasure is a bounded morphism into the executable relation**
(`erase_isBoundedMorphism_exec`): it preserves every β-step and reflects
every executable step out of an erasure.  Hence a covered translation
(`eraseExecCovered`), invariance of every Hennessy–Milner formula
(`sat_erase_iff_exec`), and bisimilarity of terms with one erasure
(`bisimilar_of_erase_eq_exec`).

**Strong normalization is a bisimulation invariant**
(`acc_iff_of_isBoundedMorphism`).  So the package's normalization theorem
gives strong normalization of β-reduction on intrinsic terms
(`betaStep_sn`) and of the sealed tower's steps on the slice
(`erase_towerSN`), and the two relations have the same strongly normalizing
pure λ-terms (`pure_towerSN_iff_execSN`).  On the slice one relation carries
both results (`slice_one_relation`): every slice term is strongly
normalizing for the executable relation and for the tower, the two relations
agree there, and every reduct stays in the slice; the executable relation
restricted to the slice is well founded (`slice_wellFounded`).  The
self-application `Ω` is pure and reduces to itself in both relations
(`omega_not_execSN`, `omega_not_towerSN`), so it lies outside the slice
(`omega_not_mem_sliceTerms`).

**Off the slice the relations differ in both directions.**
* A universe head steps to itself in the tower (`towerStep_head_loop`) and
  takes no executable step (`execStep_head_inv`), so the head is not
  bisimilar to itself across the two systems (`not_bisimilar_head`), is
  strongly normalizing only for the executable relation (`head_execSN`,
  `head_not_towerSN`), and every erased simple type loops in the tower
  (`eraseTypeAt_not_towerSN`), although the package normalizes it.
* Identity elimination at reflexivity is an executable step
  (`execStep_jRedex`) at a term the tower cannot reduce
  (`jRedex_towerNormal`); applied to `ω = λx. x x` with method `ω`, it is
  normal for the tower (`jOmega_towerSN`) and reduces to `Ω` in the
  executable relation (`jOmega_not_execSN`).
* So on all raw terms the identity is a simulation in neither direction
  (`not_preservesEdges_tower_exec`, `not_preservesEdges_exec_tower`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.SimpleFragmentExecutable

open Set
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.GSLT.Scope.SimpleFragment

/-! ## Pure λ-terms -/

section Pure

open Presentation

variable {Head : Type}

/-- **Pure λ-terms**: raw terms built from variables, abstraction and
application only. -/
inductive PureLambda : {n : Nat} → Tm Head n → Prop
  | var {n : Nat} (i : Fin n) : PureLambda (.var i)
  | lam {n : Nat} {body : Tm Head (n + 1)} : PureLambda body → PureLambda (.lam body)
  | app {n : Nat} {f a : Tm Head n} : PureLambda f → PureLambda a → PureLambda (.app f a)

theorem PureLambda.rename {n m : Nat} {t : Tm Head n} (pure : PureLambda t) (ρ : Ren n m) :
    PureLambda (Presentation.rename ρ t) := by
  induction pure generalizing m with
  | var i => exact .var (ρ i)
  | lam _ ih => exact .lam (ih (liftRen ρ))
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)

theorem PureLambda.subst {n m : Nat} {t : Tm Head n} (pure : PureLambda t) {σ : Sub Head n m}
    (pureσ : ∀ i, PureLambda (σ i)) : PureLambda (Presentation.subst σ t) := by
  induction pure generalizing m with
  | var i => exact pureσ i
  | lam _ ih =>
      refine .lam (ih fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .var 0
      · exact (pureσ j).rename wk
  | app _ _ ihf iha => exact .app (ihf pureσ) (iha pureσ)

theorem PureLambda.inst0 {n : Nat} {body : Tm Head (n + 1)} {a : Tm Head n}
    (pureBody : PureLambda body) (pureA : PureLambda a) :
    PureLambda (Presentation.inst0 a body) :=
  pureBody.subst fun i => Fin.cases pureA (fun j => .var j) i

/-- A root computation that never fires at a pure λ-term. -/
def RootFree (root : RootComputation Head) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃t u : Tm Head n⦄, root.step t u → ¬ PureLambda t

/-- The empty root computation, that of the sealed tower, fires nowhere. -/
theorem rootFree_empty : RootFree (RootComputation.empty : RootComputation Head) :=
  fun _ _ _ step => step.elim

/-- An application spine headed by a term that is not pure is not pure. -/
theorem not_pure_foldl {n : Nat} :
    ∀ (args : List (Tm Head n)) {f : Tm Head n}, ¬ PureLambda f →
      ¬ PureLambda (args.foldl Tm.app f)
  | [], _, notPure => notPure
  | _ :: rest, _, notPure =>
      not_pure_foldl rest fun pure => by
        cases pure with
        | app pureF _ => exact notPure pureF

/-- An application spine headed by a constant is not a pure λ-term. -/
theorem not_pure_appSpine_const {n : Nat} (c : DeclName) (args : List (Tm Head n)) :
    ¬ PureLambda (TypedEquality.Normalization.appSpine (.const c) args) :=
  not_pure_foldl args fun pure => by cases pure

/-- A package whose root steps start at applications of constants never fires
at a pure λ-term. -/
theorem RootFree.of_spineHeaded {R : Rules Head}
    (spine : TypedEquality.StrongNormalization.SpineHeaded R) : RootFree R.computation := by
  intro n t u step pure
  obtain ⟨c, args, rfl⟩ := spine step
  exact not_pure_appSpine_const c args pure

/-- **Steps out of pure λ-terms do not depend on the package**: a step of one
package and head equality out of a pure λ-term is a step of every other. -/
theorem StepCore.transfer {root root' : RootComputation Head}
    {headEq headEq' : Head → Head → Prop} (free : RootFree root) {n : Nat}
    {t u : Tm Head n} (step : StepCore root headEq t u) (pure : PureLambda t) :
    StepCore root' headEq' t u := by
  induction step with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst => cases pure
  | betaSigmaSnd => cases pure
  | head => cases pure
  | root rootStep => exact absurd pure (free rootStep)
  | congPiDom => cases pure
  | congPiCod => cases pure
  | congSigmaDom => cases pure
  | congSigmaCod => cases pure
  | congIdTy => cases pure
  | congIdLeft => cases pure
  | congIdRight => cases pure
  | congLam _ ih =>
      cases pure with
      | lam pureBody => exact .congLam (ih pureBody)
  | congAppFun _ ih =>
      cases pure with
      | app pureF _ => exact .congAppFun (ih pureF)
  | congAppArg _ ih =>
      cases pure with
      | app _ pureA => exact .congAppArg (ih pureA)
  | congPairFst => cases pure
  | congPairSnd => cases pure
  | congFst => cases pure
  | congSnd => cases pure
  | congRefl => cases pure

/-- **Pure λ-terms are closed under reduction**, in every package that does
not fire at them. -/
theorem PureLambda.of_step {root : RootComputation Head} {headEq : Head → Head → Prop}
    (free : RootFree root) {n : Nat} {t u : Tm Head n} (step : StepCore root headEq t u)
    (pure : PureLambda t) : PureLambda u := by
  induction step with
  | betaPi body a =>
      cases pure with
      | app pureF pureA =>
          cases pureF with
          | lam pureBody => exact pureBody.inst0 pureA
  | betaSigmaFst => cases pure
  | betaSigmaSnd => cases pure
  | head => cases pure
  | root rootStep => exact absurd pure (free rootStep)
  | congPiDom => cases pure
  | congPiCod => cases pure
  | congSigmaDom => cases pure
  | congSigmaCod => cases pure
  | congIdTy => cases pure
  | congIdLeft => cases pure
  | congIdRight => cases pure
  | congLam _ ih =>
      cases pure with
      | lam pureBody => exact .lam (ih pureBody)
  | congAppFun _ ih =>
      cases pure with
      | app pureF pureA => exact .app (ih pureF) pureA
  | congAppArg _ ih =>
      cases pure with
      | app pureF pureA => exact .app pureF (ih pureA)
  | congPairFst => cases pure
  | congPairSnd => cases pure
  | congFst => cases pure
  | congSnd => cases pure
  | congRefl => cases pure

/-! ### Terms without redexes -/

/-- A raw term with no β-redex, no pair, no projection and no universe head:
variables, constants, abstraction, application of a non-abstraction, and
reflexivity. -/
inductive RedexFree : {n : Nat} → Tm Head n → Prop
  | var {n : Nat} (i : Fin n) : RedexFree (.var i)
  | const {n : Nat} (c : DeclName) : RedexFree (.const c : Tm Head n)
  | lam {n : Nat} {body : Tm Head (n + 1)} : RedexFree body → RedexFree (.lam body)
  | app {n : Nat} {f a : Tm Head n} : RedexFree f → (∀ body, f ≠ .lam body) → RedexFree a →
      RedexFree (.app f a)
  | refl {n : Nat} {a : Tm Head n} : RedexFree a → RedexFree (.refl a)

/-- **A redex-free term takes no step** in a presentation without root
computation, whatever its head equality. -/
theorem RedexFree.no_step {root : RootComputation Head} {headEq : Head → Head → Prop}
    (noRoot : ∀ {n : Nat} {t u : Tm Head n}, ¬ root.step t u) {n : Nat} {t u : Tm Head n}
    (free : RedexFree t) : ¬ StepCore root headEq t u := by
  intro step
  induction step with
  | betaPi body a =>
      cases free with
      | app _ notLam _ => exact notLam body rfl
  | betaSigmaFst => cases free
  | betaSigmaSnd => cases free
  | head => cases free
  | root rootStep => exact noRoot rootStep
  | congPiDom => cases free
  | congPiCod => cases free
  | congSigmaDom => cases free
  | congSigmaCod => cases free
  | congIdTy => cases free
  | congIdLeft => cases free
  | congIdRight => cases free
  | congLam _ ih =>
      cases free with
      | lam freeBody => exact ih freeBody
  | congAppFun _ ih =>
      cases free with
      | app freeF _ _ => exact ih freeF
  | congAppArg _ ih =>
      cases free with
      | app _ _ freeA => exact ih freeA
  | congPairFst => cases free
  | congPairSnd => cases free
  | congFst => cases free
  | congSnd => cases free
  | congRefl _ ih =>
      cases free with
      | refl freeA => exact ih freeA

end Pure

/-! ## The two raw relations -/

open Presentation.TypedEquality.StrongNormalization (SN)
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel

/-- The executable package's one-step reduction on raw terms with `n` free
variables: the relation of its strong normalization theorem. -/
abbrev ExecStep (n : ℕ) : Presentation.Tower.Tm n → Presentation.Tower.Tm n → Prop :=
  Presentation.TypedEquality.StrongNormalization.Reduces CodeModel.objectRules

/-- The executable package on raw terms with `n` free variables. -/
abbrev execSystem (n : ℕ) : GSLT :=
  transitionSystem (ExecStep n)

/-- The sealed tower does not fire at pure λ-terms. -/
theorem towerRootFree : RootFree Presentation.Tower.rules.computation :=
  rootFree_empty

/-- The executable package does not fire at pure λ-terms. -/
theorem objectRootFree : RootFree CodeModel.objectRules.computation :=
  RootFree.of_spineHeaded
    (Presentation.TypedEquality.StrongNormalization.RootShape.spineHeaded CodeModel.objectShape)

/-- The executable package without its proposition codes does not fire at pure
λ-terms either. -/
theorem rulesRootFree : RootFree rules.computation :=
  RootFree.of_spineHeaded
    (Presentation.TypedEquality.StrongNormalization.RootShape.spineHeaded shape)

/-- **The two relations coincide on pure λ-terms.** -/
theorem towerStep_iff_execStep {n : ℕ} {t u : Presentation.Tower.Tm n} (pure : PureLambda t) :
    TowerStep n t u ↔ ExecStep n t u :=
  ⟨fun step => StepCore.transfer towerRootFree step pure,
    fun step => StepCore.transfer objectRootFree step pure⟩

/-- **The identity on pure λ-terms is a bisimulation** between the sealed
tower and the executable package. -/
theorem pure_isBisimulation (n : ℕ) :
    IsBisimulation (TowerStep n) (ExecStep n) fun t u => t = u ∧ PureLambda t := by
  rintro t _ ⟨rfl, pure⟩
  refine ⟨fun t' step => ⟨t', (towerStep_iff_execStep pure).mp step, rfl,
      PureLambda.of_step towerRootFree step pure⟩,
    fun t' step => ⟨t', (towerStep_iff_execStep pure).mpr step, rfl,
      PureLambda.of_step objectRootFree step pure⟩⟩

/-! ## Erasure into the executable relation -/

section Erasure

variable {Γ : List Ty} {A : Ty}

/-- **Erasures are pure λ-terms.** -/
theorem eraseTerm_pure : ∀ {Γ : List Ty} {A : Ty} (t : Term Γ A),
    PureLambda (TowerDTT.eraseTerm t)
  | _, _, .var _ => .var _
  | _, _, .lam body => .lam (eraseTerm_pure body)
  | _, _, .app f a => .app (eraseTerm_pure f) (eraseTerm_pure a)

/-- **Erasure is a bounded morphism into every presentation that does not fire
at pure λ-terms**, whatever its head equality. -/
theorem erase_isBoundedMorphism_of_rootFree
    {root : Presentation.RootComputation Presentation.Tower.Head}
    {headEq : Presentation.Tower.Head → Presentation.Tower.Head → Prop} (free : RootFree root)
    (Γ : List Ty) (A : Ty) :
    IsBoundedMorphism (@BetaStep Γ A)
      (Presentation.StepCore root headEq : Presentation.Tower.Tm Γ.length → _ → Prop)
      TowerDTT.eraseTerm :=
  ⟨fun _ _ reduces => StepCore.transfer towerRootFree (BetaStep.erase reduces) (eraseTerm_pure _),
    fun t _ step => erase_liftStep t (StepCore.transfer free step (eraseTerm_pure t))⟩

/-- **Erasure is a bounded morphism into the executable package**: it
preserves every β-step and reflects every executable step out of an
erasure. -/
theorem erase_isBoundedMorphism_exec (Γ : List Ty) (A : Ty) :
    IsBoundedMorphism (@BetaStep Γ A) (ExecStep Γ.length) TowerDTT.eraseTerm :=
  erase_isBoundedMorphism_of_rootFree objectRootFree Γ A

/-- The GSLT morphism into the executable package. -/
def eraseExecTranslation (Γ : List Ty) (A : Ty) :
    OperationalTranslation (simpleSystem Γ A) (execSystem Γ.length) :=
  operationalOfPreserves (erase_isBoundedMorphism_exec Γ A).map

/-- **Erasure is a covered translation into the executable package.** -/
def eraseExecCovered (Γ : List Ty) (A : Ty) :
    CoveredTranslation (simpleSystem Γ A) (execSystem Γ.length) :=
  coveredOfBoundedMorphism (erase_isBoundedMorphism_exec Γ A)

@[simp] theorem eraseExecCovered_mapTerm (Γ : List Ty) (A : Ty) :
    (eraseExecCovered Γ A).mapTerm = TowerDTT.eraseTerm :=
  rfl

/-- **Every Hennessy–Milner formula has the same truth at a simple term and at
its erasure in the executable package.** -/
theorem sat_erase_iff_exec (formula : Mettapedia.GSLT.HennessyMilner.Formula PEmpty Unit)
    (t : Term Γ A) :
    (hmSystem (@BetaStep Γ A)).sat formula t ↔
      (hmSystem (ExecStep Γ.length)).sat formula (TowerDTT.eraseTerm t) :=
  sat_iff_of_isBoundedMorphism (erase_isBoundedMorphism_exec Γ A) formula t

/-- A simple term is bisimilar to its erasure in the executable package. -/
theorem bisimilar_erase_exec (t : Term Γ A) :
    Bisimilar (@BetaStep Γ A) (ExecStep Γ.length) t (TowerDTT.eraseTerm t) :=
  (erase_isBoundedMorphism_exec Γ A).bisimilar t

/-- **Terms with one erasure are bisimilar**, read through the executable
package. -/
theorem bisimilar_of_erase_eq_exec {left right : Term Γ A}
    (same : TowerDTT.eraseTerm left = TowerDTT.eraseTerm right) :
    Bisimilar (@BetaStep Γ A) (@BetaStep Γ A) left right :=
  (erase_isBoundedMorphism_exec Γ A).bisimilar_of_eq (erase_isBoundedMorphism_exec Γ A) same

/-- The two discarded identities are distinct, and bisimilar through the
executable package. -/
theorem discardIdentities_bisimilar_exec :
    ErasureBoundary.discardAtomicIdentity ≠ ErasureBoundary.discardFunctionIdentity ∧
      Bisimilar (@BetaStep [] (.arr .atom .atom)) (@BetaStep [] (.arr .atom .atom))
        ErasureBoundary.discardAtomicIdentity ErasureBoundary.discardFunctionIdentity :=
  ⟨ErasureBoundary.discardIdentities_ne,
    bisimilar_of_erase_eq_exec ErasureBoundary.erase_discardIdentities_eq⟩

/-- An erasure is bisimilar to itself across the tower and the executable
package. -/
theorem erase_bisimilar_tower_exec (t : Term Γ A) :
    Bisimilar (TowerStep Γ.length) (ExecStep Γ.length) (TowerDTT.eraseTerm t)
      (TowerDTT.eraseTerm t) :=
  (pure_isBisimulation Γ.length).bisimilar ⟨rfl, eraseTerm_pure t⟩

end Erasure

/-! ## The slice -/

section Slice

variable {Γ : List Ty}

theorem sliceTerms_pure {t : Presentation.Tower.Tm Γ.length} (member : t ∈ sliceTerms Γ) :
    PureLambda t := by
  obtain ⟨_, s, rfl⟩ := member
  exact eraseTerm_pure s

/-- **The slice is closed under the executable relation.** -/
theorem sliceTerms_execStep {t u : Presentation.Tower.Tm Γ.length} (member : t ∈ sliceTerms Γ)
    (step : ExecStep Γ.length t u) : u ∈ sliceTerms Γ := by
  obtain ⟨A, s, rfl⟩ := member
  obtain ⟨s', _, rfl⟩ := (erase_isBoundedMorphism_exec Γ A).lift step
  exact ⟨A, s', rfl⟩

/-- **On the slice the two relations coincide.** -/
theorem slice_towerStep_iff_execStep {t u : Presentation.Tower.Tm Γ.length}
    (member : t ∈ sliceTerms Γ) : TowerStep Γ.length t u ↔ ExecStep Γ.length t u :=
  towerStep_iff_execStep (sliceTerms_pure member)

/-- **The identity on the slice is a bisimulation** between the sealed tower and
the executable package. -/
theorem slice_isBisimulation (Γ : List Ty) :
    IsBisimulation (TowerStep Γ.length) (ExecStep Γ.length)
      fun t u => t = u ∧ t ∈ sliceTerms Γ := by
  rintro t _ ⟨rfl, member⟩
  refine ⟨fun t' step => ⟨t', (slice_towerStep_iff_execStep member).mp step, rfl,
      sliceTerms_execStep member ((slice_towerStep_iff_execStep member).mp step)⟩,
    fun t' step => ⟨t', (slice_towerStep_iff_execStep member).mpr step, rfl,
      sliceTerms_execStep member step⟩⟩

end Slice

/-! ## Strong normalization is a bisimulation invariant -/

section Invariance

universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop} {f : α → β}

/-- **A bounded morphism preserves and reflects strong normalization.** -/
theorem acc_iff_of_isBoundedMorphism (bounded : IsBoundedMorphism r s f) (a : α) :
    Acc (fun y x => r x y) a ↔ Acc (fun y x => s x y) (f a) := by
  constructor
  · intro accessible
    induction accessible with
    | intro x _ ih =>
        refine Acc.intro _ fun b' step => ?_
        obtain ⟨x', step', rfl⟩ := bounded.lift step
        exact ih x' step'
  · intro accessible
    suffices ∀ b, Acc (fun y x => s x y) b → ∀ x, f x = b → Acc (fun y x => r x y) x from
      this _ accessible a rfl
    intro b accessibleB
    induction accessibleB with
    | intro y _ ih =>
        rintro x rfl
        exact Acc.intro _ fun x' step => ih (f x') (bounded.map step) x' rfl

end Invariance

/-! ## Strong normalization agrees on pure λ-terms -/

section PureNormalization

variable {n : ℕ}

/-- The pure λ-terms with `n` free variables. -/
abbrev PureTm (n : ℕ) : Type :=
  {t : Presentation.Tower.Tm n // PureLambda t}

/-- The pure λ-terms under the tower's steps. -/
abbrev pureStep (s t : PureTm n) : Prop :=
  TowerStep n s.1 t.1

/-- The inclusion of pure λ-terms is a bounded morphism into the tower. -/
theorem pureInclusion_tower : IsBoundedMorphism (@pureStep n) (TowerStep n) Subtype.val :=
  ⟨fun _ _ step => step,
    fun s u step => ⟨⟨u, PureLambda.of_step towerRootFree step s.2⟩, step, rfl⟩⟩

/-- The inclusion of pure λ-terms is a bounded morphism into the executable
package. -/
theorem pureInclusion_exec : IsBoundedMorphism (@pureStep n) (ExecStep n) Subtype.val :=
  ⟨fun s _ step => (towerStep_iff_execStep s.2).mp step,
    fun s u step => ⟨⟨u, PureLambda.of_step objectRootFree step s.2⟩,
      (towerStep_iff_execStep s.2).mpr step, rfl⟩⟩

/-- **On pure λ-terms the tower and the executable package have the same
strongly normalizing terms.** -/
theorem pure_towerSN_iff_execSN {t : Presentation.Tower.Tm n} (pure : PureLambda t) :
    Acc (fun u t => TowerStep n t u) t ↔ SN CodeModel.objectRules t :=
  (acc_iff_of_isBoundedMorphism pureInclusion_tower ⟨t, pure⟩).symm.trans
    (acc_iff_of_isBoundedMorphism pureInclusion_exec ⟨t, pure⟩)

end PureNormalization

/-! ## One relation on the slice -/

section OneRelation

variable {Γ : List Ty} {A : Ty}

/-- **β-reduction of intrinsic simple terms is strongly normalizing**, pulled
back from the executable package's normalization theorem along erasure. -/
theorem betaStep_sn (t : Term Γ A) : Acc (fun u t => BetaStep t u) t :=
  (acc_iff_of_isBoundedMorphism (erase_isBoundedMorphism_exec Γ A) t).mpr (simple_sn t).1

/-- **The sealed tower is strongly normalizing at every erasure.** -/
theorem erase_towerSN (t : Term Γ A) :
    Acc (fun u t => TowerStep Γ.length t u) (TowerDTT.eraseTerm t) :=
  (acc_iff_of_isBoundedMorphism (erase_isBoundedMorphism Γ A) t).mp (betaStep_sn t)

/-- **One relation on the slice**: every slice term is strongly normalizing for
the executable package and for the sealed tower, the two relations have the
same steps out of it, and every executable reduct stays in the slice. -/
theorem slice_one_relation (Γ : List Ty) :
    ∀ t ∈ sliceTerms Γ,
      SN CodeModel.objectRules t ∧ Acc (fun u t => TowerStep Γ.length t u) t ∧
        (∀ u, TowerStep Γ.length t u ↔ ExecStep Γ.length t u) ∧
        ∀ u, ExecStep Γ.length t u → u ∈ sliceTerms Γ := by
  rintro _ ⟨A, s, rfl⟩
  exact ⟨(simple_sn s).1, erase_towerSN s,
    fun _ => slice_towerStep_iff_execStep ⟨A, s, rfl⟩,
    fun _ step => sliceTerms_execStep ⟨A, s, rfl⟩ step⟩

/-- **The executable relation restricted to the slice is well founded.** -/
theorem slice_wellFounded (Γ : List Ty) :
    WellFounded fun u t : sliceTerms Γ => ExecStep Γ.length t.1 u.1 :=
  ⟨fun t => InvImage.accessible Subtype.val ((slice_one_relation Γ t.1 t.2).1)⟩

/-- `Ω` is a pure λ-term. -/
theorem omega_pure : PureLambda omega :=
  .app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))

/-- **Control: `Ω` is not strongly normalizing for the executable relation**
(`omega_not_sn`, read through `ExecStep`). -/
theorem omega_not_execSN : ¬ Acc (fun u t => ExecStep 0 t u) omega :=
  omega_not_sn

/-- **Control: `Ω` loops in the sealed tower too.** -/
theorem omega_not_towerSN : ¬ Acc (fun u t => TowerStep 0 t u) omega :=
  not_acc_of_loop (r := fun u t => TowerStep 0 t u)
    (Presentation.StepCore.betaPi _ omegaHalf : TowerStep 0 omega omega)

/-- **`Ω` is not an erasure of a simple term**: the slice is strongly
normalizing and `Ω` is not. -/
theorem omega_not_mem_sliceTerms : omega ∉ sliceTerms [] :=
  fun member => omega_not_sn (slice_one_relation [] omega member).1

end OneRelation

/-! ## Off the slice the two relations differ -/

section OffSlice

/-- An application spine headed by a constant is not a universe head. -/
theorem foldl_app_ne_head {n : ℕ} :
    ∀ (args : List (Presentation.Tower.Tm n)) {f : Presentation.Tower.Tm n},
      (∀ h, f ≠ .head h) → ∀ h, args.foldl Presentation.Tm.app f ≠ .head h
  | [], _, notHead, h => notHead h
  | _ :: rest, _, _, h => foldl_app_ne_head rest (fun _ same => by cases same) h

/-- **A universe head steps to itself in the sealed tower.** -/
theorem towerStep_head_loop (n : ℕ) :
    TowerStep n (.head .legacyGround) (.head .legacyGround) :=
  .head (show Presentation.Tower.HeadEq .legacyGround .legacyGround from trivial)

/-- **A universe head takes no executable step.** -/
theorem execStep_head_inv {n : ℕ} {h : Presentation.Tower.Head}
    {u : Presentation.Tower.Tm n} : ¬ ExecStep n (.head h) u := by
  intro step
  cases step with
  | head impossible => exact impossible
  | root rootStep =>
      obtain ⟨c, args, same⟩ :=
        Presentation.TypedEquality.StrongNormalization.RootShape.spineHeaded CodeModel.objectShape
          rootStep
      exact foldl_app_ne_head args (fun _ equal => by cases equal) h same.symm

/-- **Control: the identity is not a bisimulation on all raw terms**: a
universe head is not bisimilar to itself across the two systems. -/
theorem not_bisimilar_head (n : ℕ) :
    ¬ Bisimilar (TowerStep n) (ExecStep n) (.head .legacyGround) (.head .legacyGround) := by
  intro bisimilar
  obtain ⟨_, step, _⟩ := bisimilar.exists_child_left (towerStep_head_loop n)
  exact execStep_head_inv step

/-- A universe head is strongly normalizing for the executable package. -/
theorem head_execSN {n : ℕ} (h : Presentation.Tower.Head) :
    SN CodeModel.objectRules (.head h : Presentation.Tower.Tm n) :=
  Acc.intro _ fun _ step => (execStep_head_inv step).elim

/-- **Control: a universe head is not strongly normalizing for the tower.** -/
theorem head_not_towerSN (n : ℕ) :
    ¬ Acc (fun u t => TowerStep n t u) (.head .legacyGround) :=
  not_acc_of_loop (r := fun u t => TowerStep n t u) (towerStep_head_loop n)

/-- Every erased simple type steps to itself in the sealed tower. -/
theorem eraseTypeAt_towerLoop : ∀ (A : Ty) (n : ℕ),
    TowerStep n (TowerDTT.eraseTypeAt n A) (TowerDTT.eraseTypeAt n A)
  | .atom, n => towerStep_head_loop n
  | .arr domain _, n => .congPiDom (eraseTypeAt_towerLoop domain n)

/-- **Control: no erased simple type is strongly normalizing for the sealed
tower**, although the executable package normalizes it (`simple_sn`). -/
theorem eraseTypeAt_not_towerSN (A : Ty) (n : ℕ) :
    ¬ Acc (fun u t => TowerStep n t u) (TowerDTT.eraseTypeAt n A) :=
  not_acc_of_loop (r := fun u t => TowerStep n t u) (eraseTypeAt_towerLoop A n)

/-- The tower's root computation has no steps. -/
theorem tower_noRoot {n : ℕ} {t u : Presentation.Tower.Tm n} :
    ¬ Presentation.Tower.rules.computation.step t u :=
  fun step => step.elim

/-- Identity elimination at reflexivity, with every argument the variable of a
one-variable context. -/
def jRedex : Presentation.Tower.Tm 1 :=
  Presentation.TypedEquality.Normalization.appSpine (.const Package.jName)
    [.var 0, .var 0, .var 0, .var 0, .var 0, .refl (.var 0)]

/-- **Identity elimination at reflexivity is an executable step.** -/
theorem execStep_jRedex : ExecStep 1 jRedex (.var 0) :=
  .root (CodeModel.programCodes.extend_base_step rules
    (rules_step (listed 3 (by decide)) ⟨_, _, _, _, _, _, rfl, rfl⟩))

theorem jRedex_redexFree : RedexFree jRedex :=
  .app (.app (.app (.app (.app (.app (.const _) (fun _ same => by cases same) (.var 0))
    (fun _ same => by cases same) (.var 0)) (fun _ same => by cases same) (.var 0))
    (fun _ same => by cases same) (.var 0)) (fun _ same => by cases same) (.var 0))
    (fun _ same => by cases same) (.refl (.var 0))

/-- **Control: the sealed tower cannot reduce it.** -/
theorem jRedex_towerNormal (u : Presentation.Tower.Tm 1) : ¬ TowerStep 1 jRedex u :=
  jRedex_redexFree.no_step tower_noRoot

/-- **Control: on all raw terms the identity is not a simulation of the tower by
the executable package** (a universe head). -/
theorem not_preservesEdges_tower_exec (n : ℕ) : ¬ PreservesEdges (TowerStep n) (ExecStep n) id :=
  fun preserves => execStep_head_inv (preserves (towerStep_head_loop n))

/-- **Control: nor of the executable package by the tower** (identity
elimination at reflexivity). -/
theorem not_preservesEdges_exec_tower : ¬ PreservesEdges (ExecStep 1) (TowerStep 1) id :=
  fun preserves => jRedex_towerNormal _ (preserves execStep_jRedex)

/-- The self-application `ω = λx. x x` in one free variable. -/
def selfApply : Presentation.Tower.Tm 1 :=
  .lam (.app (.var 0) (.var 0))

/-- Identity elimination at reflexivity with method `ω`, applied to `ω`. -/
def jOmega : Presentation.Tower.Tm 1 :=
  .app (Presentation.TypedEquality.Normalization.appSpine (.const Package.jName)
    [.var 0, .var 0, .var 0, selfApply, .var 0, .refl (.var 0)]) selfApply

theorem selfApply_redexFree : RedexFree selfApply :=
  .lam (.app (.var 0) (fun _ same => by cases same) (.var 0))

theorem jOmega_redexFree : RedexFree jOmega :=
  .app (.app (.app (.app (.app (.app (.app (.const _) (fun _ same => by cases same) (.var 0))
    (fun _ same => by cases same) (.var 0)) (fun _ same => by cases same) (.var 0))
    (fun _ same => by cases same) selfApply_redexFree) (fun _ same => by cases same) (.var 0))
    (fun _ same => by cases same) (.refl (.var 0))) (fun _ same => by cases same)
    selfApply_redexFree

/-- **The sealed tower sees `jOmega` as a normal form.** -/
theorem jOmega_towerSN : Acc (fun u t => TowerStep 1 t u) jOmega :=
  Acc.intro _ fun _ step => (jOmega_redexFree.no_step tower_noRoot step).elim

/-- `Ω` in one free variable reduces to itself. -/
theorem omegaOne_execLoop :
    ExecStep 1 (.app selfApply selfApply) (.app selfApply selfApply) :=
  Presentation.StepCore.betaPi _ selfApply

/-- **Control: the executable package reduces `jOmega` to `Ω`**, so it is not
strongly normalizing there. -/
theorem jOmega_not_execSN : ¬ SN CodeModel.objectRules jOmega := by
  intro sn
  have step : ExecStep 1 jOmega (.app selfApply selfApply) :=
    .congAppFun (.root (CodeModel.programCodes.extend_base_step rules
      (rules_step (listed 3 (by decide)) ⟨_, _, _, _, _, _, rfl, rfl⟩)))
  exact not_acc_of_loop (r := fun u t => ExecStep 1 t u) omegaOne_execLoop (sn.inv step)

end OffSlice

end Mettapedia.GSLT.Scope.SimpleFragmentExecutable
