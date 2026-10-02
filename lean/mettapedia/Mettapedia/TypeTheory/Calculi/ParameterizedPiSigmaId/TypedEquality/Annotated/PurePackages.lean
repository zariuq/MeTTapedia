import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ConstantInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.CoreHeadReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationForms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Lifting

/-!
# Packages without root computation: injective type formers and the lifting

A rule package is **rigid** (`Rules.Rigid`) when it has no root computation and its declared
types have no abstraction: its declared constants are typed and never computed with. It is
**pure** (`Rules.Pure`) when, moreover, it declares no constant; a pure package is rigid
(`Rules.Pure.rigid`), and its annotation is `ChurchRules.ofPure`.

**Injectivity and no-confusion of the annotated type formers** (`CFormerFacts.ofNoSteps`), for
every annotated package without root steps, whatever constants it declares. The logical
relation reads canonical forms off rigid types (`RigidTypes`), which need a typed decoder of
proposition codes. So the package is extended (`RigidExtension.church`): its constants move to
shifted names (`RigidExtension.shift`), apart from the extension's own names, and two rigid
constants are added, `prop : v₀` and `holds : prop → u₀` for a universe `u₀` typed by `v₀`,
with no root step. For the extension:

* the core weak-head reduction is deterministic and leaves the canonical forms alone
  (`RigidExtension.reduction`), since no root step exists;
* reading every universe as the universe, every other head as the ground type and every
  constant as the least element is a valid reading (`RigidExtension.valid`), under which every
  constant is adequate (`RigidExtension.constAdequate`): the least element observes nothing;
* the heads that are not universes are rigid ground types and the decoder is stuck at
  universes.

The fundamental lemma of the logical relation, applied to the extension, matches equal type
formers with components equal in the extension (`CTypeEq.formersMatch_of_normal`). Renaming
the constants sends every derivation of the package into the extension
(`RigidExtension.toExtInstance`). Instantiating each shifted name by its constant, `prop` by
`u₀` and `holds` by the identity on it sends every derivation of the extension back to the
package (`RigidExtension.backInstance`, `CDerivable.instConsts`), and the round trip changes no
term (`RigidExtension.back_toExt`): the extension is conservative over the package, with no
condition on the constants a term mentions.

**The lifting** (`LiftingFacts.ofNoSteps`, `LiftingFacts.ofRigid`, `lifts_ofRigid`): with
strong normalization of typed terms, coherence of annotations follows (`coherence`); root
lifting and root preservation hold vacuously; declared types without abstractions are formed
as soon as their erasures are (`CDeclsRigid.ofRigid`). Every derivation of a rigid package is
the erasure of a derivation of its annotation over every formed annotated context erasing to
its context: the Church–Curry correspondence for rigid packages. The pure case
(`CFormerFacts.ofPure`, `LiftingFacts.ofPure`, `lifts_ofPure`) is an instance.

Strong normalization may come from a larger package: formed contexts persist into a larger
package (`Normalization.CtxFormed.mono`), and strong normalization for a package with more root
steps gives strong normalization for the package (`StrongNormalization.SN.of_rootSub`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-- **A pure universe package**: it declares no constant and has no root computation. -/
structure Rules.Pure {Head : Type} (R : Rules Head) : Prop where
  noConstants : ∀ name, R.constantType name = none
  noSteps : ∀ {n : Nat} {l r : Tm Head n}, ¬ R.computation.step l r

/-- **A rigid package**: it has no root computation, and its declared types have no
abstraction. -/
structure Rules.Rigid {Head : Type} (R : Rules Head) : Prop where
  noSteps : ∀ {n : Nat} {l r : Tm Head n}, ¬ R.computation.step l r
  lamFree : ∀ {name : DeclName} {type : Tm Head 0}, R.constantType name = some type →
    TypedEquality.Annotated.lamFree type = true

/-- A pure package is rigid. -/
theorem Rules.Pure.rigid {Head : Type} {R : Rules Head} (pure : R.Pure) : R.Rigid where
  noSteps := pure.noSteps
  lamFree := fun declared => by
    rw [pure.noConstants] at declared
    cases declared

namespace TypedEquality

/-! ## Sub-packages: formed contexts and strong normalization -/

/-- A formed context of a sub-package is formed in the package. -/
theorem Normalization.CtxFormed.mono {Head : Type} {R' R : Rules Head}
    (sub : Normalization.RulesSub R' R) {n : Nat} {Γ : Ctx Head n}
    (formed : Normalization.CtxFormed R' Γ) : Normalization.CtxFormed R Γ := by
  induction formed with
  | nil => exact .nil
  | snoc _ type ih =>
      obtain ⟨u, hu, typing⟩ := type
      exact .snoc ih ⟨u, sub.isUniverse hu, Normalization.Derivable.mono sub typing⟩

/-- A step of the directed reduction of a package is a step of every package with its root
steps. -/
theorem StrongNormalization.Reduces.of_rootSub {Head : Type} {R R' : Rules Head}
    (sub : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r → R'.computation.step l r)
    {n : Nat} {t u : Tm Head n} (step : StrongNormalization.Reduces R t u) :
    StrongNormalization.Reduces R' t u := by
  induction step with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | head h => exact .head h
  | root h => exact .root (sub h)
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

/-- **Strong normalization is inherited from a package with more root steps.** -/
theorem StrongNormalization.SN.of_rootSub {Head : Type} {R R' : Rules Head}
    (sub : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r → R'.computation.step l r)
    {n : Nat} {t : Tm Head n} (sn : StrongNormalization.SN R' t) : StrongNormalization.SN R t :=
  Subrelation.accessible (fun step => StrongNormalization.Reduces.of_rootSub sub step) sn

namespace Annotated

open Impredicative.Domain
open Normalization (LevelModel CumulativeAlgebra HeadSame)
open UniverseLevel (LevelOrder)

variable {Head : Type}

/-- The annotation of a pure package: no declared constants and no root steps. -/
abbrev ChurchRules.ofPure {R : Rules Head} (pure : R.Pure) : ChurchRules R :=
  ChurchRules.empty R pure.noConstants

/-- **A reading of the heads in the domain**: universes as the universe, heads typed by a head
that are not universes as the ground type, every head a type of the universe, and heads equal
by head equality alike. -/
structure HeadReading (R : Rules Head) where
  read : Head → List Tok
  universes : ∀ {h : Head}, R.isUniverse h → read h = Elem.univ
  types : ∀ h : Head, Ty (read h) Elem.univ
  headEq : ∀ {h h' : Head}, R.headEq h h' → read h = read h'
  ground : ∀ {h u : Head}, R.headTyping h u → ¬ R.isUniverse h → read h = Elem.ground

/-! ## The core reduction of a package without root steps -/

section Core

variable {R : Rules Head} {P : ChurchRules R} {K : RigidTypes P}
  (noSteps : ∀ {n : Nat} {l r : CTm Head n}, ¬ P.computation.step l r)
include noSteps

/-- A core step without root steps is at an application or a projection. -/
theorem CoreStep.shape {n : Nat} {t u : CTm Head n} (s : CoreStep P K t u) :
    (∃ f a, t = .app f a) ∨ (∃ p, t = .fst p) ∨ (∃ p, t = .snd p) := by
  cases s with
  | beta A b a => exact .inl ⟨_, _, rfl⟩
  | appFun a _ => exact .inl ⟨_, _, rfl⟩
  | root h => exact (noSteps h).elim
  | holdsArg _ => exact .inl ⟨_, _, rfl⟩
  | fstPair a b => exact .inr (.inl ⟨_, rfl⟩)
  | sndPair a b => exact .inr (.inr ⟨_, rfl⟩)
  | fst _ => exact .inr (.inl ⟨_, rfl⟩)
  | snd _ => exact .inr (.inr ⟨_, rfl⟩)

/-- A term that is neither an application nor a projection takes no core step. -/
theorem CoreStep.not_of_shape {n : Nat} {t u : CTm Head n}
    (app : ∀ f a, t ≠ .app f a) (fst : ∀ p, t ≠ .fst p) (snd : ∀ p, t ≠ .snd p) :
    ¬ CoreStep P K t u := fun s => by
  rcases CoreStep.shape noSteps s with ⟨f, a, e⟩ | ⟨p, e⟩ | ⟨p, e⟩
  · exact app f a e
  · exact fst p e
  · exact snd p e

theorem CoreStep.not_const {n : Nat} {c : DeclName} {u : CTm Head n} :
    ¬ CoreStep P K (.const c) u :=
  CoreStep.not_of_shape noSteps (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun)

theorem CoreStep.not_head {n : Nat} {h : Head} {u : CTm Head n} :
    ¬ CoreStep P K (.head h) u :=
  CoreStep.not_of_shape noSteps (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun)

theorem CoreStep.not_lam {n : Nat} {A : CTm Head n} {b : CTm Head (n + 1)} {u : CTm Head n} :
    ¬ CoreStep P K (.lam A b) u :=
  CoreStep.not_of_shape noSteps (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun)

theorem CoreStep.not_pair {n : Nat} {a b u : CTm Head n} : ¬ CoreStep P K (.pair a b) u :=
  CoreStep.not_of_shape noSteps (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun)

/-- **The core reduction without root steps is deterministic.** -/
theorem CoreStep.deterministic {n : Nat} {t u u' : CTm Head n} (s₁ : CoreStep P K t u)
    (s₂ : CoreStep P K t u') : u = u' := by
  induction s₁ generalizing u' with
  | beta A b a =>
      cases s₂ with
      | beta => rfl
      | appFun _ s => exact absurd s (CoreStep.not_lam noSteps)
      | root h => exact (noSteps h).elim
  | appFun a s ih =>
      cases s₂ with
      | beta => exact absurd s (CoreStep.not_lam noSteps)
      | appFun _ s' => rw [ih s']
      | root h => exact (noSteps h).elim
      | holdsArg _ => exact absurd s (CoreStep.not_const noSteps)
  | root h => exact (noSteps h).elim
  | holdsArg s ih =>
      cases s₂ with
      | appFun _ s' => exact absurd s' (CoreStep.not_const noSteps)
      | root h => exact (noSteps h).elim
      | holdsArg s' => rw [ih s']
  | fstPair a b =>
      cases s₂ with
      | root h => exact (noSteps h).elim
      | fstPair => rfl
      | fst s => exact absurd s (CoreStep.not_pair noSteps)
  | sndPair a b =>
      cases s₂ with
      | root h => exact (noSteps h).elim
      | sndPair => rfl
      | snd s => exact absurd s (CoreStep.not_pair noSteps)
  | fst s ih =>
      cases s₂ with
      | root h => exact (noSteps h).elim
      | fstPair => exact absurd s (CoreStep.not_pair noSteps)
      | fst s' => rw [ih s']
  | snd s ih =>
      cases s₂ with
      | root h => exact (noSteps h).elim
      | sndPair => exact absurd s (CoreStep.not_pair noSteps)
      | snd s' => rw [ih s']

/-- The successor applied to a term takes no core step, the successor not being the
decoder. -/
theorem CoreStep.not_suc (ne : K.suc ≠ K.holds) {n : Nat} {m u : CTm Head n} :
    ¬ CoreStep P K (.app (.const K.suc) m) u := by
  intro s
  generalize e : (CTm.app (.const K.suc) m : CTm Head n) = t at s
  cases s with
  | beta A b a => cases e
  | appFun a s' =>
      injection e with _ e₁ _
      subst e₁
      exact CoreStep.not_const noSteps s'
  | root h => exact noSteps h
  | holdsArg _ =>
      injection e with _ e₁ _
      injection e₁ with _ e₂
      exact ne e₂
  | fstPair a b => cases e
  | sndPair a b => cases e
  | fst _ => cases e
  | snd _ => cases e

/-- The decoder applied to a head takes no core step. -/
theorem CoreStep.not_holds_head {n : Nat} {h : Head} {u : CTm Head n} :
    ¬ CoreStep P K (.app (.const K.holds) (.head h)) u := by
  intro s
  generalize e : (CTm.app (.const K.holds) (.head h) : CTm Head n) = t at s
  cases s with
  | beta A b a => cases e
  | appFun a s' =>
      injection e with _ e₁ _
      subst e₁
      exact CoreStep.not_const noSteps s'
  | root h => exact noSteps h
  | holdsArg s' =>
      injection e with _ _ e₂
      subst e₂
      exact CoreStep.not_head noSteps s'
  | fstPair a b => cases e
  | sndPair a b => cases e
  | fst _ => cases e
  | snd _ => cases e

end Core

/-! ## Instantiation keeps type formers -/

section Formers

variable {R R' : Rules Head} {P : ChurchRules R} {Q : ChurchRules R'}
  {θ : DeclName → CTm Head 0}

/-- An instantiated type former is the same former. -/
theorem CFormer.instConsts {n : Nat} {A : CTm Head n} (former : CFormer A) :
    CFormer (A.instConsts θ) := by
  cases former with
  | head h => exact .head h
  | pi A B => exact .pi _ _
  | sigma A B => exact .sigma _ _
  | id A a b => exact .id _ _ _

/-- **Matching type formers instantiate**: the same formers, with instantiated components
equal in the target package. -/
theorem CFormersMatch.instConsts (inst : ConstInstance P Q θ) {n : Nat} {Γ : CCtx Head n}
    {A B : CTm Head n} (m : CFormersMatch P Γ A B) :
    CFormersMatch Q (Γ.instConsts θ) (A.instConsts θ) (B.instConsts θ) := by
  rcases m with ⟨h, h', rfl, rfl, same⟩ | ⟨A₁, B₁, A₂, B₂, rfl, rfl, eA, eB⟩ |
    ⟨A₁, B₁, A₂, B₂, rfl, rfl, eA, eB⟩ | ⟨C, x, y, C', x', y', rfl, rfl, eC, ex, ey⟩
  · exact .inl ⟨h, h', rfl, rfl, same.imp id inst.headEq⟩
  · exact .inr (.inl ⟨_, _, _, _, rfl, rfl, CTypeEq.instConsts inst eA,
      CTypeEq.instConsts inst eB⟩)
  · exact .inr (.inr (.inl ⟨_, _, _, _, rfl, rfl, CTypeEq.instConsts inst eA,
      CTypeEq.instConsts inst eB⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, _, _, _, rfl, rfl, CTypeEq.instConsts inst eC,
      CDerivable.instConsts inst ex, CDerivable.instConsts inst ey⟩))

end Formers

/-! ## The rigid extension of a package without root steps -/

namespace RigidExtension

/-- The type of proposition codes. -/
def prop : DeclName := .num .anonymous 0
/-- The decoder. -/
def holds : DeclName := .num .anonymous 1
/-- The numbers, zero and successor: names the relation reads, not declared. -/
def num : DeclName := .num .anonymous 2
def zero : DeclName := .num .anonymous 3
def suc : DeclName := .num .anonymous 4

theorem holds_ne_prop : holds ≠ prop := by
  intro h
  injection h with _ h'
  exact absurd h' (by decide)

theorem suc_ne_holds : suc ≠ holds := by
  intro h
  injection h with _ h'
  exact absurd h' (by decide)

/-- **The name of a constant of the package in the extension.** The package's names move to
names with a string component, apart from the extension's own names, which are numeric. -/
def shift (c : DeclName) : DeclName := .str c ""

/-- **The renaming of the package's constants** into the extension. -/
def toExt (c : DeclName) : CTm Head 0 := .const (shift c)

variable (u₀ v₀ : Head)

/-- The declared types of the two rigid constants: `prop : v₀` and `holds : prop → u₀`. -/
def decls (c : DeclName) : Option (CTm Head 0) :=
  if c = prop then some (.head v₀) else if c = holds then some (.pi (.const prop) (.head u₀))
  else none

theorem decls_prop : decls u₀ v₀ prop = some (.head v₀) := if_pos rfl

theorem decls_holds : decls u₀ v₀ holds = some (.pi (.const prop) (.head u₀)) := by
  unfold decls
  rw [if_neg holds_ne_prop, if_pos rfl]

/-- **The declared types of the extension**: at a shifted name the package's declared type,
its constants renamed; `prop` and `holds` at their names. -/
def extDecls {R : Rules Head} (P : ChurchRules R) : DeclName → Option (CTm Head 0)
  | .str c _ => (P.constantType c).map (CTm.instConsts toExt)
  | c => decls u₀ v₀ c

/-- The package extended: the package's universe rules, the declared types of the extension,
erased. -/
def rules {R : Rules Head} (P : ChurchRules R) : Rules Head :=
  { R with constantType := fun c => (extDecls u₀ v₀ P c).map CTm.erase }

/-- The annotation of the extension, without root steps. -/
def church {R : Rules Head} (P : ChurchRules R) : ChurchRules (rules u₀ v₀ P) where
  constantType := extDecls u₀ v₀ P
  computation := .empty
  erase_constantType := fun _ => rfl
  erase_step := fun h => h.elim

theorem church_prop {R : Rules Head} (P : ChurchRules R) :
    (church u₀ v₀ P).constantType prop = some (.head v₀) :=
  decls_prop u₀ v₀

theorem church_holds {R : Rules Head} (P : ChurchRules R) :
    (church u₀ v₀ P).constantType holds = some (.pi (.const prop) (.head u₀)) :=
  decls_holds u₀ v₀

theorem church_shift {R : Rules Head} (P : ChurchRules R) (c : DeclName) :
    (church u₀ v₀ P).constantType (shift c) = (P.constantType c).map (CTm.instConsts toExt) :=
  rfl

/-- The definitions of the two rigid constants: `prop` is the universe `u₀`, `holds` the
identity on it; every other name is its constant. -/
def inst (c : DeclName) : CTm Head 0 :=
  if c = prop then .head u₀ else if c = holds then .lam (.head u₀) (.var 0) else .const c

theorem inst_prop : inst u₀ prop = .head u₀ := if_pos rfl

theorem inst_holds : inst u₀ holds = .lam (.head u₀) (.var 0) := by
  unfold inst
  rw [if_neg holds_ne_prop, if_pos rfl]

/-- **The instantiation back from the extension**: each shifted name by its constant, the
other names as `inst`. -/
def back : DeclName → CTm Head 0
  | .str c _ => .const c
  | c => inst u₀ c

/-- **The round trip is the identity**: renaming into the extension and instantiating back
changes no term. -/
theorem back_toExt {n : Nat} (t : CTm Head n) :
    (t.instConsts toExt).instConsts (back u₀) = t := by
  rw [CTm.instConsts_instConsts]
  exact CTm.instConsts_const t

/-- The round trip is the identity on contexts. -/
theorem back_toExt_ctx {n : Nat} (Γ : CCtx Head n) :
    (Γ.instConsts toExt).instConsts (back u₀) = Γ := by
  rw [CCtx.instConsts_instConsts]
  exact CCtx.instConsts_const Γ

variable {u₀ v₀} {R : Rules Head} {P : ChurchRules R} {L : Type} [LevelOrder L]

/-- The universe laws of the package are those of its extension. -/
def levels (levels : LevelModel R L) : LevelModel (rules u₀ v₀ P) L where
  level := levels.level
  successor := levels.successor
  universe_typing := levels.universe_typing
  ground_typing := levels.ground_typing
  cumulative_universe := levels.cumulative_universe
  headEq_level := levels.headEq_level
  join_level := levels.join_level
  join_exists := levels.join_exists
  join_upper := levels.join_upper
  cumulative_refl := levels.cumulative_refl
  headEq_symm := levels.headEq_symm
  headEq_trans := levels.headEq_trans
  universe_decided := levels.universe_decided

section Typings

variable (levels : LevelModel R L) (hu₀ : R.isUniverse u₀) (t₀ : R.headTyping u₀ v₀)
include levels hu₀ t₀

/-- `v₀` is a universe. -/
theorem hv₀ : R.isUniverse v₀ := (levels.universe_typing hu₀ t₀).1

/-- `prop` is a type of the universe `v₀`. -/
theorem prop_typed {n : Nat} (Γ : CCtx Head n) :
    CTyped (church u₀ v₀ P) Γ (.const prop) (.head v₀) := by
  obtain ⟨v₁, hv₁, t₁, -⟩ := levels.successor (hv₀ levels hu₀ t₀)
  exact .const (church_prop u₀ v₀ P) (.headType t₁) hv₁

/-- **The decoder is typed** at `prop → u₀`. -/
theorem holds_typed {n : Nat} (Γ : CCtx Head n) :
    CTyped (church u₀ v₀ P) Γ (.const holds) (.pi (.const prop) (.head u₀)) := by
  have hv := hv₀ levels hu₀ t₀
  obtain ⟨w, join⟩ := levels.join_exists hv hv
  exact .const (church_holds u₀ v₀ P)
    (.piForm (prop_typed levels hu₀ t₀ .nil) hv (.headType t₀) hv join)
    (levels.join_level join).1

/-- The rigid constants instantiate back to closed terms of the package typed at their
instantiated declared types. -/
theorem typed_back {c : DeclName} {D : CTm Head 0} (declared : decls u₀ v₀ c = some D) :
    CTyped P .nil (inst u₀ c) (D.instConsts (back u₀)) := by
  have hv := hv₀ levels hu₀ t₀
  unfold decls at declared
  split at declared
  · rename_i hc
    subst hc
    cases declared
    show CTyped _ _ (inst u₀ prop) (.head v₀)
    rw [inst_prop]
    exact .headType t₀
  · split at declared
    · rename_i _ hc
      subst hc
      cases declared
      show CTyped _ _ (inst u₀ holds) (.pi ((inst u₀ prop).liftClosed) (.head u₀))
      rw [inst_prop, inst_holds]
      obtain ⟨w, join⟩ := levels.join_exists hv hv
      exact .lamIntro (.headType t₀) hv (.piForm (.headType t₀) hv (.headType t₀) hv join)
        (levels.join_level join).1 (.var 0)
    · cases declared

end Typings

/-- **The rigid types of the extension**: `prop` and `holds`, names for the numbers that the
extension does not declare, and the heads that are not universes as ground types. -/
def rigid (levels : LevelModel R L) (hu₀ : R.isUniverse u₀) (t₀ : R.headTyping u₀ v₀) :
    RigidTypes (church u₀ v₀ P) where
  prop := prop
  holds := holds
  num := num
  zero := zero
  suc := suc
  holds_typed := fun Γ => ⟨u₀, hu₀, holds_typed levels hu₀ t₀ Γ⟩
  ground := fun g => ∃ h, g = .head h ∧ ¬ R.isUniverse h

section Reduction

variable (levels : LevelModel R L) (hu₀ : R.isUniverse u₀) (t₀ : R.headTyping u₀ v₀)

theorem noSteps {n : Nat} {l r : CTm Head n} : ¬ (church u₀ v₀ P).computation.step l r :=
  fun h => h.elim

/-- **The weak-head reduction of the extension**: its core steps, without root steps. -/
def reduction : HeadReduction (church u₀ v₀ P) (rigid levels hu₀ t₀) where
  step := CoreStep (church u₀ v₀ P) (rigid levels hu₀ t₀)
  beta := .beta
  appFun := fun a s => .appFun a s
  root := .root
  holdsArg := .holdsArg
  deterministic := CoreStep.deterministic noSteps
  head_normal := fun _ _ => CoreStep.not_head noSteps
  pi_normal := fun _ _ _ =>
    CoreStep.not_of_shape noSteps (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun)
  id_normal := fun _ _ _ _ =>
    CoreStep.not_of_shape noSteps (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun)
  refl_normal := fun _ _ =>
    CoreStep.not_of_shape noSteps (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun)
  prop_normal := fun _ => CoreStep.not_const noSteps
  num_normal := fun _ => CoreStep.not_const noSteps
  zero_normal := fun _ => CoreStep.not_const noSteps
  suc_normal := fun _ _ => CoreStep.not_suc noSteps suc_ne_holds
  fstPair := .fstPair
  sndPair := .sndPair
  fst := .fst
  snd := .snd
  sigma_normal := fun _ _ _ =>
    CoreStep.not_of_shape noSteps (fun _ _ => nofun) (fun _ => nofun) (fun _ => nofun)
  ground_normal := fun _ hg => by
    obtain ⟨h, rfl, -⟩ := hg
    exact CoreStep.not_head noSteps

/-- The decoder is stuck at universes. -/
theorem stuck : (reduction (P := P) levels hu₀ t₀).DecoderStuckAtUniverses :=
  fun _ _ => CoreStep.not_holds_head noSteps

/-- A type former takes no step. -/
theorem normal_of_former {n : Nat} {B : CTm Head n} (former : CFormer B) :
    (reduction (P := P) levels hu₀ t₀).Normal B := by
  cases former with
  | head h => exact HeadReduction.normal_head h
  | pi A B => exact HeadReduction.normal_pi A B
  | sigma A B => exact HeadReduction.normal_sigma A B
  | id A a b => exact HeadReduction.normal_id A a b

end Reduction

section Reading

variable (read : HeadReading R)

/-- The reading of the extension: heads as the head reading says, constants as the least
element. -/
def reading : Reading Head := ⟨read.read, fun _ => Ideal.bot⟩

/-- **The reading validates the extension.** -/
theorem valid (levels : LevelModel R L) :
    ReadingValid (reading read) (church u₀ v₀ P) :=
  ReadingValid.ofLevels (RigidExtension.levels levels) read.universes read.types read.headEq
    (fun _ _ => Ideal.le_antisymm (Ideal.projT_le _ _) (Ideal.bot_le _)) (fun step => step.elim)

/-- **The heads that are not universes are rigid ground types.** -/
theorem groundHeads (levels : LevelModel R L) (hu₀ : R.isUniverse u₀)
    (t₀ : R.headTyping u₀ v₀) : (rigid (P := P) levels hu₀ t₀).GroundHeads (reading read) := by
  intro h u typing
  rcases levels.universe_decided h with hh | hh
  · exact .inl hh
  · exact .inr ⟨read.ground typing hh, fun {_} => ⟨h, rfl, hh⟩⟩

/-- **Every constant of the extension is adequate** under the reading: it denotes the least
element, whose tokens are entailed by the empty element and relate everything. -/
theorem constAdequate {K : RigidTypes (church u₀ v₀ P)} (H : HeadReduction (church u₀ v₀ P) K) :
    ConstAdequate (reading read) H := by
  intro _ _ _ _ _ _ _ _ _ _ s member _
  exact RT.of_vacuous member

end Reading

/-- **The package's derivations rename into the extension.** -/
theorem toExtInstance (noSteps : ∀ {n : Nat} {l r : CTm Head n}, ¬ P.computation.step l r) :
    ConstInstance P (church u₀ v₀ P) toExt where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  typed := by
    intro c D u declared typing hu
    have known : (church u₀ v₀ P).constantType (shift c) = some (D.instConsts toExt) := by
      rw [church_shift, declared, Option.map_some]
    have h := CDerivable.const (Γ := .nil) known typing hu
    rwa [CTm.liftClosed_zero] at h
  steps := fun step => (noSteps step).elim
  requires := fun step _ => (noSteps step).elim

/-- **The extension's derivations come back to the package**: each shifted name to its
constant, and `prop` and `holds` to their definitions. -/
theorem backInstance (levels : LevelModel R L) (hu₀ : R.isUniverse u₀)
    (t₀ : R.headTyping u₀ v₀) : ConstInstance (church u₀ v₀ P) P (back u₀) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  typed := by
    intro c D u declared typing hu
    cases c with
    | str d s =>
        change (P.constantType d).map (CTm.instConsts toExt) = some D at declared
        cases hd : P.constantType d with
        | none =>
            rw [hd] at declared
            cases declared
        | some D₀ =>
            rw [hd, Option.map_some] at declared
            cases declared
            rw [back_toExt] at typing ⊢
            have h := CDerivable.const (Γ := .nil) hd typing hu
            rwa [CTm.liftClosed_zero] at h
    | anonymous => exact typed_back levels hu₀ t₀ declared
    | num p k => exact typed_back levels hu₀ t₀ declared
  steps := fun step => step.elim
  requires := fun step _ => step.elim

end RigidExtension

/-! ## Injectivity and no-confusion of the type formers -/

section FormerFacts

open RigidExtension

variable {R : Rules Head} {P : ChurchRules R} {L : Type} [LevelOrder L]
  (noSteps : ∀ {n : Nat} {l r : CTm Head n}, ¬ P.computation.step l r) (levels : LevelModel R L)
  (read : HeadReading R) (ground : GroundHeadEq R)

include noSteps levels read ground in
/-- **Equal type formers of a package without root steps match in its rigid extension**, at
their renamings. -/
theorem RigidExtension.formersMatch {u₀ v₀ : Head} (hu₀ : R.isUniverse u₀)
    (t₀ : R.headTyping u₀ v₀) {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}
    (equal : CTypeEq P Γ A B) (formed : CCtxFormed P Γ) (former : CFormer A)
    (former' : CFormer B) :
    CFormersMatch (church u₀ v₀ P) (Γ.instConsts toExt) (A.instConsts toExt)
      (B.instConsts toExt) :=
  CTypeEq.formersMatch_of_normal (RigidExtension.levels levels) (valid read levels)
    (groundHeads read levels hu₀ t₀) ground (stuck levels hu₀ t₀) (Q := church u₀ v₀ P)
    (ChurchRulesSub.refl _) (fun _ => constAdequate read _)
    (CTypeEq.instConsts (toExtInstance noSteps) equal)
    (CCtxFormed.instConsts (toExtInstance noSteps) formed)
    former.instConsts (normal_of_former levels hu₀ t₀ former'.instConsts)

include noSteps levels read ground in
/-- **Injectivity and no-confusion of the annotated type formers of a package without root
steps, with a universe**, from the fundamental lemma of the logical relation on the rigid
extension and the round trip of renaming its constants. -/
theorem CFormerFacts.ofNoSteps {u₀ : Head} (hu₀ : R.isUniverse u₀) : CFormerFacts P where
  forms {n Γ A B} equal formed former former' := by
    obtain ⟨v₀, -, t₀, -⟩ := levels.successor hu₀
    have pulled := CFormersMatch.instConsts (backInstance levels hu₀ t₀)
      (RigidExtension.formersMatch noSteps levels read ground hu₀ t₀ equal formed former former')
    rwa [back_toExt_ctx, back_toExt, back_toExt] at pulled

end FormerFacts

/-! ## The lifting -/

section Lifting

variable {R : Rules Head} {P : ChurchRules R} {L : Type} [LevelOrder L]
  (noSteps : ∀ {n : Nat} {l r : Tm Head n}, ¬ R.computation.step l r) (levels : LevelModel R L)
  (algebra : CumulativeAlgebra R) (read : HeadReading R) (ground : GroundHeadEq R)
  {u₀ : Head} (hu₀ : R.isUniverse u₀)
  (sn : ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, Normalization.CtxFormed R Γ →
    Typed R Γ t A → StrongNormalization.SN R t)

include noSteps levels algebra read ground hu₀ sn in
/-- **The facts lifting needs, for a package without root computation whose annotated declared
types are formed as soon as their erasures are**: coherence of annotations from the
injectivity of the type formers and strong normalization; root lifting and root preservation
hold vacuously. -/
theorem LiftingFacts.ofNoSteps (declared : CDeclsFormed P) : LiftingFacts P :=
  LiftingFacts.ofCoherenceFacts
    (CoherenceFacts.ofSN
      (CFormerFacts.ofNoSteps (fun step => noSteps (P.erase_step step)) levels read ground hu₀)
      sn)
    levels algebra (fun step => (noSteps step).elim)
    (fun _ step _ => (noSteps (P.erase_step step)).elim) declared

/-- The annotated declared types of a rigid package erase to declared types without
abstractions, so they are rigid. -/
theorem CDeclsRigid.ofRigid (rigid : R.Rigid) : CDeclsRigid P :=
  rigid_of_lamFree fun declared => rigid.lamFree (P.erase_declared declared)

include levels algebra read ground hu₀ sn in
/-- **The facts lifting needs, for a rigid package.** -/
theorem LiftingFacts.ofRigid (rigid : R.Rigid) : LiftingFacts P :=
  LiftingFacts.ofNoSteps rigid.noSteps levels algebra read ground hu₀ sn
    (CDeclsRigid.formed (CDeclsRigid.ofRigid rigid))

include levels algebra read ground hu₀ sn in
/-- **The Church–Curry correspondence for a rigid package**: every derivation lifts to the
annotation, over every formed annotated context erasing to its context. -/
theorem lifts_ofRigid (rigid : R.Rigid) {statement : Statement Head}
    (derivation : Derivable R statement) : Lifts P statement :=
  lifts levels (LiftingFacts.ofRigid levels algebra read ground hu₀ sn rigid) derivation

end Lifting

/-! ## Pure packages -/

section Pure

variable {R : Rules Head} {L : Type} [LevelOrder L] (pure : R.Pure) (levels : LevelModel R L)
  (algebra : CumulativeAlgebra R) (read : HeadReading R) (ground : GroundHeadEq R)

include pure levels read ground in
/-- **Injectivity and no-confusion of the annotated type formers of a pure package with a
universe**: the case of a package without root steps. -/
theorem CFormerFacts.ofPure {u₀ : Head} (hu₀ : R.isUniverse u₀) :
    CFormerFacts (ChurchRules.ofPure pure) :=
  CFormerFacts.ofNoSteps (fun h => h.elim) levels read ground hu₀

variable {u₀ : Head} (hu₀ : R.isUniverse u₀)
  (sn : ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, Normalization.CtxFormed R Γ →
    Typed R Γ t A → StrongNormalization.SN R t)
include pure levels algebra read ground hu₀ sn

/-- **The facts lifting needs, for a pure package**: the case of a rigid package. -/
theorem LiftingFacts.ofPure : LiftingFacts (ChurchRules.ofPure pure) :=
  LiftingFacts.ofRigid levels algebra read ground hu₀ sn pure.rigid

/-- **The Church–Curry correspondence for a pure package**: every derivation lifts to the
annotation, over every formed annotated context erasing to its context. -/
theorem lifts_ofPure {statement : Statement Head} (derivation : Derivable R statement) :
    Lifts (ChurchRules.ofPure pure) statement :=
  lifts levels (LiftingFacts.ofPure pure levels algebra read ground hu₀ sn) derivation

end Pure

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
