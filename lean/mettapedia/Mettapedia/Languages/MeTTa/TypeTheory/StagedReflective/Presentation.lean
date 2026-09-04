import Mettapedia.Languages.MeTTa.RuntimeSpec
import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.GSLT.LanguageDef.LF.PureCorrespondence
import Mettapedia.GSLT.Dynamics.WeightCost
import Mettapedia.PLN.Evidence.BinEvNat
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem
import Mettapedia.Languages.MeTTa.Prime.Language
import Mettapedia.Languages.MeTTa.Prime.LanguageDef
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing
import Mettapedia.TypeTheory.ModalCwF

/-!
# Deriving the native type theory of the MeTTa family — derivation skeleton

## Purpose

This module sets up the *derivation* of the MeTTa-native type theory from the
observed properties of the MeTTa dialects (Prime, HE, PeTTa, Zero), extending
the structured property collections of `RuntimeSpec`/`DialectProfile`.

The discipline is **derive, don't impose**:

1. each dialect contributes an auditable *bag of observations* about its
   operational behaviour (§1);
2. each observation *forces* a requirement on any candidate type theory (§2);
3. the candidate space is given by an explicit judgmental spine — a contextual
   multimodal CwF with a universe à la Tarski — parameterized by a mode theory
   (§3–§4);
4. satisfaction of each requirement is a *witness structure* carrying a
   nontriviality field, so no requirement can be discharged vacuously (§5–§8);
5. the native theory is a candidate together with one witness per forced
   requirement, plus the parity square that makes its checker an authority
   from birth (§9–§10).

The intended semantic reading is **types as spaces**: a closed type denotes a
space of patterns, membership is matching, subtyping is inclusion (§6).  The
universe is a space of type codes with `el` as decoding — the same
codes-plus-decoding pattern already used by the reflection layer.

## Honesty contract

Every declaration in this file elaborates.  Work not yet proved is either an
uninstantiated structure (the future work is to *build its instance*) or an
entry in `openObligations` (§11), whose count is pinned by a theorem so the
completion state is machine-visible.  The small theorems proved here
(forcing injectivity, coverage, subtyping laws) are genuine but deliberately
modest; no structure defined here is claimed to *be* the completed theory.

The equality architecture and reflective-quotation gate have since been
resolved inside this module.  The selected kernel equality is the intensional
core; stronger observational or cubical relations remain explicitly named
profiles rather than leaking into conversion.  Same-stage quotation carries a
nonzero quotation-depth witness and has distinct positive and negative models.
The obligations that genuinely remain are listed at §11.
-/

namespace Mettapedia.Languages.MeTTa.StagedReflective

universe uNativeClaim uNativeCertificate uNativeProof uRaw uRawTarget

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.GSLT.LanguageDef.KernelAuthority (Checker)
open Mettapedia.TypeTheory

/-! ## §1 Observations: the dialect property bags

Each constructor is a falsifiable statement about a dialect's operational
behaviour.  The bags below are *auditable working requirement profiles*:
correcting them is cheap and changes the forced requirement set mechanically.
They are neither complete dialect specifications nor a selection of Prime's
eventual type theory. -/

/-- Type-theory-forcing observations about a MeTTa-family dialect. -/
inductive Observation where
  /-- Evaluation yields collections of results (superposition). -/
  | collectionResults
  /-- The core operation is pattern matching with metavariables. -/
  | metavariablePatterns
  /-- Programs are data: quotation and evaluation are internal. -/
  | nativeReflection
  /-- Atomspaces are first-class values. -/
  | spacesFirstClass
  /-- Unknown symbols remain uninterpreted; they never signal errors. -/
  | unknownsInert
  /-- Reduction carries cost/resource accounting. -/
  | costAccounted
  /-- Claims may carry graded evidence (world-model layer). -/
  | evidenceAnnotated
  /-- Interpreter levels are distinguished (staged tower). -/
  | stagedTower
  deriving DecidableEq, Repr

/-- A dialect's observation bag.  `observed` is deliberately a bare list:
multiplicity is irrelevant, order is not load-bearing, and membership is the
only operation used downstream. -/
structure ObservationBag where
  dialectName : String
  observed : List Observation
  deriving Repr

/-- Current exploratory Prime requirement profile.  Its eight observations
are inputs to the candidate derivation, not a claim that Prime is fixed or
exhaustively specified here. -/
def primeBag : ObservationBag where
  dialectName := "prime"
  observed :=
    [.collectionResults, .metavariablePatterns, .nativeReflection,
     .spacesFirstClass, .unknownsInert, .costAccounted,
     .evidenceAnnotated, .stagedTower]

/-- Current HE requirements used by the shared native-typing candidate. -/
def heBag : ObservationBag where
  dialectName := "he"
  observed :=
    [.collectionResults, .metavariablePatterns, .nativeReflection,
     .spacesFirstClass, .unknownsInert]

/-- Current PeTTa requirements used by this shared typing candidate.  Equality
with the HE list records only this selected fragment; it does not identify the
two dialects or their complete observable interfaces. -/
def pettaBag : ObservationBag where
  dialectName := "petta"
  observed :=
    [.collectionResults, .metavariablePatterns, .nativeReflection,
     .spacesFirstClass, .unknownsInert]

/-- Zero: the minimal work-closure fragment — collections, metavariables,
inert unknowns. -/
def zeroBag : ObservationBag where
  dialectName := "zero"
  observed := [.collectionResults, .metavariablePatterns, .unknownsInert]

/-- Working family profiles under comparison.  Membership here does not make
one profile a specification or one candidate theory authoritative. -/
def familyBags : List ObservationBag := [primeBag, heBag, pettaBag, zeroBag]

/-! ## §2 Requirements and the forcing map -/

/-- Requirements on a candidate type theory.  Each is discharged only by the
corresponding witness structure of §5–§8, never by a bare flag. -/
inductive Requirement where
  /-- Semantic types classify collections (types-as-spaces). -/
  | typesAsCollections
  /-- Open terms are typed relative to contexts; metavariables first-class. -/
  | contextualJudgment
  /-- An internal code/quotation modality. -/
  | quotationModality
  /-- Types for spaces as values (the universe supports space codes). -/
  | spaceTypes
  /-- A interface mode that never rejects unknown-only programs. -/
  | successInterface
  /-- Cost grading in the mode theory. -/
  | gradedModality
  /-- Evidence decorations fibred over the kernel, never inside it. -/
  | evidenceFibration
  /-- Staging levels in the mode theory. -/
  | levelModalities
  /-- Genuinely dependent type families (full DTT/MTT-tier reasoning). -/
  | dependentFamilies
  /-- Propositional identity with a reflexivity witness. -/
  | identityTypes
  /-- Language presentations as first-class typed values. -/
  | languageCodes
  /-- Native proof objects remain first-class and proof relevant. -/
  | nativeProofObjects
  /-- Universes and meta-authorities are strictly level stratified. -/
  | stratifiedMetalogic
  /-- Production typing computes directly on Pattern claims and carries no
  certificate language through the interior fast path. -/
  | directTypingPath
  deriving DecidableEq, Repr

/-- Each observation forces exactly one requirement. -/
def forces : Observation → Requirement
  | .collectionResults => .typesAsCollections
  | .metavariablePatterns => .contextualJudgment
  | .nativeReflection => .quotationModality
  | .spacesFirstClass => .spaceTypes
  | .unknownsInert => .successInterface
  | .costAccounted => .gradedModality
  | .evidenceAnnotated => .evidenceFibration
  | .stagedTower => .levelModalities

/-- Distinct observations force distinct requirements: no requirement is an
artifact of conflating two observations. -/
theorem forces_injective : Function.Injective forces := by
  intro a b h
  cases a <;> cases b <;> simp_all [forces]

/-- The requirements a bag forces. -/
def ObservationBag.requirements (bag : ObservationBag) : List Requirement :=
  bag.observed.map forces

/-- The current Prime observation bag forces the full *observed* requirement
set, in order.  The normative commitments below are deliberately separate. -/
theorem prime_forces_all :
    primeBag.requirements =
      [.typesAsCollections, .contextualJudgment, .quotationModality,
       .spaceTypes, .successInterface, .gradedModality,
       .evidenceFibration, .levelModalities] := rfl

/-- Zero's requirements are among Prime's: the minimal dialect forces a
subfamily, so one spine can serve the whole family. -/
theorem zero_requirements_subset_prime :
    ∀ r ∈ zeroBag.requirements, r ∈ primeBag.requirements := by decide

/-! ### Target commitments: the normative channel

Observations describe the dialects as they run today.  Commitments *grant*
capacities the family is being extended toward — they are declared, never
observed, and the two channels are kept apart so an imposed requirement can
never masquerade as a derived one.  `commitments_extend_observations` is the
machine-checked form of that separation: no current observation forces any
committed requirement, so these are genuine extensions of the family, and
the dialect that realizes them (Prime) is expected to *change* to meet them
rather than the theory shrinking to fit the dialects. -/

/-- Capacities granted to the family beyond current observed behaviour. -/
inductive TargetCommitment where
  /-- Full dependent-family reasoning (DTT/MTT tier). -/
  | dttReasoning
  /-- Propositional identity and its elimination. -/
  | identityReasoning
  /-- Native, typed manipulation of language presentations
  (the intermediate-language capacity). -/
  | languageManipulation
  /-- Proof objects are native data closed under admitted operations. -/
  | proofObjectProgramming
  /-- A non-self-certifying tower of universes and meta-authorities. -/
  | stratifiedBootstrap
  /-- The native typing authority is a direct decision kernel over MeTTa
  Patterns; proof-carrying replay remains an optional boundary mode. -/
  | directTypingPath
  deriving DecidableEq, Repr

/-- Each commitment forces exactly one requirement. -/
def commitmentForces : TargetCommitment → Requirement
  | .dttReasoning => .dependentFamilies
  | .identityReasoning => .identityTypes
  | .languageManipulation => .languageCodes
  | .proofObjectProgramming => .nativeProofObjects
  | .stratifiedBootstrap => .stratifiedMetalogic
  | .directTypingPath => .directTypingPath

theorem commitmentForces_injective : Function.Injective commitmentForces := by
  intro a b h
  cases a <;> cases b <;> simp_all [commitmentForces]

/-- The capacities being granted to Prime. -/
def primeCommitments : List TargetCommitment :=
  [.dttReasoning, .identityReasoning, .languageManipulation,
   .proofObjectProgramming, .stratifiedBootstrap, .directTypingPath]

/-- Committed requirements are NOT forced by any current observation: the
normative channel genuinely extends the descriptive one. -/
theorem commitments_extend_observations :
    ∀ c : TargetCommitment,
      commitmentForces c ∉ primeBag.requirements := by
  intro c
  cases c <;> decide

/-! ## §3–§4 General modal CwF interface

The reusable mode theory, cost grading, contextual multimodal CwF laws,
dependent-product structure, and term-level quotation interface live in
`Mettapedia.TypeTheory.ModalCwF`.  This module supplies MeTTa-family models
and derived requirements without making those general definitions language-specific. -/

/-! ## §5 Types as spaces: the semantic layer -/

/-- A semantic space of patterns: the extensional reading of a type.  The
intended refinement chain runs space → atomspace value → indexed store; this
extensional layer is where the subtyping lattice lives. -/
def Space : Type := Pattern → Prop

namespace Space

/-- Membership is matching (extensional reading). -/
def Mem (p : Pattern) (S : Space) : Prop := S p

/-- Subtyping is inclusion of spaces. -/
def Sub (S T : Space) : Prop := ∀ p, S p → T p

/-- The unknown/dynamic type: the whole space of patterns.  This is the
semantic reading of the gradual `?`. -/
def top : Space := fun _ => True

/-- Meet of spaces. -/
def inter (S T : Space) : Space := fun p => S p ∧ T p

/-- Join of spaces. -/
def union (S T : Space) : Space := fun p => S p ∨ T p

theorem sub_refl (S : Space) : Sub S S := fun _ h => h

theorem sub_trans {S T U : Space} (h₁ : Sub S T) (h₂ : Sub T U) : Sub S U :=
  fun p hp => h₂ p (h₁ p hp)

theorem sub_top (S : Space) : Sub S top := fun _ _ => trivial

theorem inter_sub_left (S T : Space) : Sub (inter S T) S :=
  fun _ h => h.1

theorem inter_sub_right (S T : Space) : Sub (inter S T) T :=
  fun _ h => h.2

theorem sub_union_left (S T : Space) : Sub S (union S T) :=
  fun _ h => Or.inl h

theorem sub_union_right (S T : Space) : Sub T (union S T) :=
  fun _ h => Or.inr h

end Space

/-! ## §5a A noncollapsed families model

The first semantic point is the ordinary families CwF.  Contexts are small
types, substitutions are functions, types are indexed small types, and terms
are dependent sections.  Its Tarski universe contains codes in `Type 0` and
decodes them one universe lower than the ambient CwF.  Stages are natural
numbers and a modality may only point from a higher stage to a lower one.

This model is intentionally semantic rather than a second syntax.  It gives
the native presentation a nondegenerate target in which dependent products
are actual dependent functions.  The later rule-algebra initiality theorem
does not identify this semantic CwF with the authored syntax; the stronger
CwF-level comparison remains an explicit obligation. -/

/-- A stage morphism retains both its nonascending level law and the number of
reflective quotation layers it introduces.  The latter supplies genuine
same-stage endomorphisms without weakening the staging order. -/
structure StageHom (high low : Nat) where
  descent : low ≤ high
  quoteDepth : Nat

/-- Natural-number stages with nonascending, quotation-graded morphisms. -/
def stageModeTheory : ModeTheory where
  Mode := Nat
  Hom := StageHom
  id := fun level => ⟨Nat.le_refl level, 0⟩
  comp := fun earlier later =>
    ⟨Nat.le_trans later.descent earlier.descent,
      earlier.quoteDepth + later.quoteDepth⟩
  id_comp := by
    intro a b morphism
    cases morphism
    simp
  comp_id := by
    intro a b morphism
    cases morphism
    simp
  comp_assoc := by
    intro a b c d first second third
    cases first
    cases second
    cases third
    simp [Nat.add_assoc]

/-- Expose the natural-number carrier without relying on reducibility during
typeclass search. -/
def stageOfNat (level : Nat) : stageModeTheory.Mode := by
  change Nat
  exact level

theorem stageOfNat_injective : Function.Injective stageOfNat := by
  intro left right equal
  simpa [stageOfNat, stageModeTheory] using equal

def stageIndex (level : stageModeTheory.Mode) : Nat := by
  change Nat at level
  exact level

@[simp] theorem stageIndex_stageOfNat (level : Nat) :
    stageIndex (stageOfNat level) = level :=
  rfl

/-- The live cost-rho carrier: two natural resource coordinates. -/
abbrev NativeCostAccount :=
  Mettapedia.GSLT.VectorialAccount Nat 2

def nativeCostZero : NativeCostAccount := fun _ => 0

def nativeCostAdd (left right : NativeCostAccount) : NativeCostAccount :=
  fun coordinate => left coordinate + right coordinate

/-- Spend `high-low` units in the first cost coordinate when descending a
stage; the second coordinate is reserved for an independent resource. -/
def stageRouteCost {high low : stageModeTheory.Mode}
    (_route : stageModeTheory.Hom high low) : NativeCostAccount :=
  fun coordinate =>
    if coordinate = 0 then stageIndex high - stageIndex low else 0

/-- Cost-rho's vectorial account grades the stage category. -/
def nativeCostGrading : CostGrading stageModeTheory where
  Grade := NativeCostAccount
  unit := nativeCostZero
  add := nativeCostAdd
  add_assoc := by intros; funext coordinate; simp [nativeCostAdd, Nat.add_assoc]
  unit_add := by intros; funext coordinate; simp [nativeCostZero, nativeCostAdd]
  add_unit := by intros; funext coordinate; simp [nativeCostZero, nativeCostAdd]
  gradeOf := stageRouteCost
  gradeOf_id := by
    intro mode
    funext coordinate
    by_cases firstCoordinate : coordinate = 0
    · simp [stageRouteCost, nativeCostZero, firstCoordinate]
    · simp [stageRouteCost, nativeCostZero, firstCoordinate]
  gradeOf_comp := by
    intro high middle low earlier later
    funext coordinate
    have earlierLe : stageIndex middle ≤ stageIndex high := by
      exact earlier.descent
    have laterLe : stageIndex low ≤ stageIndex middle := by
      exact later.descent
    by_cases firstCoordinate : coordinate = 0
    · subst coordinate
      simp only [stageRouteCost, if_pos, nativeCostAdd]
      omega
    · simp [stageRouteCost, nativeCostAdd, firstCoordinate]

/-- Small codes used by the first Tarski universe.  The pattern code is the
first point where the universe names the runtime's actual pattern carrier. -/
inductive FamiliesCode where
  | empty
  | unit
  | pattern
  /-- Universe-free dependent λΠ syntax, with its executable βη kernel. -/
  | lambdaPiExpr
  /-- Full validated five-field language presentations as intrinsic values. -/
  | validatedLanguage
  deriving DecidableEq, Repr

/-- Decoding for the first Tarski universe. -/
def FamiliesCode.decode : FamiliesCode → Type
  | .empty => Empty
  | .unit => PUnit
  | .pattern => Pattern
  | .lambdaPiExpr => Mettapedia.GSLT.LanguageDef.Pure.Expr
  | .validatedLanguage => Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef

private def familiesLock {high low : stageModeTheory.Mode}
    (_ : stageModeTheory.Hom high low) (Γ : Type) : Type :=
  Γ

/-- One reflective code layer.  The distinguished `none` is the code token;
`some value` retains an already available inhabitant. -/
abbrev ReflectiveCodeLayer (A : Type) := Option A

/-- Iterated reflective code layers, graded by a mode morphism. -/
def reflectiveCodeIter : Nat → Type → Type
  | 0, A => A
  | depth + 1, A => ReflectiveCodeLayer (reflectiveCodeIter depth A)

theorem reflectiveCodeIter_add (earlier later : Nat) (A : Type) :
    reflectiveCodeIter (earlier + later) A =
      reflectiveCodeIter later (reflectiveCodeIter earlier A) := by
  induction later with
  | zero => simp [reflectiveCodeIter]
  | succ later inductionHypothesis =>
      change ReflectiveCodeLayer (reflectiveCodeIter (earlier + later) A) =
        ReflectiveCodeLayer (reflectiveCodeIter later (reflectiveCodeIter earlier A))
      exact congrArg ReflectiveCodeLayer inductionHypothesis

private def familiesBoxTy {high low : stageModeTheory.Mode}
    (modality : stageModeTheory.Hom high low) {Γ : Type}
    (A : familiesLock modality Γ → Type) : Γ → Type :=
  fun value => reflectiveCodeIter modality.quoteDepth (A value)

private def familiesLockSub {high low : stageModeTheory.Mode}
    (_ : stageModeTheory.Hom high low) {Γ Δ : Type}
    (substitution : Γ → Δ) : Γ → Δ :=
  substitution

/-- The standard families CwF, repeated at every stage.  Locking preserves the
underlying context while `boxTy` applies the quotation depth carried by the
mode morphism.  Depth zero is the identity and positive depth introduces
iterated reflective code layers. -/
def familiesCwF : ModalCwF stageModeTheory where
  Con := fun _ => Type
  Sub := fun Γ Δ => Γ → Δ
  sid := fun _ value => value
  scomp := fun substitution later value => later (substitution value)
  Ty := fun Γ => Γ → Type
  Tm := fun Γ A => (value : Γ) → A value
  tySub := fun A substitution value => A (substitution value)
  tmSub := fun term substitution value => term (substitution value)
  tySub_id := by intros; rfl
  tySub_comp := by intros; rfl
  empty := fun _ => PUnit
  ext := fun Γ A => Sigma A
  wk := fun _ value => value.1
  vz := fun _ value => value.2
  sext := fun substitution term value => ⟨substitution value, term value⟩
  pi := fun A B value => (argument : A value) → B ⟨value, argument⟩
  univ := fun _ _ => FamiliesCode
  el := fun code value => (code value).decode
  lock := familiesLock
  boxTy := familiesBoxTy

namespace FamiliesCwF

/-- Lambda introduction for the semantic dependent-function fragment. -/
def lam {mode : stageModeTheory.Mode} {Γ : familiesCwF.Con mode}
    {A : familiesCwF.Ty Γ} {B : familiesCwF.Ty (familiesCwF.ext Γ A)}
    (body : familiesCwF.Tm (familiesCwF.ext Γ A) B) :
    familiesCwF.Tm Γ (familiesCwF.pi A B) :=
  fun value argument => body ⟨value, argument⟩

/-- Application for the semantic dependent-function fragment. -/
def app {mode : stageModeTheory.Mode} {Γ : familiesCwF.Con mode}
    {A : familiesCwF.Ty Γ} {B : familiesCwF.Ty (familiesCwF.ext Γ A)}
    (function : familiesCwF.Tm Γ (familiesCwF.pi A B))
    (argument : familiesCwF.Tm Γ A) :
    familiesCwF.Tm Γ
      (familiesCwF.tySub B
        (familiesCwF.sext (familiesCwF.sid Γ) argument)) :=
  fun value => function value (argument value)

/-- The semantic Π-fragment computes by beta reduction. -/
theorem app_lam {mode : stageModeTheory.Mode} {Γ : familiesCwF.Con mode}
    {A : familiesCwF.Ty Γ} {B : familiesCwF.Ty (familiesCwF.ext Γ A)}
    (body : familiesCwF.Tm (familiesCwF.ext Γ A) B)
    (argument : familiesCwF.Tm Γ A) :
    app (lam body) argument =
      familiesCwF.tmSub body
        (familiesCwF.sext (familiesCwF.sid Γ) argument) :=
  rfl

/-- The semantic Π-fragment is eta-complete extensionally. -/
theorem lam_app {mode : stageModeTheory.Mode} {Γ : familiesCwF.Con mode}
    {A : familiesCwF.Ty Γ} {B : familiesCwF.Ty (familiesCwF.ext Γ A)}
    (function : familiesCwF.Tm Γ (familiesCwF.pi A B)) :
    lam (fun value => function value.1 value.2) = function := by
  funext value argument
  rfl

end FamiliesCwF

/-- The families Π operations satisfy the generic dependent-product laws. -/
def familiesPiStructure : PiStructure stageModeTheory familiesCwF where
  lam := FamiliesCwF.lam
  app := FamiliesCwF.app
  beta := FamiliesCwF.app_lam
  pi_sub := by intros; rfl
  extensional := by
    intro mode Γ A B left right pointwise
    funext value argument
    have applied := pointwise
      (Δ := Sigma A) (familiesCwF.wk A) (familiesCwF.vz A)
    have appliedEquality := eq_of_heq applied
    exact congrFun appliedEquality ⟨value, argument⟩

/-- Every CwF and modal equation required by `ModalCwFLaws` holds in the
families model. -/
def familiesCwFLaws : ModalCwFLaws stageModeTheory familiesCwF where
  scomp_sid_left := by intros; rfl
  scomp_sid_right := by intros; rfl
  scomp_assoc := by intros; rfl
  tmSub_id := by intros; exact HEq.rfl
  tmSub_comp := by intros; exact HEq.rfl
  wk_sext := by intros; rfl
  vz_sext := by intros; exact HEq.rfl
  sext_eta := by
    intro mode Γ A
    funext value
    rcases value with ⟨base, fibre⟩
    rfl
  piLaws := familiesPiStructure
  lockSub := familiesLockSub
  lockSub_sid := by intros; rfl
  lockSub_comp := by intros; rfl
  boxTy_natural := by intros; rfl
  lock_id := by intros; rfl
  lock_comp := by intros; rfl
  lockSub_id := by intros; exact HEq.rfl
  lockSub_modal_comp := by intros; exact HEq.rfl
  boxTy_id := by intros; exact HEq.rfl
  boxTy_comp := by
    intro first middle last earlier later Γ direct nested equalTypes
    have sameTypes : direct = nested := eq_of_heq equalTypes
    subst nested
    apply heq_of_eq
    funext value
    exact reflectiveCodeIter_add earlier.quoteDepth later.quoteDepth
      (direct value)

/-- The families model has terminal empty contexts, natural comprehension,
and a substitution-stable Tarski universe. -/
def familiesCwFCoherence :
    ModalCwFCoherence stageModeTheory familiesCwF familiesCwFLaws where
  empty_sub_unique := by
    intro mode context left right
    funext value
    cases left value
    cases right value
    rfl
  sext_natural := by intros; rfl
  univ_natural := by intros; rfl
  el_natural := by intros; rfl

/-- General comprehension eta is available in the concrete semantic model,
not merely the identity-instance eta stored in the basic law package. -/
theorem familiesCwF_sext_unique
    {mode : stageModeTheory.Mode} {source target : familiesCwF.Con mode}
    (type : familiesCwF.Ty target)
    (substitution : familiesCwF.Sub source (familiesCwF.ext target type)) :
    substitution =
      familiesCwF.sext
        (familiesCwF.scomp substitution (familiesCwF.wk type))
        (familiesCwF.castTm
          (familiesCwF.tySub_comp type substitution
            (familiesCwF.wk type)).symm
          (familiesCwF.tmSub (familiesCwF.vz type) substitution)) :=
  familiesCwFCoherence.sext_unique type substitution

/-! ### The basic equations do not force terminality -/

/-- Changing only the designated empty context leaves every basic CwF law
intact, demonstrating that terminality is genuinely additional coherence. -/
def nonterminalFamiliesCwF : ModalCwF stageModeTheory :=
  familiesCwF.replaceEmpty (fun _ => Bool)

/-- The basic equations never inspect the designated empty context. -/
def nonterminalFamiliesCwFLaws :
    ModalCwFLaws stageModeTheory nonterminalFamiliesCwF :=
  familiesCwFLaws.replaceEmpty (fun _ => Bool)

private def nonterminalEmptyFalse :
    nonterminalFamiliesCwF.Sub PUnit
      (nonterminalFamiliesCwF.empty (stageOfNat 0)) :=
  fun _ => false

private def nonterminalEmptyTrue :
    nonterminalFamiliesCwF.Sub PUnit
      (nonterminalFamiliesCwF.empty (stageOfNat 0)) :=
  fun _ => true

theorem nonterminal_empty_substitutions_distinct :
    nonterminalEmptyFalse ≠ nonterminalEmptyTrue := by
  intro equality
  have pointwise := congrFun equality PUnit.unit
  cases pointwise

/-- Negative control: a law-complete operational CwF need not have the
semantic coherence package. -/
theorem basic_modal_cwf_laws_do_not_force_coherence :
    ¬ Nonempty
      (ModalCwFCoherence stageModeTheory nonterminalFamiliesCwF
        nonterminalFamiliesCwFLaws) := by
  rintro ⟨coherence⟩
  exact nonterminal_empty_substitutions_distinct
    (coherence.empty_sub_unique nonterminalEmptyFalse nonterminalEmptyTrue)

namespace FamiliesCwF

/-- Canonical introduction into an iterated reflective-code layer.  Positive
quotation depth uses the distinguished code token; depth zero retains the
original term. -/
def quoteIter : (depth : Nat) → {A : Type} → A → reflectiveCodeIter depth A
  | 0, _, value => value
  | _ + 1, _, _ => none

end FamiliesCwF

/-- The families model interprets authored quotation by introducing the
canonical code token at positive quote depth and acting as identity at depth
zero. -/
def familiesQuotationTerms :
    QuotationTermStructure stageModeTheory familiesCwF familiesCwFLaws where
  quoteTm := fun {high} {low} modality {Γ} {A} term value =>
    FamiliesCwF.quoteIter modality.quoteDepth (term value)
  quote_sub := by intros; exact HEq.rfl
  quote_id := by intros; exact HEq.rfl

/-! ### Quotation is not determined by the bare modal CwF

The current families CwF admits more than one substitution-stable quotation
introduction.  This concrete separation is the term-level analogue of the
operational non-factorization results elsewhere in the library: modal context
and type transport alone do not reconstruct an authored quotation rule. -/

/-- An alternative quotation algebra that injects an inhabited term through
every reflective layer instead of returning the canonical token. -/
def FamiliesCwF.quoteIterSome : (depth : Nat) → {A : Type} → A →
    reflectiveCodeIter depth A
  | 0, _, value => value
  | depth + 1, _, value => some (FamiliesCwF.quoteIterSome depth value)

/-- The alternative families quotation is equally stable under substitution
and the identity modality. -/
def familiesQuotationTermsSome :
    QuotationTermStructure stageModeTheory familiesCwF familiesCwFLaws where
  quoteTm := fun {high} {low} modality {Γ} {A} term value =>
    FamiliesCwF.quoteIterSome modality.quoteDepth (term value)
  quote_sub := by intros; exact HEq.rfl
  quote_id := by intros; exact HEq.rfl

/-- Positive witness: the canonical quotation of the unique unit term at one
reflective layer is the distinguished token. -/
theorem familiesQuotationTerms_unit_depth_one :
    familiesQuotationTerms.quoteTm
        (⟨Nat.le_refl 0, 1⟩ : StageHom 0 0)
        (fun _ : PUnit => PUnit.unit) PUnit.unit = none :=
  rfl

/-- Negative witness: the enriched quotation operation is not derivable from
the common mode theory, CwF, and modal laws.  Two valid enrichments of those
same data disagree on a closed unit term. -/
theorem bare_modal_cwf_does_not_determine_quotation :
    familiesQuotationTerms.quoteTm
        (⟨Nat.le_refl 0, 1⟩ : StageHom 0 0)
        (fun _ : PUnit => PUnit.unit) PUnit.unit ≠
      familiesQuotationTermsSome.quoteTm
        (⟨Nat.le_refl 0, 1⟩ : StageHom 0 0)
        (fun _ : PUnit => PUnit.unit) PUnit.unit := by
  intro equal
  change (none : Option PUnit) = some PUnit.unit at equal
  cases equal

/-! ## §6 Requirement witnesses

Each witness structure carries at least one nontriviality field, so the
corresponding requirement cannot be satisfied by a degenerate instance. -/

/-- Witness for `typesAsCollections` and the semantic half of `spaceTypes`:
closed types of a designated base mode denote spaces, nondegenerately. -/
structure SpaceModel (M : ModeTheory) (C : ModalCwF M) where
  baseMode : M.Mode
  interp : C.Ty (C.empty baseMode) → Space
  /-- Blocks the collapsed model: at least two closed types denote
  distinct spaces. -/
  nondegenerate :
    ∃ A B : C.Ty (C.empty baseMode), interp A ≠ interp B

/-- Witness for `spaceTypes`: the universe reflects spaces — there is a
closed code whose decoding is a designated nontrivial space. -/
structure SpaceCodeWitness (M : ModeTheory) (C : ModalCwF M)
    (model : SpaceModel M C) where
  spaceCode : C.Tm (C.empty model.baseMode) (C.univ (C.empty model.baseMode))
  decodesToProperSpace :
    model.interp (C.el spaceCode) ≠ Space.top

/-- Witness for `quotationModality`: a designated same-mode modality types
reflection, and its box action is semantically nondegenerate. -/
structure QuotationWitness (M : ModeTheory) (C : ModalCwF M) where
  baseMode : M.Mode
  codeMode : M.Mode
  quote : M.Hom baseMode codeMode
  sameMode : baseMode = codeMode
  nondegenerate :
    ∃ (Γ : C.Con codeMode) (A : C.Ty (C.lock quote Γ)),
      Nonempty (C.Tm Γ (C.boxTy quote A)) ∧
        IsEmpty (C.Tm (C.lock quote Γ) A)

/-- Same-stage quotation at level zero introduces one genuine reflective code
layer while respecting the nonascending stage discipline. -/
def familiesQuotationWitness :
    QuotationWitness stageModeTheory familiesCwF where
  baseMode := stageOfNat 0
  codeMode := stageOfNat 0
  quote := ⟨Nat.le_refl 0, 1⟩
  sameMode := rfl
  nondegenerate := by
    refine ⟨PUnit, (fun _ => Empty), ?_, ?_⟩
    · exact ⟨fun _ => none⟩
    · exact ⟨fun impossible => Empty.elim (impossible PUnit.unit)⟩

/-- Positive witness: the quotation layer has a canonical code token even
when the quoted object type has no inhabitants. -/
theorem familiesQuotation_code_inhabited :
    Nonempty
      (familiesCwF.Tm PUnit
        (familiesCwF.boxTy familiesQuotationWitness.quote
          (fun _ => Empty))) :=
  ⟨fun _ => none⟩

/-- Negative witness: the underlying empty object fibre remains empty. -/
theorem familiesQuotation_object_empty :
    IsEmpty
      (familiesCwF.Tm
        (familiesCwF.lock familiesQuotationWitness.quote PUnit)
        (fun _ => Empty)) :=
  ⟨fun impossible => Empty.elim (impossible PUnit.unit)⟩

/-- Witness for `levelModalities`: modes carry interpreter levels, homs never
ascend (an evaluator may only interpret strictly lower code), and the tower
is genuinely inhabited at two levels. -/
structure LevelWitness (M : ModeTheory) where
  level : M.Mode → Nat
  descending : ∀ {a b : M.Mode}, M.Hom a b → level b ≤ level a
  lo : M.Mode
  hi : M.Mode
  lo_lt_hi : level lo < level hi

/-- The live natural-number stage category has a genuine two-level fragment,
and every stage morphism respects its order. -/
def stageLevelWitness : LevelWitness stageModeTheory where
  level := stageIndex
  descending := fun route => route.descent
  lo := stageOfNat 0
  hi := stageOfNat 1
  lo_lt_hi := by
    simp [stageIndex_stageOfNat]

/-- Witness for `gradedModality`: a cost grading whose grades are not all
trivial on some actual modality. -/
structure GradingWitness (M : ModeTheory) where
  grading : CostGrading M
  a : M.Mode
  b : M.Mode
  f : M.Hom a b
  nontrivial : grading.gradeOf f ≠ grading.unit

/-- One genuine stage descent has nonzero cost in the live cost-rho account. -/
def nativeGradingWitness : GradingWitness stageModeTheory where
  grading := nativeCostGrading
  a := stageOfNat 1
  b := stageOfNat 0
  f := ⟨by simp [stageOfNat], 0⟩
  nontrivial := by
    intro zeroCost
    have firstCoordinate := congrFun zeroCost (0 : Fin 2)
    simp [nativeCostGrading, stageRouteCost, stageOfNat, stageIndex,
      nativeCostZero] at firstCoordinate

/-- Witness for `evidenceFibration`: evidence decorations attach to terms
from *outside* the kernel — a commutative evidence monoid and a measure on
terms.  The kernel types and terms are untouched; the intended instance
takes evidence from the world-model layer's evidence carrier.  Transport
laws under substitution are a listed obligation. -/
structure EvidenceFibration (M : ModeTheory) (C : ModalCwF M) where
  Ev : Type
  zero : Ev
  add : Ev → Ev → Ev
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  /-- Evidence is retained in a fibre over a kernel term, not computed from
  or inserted into that term. -/
  Decoration : {m : M.Mode} → {Γ : C.Con m} → {A : C.Ty Γ} →
    C.Tm Γ A → Type
  evidence : {m : M.Mode} → {Γ : C.Con m} → {A : C.Ty Γ} →
    {term : C.Tm Γ A} → Decoration term → Ev
  reindex : {m : M.Mode} → {Γ Δ : C.Con m} → {A : C.Ty Δ} →
    {term : C.Tm Δ A} → Decoration term → (σ : C.Sub Γ Δ) →
    Decoration (C.tmSub term σ)
  reindex_evidence : ∀ {m : M.Mode} {Γ Δ : C.Con m} {A : C.Ty Δ}
    {term : C.Tm Δ A} (decoration : Decoration term) (σ : C.Sub Γ Δ),
    evidence (reindex decoration σ) = evidence decoration
  reindex_id : ∀ {m : M.Mode} {Γ : C.Con m} {A : C.Ty Γ}
    {term : C.Tm Γ A} (decoration : Decoration term),
    HEq (reindex decoration (C.sid Γ)) decoration
  reindex_comp : ∀ {m : M.Mode} {Γ Δ Ε : C.Con m} {A : C.Ty Ε}
    {term : C.Tm Ε A} (decoration : Decoration term)
    (σ : C.Sub Γ Δ) (τ : C.Sub Δ Ε),
    HEq (reindex decoration (C.scomp σ τ))
      (reindex (reindex decoration τ) σ)
  /-- Blocks the collapsed decoration: the same kernel term admits two
  retained evidence values. -/
  nondegenerate :
    ∃ (m : M.Mode) (Γ : C.Con m) (A : C.Ty Γ) (term : C.Tm Γ A)
      (left right : Decoration term), evidence left ≠ evidence right

/-- The load-bearing finite PLN evidence carrier. -/
abbrev NativeEvidence := Mettapedia.PLN.Evidence.BinEvNat

/-- PLN evidence is a constant external fibre over each typed kernel term.
Reindexing changes the term/context but retains the evidence exactly. -/
def nativeEvidenceFibration : EvidenceFibration stageModeTheory familiesCwF where
  Ev := NativeEvidence
  zero := 0
  add := (· + ·)
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := zero_add
  Decoration := fun _ => NativeEvidence
  evidence := fun decoration => decoration
  reindex := fun decoration _ => decoration
  reindex_evidence := by intros; rfl
  reindex_id := by intros; exact HEq.rfl
  reindex_comp := by intros; exact HEq.rfl
  nondegenerate := by
    refine ⟨stageOfNat 0, PUnit, (fun _ => PUnit),
      (fun _ => PUnit.unit), ⟨1, 0⟩, ⟨0, 1⟩, ?_⟩
    intro equalEvidence
    have positiveCoordinates := congrArg
      Mettapedia.PLN.Evidence.BinEvNat.pos equalEvidence
    change (1 : Nat) = 0 at positiveCoordinates
    omega

/-- The zero and one-positive decorations remain different after every
substitution; reindexing never erases retained evidence. -/
theorem nativeEvidence_reindex_separates
    {mode : stageModeTheory.Mode} {Γ Δ : familiesCwF.Con mode}
    {A : familiesCwF.Ty Δ} {term : familiesCwF.Tm Δ A}
    (σ : familiesCwF.Sub Γ Δ) :
    nativeEvidenceFibration.reindex
        (term := term) (⟨0, 0⟩ : NativeEvidence) σ ≠
      nativeEvidenceFibration.reindex
        (term := term) (⟨1, 0⟩ : NativeEvidence) σ := by
  intro equalEvidence
  have positiveCoordinates := congrArg
    Mettapedia.PLN.Evidence.BinEvNat.pos equalEvidence
  change (0 : Nat) = 1 at positiveCoordinates
  omega

/-- Witness for `successInterface`: a direct executable judgment for a live
guest whose unknown-only fragment is accepted.  This is a typing-facing
interface, so no certificate type occurs in it.  `rejects` rules out the
degenerate always-accepting decision: success typing preserves unknowns, but
it does not abandon all static discrimination. -/
structure SuccessInterface (Claim : Type) where
  decide : Claim → Bool
  Judges : Claim → Prop
  sound : ∀ claim, decide claim = true → Judges claim
  UnknownOnly : Claim → Prop
  witness : ∃ c, UnknownOnly c
  never_rejects : ∀ c, UnknownOnly c → decide c = true
  rejects : ∃ c, decide c = false

/-! ### Live HE and PeTTa success interfaces

These instances expose the pass-through fragments of the two executable
language specifications.  They are intentionally smaller than complete
typing algorithms: the requirement forced by `unknownsInert` is precisely
that an unknown term has a valid operational continuation.  Soundness lands
in each dialect's own evaluation relation, while a concrete non-pass-through
claim is rejected. -/

/-- The HE pass-through checker only needs the subject and expected type;
space, grounded dispatch, and bindings are universally quantified in its
native judgment. -/
structure HESuccessClaim where
  atom : Mettapedia.Languages.MeTTa.OSLFCore.Atom
  expected : Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-- The exact guard of HE's `EvalAtom.type_pass` constructor. -/
def hePasses (claim : HESuccessClaim) : Prop :=
  Mettapedia.Languages.MeTTa.HE.isEmptyOrError claim.atom = false ∧
    (claim.expected = Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType ∨
      claim.expected = Mettapedia.Languages.MeTTa.HE.getMetaType claim.atom ∨
      Mettapedia.Languages.MeTTa.HE.getMetaType claim.atom =
        Mettapedia.Languages.MeTTa.OSLFCore.Atom.variableType)

/-- Boolean presentation of the HE pass-through guard. -/
def hePassesBool (claim : HESuccessClaim) : Bool :=
  (Mettapedia.Languages.MeTTa.HE.isEmptyOrError claim.atom == false) &&
    ((claim.expected == Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType) ||
      (claim.expected == Mettapedia.Languages.MeTTa.HE.getMetaType claim.atom) ||
      (Mettapedia.Languages.MeTTa.HE.getMetaType claim.atom ==
        Mettapedia.Languages.MeTTa.OSLFCore.Atom.variableType))

theorem hePassesBool_eq_true (claim : HESuccessClaim) :
    hePassesBool claim = true ↔ hePasses claim := by
  simp [hePassesBool, hePasses, Bool.or_eq_true]
  tauto

/-- HE's direct executable success-fragment decision. -/
def heSuccessDecide : HESuccessClaim → Bool :=
  hePassesBool

/-- The native HE judgment selected by the success interface. -/
def HEPassesJudgment (claim : HESuccessClaim) : Prop :=
  ∀ (space : Mettapedia.Languages.MeTTa.HE.Space)
    (dispatch : Mettapedia.Languages.MeTTa.HE.GroundedDispatch)
    (bindings : Mettapedia.Languages.MeTTa.HE.Bindings),
    Mettapedia.Languages.MeTTa.HE.EvalAtom space dispatch
      claim.atom claim.expected bindings (claim.atom, bindings)

/-- Executable acceptance enters HE's authored evaluation relation. -/
theorem heSuccessDecide_sound (claim : HESuccessClaim)
    (accepted : heSuccessDecide claim = true) :
    HEPassesJudgment claim := by
  have passes : hePasses claim :=
    (hePassesBool_eq_true claim).mp accepted
  intro space dispatch bindings
  exact Mettapedia.Languages.MeTTa.HE.EvalAtom.type_pass
    claim.atom claim.expected bindings passes.1 passes.2

/-- Unknown HE symbols are the unknown-only fragment. -/
def HEUnknownOnly (claim : HESuccessClaim) : Prop :=
  ∃ name : String,
    claim.atom = .symbol name ∧
      name ≠ "Empty" ∧
      claim.expected = Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType

/-- A deliberately unsupported HE expected type. -/
def heRejectedClaim : HESuccessClaim where
  atom := .symbol "native-success-subject"
  expected := .symbol "NativeSuccessUnsupportedType"

/-- HE's unknown-preserving pass-through fragment is a nondegenerate success
interface over the live `EvalAtom` relation. -/
def heSuccessInterface : SuccessInterface HESuccessClaim where
  decide := heSuccessDecide
  Judges := HEPassesJudgment
  sound := heSuccessDecide_sound
  UnknownOnly := HEUnknownOnly
  witness := by
    refine ⟨⟨.symbol "native-unknown",
      Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType⟩, ?_⟩
    exact ⟨"native-unknown", rfl, by decide, rfl⟩
  never_rejects := by
    intro claim unknown
    rcases claim with ⟨atom, expected⟩
    rcases unknown with ⟨name, atomEq, notEmpty, expectedEq⟩
    dsimp at atomEq expectedEq
    subst atom
    subst expected
    apply (hePassesBool_eq_true _).mpr
    constructor
    · simp [Mettapedia.Languages.MeTTa.HE.isEmptyOrError,
        Mettapedia.Languages.MeTTa.HE.isEmptyAtom,
        Mettapedia.Languages.MeTTa.HE.isErrorAtom,
        Mettapedia.Languages.MeTTa.OSLFCore.Atom.empty, notEmpty]
    · exact Or.inl rfl
  rejects := by
    exact ⟨heRejectedClaim, rfl⟩

/-- The PeTTa pass-through interface names a nullary symbol and its expected
type. -/
structure PeTTaSuccessClaim where
  symbol : String
  expected : Pattern

/-- PeTTa's direct executable pass-through-type decision. -/
def pettaSuccessDecide (claim : PeTTaSuccessClaim) : Bool :=
    (claim.expected == Mettapedia.Languages.MeTTa.PeTTa.atomType) ||
    (claim.expected == Mettapedia.Languages.MeTTa.PeTTa.expressionType) ||
    (claim.expected == Mettapedia.Languages.MeTTa.PeTTa.undefinedType) ||
    (claim.expected == Mettapedia.Languages.MeTTa.PeTTa.groundedType)

theorem pettaSuccessDecide_eq_true (claim : PeTTaSuccessClaim) :
    pettaSuccessDecide claim = true ↔
      Mettapedia.Languages.MeTTa.PeTTa.isPassThroughType claim.expected := by
  simp [pettaSuccessDecide,
    Mettapedia.Languages.MeTTa.PeTTa.isPassThroughType, Bool.or_eq_true]
  tauto

/-- The native PeTTa evaluation judgment selected by the success interface. -/
def PeTTaPassesJudgment (claim : PeTTaSuccessClaim) : Prop :=
  ∀ (space : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace)
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings),
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval space
      (.apply claim.symbol []) claim.expected bindings
      [(.apply claim.symbol [], bindings)]

/-- Executable acceptance enters PeTTa's authored evaluation relation. -/
theorem pettaSuccessDecide_sound (claim : PeTTaSuccessClaim)
    (accepted : pettaSuccessDecide claim = true) :
    PeTTaPassesJudgment claim := by
  have passes : Mettapedia.Languages.MeTTa.PeTTa.isPassThroughType
      claim.expected := (pettaSuccessDecide_eq_true claim).mp accepted
  intro space bindings
  exact Mettapedia.Languages.MeTTa.PeTTa.meTTaEval_ground_passThrough passes

/-- PeTTa's undefined expected type is its unknown-only fragment. -/
def PeTTaUnknownOnly (claim : PeTTaSuccessClaim) : Prop :=
  claim.expected = Mettapedia.Languages.MeTTa.PeTTa.undefinedType

/-- A deliberately unsupported PeTTa expected type. -/
def pettaRejectedClaim : PeTTaSuccessClaim where
  symbol := "native-success-subject"
  expected := .apply "NativeSuccessUnsupportedType" []

/-- PeTTa's undefined-type pass-through is a nondegenerate success interface
over the live `MeTTaEval` relation. -/
def pettaSuccessInterface : SuccessInterface PeTTaSuccessClaim where
  decide := pettaSuccessDecide
  Judges := PeTTaPassesJudgment
  sound := pettaSuccessDecide_sound
  UnknownOnly := PeTTaUnknownOnly
  witness := ⟨⟨"native-unknown",
    Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩, rfl⟩
  never_rejects := by
    intro claim unknown
    rcases claim with ⟨symbol, expected⟩
    unfold PeTTaUnknownOnly at unknown
    dsimp at unknown
    subst expected
    rfl
  rejects := by
    exact ⟨pettaRejectedClaim, rfl⟩

/-- Positive HE witness: some unknown-only claim is operationally accepted. -/
theorem heSuccessInterface_positive :
    ∃ claim, heSuccessInterface.UnknownOnly claim ∧
      heSuccessInterface.decide claim = true := by
  rcases heSuccessInterface.witness with ⟨claim, unknown⟩
  exact ⟨claim, unknown, heSuccessInterface.never_rejects claim unknown⟩

/-- Negative HE witness: success typing still rejects an unsupported type. -/
theorem heSuccessInterface_negative :
    ∃ claim, heSuccessInterface.decide claim = false :=
  heSuccessInterface.rejects

/-- Positive PeTTa witness: some unknown-only claim is operationally accepted. -/
theorem pettaSuccessInterface_positive :
    ∃ claim, pettaSuccessInterface.UnknownOnly claim ∧
      pettaSuccessInterface.decide claim = true := by
  rcases pettaSuccessInterface.witness with ⟨claim, unknown⟩
  exact ⟨claim, unknown, pettaSuccessInterface.never_rejects claim unknown⟩

/-- Negative PeTTa witness: success typing still rejects an unsupported type. -/
theorem pettaSuccessInterface_negative :
    ∃ claim, pettaSuccessInterface.decide claim = false :=
  pettaSuccessInterface.rejects

/-! ### Fast correct-by-construction Pattern typing

This is the named composite between a native MeTTa typing calculus and the
certificate-free NIK decision interface.  Its scope is deliberately exact:
direct annotations, the unknown top type, bare-symbol typing, and structural
expression typing from PeTTa's live `MeTTaType` calculus.  It is not presented
as a decision procedure for the recursive arrow fragment.

Inside the trusted path, values carry an inductive `FastPatternTyping`
derivation and operations construct new derivations directly.  The Boolean
decision is used at an external publication boundary; its `Unit` certificate
has no choices and cannot contain a replay trace. -/

/-- A native typing query over Pattern terms and Pattern types. -/
structure PatternTypingClaim where
  space : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace
  term : Pattern
  type : Pattern

/-- The decidable, correct-by-construction fragment of PeTTa's native Pattern
typing calculus.  Every constructor is an actual `MeTTaType` rule. -/
inductive FastPatternTyping : PatternTypingClaim → Prop where
  | annotation {space term type}
      (member : Mettapedia.Languages.MeTTa.PeTTa.typeAnnotationPat term type ∈
        space.facts) :
      FastPatternTyping ⟨space, term, type⟩
  | undefined {space term} :
      FastPatternTyping ⟨space, term,
        Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩
  | symbol {space name} :
      FastPatternTyping ⟨space, .apply name [],
        Mettapedia.Languages.MeTTa.PeTTa.atomType⟩
  | application {space name arguments} (nonempty : arguments ≠ []) :
      FastPatternTyping ⟨space, .apply name arguments,
        Mettapedia.Languages.MeTTa.PeTTa.expressionType⟩

/-- The structural half of the executable fragment decision. -/
def fastIntrinsicTypeBool (term type : Pattern) : Bool :=
  match term with
  | .apply _ [] => type == Mettapedia.Languages.MeTTa.PeTTa.atomType
  | .apply _ (_ :: _) =>
      type == Mettapedia.Languages.MeTTa.PeTTa.expressionType
  | _ => false

/-- Executable native typing decision for the stated fragment. -/
def fastPatternTypingBool (claim : PatternTypingClaim) : Bool :=
  claim.space.facts.contains
      (Mettapedia.Languages.MeTTa.PeTTa.typeAnnotationPat claim.term claim.type) ||
    ((claim.type == Mettapedia.Languages.MeTTa.PeTTa.undefinedType) ||
      fastIntrinsicTypeBool claim.term claim.type)

/-- The executable decision is exact for the independently presented
inductive fragment, not merely sound. -/
theorem fastPatternTypingBool_correct (claim : PatternTypingClaim) :
    fastPatternTypingBool claim = true ↔ FastPatternTyping claim := by
  rcases claim with ⟨space, term, type⟩
  constructor
  · intro accepted
    simp only [fastPatternTypingBool, Bool.or_eq_true] at accepted
    rcases accepted with annotated | unknown | intrinsic
    · exact .annotation (List.contains_iff_mem.mp annotated)
    · have typeEq : type = Mettapedia.Languages.MeTTa.PeTTa.undefinedType :=
        beq_iff_eq.mp unknown
      subst type
      exact .undefined
    · cases term with
      | bvar index => simp [fastIntrinsicTypeBool] at intrinsic
      | fvar name => simp [fastIntrinsicTypeBool] at intrinsic
      | lambda binder body => simp [fastIntrinsicTypeBool] at intrinsic
      | multiLambda count binders body => simp [fastIntrinsicTypeBool] at intrinsic
      | subst body replacement => simp [fastIntrinsicTypeBool] at intrinsic
      | collection kind elements rest => simp [fastIntrinsicTypeBool] at intrinsic
      | apply name arguments =>
          cases arguments with
          | nil =>
              have typeEq : type = Mettapedia.Languages.MeTTa.PeTTa.atomType :=
                beq_iff_eq.mp intrinsic
              subst type
              exact .symbol
          | cons first rest =>
              have typeEq : type =
                  Mettapedia.Languages.MeTTa.PeTTa.expressionType :=
                beq_iff_eq.mp intrinsic
              subst type
              exact .application (List.cons_ne_nil first rest)
  · intro derivation
    cases derivation with
    | annotation member =>
        simp only [fastPatternTypingBool, Bool.or_eq_true]
        exact Or.inl (List.contains_iff_mem.mpr member)
    | undefined => simp [fastPatternTypingBool]
    | symbol => simp [fastPatternTypingBool, fastIntrinsicTypeBool]
    | application nonempty =>
        rename_i arguments
        cases arguments with
        | nil => exact (nonempty rfl).elim
        | cons first rest =>
            simp [fastPatternTypingBool, fastIntrinsicTypeBool]

/-- The native Pattern typing fragment as a certificate-free decision
kernel. -/
def fastPatternTypingKernel :
    Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker.DecisionKernel
      PatternTypingClaim FastPatternTyping where
  decide := fastPatternTypingBool
  correct := fastPatternTypingBool_correct

/-- Calculus soundness: every fast derivation is a derivation in PeTTa's
authored Pattern typing relation. -/
theorem FastPatternTyping.language_sound {claim : PatternTypingClaim}
    (derivation : FastPatternTyping claim) :
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaType
      claim.space claim.term claim.type := by
  cases derivation with
  | annotation member => exact .typeAnnotation _ _ member
  | undefined => exact .undefinedIsTop _
  | symbol => exact .symbolIsAtom _
  | application nonempty => exact .appIsExpression _ _ nonempty

/-- An interior fast-path value carries its derivation as its type; no replay
certificate or checker call is stored in it. -/
structure FastTypedPattern (claim : PatternTypingClaim) where
  derivation : FastPatternTyping claim

/-- Correct-by-construction weakening to the native unknown type. -/
def FastTypedPattern.toUnknown {claim : PatternTypingClaim}
    (_typed : FastTypedPattern claim) :
    FastTypedPattern ⟨claim.space, claim.term,
      Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩ :=
  ⟨FastPatternTyping.undefined⟩

/-- Publication through NIK is available from the carried derivation, while
the language judgment follows directly from calculus soundness. -/
theorem fast_pattern_typing_correct_by_construction
    {claim : PatternTypingClaim} (typed : FastTypedPattern claim) :
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaType
        claim.space claim.term claim.type ∧
      fastPatternTypingKernel.toChecker.check claim () = true :=
  ⟨typed.derivation.language_sound,
    (fastPatternTypingKernel.correct claim).mpr typed.derivation⟩

/-- The NIK publication boundary is exact for the native fragment. -/
theorem fastPatternTyping_authority :
    fastPatternTypingKernel.toChecker.Authority FastPatternTyping :=
  fastPatternTypingKernel.authority

/-- There is no certificate choice and therefore no certificate-level
micro-trace in the fast Pattern typing authority. -/
theorem fastPatternTyping_certificate_irrelevant
    (claim : PatternTypingClaim) (left right : Unit) :
    fastPatternTypingKernel.toChecker.check claim left =
      fastPatternTypingKernel.toChecker.check claim right := by
  cases left
  cases right
  rfl

/-- Positive witness for the correct-by-construction fast path. -/
theorem fastPatternTyping_unknown_positive
    (space : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) (term : Pattern) :
    fastPatternTypingKernel.toChecker.check
      ⟨space, term, Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩ () = true :=
  (fastPatternTypingKernel.correct _).mpr .undefined

/-- A concrete unsupported claim is rejected: the composite is not an
always-accepting typing facade. -/
def fastPatternTypingRejected : PatternTypingClaim where
  space := Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty
  term := .bvar 0
  type := .apply "NativeFastUnsupportedType" []

theorem fastPatternTyping_unsupported_negative :
    fastPatternTypingKernel.toChecker.check fastPatternTypingRejected () = false := by
  rfl

/-- Witness for the normative `directTypingPath` commitment.  Exact decision
and soundness into the guest calculus are both required, along with positive
and negative points; a constant decision facade cannot inhabit it. -/
structure DirectPatternTypingWitness where
  Meaning : PatternTypingClaim → Prop
  kernel : Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker.DecisionKernel
    PatternTypingClaim Meaning
  calculusSound : ∀ {claim}, Meaning claim →
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaType
      claim.space claim.term claim.type
  positive : ∃ claim, Meaning claim
  negative : ∃ claim, ¬ Meaning claim

namespace DirectPatternTypingWitness

/-- The deliberately too-rich two-tag format for the selected direct
judgment.  It is used only as a negative exact-parity canary. -/
def taggedProofSystem (direct : DirectPatternTypingWitness) :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofSystem
      PatternTypingClaim where
  ProofObject := Bool
  Judges := fun _ claim => direct.Meaning claim

end DirectPatternTypingWitness

/-- The live fast Pattern fragment discharges the direct-typing commitment. -/
def fastDirectPatternTypingWitness : DirectPatternTypingWitness where
  Meaning := FastPatternTyping
  kernel := fastPatternTypingKernel
  calculusSound := FastPatternTyping.language_sound
  positive := by
    exact ⟨⟨Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty,
      .bvar 0, Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩,
      .undefined⟩
  negative := by
    refine ⟨fastPatternTypingRejected, ?_⟩
    intro derivation
    have accepted :=
      (fastPatternTypingKernel.correct fastPatternTypingRejected).mpr derivation
    have rejected :
        fastPatternTypingKernel.decide fastPatternTypingRejected = false := by
      rfl
    rw [rejected] at accepted
    contradiction

/-! ### Exact parity for the direct typing judgment

Direct decision and proof-relevant publication are different authority tiers.
The fast typing judgment is proposition-valued, so its canonical native proof
object is `Unit`: the kernel computes theoremhood directly and retains no
micro-trace.  Prime Need's proof-relevant boundary is constructed separately
below. -/

namespace FastPatternParity

open Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-- The canonical native proof system for the proposition-valued fast typing
judgment.  It deliberately retains no proof tag. -/
def proofSystem : NativeProofSystem PatternTypingClaim where
  ProofObject := Unit
  Judges := fun _ claim => FastPatternTyping claim

/-- The native proof kernel performs the same direct computation as the
production typing decision; the `Unit` object contributes no work. -/
def nativeKernel : NativeProofKernel proofSystem where
  decide claim _ := fastPatternTypingBool claim
  correct claim _ := fastPatternTypingBool_correct claim

/-- Exact accepted/native fibre parity for the direct Pattern typing path. -/
def certificateEquivalence :
    CertificateEquivalence fastPatternTypingKernel.toChecker proofSystem :=
  nativeKernel.certificateEquivalence

/-- The direct typing checker is therefore an exact authority for inhabitation
of its canonical native judgment fibre. -/
theorem authority :
    fastPatternTypingKernel.toChecker.Authority
      (fun claim => Nonempty (proofSystem.ProofFibre claim)) :=
  certificateEquivalence.authority

/-- The native proof kernel adds no second typing pass: with its unique proof
object erased, its decision is definitionally the production decision. -/
theorem computes_directly (claim : PatternTypingClaim)
    (proof : proofSystem.ProofObject) :
    nativeKernel.decide claim proof = fastPatternTypingKernel.decide claim := by
  cases proof
  rfl

/-- The canonical typing proof fibre is proposition-like: every two judged
native objects in one fibre are equal. -/
theorem proofFibre_subsingleton (claim : PatternTypingClaim) :
    Subsingleton (proofSystem.ProofFibre claim) :=
  ⟨fun left right => by
    apply Subtype.ext
    cases left.1
    cases right.1
    rfl⟩

/-- A two-tag proof guest has the same theoremhood but strictly more proof
identity than the direct decision checker can preserve. -/
def taggedProofSystem : NativeProofSystem PatternTypingClaim where
  ProofObject := Bool
  Judges := fun _ claim => FastPatternTyping claim

/-- Negative parity witness: theoremhood parity cannot be silently promoted
to parity with an independently proof-relevant certificate format. -/
theorem no_tagged_certificateEquivalence :
    ¬ Nonempty
      (CertificateEquivalence fastPatternTypingKernel.toChecker
        taggedProofSystem) := by
  rintro ⟨boundary⟩
  let claim : PatternTypingClaim :=
    ⟨Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty, .bvar 0,
      Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩
  have typed : FastPatternTyping claim := .undefined
  let falseProof : taggedProofSystem.ProofFibre claim := ⟨false, typed⟩
  let trueProof : taggedProofSystem.ProofFibre claim := ⟨true, typed⟩
  have sameAccepted :
      (boundary.fibreEquiv claim).symm falseProof =
        (boundary.fibreEquiv claim).symm trueProof := by
    apply Subtype.ext
    exact Subsingleton.elim _ _
  have sameProof : falseProof = trueProof :=
    (boundary.fibreEquiv claim).symm.injective sameAccepted
  have false_eq_true := congrArg (fun proof => proof.1) sameProof
  exact Bool.false_ne_true false_eq_true

end FastPatternParity

/-- Audit package for O8.  Exact theoremhood parity, a computing native
kernel, positive and negative claims, and the proof-tag counterexample are all
required together. -/
structure NativeAuthorityParityWitness
    (direct : DirectPatternTypingWitness) where
  guest : Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofSystem
    PatternTypingClaim
  nativeKernel : Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofKernel
    guest
  parity : Mettapedia.GSLT.LanguageDef.NIKMetalogic.CertificateEquivalence
    direct.kernel.toChecker guest
  computes_directly : ∀ claim proof,
    nativeKernel.decide claim proof = direct.kernel.decide claim
  positive : ∃ claim,
    direct.kernel.toChecker.check claim () = true
  negative : ∃ claim,
    direct.kernel.toChecker.check claim () = false
  fibres_subsingleton : ∀ claim, Subsingleton (guest.ProofFibre claim)
  tagged_format_not_exact :
    ¬ Nonempty
      (Mettapedia.GSLT.LanguageDef.NIKMetalogic.CertificateEquivalence
        direct.kernel.toChecker direct.taggedProofSystem)

/-- Concrete authority-from-birth witness for the direct Pattern fragment. -/
def fastNativeAuthorityParityWitness :
    NativeAuthorityParityWitness fastDirectPatternTypingWitness where
  guest := FastPatternParity.proofSystem
  nativeKernel := FastPatternParity.nativeKernel
  parity := FastPatternParity.certificateEquivalence
  computes_directly := FastPatternParity.computes_directly
  positive := by
    exact ⟨⟨Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty,
      .bvar 0, Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩,
      fastPatternTyping_unknown_positive _ _⟩
  negative := ⟨fastPatternTypingRejected,
    fastPatternTyping_unsupported_negative⟩
  fibres_subsingleton := FastPatternParity.proofFibre_subsingleton
  tagged_format_not_exact :=
    FastPatternParity.no_tagged_certificateEquivalence

/-! ## §6d Prime Need as an admitted native proof flow

The production interpretation of admission is amortized: a Need transition is
admitted with its semantic preservation law once, after which native
derivations apply it by typed composition.  The interior operation below does
not invoke a checker.  A checker appears only at the optional publication
boundary, where it compares the retained output index and preserves the exact
native proof fibre.

This is the live modular Prime Need relation from `Prime.Language`, not a
second evaluator or a synthetic transition system. -/

namespace PrimeNeedProofFlow

open Mettapedia.Languages.MeTTa.Prime.Language
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-- A Need judgment states both the live operational term and the complete bag
it denotes.  Keeping the bag in the claim makes preservation non-vacuous. -/
structure Claim (model : Model) where
  term : NeedTerm model
  expected : Multiset Pattern

/-- One admitted operation is an actual Need step whose expected bag is
unchanged across the endpoints. -/
structure Step (model : Model)
    (source target : Claim model) where
  operational : PLift
    ((needGSLT model).Step source.term target.term)
  expected_eq : source.expected = target.expected

/-- Independent semantic meaning of a Need claim, through Prime's live
elaboration rather than through the admission checker. -/
def Meaning (model : Model) (claim : Claim model) : Prop :=
  (needElaboration model).elaborate claim.term =
    some claim.expected

/-- An admission seed is proof that the starting claim has its declared live
Prime meaning.  It is paid for at admission time, not reconstructed per step. -/
abbrev Seed (model : Model) (claim : Claim model) :=
  PLift (Meaning model claim)

/-- Live Need steps preserve claim meaning. -/
theorem step_sound (model : Model)
    {source target : Claim model} (step : Step model source target)
    (sourceMeaning : Meaning model source) : Meaning model target := by
  have preserves :=
    (needElaboration model).rewrite step.operational.down
  calc
    (needElaboration model).elaborate target.term =
        (needElaboration model).elaborate source.term :=
      preserves.symm
    _ = some source.expected := sourceMeaning
    _ = some target.expected := congrArg some step.expected_eq

/-- Admission seeds are meaningful by construction. -/
theorem seed_sound (model : Model) {claim : Claim model}
    (seed : Seed model claim) : Meaning model claim :=
  seed.down

/-- The proof-relevant substitution algebra generated by live Need steps. -/
abbrev Clone (model : Model) :=
  operationalDerivationClone (Step model) (Seed model)

/-- Every live Need step is admitted as a one-premise native operation. -/
def admittedRules (model : Model) :
    AdmittedCloneRules (Clone model) (Meaning model) :=
  operationalAdmittedRules (step_sound model)

/-- The whole closed Need proof algebra is semantically sound without an
interior checker call. -/
def soundClone (model : Model) :
    SoundClone (Clone model) (Meaning model) :=
  operationalSoundClone (seed_sound model) (step_sound model)

/-- The singleton proof environment used to apply one admitted unary rule. -/
def singletonEnvironment (model : Model)
    {source : Claim model}
    (proof : (Clone model).Hom [] source) :
    (index : Fin ([source].length)) →
      (Clone model).Hom [] ([source].get index) := by
  intro index
  refine Fin.cases proof ?_ index
  intro impossible
  exact Fin.elim0 impossible

/-- Apply one already-admitted Need operation.  This is the zero-recheck
interior path: it is clone substitution, with no checker argument. -/
def applyAdmitted (model : Model)
    (rule : OperationalRule (Step model))
    (prior : (Clone model).Hom [] rule.source) :
    (Clone model).Hom [] rule.target :=
  (admittedRules model).applyClosed rule
    (singletonEnvironment model prior)

/-- Admission adds no hidden replay phase: operational application is exactly
one native `advance` node over the already-held proof. -/
theorem applyAdmitted_eq_advance (model : Model)
    (rule : OperationalRule (Step model))
    (prior : (Clone model).Hom [] rule.source) :
    applyAdmitted model rule prior =
      OperationalDerivation.advance prior rule.step := by
  rfl

/-- The zero-recheck application preserves semantic meaning by the law paid
for when the operation was admitted. -/
theorem applyAdmitted_sound (model : Model)
    (rule : OperationalRule (Step model))
    (prior : (Clone model).Hom [] rule.source)
    (sourceMeaning : Meaning model rule.source) :
    Meaning model rule.target :=
  (admittedRules model).applyClosed_sound rule
    (singletonEnvironment model prior)
    (fun index => by
      refine Fin.cases sourceMeaning ?_ index
      intro impossible
      exact Fin.elim0 impossible)

/-- The exact request claim for the live occurrence bag. -/
def requestClaim (model : Model) (space : model.Space)
    (subject : Pattern) : Claim model where
  term := .request space subject
  expected := model.base.source.occurrences space subject

/-- The corresponding occurrence answer retains the same complete bag. -/
def answerClaim (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat) : Claim model where
  term := .answer space subject (needKey model space subject)
    occurrence result
  expected := model.base.source.occurrences space subject

/-- A request seed is meaningful by computation of the live elaboration. -/
theorem request_meaning (model : Model) (space : model.Space)
    (subject : Pattern) : Meaning model (requestClaim model space subject) :=
  rfl

/-- An admitted occurrence is an actual rule of the live Need GSLT. -/
def foundRule (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    OperationalRule (Step model) where
  source := requestClaim model space subject
  target := answerClaim model space subject result occurrence
  step :=
    { operational := ⟨(needGSLT_step_iff model space subject
          result occurrence).2 copy⟩
      expected_eq := rfl }

/-- The admitted request seed, retained as native evidence rather than a
micro-trace of how its complete bag was computed. -/
def requestProof (model : Model) (space : model.Space)
    (subject : Pattern) :
    (Clone model).Hom [] (requestClaim model space subject) :=
  .admittedSeed ⟨request_meaning model space subject⟩

/-- A real Need occurrence flows by applying the already-admitted operation;
there is no interior certificate construction or checker invocation. -/
def foundProof (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (Clone model).Hom [] (answerClaim model space subject result occurrence) :=
  applyAdmitted model (foundRule model space subject result occurrence copy)
    (requestProof model space subject)

/-- Positive Mode-B theorem: the actual Need answer retains the full declared
bag after zero-recheck native application. -/
theorem found_flows_without_recheck (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    Meaning model (answerClaim model space subject result occurrence) :=
  (soundClone model).closed_sound
    (foundProof model space subject result occurrence copy)

/-- Native proof objects and their entire exact judged fibres. -/
abbrev ProofSystem (model : Model) :=
  cloneNativeProofSystem (Clone model)

/-- A realization with decidable claim identity checks only the retained
output index; it never replays the Need derivation. -/
def nativeKernel (model : Model) [DecidableEq (Claim model)] :
    NativeProofKernel (ProofSystem model) :=
  cloneNativeProofKernel (Clone model)

/-- The primary publication boundary preserves the exact native proof fibre. -/
def primaryBoundary (model : Model)
    [DecidableEq (Claim model)] :
    CertificateEquivalence
      (nativeKernel model).toChecker (ProofSystem model) :=
  (nativeKernel model).certificateEquivalence

/-- Optional publication of a flowed Need result checks only its output index;
semantic soundness still comes from admission and native composition. -/
theorem found_reaches_primary_boundary (model : Model)
    [DecidableEq (Claim model)]
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (∃ certificate,
      (nativeKernel model).toChecker.check
        (answerClaim model space subject result occurrence) certificate = true) ∧
      Meaning model (answerClaim model space subject result occurrence) :=
  closedCloneProof_flows_without_recheck
    (soundClone model) (primaryBoundary model)
    (foundProof model space subject result occurrence copy)

/-- Negative witness: an answer is terminal in the Need algebra, so no
admitted Need operation can use it as the source of another step. -/
theorem answer_has_no_admitted_successor (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat) :
    ¬ ∃ target : Claim model,
      Nonempty
        (Step model (answerClaim model space subject result occurrence) target) := by
  intro successor
  rcases successor with ⟨⟨targetTerm, targetExpected⟩, ⟨step⟩⟩
  cases targetTerm <;> cases step.operational.down

/-- Revision mutation invalidates answer identity even for the same subject
and occurrence: a stale admitted result cannot be reused at a new revision. -/
theorem answer_key_changes_with_revision (model : Model)
    {first second : model.Space} (subject result : Pattern) (occurrence : Nat)
    (different : model.revision first ≠ model.revision second) :
    (answerClaim model first subject result occurrence).term ≠
      (answerClaim model second subject result occurrence).term := by
  intro equal
  injection equal with _ _ keyEqual _ _
  exact needKey_ne_of_revision_ne model subject different keyEqual

/-- Audit package for the native-proof-object commitment.  Its positive law
is conditional only on a real occurrence supplied by the selected operational
base; its negative law rules out fabricated continuation from terminal Need
answers. -/
structure NativeProofFlowWitness where
  rules : ∀ model : Model,
    AdmittedCloneRules (Clone model) (Meaning model)
  semantics : ∀ model : Model,
    SoundClone (Clone model) (Meaning model)
  exactBoundary : ∀ (model : Model) [DecidableEq (Claim model)],
    CertificateEquivalence
      (nativeKernel model).toChecker (ProofSystem model)
  occurrenceFlows : ∀ (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat),
    occurrence < Multiset.count result
      (model.base.source.occurrences space subject) →
    Meaning model (answerClaim model space subject result occurrence)
  answerTerminal : ∀ (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat),
    ¬ ∃ target : Claim model,
      Nonempty
        (Step model (answerClaim model space subject result occurrence) target)
  mutationInvalidates : ∀ (model : Model) {first second : model.Space}
    (subject result : Pattern) (occurrence : Nat),
    model.revision first ≠ model.revision second →
    (answerClaim model first subject result occurrence).term ≠
      (answerClaim model second subject result occurrence).term

/-- The live modular Prime Need algebra discharges the native proof-flow
commitment for every selected operational base. -/
def nativeProofFlowWitness : NativeProofFlowWitness where
  rules := admittedRules
  semantics := soundClone
  exactBoundary := primaryBoundary
  occurrenceFlows := found_flows_without_recheck
  answerTerminal := answer_has_no_admitted_successor
  mutationInvalidates := answer_key_changes_with_revision

end PrimeNeedProofFlow

/-! ## §6e Prime Need inside the returned-fibre fragment of GSLT-IL

The relation below is exact only for commands already returned at one selected
Prime Need stage.  GSLT-IL additionally has pending `via` commands and their
transport steps; the negative witness at the end of the section keeps that
strict extension visible. -/

namespace PrimeGSLTILReturnedFibre

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.MeTTa.Prime.Language
open PrimeNeedProofFlow

/-- The proposition underlying one proof-relevant admitted Need step. -/
def ClaimStep (model : Model) (source target : Claim model) : Prop :=
  (needGSLT model).Step source.term target.term ∧
    source.expected = target.expected

/-- Forget only proof irrelevance from the retained Need step. -/
def stepToClaimStep (model : Model) {source target : Claim model}
    (step : Step model source target) : ClaimStep model source target :=
  ⟨step.operational.down, step.expected_eq⟩

/-- Reconstruct the retained Need step from its two defining propositions. -/
def stepOfClaimStep (model : Model) {source target : Claim model}
    (step : ClaimStep model source target) : Step model source target where
  operational := ⟨step.1⟩
  expected_eq := step.2

/-- The claim-indexed GSLT used as the single returned fibre.  It reuses the
live Need relation and retains the complete expected bag in every state. -/
def claimGSLT (model : Model) : GSLT where
  Term := Claim model
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ClaimStep model
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- One-object index category for the selected Prime Need fibre. -/
abbrev Index := CategoryTheory.Discrete PUnit

def stage : Index := CategoryTheory.Discrete.mk PUnit.unit

/-- The constant one-stage operational diagram.  The one object is not a
claim that all of GSLT-IL has one stage; it selects the returned-fibre fragment
used by this comparison. -/
def diagram (model : Model) : Diagram.{0, 0, 0} Index where
  obj _ := ⟨claimGSLT model⟩
  map _ := OperationalTranslation.id (claimGSLT model)
  map_id _ := by
    apply OperationalTranslation.ext
    rfl
  map_comp _ _ := by
    apply OperationalTranslation.ext
    rfl

/-- Quote one full Need claim into the equation class of the selected stage. -/
def quoteClaim (model : Model) (claim : Claim model) :
    SemanticTerm (claimGSLT model) :=
  Quotient.mk (claimGSLT model).equations claim

/-- The returned GSLT-IL command representing one Prime Need claim. -/
def encodeClaim (model : Model) (claim : Claim model) : Command (diagram model) :=
  .at stage (quoteClaim model claim)

/-- The actual GSLT-IL step relation restricted to encoded returned claims. -/
abbrev ReturnedStep (model : Model) (source target : Claim model) :=
  Command.Step (diagram model) (encodeClaim model source)
    (encodeClaim model target)

instance step_subsingleton (model : Model) (source target : Claim model) :
    Subsingleton (Step model source target) where
  allEq first second := by
    cases first with
    | mk firstOperational firstExpected =>
      cases second with
      | mk secondOperational secondExpected =>
        have operationalEqual : firstOperational = secondOperational :=
          Subsingleton.elim _ _
        cases operationalEqual
        have expectedEqual : firstExpected = secondExpected :=
          Subsingleton.elim _ _
        cases expectedEqual
        rfl

instance returnedStep_subsingleton (model : Model)
    (source target : Claim model) :
    Subsingleton (ReturnedStep model source target) where
  allEq first second := by
    cases first with
    | fibre firstStep =>
      cases second with
      | fibre secondStep =>
        congr

/-- Exact proof-fibre equivalence between a retained Prime Need edge and the
corresponding returned-fibre GSLT-IL edge. -/
def stepEquiv (model : Model) {source target : Claim model} :
    Step model source target ≃ ReturnedStep model source target where
  toFun step :=
    .fibre (semanticStep_mk (stepToClaimStep model step))
  invFun commandStep := by
    cases commandStep with
    | fibre semanticStep =>
      apply stepOfClaimStep model
      exact (semanticStep_mk_iff_step (claimGSLT model) source target).mp
        semanticStep
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Native derivations in the returned GSLT-IL fragment use the original
Prime claims and seeds; only the one-step evidence is represented by an actual
`Command.Step`. -/
abbrev ReturnedClone (model : Model) :=
  operationalDerivationClone (ReturnedStep model) (Seed model)

/-- Map every open Prime derivation into the returned command fragment. -/
def toReturned (model : Model) {context : List (Claim model)}
    {target : Claim model} :
    (Clone model).Hom context target → (ReturnedClone model).Hom context target
  | .assumption index => .assumption index
  | .admittedSeed evidence => .admittedSeed evidence
  | .advance prior step =>
      .advance (toReturned model prior) (stepEquiv model step)

/-- Recover every open Prime derivation from the returned command fragment. -/
def fromReturned (model : Model) {context : List (Claim model)}
    {target : Claim model} :
    (ReturnedClone model).Hom context target → (Clone model).Hom context target
  | .assumption index => .assumption index
  | .admittedSeed evidence => .admittedSeed evidence
  | .advance prior step =>
      .advance (fromReturned model prior) ((stepEquiv model).symm step)

theorem fromReturned_toReturned (model : Model)
    {context : List (Claim model)} {target : Claim model}
    (proof : (Clone model).Hom context target) :
    fromReturned model (toReturned model proof) = proof := by
  induction proof with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp only [toReturned, fromReturned]
      rw [inductionHypothesis, Equiv.symm_apply_apply]

theorem toReturned_fromReturned (model : Model)
    {context : List (Claim model)} {target : Claim model}
    (proof : (ReturnedClone model).Hom context target) :
    toReturned model (fromReturned model proof) = proof := by
  induction proof with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp only [toReturned, fromReturned]
      rw [inductionHypothesis, Equiv.apply_symm_apply]

theorem toReturned_bind (model : Model)
    {sourceContext targetContext : List (Claim model)} {target : Claim model}
    (proof : (Clone model).Hom sourceContext target)
    (environment : (index : Fin sourceContext.length) →
      (Clone model).Hom targetContext (sourceContext.get index)) :
    toReturned model (OperationalDerivation.bind proof environment) =
      OperationalDerivation.bind (toReturned model proof)
        (fun index => toReturned model (environment index)) := by
  induction proof with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp only [OperationalDerivation.bind, toReturned]
      rw [inductionHypothesis]

theorem fromReturned_bind (model : Model)
    {sourceContext targetContext : List (Claim model)} {target : Claim model}
    (proof : (ReturnedClone model).Hom sourceContext target)
    (environment : (index : Fin sourceContext.length) →
      (ReturnedClone model).Hom targetContext (sourceContext.get index)) :
    fromReturned model (OperationalDerivation.bind proof environment) =
      OperationalDerivation.bind (fromReturned model proof)
        (fun index => fromReturned model (environment index)) := by
  induction proof with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp only [OperationalDerivation.bind, fromReturned]
      rw [inductionHypothesis]

/-- The exact open-clone equivalence: hypotheses, occurrence indices, and
simultaneous proof substitution are preserved both ways. -/
def cloneEquivalence (model : Model) :
    CloneEquivalence (Clone model) (ReturnedClone model) where
  toHom :=
    { map := toReturned model
      map_project := fun _ => rfl
      map_substitute := toReturned_bind model }
  invHom :=
    { map := fromReturned model
      map_project := fun _ => rfl
      map_substitute := fromReturned_bind model }
  left_inv := fromReturned_toReturned model
  right_inv := toReturned_fromReturned model

/-- Semantic preservation transported to the returned GSLT-IL edge family. -/
theorem returnedStep_sound (model : Model)
    {source target : Claim model} (step : ReturnedStep model source target)
    (sourceMeaning : Meaning model source) : Meaning model target :=
  step_sound model ((stepEquiv model).symm step) sourceMeaning

/-- Returned-fibre GSLT-IL edges are admitted into the same common operation
algebra as the original Prime Need edges. -/
def returnedAdmittedRules (model : Model) :
    AdmittedCloneRules (ReturnedClone model) (Meaning model) :=
  operationalAdmittedRules (returnedStep_sound model)

/-- Map a retained Prime rule to the exactly corresponding returned command
rule without changing either endpoint claim. -/
def toReturnedRule (model : Model) (rule : OperationalRule (Step model)) :
    OperationalRule (ReturnedStep model) where
  source := rule.source
  target := rule.target
  step := stepEquiv model rule.step

/-- The returned singleton proof environment. -/
def returnedSingletonEnvironment (model : Model)
    {source : Claim model}
    (proof : (ReturnedClone model).Hom [] source) :
    (index : Fin ([source].length)) →
      (ReturnedClone model).Hom [] ([source].get index) := by
  intro index
  refine Fin.cases proof ?_ index
  intro impossible
  exact Fin.elim0 impossible

/-- The admission square commutes on execution: applying the Prime admitted
operation and then entering GSLT-IL is exactly applying the corresponding
returned-fibre admitted operation.  Both sides are native substitution and
neither invokes a checker. -/
theorem admission_square_commutes (model : Model)
    (rule : OperationalRule (Step model))
    (prior : (Clone model).Hom [] rule.source) :
    toReturned model
        ((admittedRules model).toAdmissionHom rule |>.run
          (singletonEnvironment model prior)) =
      ((returnedAdmittedRules model).toAdmissionHom
          (toReturnedRule model rule) |>.run
        (returnedSingletonEnvironment model (toReturned model prior))) := by
  rfl

/-- The GSLT-IL pending command at the unique stage. -/
def pendingClaim (model : Model) (claim : Claim model) : Command (diagram model) :=
  .via (CategoryTheory.CategoryStruct.id stage) (quoteClaim model claim)

/-- Positive strict-extension witness: GSLT-IL can explicitly apply a route
even in the one-object diagram. -/
def applyIdentityVia (model : Model) (claim : Claim model) :
    Command.Step (diagram model) (pendingClaim model claim)
      (.at stage (transportTerm (diagram model)
        (CategoryTheory.CategoryStruct.id stage)
        (quoteClaim model claim))) :=
  Command.Step.applyVia (diagram := diagram model)
    (CategoryTheory.CategoryStruct.id stage) (quoteClaim model claim)

/-- Negative boundary: a pending route command is outside the returned Prime
Need image.  Thus the clone equivalence above cannot identify full GSLT-IL
with Prime. -/
theorem pendingClaim_not_encoded (model : Model) (claim other : Claim model) :
    pendingClaim model claim ≠ encodeClaim model other := by
  intro equality
  cases equality

/-- Audit package for O9.  It retains the exact open-clone equivalence and the
admission commuting square while requiring a concrete command outside the
returned image, so it cannot be satisfied by identifying Prime with full
GSLT-IL. -/
structure Witness where
  clone : ∀ model : Model,
    CloneEquivalence (Clone model) (ReturnedClone model)
  admissionCommutes : ∀ (model : Model)
      (rule : OperationalRule (Step model))
      (prior : (Clone model).Hom [] rule.source),
    toReturned model
        ((admittedRules model).toAdmissionHom rule |>.run
          (singletonEnvironment model prior)) =
      ((returnedAdmittedRules model).toAdmissionHom
          (toReturnedRule model rule) |>.run
        (returnedSingletonEnvironment model (toReturned model prior)))
  strictExtension : ∀ (model : Model) (claim : Claim model),
    ∃ pending : Command (diagram model),
      pending = pendingClaim model claim ∧
        ∀ other : Claim model, pending ≠ encodeClaim model other

/-- Prime's live Need algebra and the returned-fibre GSLT-IL fragment satisfy
the exact O9 relationship, with full transport kept strictly outside it. -/
def witness : Witness where
  clone := cloneEquivalence
  admissionCommutes := admission_square_commutes
  strictExtension := by
    intro model claim
    exact ⟨pendingClaim model claim, rfl,
      pendingClaim_not_encoded model claim⟩

end PrimeGSLTILReturnedFibre

/-! ## §7 Contextual judgment

`contextualJudgment` is discharged by the spine's comprehension structure
*plus* a designated contextual box: the type of open terms over a context,
internalized.  This is the metavariable type; the quotation modality and the
metavariable type must coincide (one modality, two readings). -/

structure ContextualBoxWitness (M : ModeTheory) (C : ModalCwF M)
    (Q : QuotationWitness M C) where
  /-- Internal code of an open type: boxing along the quotation modality. -/
  codeOf : {Γ : C.Con Q.codeMode} →
    C.Ty (C.lock Q.quote Γ) → C.Ty Γ
  /-- Agreement with the spine's box on the designated modality. -/
  codeOf_is_box : ∀ {Γ : C.Con Q.codeMode} (A : C.Ty (C.lock Q.quote Γ)),
    codeOf A = C.boxTy Q.quote A

/-- Open families are internalized by the same nontrivial quotation modality,
not by a second contextual-code operator. -/
def familiesContextualBoxWitness :
    ContextualBoxWitness stageModeTheory familiesCwF
      familiesQuotationWitness where
  codeOf := fun A => familiesCwF.boxTy familiesQuotationWitness.quote A
  codeOf_is_box := by intros; rfl

/-! ### Committed-capacity witnesses

Witnesses for the requirements forced by the normative channel.  Each again
carries a nontriviality field blocking the degenerate discharge. -/

/-- Witness for `dependentFamilies`: a family over a base whose fibres
genuinely vary — two instantiations differ, so the family cannot be a
constant presheaf in disguise. -/
structure DependentFamilyWitness (M : ModeTheory) (C : ModalCwF M) where
  mode : M.Mode
  Γ : C.Con mode
  A : C.Ty Γ
  B : C.Ty (C.ext Γ A)
  a₁ : C.Tm Γ (C.tySub A (C.sid Γ))
  a₂ : C.Tm Γ (C.tySub A (C.sid Γ))
  fibres_differ :
    C.tySub B (C.sext (C.sid Γ) a₁) ≠ C.tySub B (C.sext (C.sid Γ) a₂)

/-- A genuinely varying family in the families CwF.  Its fibre is empty at
`false` and inhabited at `true`, so it cannot be a constant family in
disguise. -/
def familiesDependentFamilyWitness :
    DependentFamilyWitness stageModeTheory familiesCwF where
  mode := stageOfNat 0
  Γ := PUnit
  A := fun _ => Bool
  B := fun value => if value.2 then PUnit else Empty
  a₁ := fun _ => false
  a₂ := fun _ => true
  fibres_differ := by
    intro equalFibres
    have fibreEquality : Empty = PUnit := by
      have pointwise := congrFun equalFibres PUnit.unit
      simpa [familiesCwF] using pointwise
    have impossible : Nonempty Empty := by
      rw [fibreEquality]
      exact ⟨PUnit.unit⟩
    rcases impossible with ⟨value⟩
    exact value.elim

/-- Formation, reflexivity, substitution stability, and noncollapse for
intensional identity. -/
structure IdentityFormation (M : ModeTheory) (C : ModalCwF M) where
  idTy : {m : M.Mode} → {Γ : C.Con m} → (A : C.Ty Γ) →
    C.Tm Γ A → C.Tm Γ A → C.Ty Γ
  refl : {m : M.Mode} → {Γ : C.Con m} → {A : C.Ty Γ} →
    (a : C.Tm Γ A) → C.Tm Γ (idTy A a a)
  idTy_sub : ∀ {m : M.Mode} {Γ Δ : C.Con m}
    (A : C.Ty Δ) (left right : C.Tm Δ A) (σ : C.Sub Γ Δ),
    C.tySub (idTy A left right) σ =
      idTy (C.tySub A σ) (C.tmSub left σ) (C.tmSub right σ)
  refl_sub : ∀ {m : M.Mode} {Γ Δ : C.Con m}
    {A : C.Ty Δ} (term : C.Tm Δ A) (σ : C.Sub Γ Δ),
    HEq (C.tmSub (refl term) σ) (refl (C.tmSub term σ))
  discriminates :
    ∃ (m : M.Mode) (Γ : C.Con m) (A : C.Ty Γ) (a b : C.Tm Γ A),
      IsEmpty (C.Tm Γ (idTy A a b))

namespace IdentityFormation

def firstContext {M : ModeTheory} {C : ModalCwF M}
    (_identity : IdentityFormation M C) {mode : M.Mode} {Γ : C.Con mode}
    (A : C.Ty Γ) : C.Con mode :=
  C.ext Γ A

def firstType {M : ModeTheory} {C : ModalCwF M}
    (identity : IdentityFormation M C) {mode : M.Mode} {Γ : C.Con mode}
    (A : C.Ty Γ) : C.Ty (identity.firstContext A) :=
  C.tySub A (C.wk A)

def pairContext {M : ModeTheory} {C : ModalCwF M}
    (identity : IdentityFormation M C) {mode : M.Mode} {Γ : C.Con mode}
    (A : C.Ty Γ) : C.Con mode :=
  C.ext (identity.firstContext A) (identity.firstType A)

def pairType {M : ModeTheory} {C : ModalCwF M}
    (identity : IdentityFormation M C) {mode : M.Mode} {Γ : C.Con mode}
    (A : C.Ty Γ) : C.Ty (identity.pairContext A) :=
  C.tySub (identity.firstType A) (C.wk (identity.firstType A))

def pairLeft {M : ModeTheory} {C : ModalCwF M}
    (identity : IdentityFormation M C) {mode : M.Mode} {Γ : C.Con mode}
    (A : C.Ty Γ) : C.Tm (identity.pairContext A) (identity.pairType A) :=
  C.tmSub (C.vz A) (C.wk (identity.firstType A))

def pairRight {M : ModeTheory} {C : ModalCwF M}
    (identity : IdentityFormation M C) {mode : M.Mode} {Γ : C.Con mode}
    (A : C.Ty Γ) : C.Tm (identity.pairContext A) (identity.pairType A) :=
  C.vz (identity.firstType A)

def pairIdentity {M : ModeTheory} {C : ModalCwF M}
    (identity : IdentityFormation M C) {mode : M.Mode} {Γ : C.Con mode}
    (A : C.Ty Γ) : C.Ty (identity.pairContext A) :=
  identity.idTy (identity.pairType A)
    (identity.pairLeft A) (identity.pairRight A)

def identityContext {M : ModeTheory} {C : ModalCwF M}
    (identity : IdentityFormation M C) {mode : M.Mode} {Γ : C.Con mode}
    (A : C.Ty Γ) : C.Con mode :=
  C.ext (identity.pairContext A) (identity.pairIdentity A)

end IdentityFormation

/-- Full intensional identity witness.  The motive is an internal type over
`Γ,x:A,y:A,p:Id x y`; `diagonal` embeds the reflexivity case, and `j` extends
a section over that diagonal to the whole identity context. -/
structure IdentityTypeWitness (M : ModeTheory) (C : ModalCwF M) where
  formation : IdentityFormation M C
  diagonal : {mode : M.Mode} → {Γ : C.Con mode} → (A : C.Ty Γ) →
    C.Sub (formation.firstContext A) (formation.identityContext A)
  diagonal_pair : ∀ {mode : M.Mode} {Γ : C.Con mode} (A : C.Ty Γ),
    C.scomp (diagonal A) (C.wk (formation.pairIdentity A)) =
      C.selfExtend (C.vz A)
  diagonal_refl : ∀ {mode : M.Mode} {Γ : C.Con mode} (A : C.Ty Γ),
    HEq
      (C.tmSub (C.vz (formation.pairIdentity A)) (diagonal A))
      (formation.refl (C.vz A))
  j : {mode : M.Mode} → {Γ : C.Con mode} → (A : C.Ty Γ) →
    (motive : C.Ty (formation.identityContext A)) →
    C.Tm (formation.firstContext A) (C.tySub motive (diagonal A)) →
    C.Tm (formation.identityContext A) motive
  beta : ∀ {mode : M.Mode} {Γ : C.Con mode} (A : C.Ty Γ)
    (motive : C.Ty (formation.identityContext A))
    (base : C.Tm (formation.firstContext A)
      (C.tySub motive (diagonal A))),
    C.tmSub (j A motive base) (diagonal A) = base

/-- Pointwise equality in the families CwF supplies stable intensional
identity formation and a genuinely empty unequal fibre. -/
def familiesIdentityFormation :
    IdentityFormation stageModeTheory familiesCwF where
  idTy := fun _A left right value => PLift (left value = right value)
  refl := fun _term _value => ⟨rfl⟩
  idTy_sub := by intros; rfl
  refl_sub := by intros; exact HEq.rfl
  discriminates := by
    refine ⟨stageOfNat 0, PUnit, (fun _ => Bool),
      (fun _ => false), (fun _ => true), ?_⟩
    exact ⟨fun impossible =>
      Bool.noConfusion (impossible PUnit.unit).down⟩

/-- The families model has full internal path induction.  `j` pattern-matches
only on the identity witness, and its reflexivity computation is judgmental. -/
def familiesIdentityTypes :
    IdentityTypeWitness stageModeTheory familiesCwF where
  formation := familiesIdentityFormation
  diagonal := by
    intro mode Γ A value
    exact ⟨⟨value, value.2⟩, ⟨rfl⟩⟩
  diagonal_pair := by
    intro mode Γ A
    funext value
    rfl
  diagonal_refl := by
    intros
    exact HEq.rfl
  j := by
    intro mode Γ A motive base total
    rcases total with ⟨⟨⟨value, left⟩, right⟩, path⟩
    rcases path with ⟨path⟩
    cases path
    exact base ⟨value, left⟩
  beta := by
    intro mode Γ A motive base
    funext value
    rcases value with ⟨value, element⟩
    rfl

/-- The internal J eliminator computes on the reflexivity diagonal. -/
theorem familiesIdentityTypes_beta
    {mode : stageModeTheory.Mode} {Γ : familiesCwF.Con mode}
    (A : familiesCwF.Ty Γ)
    (motive : familiesCwF.Ty
      (familiesIdentityTypes.formation.identityContext A))
    (base : familiesCwF.Tm
      (familiesIdentityTypes.formation.firstContext A)
      (familiesCwF.tySub motive (familiesIdentityTypes.diagonal A))) :
    familiesCwF.tmSub
      (familiesIdentityTypes.j A motive base)
      (familiesIdentityTypes.diagonal A) = base :=
  familiesIdentityTypes.beta A motive base

/-- Negative identity witness: false and true have an empty identity fibre. -/
theorem familiesIdentity_false_true_empty :
    IsEmpty
      (@familiesCwF.Tm (stageOfNat 0) PUnit
        (@IdentityFormation.idTy stageModeTheory familiesCwF
          familiesIdentityFormation (stageOfNat 0) PUnit
          (fun _ => Bool) (fun _ => false) (fun _ => true))) := by
  exact ⟨fun impossible =>
    Bool.noConfusion (impossible PUnit.unit).down⟩

/-- A dependent eliminator for a noncollapsed binary inductive type.  The
eliminated section lives over the internally extended context, so the motive
may genuinely depend on the scrutinee. -/
structure BinaryInductiveFamilyWitness (M : ModeTheory) (C : ModalCwF M) where
  mode : M.Mode
  context : C.Con mode
  carrier : C.Ty context
  leftConstructor : C.Tm context carrier
  rightConstructor : C.Tm context carrier
  constructors_distinct : leftConstructor ≠ rightConstructor
  eliminate : (motive : C.Ty (C.ext context carrier)) →
    C.Tm context (C.tySub motive (C.selfExtend leftConstructor)) →
    C.Tm context (C.tySub motive (C.selfExtend rightConstructor)) →
    C.Tm (C.ext context carrier) motive
  beta_left : ∀ (motive : C.Ty (C.ext context carrier))
    (leftCase : C.Tm context
      (C.tySub motive (C.selfExtend leftConstructor)))
    (rightCase : C.Tm context
      (C.tySub motive (C.selfExtend rightConstructor))),
    C.tmSub (eliminate motive leftCase rightCase)
      (C.selfExtend leftConstructor) = leftCase
  beta_right : ∀ (motive : C.Ty (C.ext context carrier))
    (leftCase : C.Tm context
      (C.tySub motive (C.selfExtend leftConstructor)))
    (rightCase : C.Tm context
      (C.tySub motive (C.selfExtend rightConstructor))),
    C.tmSub (eliminate motive leftCase rightCase)
      (C.selfExtend rightConstructor) = rightCase

/-- Boolean induction in the families model supplies a genuinely dependent
eliminator with judgmental computation at both constructors. -/
def familiesBooleanInductive :
    BinaryInductiveFamilyWitness stageModeTheory familiesCwF where
  mode := stageOfNat 0
  context := PUnit
  carrier := fun _ => Bool
  leftConstructor := fun _ => false
  rightConstructor := fun _ => true
  constructors_distinct := by
    intro equalConstructors
    have pointwise := congrFun equalConstructors PUnit.unit
    exact Bool.noConfusion pointwise
  eliminate := by
    intro motive leftCase rightCase value
    rcases value with ⟨base, flag⟩
    cases flag
    · exact leftCase base
    · exact rightCase base
  beta_left := by intros; rfl
  beta_right := by intros; rfl

/-- Positive computation witness for the left constructor. -/
theorem familiesBooleanInductive_beta_left
    (motive : familiesCwF.Ty
      (familiesCwF.ext familiesBooleanInductive.context
        familiesBooleanInductive.carrier))
    (leftCase : familiesCwF.Tm familiesBooleanInductive.context
      (familiesCwF.tySub motive
        (familiesCwF.selfExtend familiesBooleanInductive.leftConstructor)))
    (rightCase : familiesCwF.Tm familiesBooleanInductive.context
      (familiesCwF.tySub motive
        (familiesCwF.selfExtend familiesBooleanInductive.rightConstructor))) :
    familiesCwF.tmSub
      (familiesBooleanInductive.eliminate motive leftCase rightCase)
      (familiesCwF.selfExtend familiesBooleanInductive.leftConstructor) =
        leftCase :=
  familiesBooleanInductive.beta_left motive leftCase rightCase

/-- Negative collapse witness: the two Boolean constructors are distinct. -/
theorem familiesBooleanInductive_not_collapsed :
    familiesBooleanInductive.leftConstructor ≠
      familiesBooleanInductive.rightConstructor :=
  familiesBooleanInductive.constructors_distinct

/-- Witness for `languageCodes`.  The universe decodes to a full intrinsic
carrier of validated presentations.  A separately named selected region has
an exact Pattern codec with both round trips and an outside-image witness.
This separation prevents a finite bridge or one-way renderer from being
mistaken for a codec of all language presentations. -/
structure LanguageCodeWitness (M : ModeTheory) (C : ModalCwF M)
    (model : SpaceModel M C) where
  LanguageValue : Type
  asValidated : LanguageValue →
    Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef
  langCode : C.Tm (C.empty model.baseMode) (C.univ (C.empty model.baseMode))
  languageValueEquiv :
    C.Tm (C.empty model.baseMode) (C.el langCode) ≃ LanguageValue
  SelectedValue : Type
  selectedValue : SelectedValue → LanguageValue
  selectedValue_injective : Function.Injective selectedValue
  encodePattern : SelectedValue → Pattern
  decodePattern : Pattern → Option SelectedValue
  decode_encode : ∀ value,
    decodePattern (encodePattern value) = some value
  encode_decode : ∀ {pattern value},
    decodePattern pattern = some value → encodePattern value = pattern
  outside : Pattern
  outside_not_decoded : decodePattern outside = none

namespace LanguageCodeWitness

/-- The exact Pattern image of the selected language-value region. -/
def IsLanguagePattern
    {M : ModeTheory} {C : ModalCwF M} {model : SpaceModel M C}
    (witness : LanguageCodeWitness M C model) (pattern : Pattern) : Prop :=
  ∃ value, witness.encodePattern value = pattern

/-- Pattern membership in the selected image is equivalent to successful
decoding. -/
theorem isLanguagePattern_iff_decode_ne_none
    {M : ModeTheory} {C : ModalCwF M} {model : SpaceModel M C}
    (witness : LanguageCodeWitness M C model) (pattern : Pattern) :
    witness.IsLanguagePattern pattern ↔ witness.decodePattern pattern ≠ none := by
  constructor
  · rintro ⟨value, rfl⟩
    rw [witness.decode_encode]
    simp
  · intro decoded
    cases result : witness.decodePattern pattern with
    | none => exact (decoded result).elim
    | some value =>
      exact ⟨value, witness.encode_decode result⟩

/-- Every selected value contributes an inhabited code image. -/
theorem image_inhabited
    {M : ModeTheory} {C : ModalCwF M} {model : SpaceModel M C}
    (witness : LanguageCodeWitness M C model) [Nonempty witness.SelectedValue] :
    ∃ pattern, witness.IsLanguagePattern pattern := by
  let value := Classical.choice (inferInstance : Nonempty witness.SelectedValue)
  exact ⟨witness.encodePattern value, value, rfl⟩

/-- The required outside code makes the selected Pattern image proper. -/
theorem image_proper
    {M : ModeTheory} {C : ModalCwF M} {model : SpaceModel M C}
    (witness : LanguageCodeWitness M C model) :
    ¬ witness.IsLanguagePattern witness.outside := by
  rw [witness.isLanguagePattern_iff_decode_ne_none]
  exact fun different => different witness.outside_not_decoded

end LanguageCodeWitness

/-- A strict Tarski-style universe tower.  Codes for level `n` live at level
`n+1`, and decoding lands at level `n`; there is no same-level decoding field.
The distinct-level and nondegeneracy laws rule out a collapsed one-universe
masquerade. -/
structure StratifiedUniverseWitness (M : ModeTheory) (C : ModalCwF M) where
  mode : Nat → M.Mode
  adjacent_distinct : ∀ level, mode level ≠ mode (level + 1)
  decode : (level : Nat) →
    C.Tm (C.empty (mode (level + 1)))
      (C.univ (C.empty (mode (level + 1)))) →
    C.Ty (C.empty (mode level))
  nondegenerate :
    ∃ (level : Nat)
      (left right : C.Tm (C.empty (mode (level + 1)))
        (C.univ (C.empty (mode (level + 1))))),
      decode level left ≠ decode level right

namespace StratifiedUniverseWitness

/-- The level map of a stratified universe witness cannot be constant. -/
theorem no_constant_mode
    {M : ModeTheory} {C : ModalCwF M}
    (tower : StratifiedUniverseWitness M C) :
    ¬ ∃ fixedMode, ∀ level, tower.mode level = fixedMode := by
  rintro ⟨fixedMode, allEqual⟩
  apply tower.adjacent_distinct 0
  exact (allEqual 0).trans (allEqual 1).symm

end StratifiedUniverseWitness

/-! ## §7a Concrete Pattern model and bootstrap-linked universe tower -/

/-- A stable marker used to embed inhabited semantic carriers into the Pattern
space.  The embedding is deliberately visible and narrow: it does not claim
that every semantic type already has a source-faithful Pattern presentation. -/
def familiesPatternMarker : Pattern :=
  .fvar "native-type-inhabitant"

/-- A second Pattern gives a negative membership witness for the designated
proper space. -/
def familiesPatternOutside : Pattern :=
  .fvar "outside-native-type-inhabitant"

theorem familiesPatternOutside_ne_marker :
    familiesPatternOutside ≠ familiesPatternMarker := by
  decide

/-- Closed semantic types denote the singleton marker exactly when their
carrier is inhabited.  This gives a constructive, noncollapsed Pattern-space
semantics without pretending that the eventual source-faithful elaboration
map has already been built. -/
def familiesPatternInterp
    (A : familiesCwF.Ty
      (familiesCwF.empty (stageOfNat 0))) : Space :=
  fun pattern => Nonempty (A PUnit.unit) ∧ pattern = familiesPatternMarker

/-- The concrete families model is genuinely noncollapsed: `Empty` and
`PUnit` denote different Pattern spaces. -/
def familiesPatternSpaceModel : SpaceModel stageModeTheory familiesCwF where
  baseMode := stageOfNat 0
  interp := familiesPatternInterp
  nondegenerate := by
    refine ⟨(fun _ => Empty), (fun _ => PUnit), ?_⟩
    intro collapsed
    have unitMember :
        familiesPatternInterp (fun _ => PUnit) familiesPatternMarker :=
      ⟨⟨PUnit.unit⟩, rfl⟩
    have emptyMember :
        familiesPatternInterp (fun _ => Empty) familiesPatternMarker := by
      rw [collapsed]
      exact unitMember
    rcases emptyMember.1 with ⟨impossible⟩
    exact impossible.elim

/-- The first proper space is represented by the unit code. -/
def familiesSpaceCode :
    familiesCwF.Tm
      (familiesCwF.empty familiesPatternSpaceModel.baseMode)
      (familiesCwF.univ
        (familiesCwF.empty familiesPatternSpaceModel.baseMode)) :=
  fun _ => .unit

/-- The unit code decodes to an inhabited proper singleton space, not the
empty space and not the dynamic top space. -/
def familiesSpaceCodeWitness :
    SpaceCodeWitness stageModeTheory familiesCwF familiesPatternSpaceModel where
  spaceCode := familiesSpaceCode
  decodesToProperSpace := by
    intro collapsed
    have outsideMember :
        familiesPatternSpaceModel.interp
          (familiesCwF.el familiesSpaceCode) familiesPatternOutside := by
      rw [collapsed]
      trivial
    exact familiesPatternOutside_ne_marker outsideMember.2

/-- The universe contains a literal code for the runtime Pattern carrier. -/
def familiesRuntimePatternCode :
    familiesCwF.Tm
      (familiesCwF.empty familiesPatternSpaceModel.baseMode)
      (familiesCwF.univ
        (familiesCwF.empty familiesPatternSpaceModel.baseMode)) :=
  fun _ => .pattern

theorem familiesRuntimePatternCode_decodes :
    familiesCwF.el familiesRuntimePatternCode = (fun _ => Pattern) :=
  rfl

/-! ### Intrinsic validated-language values and their selected Pattern image -/

/-- The universe contains the full carrier of validated five-field language
presentations, not merely rendered names or opaque handles. -/
def familiesValidatedLanguageCode :
    familiesCwF.Tm
      (familiesCwF.empty familiesPatternSpaceModel.baseMode)
      (familiesCwF.univ
        (familiesCwF.empty familiesPatternSpaceModel.baseMode)) :=
  fun _ => .validatedLanguage

theorem familiesValidatedLanguageCode_decodes :
    familiesCwF.el familiesValidatedLanguageCode =
      (fun _ => Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef) :=
  rfl

/-- The exact selected region initially exposed as Pattern data.  This is a
two-point region of the full intrinsic carrier, not a claim to serialize every
future presentation. -/
inductive CurrentLanguageHandle where
  | zero
  | prime
  deriving DecidableEq, Repr

instance : Nonempty CurrentLanguageHandle := ⟨.zero⟩

def currentLanguagePresentation : CurrentLanguageHandle →
    Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef
  | .zero =>
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroPresentation
  | .prime =>
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation

/-- Today's Zero and Prime presentations are distinct objects. -/
theorem currentZeroPresentation_ne_currentPrimePresentation :
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroPresentation ≠
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation := by
  intro equal
  have names := congrArg
    (fun presentation : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef =>
      presentation.language.name) equal
  change "metta-zero-query-kernel" = "metta-prime-spec-probe" at names
  have distinct : "metta-zero-query-kernel" ≠ "metta-prime-spec-probe" := by decide
  exact distinct names

theorem currentLanguagePresentation_injective :
    Function.Injective currentLanguagePresentation := by
  intro first second equal
  cases first <;> cases second
  · rfl
  · exact (currentZeroPresentation_ne_currentPrimePresentation equal).elim
  · exact (currentZeroPresentation_ne_currentPrimePresentation equal.symm).elim
  · rfl

def currentLanguagePattern : CurrentLanguageHandle → Pattern
  | .zero => .fvar "native-language/zero"
  | .prime => .fvar "native-language/prime"

def decodeCurrentLanguagePattern (pattern : Pattern) :
    Option CurrentLanguageHandle :=
  if pattern = currentLanguagePattern .zero then some .zero
  else if pattern = currentLanguagePattern .prime then some .prime
  else none

theorem decodeCurrentLanguagePattern_encode (value : CurrentLanguageHandle) :
    decodeCurrentLanguagePattern (currentLanguagePattern value) = some value := by
  cases value <;> decide

theorem currentLanguagePattern_decode
    {pattern : Pattern} {value : CurrentLanguageHandle}
    (decoded : decodeCurrentLanguagePattern pattern = some value) :
    currentLanguagePattern value = pattern := by
  unfold decodeCurrentLanguagePattern at decoded
  split at decoded
  · rename_i isZero
    have valueIsZero : CurrentLanguageHandle.zero = value :=
      Option.some.inj decoded
    subst value
    exact isZero.symm
  · split at decoded
    · rename_i isPrime
      have valueIsPrime : CurrentLanguageHandle.prime = value :=
        Option.some.inj decoded
      subst value
      exact isPrime.symm
    · cases decoded

def outsideCurrentLanguagePattern : Pattern :=
  .fvar "not-a-native-language-code"

theorem outsideCurrentLanguagePattern_not_decoded :
    decodeCurrentLanguagePattern outsideCurrentLanguagePattern = none := by
  decide

/-- Full intrinsic language values plus an exact, explicitly selected Pattern
codec. -/
def familiesLanguageCodeWitness :
    LanguageCodeWitness stageModeTheory familiesCwF familiesPatternSpaceModel where
  LanguageValue := Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef
  asValidated := _root_.id
  langCode := familiesValidatedLanguageCode
  languageValueEquiv :=
    { toFun := fun term => term PUnit.unit
      invFun := fun value _ => value
      left_inv := by intro term; funext value; cases value; rfl
      right_inv := by intro value; rfl }
  SelectedValue := CurrentLanguageHandle
  selectedValue := currentLanguagePresentation
  selectedValue_injective := currentLanguagePresentation_injective
  encodePattern := currentLanguagePattern
  decodePattern := decodeCurrentLanguagePattern
  decode_encode := decodeCurrentLanguagePattern_encode
  encode_decode := currentLanguagePattern_decode
  outside := outsideCurrentLanguagePattern
  outside_not_decoded := outsideCurrentLanguagePattern_not_decoded

/-- Positive image witness for the current Prime presentation. -/
theorem currentPrimePattern_is_languagePattern :
    familiesLanguageCodeWitness.IsLanguagePattern
      (currentLanguagePattern .prime) :=
  ⟨.prime, rfl⟩

/-- Negative image witness: the selected codec rejects an unrelated Pattern. -/
theorem outsideCurrentLanguagePattern_not_languagePattern :
    ¬ familiesLanguageCodeWitness.IsLanguagePattern
      outsideCurrentLanguagePattern :=
  familiesLanguageCodeWitness.image_proper

/-! ### Structural language manipulation in the common admission algebra -/

/-- Authored constructors form an intrinsically validated carrier: membership
in the selected presentation is part of every value. -/
def authoredConstructorAdmissionObject
    (presentation : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef) :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.AdmissionObject where
  Carrier := Mettapedia.GSLT.LanguageDef.StructuralMorphism.DeclaredConstructor
    presentation
  Meaning := fun _ => True

/-- Every structural presentation map acts directly on its intrinsically
typed constructor values and hence supplies a common admission arrow. -/
def structuralConstructorAdmission
    {source target : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef}
    (morphism : Mettapedia.GSLT.LanguageDef.StructuralMorphism source target) :
    authoredConstructorAdmissionObject source ⟶
      authoredConstructorAdmissionObject target where
  run := morphism.mapConstructor
  preserves := fun _ _ => trivial

/-- A real constructor value in today's Zero presentation. -/
def currentZeroEquationConstructor :
    Mettapedia.GSLT.LanguageDef.StructuralMorphism.DeclaredConstructor
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroPresentation :=
  ⟨Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor, by
    change List.Mem Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor
      [Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor,
       Mettapedia.Languages.MeTTa.MeTTaZero.queryRequestConstructor,
       Mettapedia.Languages.MeTTa.MeTTaZero.queryAnswerConstructor,
       Mettapedia.Languages.MeTTa.MeTTaZero.evaluationRequestConstructor,
       Mettapedia.Languages.MeTTa.MeTTaZero.evaluationAnswerConstructor]
    exact List.mem_cons_self⟩

/-- Positive operational content: the admitted current Zero-to-Prime map
really transports an authored constructor value into Prime. -/
theorem currentZeroToPrime_maps_equationConstructor :
    ((structuralConstructorAdmission
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroToPrimePresentation).run
        currentZeroEquationConstructor).1 =
      Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor := by
  exact Mettapedia.GSLT.LanguageDef.mapGrammarRule_id _

/-- Audit package for first-class language manipulation.  Its map is the live
proper Zero-to-Prime structural inclusion; the reverse identity-symbol map is
required to remain impossible. -/
structure LanguageManipulationWitness where
  codes : LanguageCodeWitness stageModeTheory familiesCwF
    familiesPatternSpaceModel
  structural : Mettapedia.GSLT.LanguageDef.StructuralMorphism
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroPresentation
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
  endpointsDistinct :
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroPresentation ≠
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
  sourceConstructor :
    Mettapedia.GSLT.LanguageDef.StructuralMorphism.DeclaredConstructor
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroPresentation
  mapsSourceConstructor :
    ((structuralConstructorAdmission structural).run sourceConstructor).1 =
      Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor
  noIdentityReverse :
    ¬ ∃ retraction : Mettapedia.GSLT.LanguageDef.StructuralMorphism
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroPresentation,
      retraction.symbols = Mettapedia.GSLT.LanguageDef.LanguageDefSymbolMap.id

/-- O13's intrinsic carrier, exact selected Pattern image, nonidentity typed
operation, and negative reverse witness. -/
def nativeLanguageManipulationWitness : LanguageManipulationWitness where
  codes := familiesLanguageCodeWitness
  structural :=
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroToPrimePresentation
  endpointsDistinct := currentZeroPresentation_ne_currentPrimePresentation
  sourceConstructor := currentZeroEquationConstructor
  mapsSourceConstructor := currentZeroToPrime_maps_equationConstructor
  noIdentityReverse :=
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.no_identity_symbol_retraction

/-! ### Executable λΠ fragment inside the universe

The existing universe-free Pure λΠ carrier is a first-class code in the
families universe.  Its total injection into the LF carrier already commutes
with lifting, substitution, normalization, and executable βη conversion.
The declarations below connect that live bridge to the native universe rather
than duplicating a second λΠ implementation. -/

/-- A closed universe code for the live executable λΠ fragment. -/
def familiesLambdaPiCode :
    familiesCwF.Tm
      (familiesCwF.empty familiesPatternSpaceModel.baseMode)
      (familiesCwF.univ
        (familiesCwF.empty familiesPatternSpaceModel.baseMode)) :=
  fun _ => .lambdaPiExpr

theorem familiesLambdaPiCode_decodes :
    familiesCwF.el familiesLambdaPiCode =
      (fun _ => Mettapedia.GSLT.LanguageDef.Pure.Expr) :=
  rfl

/-- The native-universe λΠ carrier enters the live LF checker through the
existing total, injective encoding. -/
def lambdaPiToLF
    (expression :
      (familiesCwF.el familiesLambdaPiCode) PUnit.unit) :
    Mettapedia.GSLT.LanguageDef.LF.Term :=
  Mettapedia.GSLT.LanguageDef.LFPureCorrespondence.encodeExpr expression

theorem lambdaPiToLF_injective : Function.Injective lambdaPiToLF :=
  Mettapedia.GSLT.LanguageDef.LFPureCorrespondence.encodeExpr_injective

/-- Dependent-product syntax is preserved, not erased to an arrow tag. -/
theorem lambdaPiToLF_pi (domain body :
    (familiesCwF.el familiesLambdaPiCode) PUnit.unit) :
    lambdaPiToLF (.pi domain body) =
      .pi (lambdaPiToLF domain) (lambdaPiToLF body) :=
  rfl

/-- Capture-avoiding substitution is preserved by the native-universe to LF
map. -/
theorem lambdaPiToLF_subst (index : Nat)
    (replacement expression :
      (familiesCwF.el familiesLambdaPiCode) PUnit.unit) :
    lambdaPiToLF
        (Mettapedia.GSLT.LanguageDef.Pure.Expr.subst
          index replacement expression) =
      Mettapedia.GSLT.LanguageDef.LFTyping.subst index
        (lambdaPiToLF replacement) (lambdaPiToLF expression) :=
  Mettapedia.GSLT.LanguageDef.LFPureCorrespondence.encodeExpr_subst
    index replacement expression

/-- Conversion on the terminating λΠ fragment is equality after its
executable βη evaluation. -/
def LambdaPiEvaluatedConversion
    (left right : (familiesCwF.el familiesLambdaPiCode) PUnit.unit) : Prop :=
  Mettapedia.GSLT.LanguageDef.PureBetaEta.normalForm left =
    Mettapedia.GSLT.LanguageDef.PureBetaEta.normalForm right

/-- Exact decision procedure for evaluated λΠ conversion. -/
def lambdaPiDecidedConversion :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.DecidedRelation
      _ LambdaPiEvaluatedConversion where
  decide := Mettapedia.GSLT.LanguageDef.PureBetaEta.convBool
  correct := by
    intro left right
    simp [LambdaPiEvaluatedConversion,
      Mettapedia.GSLT.LanguageDef.PureBetaEta.convBool]

/-- Evaluation-based conversion commutes exactly with the existing LF
kernel on the embedded fragment. -/
theorem lambdaPi_conversion_commutes
    (left right : (familiesCwF.el familiesLambdaPiCode) PUnit.unit) :
    lambdaPiDecidedConversion.decide left right =
      Mettapedia.GSLT.LanguageDef.LFBetaEta.convBool []
        Mettapedia.GSLT.LanguageDef.PureBetaEta.normalizationFuel
        (lambdaPiToLF left) (lambdaPiToLF right) :=
  Mettapedia.GSLT.LanguageDef.LFPureCorrespondence.encodeExpr_convBool
    left right

/-- Acceptance by evaluated conversion has an independently authored
common-reduct witness. -/
theorem lambdaPi_decision_sound
    {left right : (familiesCwF.el familiesLambdaPiCode) PUnit.unit}
    (accepted : lambdaPiDecidedConversion.decide left right = true) :
    Mettapedia.GSLT.LanguageDef.PureBetaEta.Conv left right :=
  Mettapedia.GSLT.LanguageDef.PureBetaEta.convBool_sound accepted

/-- Positive β-conversion witness in the universe-coded fragment. -/
theorem lambdaPi_beta_positive :
    lambdaPiDecidedConversion.decide
      (.app (.lam .sort (.bvar 0)) .sort) .sort = true := by
  decide

/-- Positive η-conversion witness in the universe-coded fragment. -/
theorem lambdaPi_eta_positive :
    lambdaPiDecidedConversion.decide
      (.lam .sort (.app (.bvar 1) (.bvar 0))) (.bvar 0) = true := by
  decide

/-- Negative witness: a free variable and the universe sort do not share the
computed normal form. -/
theorem lambdaPi_unrelated_negative :
    lambdaPiDecidedConversion.decide (.bvar 0) .sort = false := by
  decide

/-- The complete O2 witness bundle.  It keeps the semantic Π structure and
the executable λΠ carrier distinct: their semantic-CwF comparison remains
open, while O2 asks only for a genuine Pattern model and an embedded,
evaluation-decided Π fragment. -/
structure PatternLambdaPiRealization where
  model : SpaceModel stageModeTheory familiesCwF
  properCode : SpaceCodeWitness stageModeTheory familiesCwF model
  patternCode : familiesCwF.Tm
    (familiesCwF.empty model.baseMode)
    (familiesCwF.univ (familiesCwF.empty model.baseMode))
  patternCode_decodes :
    familiesCwF.el patternCode = (fun _ => Pattern)
  lambdaPiCode : familiesCwF.Tm
    (familiesCwF.empty model.baseMode)
    (familiesCwF.univ (familiesCwF.empty model.baseMode))
  lambdaPiCode_decodes :
    familiesCwF.el lambdaPiCode =
      (fun _ => Mettapedia.GSLT.LanguageDef.Pure.Expr)
  conversion : Mettapedia.GSLT.LanguageDef.NIKMetalogic.DecidedRelation
    _ LambdaPiEvaluatedConversion
  carrierFaithful : Function.Injective lambdaPiToLF
  piPreserved : ∀ domain body,
    lambdaPiToLF (.pi domain body) =
      .pi (lambdaPiToLF domain) (lambdaPiToLF body)
  conversionCommutes : ∀ left right,
    conversion.decide left right =
      Mettapedia.GSLT.LanguageDef.LFBetaEta.convBool []
        Mettapedia.GSLT.LanguageDef.PureBetaEta.normalizationFuel
        (lambdaPiToLF left) (lambdaPiToLF right)
  betaAccepted : conversion.decide
    (.app (.lam .sort (.bvar 0)) .sort) .sort = true
  unrelatedRejected : conversion.decide (.bvar 0) .sort = false

/-- The concrete O2 realization.  Its positive and negative conversion fields
prevent the executable fragment from collapsing to an always-accepting or
always-rejecting checker. -/
def familiesPatternLambdaPiRealization : PatternLambdaPiRealization where
  model := familiesPatternSpaceModel
  properCode := familiesSpaceCodeWitness
  patternCode := familiesRuntimePatternCode
  patternCode_decodes := familiesRuntimePatternCode_decodes
  lambdaPiCode := familiesLambdaPiCode
  lambdaPiCode_decodes := familiesLambdaPiCode_decodes
  conversion := lambdaPiDecidedConversion
  carrierFaithful := lambdaPiToLF_injective
  piPreserved := lambdaPiToLF_pi
  conversionCommutes := lambdaPi_conversion_commutes
  betaAccepted := lambdaPi_beta_positive
  unrelatedRejected := lambdaPi_unrelated_negative

/-- Empty and unit codes, available at every stage. -/
def familiesEmptyCode (level : Nat) :
    familiesCwF.Tm (familiesCwF.empty (stageOfNat (level + 1)))
      (familiesCwF.univ (familiesCwF.empty (stageOfNat (level + 1)))) :=
  fun _ => .empty

def familiesUnitCode (level : Nat) :
    familiesCwF.Tm (familiesCwF.empty (stageOfNat (level + 1)))
      (familiesCwF.univ (familiesCwF.empty (stageOfNat (level + 1)))) :=
  fun _ => .unit

/-- A noncollapsed Tarski tower.  Stage `n+1` contains small codes whose
decoding is a type at stage `n`; the empty and unit codes stay distinct. -/
def familiesUniverseTower :
    StratifiedUniverseWitness stageModeTheory familiesCwF where
  mode := stageOfNat
  adjacent_distinct := by
    intro level equality
    exact Nat.ne_of_lt (Nat.lt_succ_self level)
      (stageOfNat_injective equality)
  decode := fun _ code _ => (code PUnit.unit).decode
  nondegenerate := by
    refine ⟨0, familiesEmptyCode 0, familiesUnitCode 0, ?_⟩
    intro collapsed
    have carrierEquality : Empty = PUnit :=
      congrFun collapsed PUnit.unit
    have impossible : Nonempty Empty := by
      rw [carrierEquality]
      exact ⟨PUnit.unit⟩
    rcases impossible with ⟨value⟩
    exact value.elim

/-- The statement family classified by universe contracts: a statement at
level `n` is a semantic type at that same stage. -/
abbrev FamiliesUniverseStatement (level : Nat) : Type 1 :=
  familiesCwF.Ty (familiesCwF.empty (stageOfNat level))

/-- Decoding a universe code at level `n+1` produces a NIK bootstrap contract
whose target is exactly level `n`. -/
def familiesUniverseLowerContract (level : Nat)
    (code : familiesCwF.Tm (familiesCwF.empty (stageOfNat (level + 1)))
      (familiesCwF.univ
        (familiesCwF.empty (stageOfNat (level + 1))))) :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.LowerContract
      FamiliesUniverseStatement (level + 1) where
  targetLevel := ⟨level, Nat.lt_succ_self level⟩
  kind := .modelSound
  statement := familiesUniverseTower.decode level code

@[simp] theorem familiesUniverseLowerContract_target (level : Nat)
    (code : familiesCwF.Tm (familiesCwF.empty (stageOfNat (level + 1)))
      (familiesCwF.univ
        (familiesCwF.empty (stageOfNat (level + 1))))) :
    (familiesUniverseLowerContract level code).targetLevel.val = level :=
  rfl

/-- Positive and negative witnesses meet at the bootstrap seam: both first
universe codes yield well-stratified contracts, but their lower statements
remain distinct. -/
theorem firstUniverseLowerContracts_distinct :
    familiesUniverseLowerContract 0 (familiesEmptyCode 0) ≠
      familiesUniverseLowerContract 0 (familiesUnitCode 0) := by
  intro contractsEqual
  let extractStatement :
      Mettapedia.GSLT.LanguageDef.NIKMetalogic.LowerContract
          FamiliesUniverseStatement 1 →
        FamiliesUniverseStatement 0 := fun contract => by
      have targetIsZero : contract.targetLevel.val = 0 := by
        exact Nat.eq_zero_of_le_zero
          (Nat.le_of_lt_succ contract.targetLevel.isLt)
      simpa [targetIsZero] using contract.statement
  have statementEquality := congrArg extractStatement contractsEqual
  have carrierEquality : Empty = PUnit :=
    congrFun statementEquality PUnit.unit
  have impossible : Nonempty Empty := by
    rw [carrierEquality]
    exact ⟨PUnit.unit⟩
  rcases impossible with ⟨value⟩
  exact value.elim

/-! ## §7b Native intensional conversion

The current native conversion carrier joins the executable λΠ fragment,
universe codes, and runtime Patterns.  The selected equality architecture
below fixes an intensional kernel core.  It deliberately does not identify
that core with observational equality, UIP, cubical structure, or univalence;
such relations require separately named extension profiles. -/

inductive NativeConversionTerm where
  | lambdaPi : Mettapedia.GSLT.LanguageDef.Pure.Expr → NativeConversionTerm
  | code : FamiliesCode → NativeConversionTerm
  | pattern : Pattern → NativeConversionTerm
  deriving DecidableEq, Repr

/-- Compute a canonical form.  Codes and Patterns are already values; the
λΠ branch uses the live terminating βη evaluator. -/
def NativeConversionTerm.normalForm :
    NativeConversionTerm → NativeConversionTerm
  | .lambdaPi expression => .lambdaPi
      (Mettapedia.GSLT.LanguageDef.PureBetaEta.normalForm expression)
  | .code familyCode => NativeConversionTerm.code familyCode
  | .pattern runtimePattern => NativeConversionTerm.pattern runtimePattern

/-- Declarative conversion article: both terms compute to one named common
canonical form. -/
def NativeConverts (left right : NativeConversionTerm) : Prop :=
  ∃ common,
    left.normalForm = common ∧ right.normalForm = common

/-- Exact computing decision for native intensional conversion. -/
def nativeDecidedConversion :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.DecidedRelation
      NativeConversionTerm NativeConverts where
  decide := fun left right => decide (left.normalForm = right.normalForm)
  correct := by
    intro left right
    rw [decide_eq_true_eq]
    constructor
    · intro equal
      exact ⟨left.normalForm, rfl, equal.symm⟩
    · rintro ⟨common, leftEqual, rightEqual⟩
      exact leftEqual.trans rightEqual.symm

theorem nativeConversion_lambdaPi_agrees (left right :
    Mettapedia.GSLT.LanguageDef.Pure.Expr) :
    nativeDecidedConversion.decide (.lambdaPi left) (.lambdaPi right) =
      lambdaPiDecidedConversion.decide left right := by
  apply Bool.eq_iff_iff.mpr
  rw [nativeDecidedConversion.correct, lambdaPiDecidedConversion.correct]
  constructor
  · rintro ⟨common, leftEqual, rightEqual⟩
    simpa [LambdaPiEvaluatedConversion,
      NativeConversionTerm.normalForm] using
        leftEqual.trans rightEqual.symm
  · intro equal
    exact ⟨.lambdaPi
      (Mettapedia.GSLT.LanguageDef.PureBetaEta.normalForm left),
      rfl, congrArg NativeConversionTerm.lambdaPi equal.symm⟩

theorem nativeConversion_beta_positive :
    nativeDecidedConversion.decide
      (.lambdaPi (.app (.lam .sort (.bvar 0)) .sort))
      (.lambdaPi .sort) = true := by
  rw [nativeConversion_lambdaPi_agrees]
  exact lambdaPi_beta_positive

theorem nativeConversion_code_pattern_negative :
    nativeDecidedConversion.decide (.code .pattern)
      (.pattern familiesPatternMarker) = false := by
  simp [nativeDecidedConversion, NativeConversionTerm.normalForm]

/-! ## §7c Equality-neutral recursion for the intrinsic Pure syntax

Full initiality among semantic `ModalCwF` models is not proved here.  The raw
binding signature is independent of conversion, however.  This section proves
its genuine recursion and uniqueness theorem, including the binder-indexed
operations.  It is therefore an initiality precursor rather than a disguised
semantic self-model.

The algebra deliberately contains every live `PureTm` constructor, including
global constants, dependent products, dependent sums, and identity terms. -/

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax

/-- An algebra for the complete raw, intrinsically scoped Pure signature. -/
structure PureRawAlgebra where
  Carrier : Nat → Type uRaw
  var : {n : Nat} → Fin n → Carrier n
  const : {n : Nat} → DeclName → Carrier n
  u0 : {n : Nat} → Carrier n
  u1 : {n : Nat} → Carrier n
  pi : {n : Nat} → Carrier n → Carrier (n + 1) → Carrier n
  sigma : {n : Nat} → Carrier n → Carrier (n + 1) → Carrier n
  id : {n : Nat} → Carrier n → Carrier n → Carrier n → Carrier n
  lam : {n : Nat} → Carrier (n + 1) → Carrier n
  app : {n : Nat} → Carrier n → Carrier n → Carrier n
  pair : {n : Nat} → Carrier n → Carrier n → Carrier n
  fst : {n : Nat} → Carrier n → Carrier n
  snd : {n : Nat} → Carrier n → Carrier n
  refl : {n : Nat} → Carrier n → Carrier n

/-- Preservation of the complete raw Pure signature by an indexed map. -/
structure PureRawPreserves
    (source : PureRawAlgebra.{uRaw})
    (target : PureRawAlgebra.{uRawTarget})
    (map : {n : Nat} → source.Carrier n → target.Carrier n) : Prop where
  map_var : ∀ {n} (index : Fin n), map (source.var index) = target.var index
  map_const : ∀ {n} name,
    map (source.const (n := n) name) = target.const name
  map_u0 : ∀ {n}, map (source.u0 (n := n)) = target.u0
  map_u1 : ∀ {n}, map (source.u1 (n := n)) = target.u1
  map_pi : ∀ {n} (domain : source.Carrier n)
      (body : source.Carrier (n + 1)),
    map (source.pi domain body) = target.pi (map domain) (map body)
  map_sigma : ∀ {n} (domain : source.Carrier n)
      (body : source.Carrier (n + 1)),
    map (source.sigma domain body) = target.sigma (map domain) (map body)
  map_id : ∀ {n} (type left right : source.Carrier n),
    map (source.id type left right) =
      target.id (map type) (map left) (map right)
  map_lam : ∀ {n} (body : source.Carrier (n + 1)),
    map (source.lam body) = target.lam (map body)
  map_app : ∀ {n} (function argument : source.Carrier n),
    map (source.app function argument) = target.app (map function) (map argument)
  map_pair : ∀ {n} (left right : source.Carrier n),
    map (source.pair left right) = target.pair (map left) (map right)
  map_fst : ∀ {n} (pair : source.Carrier n),
    map (source.fst pair) = target.fst (map pair)
  map_snd : ∀ {n} (pair : source.Carrier n),
    map (source.snd pair) = target.snd (map pair)
  map_refl : ∀ {n} (term : source.Carrier n),
    map (source.refl term) = target.refl (map term)

/-- A homomorphism of raw Pure algebras. -/
structure PureRawHom
    (source : PureRawAlgebra.{uRaw})
    (target : PureRawAlgebra.{uRawTarget}) where
  map : {n : Nat} → source.Carrier n → target.Carrier n
  preserves : PureRawPreserves source target map

namespace PureRawHom

/-- Identity interpretation of a raw Pure algebra. -/
def id (algebra : PureRawAlgebra.{uRaw}) : PureRawHom algebra algebra where
  map := fun term => term
  preserves := by
    constructor <;> intros <;> rfl

/-- Composition of raw Pure-algebra interpretations. -/
def comp
    {first : PureRawAlgebra.{uRaw}}
    {middle : PureRawAlgebra.{uRawTarget}}
    {last : PureRawAlgebra.{uNativeClaim}}
    (earlier : PureRawHom first middle)
    (later : PureRawHom middle last) :
    PureRawHom first last where
  map := fun term => later.map (earlier.map term)
  preserves := by
    constructor
    · intro n index
      rw [earlier.preserves.map_var, later.preserves.map_var]
    · intro n name
      rw [earlier.preserves.map_const, later.preserves.map_const]
    · intro n
      rw [earlier.preserves.map_u0, later.preserves.map_u0]
    · intro n
      rw [earlier.preserves.map_u1, later.preserves.map_u1]
    · intro n domain body
      rw [earlier.preserves.map_pi, later.preserves.map_pi]
    · intro n domain body
      rw [earlier.preserves.map_sigma, later.preserves.map_sigma]
    · intro n type left right
      rw [earlier.preserves.map_id, later.preserves.map_id]
    · intro n body
      rw [earlier.preserves.map_lam, later.preserves.map_lam]
    · intro n function argument
      rw [earlier.preserves.map_app, later.preserves.map_app]
    · intro n left right
      rw [earlier.preserves.map_pair, later.preserves.map_pair]
    · intro n pair
      rw [earlier.preserves.map_fst, later.preserves.map_fst]
    · intro n pair
      rw [earlier.preserves.map_snd, later.preserves.map_snd]
    · intro n term
      rw [earlier.preserves.map_refl, later.preserves.map_refl]

end PureRawHom

@[ext] theorem PureRawHom.ext
    {source : PureRawAlgebra.{uRaw}}
    {target : PureRawAlgebra.{uRawTarget}}
    (left right : PureRawHom source target)
    (mapsEqual : ∀ {n} (term : source.Carrier n),
      left.map term = right.map term) :
    left = right := by
  cases left with
  | mk leftMap leftPreserves =>
    cases right with
    | mk rightMap rightPreserves =>
      have mapEquality :
          (@leftMap : (n : Nat) → source.Carrier n → target.Carrier n) =
            @rightMap := by
        funext n term
        exact mapsEqual (n := n) term
      cases mapEquality
      rfl

@[simp] theorem PureRawHom.id_comp
    {source : PureRawAlgebra.{uRaw}}
    {target : PureRawAlgebra.{uRawTarget}}
    (hom : PureRawHom source target) :
    PureRawHom.comp (PureRawHom.id source) hom = hom := by
  apply PureRawHom.ext
  intro n term
  rfl

@[simp] theorem PureRawHom.comp_id
    {source : PureRawAlgebra.{uRaw}}
    {target : PureRawAlgebra.{uRawTarget}}
    (hom : PureRawHom source target) :
    PureRawHom.comp hom (PureRawHom.id target) = hom := by
  apply PureRawHom.ext
  intro n term
  rfl

theorem PureRawHom.comp_assoc
    {first : PureRawAlgebra.{uRaw}}
    {second : PureRawAlgebra.{uRawTarget}}
    {third : PureRawAlgebra.{uNativeClaim}}
    {fourth : PureRawAlgebra.{uNativeProof}}
    (firstHom : PureRawHom first second)
    (secondHom : PureRawHom second third)
    (thirdHom : PureRawHom third fourth) :
    PureRawHom.comp (PureRawHom.comp firstHom secondHom) thirdHom =
      PureRawHom.comp firstHom (PureRawHom.comp secondHom thirdHom) := by
  apply PureRawHom.ext
  intro n term
  rfl

/-- The live intrinsic Pure syntax as an algebra of its raw signature. -/
def pureSyntaxAlgebra : PureRawAlgebra where
  Carrier := PureTm
  var := PureTm.var
  const := PureTm.const
  u0 := PureTm.u0
  u1 := PureTm.u1
  pi := PureTm.pi
  sigma := PureTm.sigma
  id := PureTm.id
  lam := PureTm.lam
  app := PureTm.app
  pair := PureTm.pair
  fst := PureTm.fst
  snd := PureTm.snd
  refl := PureTm.refl

/-- Structural interpretation of intrinsic Pure syntax in any raw algebra. -/
def pureRawFold (target : PureRawAlgebra.{uRawTarget}) :
    {n : Nat} → PureTm n → target.Carrier n
  | _, .var index => target.var index
  | _, .const name => target.const name
  | _, .u0 => target.u0
  | _, .u1 => target.u1
  | _, .pi domain body =>
      target.pi (pureRawFold target domain) (pureRawFold target body)
  | _, .sigma domain body =>
      target.sigma (pureRawFold target domain) (pureRawFold target body)
  | _, .id type left right =>
      target.id (pureRawFold target type) (pureRawFold target left)
        (pureRawFold target right)
  | _, .lam body => target.lam (pureRawFold target body)
  | _, .app function argument =>
      target.app (pureRawFold target function) (pureRawFold target argument)
  | _, .pair left right =>
      target.pair (pureRawFold target left) (pureRawFold target right)
  | _, .fst pair => target.fst (pureRawFold target pair)
  | _, .snd pair => target.snd (pureRawFold target pair)
  | _, .refl term => target.refl (pureRawFold target term)

/-- The structural fold is a raw Pure-algebra homomorphism. -/
def pureRawFoldHom (target : PureRawAlgebra.{uRawTarget}) :
    PureRawHom pureSyntaxAlgebra target where
  map := pureRawFold target
  preserves := by
    constructor <;> intros <;> rfl

/-- Any raw Pure-algebra homomorphism agrees pointwise with structural fold. -/
theorem pureRawFold_unique_pointwise
    (target : PureRawAlgebra.{uRawTarget})
    (hom : PureRawHom pureSyntaxAlgebra target) :
    ∀ {n} (term : PureTm n), hom.map term = pureRawFold target term := by
  intro n term
  induction term with
  | var index => exact hom.preserves.map_var index
  | const name => exact hom.preserves.map_const name
  | u0 => exact hom.preserves.map_u0
  | u1 => exact hom.preserves.map_u1
  | pi domain body domainIH bodyIH =>
      calc
        hom.map (PureTm.pi domain body) =
            target.pi (hom.map domain) (hom.map body) := by
          simpa only [pureSyntaxAlgebra] using
            hom.preserves.map_pi domain body
        _ = target.pi (pureRawFold target domain)
            (pureRawFold target body) := by rw [domainIH, bodyIH]
        _ = pureRawFold target (PureTm.pi domain body) := rfl
  | sigma domain body domainIH bodyIH =>
      calc
        hom.map (PureTm.sigma domain body) =
            target.sigma (hom.map domain) (hom.map body) := by
          simpa only [pureSyntaxAlgebra] using
            hom.preserves.map_sigma domain body
        _ = target.sigma (pureRawFold target domain)
            (pureRawFold target body) := by rw [domainIH, bodyIH]
        _ = pureRawFold target (PureTm.sigma domain body) := rfl
  | id type left right typeIH leftIH rightIH =>
      calc
        hom.map (PureTm.id type left right) =
            target.id (hom.map type) (hom.map left) (hom.map right) := by
          simpa only [pureSyntaxAlgebra] using
            hom.preserves.map_id type left right
        _ = target.id (pureRawFold target type) (pureRawFold target left)
            (pureRawFold target right) := by rw [typeIH, leftIH, rightIH]
        _ = pureRawFold target (PureTm.id type left right) := rfl
  | lam body bodyIH =>
      calc
        hom.map (PureTm.lam body) = target.lam (hom.map body) := by
          simpa only [pureSyntaxAlgebra] using hom.preserves.map_lam body
        _ = target.lam (pureRawFold target body) := by rw [bodyIH]
        _ = pureRawFold target (PureTm.lam body) := rfl
  | app function argument functionIH argumentIH =>
      calc
        hom.map (PureTm.app function argument) =
            target.app (hom.map function) (hom.map argument) := by
          simpa only [pureSyntaxAlgebra] using
            hom.preserves.map_app function argument
        _ = target.app (pureRawFold target function)
            (pureRawFold target argument) := by rw [functionIH, argumentIH]
        _ = pureRawFold target (PureTm.app function argument) := rfl
  | pair left right leftIH rightIH =>
      calc
        hom.map (PureTm.pair left right) =
            target.pair (hom.map left) (hom.map right) := by
          simpa only [pureSyntaxAlgebra] using
            hom.preserves.map_pair left right
        _ = target.pair (pureRawFold target left)
            (pureRawFold target right) := by rw [leftIH, rightIH]
        _ = pureRawFold target (PureTm.pair left right) := rfl
  | fst pair pairIH =>
      calc
        hom.map (PureTm.fst pair) = target.fst (hom.map pair) := by
          simpa only [pureSyntaxAlgebra] using hom.preserves.map_fst pair
        _ = target.fst (pureRawFold target pair) := by rw [pairIH]
        _ = pureRawFold target (PureTm.fst pair) := rfl
  | snd pair pairIH =>
      calc
        hom.map (PureTm.snd pair) = target.snd (hom.map pair) := by
          simpa only [pureSyntaxAlgebra] using hom.preserves.map_snd pair
        _ = target.snd (pureRawFold target pair) := by rw [pairIH]
        _ = pureRawFold target (PureTm.snd pair) := rfl
  | refl term termIH =>
      calc
        hom.map (PureTm.refl term) = target.refl (hom.map term) := by
          simpa only [pureSyntaxAlgebra] using hom.preserves.map_refl term
        _ = target.refl (pureRawFold target term) := by rw [termIH]
        _ = pureRawFold target (PureTm.refl term) := rfl

/-- The intrinsic raw Pure syntax is initial among algebras of its complete
binding signature: every homomorphism out of it is the structural fold. -/
theorem pureRawFold_unique
    (target : PureRawAlgebra.{uRawTarget})
    (hom : PureRawHom pureSyntaxAlgebra target) :
    hom = pureRawFoldHom target := by
  apply PureRawHom.ext
  exact pureRawFold_unique_pointwise target hom

/-- A nontrivial target algebra: structural node count, including binders. -/
abbrev pureNodeCountAlgebra : PureRawAlgebra where
  Carrier := fun _ => Nat
  var := fun _ => 1
  const := fun _ => 1
  u0 := fun {_} => 1
  u1 := fun {_} => 1
  pi := fun domain body => domain + body + 1
  sigma := fun domain body => domain + body + 1
  id := fun type left right => type + left + right + 1
  lam := fun body => body + 1
  app := fun function argument => function + argument + 1
  pair := fun left right => left + right + 1
  fst := fun pair => pair + 1
  snd := fun pair => pair + 1
  refl := fun term => term + 1

/-- The unique structural node-count interpretation. -/
def pureNodeCount {n : Nat} (term : PureTm n) : Nat :=
  pureRawFold pureNodeCountAlgebra term

/-- Positive nondegeneracy witness: interpretation traverses a binder and an
application rather than collapsing all syntax to one value. -/
theorem pureNodeCount_betaShape_positive :
    pureNodeCount
      (PureTm.app (PureTm.lam (PureTm.var (0 : Fin 1))) PureTm.u0) = 4 :=
  rfl

/-- The deliberately collapsed unit algebra is a valid target of fold. -/
abbrev pureUnitAlgebra : PureRawAlgebra where
  Carrier := fun _ => PUnit
  var := fun _ => PUnit.unit
  const := fun _ => PUnit.unit
  u0 := fun {_} => PUnit.unit
  u1 := fun {_} => PUnit.unit
  pi := fun _ _ => PUnit.unit
  sigma := fun _ _ => PUnit.unit
  id := fun _ _ _ => PUnit.unit
  lam := fun _ => PUnit.unit
  app := fun _ _ => PUnit.unit
  pair := fun _ _ => PUnit.unit
  fst := fun _ => PUnit.unit
  snd := fun _ => PUnit.unit
  refl := fun _ => PUnit.unit

/-- Negative noncollapse witness: the unique erasure into the unit algebra has
no raw-algebra map back, since such a map would identify `u0` and `u1`. -/
theorem no_unit_to_pure_syntax_hom :
    ¬ Nonempty (PureRawHom pureUnitAlgebra pureSyntaxAlgebra) := by
  rintro ⟨hom⟩
  have u0Mapped := hom.preserves.map_u0 (n := 0)
  have u1Mapped := hom.preserves.map_u1 (n := 0)
  have collapsed : (PureTm.u0 : PureTm 0) = PureTm.u1 := by
    exact u0Mapped.symm.trans u1Mapped
  cases collapsed

/-! ### Equality profiles and their quotient presentations

An optional equality extension inhabits this interface; it does not change the
intensional core.  Besides being a congruence for the complete raw signature,
an admissible equality profile supplies stability under simultaneous
substitution.  The condition relates substitutions pointwise, so it remains
suitable for nontrivial open terms rather than merely closed syntax.  Renaming
stability is derived below rather than supplied as a duplicate premise. -/

/-- An equality profile admissible for the intrinsically scoped Pure syntax. -/
structure PureEqualityProfile where
  Rel : {n : Nat} → PureTm n → PureTm n → Prop
  equivalence : ∀ n, Equivalence (@Rel n)
  congr_pi : ∀ {n} {A A' : PureTm n} {B B' : PureTm (n + 1)},
    Rel A A' → Rel B B' → Rel (.pi A B) (.pi A' B')
  congr_sigma : ∀ {n} {A A' : PureTm n} {B B' : PureTm (n + 1)},
    Rel A A' → Rel B B' → Rel (.sigma A B) (.sigma A' B')
  congr_id : ∀ {n} {A A' a a' b b' : PureTm n},
    Rel A A' → Rel a a' → Rel b b' → Rel (.id A a b) (.id A' a' b')
  congr_lam : ∀ {n} {body body' : PureTm (n + 1)},
    Rel body body' → Rel (.lam body) (.lam body')
  congr_app : ∀ {n} {f f' a a' : PureTm n},
    Rel f f' → Rel a a' → Rel (.app f a) (.app f' a')
  congr_pair : ∀ {n} {a a' b b' : PureTm n},
    Rel a a' → Rel b b' → Rel (.pair a b) (.pair a' b')
  congr_fst : ∀ {n} {pair pair' : PureTm n},
    Rel pair pair' → Rel (.fst pair) (.fst pair')
  congr_snd : ∀ {n} {pair pair' : PureTm n},
    Rel pair pair' → Rel (.snd pair) (.snd pair')
  congr_refl : ∀ {n} {term term' : PureTm n},
    Rel term term' → Rel (.refl term) (.refl term')
  subst_closed : ∀ {n m}
    {leftSub rightSub :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub n m}
    {left right : PureTm n},
    (∀ index, Rel (leftSub index) (rightSub index)) → Rel left right →
      Rel
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst leftSub left)
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst rightSub right)

namespace PureEqualityProfile

/-- Renaming stability is forced by pointwise substitution stability: use the
renaming as a substitution whose images are variables.  It is therefore a
theorem of every admissible profile rather than an independently supplied
regularity premise. -/
theorem rename_closed (profile : PureEqualityProfile) {n m : Nat}
    (ρ : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.Ren n m)
    {left right : PureTm n} (related : profile.Rel left right) :
    profile.Rel
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename ρ left)
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename ρ right) := by
  have substituted := profile.subst_closed
    (leftSub :=
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.renToSub ρ)
    (rightSub :=
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.renToSub ρ)
    (fun index => (profile.equivalence m).refl _)
    related
  simpa only [
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.subst_renToSub] using
      substituted

/-- The setoid presented by one equality profile at one de Bruijn depth. -/
def setoid (profile : PureEqualityProfile) (n : Nat) : Setoid (PureTm n) where
  r := profile.Rel
  iseqv := profile.equivalence n

/-- Map a unary syntax operation through an equality-profile quotient. -/
def mapOne (profile : PureEqualityProfile) {n m : Nat}
    (operation : PureTm n → PureTm m)
    (respects : ∀ {left right}, profile.Rel left right →
      profile.Rel (operation left) (operation right)) :
    Quotient (profile.setoid n) → Quotient (profile.setoid m) :=
  Quotient.map' (s₁ := profile.setoid n) (s₂ := profile.setoid m)
    operation (fun _ _ related => respects related)

/-- Map a binary syntax operation through equality-profile quotients. -/
def mapTwo (profile : PureEqualityProfile) {n₁ n₂ m : Nat}
    (operation : PureTm n₁ → PureTm n₂ → PureTm m)
    (respects : ∀ {left₁ right₁ left₂ right₂},
      profile.Rel left₁ right₁ → profile.Rel left₂ right₂ →
        profile.Rel (operation left₁ left₂) (operation right₁ right₂))
    (first : Quotient (profile.setoid n₁))
    (second : Quotient (profile.setoid n₂)) :
    Quotient (profile.setoid m) :=
  Quotient.liftOn₂ first second
    (fun left right => Quotient.mk (profile.setoid m) (operation left right))
    (fun _ _ _ _ firstRelated secondRelated =>
      Quotient.sound (respects firstRelated secondRelated))

/-- Map a ternary syntax operation through equality-profile quotients. -/
def mapThree (profile : PureEqualityProfile) {n₁ n₂ n₃ m : Nat}
    (operation : PureTm n₁ → PureTm n₂ → PureTm n₃ → PureTm m)
    (respects : ∀ {left₁ right₁ left₂ right₂ left₃ right₃},
      profile.Rel left₁ right₁ → profile.Rel left₂ right₂ →
      profile.Rel left₃ right₃ →
        profile.Rel (operation left₁ left₂ left₃)
          (operation right₁ right₂ right₃))
    (first : Quotient (profile.setoid n₁))
    (second : Quotient (profile.setoid n₂))
    (third : Quotient (profile.setoid n₃)) :
    Quotient (profile.setoid m) :=
  Quotient.liftOn first
    (fun firstTerm =>
      profile.mapTwo (fun secondTerm thirdTerm =>
        operation firstTerm secondTerm thirdTerm)
        (fun secondRelated thirdRelated =>
          respects ((profile.equivalence n₁).refl firstTerm)
            secondRelated thirdRelated)
        second third)
    (by
      intro firstLeft firstRight firstRelated
      refine Quotient.inductionOn₂ second third ?_
      intro secondTerm thirdTerm
      exact Quotient.sound
        (respects firstRelated ((profile.equivalence n₂).refl secondTerm)
          ((profile.equivalence n₃).refl thirdTerm)))

/-- Renaming descends to every admissible profile quotient. -/
def rename (profile : PureEqualityProfile) {n m : Nat}
    (ρ : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.Ren n m) :
    Quotient (profile.setoid n) → Quotient (profile.setoid m) :=
  profile.mapOne
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename ρ)
    (fun related => profile.rename_closed ρ related)

/-- A raw simultaneous substitution descends to the profile quotient.  The
more general quotient-valued environment is built later with the contextual
presentation; this operation already proves stability under every live
intrinsic substitution. -/
def substRaw (profile : PureEqualityProfile) {n m : Nat}
    (σ : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub n m) :
    Quotient (profile.setoid n) → Quotient (profile.setoid m) :=
  profile.mapOne
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst σ)
    (fun related => profile.subst_closed
      (fun index => (profile.equivalence m).refl (σ index)) related)

@[simp] theorem rename_mk (profile : PureEqualityProfile) {n m : Nat}
    (ρ : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.Ren n m)
    (term : PureTm n) :
    profile.rename ρ (Quotient.mk (profile.setoid n) term) =
      Quotient.mk (profile.setoid m)
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename ρ term) :=
  rfl

@[simp] theorem substRaw_mk (profile : PureEqualityProfile) {n m : Nat}
    (σ : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub n m)
    (term : PureTm n) :
    profile.substRaw σ (Quotient.mk (profile.setoid n) term) =
      Quotient.mk (profile.setoid m)
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst σ term) :=
  rfl

/-- Identity substitution remains identity after quotienting. -/
theorem substRaw_ids (profile : PureEqualityProfile) {n : Nat}
    (term : Quotient (profile.setoid n)) :
    profile.substRaw
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.ids (n := n)) term =
      term := by
  refine Quotient.inductionOn term ?_
  intro syntaxTerm
  simp

/-- Composition of raw substitutions remains composition after quotienting. -/
theorem substRaw_comp (profile : PureEqualityProfile) {n m k : Nat}
    (τ : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub m k)
    (σ : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub n m)
    (term : Quotient (profile.setoid n)) :
    profile.substRaw τ (profile.substRaw σ term) =
      profile.substRaw
        (fun index =>
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst τ (σ index))
        term := by
  refine Quotient.inductionOn term ?_
  intro syntaxTerm
  simp

/-- `finer.FinerThan coarser` means every equation of `finer` is also an
equation of `coarser`, hence there is a canonical quotient map from the finer
presentation to the coarser one. -/
def FinerThan (finer coarser : PureEqualityProfile) : Prop :=
  ∀ {n} {left right : PureTm n}, finer.Rel left right → coarser.Rel left right

/-- The canonical map induced by inclusion of equality profiles. -/
def quotientMap {finer coarser : PureEqualityProfile}
    (includes : finer.FinerThan coarser) (n : Nat) :
    Quotient (finer.setoid n) → Quotient (coarser.setoid n) :=
  Quotient.map' id (fun _ _ related => includes related)

@[simp] theorem quotientMap_mk {finer coarser : PureEqualityProfile}
    (includes : finer.FinerThan coarser) {n : Nat} (term : PureTm n) :
    quotientMap includes n (Quotient.mk (finer.setoid n) term) =
      Quotient.mk (coarser.setoid n) term :=
  rfl

end PureEqualityProfile

/-! ### Equality kernels forced by contextual interpretations -/

/-- Substitution action and its naturality for one raw interpretation.  This
is the exact extra structure needed beyond a raw-signature homomorphism for
the interpretation kernel to be stable under open substitution.  It is not
presented as a full CwF: context comprehension and typed terms enter at the
later semantic interpretation boundary. -/
structure PureInterpretationSubstitutionAction
    (target : PureRawAlgebra.{uRawTarget})
    (hom : PureRawHom pureSyntaxAlgebra target) where
  semanticSubst : {n m : Nat} →
    (Fin n → target.Carrier m) → target.Carrier n → target.Carrier m
  map_subst : ∀ {n m}
    (substitution :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub n m)
    (term : PureTm n),
    hom.map
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
          substitution term) =
      semanticSubst (fun index => hom.map (substitution index)) (hom.map term)

namespace PureRawHom

/-- Equality of semantic images induces every congruence law automatically;
substitution naturality induces the open-substitution law.  Thus an
interpretation kernel is an admissible equality profile without separately
postulating its regularity fields. -/
def kernelProfile {target : PureRawAlgebra.{uRawTarget}}
    (hom : PureRawHom pureSyntaxAlgebra target)
    (action : PureInterpretationSubstitutionAction target hom) :
    PureEqualityProfile where
  Rel := fun left right => hom.map left = hom.map right
  equivalence := fun _ =>
    { refl := fun term => Eq.refl (hom.map term)
      symm := fun related => related.symm
      trans := fun first second => first.trans second }
  congr_pi := by
    intro n A A' B B' domainRelated bodyRelated
    calc
      hom.map (.pi A B) = target.pi (hom.map A) (hom.map B) := by
        simpa only [pureSyntaxAlgebra] using hom.preserves.map_pi A B
      _ = target.pi (hom.map A') (hom.map B') := by
        rw [domainRelated, bodyRelated]
      _ = hom.map (.pi A' B') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_pi A' B').symm
  congr_sigma := by
    intro n A A' B B' domainRelated bodyRelated
    calc
      hom.map (.sigma A B) = target.sigma (hom.map A) (hom.map B) := by
        simpa only [pureSyntaxAlgebra] using hom.preserves.map_sigma A B
      _ = target.sigma (hom.map A') (hom.map B') := by
        rw [domainRelated, bodyRelated]
      _ = hom.map (.sigma A' B') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_sigma A' B').symm
  congr_id := by
    intro n A A' left left' right right' typeRelated leftRelated rightRelated
    calc
      hom.map (.id A left right) =
          target.id (hom.map A) (hom.map left) (hom.map right) := by
        simpa only [pureSyntaxAlgebra] using
          hom.preserves.map_id A left right
      _ = target.id (hom.map A') (hom.map left') (hom.map right') := by
        rw [typeRelated, leftRelated, rightRelated]
      _ = hom.map (.id A' left' right') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_id A' left' right').symm
  congr_lam := by
    intro n body body' related
    calc
      hom.map (.lam body) = target.lam (hom.map body) := by
        simpa only [pureSyntaxAlgebra] using hom.preserves.map_lam body
      _ = target.lam (hom.map body') := by rw [related]
      _ = hom.map (.lam body') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_lam body').symm
  congr_app := by
    intro n function function' argument argument' functionRelated argumentRelated
    calc
      hom.map (.app function argument) =
          target.app (hom.map function) (hom.map argument) := by
        simpa only [pureSyntaxAlgebra] using
          hom.preserves.map_app function argument
      _ = target.app (hom.map function') (hom.map argument') := by
        rw [functionRelated, argumentRelated]
      _ = hom.map (.app function' argument') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_app function' argument').symm
  congr_pair := by
    intro n left left' right right' leftRelated rightRelated
    calc
      hom.map (.pair left right) =
          target.pair (hom.map left) (hom.map right) := by
        simpa only [pureSyntaxAlgebra] using hom.preserves.map_pair left right
      _ = target.pair (hom.map left') (hom.map right') := by
        rw [leftRelated, rightRelated]
      _ = hom.map (.pair left' right') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_pair left' right').symm
  congr_fst := by
    intro n pair pair' related
    calc
      hom.map (.fst pair) = target.fst (hom.map pair) := by
        simpa only [pureSyntaxAlgebra] using hom.preserves.map_fst pair
      _ = target.fst (hom.map pair') := by rw [related]
      _ = hom.map (.fst pair') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_fst pair').symm
  congr_snd := by
    intro n pair pair' related
    calc
      hom.map (.snd pair) = target.snd (hom.map pair) := by
        simpa only [pureSyntaxAlgebra] using hom.preserves.map_snd pair
      _ = target.snd (hom.map pair') := by rw [related]
      _ = hom.map (.snd pair') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_snd pair').symm
  congr_refl := by
    intro n term term' related
    calc
      hom.map (.refl term) = target.refl (hom.map term) := by
        simpa only [pureSyntaxAlgebra] using hom.preserves.map_refl term
      _ = target.refl (hom.map term') := by rw [related]
      _ = hom.map (.refl term') := by
        simpa only [pureSyntaxAlgebra] using
          (hom.preserves.map_refl term').symm
  subst_closed := by
    intro n m leftSub rightSub left right substitutionsRelated termsRelated
    have environmentsEqual :
        (fun index => hom.map (leftSub index)) =
          (fun index => hom.map (rightSub index)) := by
      funext index
      exact substitutionsRelated index
    calc
      hom.map
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
            leftSub left) =
          action.semanticSubst (fun index => hom.map (leftSub index))
            (hom.map left) := action.map_subst leftSub left
      _ = action.semanticSubst (fun index => hom.map (rightSub index))
            (hom.map right) := by rw [environmentsEqual, termsRelated]
      _ = hom.map
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
            rightSub right) := (action.map_subst rightSub right).symm

end PureRawHom

/-- The identity interpretation carries the ordinary syntactic substitution
action. -/
def pureSyntaxSubstitutionAction :
    PureInterpretationSubstitutionAction pureSyntaxAlgebra
      (PureRawHom.id pureSyntaxAlgebra) where
  semanticSubst :=
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
  map_subst := by intros; rfl

/-- Syntactic equality recovered as the kernel of the identity contextual
interpretation, rather than assembled from a second list of regularity
proofs.  Reducibility retains the expected definitional equality interface
for clients of the profile. -/
abbrev syntacticEqualityProfile : PureEqualityProfile :=
  (PureRawHom.id pureSyntaxAlgebra).kernelProfile
    pureSyntaxSubstitutionAction

theorem syntacticEqualityProfile_rel_iff {n : Nat}
    (left right : PureTm n) :
    syntacticEqualityProfile.Rel left right ↔ left = right := by
  rfl

/-- A raw algebra that identifies every variable with `u1` while keeping
`u0` distinct.  It is a valid algebra for the constructor signature, but its
interpretation kernel is not stable under open substitution. -/
abbrev substitutionUnstablePureAlgebra : PureRawAlgebra where
  Carrier := fun _ => Bool
  var := fun _ => true
  const := fun _ => false
  u0 := false
  u1 := true
  pi := fun _ _ => false
  sigma := fun _ _ => false
  id := fun _ _ _ => false
  lam := fun _ => false
  app := fun _ _ => false
  pair := fun _ _ => false
  fst := fun _ => false
  snd := fun _ => false
  refl := fun _ => false

def substitutionUnstablePureHom :
    PureRawHom pureSyntaxAlgebra substitutionUnstablePureAlgebra :=
  pureRawFoldHom substitutionUnstablePureAlgebra

/-- Negative control: raw constructor preservation alone does not force
substitution regularity.  Replacing the related variable and `u1` by the same
`u0` environment separates their images, so no natural substitution action
can exist for this raw interpretation. -/
theorem substitutionUnstablePureHom_has_no_substitution_action :
    ¬ Nonempty
      (PureInterpretationSubstitutionAction substitutionUnstablePureAlgebra
        substitutionUnstablePureHom) := by
  rintro ⟨action⟩
  let substitution :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub 1 0 :=
    fun _ => .u0
  have related :
      substitutionUnstablePureHom.map (.var (0 : Fin 1)) =
        substitutionUnstablePureHom.map .u1 := by
    rfl
  have semanticRelated := congrArg
    (action.semanticSubst
      (fun _ : Fin 1 =>
        substitutionUnstablePureHom.map (PureTm.u0 : PureTm 0)))
    related
  have substitutedRelated :
      substitutionUnstablePureHom.map
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
            substitution (.var (0 : Fin 1))) =
        substitutionUnstablePureHom.map
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
            substitution .u1) :=
    (action.map_subst substitution (.var (0 : Fin 1))).trans
      (semanticRelated.trans (action.map_subst substitution .u1).symm)
  change false = true at substitutedRelated
  cases substitutedRelated

/-- The quotient algebra selected by an equality profile. -/
def pureProfileQuotientAlgebra (profile : PureEqualityProfile) :
    PureRawAlgebra where
  Carrier := fun n => Quotient (profile.setoid n)
  var := fun {n} index => Quotient.mk (profile.setoid n) (.var index)
  const := fun {n} name => Quotient.mk (profile.setoid n) (.const name)
  u0 := fun {n} => Quotient.mk (profile.setoid n) .u0
  u1 := fun {n} => Quotient.mk (profile.setoid n) .u1
  pi := fun domain body => profile.mapTwo PureTm.pi
    (fun domainRelated bodyRelated => profile.congr_pi domainRelated bodyRelated)
    domain body
  sigma := fun domain body => profile.mapTwo PureTm.sigma
    (fun domainRelated bodyRelated =>
      profile.congr_sigma domainRelated bodyRelated) domain body
  id := fun type left right => profile.mapThree PureTm.id
    (fun typeRelated leftRelated rightRelated =>
      profile.congr_id typeRelated leftRelated rightRelated) type left right
  lam := fun body => profile.mapOne PureTm.lam
    (fun related => profile.congr_lam related) body
  app := fun function argument => profile.mapTwo PureTm.app
    (fun functionRelated argumentRelated =>
      profile.congr_app functionRelated argumentRelated) function argument
  pair := fun left right => profile.mapTwo PureTm.pair
    (fun leftRelated rightRelated =>
      profile.congr_pair leftRelated rightRelated) left right
  fst := fun pair => profile.mapOne PureTm.fst
    (fun related => profile.congr_fst related) pair
  snd := fun pair => profile.mapOne PureTm.snd
    (fun related => profile.congr_snd related) pair
  refl := fun term => profile.mapOne PureTm.refl
    (fun related => profile.congr_refl related) term

/-- Canonical projection from raw Pure syntax to a selected profile quotient. -/
def pureProfileQuotientHom (profile : PureEqualityProfile) :
    PureRawHom pureSyntaxAlgebra (pureProfileQuotientAlgebra profile) where
  map := fun {n} term => Quotient.mk (profile.setoid n) term
  preserves := by
    constructor <;> intros <;>
      rfl

/-- A raw interpretation respects a selected equality profile exactly when it
identifies every pair related by that profile. -/
def PureRawHom.RespectsProfile {target : PureRawAlgebra.{uRawTarget}}
    (hom : PureRawHom pureSyntaxAlgebra target)
    (profile : PureEqualityProfile) : Prop :=
  ∀ {n} {left right : PureTm n}, profile.Rel left right →
    hom.map left = hom.map right

/-- The canonical quotient projection respects its defining profile. -/
theorem pureProfileQuotientHom_respects (profile : PureEqualityProfile) :
    (pureProfileQuotientHom profile).RespectsProfile profile := by
  intro n left right related
  exact Quotient.sound related

abbrev IntrinsicPureConv {n : Nat} :=
  @Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv n

abbrev IntrinsicPureRed {n : Nat} :=
  @Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.Red n

/-- Equivalence closure transports through any operation that transports one
intrinsic Pure reduction step. -/
theorem intrinsicPureConv_map {n m : Nat} (operation : PureTm n → PureTm m)
    (mapsRed : ∀ {left right}, IntrinsicPureRed left right →
      IntrinsicPureRed (operation left) (operation right))
    {left right : PureTm n} (conversion : IntrinsicPureConv left right) :
    IntrinsicPureConv (operation left) (operation right) := by
  induction conversion with
  | rel left right step => exact .rel _ _ (mapsRed step)
  | refl term => exact .refl _
  | symm left right related inductionHypothesis =>
      exact .symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact .trans _ _ _ firstIH secondIH

theorem intrinsicPureConv_congr_pi {n : Nat}
    {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (domain : IntrinsicPureConv A A') (body : IntrinsicPureConv B B') :
    IntrinsicPureConv (.pi A B) (.pi A' B') :=
  Relation.EqvGen.trans _ _ _
    (intrinsicPureConv_map (fun term => .pi term B)
      (fun step => .congPiDom step) domain)
    (intrinsicPureConv_map (fun term => .pi A' term)
      (fun step => .congPiCod step) body)

theorem intrinsicPureConv_congr_sigma {n : Nat}
    {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (domain : IntrinsicPureConv A A') (body : IntrinsicPureConv B B') :
    IntrinsicPureConv (.sigma A B) (.sigma A' B') :=
  Relation.EqvGen.trans _ _ _
    (intrinsicPureConv_map (fun term => .sigma term B)
      (fun step => .congSigmaDom step) domain)
    (intrinsicPureConv_map (fun term => .sigma A' term)
      (fun step => .congSigmaCod step) body)

theorem intrinsicPureConv_congr_id {n : Nat}
    {A A' a a' b b' : PureTm n}
    (type : IntrinsicPureConv A A')
    (left : IntrinsicPureConv a a')
    (right : IntrinsicPureConv b b') :
    IntrinsicPureConv (.id A a b) (.id A' a' b') :=
  Relation.EqvGen.trans _ _ _
    (intrinsicPureConv_map (fun term => .id term a b)
      (fun step => .congIdTy step) type)
    (Relation.EqvGen.trans _ _ _
      (intrinsicPureConv_map (fun term => .id A' term b)
        (fun step => .congIdLeft step) left)
      (intrinsicPureConv_map (fun term => .id A' a' term)
        (fun step => .congIdRight step) right))

theorem intrinsicPureConv_congr_lam {n : Nat}
    {body body' : PureTm (n + 1)}
    (conversion : IntrinsicPureConv body body') :
    IntrinsicPureConv (.lam body) (.lam body') :=
  intrinsicPureConv_map PureTm.lam (fun step => .congLam step) conversion

theorem intrinsicPureConv_congr_app {n : Nat}
    {function function' argument argument' : PureTm n}
    (functionConversion : IntrinsicPureConv function function')
    (argumentConversion : IntrinsicPureConv argument argument') :
    IntrinsicPureConv (.app function argument) (.app function' argument') :=
  Relation.EqvGen.trans _ _ _
    (intrinsicPureConv_map (fun term => .app term argument)
      (fun step => .congAppFun step) functionConversion)
    (intrinsicPureConv_map (fun term => .app function' term)
      (fun step => .congAppArg step) argumentConversion)

theorem intrinsicPureConv_congr_pair {n : Nat}
    {left left' right right' : PureTm n}
    (leftConversion : IntrinsicPureConv left left')
    (rightConversion : IntrinsicPureConv right right') :
    IntrinsicPureConv (.pair left right) (.pair left' right') :=
  Relation.EqvGen.trans _ _ _
    (intrinsicPureConv_map (fun term => .pair term right)
      (fun step => .congPairFst step) leftConversion)
    (intrinsicPureConv_map (fun term => .pair left' term)
      (fun step => .congPairSnd step) rightConversion)

theorem intrinsicPureConv_congr_fst {n : Nat} {pair pair' : PureTm n}
    (conversion : IntrinsicPureConv pair pair') :
    IntrinsicPureConv (.fst pair) (.fst pair') :=
  intrinsicPureConv_map PureTm.fst (fun step => .congFst step) conversion

theorem intrinsicPureConv_congr_snd {n : Nat} {pair pair' : PureTm n}
    (conversion : IntrinsicPureConv pair pair') :
    IntrinsicPureConv (.snd pair) (.snd pair') :=
  intrinsicPureConv_map PureTm.snd (fun step => .congSnd step) conversion

theorem intrinsicPureConv_congr_refl {n : Nat} {term term' : PureTm n}
    (conversion : IntrinsicPureConv term term') :
    IntrinsicPureConv (.refl term) (.refl term') :=
  intrinsicPureConv_map PureTm.refl (fun step => .congRefl step) conversion

/-- Pointwise convertible substitution environments yield convertible
instances.  The binder cases use the actual live `liftSub` and renaming
lemmas, so this is the contextual rather than merely closed conversion law. -/
theorem intrinsicPureConv_subst_pointwise {n m : Nat}
    {leftSub rightSub :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub n m}
    (substitutions : ∀ index, IntrinsicPureConv
      (leftSub index) (rightSub index)) :
    ∀ term : PureTm n, IntrinsicPureConv
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst leftSub term)
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst rightSub term) := by
  intro term
  induction term generalizing m with
  | var index => exact substitutions index
  | const name => exact .refl _
  | u0 => exact .refl _
  | u1 => exact .refl _
  | pi domain body domainIH bodyIH =>
      apply intrinsicPureConv_congr_pi
      · exact domainIH substitutions
      · apply bodyIH
        intro index
        refine Fin.cases ?_ ?_ index
        · exact .refl _
        · intro predecessor
          exact Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.conv_rename
            Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.wk
            (substitutions predecessor)
  | sigma domain body domainIH bodyIH =>
      apply intrinsicPureConv_congr_sigma
      · exact domainIH substitutions
      · apply bodyIH
        intro index
        refine Fin.cases ?_ ?_ index
        · exact .refl _
        · intro predecessor
          exact Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.conv_rename
            Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.wk
            (substitutions predecessor)
  | id type left right typeIH leftIH rightIH =>
      exact intrinsicPureConv_congr_id (typeIH substitutions)
        (leftIH substitutions) (rightIH substitutions)
  | lam body bodyIH =>
      apply intrinsicPureConv_congr_lam
      apply bodyIH
      intro index
      refine Fin.cases ?_ ?_ index
      · exact .refl _
      · intro predecessor
        exact Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.conv_rename
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.wk
          (substitutions predecessor)
  | app function argument functionIH argumentIH =>
      exact intrinsicPureConv_congr_app (functionIH substitutions)
        (argumentIH substitutions)
  | pair left right leftIH rightIH =>
      exact intrinsicPureConv_congr_pair (leftIH substitutions)
        (rightIH substitutions)
  | fst pair pairIH => exact intrinsicPureConv_congr_fst (pairIH substitutions)
  | snd pair pairIH => exact intrinsicPureConv_congr_snd (pairIH substitutions)
  | refl term termIH => exact intrinsicPureConv_congr_refl (termIH substitutions)

/-- Both the substituted term and its simultaneous environment may vary by
intrinsic Pure conversion. -/
theorem intrinsicPureConv_subst_congr {n m : Nat}
    {leftSub rightSub :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub n m}
    {left right : PureTm n}
    (substitutions : ∀ index, IntrinsicPureConv
      (leftSub index) (rightSub index))
    (terms : IntrinsicPureConv left right) :
    IntrinsicPureConv
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst leftSub left)
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst rightSub right) :=
  Relation.EqvGen.trans _ _ _
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.conv_subst leftSub terms)
    (intrinsicPureConv_subst_pointwise substitutions right)

/-- The actual intrinsic Pure conversion relation as one admissible equality
profile.  It is evidence for the extension interface, not kernel selection. -/
def intrinsicPureConversionProfile : PureEqualityProfile where
  Rel := IntrinsicPureConv
  equivalence := fun _ =>
    ⟨fun term => .refl term,
      fun relation => .symm _ _ relation,
      fun first second => .trans _ _ _ first second⟩
  congr_pi := intrinsicPureConv_congr_pi
  congr_sigma := intrinsicPureConv_congr_sigma
  congr_id := intrinsicPureConv_congr_id
  congr_lam := intrinsicPureConv_congr_lam
  congr_app := intrinsicPureConv_congr_app
  congr_pair := intrinsicPureConv_congr_pair
  congr_fst := intrinsicPureConv_congr_fst
  congr_snd := intrinsicPureConv_congr_snd
  congr_refl := intrinsicPureConv_congr_refl
  subst_closed := fun substitutions conversion =>
    intrinsicPureConv_subst_congr substitutions conversion

/-- Positive witness for the live intrinsic profile: β-conversion is one of
its genuine, nonsyntactic equations. -/
theorem intrinsicPureConversionProfile_beta :
    intrinsicPureConversionProfile.Rel
      (PureTm.app (PureTm.lam (PureTm.var (0 : Fin 1))) PureTm.u0)
      (PureTm.u0 : PureTm 0) := by
  exact Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.red_implies_conv
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.Red.betaPi
      (PureTm.var (0 : Fin 1)) PureTm.u0)

/-- The positive β witness becomes literal equality in the corresponding
profile quotient. -/
theorem intrinsicPureProfile_beta_quotient :
    (pureProfileQuotientHom intrinsicPureConversionProfile).map
        (PureTm.app (PureTm.lam (PureTm.var (0 : Fin 1))) PureTm.u0) =
      (pureProfileQuotientHom intrinsicPureConversionProfile).map
        (PureTm.u0 : PureTm 0) :=
  Quotient.sound intrinsicPureConversionProfile_beta

/-- Positive quotient witness: syntactic equality does not collapse the two
universe constructors. -/
theorem syntacticProfile_u0_ne_u1 :
    (pureProfileQuotientHom syntacticEqualityProfile).map
        (PureTm.u0 : PureTm 0) ≠
      (pureProfileQuotientHom syntacticEqualityProfile).map PureTm.u1 := by
  intro equalClasses
  have termsEqual : (PureTm.u0 : PureTm 0) = PureTm.u1 :=
    Quotient.exact equalClasses
  cases termsEqual

/-- Syntactic equality is the finest admissible equality profile. -/
theorem syntacticEqualityProfile_finer
    (profile : PureEqualityProfile) :
    syntacticEqualityProfile.FinerThan profile := by
  intro n left right equal
  have termsEqual := (syntacticEqualityProfile_rel_iff left right).mp equal
  subst right
  exact (profile.equivalence n).refl left

/-- Negative witness distinguishing the live Pure conversion profile from raw
syntax: β-conversion prevents an inclusion back into syntactic equality. -/
theorem intrinsicPureProfile_not_finer_than_syntactic :
    ¬ intrinsicPureConversionProfile.FinerThan syntacticEqualityProfile := by
  intro includes
  have syntaxEquality := includes intrinsicPureConversionProfile_beta
  change PureTm.app (PureTm.lam (PureTm.var (0 : Fin 1))) PureTm.u0 =
    (PureTm.u0 : PureTm 0) at syntaxEquality
  cases syntaxEquality

/-- A profile that identifies the two universes cannot be interpreted by the
identity syntax homomorphism.  This is a negative witness that profile-respect
is a real restriction, not bookkeeping around an arbitrary raw fold. -/
theorem profile_equating_universes_blocks_identity
    (profile : PureEqualityProfile)
    (collapses : profile.Rel (PureTm.u0 : PureTm 0) PureTm.u1) :
    ¬ (PureRawHom.id pureSyntaxAlgebra).RespectsProfile profile := by
  intro respects
  have termsEqual := respects collapses
  change (PureTm.u0 : PureTm 0) = PureTm.u1 at termsEqual
  cases termsEqual

/-- Negative profile-order witness: any profile equating the universes is
strictly coarser than raw syntactic equality, so there is no inclusion of its
equations back into the syntactic profile. -/
theorem profile_equating_universes_not_finer_than_syntactic
    (profile : PureEqualityProfile)
    (collapses : profile.Rel (PureTm.u0 : PureTm 0) PureTm.u1) :
    ¬ profile.FinerThan syntacticEqualityProfile := by
  intro includes
  have termsEqual : (PureTm.u0 : PureTm 0) = PureTm.u1 := includes collapses
  cases termsEqual

/-- Factor a profile-respecting interpretation through the selected quotient. -/
def PureRawHom.factorThroughProfile
    {target : PureRawAlgebra.{uRawTarget}}
    (profile : PureEqualityProfile)
    (hom : PureRawHom pureSyntaxAlgebra target)
    (respects : hom.RespectsProfile profile) :
    PureRawHom (pureProfileQuotientAlgebra profile) target where
  map := fun {n} quotient => Quotient.liftOn quotient hom.map
    (fun left right related => respects related)
  preserves := by
    constructor
    · intro n index
      exact hom.preserves.map_var index
    · intro n name
      exact hom.preserves.map_const name
    · intro n
      exact hom.preserves.map_u0
    · intro n
      exact hom.preserves.map_u1
    · intro n domain body
      refine Quotient.inductionOn₂ domain body ?_
      intro domainTerm bodyTerm
      exact hom.preserves.map_pi domainTerm bodyTerm
    · intro n domain body
      refine Quotient.inductionOn₂ domain body ?_
      intro domainTerm bodyTerm
      exact hom.preserves.map_sigma domainTerm bodyTerm
    · intro n type left right
      refine Quotient.inductionOn type ?_
      intro typeTerm
      refine Quotient.inductionOn₂ left right ?_
      intro leftTerm rightTerm
      exact hom.preserves.map_id typeTerm leftTerm rightTerm
    · intro n body
      refine Quotient.inductionOn body ?_
      intro bodyTerm
      exact hom.preserves.map_lam bodyTerm
    · intro n function argument
      refine Quotient.inductionOn₂ function argument ?_
      intro functionTerm argumentTerm
      exact hom.preserves.map_app functionTerm argumentTerm
    · intro n left right
      refine Quotient.inductionOn₂ left right ?_
      intro leftTerm rightTerm
      exact hom.preserves.map_pair leftTerm rightTerm
    · intro n pair
      refine Quotient.inductionOn pair ?_
      intro pairTerm
      exact hom.preserves.map_fst pairTerm
    · intro n pair
      refine Quotient.inductionOn pair ?_
      intro pairTerm
      exact hom.preserves.map_snd pairTerm
    · intro n term
      refine Quotient.inductionOn term ?_
      intro syntaxTerm
      exact hom.preserves.map_refl syntaxTerm

/-- The factorization triangle commutes: quotienting and then interpreting is
exactly the original profile-respecting interpretation. -/
theorem PureRawHom.factorThroughProfile_comp_projection
    {target : PureRawAlgebra.{uRawTarget}}
    (profile : PureEqualityProfile)
    (hom : PureRawHom pureSyntaxAlgebra target)
    (respects : hom.RespectsProfile profile) :
    PureRawHom.comp (pureProfileQuotientHom profile)
      (hom.factorThroughProfile profile respects) = hom := by
  apply PureRawHom.ext
  intro n term
  rfl

/-- The factorization is unique among quotient-algebra homomorphisms. -/
theorem PureRawHom.factorThroughProfile_unique
    {target : PureRawAlgebra.{uRawTarget}}
    (profile : PureEqualityProfile)
    (hom : PureRawHom pureSyntaxAlgebra target)
    (factor : PureRawHom (pureProfileQuotientAlgebra profile) target)
    (commutes : PureRawHom.comp (pureProfileQuotientHom profile) factor = hom) :
    factor = hom.factorThroughProfile profile
      (by
        intro n left right related
        have mapped := congrArg
          (fun candidate : PureRawHom pureSyntaxAlgebra target =>
            candidate.map left) commutes
        have mappedRight := congrArg
          (fun candidate : PureRawHom pureSyntaxAlgebra target =>
            candidate.map right) commutes
        have quotientEqual :
            (pureProfileQuotientHom profile).map left =
              (pureProfileQuotientHom profile).map right :=
          Quotient.sound related
        exact mapped.symm.trans
          ((congrArg factor.map quotientEqual).trans mappedRight)) := by
  apply PureRawHom.ext
  intro n quotient
  refine Quotient.inductionOn quotient ?_
  intro term
  have mapped := congrArg
    (fun candidate : PureRawHom pureSyntaxAlgebra target => candidate.map term)
    commutes
  exact mapped

/-! ## §7d The equality-neutral native raw presentation

The preceding initiality precursor covers the live intrinsic Pure signature.
The native MeTTa presentation must additionally expose the operational
structure that forced this derivation: stage-changing quotation, runtime
patterns, collections, and validated languages.  Cost and evidence remain
in an external decoration fibre below; they are native data without becoming
kernel-term constructors.

This section forms their free *raw* extension.  A native algebra is a family
of complete `PureRawAlgebra`s indexed by interpreter stage, together with the
six genuinely MeTTa-specific operations.  Consequently the Pure operations
remain available on mixed native terms: for example, application may consume
a quoted or evidence-decorated term.  No equality laws are imposed here, so
raw initiality is not presented as the stronger semantic-CwF initiality still
listed at §11. -/

/-- Intrinsically scoped raw terms for the staged native presentation.

The first index is the interpreter stage and the second is de Bruijn depth. -/
inductive StagedReflectiveTm : Nat → Nat → Type where
  | var {stage binders : Nat} : Fin binders → StagedReflectiveTm stage binders
  | const {stage binders : Nat} : DeclName → StagedReflectiveTm stage binders
  | u0 {stage binders : Nat} : StagedReflectiveTm stage binders
  | u1 {stage binders : Nat} : StagedReflectiveTm stage binders
  | pi {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage (binders + 1) → StagedReflectiveTm stage binders
  | sigma {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage (binders + 1) → StagedReflectiveTm stage binders
  | id {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders → StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders
  | lam {stage binders : Nat} : StagedReflectiveTm stage (binders + 1) →
      StagedReflectiveTm stage binders
  | app {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders → StagedReflectiveTm stage binders
  | pair {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders → StagedReflectiveTm stage binders
  | fst {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders
  | snd {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders
  | refl {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders
  /-- Primitive sharing.  The body binds the shared value at de Bruijn index
  zero.  Inlining is deliberately absent from raw syntax: it is an optional
  equality-profile equation. -/
  | letE {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage (binders + 1) → StagedReflectiveTm stage binders
  /-- A runtime Pattern is a first-class native value. -/
  | pattern {stage binders : Nat} : Pattern → StagedReflectiveTm stage binders
  /-- Empty collection/superposition.  Algebraic bag equations belong to an
  equality profile, not to raw syntax. -/
  | empty {stage binders : Nat} : StagedReflectiveTm stage binders
  /-- Binary collection/superposition before quotienting by bag laws. -/
  | superpose {stage binders : Nat} : StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders → StagedReflectiveTm stage binders
  /-- A validated five-field language presentation is a first-class value. -/
  | language {stage binders : Nat} :
      Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef →
      StagedReflectiveTm stage binders
  /-- Quotation follows an explicit nonascending stage morphism. -/
  | quote {high low binders : Nat} : StageHom high low →
      StagedReflectiveTm high binders → StagedReflectiveTm low binders

/-! ### Support-indexed renaming and substitution

A renaming acts uniformly at every stage.  A simultaneous substitution is a
family indexed by stage: when substitution crosses `quote route term`, the
body uses the environment at `route`'s source stage.  This is the minimal
honest action for a stage-changing binder presentation; a single low-stage
environment cannot simply be retyped as a high-stage one. -/

abbrev NativeRen (source target : Nat) := Fin source → Fin target

def nativeIdRen : NativeRen binders binders := fun index => index

def nativeWk : NativeRen binders (binders + 1) := Fin.succ

def nativeLiftRen (rho : NativeRen source target) :
    NativeRen (source + 1) (target + 1) :=
  Fin.cases 0 (fun index => Fin.succ (rho index))

/-- Capture-avoiding renaming, including beneath Pure binders and across
quotation. -/
def nativeRename (rho : NativeRen source target) :
    StagedReflectiveTm stage source → StagedReflectiveTm stage target
  | .var index => .var (rho index)
  | .const name => .const name
  | .u0 => .u0
  | .u1 => .u1
  | .pi domain body =>
      .pi (nativeRename rho domain)
        (nativeRename (nativeLiftRen rho) body)
  | .sigma domain body =>
      .sigma (nativeRename rho domain)
        (nativeRename (nativeLiftRen rho) body)
  | .id type left right =>
      .id (nativeRename rho type) (nativeRename rho left)
        (nativeRename rho right)
  | .lam body => .lam (nativeRename (nativeLiftRen rho) body)
  | .app function argument =>
      .app (nativeRename rho function) (nativeRename rho argument)
  | .pair left right =>
      .pair (nativeRename rho left) (nativeRename rho right)
  | .fst pair => .fst (nativeRename rho pair)
  | .snd pair => .snd (nativeRename rho pair)
  | .refl term => .refl (nativeRename rho term)
  | .letE value body =>
      .letE (nativeRename rho value)
        (nativeRename (nativeLiftRen rho) body)
  | .pattern value => .pattern value
  | .empty => .empty
  | .superpose left right =>
      .superpose (nativeRename rho left) (nativeRename rho right)
  | .language value => .language value
  | .quote route term => .quote route (nativeRename rho term)

/-- Stage-polymorphic simultaneous substitution.  Its stage parameter is
essential data, not an implementation detail. -/
abbrev NativeSub (source target : Nat) :=
  (stage : Nat) → Fin source → StagedReflectiveTm stage target

def nativeIds : NativeSub binders binders :=
  fun _ index => .var index

def nativeLiftSub (substitution : NativeSub source target) :
    NativeSub (source + 1) (target + 1) :=
  fun stage => Fin.cases (.var 0)
    (fun index => nativeRename nativeWk (substitution stage index))

/-- Capture-avoiding simultaneous substitution.  The quotation case selects
the substitution component at the quoted term's source stage automatically. -/
def nativeSubst (substitution : NativeSub source target) :
    StagedReflectiveTm stage source → StagedReflectiveTm stage target
  | .var index => substitution _ index
  | .const name => .const name
  | .u0 => .u0
  | .u1 => .u1
  | .pi domain body =>
      .pi (nativeSubst substitution domain)
        (nativeSubst (nativeLiftSub substitution) body)
  | .sigma domain body =>
      .sigma (nativeSubst substitution domain)
        (nativeSubst (nativeLiftSub substitution) body)
  | .id type left right =>
      .id (nativeSubst substitution type) (nativeSubst substitution left)
        (nativeSubst substitution right)
  | .lam body => .lam (nativeSubst (nativeLiftSub substitution) body)
  | .app function argument =>
      .app (nativeSubst substitution function)
        (nativeSubst substitution argument)
  | .pair left right =>
      .pair (nativeSubst substitution left) (nativeSubst substitution right)
  | .fst pair => .fst (nativeSubst substitution pair)
  | .snd pair => .snd (nativeSubst substitution pair)
  | .refl term => .refl (nativeSubst substitution term)
  | .letE value body =>
      .letE (nativeSubst substitution value)
        (nativeSubst (nativeLiftSub substitution) body)
  | .pattern value => .pattern value
  | .empty => .empty
  | .superpose left right =>
      .superpose (nativeSubst substitution left)
        (nativeSubst substitution right)
  | .language value => .language value
  | .quote route term => .quote route (nativeSubst substitution term)

/-- Composition of stage-polymorphic substitutions. -/
def nativeSubComp (later : NativeSub middle target)
    (earlier : NativeSub source middle) : NativeSub source target :=
  fun stage index => nativeSubst later (earlier stage index)

/-- A renaming viewed as a stage-polymorphic substitution. -/
def nativeSubOfRen (rho : NativeRen source target) :
    NativeSub source target :=
  fun _ index => .var (rho index)

@[simp] theorem nativeLiftRen_id :
    nativeLiftRen (nativeIdRen (binders := binders)) = nativeIdRen := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

theorem nativeLiftRen_eq_pureLiftRen (rho : NativeRen source target) :
    nativeLiftRen rho =
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.liftRen rho := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

@[simp] theorem nativeLiftRen_comp_apply
    (later : NativeRen middle target) (earlier : NativeRen source middle)
    (index : Fin (source + 1)) :
    nativeLiftRen later (nativeLiftRen earlier index) =
      nativeLiftRen (fun previous => later (earlier previous)) index := by
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

theorem nativeRename_ext {left right : NativeRen source target}
    (pointwise : ∀ index, left index = right index) :
    ∀ {stage} (term : StagedReflectiveTm stage source),
      nativeRename left term = nativeRename right term := by
  intro stage term
  induction term generalizing target with
  | var index => simp [nativeRename, pointwise index]
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [nativeRename]
      congr 1
      · exact domainIH pointwise
      · apply bodyIH
        intro index
        refine Fin.cases ?_ ?_ index
        · rfl
        · intro previous
          simp [nativeLiftRen, pointwise previous]
  | sigma domain body domainIH bodyIH =>
      simp only [nativeRename]
      congr 1
      · exact domainIH pointwise
      · apply bodyIH
        intro index
        refine Fin.cases ?_ ?_ index
        · rfl
        · intro previous
          simp [nativeLiftRen, pointwise previous]
  | id type leftTerm rightTerm typeIH leftIH rightIH =>
      simp [nativeRename, typeIH pointwise, leftIH pointwise,
        rightIH pointwise]
  | lam body bodyIH =>
      simp only [nativeRename]
      congr 1
      apply bodyIH
      intro index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro previous
        simp [nativeLiftRen, pointwise previous]
  | app function argument functionIH argumentIH =>
      simp [nativeRename, functionIH pointwise, argumentIH pointwise]
  | pair leftTerm rightTerm leftIH rightIH =>
      simp [nativeRename, leftIH pointwise, rightIH pointwise]
  | fst pair pairIH => simp [nativeRename, pairIH pointwise]
  | snd pair pairIH => simp [nativeRename, pairIH pointwise]
  | refl value valueIH => simp [nativeRename, valueIH pointwise]
  | letE value body valueIH bodyIH =>
      simp only [nativeRename]
      congr 1
      · exact valueIH pointwise
      · exact bodyIH (fun index => by
          refine Fin.cases ?_ ?_ index
          · rfl
          · intro previous
            simp [nativeLiftRen, pointwise previous])
  | pattern value => rfl
  | empty => rfl
  | superpose leftTerm rightTerm leftIH rightIH =>
      simp [nativeRename, leftIH pointwise, rightIH pointwise]
  | language value => rfl
  | quote route value valueIH => simp [nativeRename, valueIH pointwise]

@[simp] theorem nativeRename_id :
    ∀ {stage} (term : StagedReflectiveTm stage binders),
      nativeRename nativeIdRen term = term := by
  intro stage term
  induction term with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp [nativeRename, domainIH, bodyIH, nativeLiftRen_id]
  | sigma domain body domainIH bodyIH =>
      simp [nativeRename, domainIH, bodyIH, nativeLiftRen_id]
  | id type left right typeIH leftIH rightIH =>
      simp [nativeRename, typeIH, leftIH, rightIH]
  | lam body bodyIH => simp [nativeRename, bodyIH, nativeLiftRen_id]
  | app function argument functionIH argumentIH =>
      simp [nativeRename, functionIH, argumentIH]
  | pair left right leftIH rightIH =>
      simp [nativeRename, leftIH, rightIH]
  | fst pair pairIH => simp [nativeRename, pairIH]
  | snd pair pairIH => simp [nativeRename, pairIH]
  | refl value valueIH => simp [nativeRename, valueIH]
  | letE value body valueIH bodyIH =>
      simp [nativeRename, valueIH, bodyIH, nativeLiftRen_id]
  | pattern value => rfl
  | empty => rfl
  | superpose left right leftIH rightIH =>
      simp [nativeRename, leftIH, rightIH]
  | language value => rfl
  | quote route value valueIH => simp [nativeRename, valueIH]

@[simp] theorem nativeRename_comp
    (later : NativeRen middle target) (earlier : NativeRen source middle) :
    ∀ {stage} (term : StagedReflectiveTm stage source),
      nativeRename later (nativeRename earlier term) =
        nativeRename (fun index => later (earlier index)) term := by
  intro stage term
  induction term generalizing middle target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [nativeRename]
      congr 1
      · exact domainIH later earlier
      · calc
          nativeRename (nativeLiftRen later)
              (nativeRename (nativeLiftRen earlier) body) =
              nativeRename
                (fun index =>
                  nativeLiftRen later (nativeLiftRen earlier index)) body :=
            bodyIH (nativeLiftRen later) (nativeLiftRen earlier)
          _ = nativeRename
                (nativeLiftRen (fun index => later (earlier index))) body := by
            apply nativeRename_ext
            exact nativeLiftRen_comp_apply later earlier
  | sigma domain body domainIH bodyIH =>
      simp only [nativeRename]
      congr 1
      · exact domainIH later earlier
      · calc
          nativeRename (nativeLiftRen later)
              (nativeRename (nativeLiftRen earlier) body) =
              nativeRename
                (fun index =>
                  nativeLiftRen later (nativeLiftRen earlier index)) body :=
            bodyIH (nativeLiftRen later) (nativeLiftRen earlier)
          _ = nativeRename
                (nativeLiftRen (fun index => later (earlier index))) body := by
            apply nativeRename_ext
            exact nativeLiftRen_comp_apply later earlier
  | id type left right typeIH leftIH rightIH =>
      simp [nativeRename, typeIH later earlier, leftIH later earlier,
        rightIH later earlier]
  | lam body bodyIH =>
      simp only [nativeRename]
      congr 1
      calc
        nativeRename (nativeLiftRen later)
            (nativeRename (nativeLiftRen earlier) body) =
            nativeRename
              (fun index =>
                nativeLiftRen later (nativeLiftRen earlier index)) body :=
          bodyIH (nativeLiftRen later) (nativeLiftRen earlier)
        _ = nativeRename
              (nativeLiftRen (fun index => later (earlier index))) body := by
          apply nativeRename_ext
          exact nativeLiftRen_comp_apply later earlier
  | app function argument functionIH argumentIH =>
      simp [nativeRename, functionIH later earlier, argumentIH later earlier]
  | pair left right leftIH rightIH =>
      simp [nativeRename, leftIH later earlier, rightIH later earlier]
  | fst pair pairIH => simp [nativeRename, pairIH later earlier]
  | snd pair pairIH => simp [nativeRename, pairIH later earlier]
  | refl value valueIH => simp [nativeRename, valueIH later earlier]
  | letE value body valueIH bodyIH =>
      simp only [nativeRename]
      congr 1
      · exact valueIH later earlier
      · calc
          nativeRename (nativeLiftRen later)
              (nativeRename (nativeLiftRen earlier) body) =
              nativeRename
                (fun index =>
                  nativeLiftRen later (nativeLiftRen earlier index)) body :=
            bodyIH (nativeLiftRen later) (nativeLiftRen earlier)
          _ = nativeRename
                (nativeLiftRen (fun index => later (earlier index))) body := by
            apply nativeRename_ext
            exact nativeLiftRen_comp_apply later earlier
  | pattern value => rfl
  | empty => rfl
  | superpose left right leftIH rightIH =>
      simp [nativeRename, leftIH later earlier, rightIH later earlier]
  | language value => rfl
  | quote route value valueIH =>
      simp [nativeRename, valueIH later earlier]

theorem nativeLiftSub_ext {left right : NativeSub source target}
    (pointwise : ∀ stage index, left stage index = right stage index) :
    ∀ stage index,
      nativeLiftSub left stage index = nativeLiftSub right stage index := by
  intro stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    simp [nativeLiftSub, pointwise stage previous]

theorem nativeSubst_ext {left right : NativeSub source target}
    (pointwise : ∀ stage index, left stage index = right stage index) :
    ∀ {stage} (term : StagedReflectiveTm stage source),
      nativeSubst left term = nativeSubst right term := by
  intro stage term
  induction term generalizing target with
  | var index => exact pointwise _ index
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [nativeSubst]
      congr 1
      · exact domainIH pointwise
      · exact bodyIH (nativeLiftSub_ext pointwise)
  | sigma domain body domainIH bodyIH =>
      simp only [nativeSubst]
      congr 1
      · exact domainIH pointwise
      · exact bodyIH (nativeLiftSub_ext pointwise)
  | id type leftTerm rightTerm typeIH leftIH rightIH =>
      simp [nativeSubst, typeIH pointwise, leftIH pointwise,
        rightIH pointwise]
  | lam body bodyIH =>
      simp only [nativeSubst]
      congr 1
      exact bodyIH (nativeLiftSub_ext pointwise)
  | app function argument functionIH argumentIH =>
      simp [nativeSubst, functionIH pointwise, argumentIH pointwise]
  | pair leftTerm rightTerm leftIH rightIH =>
      simp [nativeSubst, leftIH pointwise, rightIH pointwise]
  | fst pair pairIH => simp [nativeSubst, pairIH pointwise]
  | snd pair pairIH => simp [nativeSubst, pairIH pointwise]
  | refl value valueIH => simp [nativeSubst, valueIH pointwise]
  | letE value body valueIH bodyIH =>
      simp only [nativeSubst]
      congr 1
      · exact valueIH pointwise
      · exact bodyIH (nativeLiftSub_ext pointwise)
  | pattern value => rfl
  | empty => rfl
  | superpose leftTerm rightTerm leftIH rightIH =>
      simp [nativeSubst, leftIH pointwise, rightIH pointwise]
  | language value => rfl
  | quote route value valueIH => simp [nativeSubst, valueIH pointwise]

@[simp] theorem nativeLiftSub_ids :
    nativeLiftSub (nativeIds (binders := binders)) = nativeIds := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

@[simp] theorem nativeSubst_ids :
    ∀ {stage} (term : StagedReflectiveTm stage binders),
      nativeSubst nativeIds term = term := by
  intro stage term
  induction term with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp [nativeSubst, nativeLiftSub_ids, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [nativeSubst, nativeLiftSub_ids, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [nativeSubst, typeIH, leftIH, rightIH]
  | lam body bodyIH => simp [nativeSubst, nativeLiftSub_ids, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [nativeSubst, functionIH, argumentIH]
  | pair left right leftIH rightIH =>
      simp [nativeSubst, leftIH, rightIH]
  | fst pair pairIH => simp [nativeSubst, pairIH]
  | snd pair pairIH => simp [nativeSubst, pairIH]
  | refl value valueIH => simp [nativeSubst, valueIH]
  | letE value body valueIH bodyIH =>
      simp [nativeSubst, nativeLiftSub_ids, valueIH, bodyIH]
  | pattern value => rfl
  | empty => rfl
  | superpose left right leftIH rightIH =>
      simp [nativeSubst, leftIH, rightIH]
  | language value => rfl
  | quote route value valueIH => simp [nativeSubst, valueIH]

@[simp] theorem nativeLiftSubOfRen (rho : NativeRen source target) :
    nativeLiftSub (nativeSubOfRen rho) =
      nativeSubOfRen (nativeLiftRen rho) := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

/-- Renaming is exactly the variable-only instance of simultaneous
substitution. -/
theorem nativeSubst_ofRen (rho : NativeRen source target) :
    ∀ {stage} (term : StagedReflectiveTm stage source),
      nativeSubst (nativeSubOfRen rho) term = nativeRename rho term := by
  intro stage term
  induction term generalizing target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp [nativeSubst, nativeRename, nativeLiftSubOfRen, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [nativeSubst, nativeRename, nativeLiftSubOfRen, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [nativeSubst, nativeRename, typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      simp [nativeSubst, nativeRename, nativeLiftSubOfRen, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [nativeSubst, nativeRename, functionIH, argumentIH]
  | pair left right leftIH rightIH =>
      simp [nativeSubst, nativeRename, leftIH, rightIH]
  | fst pair pairIH => simp [nativeSubst, nativeRename, pairIH]
  | snd pair pairIH => simp [nativeSubst, nativeRename, pairIH]
  | refl value valueIH => simp [nativeSubst, nativeRename, valueIH]
  | letE value body valueIH bodyIH =>
      simp [nativeSubst, nativeRename, nativeLiftSubOfRen, valueIH, bodyIH]
  | pattern value => rfl
  | empty => rfl
  | superpose left right leftIH rightIH =>
      simp [nativeSubst, nativeRename, leftIH, rightIH]
  | language value => rfl
  | quote route value valueIH =>
      simp [nativeSubst, nativeRename, valueIH]

/-- Substitution under quotation visibly selects the stage-indexed environment
at the quotation source. -/
@[simp] theorem nativeSubst_quote
    (substitution : NativeSub source target)
    {high low : Nat} (route : StageHom high low)
    (term : StagedReflectiveTm high source) :
    nativeSubst substitution (StagedReflectiveTm.quote route term) =
      StagedReflectiveTm.quote route (nativeSubst substitution term) :=
  rfl

@[simp] theorem nativeRename_liftSub
    (rho : NativeRen middle target) (substitution : NativeSub source middle)
    (stage : Nat) (index : Fin (source + 1)) :
    nativeRename (nativeLiftRen rho)
        (nativeLiftSub substitution stage index) =
      nativeLiftSub
        (fun current index =>
          nativeRename rho (substitution current index)) stage index := by
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    calc
      nativeRename (nativeLiftRen rho)
          (nativeRename nativeWk (substitution stage previous)) =
          nativeRename
            (fun index => nativeLiftRen rho (nativeWk index))
            (substitution stage previous) :=
        nativeRename_comp (nativeLiftRen rho) nativeWk _
      _ = nativeRename (fun index => nativeWk (rho index))
            (substitution stage previous) := by
        apply nativeRename_ext
        intro index
        rfl
      _ = nativeRename nativeWk
            (nativeRename rho (substitution stage previous)) := by
        symm
        exact nativeRename_comp nativeWk rho _

/-- Renaming after substitution renames every member of the stage-indexed
environment. -/
theorem nativeRename_subst
    (rho : NativeRen middle target) (substitution : NativeSub source middle) :
    ∀ {stage} (term : StagedReflectiveTm stage source),
      nativeRename rho (nativeSubst substitution term) =
        nativeSubst
          (fun current index => nativeRename rho (substitution current index))
          term := by
  intro stage term
  induction term generalizing middle target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [nativeSubst, nativeRename]
      congr 1
      · exact domainIH rho substitution
      · calc
          nativeRename (nativeLiftRen rho)
              (nativeSubst (nativeLiftSub substitution) body) =
              nativeSubst
                (fun current index =>
                  nativeRename (nativeLiftRen rho)
                    (nativeLiftSub substitution current index)) body :=
            bodyIH (nativeLiftRen rho) (nativeLiftSub substitution)
          _ = nativeSubst
                (nativeLiftSub
                  (fun current index =>
                    nativeRename rho (substitution current index))) body := by
            apply nativeSubst_ext
            exact nativeRename_liftSub rho substitution
  | sigma domain body domainIH bodyIH =>
      simp only [nativeSubst, nativeRename]
      congr 1
      · exact domainIH rho substitution
      · calc
          nativeRename (nativeLiftRen rho)
              (nativeSubst (nativeLiftSub substitution) body) =
              nativeSubst
                (fun current index =>
                  nativeRename (nativeLiftRen rho)
                    (nativeLiftSub substitution current index)) body :=
            bodyIH (nativeLiftRen rho) (nativeLiftSub substitution)
          _ = nativeSubst
                (nativeLiftSub
                  (fun current index =>
                    nativeRename rho (substitution current index))) body := by
            apply nativeSubst_ext
            exact nativeRename_liftSub rho substitution
  | id type left right typeIH leftIH rightIH =>
      simp [nativeSubst, nativeRename, typeIH rho substitution,
        leftIH rho substitution, rightIH rho substitution]
  | lam body bodyIH =>
      simp only [nativeSubst, nativeRename]
      congr 1
      calc
        nativeRename (nativeLiftRen rho)
            (nativeSubst (nativeLiftSub substitution) body) =
            nativeSubst
              (fun current index =>
                nativeRename (nativeLiftRen rho)
                  (nativeLiftSub substitution current index)) body :=
          bodyIH (nativeLiftRen rho) (nativeLiftSub substitution)
        _ = nativeSubst
              (nativeLiftSub
                (fun current index =>
                  nativeRename rho (substitution current index))) body := by
          apply nativeSubst_ext
          exact nativeRename_liftSub rho substitution
  | app function argument functionIH argumentIH =>
      simp [nativeSubst, nativeRename, functionIH rho substitution,
        argumentIH rho substitution]
  | pair left right leftIH rightIH =>
      simp [nativeSubst, nativeRename, leftIH rho substitution,
        rightIH rho substitution]
  | fst pair pairIH => simp [nativeSubst, nativeRename, pairIH rho substitution]
  | snd pair pairIH => simp [nativeSubst, nativeRename, pairIH rho substitution]
  | refl value valueIH =>
      simp [nativeSubst, nativeRename, valueIH rho substitution]
  | letE value body valueIH bodyIH =>
      simp only [nativeSubst, nativeRename]
      congr 1
      · exact valueIH rho substitution
      · calc
          nativeRename (nativeLiftRen rho)
              (nativeSubst (nativeLiftSub substitution) body) =
              nativeSubst
                (fun current index =>
                  nativeRename (nativeLiftRen rho)
                    (nativeLiftSub substitution current index)) body :=
            bodyIH (nativeLiftRen rho) (nativeLiftSub substitution)
          _ = nativeSubst
                (nativeLiftSub
                  (fun current index =>
                    nativeRename rho (substitution current index))) body := by
            apply nativeSubst_ext
            exact nativeRename_liftSub rho substitution
  | pattern value => rfl
  | empty => rfl
  | superpose left right leftIH rightIH =>
      simp [nativeSubst, nativeRename, leftIH rho substitution,
        rightIH rho substitution]
  | language value => rfl
  | quote route value valueIH =>
      simp [nativeSubst, nativeRename, valueIH rho substitution]

@[simp] theorem nativeLiftSub_liftRen_apply
    (substitution : NativeSub middle target)
    (rho : NativeRen source middle) (stage : Nat)
    (index : Fin (source + 1)) :
    nativeLiftSub substitution stage (nativeLiftRen rho index) =
      nativeLiftSub
        (fun current index => substitution current (rho index))
        stage index := by
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

/-- Substitution after renaming selects the renamed variables from every stage
of the environment. -/
theorem nativeSubst_rename
    (substitution : NativeSub middle target)
    (rho : NativeRen source middle) :
    ∀ {stage} (term : StagedReflectiveTm stage source),
      nativeSubst substitution (nativeRename rho term) =
        nativeSubst
          (fun current index => substitution current (rho index)) term := by
  intro stage term
  induction term generalizing middle target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [nativeSubst, nativeRename]
      congr 1
      · exact domainIH substitution rho
      · calc
          nativeSubst (nativeLiftSub substitution)
              (nativeRename (nativeLiftRen rho) body) =
              nativeSubst
                (fun current index =>
                  nativeLiftSub substitution current
                    (nativeLiftRen rho index)) body :=
            bodyIH (nativeLiftSub substitution) (nativeLiftRen rho)
          _ = nativeSubst
                (nativeLiftSub
                  (fun current index => substitution current (rho index))) body := by
            apply nativeSubst_ext
            exact nativeLiftSub_liftRen_apply substitution rho
  | sigma domain body domainIH bodyIH =>
      simp only [nativeSubst, nativeRename]
      congr 1
      · exact domainIH substitution rho
      · calc
          nativeSubst (nativeLiftSub substitution)
              (nativeRename (nativeLiftRen rho) body) =
              nativeSubst
                (fun current index =>
                  nativeLiftSub substitution current
                    (nativeLiftRen rho index)) body :=
            bodyIH (nativeLiftSub substitution) (nativeLiftRen rho)
          _ = nativeSubst
                (nativeLiftSub
                  (fun current index => substitution current (rho index))) body := by
            apply nativeSubst_ext
            exact nativeLiftSub_liftRen_apply substitution rho
  | id type left right typeIH leftIH rightIH =>
      simp [nativeSubst, nativeRename, typeIH substitution rho,
        leftIH substitution rho, rightIH substitution rho]
  | lam body bodyIH =>
      simp only [nativeSubst, nativeRename]
      congr 1
      calc
        nativeSubst (nativeLiftSub substitution)
            (nativeRename (nativeLiftRen rho) body) =
            nativeSubst
              (fun current index =>
                nativeLiftSub substitution current
                  (nativeLiftRen rho index)) body :=
          bodyIH (nativeLiftSub substitution) (nativeLiftRen rho)
        _ = nativeSubst
              (nativeLiftSub
                (fun current index => substitution current (rho index))) body := by
          apply nativeSubst_ext
          exact nativeLiftSub_liftRen_apply substitution rho
  | app function argument functionIH argumentIH =>
      simp [nativeSubst, nativeRename, functionIH substitution rho,
        argumentIH substitution rho]
  | pair left right leftIH rightIH =>
      simp [nativeSubst, nativeRename, leftIH substitution rho,
        rightIH substitution rho]
  | fst pair pairIH => simp [nativeSubst, nativeRename, pairIH substitution rho]
  | snd pair pairIH => simp [nativeSubst, nativeRename, pairIH substitution rho]
  | refl value valueIH =>
      simp [nativeSubst, nativeRename, valueIH substitution rho]
  | letE value body valueIH bodyIH =>
      simp only [nativeSubst, nativeRename]
      congr 1
      · exact valueIH substitution rho
      · calc
          nativeSubst (nativeLiftSub substitution)
              (nativeRename (nativeLiftRen rho) body) =
              nativeSubst
                (fun current index =>
                  nativeLiftSub substitution current
                    (nativeLiftRen rho index)) body :=
            bodyIH (nativeLiftSub substitution) (nativeLiftRen rho)
          _ = nativeSubst
                (nativeLiftSub
                  (fun current index => substitution current (rho index))) body := by
            apply nativeSubst_ext
            exact nativeLiftSub_liftRen_apply substitution rho
  | pattern value => rfl
  | empty => rfl
  | superpose left right leftIH rightIH =>
      simp [nativeSubst, nativeRename, leftIH substitution rho,
        rightIH substitution rho]
  | language value => rfl
  | quote route value valueIH =>
      simp [nativeSubst, nativeRename, valueIH substitution rho]

@[simp] theorem nativeSubst_liftSub_wk
    (substitution : NativeSub source target)
    {stage : Nat} (term : StagedReflectiveTm stage source) :
    nativeSubst (nativeLiftSub substitution) (nativeRename nativeWk term) =
      nativeRename nativeWk (nativeSubst substitution term) := by
  calc
    nativeSubst (nativeLiftSub substitution) (nativeRename nativeWk term) =
        nativeSubst
          (fun current index => nativeLiftSub substitution current
            (nativeWk index)) term :=
      nativeSubst_rename (nativeLiftSub substitution) nativeWk term
    _ = nativeSubst
          (fun current index =>
            nativeRename nativeWk (substitution current index)) term := by
      rfl
    _ = nativeRename nativeWk (nativeSubst substitution term) := by
      symm
      exact nativeRename_subst nativeWk substitution term

@[simp] theorem nativeLiftSubComp_apply
    (later : NativeSub middle target) (earlier : NativeSub source middle)
    (stage : Nat) (index : Fin (source + 1)) :
    nativeSubComp (nativeLiftSub later) (nativeLiftSub earlier) stage index =
      nativeLiftSub (nativeSubComp later earlier) stage index := by
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    exact nativeSubst_liftSub_wk later (earlier stage previous)

/-- Associativity of stage-indexed simultaneous substitution. -/
@[simp] theorem nativeSubst_comp
    (later : NativeSub middle target) (earlier : NativeSub source middle) :
    ∀ {stage} (term : StagedReflectiveTm stage source),
      nativeSubst later (nativeSubst earlier term) =
        nativeSubst (nativeSubComp later earlier) term := by
  intro stage term
  induction term generalizing middle target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [nativeSubst]
      congr 1
      · exact domainIH later earlier
      · calc
          nativeSubst (nativeLiftSub later)
              (nativeSubst (nativeLiftSub earlier) body) =
              nativeSubst
                (nativeSubComp (nativeLiftSub later)
                  (nativeLiftSub earlier)) body :=
            bodyIH (nativeLiftSub later) (nativeLiftSub earlier)
          _ = nativeSubst
                (nativeLiftSub (nativeSubComp later earlier)) body := by
            apply nativeSubst_ext
            exact nativeLiftSubComp_apply later earlier
  | sigma domain body domainIH bodyIH =>
      simp only [nativeSubst]
      congr 1
      · exact domainIH later earlier
      · calc
          nativeSubst (nativeLiftSub later)
              (nativeSubst (nativeLiftSub earlier) body) =
              nativeSubst
                (nativeSubComp (nativeLiftSub later)
                  (nativeLiftSub earlier)) body :=
            bodyIH (nativeLiftSub later) (nativeLiftSub earlier)
          _ = nativeSubst
                (nativeLiftSub (nativeSubComp later earlier)) body := by
            apply nativeSubst_ext
            exact nativeLiftSubComp_apply later earlier
  | id type left right typeIH leftIH rightIH =>
      simp [nativeSubst, typeIH later earlier, leftIH later earlier,
        rightIH later earlier]
  | lam body bodyIH =>
      simp only [nativeSubst]
      congr 1
      calc
        nativeSubst (nativeLiftSub later)
            (nativeSubst (nativeLiftSub earlier) body) =
            nativeSubst
              (nativeSubComp (nativeLiftSub later)
                (nativeLiftSub earlier)) body :=
          bodyIH (nativeLiftSub later) (nativeLiftSub earlier)
        _ = nativeSubst
              (nativeLiftSub (nativeSubComp later earlier)) body := by
          apply nativeSubst_ext
          exact nativeLiftSubComp_apply later earlier
  | app function argument functionIH argumentIH =>
      simp [nativeSubst, functionIH later earlier, argumentIH later earlier]
  | pair left right leftIH rightIH =>
      simp [nativeSubst, leftIH later earlier, rightIH later earlier]
  | fst pair pairIH => simp [nativeSubst, pairIH later earlier]
  | snd pair pairIH => simp [nativeSubst, pairIH later earlier]
  | refl value valueIH => simp [nativeSubst, valueIH later earlier]
  | letE value body valueIH bodyIH =>
      simp only [nativeSubst]
      congr 1
      · exact valueIH later earlier
      · calc
          nativeSubst (nativeLiftSub later)
              (nativeSubst (nativeLiftSub earlier) body) =
              nativeSubst
                (nativeSubComp (nativeLiftSub later)
                  (nativeLiftSub earlier)) body :=
            bodyIH (nativeLiftSub later) (nativeLiftSub earlier)
          _ = nativeSubst
                (nativeLiftSub (nativeSubComp later earlier)) body := by
            apply nativeSubst_ext
            exact nativeLiftSubComp_apply later earlier
  | pattern value => rfl
  | empty => rfl
  | superpose left right leftIH rightIH =>
      simp [nativeSubst, leftIH later earlier, rightIH later earlier]
  | language value => rfl
  | quote route value valueIH =>
      simp [nativeSubst, valueIH later earlier]

@[simp] theorem nativeSubComp_left_id (substitution : NativeSub source target) :
    nativeSubComp nativeIds substitution = substitution := by
  funext stage index
  exact nativeSubst_ids (substitution stage index)

@[simp] theorem nativeSubComp_right_id (substitution : NativeSub source target) :
    nativeSubComp substitution nativeIds = substitution := by
  rfl

theorem nativeSubComp_assoc
    (third : NativeSub thirdSource target)
    (second : NativeSub secondSource thirdSource)
    (first : NativeSub source secondSource) :
    nativeSubComp third (nativeSubComp second first) =
      nativeSubComp (nativeSubComp third second) first := by
  funext stage index
  exact nativeSubst_comp third second (first stage index)

/-! ### Primitive sharing and profile-level inlining

Raw `letE` is a binder constructor.  Its possible inlining needs one
replacement at every stage because a body may contain quotation.  Therefore
the equation is expressed using an explicit stage family; raw syntax itself
does not invent cross-stage values. -/

/-- One term at every interpreter stage, with a common free-variable
support.  Q7 may later strengthen this bare family with quotation coherence. -/
abbrev NativeTermFamily (binders : Nat) :=
  (stage : Nat) → StagedReflectiveTm stage binders

/-- Extend the identity environment with a stage-polymorphic value at de
Bruijn index zero. -/
def nativeConsSub (value : NativeTermFamily binders) :
    NativeSub (binders + 1) binders :=
  fun stage => Fin.cases (value stage) (fun index => .var index)

@[simp] theorem nativeConsSub_zero (value : NativeTermFamily binders)
    (stage : Nat) :
    nativeConsSub value stage (0 : Fin (binders + 1)) = value stage :=
  rfl

@[simp] theorem nativeConsSub_succ (value : NativeTermFamily binders)
    (stage : Nat) (index : Fin binders) :
    nativeConsSub value stage index.succ =
      (StagedReflectiveTm.var index : StagedReflectiveTm stage binders) :=
  rfl

/-- Profile-level inlining for a stage-polymorphic shared value. -/
def nativeInlineLet (value : NativeTermFamily binders)
    (body : StagedReflectiveTm stage (binders + 1)) : StagedReflectiveTm stage binders :=
  nativeSubst (nativeConsSub value) body

@[simp] theorem nativeInlineLet_var_zero
    (value : NativeTermFamily binders) (stage : Nat) :
    nativeInlineLet value
        (StagedReflectiveTm.var (0 : Fin (binders + 1)) :
          StagedReflectiveTm stage (binders + 1)) =
      value stage :=
  rfl

/-- The smallest stage-polymorphic sharing value. -/
def nativeU0Family : NativeTermFamily binders := fun _ => .u0

/-- Positive raw witness: sharing is a genuine constructor before an equality
profile is selected. -/
theorem nativeLet_is_primitive_before_inlining :
    (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0) ≠
      nativeInlineLet nativeU0Family (.var (0 : Fin 1)) := by
  intro equal
  cases equal

/-- Objects of the support/substitution category.  The wrapper prevents the
native category structure from being confused with unrelated categories on
natural numbers. -/
structure NativeSupport where
  arity : Nat

namespace NativeSupport

instance : CategoryTheory.Category NativeSupport where
  Hom source target := NativeSub source.arity target.arity
  id _ := nativeIds
  comp earlier later := nativeSubComp later earlier
  id_comp morphism := nativeSubComp_right_id morphism
  comp_id morphism := nativeSubComp_left_id morphism
  assoc first second third := nativeSubComp_assoc third second first

end NativeSupport

/-- An algebra for the staged native raw signature.  `atStage` carries the
entire Pure algebra, which makes Pure operations available on every native
carrier rather than embedding Pure as an opaque leaf. -/
structure NativeRawAlgebra where
  atStage : Nat → PureRawAlgebra.{uRaw}
  pattern : {stage binders : Nat} → Pattern →
    (atStage stage).Carrier binders
  empty : {stage binders : Nat} → (atStage stage).Carrier binders
  superpose : {stage binders : Nat} → (atStage stage).Carrier binders →
    (atStage stage).Carrier binders → (atStage stage).Carrier binders
  letE : {stage binders : Nat} → (atStage stage).Carrier binders →
    (atStage stage).Carrier (binders + 1) → (atStage stage).Carrier binders
  language : {stage binders : Nat} →
    Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef →
    (atStage stage).Carrier binders
  quote : {high low binders : Nat} → StageHom high low →
    (atStage high).Carrier binders → (atStage low).Carrier binders

/-- Preservation of the staged native raw signature. -/
structure NativeRawPreserves
    (source : NativeRawAlgebra.{uRaw})
    (target : NativeRawAlgebra.{uRawTarget})
    (map : {stage binders : Nat} →
      (source.atStage stage).Carrier binders →
      (target.atStage stage).Carrier binders) : Prop where
  pure : ∀ stage, PureRawPreserves (source.atStage stage)
    (target.atStage stage) (fun term => map term)
  map_pattern : ∀ {stage binders} (value : Pattern),
    map (source.pattern (stage := stage) (binders := binders) value) =
      target.pattern value
  map_empty : ∀ {stage binders},
    map (source.empty (stage := stage) (binders := binders)) = target.empty
  map_superpose : ∀ {stage binders}
      (left right : (source.atStage stage).Carrier binders),
    map (source.superpose left right) = target.superpose (map left) (map right)
  map_letE : ∀ {stage binders}
      (value : (source.atStage stage).Carrier binders)
      (body : (source.atStage stage).Carrier (binders + 1)),
    map (source.letE value body) = target.letE (map value) (map body)
  map_language : ∀ {stage binders} value,
    map (source.language (stage := stage) (binders := binders) value) =
      target.language value
  map_quote : ∀ {high low binders} (route : StageHom high low)
      (term : (source.atStage high).Carrier binders),
    map (source.quote route term) = target.quote route (map term)

/-- A homomorphism of staged native raw algebras. -/
structure NativeRawHom
    (source : NativeRawAlgebra.{uRaw})
    (target : NativeRawAlgebra.{uRawTarget}) where
  map : {stage binders : Nat} →
    (source.atStage stage).Carrier binders →
    (target.atStage stage).Carrier binders
  preserves : NativeRawPreserves source target map

/-- The free native syntax as its own staged raw algebra. -/
abbrev nativeSyntaxAlgebra : NativeRawAlgebra where
  atStage := fun stage =>
    { Carrier := StagedReflectiveTm stage
      var := StagedReflectiveTm.var
      const := StagedReflectiveTm.const
      u0 := StagedReflectiveTm.u0
      u1 := StagedReflectiveTm.u1
      pi := StagedReflectiveTm.pi
      sigma := StagedReflectiveTm.sigma
      id := StagedReflectiveTm.id
      lam := StagedReflectiveTm.lam
      app := StagedReflectiveTm.app
      pair := StagedReflectiveTm.pair
      fst := StagedReflectiveTm.fst
      snd := StagedReflectiveTm.snd
      refl := StagedReflectiveTm.refl }
  pattern := StagedReflectiveTm.pattern
  empty := StagedReflectiveTm.empty
  superpose := StagedReflectiveTm.superpose
  letE := StagedReflectiveTm.letE
  language := StagedReflectiveTm.language
  quote := StagedReflectiveTm.quote

/-- Structural interpretation of native raw syntax in any native algebra. -/
def nativeRawFold (target : NativeRawAlgebra.{uRawTarget}) :
    {stage binders : Nat} → StagedReflectiveTm stage binders →
      (target.atStage stage).Carrier binders
  | _, _, .var index => (target.atStage _).var index
  | _, _, .const name => (target.atStage _).const name
  | _, _, .u0 => (target.atStage _).u0
  | _, _, .u1 => (target.atStage _).u1
  | _, _, .pi domain body =>
      (target.atStage _).pi (nativeRawFold target domain)
        (nativeRawFold target body)
  | _, _, .sigma domain body =>
      (target.atStage _).sigma (nativeRawFold target domain)
        (nativeRawFold target body)
  | _, _, .id type left right =>
      (target.atStage _).id (nativeRawFold target type)
        (nativeRawFold target left) (nativeRawFold target right)
  | _, _, .lam body => (target.atStage _).lam (nativeRawFold target body)
  | _, _, .app function argument =>
      (target.atStage _).app (nativeRawFold target function)
        (nativeRawFold target argument)
  | _, _, .pair left right =>
      (target.atStage _).pair (nativeRawFold target left)
        (nativeRawFold target right)
  | _, _, .fst pair => (target.atStage _).fst (nativeRawFold target pair)
  | _, _, .snd pair => (target.atStage _).snd (nativeRawFold target pair)
  | _, _, .refl term => (target.atStage _).refl (nativeRawFold target term)
  | _, _, .pattern value => target.pattern value
  | _, _, .empty => target.empty
  | _, _, .superpose left right =>
      target.superpose (nativeRawFold target left) (nativeRawFold target right)
  | _, _, .letE value body =>
      target.letE (nativeRawFold target value) (nativeRawFold target body)
  | _, _, .language value => target.language value
  | _, _, .quote route term => target.quote route (nativeRawFold target term)

/-- The structural fold is a native raw-algebra homomorphism. -/
def nativeRawFoldHom (target : NativeRawAlgebra.{uRawTarget}) :
    NativeRawHom nativeSyntaxAlgebra target where
  map := nativeRawFold target
  preserves := by
    constructor
    · intro stage
      constructor <;> intros <;> rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl

/-- Any native raw-algebra homomorphism agrees pointwise with structural
fold. -/
theorem nativeRawFold_unique_pointwise
    (target : NativeRawAlgebra.{uRawTarget})
    (hom : NativeRawHom nativeSyntaxAlgebra target) :
    ∀ {stage binders} (term : StagedReflectiveTm stage binders),
      hom.map term = nativeRawFold target term := by
  intro stage binders term
  induction term with
  | var index => exact (hom.preserves.pure _).map_var index
  | const name => exact (hom.preserves.pure _).map_const name
  | u0 => exact (hom.preserves.pure _).map_u0
  | u1 => exact (hom.preserves.pure _).map_u1
  | pi domain body domainIH bodyIH =>
      rw [(hom.preserves.pure _).map_pi, domainIH, bodyIH]
      rfl
  | sigma domain body domainIH bodyIH =>
      rw [(hom.preserves.pure _).map_sigma, domainIH, bodyIH]
      rfl
  | id type left right typeIH leftIH rightIH =>
      rw [(hom.preserves.pure _).map_id, typeIH, leftIH, rightIH]
      rfl
  | lam body bodyIH =>
      rw [(hom.preserves.pure _).map_lam, bodyIH]
      rfl
  | app function argument functionIH argumentIH =>
      rw [(hom.preserves.pure _).map_app, functionIH, argumentIH]
      rfl
  | pair left right leftIH rightIH =>
      rw [(hom.preserves.pure _).map_pair, leftIH, rightIH]
      rfl
  | fst pair pairIH =>
      rw [(hom.preserves.pure _).map_fst, pairIH]
      rfl
  | snd pair pairIH =>
      rw [(hom.preserves.pure _).map_snd, pairIH]
      rfl
  | refl term termIH =>
      rw [(hom.preserves.pure _).map_refl, termIH]
      rfl
  | pattern value => exact hom.preserves.map_pattern value
  | empty => exact hom.preserves.map_empty
  | superpose left right leftIH rightIH =>
      rw [hom.preserves.map_superpose, leftIH, rightIH]
      rfl
  | letE value body valueIH bodyIH =>
      rw [hom.preserves.map_letE, valueIH, bodyIH]
      rfl
  | language value => exact hom.preserves.map_language value
  | quote route term termIH =>
      rw [hom.preserves.map_quote, termIH]
      rfl

@[ext] theorem NativeRawHom.ext
    {source : NativeRawAlgebra.{uRaw}}
    {target : NativeRawAlgebra.{uRawTarget}}
    (left right : NativeRawHom source target)
    (mapsEqual : ∀ {stage binders}
      (term : (source.atStage stage).Carrier binders),
      left.map term = right.map term) :
    left = right := by
  cases left with
  | mk leftMap leftPreserves =>
    cases right with
    | mk rightMap rightPreserves =>
      have mapEquality :
          (@leftMap : (stage binders : Nat) →
            (source.atStage stage).Carrier binders →
            (target.atStage stage).Carrier binders) = @rightMap := by
        funext stage binders term
        exact mapsEqual term
      cases mapEquality
      rfl

/-- Native raw syntax is initial among algebras of the complete extended raw
signature. -/
theorem nativeRawFold_unique
    (target : NativeRawAlgebra.{uRawTarget})
    (hom : NativeRawHom nativeSyntaxAlgebra target) :
    hom = nativeRawFoldHom target := by
  apply NativeRawHom.ext
  exact nativeRawFold_unique_pointwise target hom

/-! ### Conservative inclusion of intrinsic Pure -/

/-- Embed an intrinsic Pure term at any native stage.  This is the structural
Pure fold into that stage, so every Pure constructor remains visible. -/
def embedPure (stage : Nat) : {binders : Nat} → PureTm binders →
    StagedReflectiveTm stage binders
  | _, .var index => .var index
  | _, .const name => .const name
  | _, .u0 => .u0
  | _, .u1 => .u1
  | _, .pi domain body => .pi (embedPure stage domain) (embedPure stage body)
  | _, .sigma domain body =>
      .sigma (embedPure stage domain) (embedPure stage body)
  | _, .id type left right =>
      .id (embedPure stage type) (embedPure stage left) (embedPure stage right)
  | _, .lam body => .lam (embedPure stage body)
  | _, .app function argument =>
      .app (embedPure stage function) (embedPure stage argument)
  | _, .pair left right => .pair (embedPure stage left) (embedPure stage right)
  | _, .fst pair => .fst (embedPure stage pair)
  | _, .snd pair => .snd (embedPure stage pair)
  | _, .refl term => .refl (embedPure stage term)

/-- Embed an intrinsic Pure simultaneous substitution independently at every
stage. -/
def embedPureSub
    (substitution : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub
      source target) : NativeSub source target :=
  fun stage index => embedPure stage (substitution index)

/-- Native renaming restricts exactly to the live intrinsic Pure renaming. -/
theorem nativeRename_embedPure (rho : NativeRen source target) (stage : Nat) :
    ∀ term : PureTm source,
      nativeRename rho (embedPure stage term) =
        embedPure stage
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename rho term) := by
  intro term
  induction term generalizing target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename]
      congr 1
      · exact domainIH rho
      · rw [nativeLiftRen_eq_pureLiftRen rho]
        exact bodyIH _
  | sigma domain body domainIH bodyIH =>
      simp only [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename]
      congr 1
      · exact domainIH rho
      · rw [nativeLiftRen_eq_pureLiftRen rho]
        exact bodyIH _
  | id type left right typeIH leftIH rightIH =>
      simp [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename,
        typeIH rho, leftIH rho, rightIH rho]
  | lam body bodyIH =>
      simp only [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename]
      congr 1
      rw [nativeLiftRen_eq_pureLiftRen rho]
      exact bodyIH _
  | app function argument functionIH argumentIH =>
      simp [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename,
        functionIH rho, argumentIH rho]
  | pair left right leftIH rightIH =>
      simp [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename,
        leftIH rho, rightIH rho]
  | fst pair pairIH =>
      simp [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename, pairIH rho]
  | snd pair pairIH =>
      simp [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename, pairIH rho]
  | refl value valueIH =>
      simp [embedPure, nativeRename,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename, valueIH rho]

/-- Lifting an embedded Pure substitution agrees with embedding the intrinsic
Pure lift. -/
theorem nativeLiftSub_embedPureSub
    (substitution : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub
      source target) :
    nativeLiftSub (embedPureSub substitution) =
      embedPureSub
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.liftSub
          substitution) := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    exact nativeRename_embedPure nativeWk stage (substitution previous)

/-- Native simultaneous substitution restricts exactly to the live intrinsic
Pure simultaneous substitution. -/
theorem nativeSubst_embedPure
    (substitution : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.Sub
      source target) (stage : Nat) :
    ∀ term : PureTm source,
      nativeSubst (embedPureSub substitution) (embedPure stage term) =
        embedPure stage
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
            substitution term) := by
  intro term
  induction term generalizing target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst]
      congr 1
      · exact domainIH substitution
      · rw [nativeLiftSub_embedPureSub]
        exact bodyIH
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.liftSub
            substitution)
  | sigma domain body domainIH bodyIH =>
      simp only [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst]
      congr 1
      · exact domainIH substitution
      · rw [nativeLiftSub_embedPureSub]
        exact bodyIH
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.liftSub
            substitution)
  | id type left right typeIH leftIH rightIH =>
      simp [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst,
        typeIH substitution, leftIH substitution, rightIH substitution]
  | lam body bodyIH =>
      simp only [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst]
      congr 1
      rw [nativeLiftSub_embedPureSub]
      exact bodyIH
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.liftSub substitution)
  | app function argument functionIH argumentIH =>
      simp [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst,
        functionIH substitution, argumentIH substitution]
  | pair left right leftIH rightIH =>
      simp [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst,
        leftIH substitution, rightIH substitution]
  | fst pair pairIH =>
      simp [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst,
        pairIH substitution]
  | snd pair pairIH =>
      simp [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst,
        pairIH substitution]
  | refl value valueIH =>
      simp [embedPure, nativeSubst,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst,
        valueIH substitution]

/-- Partial erasure of a native term to the Pure fragment.  Every genuinely
native constructor is rejected; mixed terms containing one are rejected
recursively. -/
def StagedReflectiveTm.pureProjection :
    {stage binders : Nat} → StagedReflectiveTm stage binders → Option (PureTm binders)
  | _, _, .var index => some (.var index)
  | _, _, .const name => some (.const name)
  | _, _, .u0 => some .u0
  | _, _, .u1 => some .u1
  | _, _, .pi domain body => do
      let domain' ← domain.pureProjection
      let body' ← body.pureProjection
      pure (.pi domain' body')
  | _, _, .sigma domain body => do
      let domain' ← domain.pureProjection
      let body' ← body.pureProjection
      pure (.sigma domain' body')
  | _, _, .id type left right => do
      let type' ← type.pureProjection
      let left' ← left.pureProjection
      let right' ← right.pureProjection
      pure (.id type' left' right')
  | _, _, .lam body => return .lam (← body.pureProjection)
  | _, _, .app function argument =>
      return .app (← function.pureProjection) (← argument.pureProjection)
  | _, _, .pair left right =>
      return .pair (← left.pureProjection) (← right.pureProjection)
  | _, _, StagedReflectiveTm.fst value =>
      return PureTm.fst (← value.pureProjection)
  | _, _, StagedReflectiveTm.snd value =>
      return PureTm.snd (← value.pureProjection)
  | _, _, StagedReflectiveTm.refl value =>
      return PureTm.refl (← value.pureProjection)
  | _, _, .letE _ _ => none
  | _, _, .pattern _ => none
  | _, _, .empty => none
  | _, _, .superpose _ _ => none
  | _, _, .language _ => none
  | _, _, .quote _ _ => none

@[simp] theorem pureProjection_embedPure (stage : Nat) {binders : Nat}
    (term : PureTm binders) :
    (embedPure stage term).pureProjection = some term := by
  induction term with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH => simp [embedPure, domainIH, bodyIH,
      StagedReflectiveTm.pureProjection]
  | sigma domain body domainIH bodyIH => simp [embedPure, domainIH, bodyIH,
      StagedReflectiveTm.pureProjection]
  | id type left right typeIH leftIH rightIH => simp [embedPure,
      typeIH, leftIH, rightIH, StagedReflectiveTm.pureProjection]
  | lam body bodyIH => simp [embedPure, bodyIH,
      StagedReflectiveTm.pureProjection]
  | app function argument functionIH argumentIH => simp [embedPure,
      functionIH, argumentIH, StagedReflectiveTm.pureProjection]
  | pair left right leftIH rightIH => simp [embedPure, leftIH,
      rightIH, StagedReflectiveTm.pureProjection]
  | fst pair pairIH => simp [embedPure, pairIH,
      StagedReflectiveTm.pureProjection]
  | snd pair pairIH => simp [embedPure, pairIH,
      StagedReflectiveTm.pureProjection]
  | refl term termIH => simp [embedPure, termIH,
      StagedReflectiveTm.pureProjection]

/-- The intrinsic Pure fragment embeds conservatively into every native
stage. -/
theorem embedPure_injective (stage : Nat) {binders : Nat} :
    Function.Injective (embedPure stage : PureTm binders → StagedReflectiveTm stage binders) := by
  intro left right equal
  have projected := congrArg StagedReflectiveTm.pureProjection equal
  simpa using projected

/-- Raw syntactic equality is reflected exactly by the Pure embedding. -/
theorem embedPure_eq_iff (stage : Nat) {binders : Nat}
    (left right : PureTm binders) :
    embedPure stage left = embedPure stage right ↔ left = right :=
  ⟨fun equal => embedPure_injective stage equal,
    fun equal => congrArg (embedPure stage) equal⟩

/-- A genuine stage descent introducing one quotation layer. -/
def oneToZeroQuotation : StageHom 1 0 := ⟨by omega, 1⟩

/-- A substitution whose variable image genuinely depends on interpreter
stage.  This is the smallest positive witness that the stage index in
`NativeSub` carries information. -/
def stageSensitiveSub : NativeSub 1 0 :=
  fun stage _ => if stage = 0 then .u0 else .u1

theorem stageSensitiveSub_zero_component :
    stageSensitiveSub 0 (0 : Fin 1) = (StagedReflectiveTm.u0 : StagedReflectiveTm 0 0) := by
  rfl

theorem stageSensitiveSub_one_component :
    stageSensitiveSub 1 (0 : Fin 1) = (StagedReflectiveTm.u1 : StagedReflectiveTm 1 0) := by
  rfl

/-- Unquoted syntax selects the current stage's component. -/
theorem stageSensitiveSub_unquoted :
    nativeSubst stageSensitiveSub (StagedReflectiveTm.var (0 : Fin 1) :
      StagedReflectiveTm 0 1) = .u0 := by
  rfl

/-- Quoted syntax selects the quotation source stage's component rather than
reusing the surrounding stage-zero component. -/
theorem stageSensitiveSub_quoted :
    nativeSubst stageSensitiveSub
        (StagedReflectiveTm.quote oneToZeroQuotation
          (StagedReflectiveTm.var (0 : Fin 1) : StagedReflectiveTm 1 1)) =
      StagedReflectiveTm.quote oneToZeroQuotation
        (StagedReflectiveTm.u1 : StagedReflectiveTm 1 0) := by
  rfl

/-- A stage-polymorphic substitution is projection-constant when all of its
stage components erase to the same Pure environment. -/
def PureProjectionStageConstant (substitution : NativeSub source target) : Prop :=
  ∀ first second index,
    (substitution first index).pureProjection =
      (substitution second index).pureProjection

/-- Negative witness: valid native substitutions need not arise by copying one
stage-local environment to every stage. -/
theorem stageSensitiveSub_not_projection_constant :
    ¬ PureProjectionStageConstant stageSensitiveSub := by
  intro constant
  have equalProjections := constant 0 1 (0 : Fin 1)
  change (some PureTm.u0 : Option (PureTm 0)) = some PureTm.u1 at equalProjections
  cases equalProjections

/-- Positive native-only witness: the new presentation contains staged code. -/
def quotedPureUniverse : StagedReflectiveTm 0 0 :=
  .quote oneToZeroQuotation (.u0 : StagedReflectiveTm 1 0)

/-- Negative image witness: quotation is not an alternative spelling of any
intrinsic Pure term. -/
theorem quotedPureUniverse_not_in_pure_image :
    ¬ ∃ term : PureTm 0, embedPure 0 term = quotedPureUniverse := by
  rintro ⟨term, equal⟩
  have projected := congrArg StagedReflectiveTm.pureProjection equal
  rw [pureProjection_embedPure] at projected
  change (some term : Option (PureTm 0)) = none at projected
  cases projected

/-- A mixed term demonstrates that Pure operations act on genuinely native
subterms rather than treating the Pure fragment as an opaque leaf. -/
def mixedNativeApplication : StagedReflectiveTm 0 0 :=
  .app (.lam (.var (0 : Fin 1))) quotedPureUniverse

theorem mixedNativeApplication_not_in_pure_image :
    ¬ ∃ term : PureTm 0, embedPure 0 term = mixedNativeApplication := by
  rintro ⟨term, equal⟩
  have projected := congrArg StagedReflectiveTm.pureProjection equal
  rw [pureProjection_embedPure] at projected
  change (some term : Option (PureTm 0)) = none at projected
  cases projected

/-- Any term rejected by the Pure projection is outside the conservative Pure
image.  This one lemma supplies the negative half for every genuinely native
constructor. -/
theorem pureProjection_none_not_in_pure_image
    {stage binders : Nat} (native : StagedReflectiveTm stage binders)
    (notPure : native.pureProjection = none) :
    ¬ ∃ pure : PureTm binders, embedPure stage pure = native := by
  rintro ⟨pure, equal⟩
  have projected := congrArg StagedReflectiveTm.pureProjection equal
  rw [pureProjection_embedPure, notPure] at projected
  cases projected

/-- Positive Pattern witness in the native raw presentation. -/
def nativeRuntimePattern : StagedReflectiveTm 0 0 :=
  .pattern familiesPatternMarker

theorem nativeRuntimePattern_not_in_pure_image :
    ¬ ∃ pure : PureTm 0, embedPure 0 pure = nativeRuntimePattern :=
  pureProjection_none_not_in_pure_image nativeRuntimePattern rfl

/-- Positive collection witness containing two distinct Pure universes. -/
def nativeUniverseSuperposition : StagedReflectiveTm 0 0 :=
  .superpose .u0 .u1

theorem nativeUniverseSuperposition_not_in_pure_image :
    ¬ ∃ pure : PureTm 0, embedPure 0 pure = nativeUniverseSuperposition :=
  pureProjection_none_not_in_pure_image nativeUniverseSuperposition rfl

/-- Positive first-class language witness: today's validated Prime
presentation is an intrinsic native value, but is not confused with a Pure
term. -/
def nativeCurrentPrimeLanguage : StagedReflectiveTm 0 0 :=
  .language
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation

theorem nativeCurrentPrimeLanguage_not_in_pure_image :
    ¬ ∃ pure : PureTm 0, embedPure 0 pure = nativeCurrentPrimeLanguage :=
  pureProjection_none_not_in_pure_image nativeCurrentPrimeLanguage rfl

/-! ### The intrinsic Pure contextual refinement

The raw native ABT has more substitutions than intrinsic Pure: a native
substitution supplies one variable image at every stage, because substitution
under quotation must select the quotation source stage.  Intrinsic Pure embeds
as the stage-uniform part.  This section retains Pure's actual hypothetical
judgment and typed simultaneous substitutions, proves their laws, and maps
them faithfully into the native support category.

This is deliberately not the modal typing presentation constructed below.
In particular, it does not manufacture a Fitch lock from quotation: the
negative non-fullness theorem below exhibits a native stage-sensitive
substitution that no intrinsic Pure context morphism can supply. -/

namespace IntrinsicPureRefinement

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing
open CategoryTheory
open scoped CategoryTheory

/-- Typed identity substitution for the live intrinsic Pure judgment. -/
theorem ctxMor_ids (context : Ctx binders) :
    CtxMor context context (ids (n := binders)) := by
  intro index
  change HasType context (.var index) (subst ids (lookup context index))
  rw [subst_ids]
  exact HasType.var index

/-- Execution-order composition of intrinsic Pure substitutions. -/
def pureSubComp (later : Sub middle target) (earlier : Sub source middle) :
    Sub source target :=
  fun index => subst later (earlier index)

/-- Typed context morphisms are closed under simultaneous-substitution
composition. -/
theorem ctxMor_comp {sourceContext : Ctx source}
    {middleContext : Ctx middle} {targetContext : Ctx target}
    {earlier : Sub source middle} {later : Sub middle target}
    (earlierTyped : CtxMor sourceContext middleContext earlier)
    (laterTyped : CtxMor middleContext targetContext later) :
    CtxMor sourceContext targetContext (pureSubComp later earlier) := by
  intro index
  have typed := typing_subst (earlierTyped index) laterTyped
  rw [subst_comp] at typed
  change HasType targetContext (subst later (earlier index))
    (subst (fun inner => subst later (earlier inner))
      (lookup sourceContext index))
  exact typed

/-- One intrinsically typed Pure context, retaining its telescope length. -/
structure ContextObject where
  arity : Nat
  context : Ctx arity

/-- A morphism is an actual typed simultaneous substitution, not merely a
function between the underlying finite supports. -/
structure TypedSub (source target : ContextObject) where
  map : Sub source.arity target.arity
  typed : CtxMor source.context target.context map

namespace TypedSub

@[ext]
theorem ext {source target : ContextObject}
    {first second : TypedSub source target}
    (map : first.map = second.map) : first = second := by
  cases first
  cases second
  cases map
  rfl

end TypedSub

/-- Intrinsic Pure contexts and typed substitutions form a category. -/
instance : CategoryTheory.Category ContextObject where
  Hom := TypedSub
  id object := ⟨ids, ctxMor_ids object.context⟩
  comp earlier later :=
    ⟨pureSubComp later.map earlier.map,
      ctxMor_comp earlier.typed later.typed⟩
  id_comp morphism := by
    apply TypedSub.ext
    funext index
    rfl
  comp_id morphism := by
    apply TypedSub.ext
    funext index
    exact subst_ids (t := morphism.map index)
  assoc first second third := by
    apply TypedSub.ext
    funext index
    exact subst_comp third.map second.map (first.map index)

/-- Embedding commutes with composition of Pure substitutions. -/
theorem embedPureSub_comp (later : Sub middle target)
    (earlier : Sub source middle) :
    embedPureSub (pureSubComp later earlier) =
      nativeSubComp (embedPureSub later) (embedPureSub earlier) := by
  funext stage index
  exact (nativeSubst_embedPure later stage (earlier index)).symm

/-- Forget the telescope types while retaining the complete staged native
substitution.  This is the contextual refinement map into the support-indexed
ABT substitution category. -/
def toNativeSupport : CategoryTheory.Functor ContextObject NativeSupport where
  obj object := ⟨object.arity⟩
  map substitution := embedPureSub substitution.map
  map_id object := by
    funext stage index
    rfl
  map_comp earlier later := embedPureSub_comp later.map earlier.map

/-- The contextual refinement is faithful: native equality of embedded typed
substitutions reflects equality of the intrinsic Pure maps. -/
theorem toNativeSupport_map_injective
    {source target : ContextObject} :
    Function.Injective
      (fun substitution : TypedSub source target =>
        toNativeSupport.map substitution) := by
  intro left right equal
  apply TypedSub.ext
  funext index
  have component := congrFun (congrFun equal 0) index
  exact embedPure_injective 0 component

/-- Proof-relevant refinement of one intrinsic Pure hypothetical judgment
into native raw syntax at a selected stage.  The original derivation is
retained together with exact source-term and source-type equations. -/
structure TypingAt (stage : Nat) (context : Ctx binders)
    (term type : StagedReflectiveTm stage binders) where
  sourceTerm : PureTm binders
  sourceType : PureTm binders
  sourceTyping : HasType context sourceTerm sourceType
  term_eq : term = embedPure stage sourceTerm
  type_eq : type = embedPure stage sourceType

/-- Embedded typing is reflected exactly; the refinement does not create new
Pure derivations on the Pure image. -/
theorem typingAt_embed_iff (stage : Nat) (context : Ctx binders)
    (term type : PureTm binders) :
    Nonempty (TypingAt stage context (embedPure stage term)
      (embedPure stage type)) ↔ HasType context term type := by
  constructor
  · rintro ⟨refinement⟩
    have termEqual : term = refinement.sourceTerm :=
      embedPure_injective stage refinement.term_eq
    have typeEqual : type = refinement.sourceType :=
      embedPure_injective stage refinement.type_eq
    simpa [termEqual, typeEqual] using refinement.sourceTyping
  · intro typed
    exact ⟨⟨term, type, typed, rfl, rfl⟩⟩

/-- Typed simultaneous substitution commutes with the refinement map.  The
result uses Pure's real `typing_subst` theorem and the previously proved ABT
substitution square. -/
def TypingAt.subst {stage : Nat} {sourceContext : Ctx source}
    {targetContext : Ctx target} {term type : StagedReflectiveTm stage source}
    (typing : TypingAt stage sourceContext term type)
    (substitution : Sub source target)
    (substitutionTyped : CtxMor sourceContext targetContext substitution) :
    TypingAt stage targetContext
      (nativeSubst (embedPureSub substitution) term)
      (nativeSubst (embedPureSub substitution) type) where
  sourceTerm :=
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
      substitution typing.sourceTerm
  sourceType :=
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst
      substitution typing.sourceType
  sourceTyping := typing_subst typing.sourceTyping substitutionTyped
  term_eq :=
    (congrArg (nativeSubst (embedPureSub substitution)) typing.term_eq).trans
      (nativeSubst_embedPure substitution stage typing.sourceTerm)
  type_eq :=
    (congrArg (nativeSubst (embedPureSub substitution)) typing.type_eq).trans
      (nativeSubst_embedPure substitution stage typing.sourceType)

/-- Pointwise context conversion retains the exact embedded native term and
type while changing the source hypothetical context. -/
def TypingAt.contextConv {stage binders : Nat}
    {sourceContext targetContext : Ctx binders}
    {term type : StagedReflectiveTm stage binders}
    (conversion : ∀ index : Fin binders,
      Conv (lookup sourceContext index) (lookup targetContext index))
    (typing : TypingAt stage sourceContext term type) :
    TypingAt stage targetContext term type where
  sourceTerm := typing.sourceTerm
  sourceType := typing.sourceType
  sourceTyping := context_conv conversion typing.sourceTyping
  term_eq := typing.term_eq
  type_eq := typing.type_eq

/-- Positive contextual witness: Pure's universe judgment embeds at every
stage and in every intrinsic context. -/
def u0Typing (stage : Nat) (context : Ctx binders) :
    TypingAt stage context (.u0 : StagedReflectiveTm stage binders) .u1 :=
  ⟨.u0, .u1, HasType.u0_type context, rfl, rfl⟩

/-- A one-variable context supplies a nonempty hom fibre: its typed identity
maps to the native identity substitution. -/
def oneUniverseContext : ContextObject :=
  ⟨1, .snoc .nil .u0⟩

def oneUniverseIdentity :
    TypedSub oneUniverseContext oneUniverseContext :=
  ⟨ids, ctxMor_ids oneUniverseContext.context⟩

theorem oneUniverseContext_identity_maps_to_native_identity :
    toNativeSupport.map oneUniverseIdentity = nativeIds := by
  rfl

/-- A native endosubstitution whose zeroth-stage component is the variable
and whose positive-stage components are the universe. -/
def stageSensitiveEndSub : NativeSub 1 1 :=
  fun stage index => if stage = 0 then .var index else .u0

/-- Negative refinement witness: the contextual functor is not full into all
native substitutions.  Stage sensitivity is real extra native structure, not
an alternative encoding of one Pure typed substitution. -/
theorem stageSensitiveEndSub_has_no_typedPure_preimage :
    ¬ ∃ substitution : TypedSub oneUniverseContext oneUniverseContext,
      toNativeSupport.map substitution = stageSensitiveEndSub := by
  rintro ⟨substitution, equal⟩
  let index : Fin oneUniverseContext.arity := ⟨0, by decide⟩
  have atZero := congrFun (congrFun equal 0) index
  have atOne := congrFun (congrFun equal 1) index
  change embedPure 0 (substitution.map index) =
    embedPure 0 (PureTm.var index) at atZero
  change embedPure 1 (substitution.map index) =
    embedPure 1 PureTm.u0 at atOne
  have zeroSource : substitution.map index = PureTm.var index :=
    embedPure_injective 0 atZero
  have oneSource : substitution.map index = PureTm.u0 :=
    embedPure_injective 1 atOne
  have impossible : PureTm.var index = .u0 :=
    zeroSource.symm.trans oneSource
  cases impossible

/-- Native quotation is outside the intrinsic typed refinement, independently
of which native type one proposes for it.  Typing quotation therefore uses the
genuine modal context/lock rules of the native judgment below. -/
theorem quotedPureUniverse_has_no_intrinsic_typing :
    ¬ ∃ type : StagedReflectiveTm 0 0,
      Nonempty (TypingAt 0 .nil quotedPureUniverse type) := by
  rintro ⟨type, refinement⟩
  rcases refinement with ⟨refinement⟩
  apply quotedPureUniverse_not_in_pure_image
  exact ⟨refinement.sourceTerm, refinement.term_eq.symm⟩

end IntrinsicPureRefinement

/-! ### A modal hypothetical judgment over the native ABT

Intrinsic Pure supplies the dependent core, but quotation crosses interpreter
stages.  A variable occurring below a quotation therefore needs an image at
the quotation's source stage.  The native substitution algebra already
records exactly this data: `NativeSub source target` is indexed by stage.

The contextual presentation below follows that fact rather than pretending a
single-stage argument can be retyped at every stage.  Context entries and
substitutable arguments are stage-indexed families.  Conversion is an
explicit parameter whose only laws here are equivalence and substitution
stability.  The selected architecture later fixes syntactic conversion as the
kernel core and exposes stronger policies only through explicit extension. -/

namespace NativeModalTyping

/-- A term available coherently as syntax at every interpreter stage. -/
abbrev TermFamily (binders : Nat) :=
  (stage : Nat) → StagedReflectiveTm stage binders

/-- Telescope contexts whose entries have a component at every stage. -/
inductive Context : Nat → Type where
  | nil : Context 0
  | snoc : Context binders → TermFamily binders → Context (binders + 1)
  /-- A Fitch-style source-context lock for one explicit stage route.  The
  lock changes contextual structure without inventing a term variable. -/
  | lock {high low binders : Nat} : StageHom high low →
      Context binders → Context binders

/-- Lookup at a selected stage, weakened into the full telescope. -/
def Context.lookup : Context binders →
    (stage : Nat) → Fin binders → StagedReflectiveTm stage binders
  | .nil, _, index => nomatch index
  | .snoc context type, stage, index =>
      Fin.cases (nativeRename nativeWk (type stage))
        (fun previous =>
          nativeRename nativeWk (Context.lookup context stage previous)) index
  | .lock _ context, stage, index => Context.lookup context stage index

@[simp] theorem Context.lookup_snoc_zero
    (context : Context binders) (type : TermFamily binders) (stage : Nat) :
    Context.lookup (.snoc context type) stage 0 =
      nativeRename nativeWk (type stage) :=
  rfl

@[simp] theorem Context.lookup_snoc_succ
    (context : Context binders) (type : TermFamily binders) (stage : Nat)
    (index : Fin binders) :
    Context.lookup (.snoc context type) stage index.succ =
      nativeRename nativeWk (Context.lookup context stage index) :=
  rfl

@[simp] theorem Context.lookup_lock
    (route : StageHom high low) (context : Context binders)
    (stage : Nat) (index : Fin binders) :
    Context.lookup (.lock route context) stage index =
      Context.lookup context stage index :=
  rfl

/-- A lock is genuine contextual syntax, not an alias for the context it
guards. -/
theorem Context.lock_ne_unlocked (route : StageHom high low)
    (context : Context binders) :
    Context.lock route context ≠ context := by
  intro equal
  cases context <;> cases equal

/-- The equality data needed by the conversion rule and typed substitution.
Congruence and computational adequacy remain separate extension-profile
demands; they are not smuggled into this minimal substitution doctrine. -/
structure ConversionPolicy where
  Rel : {stage binders : Nat} →
    StagedReflectiveTm stage binders → StagedReflectiveTm stage binders → Prop
  equivalence : ∀ stage binders,
    Equivalence (@Rel stage binders)
  subst_closed : ∀ {stage source target}
    (substitution : NativeSub source target)
    {left right : StagedReflectiveTm stage source},
    Rel left right →
      Rel (nativeSubst substitution left) (nativeSubst substitution right)

/-- Finest conversion policy, used as the equality-neutral positive point. -/
def syntacticConversion : ConversionPolicy where
  Rel := (· = ·)
  equivalence := fun _ _ => ⟨Eq.refl, Eq.symm, Eq.trans⟩
  subst_closed := by
    intro stage source target substitution left right equal
    cases equal
    rfl

/-- Instantiate the newest variable by a stage-indexed argument family. -/
def subst0 (argument : TermFamily binders) : NativeSub (binders + 1) binders :=
  fun stage => Fin.cases (argument stage) (fun index => .var index)

/-- Binder instantiation at a selected stage. -/
def inst0 (argument : TermFamily binders)
    (body : StagedReflectiveTm stage (binders + 1)) : StagedReflectiveTm stage binders :=
  nativeSubst (subst0 argument) body

@[simp] theorem subst0_zero (argument : TermFamily binders) (stage : Nat) :
    subst0 argument stage 0 = argument stage :=
  rfl

@[simp] theorem subst0_succ (argument : TermFamily binders) (stage : Nat)
    (index : Fin binders) :
    subst0 argument stage index.succ = .var index :=
  rfl

@[simp] theorem subst0_rename_wk (argument : TermFamily binders)
    (term : StagedReflectiveTm stage binders) :
    nativeSubst (subst0 argument) (nativeRename nativeWk term) = term := by
  rw [nativeSubst_rename]
  calc
    nativeSubst
        (fun current index => subst0 argument current (nativeWk index)) term =
        nativeSubst nativeIds term := by
      apply nativeSubst_ext
      intro current index
      rfl
    _ = term := nativeSubst_ids term

/-- Instantiation commutes with native simultaneous substitution. -/
theorem subst_inst0 (substitution : NativeSub source target)
    (argument : TermFamily source)
    (body : StagedReflectiveTm stage (source + 1)) :
    nativeSubst substitution (inst0 argument body) =
      inst0 (fun current => nativeSubst substitution (argument current))
        (nativeSubst (nativeLiftSub substitution) body) := by
  rw [inst0, inst0, nativeSubst_comp]
  rw [nativeSubst_comp]
  apply nativeSubst_ext
  intro current index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    change substitution current previous =
      nativeSubst
        (subst0 (fun current => nativeSubst substitution (argument current)))
        (nativeRename nativeWk (substitution current previous))
    exact (subst0_rename_wk _ _).symm

/-- Instantiation commutes with native renaming. -/
theorem rename_inst0 (rho : NativeRen source target)
    (argument : TermFamily source)
    (body : StagedReflectiveTm stage (source + 1)) :
    nativeRename rho (inst0 argument body) =
      inst0 (fun current => nativeRename rho (argument current))
        (nativeRename (nativeLiftRen rho) body) := by
  calc
    nativeRename rho (inst0 argument body) =
        nativeSubst (nativeSubOfRen rho) (inst0 argument body) :=
      (nativeSubst_ofRen rho (inst0 argument body)).symm
    _ = inst0
          (fun current =>
            nativeSubst (nativeSubOfRen rho) (argument current))
          (nativeSubst (nativeLiftSub (nativeSubOfRen rho)) body) :=
      subst_inst0 (nativeSubOfRen rho) argument body
    _ = inst0 (fun current => nativeRename rho (argument current))
          (nativeRename (nativeLiftRen rho) body) := by
      congr 1
      · funext current
        exact nativeSubst_ofRen rho (argument current)
      · rw [nativeLiftSubOfRen]
        exact nativeSubst_ofRen (nativeLiftRen rho) body

/-- Renaming compatibility of stage-indexed contexts. -/
def ContextRen (source : Context sourceBinders)
    (target : Context targetBinders)
    (rho : NativeRen sourceBinders targetBinders) : Prop :=
  ∀ stage index,
    Context.lookup target stage (rho index) =
      nativeRename rho (Context.lookup source stage index)

/-- Context renaming lifts through one dependent binder. -/
theorem ContextRen.snoc
    {source : Context sourceBinders} {target : Context targetBinders}
    {rho : NativeRen sourceBinders targetBinders}
    (compatible : ContextRen source target rho)
    (type : TermFamily sourceBinders) :
    ContextRen (.snoc source type)
      (.snoc target (fun stage => nativeRename rho (type stage)))
      (nativeLiftRen rho) := by
  intro stage index
  refine Fin.cases ?_ ?_ index
  · calc
      Context.lookup
          (.snoc target (fun current => nativeRename rho (type current)))
          stage (nativeLiftRen rho 0) =
          nativeRename nativeWk (nativeRename rho (type stage)) := by
        rfl
      _ = nativeRename (fun index => nativeWk (rho index)) (type stage) := by
        exact nativeRename_comp nativeWk rho (type stage)
      _ = nativeRename (fun index => nativeLiftRen rho (nativeWk index))
          (type stage) := by
        apply nativeRename_ext
        intro index
        rfl
      _ = nativeRename (nativeLiftRen rho)
          (nativeRename nativeWk (type stage)) := by
        exact (nativeRename_comp (nativeLiftRen rho) nativeWk
          (type stage)).symm
      _ = nativeRename (nativeLiftRen rho)
          (Context.lookup (.snoc source type) stage 0) := by
        rfl
  · intro previous
    calc
      Context.lookup
          (.snoc target (fun current => nativeRename rho (type current)))
          stage (nativeLiftRen rho previous.succ) =
          nativeRename nativeWk
            (Context.lookup target stage (rho previous)) := by
        rfl
      _ = nativeRename nativeWk
          (nativeRename rho (Context.lookup source stage previous)) := by
        rw [compatible stage previous]
      _ = nativeRename (fun index => nativeWk (rho index))
          (Context.lookup source stage previous) := by
        exact nativeRename_comp nativeWk rho _
      _ = nativeRename (fun index => nativeLiftRen rho (nativeWk index))
          (Context.lookup source stage previous) := by
        apply nativeRename_ext
        intro index
        rfl
      _ = nativeRename (nativeLiftRen rho)
          (nativeRename nativeWk
            (Context.lookup source stage previous)) := by
        exact (nativeRename_comp (nativeLiftRen rho) nativeWk _).symm
      _ = nativeRename (nativeLiftRen rho)
          (Context.lookup (.snoc source type) stage previous.succ) := by
        rfl

/-- Compatible renamings pass through the same explicit context lock. -/
theorem ContextRen.lock
    {source : Context sourceBinders} {target : Context targetBinders}
    {rho : NativeRen sourceBinders targetBinders}
    (compatible : ContextRen source target rho)
    (route : StageHom high low) :
    ContextRen (.lock route source) (.lock route target) rho := by
  intro stage index
  exact compatible stage index

/-- Authored native hypothetical typing.  The DTT fragment mirrors intrinsic
Pure, while `quote_intro` is a genuine modal rule and collections, Patterns,
and validated languages are native values. -/
inductive HasType (conversion : ConversionPolicy) :
    Context binders → StagedReflectiveTm stage binders →
      StagedReflectiveTm stage binders → Prop where
  | u0_type (context : Context binders) :
      HasType conversion context .u0 .u1
  | var {context : Context binders} (index : Fin binders) :
      HasType conversion context (.var index)
        (Context.lookup context stage index)
  | pi_form {context : Context binders} {domain : TermFamily binders}
      {body : StagedReflectiveTm stage (binders + 1)} :
      HasType conversion context (domain stage) .u1 →
      HasType conversion (.snoc context domain) body .u1 →
      HasType conversion context (.pi (domain stage) body) .u1
  | sigma_form {context : Context binders} {domain : TermFamily binders}
      {body : StagedReflectiveTm stage (binders + 1)} :
      HasType conversion context (domain stage) .u1 →
      HasType conversion (.snoc context domain) body .u1 →
      HasType conversion context (.sigma (domain stage) body) .u1
  | lam_intro {context : Context binders} {domain : TermFamily binders}
      {body bodyType : StagedReflectiveTm stage (binders + 1)} :
      HasType conversion (.snoc context domain) body bodyType →
      HasType conversion context (.lam body) (.pi (domain stage) bodyType)
  | app_elim {context : Context binders} {function : StagedReflectiveTm stage binders}
      {argument : TermFamily binders} {domain : TermFamily binders}
      {bodyType : StagedReflectiveTm stage (binders + 1)} :
      HasType conversion context function (.pi (domain stage) bodyType) →
      (∀ current, HasType conversion context (argument current)
        (domain current)) →
      HasType conversion context (.app function (argument stage))
        (inst0 argument bodyType)
  | pair_intro {context : Context binders} {left right : TermFamily binders}
      {domain : TermFamily binders}
      {bodyType : StagedReflectiveTm stage (binders + 1)} :
      HasType conversion context (left stage) (domain stage) →
      HasType conversion context (right stage) (inst0 left bodyType) →
      HasType conversion context (.pair (left stage) (right stage))
        (.sigma (domain stage) bodyType)
  | fst_elim {context : Context binders} {pair : TermFamily binders}
      {domain : TermFamily binders}
      {bodyType : StagedReflectiveTm stage (binders + 1)} :
      HasType conversion context (pair stage)
        (.sigma (domain stage) bodyType) →
      HasType conversion context (.fst (pair stage)) (domain stage)
  | snd_elim {context : Context binders} {pair : TermFamily binders}
      {domain : TermFamily binders}
      {bodyType : StagedReflectiveTm stage (binders + 1)} :
      HasType conversion context (pair stage)
        (.sigma (domain stage) bodyType) →
      HasType conversion context (.snd (pair stage))
        (inst0 (fun current => .fst (pair current)) bodyType)
  | id_form {context : Context binders} {type left right : StagedReflectiveTm stage binders} :
      HasType conversion context type .u1 →
      HasType conversion context left type →
      HasType conversion context right type →
      HasType conversion context (.id type left right) .u1
  | refl_intro {context : Context binders} {term type : StagedReflectiveTm stage binders} :
      HasType conversion context term type →
      HasType conversion context (.refl term) (.id type term term)
  | let_intro {context : Context binders}
      {value valueType : TermFamily binders}
      {body bodyType : StagedReflectiveTm stage (binders + 1)} :
      (∀ current, HasType conversion context
        (value current) (valueType current)) →
      HasType conversion (.snoc context valueType) body bodyType →
      HasType conversion context (.letE (value stage) body)
        (inst0 value bodyType)
  | pattern_intro (context : Context binders) (value : Pattern) :
      HasType conversion context (.pattern value) .u0
  | language_intro (context : Context binders)
      (value : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef) :
      HasType conversion context (.language value) .u0
  | empty_intro {context : Context binders} {type : StagedReflectiveTm stage binders} :
      HasType conversion context type .u1 →
      HasType conversion context .empty type
  | superpose_intro {context : Context binders}
      {left right type : StagedReflectiveTm stage binders} :
      HasType conversion context left type →
      HasType conversion context right type →
      HasType conversion context (.superpose left right) type
  | quote_intro {context : Context binders} {high low : Nat}
      (route : StageHom high low)
      {term type : StagedReflectiveTm high binders} :
      HasType conversion (.lock route context) term type →
      HasType conversion context (.quote route term) (.quote route type)
  | conv {context : Context binders} {term left right : StagedReflectiveTm stage binders} :
      HasType conversion context term left →
      conversion.Rel left right →
      HasType conversion context term right

/-- Positive typed witness for primitive sharing: bind `u0`, return the bound
variable, and obtain `u1`.  The judgment does not use an inlining equation. -/
theorem primitiveLet_has_native_modal_type :
    HasType syntacticConversion .nil
      (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0) .u1 := by
  exact HasType.let_intro
    (value := nativeU0Family)
    (valueType := fun _ => .u1)
    (fun _ => HasType.u0_type .nil)
    (HasType.var 0)

/-- Typability does not collapse primitive sharing into its optional inline
form at raw syntactic equality. -/
theorem primitiveLet_typable_but_not_syntactically_inlined :
    Nonempty (HasType syntacticConversion .nil
      (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0) .u1) ∧
      (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0) ≠
        nativeInlineLet nativeU0Family (.var (0 : Fin 1)) :=
  ⟨⟨primitiveLet_has_native_modal_type⟩,
    nativeLet_is_primitive_before_inlining⟩

/-- Native hypothetical typing is stable under context-compatible renaming,
including beneath dependent binders and across quotation. -/
theorem typing_rename {conversion : ConversionPolicy}
    {context : Context source} {term type : StagedReflectiveTm stage source}
    (typing : HasType conversion context term type) :
    ∀ {target : Nat} {targetContext : Context target}
      (rho : NativeRen source target),
      ContextRen context targetContext rho →
      HasType conversion targetContext (nativeRename rho term)
        (nativeRename rho type) := by
  induction typing with
  | u0_type context =>
      intro target targetContext rho compatible
      exact .u0_type targetContext
  | var index =>
      intro target targetContext rho compatible
      simpa only [nativeRename, compatible _ index] using
        (HasType.var (conversion := conversion)
          (context := targetContext) (rho index))
  | @pi_form binders stage context domain body domainTyping bodyTyping
      domainIH bodyIH =>
      intro target targetContext rho compatible
      exact .pi_form
        (domainIH rho compatible)
        (bodyIH (nativeLiftRen rho) (ContextRen.snoc compatible domain))
  | @sigma_form binders stage context domain body domainTyping bodyTyping
      domainIH bodyIH =>
      intro target targetContext rho compatible
      exact .sigma_form
        (domainIH rho compatible)
        (bodyIH (nativeLiftRen rho) (ContextRen.snoc compatible domain))
  | @lam_intro binders stage context domain body bodyType bodyTyping bodyIH =>
      intro target targetContext rho compatible
      exact .lam_intro
        (bodyIH (nativeLiftRen rho) (ContextRen.snoc compatible domain))
  | @app_elim binders stage context function argument domain bodyType
      functionTyping argumentTyping functionIH argumentIH =>
      intro target targetContext rho compatible
      simpa only [nativeRename, rename_inst0] using
        (HasType.app_elim
          (functionIH rho compatible)
          (fun current => argumentIH current rho compatible))
  | @pair_intro binders stage context left right domain bodyType
      leftTyping rightTyping leftIH rightIH =>
      intro target targetContext rho compatible
      have renamedRight : HasType conversion targetContext
          (nativeRename rho (right stage))
          (inst0 (fun current => nativeRename rho (left current))
            (nativeRename (nativeLiftRen rho) bodyType)) := by
        simpa only [rename_inst0] using rightIH rho compatible
      exact HasType.pair_intro
        (left := fun current => nativeRename rho (left current))
        (right := fun current => nativeRename rho (right current))
        (domain := fun current => nativeRename rho (domain current))
        (bodyType := nativeRename (nativeLiftRen rho) bodyType)
        (leftIH rho compatible) renamedRight
  | @fst_elim binders stage context pair domain bodyType pairTyping pairIH =>
      intro target targetContext rho compatible
      have renamedPair : HasType conversion targetContext
          (nativeRename rho (pair stage))
          (.sigma (nativeRename rho (domain stage))
            (nativeRename (nativeLiftRen rho) bodyType)) := by
        simpa only [nativeRename] using pairIH rho compatible
      exact HasType.fst_elim
        (pair := fun current => nativeRename rho (pair current))
        (domain := fun current => nativeRename rho (domain current))
        (bodyType := nativeRename (nativeLiftRen rho) bodyType)
        renamedPair
  | @snd_elim binders stage context pair domain bodyType pairTyping pairIH =>
      intro target targetContext rho compatible
      have renamedPair : HasType conversion targetContext
          (nativeRename rho (pair stage))
          (.sigma (nativeRename rho (domain stage))
            (nativeRename (nativeLiftRen rho) bodyType)) := by
        simpa only [nativeRename] using pairIH rho compatible
      simpa [nativeRename, rename_inst0] using
        (HasType.snd_elim
          (pair := fun current => nativeRename rho (pair current))
          (domain := fun current => nativeRename rho (domain current))
          (bodyType := nativeRename (nativeLiftRen rho) bodyType)
          renamedPair)
  | @id_form binders stage context type left right typeTyping leftTyping
      rightTyping typeIH leftIH rightIH =>
      intro target targetContext rho compatible
      exact .id_form (typeIH rho compatible) (leftIH rho compatible)
        (rightIH rho compatible)
  | @refl_intro binders stage context term type termTyping termIH =>
      intro target targetContext rho compatible
      exact .refl_intro (termIH rho compatible)
  | @let_intro binders stage context value valueType body bodyType
      valueTyping bodyTyping valueIH bodyIH =>
      intro target targetContext rho compatible
      simpa only [nativeRename, rename_inst0] using
        (HasType.let_intro
          (value := fun current => nativeRename rho (value current))
          (valueType := fun current => nativeRename rho (valueType current))
          (body := nativeRename (nativeLiftRen rho) body)
          (bodyType := nativeRename (nativeLiftRen rho) bodyType)
          (fun current => valueIH current rho compatible)
          (bodyIH (nativeLiftRen rho)
            (ContextRen.snoc compatible valueType)))
  | pattern_intro context value =>
      intro target targetContext rho compatible
      exact .pattern_intro targetContext value
  | language_intro context value =>
      intro target targetContext rho compatible
      exact .language_intro targetContext value
  | @empty_intro binders stage context type typeTyping typeIH =>
      intro target targetContext rho compatible
      exact .empty_intro (typeIH rho compatible)
  | @superpose_intro binders stage context left right type leftTyping
      rightTyping leftIH rightIH =>
      intro target targetContext rho compatible
      exact .superpose_intro (leftIH rho compatible) (rightIH rho compatible)
  | @quote_intro binders high low context route term type termTyping termIH =>
      intro target targetContext rho compatible
      exact .quote_intro route
        (termIH rho (ContextRen.lock compatible route))
  | @conv binders stage context term left right termTyping related termIH =>
      intro target targetContext rho compatible
      apply HasType.conv (termIH rho compatible)
      have renamed := conversion.subst_closed (nativeSubOfRen rho) related
      simpa only [nativeSubst_ofRen] using renamed

/-- Weakening by one native dependent binder. -/
theorem weakening {conversion : ConversionPolicy}
    {context : Context binders} {term type : StagedReflectiveTm stage binders}
    (typing : HasType conversion context term type)
    (extension : TermFamily binders) :
    HasType conversion (.snoc context extension)
      (nativeRename nativeWk term) (nativeRename nativeWk type) := by
  apply typing_rename typing nativeWk
  intro current index
  rfl

/-- A native typed context morphism is a stage-indexed substitution whose
every variable image has the substituted source type. -/
def ContextMor (conversion : ConversionPolicy)
    (source : Context sourceBinders) (target : Context targetBinders)
    (substitution : NativeSub sourceBinders targetBinders) : Prop :=
  ∀ stage index,
    HasType conversion target (substitution stage index)
      (nativeSubst substitution (Context.lookup source stage index))

/-- Typed substitutions lift through one dependent binder. -/
theorem ContextMor.lift {conversion : ConversionPolicy}
    {source : Context sourceBinders} {target : Context targetBinders}
    {substitution : NativeSub sourceBinders targetBinders}
    (typed : ContextMor conversion source target substitution)
    (extension : TermFamily sourceBinders) :
    ContextMor conversion (.snoc source extension)
      (.snoc target
        (fun stage => nativeSubst substitution (extension stage)))
      (nativeLiftSub substitution) := by
  intro stage index
  refine Fin.cases ?_ ?_ index
  · change HasType conversion
      (.snoc target
        (fun current => nativeSubst substitution (extension current)))
      (.var 0)
      (nativeSubst (nativeLiftSub substitution)
        (nativeRename nativeWk (extension stage)))
    rw [nativeSubst_liftSub_wk]
    exact HasType.var 0
  · intro previous
    have weakened := weakening (typed stage previous)
      (fun current => nativeSubst substitution (extension current))
    change HasType conversion
      (.snoc target
        (fun current => nativeSubst substitution (extension current)))
      (nativeRename nativeWk (substitution stage previous))
      (nativeSubst (nativeLiftSub substitution)
        (nativeRename nativeWk (Context.lookup source stage previous)))
    rw [nativeSubst_liftSub_wk]
    exact weakened

/-- Typed substitutions pass through the same explicit context lock. -/
theorem ContextMor.lock {conversion : ConversionPolicy}
    {source : Context sourceBinders} {target : Context targetBinders}
    {substitution : NativeSub sourceBinders targetBinders}
    (typed : ContextMor conversion source target substitution)
    (route : StageHom high low) :
    ContextMor conversion (.lock route source) (.lock route target)
      substitution := by
  intro stage index
  have locked := typing_rename (typed stage index)
    (targetContext := .lock route target) nativeIdRen (by
      intro current targetIndex
      change target.lookup current targetIndex =
        nativeRename nativeIdRen (target.lookup current targetIndex)
      exact (nativeRename_id _).symm)
  simpa only [nativeRename_id, Context.lookup_lock] using locked

/-- Generic simultaneous substitution theorem for the authored modal
hypothetical judgment.  Quotation uses the source-stage component already
present in `NativeSub`; no stage cast or reconstructed trace is required. -/
theorem typing_subst {conversion : ConversionPolicy}
    {context : Context source} {term type : StagedReflectiveTm stage source}
    (typing : HasType conversion context term type) :
    ∀ {target : Nat} {targetContext : Context target}
      (substitution : NativeSub source target),
      ContextMor conversion context targetContext substitution →
      HasType conversion targetContext (nativeSubst substitution term)
        (nativeSubst substitution type) := by
  induction typing with
  | u0_type context =>
      intro target targetContext substitution typed
      exact .u0_type targetContext
  | var index =>
      intro target targetContext substitution typed
      exact typed _ index
  | @pi_form binders stage context domain body domainTyping bodyTyping
      domainIH bodyIH =>
      intro target targetContext substitution typed
      exact .pi_form
        (domainIH substitution typed)
        (bodyIH (nativeLiftSub substitution)
          (ContextMor.lift typed domain))
  | @sigma_form binders stage context domain body domainTyping bodyTyping
      domainIH bodyIH =>
      intro target targetContext substitution typed
      exact .sigma_form
        (domainIH substitution typed)
        (bodyIH (nativeLiftSub substitution)
          (ContextMor.lift typed domain))
  | @lam_intro binders stage context domain body bodyType bodyTyping bodyIH =>
      intro target targetContext substitution typed
      exact .lam_intro
        (bodyIH (nativeLiftSub substitution)
          (ContextMor.lift typed domain))
  | @app_elim binders stage context function argument domain bodyType
      functionTyping argumentTyping functionIH argumentIH =>
      intro target targetContext substitution typed
      simpa [nativeSubst, subst_inst0] using
        (HasType.app_elim
          (functionIH substitution typed)
          (fun current => argumentIH current substitution typed))
  | @pair_intro binders stage context left right domain bodyType
      leftTyping rightTyping leftIH rightIH =>
      intro target targetContext substitution typed
      have substitutedRight : HasType conversion targetContext
          (nativeSubst substitution (right stage))
          (inst0 (fun current => nativeSubst substitution (left current))
            (nativeSubst (nativeLiftSub substitution) bodyType)) := by
        simpa only [subst_inst0] using rightIH substitution typed
      exact HasType.pair_intro
        (left := fun current => nativeSubst substitution (left current))
        (right := fun current => nativeSubst substitution (right current))
        (domain := fun current => nativeSubst substitution (domain current))
        (bodyType := nativeSubst (nativeLiftSub substitution) bodyType)
        (leftIH substitution typed) substitutedRight
  | @fst_elim binders stage context pair domain bodyType pairTyping pairIH =>
      intro target targetContext substitution typed
      have substitutedPair : HasType conversion targetContext
          (nativeSubst substitution (pair stage))
          (.sigma (nativeSubst substitution (domain stage))
            (nativeSubst (nativeLiftSub substitution) bodyType)) := by
        simpa only [nativeSubst] using pairIH substitution typed
      exact HasType.fst_elim
        (pair := fun current => nativeSubst substitution (pair current))
        (domain := fun current => nativeSubst substitution (domain current))
        (bodyType := nativeSubst (nativeLiftSub substitution) bodyType)
        substitutedPair
  | @snd_elim binders stage context pair domain bodyType pairTyping pairIH =>
      intro target targetContext substitution typed
      have substitutedPair : HasType conversion targetContext
          (nativeSubst substitution (pair stage))
          (.sigma (nativeSubst substitution (domain stage))
            (nativeSubst (nativeLiftSub substitution) bodyType)) := by
        simpa only [nativeSubst] using pairIH substitution typed
      simpa [nativeSubst, subst_inst0] using
        (HasType.snd_elim
          (pair := fun current => nativeSubst substitution (pair current))
          (domain := fun current => nativeSubst substitution (domain current))
          (bodyType := nativeSubst (nativeLiftSub substitution) bodyType)
          substitutedPair)
  | @id_form binders stage context type left right typeTyping leftTyping
      rightTyping typeIH leftIH rightIH =>
      intro target targetContext substitution typed
      exact .id_form (typeIH substitution typed) (leftIH substitution typed)
        (rightIH substitution typed)
  | @refl_intro binders stage context term type termTyping termIH =>
      intro target targetContext substitution typed
      exact .refl_intro (termIH substitution typed)
  | @let_intro binders stage context value valueType body bodyType
      valueTyping bodyTyping valueIH bodyIH =>
      intro target targetContext substitution typed
      simpa only [nativeSubst, subst_inst0] using
        (HasType.let_intro
          (value := fun current => nativeSubst substitution (value current))
          (valueType := fun current =>
            nativeSubst substitution (valueType current))
          (body := nativeSubst (nativeLiftSub substitution) body)
          (bodyType := nativeSubst (nativeLiftSub substitution) bodyType)
          (fun current => valueIH current substitution typed)
          (bodyIH (nativeLiftSub substitution)
            (ContextMor.lift typed valueType)))
  | pattern_intro context value =>
      intro target targetContext substitution typed
      exact .pattern_intro targetContext value
  | language_intro context value =>
      intro target targetContext substitution typed
      exact .language_intro targetContext value
  | @empty_intro binders stage context type typeTyping typeIH =>
      intro target targetContext substitution typed
      exact .empty_intro (typeIH substitution typed)
  | @superpose_intro binders stage context left right type leftTyping
      rightTyping leftIH rightIH =>
      intro target targetContext substitution typed
      exact .superpose_intro (leftIH substitution typed)
        (rightIH substitution typed)
  | @quote_intro binders high low context route term type termTyping termIH =>
      intro target targetContext substitution typed
      exact .quote_intro route
        (termIH substitution (ContextMor.lock typed route))
  | @conv binders stage context term left right termTyping related termIH =>
      intro target targetContext substitution typed
      exact .conv (termIH substitution typed)
        (conversion.subst_closed substitution related)

/-- Identity is a typed modal context substitution. -/
theorem ContextMor.ids (conversion : ConversionPolicy)
    (context : Context binders) :
    ContextMor conversion context context nativeIds := by
  intro stage index
  change HasType conversion context (.var index)
    (nativeSubst nativeIds (context.lookup stage index))
  rw [nativeSubst_ids]
  exact HasType.var index

/-- Typed modal context substitutions compose. -/
theorem ContextMor.comp {conversion : ConversionPolicy}
    {firstContext : Context first} {middleContext : Context middle}
    {lastContext : Context last}
    {earlier : NativeSub first middle} {later : NativeSub middle last}
    (earlierTyped : ContextMor conversion firstContext middleContext earlier)
    (laterTyped : ContextMor conversion middleContext lastContext later) :
    ContextMor conversion firstContext lastContext
      (nativeSubComp later earlier) := by
  intro stage index
  have substituted := typing_subst (earlierTyped stage index)
    later laterTyped
  simpa only [nativeSubComp, nativeSubst_comp] using substituted

/-- One native modal context at a selected conversion policy. -/
structure ContextObject (conversion : ConversionPolicy) where
  arity : Nat
  context : Context arity

/-- Morphisms retain the stage-indexed substitution and its typing proof. -/
structure TypedSub (conversion : ConversionPolicy)
    (source target : ContextObject conversion) where
  map : NativeSub source.arity target.arity
  typed : ContextMor conversion source.context target.context map

namespace TypedSub

@[ext] theorem ext {conversion : ConversionPolicy}
    {source target : ContextObject conversion}
    {left right : TypedSub conversion source target}
    (mapsEqual : left.map = right.map) : left = right := by
  cases left
  cases right
  cases mapsEqual
  rfl

end TypedSub

/-- Native modal contexts and their genuinely typed substitutions form a
category for every substitution-stable conversion policy. -/
instance (conversion : ConversionPolicy) :
    CategoryTheory.Category (ContextObject conversion) where
  Hom := TypedSub conversion
  id object := ⟨nativeIds, ContextMor.ids conversion object.context⟩
  comp earlier later :=
    ⟨nativeSubComp later.map earlier.map,
      ContextMor.comp earlier.typed later.typed⟩
  id_comp morphism := by
    apply TypedSub.ext
    exact nativeSubComp_right_id morphism.map
  comp_id morphism := by
    apply TypedSub.ext
    exact nativeSubComp_left_id morphism.map
  assoc first second third := by
    apply TypedSub.ext
    exact nativeSubComp_assoc third.map second.map first.map

/-- Forget typing while retaining the exact staged substitution. -/
def toNativeSupport (conversion : ConversionPolicy) :
    CategoryTheory.Functor (ContextObject conversion) NativeSupport where
  obj object := ⟨object.arity⟩
  map substitution := substitution.map
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The modal contextual refinement is faithful: it forgets typing proofs but
never identifies distinct staged substitutions. -/
theorem toNativeSupport_map_injective (conversion : ConversionPolicy)
    {source target : ContextObject conversion} :
    Function.Injective
      (fun substitution : TypedSub conversion source target =>
        (toNativeSupport conversion).map substitution) := by
  intro left right equal
  exact TypedSub.ext equal

/-! #### Intrinsic Pure is a guest fragment, not the modal judgment itself

The embedding below is conditional only at conversion: a native policy must
contain every conversion used by intrinsic Pure.  The raw constructors,
contexts, dependent binders, and typing rules then map structurally.  Keeping
this premise explicit prevents the Pure conversion closure from being silently
declared to be the native kernel equality. -/

/-- Embed a live intrinsic Pure telescope as a stage-uniform native modal
telescope. -/
def embedPureContext :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context.Ctx binders →
      Context binders
  | .nil => .nil
  | .snoc context type =>
      .snoc (embedPureContext context) (fun stage => embedPure stage type)

/-- Lookup in the embedded telescope is exactly embedded intrinsic lookup. -/
theorem lookup_embedPureContext
    (context : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context.Ctx binders)
    (stage : Nat) (index : Fin binders) :
    (embedPureContext context).lookup stage index =
      embedPure stage
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context.lookup context index) := by
  induction context with
  | nil => exact Fin.elim0 index
  | @snoc binders context type contextIH =>
      refine Fin.cases ?_ ?_ index
      · change nativeRename nativeWk (embedPure stage type) =
          embedPure stage
            (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename
              Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.wk type)
        exact nativeRename_embedPure nativeWk stage type
      · intro previous
        change nativeRename nativeWk
            ((embedPureContext context).lookup stage previous) =
          embedPure stage
            (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename
              Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.wk
              (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context.lookup
                context previous))
        rw [contextIH previous]
        exact nativeRename_embedPure nativeWk stage _

/-- Native newest-variable substitution of stage-uniform Pure syntax is the
stagewise embedding of intrinsic Pure's newest-variable substitution. -/
theorem subst0_embedPure (argument : PureTm binders) :
    subst0 (fun stage => embedPure stage argument) =
      embedPureSub
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst0 argument) := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

/-- Binder instantiation commutes with the Pure-to-native embedding. -/
@[simp] theorem inst0_embedPure (argument : PureTm binders)
    (body : PureTm (binders + 1)) (stage : Nat) :
    inst0 (fun current => embedPure current argument) (embedPure stage body) =
      embedPure stage
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.inst0
          argument body) := by
  unfold inst0
  rw [subst0_embedPure]
  exact nativeSubst_embedPure
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst0 argument)
    stage body

/-- The dependent second projection uses the embedded first projection as
its newest-variable argument. -/
@[simp] theorem inst0_fst_embedPure (pair : PureTm binders)
    (body : PureTm (binders + 1)) (stage : Nat) :
    inst0 (fun current => .fst (embedPure current pair))
        (embedPure stage body) =
      embedPure stage
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.inst0
          (.fst pair) body) := by
  change inst0 (fun current => embedPure current (.fst pair))
      (embedPure stage body) = _
  exact inst0_embedPure (.fst pair) body stage

/-- The exact additional premise needed to host intrinsic Pure typing at one
native conversion policy.  It is inclusion, not identification, of the two
conversion relations. -/
def ExtendsIntrinsicPure (conversion : ConversionPolicy) : Prop :=
  ∀ {stage binders : Nat} {left right : PureTm binders},
    IntrinsicPureConv left right →
      conversion.Rel (embedPure stage left) (embedPure stage right)

/-- Every intrinsic Pure typing derivation maps to the authored native modal
judgment when the selected native conversion contains Pure conversion.  The
result is quantified over stages, which supplies the coherent term families
needed by dependent elimination under quotation. -/
theorem typing_embedPure {conversion : ConversionPolicy}
    (containsPure : ExtendsIntrinsicPure conversion)
    {context : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context.Ctx binders}
    {term type : PureTm binders}
    (typing :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType context term type) :
    ∀ stage,
      HasType conversion (embedPureContext context)
        (embedPure stage term) (embedPure stage type) := by
  induction typing with
  | u0_type context =>
      intro stage
      exact .u0_type (embedPureContext context)
  | @var binders context index =>
      intro stage
      simpa only [embedPure, lookup_embedPureContext] using
        (HasType.var (conversion := conversion)
          (context := embedPureContext context) index)
  | @pi_form binders context domain body domainTyping bodyTyping
      domainIH bodyIH =>
      intro stage
      exact .pi_form (domainIH stage) (bodyIH stage)
  | @sigma_form binders context domain body domainTyping bodyTyping
      domainIH bodyIH =>
      intro stage
      exact .sigma_form (domainIH stage) (bodyIH stage)
  | @lam_intro binders context domain body bodyType bodyTyping bodyIH =>
      intro stage
      exact .lam_intro (bodyIH stage)
  | @app_elim binders context function argument domain bodyType
      functionTyping argumentTyping functionIH argumentIH =>
      intro stage
      simpa only [embedPure, inst0_embedPure] using
        (HasType.app_elim
          (functionIH stage)
          (fun current => argumentIH current))
  | @pair_intro binders context left right domain bodyType
      leftTyping rightTyping leftIH rightIH =>
      intro stage
      have embeddedRight := rightIH stage
      rw [← inst0_embedPure left bodyType stage] at embeddedRight
      simpa only [embedPure] using
        (HasType.pair_intro
          (left := fun current => embedPure current left)
          (right := fun current => embedPure current right)
          (domain := fun current => embedPure current domain)
          (bodyType := embedPure stage bodyType)
          (leftIH stage) embeddedRight)
  | @fst_elim binders context pair domain bodyType pairTyping pairIH =>
      intro stage
      simpa only [embedPure] using
        (HasType.fst_elim
          (pair := fun current => embedPure current pair)
          (domain := fun current => embedPure current domain)
          (bodyType := embedPure stage bodyType)
          (pairIH stage))
  | @snd_elim binders context pair domain bodyType pairTyping pairIH =>
      intro stage
      simpa only [embedPure, inst0_fst_embedPure] using
        (HasType.snd_elim
          (pair := fun current => embedPure current pair)
          (domain := fun current => embedPure current domain)
          (bodyType := embedPure stage bodyType)
          (pairIH stage))
  | @id_form binders context type left right typeTyping leftTyping
      rightTyping typeIH leftIH rightIH =>
      intro stage
      exact .id_form (typeIH stage) (leftIH stage) (rightIH stage)
  | @refl_intro binders context term type termTyping termIH =>
      intro stage
      exact .refl_intro (termIH stage)
  | @conv binders context term left right termTyping related termIH =>
      intro stage
      exact .conv (termIH stage) (containsPure related)

/-- Syntactic native conversion cannot host intrinsic Pure's beta rule.  This
is the negative witness showing why conversion inclusion is a real premise. -/
theorem syntacticConversion_does_not_extend_intrinsicPure :
    ¬ ExtendsIntrinsicPure syntacticConversion := by
  intro containsPure
  have related :=
    containsPure (stage := 0) intrinsicPureConversionProfile_beta
  change embedPure 0
      (PureTm.app (PureTm.lam (PureTm.var (0 : Fin 1))) PureTm.u0) =
    embedPure 0 (PureTm.u0 : PureTm 0) at related
  have impossible := embedPure_injective 0 related
  cases impossible

/-- Native quotation receives an authored modal typing that the intrinsic
Pure refinement cannot express. -/
theorem quotedPureUniverse_has_native_modal_type :
    HasType syntacticConversion .nil quotedPureUniverse
      (.quote oneToZeroQuotation (.u1 : StagedReflectiveTm 1 0)) := by
  exact .quote_intro oneToZeroQuotation
    (.u0_type (.lock oneToZeroQuotation .nil))

/-- The positive modal typing and the intrinsic negative witness coexist: the
bridge relates the layers without identifying them. -/
theorem quotation_typing_separates_native_from_intrinsic :
    HasType syntacticConversion .nil quotedPureUniverse
        (.quote oneToZeroQuotation (.u1 : StagedReflectiveTm 1 0)) ∧
      ¬ ∃ type : StagedReflectiveTm 0 0,
        Nonempty
          (IntrinsicPureRefinement.TypingAt 0 .nil quotedPureUniverse type) :=
  ⟨quotedPureUniverse_has_native_modal_type,
    IntrinsicPureRefinement.quotedPureUniverse_has_no_intrinsic_typing⟩

/-! #### Equality-profile extension, after core initiality

The intensional presentation is formed once.  A stronger conversion policy
extends its derivations by inclusion of conversion evidence; it does not
change the raw syntax or require another initiality theorem. -/

/-- Inclusion of conversion relations, pointwise at every stage and
support. -/
def ConversionPolicy.Extends (larger smaller : ConversionPolicy) : Prop :=
  ∀ {stage binders} {left right : StagedReflectiveTm stage binders},
    smaller.Rel left right → larger.Rel left right

/-- Conversion-policy inclusion is reflexive. -/
theorem ConversionPolicy.extends_refl (conversion : ConversionPolicy) :
    conversion.Extends conversion := by
  intro stage binders left right related
  exact related

/-- Conversion-policy inclusion composes. -/
theorem ConversionPolicy.extends_trans
    {largest middle smallest : ConversionPolicy}
    (later : largest.Extends middle)
    (earlier : middle.Extends smallest) :
    largest.Extends smallest := by
  intro stage binders left right related
  exact later (earlier related)

/-- Every conversion policy contains syntactic equality. -/
theorem ConversionPolicy.extends_syntactic (conversion : ConversionPolicy) :
    conversion.Extends syntacticConversion := by
  intro stage binders left right equal
  cases equal
  exact (conversion.equivalence stage binders).refl left

/-- Typing is monotone under conversion-policy extension.  This is the
factorization seam for observational, quotient, or cubical profiles after the
single intensional initiality theorem. -/
theorem HasType.of_conversion_extension
    {smaller larger : ConversionPolicy}
    (includes : larger.Extends smaller)
    {context : Context binders} {term type : StagedReflectiveTm stage binders}
    (typing : HasType smaller context term type) :
    HasType larger context term type := by
  induction typing with
  | u0_type context => exact .u0_type context
  | var index => exact .var index
  | pi_form domainTyping bodyTyping domainIH bodyIH =>
      exact .pi_form domainIH bodyIH
  | sigma_form domainTyping bodyTyping domainIH bodyIH =>
      exact .sigma_form domainIH bodyIH
  | lam_intro bodyTyping bodyIH => exact .lam_intro bodyIH
  | app_elim functionTyping argumentTyping functionIH argumentIH =>
      exact .app_elim functionIH argumentIH
  | pair_intro leftTyping rightTyping leftIH rightIH =>
      exact .pair_intro leftIH rightIH
  | fst_elim pairTyping pairIH => exact .fst_elim pairIH
  | snd_elim pairTyping pairIH => exact .snd_elim pairIH
  | id_form typeTyping leftTyping rightTyping typeIH leftIH rightIH =>
      exact .id_form typeIH leftIH rightIH
  | refl_intro termTyping termIH => exact .refl_intro termIH
  | let_intro valueTyping bodyTyping valueIH bodyIH =>
      exact .let_intro valueIH bodyIH
  | pattern_intro context value => exact .pattern_intro context value
  | language_intro context value => exact .language_intro context value
  | empty_intro typeTyping typeIH => exact .empty_intro typeIH
  | superpose_intro leftTyping rightTyping leftIH rightIH =>
      exact .superpose_intro leftIH rightIH
  | quote_intro route termTyping termIH => exact .quote_intro route termIH
  | conv termTyping related termIH => exact .conv termIH (includes related)

/-- Every intensional typing derivation embeds into every later conversion
profile through the same raw term and context. -/
theorem HasType.of_syntactic
    (conversion : ConversionPolicy)
    {context : Context binders} {term type : StagedReflectiveTm stage binders}
    (typing : HasType syntacticConversion context term type) :
    HasType conversion context term type :=
  typing.of_conversion_extension conversion.extends_syntactic

end NativeModalTyping

/-! ### Typed initiality of the intensional native presentation

A bare `ModalCwF` does not determine interpretations of the native constants,
Pattern values, primitive sharing, validated-language values, or term-level
quotation.  In particular, `bare_modal_cwf_does_not_determine_quotation`
already gives two quotation structures over the same modal CwF.  The correct
target of an initiality theorem is therefore a *model of the authored
presentation*: a staged raw algebra, an algebra of locked telescope contexts,
and one local semantic operation for every typing rule.

The definitions below are a displayed presentation over the free raw syntax.
They do not assume a global interpretation theorem.  Instead,
`fold_typing` derives it by induction from the local rule operations, and
`initiality` proves that the resulting raw/context interpretation is the
unique structure-preserving one.  Conversion is fixed once, at the
intensional syntactic core; stronger equality profiles can subsequently be
handled by extension/factorization theorems without duplicating initiality. -/

namespace NativeTypedInitiality

open NativeModalTyping

/-- An algebra for the locked telescope constructors over one staged raw
algebra.  Context entries are interpreted stagewise, matching the native
support discipline used by quotation and simultaneous substitution. -/
structure ContextAlgebra (target : NativeRawAlgebra.{uRawTarget}) where
  Carrier : Nat → Type uRawTarget
  nil : Carrier 0
  snoc : {binders : Nat} → Carrier binders →
    ((stage : Nat) → (target.atStage stage).Carrier binders) →
      Carrier (binders + 1)
  lock : {high low binders : Nat} → StageHom high low →
    Carrier binders → Carrier binders

/-- Structural interpretation of native locked contexts. -/
def foldContext {target : NativeRawAlgebra.{uRawTarget}}
    (contexts : ContextAlgebra target) :
    {binders : Nat} → Context binders → contexts.Carrier binders
  | _, .nil => contexts.nil
  | _, .snoc context type =>
      contexts.snoc (foldContext contexts context)
        (fun stage => nativeRawFold target (type stage))
  | _, .lock route context =>
      contexts.lock route (foldContext contexts context)

/-- A local model of every rule of the authored intensional typing
presentation.  Every field is a rule operation; there is no field asserting
the desired global soundness theorem. -/
structure TypingAlgebra (target : NativeRawAlgebra.{uRawTarget})
    (contexts : ContextAlgebra target) where
  Judges : {stage binders : Nat} → contexts.Carrier binders →
    (target.atStage stage).Carrier binders →
    (target.atStage stage).Carrier binders → Prop
  u0_type : ∀ {stage binders} (context : Context binders),
    Judges (foldContext contexts context)
      (nativeRawFold target (.u0 : StagedReflectiveTm stage binders))
      (nativeRawFold target (.u1 : StagedReflectiveTm stage binders))
  var : ∀ {stage binders} (context : Context binders)
      (index : Fin binders),
    Judges (foldContext contexts context)
      (nativeRawFold target (.var index : StagedReflectiveTm stage binders))
      (nativeRawFold target (context.lookup stage index))
  pi_form : ∀ {stage binders} {context : Context binders}
      {domain : TermFamily binders}
      {body : StagedReflectiveTm stage (binders + 1)},
    Judges (foldContext contexts context)
      (nativeRawFold target (domain stage))
      (nativeRawFold target (.u1 : StagedReflectiveTm stage binders)) →
    Judges (foldContext contexts (.snoc context domain))
      (nativeRawFold target body)
      (nativeRawFold target (.u1 : StagedReflectiveTm stage (binders + 1))) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.pi (domain stage) body))
      (nativeRawFold target (.u1 : StagedReflectiveTm stage binders))
  sigma_form : ∀ {stage binders} {context : Context binders}
      {domain : TermFamily binders}
      {body : StagedReflectiveTm stage (binders + 1)},
    Judges (foldContext contexts context)
      (nativeRawFold target (domain stage))
      (nativeRawFold target (.u1 : StagedReflectiveTm stage binders)) →
    Judges (foldContext contexts (.snoc context domain))
      (nativeRawFold target body)
      (nativeRawFold target (.u1 : StagedReflectiveTm stage (binders + 1))) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.sigma (domain stage) body))
      (nativeRawFold target (.u1 : StagedReflectiveTm stage binders))
  lam_intro : ∀ {stage binders} {context : Context binders}
      {domain : TermFamily binders}
      {body bodyType : StagedReflectiveTm stage (binders + 1)},
    Judges (foldContext contexts (.snoc context domain))
      (nativeRawFold target body) (nativeRawFold target bodyType) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.lam body))
      (nativeRawFold target (.pi (domain stage) bodyType))
  app_elim : ∀ {stage binders} {context : Context binders}
      {function : StagedReflectiveTm stage binders}
      {argument domain : TermFamily binders}
      {bodyType : StagedReflectiveTm stage (binders + 1)},
    Judges (foldContext contexts context)
      (nativeRawFold target function)
      (nativeRawFold target (.pi (domain stage) bodyType)) →
    (∀ current, Judges (foldContext contexts context)
      (nativeRawFold target (argument current))
      (nativeRawFold target (domain current))) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.app function (argument stage)))
      (nativeRawFold target (inst0 argument bodyType))
  pair_intro : ∀ {stage binders} {context : Context binders}
      {left right domain : TermFamily binders}
      {bodyType : StagedReflectiveTm stage (binders + 1)},
    Judges (foldContext contexts context)
      (nativeRawFold target (left stage))
      (nativeRawFold target (domain stage)) →
    Judges (foldContext contexts context)
      (nativeRawFold target (right stage))
      (nativeRawFold target (inst0 left bodyType)) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.pair (left stage) (right stage)))
      (nativeRawFold target (.sigma (domain stage) bodyType))
  fst_elim : ∀ {stage binders} {context : Context binders}
      {pair domain : TermFamily binders}
      {bodyType : StagedReflectiveTm stage (binders + 1)},
    Judges (foldContext contexts context)
      (nativeRawFold target (pair stage))
      (nativeRawFold target (.sigma (domain stage) bodyType)) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.fst (pair stage)))
      (nativeRawFold target (domain stage))
  snd_elim : ∀ {stage binders} {context : Context binders}
      {pair domain : TermFamily binders}
      {bodyType : StagedReflectiveTm stage (binders + 1)},
    Judges (foldContext contexts context)
      (nativeRawFold target (pair stage))
      (nativeRawFold target (.sigma (domain stage) bodyType)) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.snd (pair stage)))
      (nativeRawFold target
        (inst0 (fun current => .fst (pair current)) bodyType))
  id_form : ∀ {stage binders} {context : Context binders}
      {type left right : StagedReflectiveTm stage binders},
    Judges (foldContext contexts context)
      (nativeRawFold target type)
      (nativeRawFold target (.u1 : StagedReflectiveTm stage binders)) →
    Judges (foldContext contexts context)
      (nativeRawFold target left) (nativeRawFold target type) →
    Judges (foldContext contexts context)
      (nativeRawFold target right) (nativeRawFold target type) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.id type left right))
      (nativeRawFold target (.u1 : StagedReflectiveTm stage binders))
  refl_intro : ∀ {stage binders} {context : Context binders}
      {term type : StagedReflectiveTm stage binders},
    Judges (foldContext contexts context)
      (nativeRawFold target term) (nativeRawFold target type) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.refl term))
      (nativeRawFold target (.id type term term))
  let_intro : ∀ {stage binders} {context : Context binders}
      {value valueType : TermFamily binders}
      {body bodyType : StagedReflectiveTm stage (binders + 1)},
    (∀ current, Judges (foldContext contexts context)
      (nativeRawFold target (value current))
      (nativeRawFold target (valueType current))) →
    Judges (foldContext contexts (.snoc context valueType))
      (nativeRawFold target body) (nativeRawFold target bodyType) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.letE (value stage) body))
      (nativeRawFold target (inst0 value bodyType))
  pattern_intro : ∀ {stage binders} (context : Context binders)
      (value : Pattern),
    Judges (foldContext contexts context)
      (nativeRawFold target (.pattern value : StagedReflectiveTm stage binders))
      (nativeRawFold target (.u0 : StagedReflectiveTm stage binders))
  language_intro : ∀ {stage binders} (context : Context binders)
      (value : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef),
    Judges (foldContext contexts context)
      (nativeRawFold target (.language value : StagedReflectiveTm stage binders))
      (nativeRawFold target (.u0 : StagedReflectiveTm stage binders))
  empty_intro : ∀ {stage binders} {context : Context binders}
      {type : StagedReflectiveTm stage binders},
    Judges (foldContext contexts context)
      (nativeRawFold target type)
      (nativeRawFold target (.u1 : StagedReflectiveTm stage binders)) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.empty : StagedReflectiveTm stage binders))
      (nativeRawFold target type)
  superpose_intro : ∀ {stage binders} {context : Context binders}
      {left right type : StagedReflectiveTm stage binders},
    Judges (foldContext contexts context)
      (nativeRawFold target left) (nativeRawFold target type) →
    Judges (foldContext contexts context)
      (nativeRawFold target right) (nativeRawFold target type) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.superpose left right))
      (nativeRawFold target type)
  quote_intro : ∀ {binders high low} {context : Context binders}
      (route : StageHom high low)
      {term type : StagedReflectiveTm high binders},
    Judges (foldContext contexts (.lock route context))
      (nativeRawFold target term) (nativeRawFold target type) →
    Judges (foldContext contexts context)
      (nativeRawFold target (.quote route term))
      (nativeRawFold target (.quote route type))
  conv : ∀ {stage binders} {context : Context binders}
      {term left right : StagedReflectiveTm stage binders},
    Judges (foldContext contexts context)
      (nativeRawFold target term) (nativeRawFold target left) →
    left = right →
    Judges (foldContext contexts context)
      (nativeRawFold target term) (nativeRawFold target right)

/-- A complete target model of the authored intensional typed presentation. -/
structure Model where
  raw : NativeRawAlgebra.{uRawTarget}
  contexts : ContextAlgebra raw
  typing : TypingAlgebra raw contexts

/-- Every authored typing derivation has a semantic image in every local
model of the presentation.  This is the existence half of typed initiality. -/
theorem fold_typing (model : Model.{uRawTarget})
    {binders stage} {context : Context binders}
    {term type : StagedReflectiveTm stage binders}
    (typing : HasType syntacticConversion context term type) :
    model.typing.Judges (foldContext model.contexts context)
      (nativeRawFold model.raw term) (nativeRawFold model.raw type) := by
  induction typing with
  | u0_type context => exact model.typing.u0_type context
  | var index => exact model.typing.var _ index
  | pi_form domainTyping bodyTyping domainIH bodyIH =>
      exact model.typing.pi_form domainIH bodyIH
  | sigma_form domainTyping bodyTyping domainIH bodyIH =>
      exact model.typing.sigma_form domainIH bodyIH
  | lam_intro bodyTyping bodyIH => exact model.typing.lam_intro bodyIH
  | app_elim functionTyping argumentTyping functionIH argumentIH =>
      exact model.typing.app_elim functionIH argumentIH
  | pair_intro leftTyping rightTyping leftIH rightIH =>
      exact model.typing.pair_intro leftIH rightIH
  | fst_elim pairTyping pairIH => exact model.typing.fst_elim pairIH
  | snd_elim pairTyping pairIH => exact model.typing.snd_elim pairIH
  | id_form typeTyping leftTyping rightTyping typeIH leftIH rightIH =>
      exact model.typing.id_form typeIH leftIH rightIH
  | refl_intro termTyping termIH => exact model.typing.refl_intro termIH
  | let_intro valueTyping bodyTyping valueIH bodyIH =>
      exact model.typing.let_intro valueIH bodyIH
  | pattern_intro context value => exact model.typing.pattern_intro context value
  | language_intro context value =>
      exact model.typing.language_intro context value
  | empty_intro typeTyping typeIH => exact model.typing.empty_intro typeIH
  | superpose_intro leftTyping rightTyping leftIH rightIH =>
      exact model.typing.superpose_intro leftIH rightIH
  | quote_intro route termTyping termIH =>
      exact model.typing.quote_intro route termIH
  | conv termTyping related termIH => exact model.typing.conv termIH related

/-- A structure-preserving interpretation of the free typed presentation.
The global typing map is retained as a proof field so uniqueness includes the
typed layer rather than only the raw term fold. -/
structure Interpretation (model : Model.{uRawTarget}) where
  raw : NativeRawHom nativeSyntaxAlgebra model.raw
  contextMap : {binders : Nat} → Context binders →
    model.contexts.Carrier binders
  map_nil : contextMap .nil = model.contexts.nil
  map_snoc : ∀ {binders} (context : Context binders)
      (type : TermFamily binders),
    contextMap (.snoc context type) =
      model.contexts.snoc (contextMap context)
        (fun stage => raw.map (type stage))
  map_lock : ∀ {high low binders} (route : StageHom high low)
      (context : Context binders),
    contextMap (.lock route context) =
      model.contexts.lock route (contextMap context)
  map_typing : ∀ {stage binders} {context : Context binders}
      {term type : StagedReflectiveTm stage binders},
    HasType syntacticConversion context term type →
      model.typing.Judges (contextMap context)
        (raw.map term) (raw.map type)

/-- The canonical typed fold into a presentation model. -/
def canonicalInterpretation (model : Model.{uRawTarget}) :
    Interpretation model where
  raw := nativeRawFoldHom model.raw
  contextMap := foldContext model.contexts
  map_nil := rfl
  map_snoc := by intros; rfl
  map_lock := by intros; rfl
  map_typing := fold_typing model

/-- Every structure-preserving context map is the structural context fold.
The proof uses raw initiality at each telescope entry. -/
theorem contextMap_unique (model : Model.{uRawTarget})
    (interpretation : Interpretation model) :
    ∀ {binders} (context : Context binders),
      interpretation.contextMap context =
        foldContext model.contexts context := by
  intro binders context
  induction context with
  | nil => exact interpretation.map_nil
  | @snoc binders context type contextIH =>
      rw [interpretation.map_snoc, contextIH]
      congr 1
      funext stage
      exact nativeRawFold_unique_pointwise model.raw interpretation.raw
        (type stage)
  | lock route context contextIH =>
      rw [interpretation.map_lock, contextIH]
      rfl

/-- Two interpretations agree on the complete raw and contextual data. -/
theorem interpretations_agree (model : Model.{uRawTarget})
    (left right : Interpretation model) :
    left.raw = right.raw ∧
      (∀ {binders} (context : Context binders),
        left.contextMap context = right.contextMap context) := by
  constructor
  · exact (nativeRawFold_unique model.raw left.raw).trans
      (nativeRawFold_unique model.raw right.raw).symm
  · intro binders context
    exact (contextMap_unique model left context).trans
      (contextMap_unique model right context).symm

/-- Full interpretation extensionality.  The typing component is
proof-irrelevant; raw and context maps contain all computational data. -/
@[ext] theorem Interpretation.ext (model : Model.{uRawTarget})
    (left right : Interpretation model)
    (rawEqual : left.raw = right.raw)
    (contextsEqual : ∀ {binders} (context : Context binders),
      left.contextMap context = right.contextMap context) :
    left = right := by
  cases left with
  | mk leftRaw leftContext leftNil leftSnoc leftLock leftTyping =>
    cases right with
    | mk rightRaw rightContext rightNil rightSnoc rightLock rightTyping =>
      change leftRaw = rightRaw at rawEqual
      cases rawEqual
      have contextFunctionsEqual :
          (@leftContext : (binders : Nat) → Context binders →
            model.contexts.Carrier binders) = @rightContext := by
        funext binders context
        exact contextsEqual context
      cases contextFunctionsEqual
      rfl

/-- Typed initiality, once, for the intensional core presentation: every
model has exactly one structure-preserving interpretation. -/
@[reducible] def initiality (model : Model.{uRawTarget}) :
    Unique (Interpretation model) where
  default := canonicalInterpretation model
  uniq interpretation := by
    apply Interpretation.ext model
    · exact nativeRawFold_unique model.raw interpretation.raw
    · intro binders context
      exact contextMap_unique model interpretation context

/-- The theorem form of the uniqueness half of typed initiality. -/
theorem interpretation_unique (model : Model.{uRawTarget})
    (interpretation : Interpretation model) :
    interpretation = canonicalInterpretation model :=
  (initiality model).uniq interpretation

/-- Positive nonvacuity witness: every target model validates the image of
the authored universe-formation judgment. -/
theorem universe_has_image (model : Model.{uRawTarget}) :
    model.typing.Judges (foldContext model.contexts (.nil : Context 0))
      (nativeRawFold model.raw (.u0 : StagedReflectiveTm 0 0))
      (nativeRawFold model.raw (.u1 : StagedReflectiveTm 0 0)) :=
  fold_typing model (HasType.u0_type .nil)

/-- Negative nonvacuity witness: no model of the full typed presentation can
interpret every judgment as false. -/
theorem no_empty_judgment_model (model : Model.{uRawTarget}) :
    ¬ (∀ {stage binders} (context : model.contexts.Carrier binders)
      (term type : (model.raw.atStage stage).Carrier binders),
      ¬ model.typing.Judges context term type) := by
  intro allEmpty
  exact allEmpty _ _ _ (universe_has_image model)

/-- The locked quotation theorem is preserved by the unique typed
interpretation; the source context remains explicitly locked in the rule
algebra used by `fold_typing`. -/
theorem quoted_universe_has_image (model : Model.{uRawTarget}) :
    model.typing.Judges (foldContext model.contexts (.nil : Context 0))
      (nativeRawFold model.raw quotedPureUniverse)
      (nativeRawFold model.raw
        (.quote oneToZeroQuotation (.u1 : StagedReflectiveTm 1 0))) :=
  fold_typing model quotedPureUniverse_has_native_modal_type

end NativeTypedInitiality

/-! ### Faithful raw contact with the live runtime Pattern interface

The native syntax does not validate itself by mapping back into another copy
of its own datatype.  This decoder targets the actual MeTTaIL `Pattern`
carrier used by the current Prime presentation.  It characterizes precisely
the direct runtime-Pattern image; quotation and other native constructors are
outside that image. -/

/-- Direct inclusion of a live runtime Pattern into native raw syntax. -/
def embedRuntimePattern (value : Pattern) : StagedReflectiveTm stage binders :=
  .pattern value

/-- Partial projection onto the direct live runtime-Pattern image. -/
def StagedReflectiveTm.runtimePattern? :
    StagedReflectiveTm stage binders → Option Pattern
  | .pattern value => some value
  | _ => none

@[simp] theorem runtimePattern?_embedRuntimePattern (value : Pattern) :
    (embedRuntimePattern (stage := stage) (binders := binders) value
      |>.runtimePattern?) = some value :=
  rfl

/-- The direct runtime inclusion is faithful. -/
theorem embedRuntimePattern_injective :
    Function.Injective
      (embedRuntimePattern (stage := stage) (binders := binders)) := by
  intro left right equal
  cases equal
  rfl

/-- Exact image characterization against the live runtime Pattern carrier. -/
theorem runtimePattern_image_iff (term : StagedReflectiveTm stage binders) :
    (∃ value : Pattern, embedRuntimePattern value = term) ↔
      ∃ value : Pattern, term.runtimePattern? = some value := by
  constructor
  · rintro ⟨value, rfl⟩
    exact ⟨value, rfl⟩
  · cases term <;>
      simp [StagedReflectiveTm.runtimePattern?, embedRuntimePattern]

/-- A concrete program from the current authored Prime interface: the left side
of its reflected-demand rewrite. -/
def currentPrimeReflectedDemandProgram : Pattern :=
  Mettapedia.Languages.MeTTa.Prime.LanguageDef.reflectedDemandRewrite.left

/-- Positive source-faithfulness witness: a real current Prime program
round-trips through the native raw inclusion. -/
theorem currentPrimeReflectedDemandProgram_roundtrip :
    (embedRuntimePattern currentPrimeReflectedDemandProgram :
      StagedReflectiveTm 0 0).runtimePattern? =
        some currentPrimeReflectedDemandProgram :=
  rfl

/-- Negative source-image witness: staged quotation is not silently decoded
as a runtime Pattern. -/
theorem quotedPureUniverse_not_runtimePattern_image :
    ¬ ∃ value : Pattern,
      (embedRuntimePattern value : StagedReflectiveTm 0 0) = quotedPureUniverse := by
  rintro ⟨value, equal⟩
  cases equal

/-! ### Cost and evidence remain a fibred decoration

Putting cost or evidence inside `StagedReflectiveTm` would make operational metadata
participate in kernel substitution and definitional equality.  Instead the
total decorated carrier projects to the unchanged raw term.  This is the raw
counterpart of `nativeEvidenceFibration`; it also leaves the certificate-free
typing face untouched. -/

/-- External cost/evidence decoration over one native kernel term. -/
structure NativeDecoratedTm (stage binders : Nat) where
  term : StagedReflectiveTm stage binders
  account : NativeCostAccount
  evidence : NativeEvidence

namespace NativeDecoratedTm

/-- The zero-decoration section of the forgetful projection. -/
def undecorated {stage binders : Nat} (term : StagedReflectiveTm stage binders) :
    NativeDecoratedTm stage binders :=
  ⟨term, nativeCostZero, ⟨0, 0⟩⟩

/-- Attach a cost account without changing the kernel term or its evidence. -/
def withCost {stage binders : Nat} (term : StagedReflectiveTm stage binders)
    (account : NativeCostAccount) : NativeDecoratedTm stage binders :=
  ⟨term, account, ⟨0, 0⟩⟩

/-- Attach PLN evidence without changing the kernel term or its cost. -/
def withEvidence {stage binders : Nat} (term : StagedReflectiveTm stage binders)
    (evidence : NativeEvidence) : NativeDecoratedTm stage binders :=
  ⟨term, nativeCostZero, evidence⟩

@[simp] theorem undecorated_term {stage binders : Nat}
    (term : StagedReflectiveTm stage binders) :
    (undecorated term).term = term := rfl

@[simp] theorem withCost_term {stage binders : Nat}
    (term : StagedReflectiveTm stage binders) (account : NativeCostAccount) :
    (withCost term account).term = term := rfl

@[simp] theorem withEvidence_term {stage binders : Nat}
    (term : StagedReflectiveTm stage binders) (evidence : NativeEvidence) :
    (withEvidence term evidence).term = term := rfl

/-- Reindex a decoration by simultaneous substitution while retaining cost and
evidence exactly. -/
def reindex (substitution : NativeSub source target)
    {stage : Nat} (decorated : NativeDecoratedTm stage source) :
    NativeDecoratedTm stage target :=
  ⟨nativeSubst substitution decorated.term, decorated.account,
    decorated.evidence⟩

@[simp] theorem reindex_term (substitution : NativeSub source target)
    {stage : Nat} (decorated : NativeDecoratedTm stage source) :
    (reindex substitution decorated).term =
      nativeSubst substitution decorated.term := rfl

@[simp] theorem reindex_account (substitution : NativeSub source target)
    {stage : Nat} (decorated : NativeDecoratedTm stage source) :
    (reindex substitution decorated).account = decorated.account := rfl

@[simp] theorem reindex_evidence (substitution : NativeSub source target)
    {stage : Nat} (decorated : NativeDecoratedTm stage source) :
    (reindex substitution decorated).evidence = decorated.evidence := rfl

@[simp] theorem reindex_ids {stage binders : Nat}
    (decorated : NativeDecoratedTm stage binders) :
    reindex nativeIds decorated = decorated := by
  cases decorated
  simp [reindex]

@[simp] theorem reindex_comp
    (later : NativeSub middle target) (earlier : NativeSub source middle)
    {stage : Nat} (decorated : NativeDecoratedTm stage source) :
    reindex later (reindex earlier decorated) =
      reindex (nativeSubComp later earlier) decorated := by
  cases decorated
  simp [reindex, nativeSubst_comp]

end NativeDecoratedTm

/-- The concrete one-step stage descent has nonzero cost. -/
theorem oneToZeroQuotation_cost_nonzero :
    stageRouteCost oneToZeroQuotation ≠ nativeCostZero := by
  intro equalAccounts
  have firstCoordinate := congrFun equalAccounts (0 : Fin 2)
  change (1 : Nat) = 0 at firstCoordinate
  omega

/-- Positive/negative cost witness: the same kernel term can carry a genuine
nonzero cost, and that decorated value is distinct from zero decoration. -/
theorem cost_decoration_is_external_and_nondegenerate :
    (NativeDecoratedTm.withCost quotedPureUniverse
        (stageRouteCost oneToZeroQuotation)).term = quotedPureUniverse ∧
      NativeDecoratedTm.withCost quotedPureUniverse
          (stageRouteCost oneToZeroQuotation) ≠
        NativeDecoratedTm.undecorated quotedPureUniverse := by
  constructor
  · rfl
  · intro equalDecorations
    have equalAccounts := congrArg NativeDecoratedTm.account equalDecorations
    exact oneToZeroQuotation_cost_nonzero equalAccounts

/-- Positive/negative evidence witness: evidence changes the decoration while
the projected kernel term remains byte-for-byte the same. -/
theorem evidence_decoration_is_external_and_nondegenerate :
    (NativeDecoratedTm.withEvidence nativeRuntimePattern
        (⟨1, 0⟩ : NativeEvidence)).term = nativeRuntimePattern ∧
      NativeDecoratedTm.withEvidence nativeRuntimePattern
          (⟨1, 0⟩ : NativeEvidence) ≠
        NativeDecoratedTm.undecorated nativeRuntimePattern := by
  constructor
  · rfl
  · intro equalDecorations
    have equalEvidence := congrArg NativeDecoratedTm.evidence equalDecorations
    have positiveCoordinates := congrArg
      Mettapedia.PLN.Evidence.BinEvNat.pos equalEvidence
    change (1 : Nat) = 0 at positiveCoordinates
    omega

/-! ### Nondegenerate interpretations and equality-profile compatibility -/

/-- Structural node count for the complete native signature. -/
abbrev nativeNodeCountAlgebra : NativeRawAlgebra where
  atStage := fun _ => pureNodeCountAlgebra
  pattern := fun _ => 1
  empty := 1
  superpose := fun left right => left + right + 1
  letE := fun value body => value + body + 1
  language := fun _ => 1
  quote := fun _ term => term + 1

def nativeNodeCount {stage binders : Nat} (term : StagedReflectiveTm stage binders) : Nat :=
  nativeRawFold nativeNodeCountAlgebra term

/-- Every native raw term has at least its root node. -/
theorem nativeNodeCount_positive {stage binders : Nat}
    (term : StagedReflectiveTm stage binders) : 0 < nativeNodeCount term := by
  induction term <;>
    simp [nativeNodeCount, nativeRawFold, nativeNodeCountAlgebra,
      pureNodeCountAlgebra]

namespace NativeTypedInitiality

/-- A noncollapsed context interpretation accompanying node-count raw
semantics.  Extension retains the stage-zero size of the declared family;
locking is a distinct context node. -/
def nodeCountContextAlgebra : ContextAlgebra nativeNodeCountAlgebra where
  Carrier := fun _ => Nat
  nil := 0
  snoc := fun context type => context + type 0 + 1
  lock := fun _ context => context + 1

/-- A genuine, independently computed target of typed initiality.  Its
judgment asserts positivity of both interpreted term and type sizes.  It is
deliberately a shape model, not a semantic typing adequacy claim. -/
def nodeCountTypingAlgebra :
    TypingAlgebra nativeNodeCountAlgebra nodeCountContextAlgebra where
  Judges := fun _ term type => 0 < term ∧ 0 < type
  u0_type := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  var := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  pi_form := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  sigma_form := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  lam_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  app_elim := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  pair_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  fst_elim := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  snd_elim := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  id_form := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  refl_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  let_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  pattern_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  language_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  empty_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  superpose_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  quote_intro := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩
  conv := by intros; exact ⟨nativeNodeCount_positive _, nativeNodeCount_positive _⟩

/-- The typed-presentation model category is inhabited by a nonconstant raw
interpretation. -/
def nodeCountModel : Model where
  raw := nativeNodeCountAlgebra
  contexts := nodeCountContextAlgebra
  typing := nodeCountTypingAlgebra

/-- Positive model witness: typed initiality computes the primitive sharing
term and its type to their genuine structural sizes. -/
theorem nodeCount_primitiveLet_image :
    nodeCountModel.typing.Judges
      (foldContext nodeCountModel.contexts (.nil : NativeModalTyping.Context 0))
      (nativeRawFold nodeCountModel.raw
        (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0))
      (nativeRawFold nodeCountModel.raw (.u1 : StagedReflectiveTm 0 0)) := by
  exact fold_typing nodeCountModel
    NativeModalTyping.primitiveLet_has_native_modal_type

/-- The positive target is noncollapsed: primitive sharing and its inlined
body receive different raw interpretations. -/
theorem nodeCount_model_separates_let_from_inlining :
    nativeRawFold nodeCountModel.raw
        (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0) ≠
      nativeRawFold nodeCountModel.raw
        (nativeInlineLet nativeU0Family (.var (0 : Fin 1))) := by
  change (3 : Nat) ≠ 1
  omega

/-- Concrete existence witness for the universal property, independent of
the free syntax as a target model. -/
theorem nodeCount_interpretation_exists :
    Nonempty (Interpretation nodeCountModel) :=
  ⟨canonicalInterpretation nodeCountModel⟩

end NativeTypedInitiality

/-! ### Raw equality profiles and the placement of sharing equations

This deliberately small profile layer records raw equality plus substitution
stability.  Typing conversion adds further laws later.  In particular,
let-inlining can be selected here without making it a constructor equation. -/

/-- A substitution-stable equality choice on the real staged raw syntax. -/
structure NativeRawEqualityProfile where
  setoid : (stage binders : Nat) → Setoid (StagedReflectiveTm stage binders)
  subst_closed : ∀ {source target stage}
      (substitution : NativeSub source target)
      {left right : StagedReflectiveTm stage source},
    (setoid stage source).r left right →
      (setoid stage target).r
        (nativeSubst substitution left) (nativeSubst substitution right)

namespace NativeRawEqualityProfile

def Rel (profile : NativeRawEqualityProfile)
    {stage binders : Nat} (left right : StagedReflectiveTm stage binders) : Prop :=
  (profile.setoid stage binders).r left right

end NativeRawEqualityProfile

/-- The finest raw profile: constructor equality only. -/
def nativeSyntacticEqualityProfile : NativeRawEqualityProfile where
  setoid := fun _ _ => ⟨Eq, Equivalence.mk (@Eq.refl _) (@Eq.symm _) (@Eq.trans _)⟩
  subst_closed := by
    intro source target stage substitution left right equal
    cases equal
    rfl

/-- A small noncollapsed semantics used to show that let-inlining profiles
need not identify the two universes.  It observes variables, universes, and
sharing; all other raw constructors are opaque at this observation level. -/
def nativeBoolObservation :
    {stage binders : Nat} → StagedReflectiveTm stage binders →
      (Fin binders → Bool) → Bool
  | _, _, .var index, environment => environment index
  | _, _, .u1, _ => true
  | _, _, .letE value body, environment =>
      nativeBoolObservation body
        (Fin.cases (nativeBoolObservation value environment) environment)
  | _, _, _, _ => false

theorem nativeBoolObservation_rename
    (rho : NativeRen source target) :
    ∀ {stage} (term : StagedReflectiveTm stage source)
      (environment : Fin target → Bool),
      nativeBoolObservation (nativeRename rho term) environment =
        nativeBoolObservation term (fun index => environment (rho index)) := by
  intro stage term
  induction term generalizing target with
  | var index => intro environment; rfl
  | const name => intro environment; rfl
  | u0 => intro environment; rfl
  | u1 => intro environment; rfl
  | pi domain body domainIH bodyIH => intro environment; rfl
  | sigma domain body domainIH bodyIH => intro environment; rfl
  | id type left right typeIH leftIH rightIH => intro environment; rfl
  | lam body bodyIH => intro environment; rfl
  | app function argument functionIH argumentIH => intro environment; rfl
  | pair left right leftIH rightIH => intro environment; rfl
  | fst pair pairIH => intro environment; rfl
  | snd pair pairIH => intro environment; rfl
  | refl value valueIH => intro environment; rfl
  | letE value body valueIH bodyIH =>
      intro environment
      simp only [nativeRename, nativeBoolObservation]
      rw [valueIH]
      rw [bodyIH]
      congr 1
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro previous
        rfl
  | pattern value => intro environment; rfl
  | empty => intro environment; rfl
  | superpose left right leftIH rightIH => intro environment; rfl
  | language value => intro environment; rfl
  | quote route value valueIH => intro environment; rfl

@[simp] theorem nativeBoolObservation_rename_wk
    {stage binders : Nat} (term : StagedReflectiveTm stage binders)
    (head : Bool) (environment : Fin binders → Bool) :
    nativeBoolObservation (nativeRename nativeWk term)
        (Fin.cases head environment) =
      nativeBoolObservation term environment := by
  rw [nativeBoolObservation_rename]
  congr 1

/-- The observation commutes with the real stage-indexed simultaneous
substitution.  The proof's lifted case is the reason primitive sharing uses a
binder rather than an unscoped pair of terms. -/
theorem nativeBoolObservation_subst
    (substitution : NativeSub source target) :
    ∀ {stage} (term : StagedReflectiveTm stage source)
      (environment : Fin target → Bool),
      nativeBoolObservation (nativeSubst substitution term) environment =
        nativeBoolObservation term
          (fun index => nativeBoolObservation
            (substitution stage index) environment) := by
  intro stage term
  induction term generalizing target with
  | var index => intro environment; rfl
  | const name => intro environment; rfl
  | u0 => intro environment; rfl
  | u1 => intro environment; rfl
  | pi domain body domainIH bodyIH => intro environment; rfl
  | sigma domain body domainIH bodyIH => intro environment; rfl
  | id type left right typeIH leftIH rightIH => intro environment; rfl
  | lam body bodyIH => intro environment; rfl
  | app function argument functionIH argumentIH => intro environment; rfl
  | pair left right leftIH rightIH => intro environment; rfl
  | fst pair pairIH => intro environment; rfl
  | snd pair pairIH => intro environment; rfl
  | refl value valueIH => intro environment; rfl
  | letE value body valueIH bodyIH =>
      intro environment
      simp only [nativeSubst, nativeBoolObservation]
      rw [valueIH]
      rw [bodyIH]
      congr 1
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro previous
        simp [nativeLiftSub, nativeBoolObservation_rename_wk]
  | pattern value => intro environment; rfl
  | empty => intro environment; rfl
  | superpose left right leftIH rightIH => intro environment; rfl
  | language value => intro environment; rfl
  | quote route value valueIH => intro environment; rfl

/-- Equality under every Boolean observation environment. -/
def nativeBooleanEqualityProfile : NativeRawEqualityProfile where
  setoid := fun _ _ =>
    { r := fun left right => ∀ environment,
        nativeBoolObservation left environment =
          nativeBoolObservation right environment
      iseqv :=
        { refl := fun _ _ => rfl
          symm := fun related environment => (related environment).symm
          trans := fun leftRight rightThird environment =>
            (leftRight environment).trans (rightThird environment) } }
  subst_closed := by
    intro source target stage substitution left right related environment
    rw [nativeBoolObservation_subst, nativeBoolObservation_subst]
    exact related _

/-- A profile validates sharing-inlining when its equality relates every raw
`letE` to simultaneous substitution of an explicit stage family. -/
def ValidatesLetInlining (profile : NativeRawEqualityProfile) : Prop :=
  ∀ {stage binders} (value : NativeTermFamily binders)
      (body : StagedReflectiveTm stage (binders + 1)),
    profile.Rel (.letE (value stage) body) (nativeInlineLet value body)

/-- Positive witness: the Boolean observation profile validates let-inlining
without collapsing the universe distinction. -/
theorem nativeBooleanEqualityProfile_validates_letInlining :
    ValidatesLetInlining nativeBooleanEqualityProfile := by
  intro stage binders value body environment
  simp only [nativeBoolObservation, nativeInlineLet]
  rw [nativeBoolObservation_subst]
  congr 1
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

theorem nativeBooleanEqualityProfile_separates_universes :
    ¬ nativeBooleanEqualityProfile.Rel
      (StagedReflectiveTm.u0 : StagedReflectiveTm 0 0) .u1 := by
  intro related
  have observed := related (fun index => Fin.elim0 index)
  change false = true at observed
  cases observed

/-- Negative witness: constructor equality does not silently inline sharing. -/
theorem nativeSyntacticEqualityProfile_rejects_letInlining :
    ¬ ValidatesLetInlining nativeSyntacticEqualityProfile := by
  intro validates
  have related := validates (stage := 0) (binders := 0)
    nativeU0Family (.var (0 : Fin 1))
  exact nativeLet_is_primitive_before_inlining related

namespace NativeRawEqualityProfile

/-- Every substitution-stable raw equality profile supplies exactly the
conversion interface required by the authored typing judgment.  This is a
bridge from optional equality packages into typing, not a choice of core
equality. -/
def toConversionPolicy (profile : NativeRawEqualityProfile) :
    NativeModalTyping.ConversionPolicy where
  Rel := profile.Rel
  equivalence := fun stage binders => (profile.setoid stage binders).iseqv
  subst_closed := profile.subst_closed

end NativeRawEqualityProfile

/-- The Boolean observation profile, exposed as one optional conversion
package used to test the post-initiality extension seam. -/
def nativeBooleanConversionPolicy : NativeModalTyping.ConversionPolicy :=
  nativeBooleanEqualityProfile.toConversionPolicy

/-- The optional Boolean profile contains every intensional syntactic
conversion. -/
theorem nativeBooleanConversion_extends_syntactic :
    nativeBooleanConversionPolicy.Extends
      NativeModalTyping.syntacticConversion :=
  NativeModalTyping.ConversionPolicy.extends_syntactic _

/-- The converse extension is impossible: Boolean observation validates
sharing-inlining, while the intensional core retains primitive sharing. -/
theorem syntacticConversion_does_not_extend_nativeBoolean :
    ¬ NativeModalTyping.syntacticConversion.Extends
      nativeBooleanConversionPolicy := by
  intro includes
  have related := nativeBooleanEqualityProfile_validates_letInlining
    (stage := 0) (binders := 0) nativeU0Family (.var (0 : Fin 1))
  exact nativeLet_is_primitive_before_inlining (includes related)

/-- A real authored typing derivation transports into the optional profile
without changing its term, type, context, or raw syntax. -/
theorem primitiveLet_typing_enters_nativeBoolean :
    NativeModalTyping.HasType nativeBooleanConversionPolicy .nil
      (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0) .u1 :=
  NativeModalTyping.primitiveLet_has_native_modal_type.of_syntactic _

/-- Concrete option-D calibration: the profile extension is strict, carries
real typing derivations, and still does not collapse the universe codes. -/
theorem nativeBoolean_is_strict_nondegenerate_typing_extension :
    nativeBooleanConversionPolicy.Extends
        NativeModalTyping.syntacticConversion ∧
      ¬ NativeModalTyping.syntacticConversion.Extends
        nativeBooleanConversionPolicy ∧
      ¬ nativeBooleanConversionPolicy.Rel
        (StagedReflectiveTm.u0 : StagedReflectiveTm 0 0) .u1 :=
  ⟨nativeBooleanConversion_extends_syntactic,
    syntacticConversion_does_not_extend_nativeBoolean,
    nativeBooleanEqualityProfile_separates_universes⟩

/-! ### The selected equality architecture

The intensional conversion policy is the sole core equality.  Stronger
equalities are explicit profile values equipped with typed inclusions from
the core.  No stronger profile is selected as production equality here.
Function extensionality, K/UIP, cubical composition, and univalence therefore
cannot enter the core through this record; a later authority must supply the
corresponding profile and laws explicitly. -/

/-- Option D as data: one fixed intensional core, a family of explicit
extensions, and a strict noncollapsed calibration point.  The absence of a
selected stronger profile is a field, so replacing the core requires changing
the architecture value rather than introducing an unqualified alias. -/
structure NativeEqualityArchitecture where
  core : NativeModalTyping.ConversionPolicy
  core_is_intensional : core = NativeModalTyping.syntacticConversion
  Extension : Type
  policy : Extension → NativeModalTyping.ConversionPolicy
  includesCore : ∀ extension, (policy extension).Extends core
  selectedStrongerProfile : Option Extension
  noSelectedStrongerProfile : selectedStrongerProfile = none
  calibration : Extension
  calibration_is_strict : ¬ core.Extends (policy calibration)
  calibration_preserves_universes :
    ¬ (policy calibration).Rel
      (StagedReflectiveTm.u0 : StagedReflectiveTm 0 0) .u1

namespace NativeEqualityArchitecture

/-- Every typing derivation in the fixed core transports to every explicit
extension without changing its context, term, type, or raw syntax. -/
theorem transport
    (architecture : NativeEqualityArchitecture)
    (extension : architecture.Extension)
    {context : NativeModalTyping.Context binders}
    {term type : StagedReflectiveTm stage binders}
    (typing : NativeModalTyping.HasType architecture.core context term type) :
    NativeModalTyping.HasType (architecture.policy extension) context term type :=
  typing.of_conversion_extension (architecture.includesCore extension)

/-- Anti-leak law: any extension not contained in the core cannot be made the
core by an alias or tag erasure. -/
theorem strictExtension_ne_core
    (architecture : NativeEqualityArchitecture)
    (extension : architecture.Extension)
    (strict : ¬ architecture.core.Extends (architecture.policy extension)) :
    architecture.policy extension ≠ architecture.core := by
  intro equal
  apply strict
  rw [equal]
  exact architecture.core.extends_refl

end NativeEqualityArchitecture

/-- The ratified architecture.  `nativeBooleanEqualityProfile` is only the
strict calibration witness; `selectedStrongerProfile = none` prevents it from
being mistaken for production conversion. -/
def selectedNativeEqualityArchitecture : NativeEqualityArchitecture where
  core := NativeModalTyping.syntacticConversion
  core_is_intensional := rfl
  Extension := NativeRawEqualityProfile
  policy := NativeRawEqualityProfile.toConversionPolicy
  includesCore := fun profile =>
    NativeModalTyping.ConversionPolicy.extends_syntactic
      profile.toConversionPolicy
  selectedStrongerProfile := none
  noSelectedStrongerProfile := rfl
  calibration := nativeBooleanEqualityProfile
  calibration_is_strict := syntacticConversion_does_not_extend_nativeBoolean
  calibration_preserves_universes :=
    nativeBooleanEqualityProfile_separates_universes

/-- Named anti-leak witness for the selected strict calibration profile. -/
theorem selectedEquality_calibration_does_not_alias_core :
    selectedNativeEqualityArchitecture.policy
        selectedNativeEqualityArchitecture.calibration ≠
      selectedNativeEqualityArchitecture.core :=
  selectedNativeEqualityArchitecture.strictExtension_ne_core
    selectedNativeEqualityArchitecture.calibration
    selectedNativeEqualityArchitecture.calibration_is_strict

/-- The architecture selects no production observational equality profile. -/
theorem selectedEquality_has_no_stronger_production_profile :
    selectedNativeEqualityArchitecture.selectedStrongerProfile = none :=
  selectedNativeEqualityArchitecture.noSelectedStrongerProfile

/-- The fixed core retains the already-proved typed-presentation initiality;
adding an equality profile does not create a second raw syntax or a second
initiality obligation. -/
@[reducible] def selectedEquality_core_is_initial
    (model : NativeTypedInitiality.Model.{uRawTarget}) :
    Unique (NativeTypedInitiality.Interpretation model) :=
  NativeTypedInitiality.initiality model

/-- Positive use of the architecture: the real primitive-sharing derivation
enters its calibration profile unchanged. -/
theorem selectedEquality_transports_primitiveLet :
    NativeModalTyping.HasType
      (selectedNativeEqualityArchitecture.policy
        selectedNativeEqualityArchitecture.calibration)
      .nil
      (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0) .u1 :=
  selectedNativeEqualityArchitecture.transport
    selectedNativeEqualityArchitecture.calibration
    NativeModalTyping.primitiveLet_has_native_modal_type

/-! ### Q5: a substitution-compositional graded cost fold -/

/-- Variable costs are indexed by both interpreter stage and support
position.  The stage coordinate is essential because a native substitution
may map the same variable differently underneath quotation. -/
abbrev NativeCostEnvironment (binders : Nat) :=
  (stage : Nat) → Fin binders → Nat

/-- A cost grade is a polynomial represented extensionally by its action on
stage-indexed variable costs. -/
abbrev NativeCostGrade (binders : Nat) :=
  NativeCostEnvironment binders → Nat

/-- Enter a binder: its bound variable has unit syntactic cost at every
stage, while older variables retain their supplied costs. -/
def nativeLiftCostEnvironment
    (environment : NativeCostEnvironment binders) :
    NativeCostEnvironment (binders + 1) :=
  fun stage => Fin.cases 1 (environment stage)

/-- The Pure fragment of the graded raw algebra at one interpreter stage. -/
abbrev nativePureGradedCostAlgebra (stage : Nat) : PureRawAlgebra where
  Carrier := NativeCostGrade
  var := fun index environment => environment stage index
  const := fun _ _ => 1
  u0 := fun _ => 1
  u1 := fun _ => 1
  pi := fun domain body environment =>
    1 + domain environment + body (nativeLiftCostEnvironment environment)
  sigma := fun domain body environment =>
    1 + domain environment + body (nativeLiftCostEnvironment environment)
  id := fun type left right environment =>
    1 + type environment + left environment + right environment
  lam := fun body environment =>
    1 + body (nativeLiftCostEnvironment environment)
  app := fun function argument environment =>
    1 + function environment + argument environment
  pair := fun left right environment =>
    1 + left environment + right environment
  fst := fun pair environment => 1 + pair environment
  snd := fun pair environment => 1 + pair environment
  refl := fun term environment => 1 + term environment

/-- The complete graded-cost algebra on the real native raw signature. -/
abbrev nativeGradedCostRawAlgebra : NativeRawAlgebra where
  atStage := nativePureGradedCostAlgebra
  pattern := fun _ _ => 1
  empty := fun _ => 1
  superpose := fun left right environment =>
    1 + left environment + right environment
  letE := fun value body environment =>
    1 + value environment + body (nativeLiftCostEnvironment environment)
  language := fun _ _ => 1
  quote := fun _ term environment => 1 + term environment

/-- The Q5 grade is literally the structural fold into the graded algebra. -/
def nativeGradedCost {stage binders : Nat}
    (term : StagedReflectiveTm stage binders) : NativeCostGrade binders :=
  nativeRawFold nativeGradedCostRawAlgebra term

theorem nativeLiftCostEnvironment_rename
    (rho : NativeRen source target)
    (environment : NativeCostEnvironment target) :
    (fun stage index =>
      nativeLiftCostEnvironment environment stage (nativeLiftRen rho index)) =
      nativeLiftCostEnvironment
        (fun stage index => environment stage (rho index)) := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

/-- Grading is natural under support renaming. -/
theorem nativeGradedCost_rename
    (rho : NativeRen source target) :
    ∀ {stage} (term : StagedReflectiveTm stage source)
      (environment : NativeCostEnvironment target),
      nativeGradedCost (nativeRename rho term) environment =
        nativeGradedCost term
          (fun current index => environment current (rho index)) := by
  intro stage term
  induction term generalizing target with
  | var index => intro environment; rfl
  | const name => intro environment; rfl
  | u0 => intro environment; rfl
  | u1 => intro environment; rfl
  | pi domain body domainIH bodyIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho domain) environment +
          nativeGradedCost (nativeRename (nativeLiftRen rho) body)
            (nativeLiftCostEnvironment environment) =
        1 + nativeGradedCost domain
            (fun current index => environment current (rho index)) +
          nativeGradedCost body
            (nativeLiftCostEnvironment
              (fun current index => environment current (rho index)))
      rw [domainIH, bodyIH, nativeLiftCostEnvironment_rename]
  | sigma domain body domainIH bodyIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho domain) environment +
          nativeGradedCost (nativeRename (nativeLiftRen rho) body)
            (nativeLiftCostEnvironment environment) =
        1 + nativeGradedCost domain
            (fun current index => environment current (rho index)) +
          nativeGradedCost body
            (nativeLiftCostEnvironment
              (fun current index => environment current (rho index)))
      rw [domainIH, bodyIH, nativeLiftCostEnvironment_rename]
  | id type left right typeIH leftIH rightIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho type) environment +
          nativeGradedCost (nativeRename rho left) environment +
          nativeGradedCost (nativeRename rho right) environment =
        1 + nativeGradedCost type
            (fun current index => environment current (rho index)) +
          nativeGradedCost left
            (fun current index => environment current (rho index)) +
          nativeGradedCost right
            (fun current index => environment current (rho index))
      rw [typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename (nativeLiftRen rho) body)
          (nativeLiftCostEnvironment environment) =
        1 + nativeGradedCost body
          (nativeLiftCostEnvironment
            (fun current index => environment current (rho index)))
      rw [bodyIH, nativeLiftCostEnvironment_rename]
  | app function argument functionIH argumentIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho function) environment +
          nativeGradedCost (nativeRename rho argument) environment =
        1 + nativeGradedCost function
            (fun current index => environment current (rho index)) +
          nativeGradedCost argument
            (fun current index => environment current (rho index))
      rw [functionIH, argumentIH]
  | pair left right leftIH rightIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho left) environment +
          nativeGradedCost (nativeRename rho right) environment =
        1 + nativeGradedCost left
            (fun current index => environment current (rho index)) +
          nativeGradedCost right
            (fun current index => environment current (rho index))
      rw [leftIH, rightIH]
  | fst pair pairIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho pair) environment =
        1 + nativeGradedCost pair
          (fun current index => environment current (rho index))
      rw [pairIH]
  | snd pair pairIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho pair) environment =
        1 + nativeGradedCost pair
          (fun current index => environment current (rho index))
      rw [pairIH]
  | refl value valueIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho value) environment =
        1 + nativeGradedCost value
          (fun current index => environment current (rho index))
      rw [valueIH]
  | letE value body valueIH bodyIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho value) environment +
          nativeGradedCost (nativeRename (nativeLiftRen rho) body)
            (nativeLiftCostEnvironment environment) =
        1 + nativeGradedCost value
            (fun current index => environment current (rho index)) +
          nativeGradedCost body
            (nativeLiftCostEnvironment
              (fun current index => environment current (rho index)))
      rw [valueIH, bodyIH, nativeLiftCostEnvironment_rename]
  | pattern value => intro environment; rfl
  | empty => intro environment; rfl
  | superpose left right leftIH rightIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho left) environment +
          nativeGradedCost (nativeRename rho right) environment =
        1 + nativeGradedCost left
            (fun current index => environment current (rho index)) +
          nativeGradedCost right
            (fun current index => environment current (rho index))
      rw [leftIH, rightIH]
  | language value => intro environment; rfl
  | quote route value valueIH =>
      intro environment
      change 1 + nativeGradedCost (nativeRename rho value) environment =
        1 + nativeGradedCost value
          (fun current index => environment current (rho index))
      rw [valueIH]

theorem nativeLiftCostEnvironment_subst
    (substitution : NativeSub source target)
    (environment : NativeCostEnvironment target) :
    (fun stage index =>
      nativeGradedCost (nativeLiftSub substitution stage index)
        (nativeLiftCostEnvironment environment)) =
      nativeLiftCostEnvironment
        (fun stage index => nativeGradedCost
          (substitution stage index) environment) := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rw [show nativeLiftSub substitution stage previous.succ =
        nativeRename nativeWk (substitution stage previous) by rfl]
    rw [nativeGradedCost_rename]
    rfl

/-- The grade composes along the actual stage-indexed simultaneous
substitution: substituting syntax is exactly substitution of its cost
polynomial. -/
theorem nativeGradedCost_subst
    (substitution : NativeSub source target) :
    ∀ {stage} (term : StagedReflectiveTm stage source)
      (environment : NativeCostEnvironment target),
      nativeGradedCost (nativeSubst substitution term) environment =
        nativeGradedCost term
          (fun current index => nativeGradedCost
            (substitution current index) environment) := by
  intro stage term
  induction term generalizing target with
  | var index => intro environment; rfl
  | const name => intro environment; rfl
  | u0 => intro environment; rfl
  | u1 => intro environment; rfl
  | pi domain body domainIH bodyIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution domain) environment +
          nativeGradedCost (nativeSubst (nativeLiftSub substitution) body)
            (nativeLiftCostEnvironment environment) =
        1 + nativeGradedCost domain
            (fun current index => nativeGradedCost
              (substitution current index) environment) +
          nativeGradedCost body
            (nativeLiftCostEnvironment
              (fun current index => nativeGradedCost
                (substitution current index) environment))
      rw [domainIH, bodyIH, nativeLiftCostEnvironment_subst]
  | sigma domain body domainIH bodyIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution domain) environment +
          nativeGradedCost (nativeSubst (nativeLiftSub substitution) body)
            (nativeLiftCostEnvironment environment) =
        1 + nativeGradedCost domain
            (fun current index => nativeGradedCost
              (substitution current index) environment) +
          nativeGradedCost body
            (nativeLiftCostEnvironment
              (fun current index => nativeGradedCost
                (substitution current index) environment))
      rw [domainIH, bodyIH, nativeLiftCostEnvironment_subst]
  | id type left right typeIH leftIH rightIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution type) environment +
          nativeGradedCost (nativeSubst substitution left) environment +
          nativeGradedCost (nativeSubst substitution right) environment =
        1 + nativeGradedCost type
            (fun current index => nativeGradedCost
              (substitution current index) environment) +
          nativeGradedCost left
            (fun current index => nativeGradedCost
              (substitution current index) environment) +
          nativeGradedCost right
            (fun current index => nativeGradedCost
              (substitution current index) environment)
      rw [typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      intro environment
      change 1 + nativeGradedCost
          (nativeSubst (nativeLiftSub substitution) body)
            (nativeLiftCostEnvironment environment) =
        1 + nativeGradedCost body
          (nativeLiftCostEnvironment
            (fun current index => nativeGradedCost
              (substitution current index) environment))
      rw [bodyIH, nativeLiftCostEnvironment_subst]
  | app function argument functionIH argumentIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution function) environment +
          nativeGradedCost (nativeSubst substitution argument) environment =
        1 + nativeGradedCost function
            (fun current index => nativeGradedCost
              (substitution current index) environment) +
          nativeGradedCost argument
            (fun current index => nativeGradedCost
              (substitution current index) environment)
      rw [functionIH, argumentIH]
  | pair left right leftIH rightIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution left) environment +
          nativeGradedCost (nativeSubst substitution right) environment =
        1 + nativeGradedCost left
            (fun current index => nativeGradedCost
              (substitution current index) environment) +
          nativeGradedCost right
            (fun current index => nativeGradedCost
              (substitution current index) environment)
      rw [leftIH, rightIH]
  | fst pair pairIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution pair) environment =
        1 + nativeGradedCost pair
          (fun current index => nativeGradedCost
            (substitution current index) environment)
      rw [pairIH]
  | snd pair pairIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution pair) environment =
        1 + nativeGradedCost pair
          (fun current index => nativeGradedCost
            (substitution current index) environment)
      rw [pairIH]
  | refl value valueIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution value) environment =
        1 + nativeGradedCost value
          (fun current index => nativeGradedCost
            (substitution current index) environment)
      rw [valueIH]
  | letE value body valueIH bodyIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution value) environment +
          nativeGradedCost (nativeSubst (nativeLiftSub substitution) body)
            (nativeLiftCostEnvironment environment) =
        1 + nativeGradedCost value
            (fun current index => nativeGradedCost
              (substitution current index) environment) +
          nativeGradedCost body
            (nativeLiftCostEnvironment
              (fun current index => nativeGradedCost
                (substitution current index) environment))
      rw [valueIH, bodyIH, nativeLiftCostEnvironment_subst]
  | pattern value => intro environment; rfl
  | empty => intro environment; rfl
  | superpose left right leftIH rightIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution left) environment +
          nativeGradedCost (nativeSubst substitution right) environment =
        1 + nativeGradedCost left
            (fun current index => nativeGradedCost
              (substitution current index) environment) +
          nativeGradedCost right
            (fun current index => nativeGradedCost
              (substitution current index) environment)
      rw [leftIH, rightIH]
  | language value => intro environment; rfl
  | quote route value valueIH =>
      intro environment
      change 1 + nativeGradedCost (nativeSubst substitution value) environment =
        1 + nativeGradedCost value
          (fun current index => nativeGradedCost
            (substitution current index) environment)
      rw [valueIH]

/-- The theorem-bearing graded algebra package. -/
structure GradedCostAlgebra where
  grade : {stage binders : Nat} → StagedReflectiveTm stage binders →
    NativeCostGrade binders
  rename_comp : ∀ {source target} (rho : NativeRen source target)
      {stage} (term : StagedReflectiveTm stage source) environment,
    grade (nativeRename rho term) environment =
      grade term (fun current index => environment current (rho index))
  subst_comp : ∀ {source target} (substitution : NativeSub source target)
      {stage} (term : StagedReflectiveTm stage source) environment,
    grade (nativeSubst substitution term) environment =
      grade term (fun current index =>
        grade (substitution current index) environment)

def nativeGradedCostAlgebra : GradedCostAlgebra where
  grade := nativeGradedCost
  rename_comp := nativeGradedCost_rename
  subst_comp := nativeGradedCost_subst

/-- Assign unit cost to every free variable occurrence. -/
def nativeUnitCostEnvironment : NativeCostEnvironment binders :=
  fun _ _ => 1

def nativeStructuralCost {stage binders : Nat}
    (term : StagedReflectiveTm stage binders) : Nat :=
  nativeGradedCost term nativeUnitCostEnvironment

/-- Cost factorization through a selected raw equality quotient. -/
def StructuralCostFactorsThrough (profile : NativeRawEqualityProfile) : Prop :=
  ∃ factor : ∀ stage binders,
      Quotient (profile.setoid stage binders) → Nat,
    ∀ {stage binders} (term : StagedReflectiveTm stage binders),
      factor stage binders (Quotient.mk (profile.setoid stage binders) term) =
        nativeStructuralCost term

theorem nativeLet_structural_cost :
    nativeStructuralCost
        (StagedReflectiveTm.letE .u0 (.var (0 : Fin 1)) : StagedReflectiveTm 0 0) = 3 :=
  rfl

theorem nativeInlineLet_structural_cost :
    nativeStructuralCost
        (nativeInlineLet nativeU0Family (.var (0 : Fin 1)) :
          StagedReflectiveTm 0 0) = 1 :=
  rfl

/-- Q5 placement theorem: structural cost is raw decoration.  It cannot be a
function on any equality quotient that validates sharing-inlining. -/
theorem graded_cost_not_profile_invariant
    (profile : NativeRawEqualityProfile)
    (inlines : ValidatesLetInlining profile) :
    ¬ StructuralCostFactorsThrough profile := by
  rintro ⟨factor, factors⟩
  let shared : StagedReflectiveTm 0 0 := .letE .u0 (.var (0 : Fin 1))
  let inlined : StagedReflectiveTm 0 0 :=
    nativeInlineLet nativeU0Family (.var (0 : Fin 1))
  have related : profile.Rel shared inlined :=
    inlines nativeU0Family (.var (0 : Fin 1))
  have equalClasses :
      Quotient.mk (profile.setoid 0 0) shared =
        Quotient.mk (profile.setoid 0 0) inlined :=
    Quotient.sound related
  have equalCosts : nativeStructuralCost shared = nativeStructuralCost inlined := by
    rw [← factors shared, ← factors inlined, equalClasses]
  change (3 : Nat) = 1 at equalCosts
  omega

/-- The placement theorem is nonvacuous: its noncollapsed Boolean profile
really validates inlining. -/
theorem nativeBoolean_cost_does_not_factor :
    ¬ StructuralCostFactorsThrough nativeBooleanEqualityProfile :=
  graded_cost_not_profile_invariant nativeBooleanEqualityProfile
    nativeBooleanEqualityProfile_validates_letInlining

/-! ### Q6: proof-relevant derivation bags and truth erasure

The proof-relevant carrier is indexed by the actual native modal typing
judgment.  Erasing a proof bag first retains only its multiplicity at each
judgment and then takes positive support.  The adjunction is stated at that
counting layer: freely marking each asserted truth once is left adjoint to
positive support.  There is deliberately no function that manufactures an
actual typing derivation from an arbitrary truth set. -/

/-- A closed package of all indices in one real native modal typing
judgment. -/
structure NativeTypingClaim where
  binders : Nat
  stage : Nat
  context : NativeModalTyping.Context binders
  term : StagedReflectiveTm stage binders
  type : StagedReflectiveTm stage binders

/-- The authored typing derivations inhabiting a native claim. -/
abbrev NativeTypingDerivation (claim : NativeTypingClaim) :=
  NativeModalTyping.HasType NativeModalTyping.syntacticConversion claim.context
    claim.term claim.type

/-- One proof occurrence together with the external PLN evidence retained
for that occurrence. -/
structure NativeEvidenceDerivation (claim : NativeTypingClaim) where
  derivation : NativeTypingDerivation claim
  evidence : NativeEvidence

/-- Optional hypothetical structure above native typing.  Premises may be
used directly; independently authored native derivations remain valid under
weakening and simultaneous cut. -/
inductive NativeHypotheticalEvidence
    (premises : Set NativeTypingClaim) : NativeTypingClaim → Type where
  | assumption {claim : NativeTypingClaim} :
      claim ∈ premises → NativeHypotheticalEvidence premises claim
  | typed {claim : NativeTypingClaim} :
      NativeEvidenceDerivation claim →
        NativeHypotheticalEvidence premises claim

/-- The real native typing layer instantiates NIK's proof-relevant
set-evidence doctrine.  Its proof objects are native typing derivations with
retained PLN evidence, not generic Boolean tags. -/
def nativeTypingEvidenceDoctrine :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.SetEvidenceDoctrine
      NativeTypingClaim where
  Evidence := NativeHypotheticalEvidence
  assumption := NativeHypotheticalEvidence.assumption
  weakening := by
    intro source target claim subset evidence
    cases evidence with
    | assumption member => exact .assumption (subset member)
    | typed entry => exact .typed entry
  substitute := by
    intro ambient intermediate claim evidence substitutions
    cases evidence with
    | assumption member => exact substitutions _ member
    | typed entry => exact .typed entry

/-- Q6's categorical adjunction on the actual native typing formula
language: proof-relevant doctrines reflect into their thin, truth-level
closures.  This is the existing NIK theorem instantiated rather than a second
competing notion of proof erasure. -/
noncomputable def nativeTypingProofErasureAdjunction :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.SetEvidenceDoctrine.proofErasureThinAdjunction
    (Formula := NativeTypingClaim)

/-- A proof-relevant bag at every native typing claim.  Repeated entries are
distinct occurrences even when proof irrelevance identifies their Lean proof
fields. -/
abbrev NativeDerivationBag :=
  (claim : NativeTypingClaim) → Multiset (NativeEvidenceDerivation claim)

/-- The multiplicity shadow of a derivation bag. -/
abbrev NativeDerivationCountBag := NativeTypingClaim → Nat

namespace NativeDerivationCountBag

/-- Positive support is the proof-erased truth set. -/
def truthSet (bag : NativeDerivationCountBag) : Set NativeTypingClaim :=
  { claim | 0 < bag claim }

/-- Regard every asserted truth as one derivation occurrence.  This is a
counting section only; it does not forge a native proof object. -/
noncomputable def ofTruthSet
    (truth : Set NativeTypingClaim) : NativeDerivationCountBag := by
  classical
  exact fun claim => if claim ∈ truth then 1 else 0

/-- Count-bag inclusion against a unit truth bag is exactly truth inclusion
against positive support.  This Galois connection is the order-enriched
adjunction from derivation multiplicities to proof-erased truth. -/
theorem truthSet_galois :
    GaloisConnection ofTruthSet truthSet := by
  intro truth bag
  constructor
  · intro bounded claim member
    have atClaim := bounded claim
    change 0 < bag claim
    have one_le : 1 ≤ bag claim := by
      simpa [ofTruthSet, member] using atClaim
    exact one_le
  · intro included claim
    by_cases member : claim ∈ truth
    · rw [show ofTruthSet truth claim = 1 by
        simp [ofTruthSet, member]]
      have positive : 0 < bag claim := included member
      exact positive
    · rw [show ofTruthSet truth claim = 0 by
        simp [ofTruthSet, member]]
      exact Nat.zero_le _

/-- The adjunction's unit is exact: erasing the unit-count presentation
recovers the original truth set. -/
theorem truthSet_ofTruthSet (truth : Set NativeTypingClaim) :
    truthSet (ofTruthSet truth) = truth := by
  classical
  ext claim
  by_cases member : claim ∈ truth <;>
    simp [truthSet, ofTruthSet, member]

/-- The counit retains no more than the original multiplicity bag. -/
theorem ofTruthSet_truthSet_le (bag : NativeDerivationCountBag) :
    ofTruthSet (truthSet bag) ≤ bag :=
  (truthSet_galois (truthSet bag) bag).2 Set.Subset.rfl

end NativeDerivationCountBag

namespace NativeDerivationBag

/-- Forget proof objects and evidence while retaining occurrence counts. -/
def count (bag : NativeDerivationBag) : NativeDerivationCountBag :=
  fun claim => (bag claim).card

/-- Truth erasure of a proof-relevant bag. -/
def truthSet (bag : NativeDerivationBag) : Set NativeTypingClaim :=
  { claim | 0 < (bag claim).card }

/-- Truth erasure agrees exactly with positive support of the multiplicity
shadow. -/
theorem truthSet_eq_count_truthSet (bag : NativeDerivationBag) :
    truthSet bag = NativeDerivationCountBag.truthSet (count bag) := by
  ext claim
  rfl

/-- A single genuine proof occurrence, supported at exactly one claim. -/
noncomputable def singleton {claim : NativeTypingClaim}
    (entry : NativeEvidenceDerivation claim) : NativeDerivationBag := by
  classical
  exact fun candidate =>
    if equal : candidate = claim then
      {equal.symm ▸ entry}
    else
      0

@[simp] theorem singleton_at {claim : NativeTypingClaim}
    (entry : NativeEvidenceDerivation claim) :
    singleton entry claim = {entry} := by
  classical
  simp [singleton]

/-- Aggregate the retained evidence at one native typing claim. -/
def evidenceAt (bag : NativeDerivationBag) (claim : NativeTypingClaim) :
    NativeEvidence :=
  (bag claim).map NativeEvidenceDerivation.evidence |>.sum

/-- The live PLN strength readout of the evidence retained at one claim. -/
def strengthAt (bag : NativeDerivationBag) (claim : NativeTypingClaim) :
    Nat × Nat :=
  (evidenceAt bag claim).strength

/-- Factoring strength through truth erasure would make the readout a
function of the proof-irrelevant truth set alone. -/
def StrengthFactorsThroughTruthAt (claim : NativeTypingClaim) : Prop :=
  ∃ readout : Set NativeTypingClaim → Nat × Nat,
    ∀ bag : NativeDerivationBag,
      readout (truthSet bag) = strengthAt bag claim

end NativeDerivationBag

/-- The concrete primitive-let judgment used as the nondegenerate Q6 fibre. -/
def primitiveLetTypingClaim : NativeTypingClaim where
  binders := 0
  stage := 0
  context := .nil
  term := .letE .u0 (.var (0 : Fin 1))
  type := .u1

/-- The primitive-let claim carries a real authored typing derivation. -/
def primitiveLetTypingDerivation :
    NativeTypingDerivation primitiveLetTypingClaim :=
  NativeModalTyping.primitiveLet_has_native_modal_type

def primitiveLetEvidenceOne :
    NativeEvidenceDerivation primitiveLetTypingClaim :=
  ⟨primitiveLetTypingDerivation, ⟨1, 0⟩⟩

def primitiveLetEvidenceTwo :
    NativeEvidenceDerivation primitiveLetTypingClaim :=
  ⟨primitiveLetTypingDerivation, ⟨2, 0⟩⟩

def primitiveLetHypotheticalEvidenceOne :
    nativeTypingEvidenceDoctrine.Evidence ∅ primitiveLetTypingClaim :=
  .typed primitiveLetEvidenceOne

def primitiveLetHypotheticalEvidenceTwo :
    nativeTypingEvidenceDoctrine.Evidence ∅ primitiveLetTypingClaim :=
  .typed primitiveLetEvidenceTwo

/-- The actual native proof fibre is non-thin: equal theoremhood retains two
different PLN evidence strengths. -/
theorem nativeTypingEvidence_not_subsingleton :
    ¬ Subsingleton
      (nativeTypingEvidenceDoctrine.Evidence ∅ primitiveLetTypingClaim) := by
  intro thin
  have equalEvidence := thin.elim primitiveLetHypotheticalEvidenceOne
    primitiveLetHypotheticalEvidenceTwo
  have equalEntries : primitiveLetEvidenceOne = primitiveLetEvidenceTwo := by
    injection equalEvidence
  have equalPLN := congrArg NativeEvidenceDerivation.evidence equalEntries
  have equalPos := congrArg Mettapedia.PLN.Evidence.BinEvNat.pos equalPLN
  change (1 : Nat) = 2 at equalPos
  omega

/-- Positive proof-erasure witness: the primitive-let judgment belongs to the
induced truth-level consequence closure. -/
theorem primitiveLetTypingClaim_in_erased_consequence :
    primitiveLetTypingClaim ∈
      nativeTypingEvidenceDoctrine.consequence ∅ :=
  ⟨primitiveLetHypotheticalEvidenceOne⟩

/-- Negative categorical witness: the unit into thin evidence is not
injective on the inhabited primitive-let fibre.  Hence the adjunction is a
reflection, not an equivalence of proof presentations. -/
theorem nativeTyping_toThinReflection_not_injective :
    ¬ Function.Injective
      (nativeTypingEvidenceDoctrine.toThinReflection
        (premises := ∅) (formula := primitiveLetTypingClaim)) := by
  intro injective
  have thin :=
    (nativeTypingEvidenceDoctrine
      |>.toThinReflection_injective_iff_subsingleton ∅
        primitiveLetTypingClaim).mp injective
  exact nativeTypingEvidence_not_subsingleton thin

noncomputable def primitiveLetEvidenceBagOne : NativeDerivationBag :=
  NativeDerivationBag.singleton primitiveLetEvidenceOne

noncomputable def primitiveLetEvidenceBagTwo : NativeDerivationBag :=
  NativeDerivationBag.singleton primitiveLetEvidenceTwo

/-- Positive erasure witness: two proof-relevant bags with different PLN
evidence assert exactly the same native typing truth. -/
theorem primitiveLetEvidenceBags_same_truth :
    NativeDerivationBag.truthSet primitiveLetEvidenceBagOne =
      NativeDerivationBag.truthSet primitiveLetEvidenceBagTwo := by
  classical
  ext claim
  by_cases equal : claim = primitiveLetTypingClaim <;>
    simp [NativeDerivationBag.truthSet, primitiveLetEvidenceBagOne,
      primitiveLetEvidenceBagTwo, NativeDerivationBag.singleton, equal]

theorem primitiveLetEvidenceBagOne_strength :
    NativeDerivationBag.strengthAt primitiveLetEvidenceBagOne
      primitiveLetTypingClaim = (1, 1) := by
  simp [NativeDerivationBag.strengthAt, NativeDerivationBag.evidenceAt,
    primitiveLetEvidenceBagOne, primitiveLetEvidenceOne,
    Mettapedia.PLN.Evidence.BinEvNat.strength]

theorem primitiveLetEvidenceBagTwo_strength :
    NativeDerivationBag.strengthAt primitiveLetEvidenceBagTwo
      primitiveLetTypingClaim = (2, 2) := by
  simp [NativeDerivationBag.strengthAt, NativeDerivationBag.evidenceAt,
    primitiveLetEvidenceBagTwo, primitiveLetEvidenceTwo,
    Mettapedia.PLN.Evidence.BinEvNat.strength]

/-- Negative occurrence witness: proof erasure identifies two genuinely
different evidence bags. -/
theorem primitiveLetEvidenceBags_distinct :
    primitiveLetEvidenceBagOne ≠ primitiveLetEvidenceBagTwo := by
  intro equalBags
  have equalStrength := congrArg
    (fun bag => NativeDerivationBag.strengthAt bag primitiveLetTypingClaim)
    equalBags
  rw [primitiveLetEvidenceBagOne_strength,
    primitiveLetEvidenceBagTwo_strength] at equalStrength
  cases equalStrength

/-- Q6 placement theorem: the live PLN strength coordinate is not recoverable
from the proof-erased truth set, even on an inhabited native raw typing fibre.
Thus evidence remains on raw derivation occurrences rather than becoming a
truth-level annotation. -/
theorem nativeEvidence_strength_does_not_factor_through_truth :
    ¬ NativeDerivationBag.StrengthFactorsThroughTruthAt
      primitiveLetTypingClaim := by
  rintro ⟨readout, factors⟩
  have one := factors primitiveLetEvidenceBagOne
  have two := factors primitiveLetEvidenceBagTwo
  rw [primitiveLetEvidenceBags_same_truth] at one
  have equalStrength := one.symm.trans two
  rw [primitiveLetEvidenceBagOne_strength,
    primitiveLetEvidenceBagTwo_strength] at equalStrength
  cases equalStrength

/-! ### Q7: one staged quotation former for terms and language values

There are two legitimate uses of the word "code" here.  A Tarski universe
code classifies a *type* (for example, the type of validated language
presentations).  Quotation produces code for a *particular term*.  They must
not be identified.  Once a validated presentation is available through its
Tarski-classified carrier, the existing `StagedReflectiveTm.quote` is the only
term-level former used to quote it; no language-specific quotation
constructor is added. -/

/-- The canonical adjacent-stage quotation route.  Its evaluator stage
descends from `level + 1` to `level`, while its reflective-code grade is one. -/
def adjacentQuotation (level : Nat) : StageHom (level + 1) level :=
  ⟨Nat.le_succ level, 1⟩

/-- A reverse evaluator-stage edge cannot be forged.  Strict reflective
depth below is therefore not being confused with ascent in the stage
category. -/
theorem no_reverse_adjacent_stage (level : Nat) :
    IsEmpty (StageHom level (level + 1)) :=
  ⟨fun route => Nat.not_succ_le_self level route.descent⟩

/-- The common level-indexed quotation operation. -/
def nativeQuoteNext (level : Nat)
    (term : StagedReflectiveTm (level + 1) binders) :
    StagedReflectiveTm level binders :=
  .quote (adjacentQuotation level) term

/-- Reflection depth for the Pure fragment.  Ordinary type-theoretic
constructors combine the maximum depth of their children. -/
abbrev nativePureReflectiveDepthAlgebra : PureRawAlgebra where
  Carrier := fun _ => Nat
  var := fun _ => 0
  const := fun _ => 0
  u0 := 0
  u1 := 0
  pi := max
  sigma := max
  id := fun type left right => max type (max left right)
  lam := _root_.id
  app := max
  pair := max
  fst := _root_.id
  snd := _root_.id
  refl := _root_.id

/-- Reflection-depth algebra for the full native raw signature. -/
abbrev nativeReflectiveDepthAlgebra : NativeRawAlgebra where
  atStage := fun _ => nativePureReflectiveDepthAlgebra
  pattern := fun _ => 0
  empty := 0
  superpose := max
  letE := max
  language := fun _ => 0
  quote := fun route termDepth => route.quoteDepth + termDepth

/-- The reflective level is the fold induced by the quotation grade already
carried by `StageHom`; it is not a second syntactic level annotation. -/
def StagedReflectiveTm.reflectiveDepth
    (term : StagedReflectiveTm stage binders) : Nat :=
  nativeRawFold nativeReflectiveDepthAlgebra term

@[simp] theorem StagedReflectiveTm.reflectiveDepth_quote
    (route : StageHom high low) (term : StagedReflectiveTm high binders) :
    reflectiveDepth (.quote route term) =
      route.quoteDepth + reflectiveDepth term :=
  rfl

/-- Every positive-grade quotation strictly raises reflective code depth. -/
theorem StagedReflectiveTm.quote_strictly_raises_reflectiveDepth
    (route : StageHom high low) (positive : 0 < route.quoteDepth)
    (term : StagedReflectiveTm high binders) :
    term.reflectiveDepth <
      (StagedReflectiveTm.quote route term).reflectiveDepth := by
  rw [reflectiveDepth_quote]
  omega

/-- In particular, the common adjacent-stage quotation raises reflective
depth by exactly one. -/
theorem nativeQuoteNext_reflectiveDepth (level : Nat)
    (term : StagedReflectiveTm (level + 1) binders) :
    (nativeQuoteNext level term).reflectiveDepth =
      term.reflectiveDepth + 1 := by
  simp [nativeQuoteNext, adjacentQuotation, Nat.add_comm]

theorem nativeQuoteNext_strictly_raises (level : Nat)
    (term : StagedReflectiveTm (level + 1) binders) :
    term.reflectiveDepth < (nativeQuoteNext level term).reflectiveDepth := by
  rw [nativeQuoteNext_reflectiveDepth]
  exact Nat.lt_succ_self _

/-- A particular validated presentation is quoted through the same former as
every other staged native term. -/
def nativeQuotedLanguage (level : Nat)
    (value : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef) :
    StagedReflectiveTm level 0 :=
  nativeQuoteNext level
    (StagedReflectiveTm.language value : StagedReflectiveTm (level + 1) 0)

/-- Partial observation of the language-value fragment inside quoted code. -/
def StagedReflectiveTm.quotedLanguage? :
    StagedReflectiveTm stage binders →
      Option Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef
  | .quote _ (.language value) => some value
  | _ => none

@[simp] theorem quotedLanguage?_nativeQuotedLanguage (level : Nat)
    (value : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef) :
    (nativeQuotedLanguage level value).quotedLanguage? = some value :=
  rfl

/-- Quoted language values receive the ordinary locked-context quotation
rule; there is no special language-code typing rule. -/
theorem nativeQuotedLanguage_has_type (level : Nat)
    (value : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef) :
    NativeModalTyping.HasType NativeModalTyping.syntacticConversion .nil
      (nativeQuotedLanguage level value)
      (nativeQuoteNext level
        (StagedReflectiveTm.u0 : StagedReflectiveTm (level + 1) 0)) := by
  exact NativeModalTyping.HasType.quote_intro (adjacentQuotation level)
    (NativeModalTyping.HasType.language_intro
      (.lock (adjacentQuotation level) .nil) value)

/-- The current Prime presentation is taken directly from the carrier
classified by the existing Tarski language-type code. -/
def currentPrimeLanguageUniverseValue :
    (familiesCwF.el familiesValidatedLanguageCode) PUnit.unit :=
  Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation

def quotedCurrentPrimeLanguage : StagedReflectiveTm 0 0 :=
  nativeQuotedLanguage 0 currentPrimeLanguageUniverseValue

theorem quotedCurrentPrimeLanguage_strictly_raises :
    (StagedReflectiveTm.language currentPrimeLanguageUniverseValue :
        StagedReflectiveTm 1 0).reflectiveDepth <
      quotedCurrentPrimeLanguage.reflectiveDepth :=
  nativeQuoteNext_strictly_raises 0 _

/-- Positive bridge witness: the real current Prime presentation, classified
by the Tarski language carrier, round-trips through the single raw quotation
former. -/
theorem quotedCurrentPrimeLanguage_roundtrip :
    quotedCurrentPrimeLanguage.quotedLanguage? =
      some Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation :=
  rfl

/-- Negative fragment witness: ordinary staged code is not misclassified as
a quoted language presentation. -/
theorem quotedPureUniverse_not_quotedLanguage :
    quotedPureUniverse.quotedLanguage? = none :=
  rfl

/-- The Q7 completion package.  Its single operation quotes arbitrary native
terms and specializes to validated languages; positive and negative decoder
laws prevent a vacuous all-language interpretation. -/
structure QuoteCodeUnificationWitness where
  quoteAtNext : ∀ {binders}, (level : Nat) →
    StagedReflectiveTm (level + 1) binders → StagedReflectiveTm level binders
  quoteAtNext_eq : ∀ {binders} (level : Nat)
      (term : StagedReflectiveTm (level + 1) binders),
    quoteAtNext level term = nativeQuoteNext level term
  strictlyRaises : ∀ {binders} (level : Nat)
      (term : StagedReflectiveTm (level + 1) binders),
    term.reflectiveDepth < (quoteAtNext level term).reflectiveDepth
  quoteLanguage : (level : Nat) →
    Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef → StagedReflectiveTm level 0
  languageUsesCommonQuote : ∀ level value,
    quoteLanguage level value =
      quoteAtNext level
        (StagedReflectiveTm.language value : StagedReflectiveTm (level + 1) 0)
  languageRoundtrip : ∀ level value,
    (quoteLanguage level value).quotedLanguage? = some value
  rejectsNonLanguage : quotedPureUniverse.quotedLanguage? = none

def nativeQuoteCodeUnificationWitness : QuoteCodeUnificationWitness where
  quoteAtNext := nativeQuoteNext
  quoteAtNext_eq := by intros; rfl
  strictlyRaises := nativeQuoteNext_strictly_raises
  quoteLanguage := nativeQuotedLanguage
  languageUsesCommonQuote := by intros; rfl
  languageRoundtrip := quotedLanguage?_nativeQuotedLanguage
  rejectsNonLanguage := quotedPureUniverse_not_quotedLanguage

/-- Positive witness: the extension's structural interpretation observes both
the Pure application spine and the quotation node. -/
theorem mixedNativeApplication_node_count :
    nativeNodeCount mixedNativeApplication = 5 := rfl

/-- Unit carrier at every stage, used only as a negative initiality witness. -/
abbrev nativeUnitAlgebra : NativeRawAlgebra where
  atStage := fun _ => pureUnitAlgebra
  pattern := fun _ => PUnit.unit
  empty := PUnit.unit
  superpose := fun _ _ => PUnit.unit
  letE := fun _ _ => PUnit.unit
  language := fun _ => PUnit.unit
  quote := fun _ _ => PUnit.unit

/-- Negative witness: the free native syntax is not terminal.  A homomorphism
from the unit algebra would identify its single element simultaneously with
the distinct `u0` and `u1` constructors. -/
theorem no_unit_to_native_syntax_hom :
    ¬ Nonempty (NativeRawHom nativeUnitAlgebra nativeSyntaxAlgebra) := by
  rintro ⟨hom⟩
  have mapsU0 := (hom.preserves.pure 0).map_u0 (n := 0)
  have mapsU1 := (hom.preserves.pure 0).map_u1 (n := 0)
  have universesEqual : (StagedReflectiveTm.u0 : StagedReflectiveTm 0 0) = .u1 :=
    mapsU0.symm.trans mapsU1
  cases universesEqual

/-- An equality profile is compatible with a native algebra at one stage when
the stage's Pure fold identifies every equation in that profile.  This keeps
optional extensions explicit rather than selecting one in raw syntax. -/
def NativeRawAlgebra.CompatibleWithPureProfileAt
    (target : NativeRawAlgebra.{uRawTarget}) (stage : Nat)
    (profile : PureEqualityProfile) : Prop :=
  ∀ {binders} {left right : PureTm binders}, profile.Rel left right →
    pureRawFold (target.atStage stage) left =
      pureRawFold (target.atStage stage) right

/-- Folding the embedded Pure fragment through a native algebra agrees with
the ordinary Pure fold into that stage. -/
theorem nativeRawFold_embedPure
    (target : NativeRawAlgebra.{uRawTarget}) (stage : Nat)
    {binders : Nat} (term : PureTm binders) :
    nativeRawFold target (embedPure stage term) =
      pureRawFold (target.atStage stage) term := by
  induction term with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH => simp [embedPure, pureRawFold,
      nativeRawFold, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH => simp [embedPure, pureRawFold,
      nativeRawFold, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH => simp [embedPure, pureRawFold,
      nativeRawFold, typeIH, leftIH, rightIH]
  | lam body bodyIH => simp [embedPure, pureRawFold, nativeRawFold, bodyIH]
  | app function argument functionIH argumentIH => simp [embedPure, pureRawFold,
      nativeRawFold, functionIH, argumentIH]
  | pair left right leftIH rightIH => simp [embedPure, pureRawFold,
      nativeRawFold, leftIH, rightIH]
  | fst pair pairIH => simp [embedPure, pureRawFold, nativeRawFold, pairIH]
  | snd pair pairIH => simp [embedPure, pureRawFold, nativeRawFold, pairIH]
  | refl term termIH => simp [embedPure, pureRawFold, nativeRawFold, termIH]

/-- Positive equality-neutral point: the free native syntax accepts the finest
syntactic Pure equality profile at every stage. -/
theorem nativeSyntax_compatible_syntactic (stage : Nat) :
    nativeSyntaxAlgebra.CompatibleWithPureProfileAt stage
      syntacticEqualityProfile := by
  intro binders left right equal
  have termsEqual := (syntacticEqualityProfile_rel_iff left right).mp equal
  subst right
  rfl

/-- Negative equality witness: a profile collapsing the two Pure universes
cannot be interpreted by the free native syntax at any stage. -/
theorem nativeSyntax_incompatible_with_universe_collapse
    (stage : Nat) (profile : PureEqualityProfile)
    (collapses : profile.Rel (PureTm.u0 : PureTm 0) PureTm.u1) :
    ¬ nativeSyntaxAlgebra.CompatibleWithPureProfileAt stage profile := by
  intro compatible
  have equalUniverses := compatible collapses
  change (StagedReflectiveTm.u0 : StagedReflectiveTm stage 0) = .u1 at equalUniverses
  cases equalUniverses

/-! ## §8 The candidate and its audit -/

/-- A candidate native type theory: a mode theory with its spine. -/
structure TypeTheoryCandidate where
  modes : ModeTheory
  spine : ModalCwF modes
  laws : ModalCwFLaws modes spine
  coherence : ModalCwFCoherence modes spine laws
  ConversionTerm : Type
  Converts : ConversionTerm → ConversionTerm → Prop
  conversion : Mettapedia.GSLT.LanguageDef.NIKMetalogic.DecidedRelation
    ConversionTerm Converts

/-- The concrete law-complete semantic candidate with executable intensional
conversion. -/
def familiesCandidate : TypeTheoryCandidate where
  modes := stageModeTheory
  spine := familiesCwF
  laws := familiesCwFLaws
  coherence := familiesCwFCoherence
  ConversionTerm := NativeConversionTerm
  Converts := NativeConverts
  conversion := nativeDecidedConversion

/-- The full audit: one witness per forced requirement.  An inhabitant of
this structure is a candidate that satisfies every requirement forced by the
family bags — the derivation target. -/
structure NativeTheoryAudit (cand : TypeTheoryCandidate) where
  equality : NativeEqualityArchitecture
  spaceModel : SpaceModel cand.modes cand.spine
  spaceCode : SpaceCodeWitness cand.modes cand.spine spaceModel
  quotation : QuotationWitness cand.modes cand.spine
  contextualBox : ContextualBoxWitness cand.modes cand.spine quotation
  levels : LevelWitness cand.modes
  grading : GradingWitness cand.modes
  evidence : EvidenceFibration cand.modes cand.spine
  InterfaceClaim : Type
  interface : SuccessInterface InterfaceClaim
  dependentFamilies : DependentFamilyWitness cand.modes cand.spine
  identityTypes : IdentityTypeWitness cand.modes cand.spine
  inductiveFamilies : BinaryInductiveFamilyWitness cand.modes cand.spine
  languageCodes : LanguageCodeWitness cand.modes cand.spine spaceModel
  universeTower : StratifiedUniverseWitness cand.modes cand.spine
  directTyping : DirectPatternTypingWitness
  authorityParity : NativeAuthorityParityWitness directTyping
  proofFlow : PrimeNeedProofFlow.NativeProofFlowWitness

/-- The concrete families candidate satisfies every descriptive and
normative requirement currently independent of the equality-profile choice.
Each field points to a separately constructed witness with its own positive
and negative/noncollapse theorem. -/
def familiesNativeTheoryAudit : NativeTheoryAudit familiesCandidate where
  equality := selectedNativeEqualityArchitecture
  spaceModel := familiesPatternSpaceModel
  spaceCode := familiesSpaceCodeWitness
  quotation := familiesQuotationWitness
  contextualBox := familiesContextualBoxWitness
  levels := stageLevelWitness
  grading := nativeGradingWitness
  evidence := nativeEvidenceFibration
  InterfaceClaim := HESuccessClaim
  interface := heSuccessInterface
  dependentFamilies := familiesDependentFamilyWitness
  identityTypes := familiesIdentityTypes
  inductiveFamilies := familiesBooleanInductive
  languageCodes := familiesLanguageCodeWitness
  universeTower := familiesUniverseTower
  directTyping := fastDirectPatternTypingWitness
  authorityParity := fastNativeAuthorityParityWitness
  proofFlow := PrimeNeedProofFlow.nativeProofFlowWitness

/-! ## §9 Parity: the theory is an authority from birth

The derived theory's checker must be measured against an independently given
judgment — the same square every hosted guest owes.  Stated generically here
so the native theory carries the obligation from its first day rather than
retrofitting it. -/

/-- The guest proof system is the generic NIK proof-object boundary, not a
second native-theory-specific definition. -/
abbrev GuestKernelSpec (Claim : Type uNativeClaim) :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofSystem.{
    uNativeClaim, uNativeProof} Claim

/-- Primary parity preserves the entire accepted/native proof fibre.  This is
strictly stronger than decode-only parity and rules out ignored proof tags. -/
abbrev KernelParity {Claim : Type uNativeClaim}
    {Certificate : Type uNativeCertificate}
    (checker : Checker Claim Certificate) (guest : GuestKernelSpec Claim) :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.CertificateEquivalence checker guest

/-- A computing realization checks native proof objects directly. -/
abbrev ComputingRealization {Claim : Type uNativeClaim}
    (guest : GuestKernelSpec Claim) :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofKernel guest

/-- A decided relation is shared with the generic NIK metalogic.  The native
theory's conversion relation owes an instance of this exact interface. -/
abbrev DecidedRelation {α : Type} (R : α → α → Prop) :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.DecidedRelation α R

/-! ## §10 The derived native theory -/

/-- The assembled derivation target.  The direct operational typing judgment
and its exact parity square are already dependently coupled inside `audit`;
there is no second unconstrained checker field that could describe a different
logic.  The full proof-relevant modal judgment remains available separately as
`nativeTypingEvidenceDoctrine`, without pretending that its entire calculus
has acquired an executable decision procedure. -/
structure DerivedNativeTheory where
  candidate : TypeTheoryCandidate
  audit : NativeTheoryAudit candidate

namespace DerivedNativeTheory

/-- The primary checker is an exact authority for inhabitation of the native
proof judgment. -/
theorem primaryAuthority (theory : DerivedNativeTheory) :
    theory.audit.directTyping.kernel.toChecker.Authority
      (fun claim =>
        Nonempty (theory.audit.authorityParity.guest.ProofFibre claim)) :=
  theory.audit.authorityParity.parity.authority

/-- The primary certificate fibre and the direct computing kernel's accepted
fibre are equivalent through the native proof fibre.  This is the precise
parity square; it does not identify the two certificate languages. -/
def primaryToNativeKernel
    (theory : DerivedNativeTheory) (claim : PatternTypingClaim) :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.AcceptedCertificateFibre
        theory.audit.directTyping.kernel.toChecker claim ≃
      Mettapedia.GSLT.LanguageDef.NIKMetalogic.AcceptedCertificateFibre
        theory.audit.authorityParity.nativeKernel.toChecker claim :=
  (theory.audit.authorityParity.parity.fibreEquiv claim).trans
    (theory.audit.authorityParity.nativeKernel.certificateEquivalence.fibreEquiv
      claim).symm

/-- The proof-relevant native modal judgment is part of every assembled
theory as the fixed contextual evidence doctrine over `NativeTypingClaim`.
This exposes proofs as native data without conflating that tier with the
decidable Pattern fragment above. -/
def proofDoctrine (_theory : DerivedNativeTheory) :=
  nativeTypingEvidenceDoctrine

end DerivedNativeTheory

/-- The concrete law-complete candidate, its nondegenerate audit, and its
exact direct-typing parity square form one inhabitant of the assembled target. -/
def familiesDerivedNativeTheory : DerivedNativeTheory where
  candidate := familiesCandidate
  audit := familiesNativeTheoryAudit

/-- Positive crown witness: the assembled theory's primary checker accepts a
real unknown-typed Pattern claim. -/
theorem familiesDerivedNativeTheory_primary_positive :
    familiesDerivedNativeTheory.audit.directTyping.kernel.toChecker.check
      ⟨Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty, .bvar 0,
        Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩ () = true :=
  fastPatternTyping_unknown_positive _ _

/-- Negative crown witness: assembly does not turn the direct typing boundary
into an always-accepting facade. -/
theorem familiesDerivedNativeTheory_primary_negative :
    familiesDerivedNativeTheory.audit.directTyping.kernel.toChecker.check
      fastPatternTypingRejected () = false :=
  fastPatternTyping_unsupported_negative

/-! ## §11 Open obligations

The typed ledger names theorem-level gaps that are not discharged by the
families-model witness bundle or by rule-algebra initiality.  The count and
duplicate check make accidental emptying or repeated bookkeeping visible.
An entry may be removed only in the same change that supplies its theorem and
connects that theorem to the assembled theory. -/

/-- Unresolved theorem boundaries in the native theory and its GSLT-IL
interpretation. -/
inductive OpenObligation where
  /-- Authored typing needs initiality/adequacy in semantic modal CwFs, not
  merely in rule algebras carrying the same operations. -/
  | semanticCwFInitiality
  /-- Interpretation kernels now derive raw congruence and renaming from
  substitution naturality.  The remaining typed rule regularity must likewise
  be forced by the semantic CwF model rather than supplied through a duplicate
  `TypingAlgebra`. -/
  | modelForcedRegularity
  /-- Generated operational judgments need a two-way adequacy theorem with the
  independently authored typing judgment on their stated fragment. -/
  | operationalTypingAdequacy
  /-- The exact returned-fibre theorem must be extended to full command syntax
  only after typed transport, substitution, cell coherence, and the universal
  factorization premises have been supplied. -/
  | fullCommandInternalLanguage
  /-- Beyond the finite eight-row conformance authority, the complete native
  judgment needs a sound, evidence-bearing executable authority over encoded
  syntax that is complete on a named fragment and abstains outside it. -/
  | executableNativeAuthority
deriving DecidableEq, Repr

/-- Human-readable statement of each machine-visible obligation. -/
def OpenObligation.description : OpenObligation → String
  | .semanticCwFInitiality =>
      "authored typing is initial and adequate in semantic modal CwFs"
  | .modelForcedRegularity =>
      "semantic CwF structure forces the remaining typed rule regularity"
  | .operationalTypingAdequacy =>
      "generated operational judgments agree with authored typing"
  | .fullCommandInternalLanguage =>
      "the internal-language theorem extends from the returned image to full commands"
  | .executableNativeAuthority =>
      "encoded native syntax has an evidence-bearing checker beyond the finite conformance image"

def openObligations : List OpenObligation :=
  [.semanticCwFInitiality,
    .modelForcedRegularity,
    .operationalTypingAdequacy,
    .fullCommandInternalLanguage,
    .executableNativeAuthority]

/-- Pinned obligation count: update together with the typed ledger. -/
theorem openObligations_count : openObligations.length = 5 := rfl

/-- Each open boundary occurs exactly once in the ledger. -/
theorem openObligations_nodup : openObligations.Nodup := by decide

/-- The assembled witness bundle is not the completed native theory. -/
theorem openObligations_nonempty : openObligations ≠ [] := by decide

/-! ## Axiom audit -/

#print axioms commitmentForces_injective
#print axioms commitments_extend_observations
#print axioms Space.sub_trans
#print axioms openObligations_count
#print axioms openObligations_nodup
#print axioms openObligations_nonempty
#print axioms DerivedNativeTheory.primaryAuthority
#print axioms familiesDerivedNativeTheory_primary_positive
#print axioms familiesDerivedNativeTheory_primary_negative
#print axioms StratifiedUniverseWitness.no_constant_mode
#print axioms FamiliesCwF.app_lam
#print axioms FamiliesCwF.lam_app
#print axioms familiesPiStructure
#print axioms familiesCwFLaws
#print axioms familiesCwFCoherence
#print axioms familiesCwF_sext_unique
#print axioms nonterminal_empty_substitutions_distinct
#print axioms basic_modal_cwf_laws_do_not_force_coherence
#print axioms familiesPatternOutside_ne_marker
#print axioms familiesRuntimePatternCode_decodes
#print axioms LanguageCodeWitness.isLanguagePattern_iff_decode_ne_none
#print axioms LanguageCodeWitness.image_proper
#print axioms familiesValidatedLanguageCode_decodes
#print axioms currentZeroPresentation_ne_currentPrimePresentation
#print axioms currentLanguagePresentation_injective
#print axioms decodeCurrentLanguagePattern_encode
#print axioms currentLanguagePattern_decode
#print axioms familiesLanguageCodeWitness
#print axioms currentPrimePattern_is_languagePattern
#print axioms outsideCurrentLanguagePattern_not_languagePattern
#print axioms currentZeroToPrime_maps_equationConstructor
#print axioms nativeLanguageManipulationWitness
#print axioms lambdaPiToLF_injective
#print axioms lambdaPiToLF_subst
#print axioms lambdaPiDecidedConversion
#print axioms lambdaPi_conversion_commutes
#print axioms lambdaPi_decision_sound
#print axioms lambdaPi_beta_positive
#print axioms lambdaPi_eta_positive
#print axioms lambdaPi_unrelated_negative
#print axioms nativeDecidedConversion
#print axioms nativeConversion_lambdaPi_agrees
#print axioms nativeConversion_beta_positive
#print axioms nativeConversion_code_pattern_negative
#print axioms nativeGradingWitness
#print axioms nativeEvidenceFibration
#print axioms nativeEvidence_reindex_separates
#print axioms heSuccessDecide_sound
#print axioms heSuccessInterface_positive
#print axioms heSuccessInterface_negative
#print axioms pettaSuccessDecide_sound
#print axioms pettaSuccessInterface_positive
#print axioms pettaSuccessInterface_negative
#print axioms fastPatternTypingBool_correct
#print axioms FastPatternTyping.language_sound
#print axioms fast_pattern_typing_correct_by_construction
#print axioms fastPatternTyping_authority
#print axioms fastPatternTyping_certificate_irrelevant
#print axioms fastPatternTyping_unknown_positive
#print axioms fastPatternTyping_unsupported_negative
#print axioms fastDirectPatternTypingWitness
#print axioms FastPatternParity.nativeKernel
#print axioms FastPatternParity.certificateEquivalence
#print axioms FastPatternParity.authority
#print axioms FastPatternParity.computes_directly
#print axioms FastPatternParity.proofFibre_subsingleton
#print axioms FastPatternParity.no_tagged_certificateEquivalence
#print axioms fastNativeAuthorityParityWitness
#print axioms PrimeNeedProofFlow.step_sound
#print axioms PrimeNeedProofFlow.applyAdmitted_eq_advance
#print axioms PrimeNeedProofFlow.applyAdmitted_sound
#print axioms PrimeNeedProofFlow.request_meaning
#print axioms PrimeNeedProofFlow.found_flows_without_recheck
#print axioms PrimeNeedProofFlow.primaryBoundary
#print axioms PrimeNeedProofFlow.found_reaches_primary_boundary
#print axioms PrimeNeedProofFlow.answer_has_no_admitted_successor
#print axioms PrimeNeedProofFlow.answer_key_changes_with_revision
#print axioms PrimeNeedProofFlow.nativeProofFlowWitness
#print axioms PrimeGSLTILReturnedFibre.stepEquiv
#print axioms PrimeGSLTILReturnedFibre.fromReturned_toReturned
#print axioms PrimeGSLTILReturnedFibre.toReturned_fromReturned
#print axioms PrimeGSLTILReturnedFibre.cloneEquivalence
#print axioms PrimeGSLTILReturnedFibre.admission_square_commutes
#print axioms PrimeGSLTILReturnedFibre.pendingClaim_not_encoded
#print axioms PrimeGSLTILReturnedFibre.witness
#print axioms familiesIdentityFormation
#print axioms familiesIdentityTypes
#print axioms familiesIdentityTypes_beta
#print axioms familiesIdentity_false_true_empty
#print axioms familiesBooleanInductive
#print axioms familiesBooleanInductive_beta_left
#print axioms familiesBooleanInductive_not_collapsed
#print axioms familiesUniverseLowerContract_target
#print axioms firstUniverseLowerContracts_distinct
#print axioms reflectiveCodeIter_add
#print axioms familiesQuotationWitness
#print axioms familiesQuotation_code_inhabited
#print axioms familiesQuotation_object_empty
#print axioms stageLevelWitness
#print axioms familiesContextualBoxWitness
#print axioms familiesQuotationTerms
#print axioms familiesQuotationTermsSome
#print axioms familiesQuotationTerms_unit_depth_one
#print axioms bare_modal_cwf_does_not_determine_quotation
#print axioms PureRawHom.ext
#print axioms PureRawHom.id_comp
#print axioms PureRawHom.comp_id
#print axioms PureRawHom.comp_assoc
#print axioms pureRawFold_unique_pointwise
#print axioms pureRawFold_unique
#print axioms pureNodeCount_betaShape_positive
#print axioms no_unit_to_pure_syntax_hom
#print axioms PureEqualityProfile.rename_closed
#print axioms PureRawHom.kernelProfile
#print axioms syntacticEqualityProfile_rel_iff
#print axioms substitutionUnstablePureHom_has_no_substitution_action
#print axioms PureEqualityProfile.rename_mk
#print axioms PureEqualityProfile.substRaw_mk
#print axioms PureEqualityProfile.substRaw_ids
#print axioms PureEqualityProfile.substRaw_comp
#print axioms PureEqualityProfile.quotientMap_mk
#print axioms pureProfileQuotientHom_respects
#print axioms intrinsicPureConv_map
#print axioms intrinsicPureConv_congr_pi
#print axioms intrinsicPureConv_congr_sigma
#print axioms intrinsicPureConv_congr_id
#print axioms intrinsicPureConv_congr_lam
#print axioms intrinsicPureConv_congr_app
#print axioms intrinsicPureConv_congr_pair
#print axioms intrinsicPureConv_congr_fst
#print axioms intrinsicPureConv_congr_snd
#print axioms intrinsicPureConv_congr_refl
#print axioms intrinsicPureConv_subst_pointwise
#print axioms intrinsicPureConv_subst_congr
#print axioms intrinsicPureConversionProfile_beta
#print axioms intrinsicPureProfile_beta_quotient
#print axioms syntacticProfile_u0_ne_u1
#print axioms syntacticEqualityProfile_finer
#print axioms intrinsicPureProfile_not_finer_than_syntactic
#print axioms profile_equating_universes_blocks_identity
#print axioms profile_equating_universes_not_finer_than_syntactic
#print axioms PureRawHom.factorThroughProfile_comp_projection
#print axioms PureRawHom.factorThroughProfile_unique
#print axioms nativeRawFold_unique_pointwise
#print axioms NativeRawHom.ext
#print axioms nativeRawFold_unique
#print axioms pureProjection_embedPure
#print axioms embedPure_injective
#print axioms embedPure_eq_iff
#print axioms quotedPureUniverse_not_in_pure_image
#print axioms mixedNativeApplication_not_in_pure_image
#print axioms pureProjection_none_not_in_pure_image
#print axioms nativeRuntimePattern_not_in_pure_image
#print axioms nativeUniverseSuperposition_not_in_pure_image
#print axioms nativeCurrentPrimeLanguage_not_in_pure_image
#print axioms IntrinsicPureRefinement.ctxMor_ids
#print axioms IntrinsicPureRefinement.ctxMor_comp
#print axioms IntrinsicPureRefinement.embedPureSub_comp
#print axioms IntrinsicPureRefinement.toNativeSupport_map_injective
#print axioms IntrinsicPureRefinement.typingAt_embed_iff
#print axioms IntrinsicPureRefinement.TypingAt.subst
#print axioms IntrinsicPureRefinement.TypingAt.contextConv
#print axioms IntrinsicPureRefinement.oneUniverseContext_identity_maps_to_native_identity
#print axioms IntrinsicPureRefinement.stageSensitiveEndSub_has_no_typedPure_preimage
#print axioms IntrinsicPureRefinement.quotedPureUniverse_has_no_intrinsic_typing
#print axioms NativeModalTyping.Context.lookup_lock
#print axioms NativeModalTyping.Context.lock_ne_unlocked
#print axioms NativeModalTyping.subst0_rename_wk
#print axioms NativeModalTyping.subst_inst0
#print axioms NativeModalTyping.rename_inst0
#print axioms NativeModalTyping.ContextRen.snoc
#print axioms NativeModalTyping.ContextRen.lock
#print axioms NativeModalTyping.primitiveLet_has_native_modal_type
#print axioms NativeModalTyping.primitiveLet_typable_but_not_syntactically_inlined
#print axioms NativeModalTyping.typing_rename
#print axioms NativeModalTyping.weakening
#print axioms NativeModalTyping.ContextMor.lift
#print axioms NativeModalTyping.ContextMor.lock
#print axioms NativeModalTyping.typing_subst
#print axioms NativeModalTyping.ContextMor.ids
#print axioms NativeModalTyping.ContextMor.comp
#print axioms NativeModalTyping.TypedSub.ext
#print axioms NativeModalTyping.toNativeSupport_map_injective
#print axioms NativeModalTyping.lookup_embedPureContext
#print axioms NativeModalTyping.subst0_embedPure
#print axioms NativeModalTyping.inst0_embedPure
#print axioms NativeModalTyping.inst0_fst_embedPure
#print axioms NativeModalTyping.typing_embedPure
#print axioms NativeModalTyping.syntacticConversion_does_not_extend_intrinsicPure
#print axioms NativeModalTyping.quotedPureUniverse_has_native_modal_type
#print axioms NativeModalTyping.quotation_typing_separates_native_from_intrinsic
#print axioms NativeModalTyping.ConversionPolicy.extends_syntactic
#print axioms NativeModalTyping.HasType.of_conversion_extension
#print axioms NativeModalTyping.HasType.of_syntactic
#print axioms NativeTypedInitiality.fold_typing
#print axioms NativeTypedInitiality.contextMap_unique
#print axioms NativeTypedInitiality.interpretations_agree
#print axioms NativeTypedInitiality.Interpretation.ext
#print axioms NativeTypedInitiality.initiality
#print axioms NativeTypedInitiality.interpretation_unique
#print axioms NativeTypedInitiality.universe_has_image
#print axioms NativeTypedInitiality.no_empty_judgment_model
#print axioms NativeTypedInitiality.quoted_universe_has_image
#print axioms runtimePattern?_embedRuntimePattern
#print axioms embedRuntimePattern_injective
#print axioms runtimePattern_image_iff
#print axioms currentPrimeReflectedDemandProgram_roundtrip
#print axioms quotedPureUniverse_not_runtimePattern_image
#print axioms oneToZeroQuotation_cost_nonzero
#print axioms cost_decoration_is_external_and_nondegenerate
#print axioms evidence_decoration_is_external_and_nondegenerate
#print axioms mixedNativeApplication_node_count
#print axioms nativeNodeCount_positive
#print axioms NativeTypedInitiality.nodeCount_primitiveLet_image
#print axioms NativeTypedInitiality.nodeCount_model_separates_let_from_inlining
#print axioms NativeTypedInitiality.nodeCount_interpretation_exists
#print axioms familiesDependentFamilyWitness
#print axioms familiesNativeTheoryAudit
#print axioms no_unit_to_native_syntax_hom
#print axioms nativeRawFold_embedPure
#print axioms nativeSyntax_compatible_syntactic
#print axioms nativeSyntax_incompatible_with_universe_collapse
#print axioms nativeLiftRen_id
#print axioms nativeLiftRen_eq_pureLiftRen
#print axioms nativeLiftRen_comp_apply
#print axioms nativeRename_ext
#print axioms nativeRename_id
#print axioms nativeRename_comp
#print axioms nativeLiftSub_ext
#print axioms nativeSubst_ext
#print axioms nativeLiftSub_ids
#print axioms nativeSubst_ids
#print axioms nativeLiftSubOfRen
#print axioms nativeSubst_ofRen
#print axioms nativeSubst_quote
#print axioms nativeRename_liftSub
#print axioms nativeRename_subst
#print axioms nativeLiftSub_liftRen_apply
#print axioms nativeSubst_rename
#print axioms nativeSubst_liftSub_wk
#print axioms nativeLiftSubComp_apply
#print axioms nativeSubst_comp
#print axioms nativeSubComp_left_id
#print axioms nativeSubComp_right_id
#print axioms nativeSubComp_assoc
#print axioms nativeConsSub_zero
#print axioms nativeConsSub_succ
#print axioms nativeInlineLet_var_zero
#print axioms nativeLet_is_primitive_before_inlining
#print axioms nativeRename_embedPure
#print axioms nativeLiftSub_embedPureSub
#print axioms nativeSubst_embedPure
#print axioms stageSensitiveSub_zero_component
#print axioms stageSensitiveSub_one_component
#print axioms stageSensitiveSub_unquoted
#print axioms stageSensitiveSub_quoted
#print axioms stageSensitiveSub_not_projection_constant
#print axioms NativeDecoratedTm.reindex_term
#print axioms NativeDecoratedTm.reindex_account
#print axioms NativeDecoratedTm.reindex_evidence
#print axioms NativeDecoratedTm.reindex_ids
#print axioms NativeDecoratedTm.reindex_comp
#print axioms nativeBoolObservation_rename
#print axioms nativeBoolObservation_rename_wk
#print axioms nativeBoolObservation_subst
#print axioms nativeBooleanEqualityProfile_validates_letInlining
#print axioms nativeBooleanEqualityProfile_separates_universes
#print axioms nativeSyntacticEqualityProfile_rejects_letInlining
#print axioms nativeBooleanConversion_extends_syntactic
#print axioms syntacticConversion_does_not_extend_nativeBoolean
#print axioms primitiveLet_typing_enters_nativeBoolean
#print axioms nativeBoolean_is_strict_nondegenerate_typing_extension
#print axioms NativeModalTyping.ConversionPolicy.extends_refl
#print axioms NativeModalTyping.ConversionPolicy.extends_trans
#print axioms NativeEqualityArchitecture.transport
#print axioms NativeEqualityArchitecture.strictExtension_ne_core
#print axioms selectedEquality_calibration_does_not_alias_core
#print axioms selectedEquality_has_no_stronger_production_profile
#print axioms selectedEquality_core_is_initial
#print axioms selectedEquality_transports_primitiveLet
#print axioms nativeLiftCostEnvironment_rename
#print axioms nativeGradedCost_rename
#print axioms nativeLiftCostEnvironment_subst
#print axioms nativeGradedCost_subst
#print axioms nativeLet_structural_cost
#print axioms nativeInlineLet_structural_cost
#print axioms graded_cost_not_profile_invariant
#print axioms nativeBoolean_cost_does_not_factor
#print axioms NativeDerivationCountBag.truthSet_galois
#print axioms NativeDerivationCountBag.truthSet_ofTruthSet
#print axioms NativeDerivationCountBag.ofTruthSet_truthSet_le
#print axioms NativeDerivationBag.truthSet_eq_count_truthSet
#print axioms NativeDerivationBag.singleton_at
#print axioms nativeTypingProofErasureAdjunction
#print axioms nativeTypingEvidence_not_subsingleton
#print axioms primitiveLetTypingClaim_in_erased_consequence
#print axioms nativeTyping_toThinReflection_not_injective
#print axioms primitiveLetEvidenceBags_same_truth
#print axioms primitiveLetEvidenceBagOne_strength
#print axioms primitiveLetEvidenceBagTwo_strength
#print axioms primitiveLetEvidenceBags_distinct
#print axioms nativeEvidence_strength_does_not_factor_through_truth
#print axioms no_reverse_adjacent_stage
#print axioms StagedReflectiveTm.reflectiveDepth_quote
#print axioms StagedReflectiveTm.quote_strictly_raises_reflectiveDepth
#print axioms nativeQuoteNext_reflectiveDepth
#print axioms nativeQuoteNext_strictly_raises
#print axioms quotedLanguage?_nativeQuotedLanguage
#print axioms nativeQuotedLanguage_has_type
#print axioms quotedCurrentPrimeLanguage_strictly_raises
#print axioms quotedCurrentPrimeLanguage_roundtrip
#print axioms quotedPureUniverse_not_quotedLanguage
#print axioms nativeQuoteCodeUnificationWitness

end Mettapedia.Languages.MeTTa.StagedReflective
