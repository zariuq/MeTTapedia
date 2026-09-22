import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.GSLT.LanguageDef.LF.PureCorrespondence
import Mettapedia.GSLT.Dynamics.WeightCost
import Mettapedia.PLN.Evidence.BinEvNat
import Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
import Mettapedia.TypeTheory.ModalCwF

/-!
# Staged scoped reflection with an explicit intensional equality policy

This named calculus and its models were developed alongside a MeTTa-family
experiment. Their laws concern the displayed syntax and semantic structures,
not a selected Prime language or the behavior of HE or PeTTa. Dialect profiles,
direct dialect judgments and their assembly remain separate adapters.
-/

set_option autoImplicit true
namespace Mettapedia.TypeTheory.Calculi.StagedScopedReflective
universe uNativeClaim uNativeCertificate uNativeProof uRaw uRawTarget
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.GSLT.LanguageDef.KernelAuthority (Checker)
open Mettapedia.TypeTheory
/-! ## §3–§4 General modal CwF interface

The reusable mode theory, cost grading, contextual multimodal CwF laws,
dependent-product structure, and term-level quotation interface live in
`Mettapedia.TypeTheory.ModalCwF`.  This module supplies MeTTa-family models
and selected capability contracts without making those general definitions
language-specific. -/

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
theorem familiesCwFCoherence :
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
  f := ⟨Nat.zero_le 1, 0⟩
  nontrivial := by
    intro zeroCost
    have firstCoordinate := congrFun zeroCost (0 : Fin 2)
    change (1 : Nat) - 0 = 0 at firstCoordinate
    omega

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

/-! ## §6d Revisioned occurrence proof flow

Admitted revisioned-occurrence derivations are defined independently in
`Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow`.  They consume an
occurrence source and a revision-keying policy, not a selected candidate
assembly.  Their exact returned-command comparison is developed separately in
`Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre`. -/

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

Witnesses for the capability contracts selected by the normative channel.
Their stated laws and noncollapse conditions, not the classification table,
specify what each construction establishes. -/

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



end Mettapedia.TypeTheory.Calculi.StagedScopedReflective
