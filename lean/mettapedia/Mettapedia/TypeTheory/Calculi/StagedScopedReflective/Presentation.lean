import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.Model

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
/-! ### Executable λΠ fragment inside the universe

The existing universe-free λΠ carrier is a first-class code in the
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
universe codes, and runtime Patterns.  This staged-reflective candidate's
equality architecture below uses an intensional kernel core.  It does not
determine the family's equality architecture or identify this core with
observational equality, UIP, cubical structure, or univalence; such relations
require separately named extension profiles. -/

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
  refine (nativeDecidedConversion.correct (.lambdaPi left) (.lambdaPi right)).trans
    (Iff.trans ?_ (lambdaPiDecidedConversion.correct left right).symm)
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

/-! ## §7c Equality-neutral recursion for the scoped two-sort syntax

Full initiality among semantic `ModalCwF` models is not proved here.  The raw
binding signature is independent of conversion, however.  This section proves
its genuine recursion and uniqueness theorem, including the binder-indexed
operations.  It is therefore an initiality precursor rather than a disguised
semantic self-model.

The algebra deliberately contains every live `ScopedTerm` constructor, including
global constants, dependent products, dependent sums, and identity terms. -/

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax

/-- An algebra for the complete raw, intrinsically scoped two-sort signature. -/
structure TwoSortRawAlgebra where
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

/-- Preservation of the complete raw two-sort signature by an indexed map. -/
structure TwoSortRawPreserves
    (source : TwoSortRawAlgebra.{uRaw})
    (target : TwoSortRawAlgebra.{uRawTarget})
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

/-- A homomorphism of raw two-sort algebras. -/
structure TwoSortRawHom
    (source : TwoSortRawAlgebra.{uRaw})
    (target : TwoSortRawAlgebra.{uRawTarget}) where
  map : {n : Nat} → source.Carrier n → target.Carrier n
  preserves : TwoSortRawPreserves source target map

namespace TwoSortRawHom

/-- Identity interpretation of a raw two-sort algebra. -/
def id (algebra : TwoSortRawAlgebra.{uRaw}) : TwoSortRawHom algebra algebra where
  map := fun term => term
  preserves := by
    constructor <;> intros <;> rfl

/-- Composition of raw two-sort-algebra interpretations. -/
def comp
    {first : TwoSortRawAlgebra.{uRaw}}
    {middle : TwoSortRawAlgebra.{uRawTarget}}
    {last : TwoSortRawAlgebra.{uNativeClaim}}
    (earlier : TwoSortRawHom first middle)
    (later : TwoSortRawHom middle last) :
    TwoSortRawHom first last where
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

end TwoSortRawHom

@[ext] theorem TwoSortRawHom.ext
    {source : TwoSortRawAlgebra.{uRaw}}
    {target : TwoSortRawAlgebra.{uRawTarget}}
    (left right : TwoSortRawHom source target)
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

@[simp] theorem TwoSortRawHom.id_comp
    {source : TwoSortRawAlgebra.{uRaw}}
    {target : TwoSortRawAlgebra.{uRawTarget}}
    (hom : TwoSortRawHom source target) :
    TwoSortRawHom.comp (TwoSortRawHom.id source) hom = hom := by
  apply TwoSortRawHom.ext
  intro n term
  rfl

@[simp] theorem TwoSortRawHom.comp_id
    {source : TwoSortRawAlgebra.{uRaw}}
    {target : TwoSortRawAlgebra.{uRawTarget}}
    (hom : TwoSortRawHom source target) :
    TwoSortRawHom.comp hom (TwoSortRawHom.id target) = hom := by
  apply TwoSortRawHom.ext
  intro n term
  rfl

theorem TwoSortRawHom.comp_assoc
    {first : TwoSortRawAlgebra.{uRaw}}
    {second : TwoSortRawAlgebra.{uRawTarget}}
    {third : TwoSortRawAlgebra.{uNativeClaim}}
    {fourth : TwoSortRawAlgebra.{uNativeProof}}
    (firstHom : TwoSortRawHom first second)
    (secondHom : TwoSortRawHom second third)
    (thirdHom : TwoSortRawHom third fourth) :
    TwoSortRawHom.comp (TwoSortRawHom.comp firstHom secondHom) thirdHom =
      TwoSortRawHom.comp firstHom (TwoSortRawHom.comp secondHom thirdHom) := by
  apply TwoSortRawHom.ext
  intro n term
  rfl

/-- The live scoped two-sort syntax as an algebra of its raw signature. -/
def twoSortSyntaxAlgebra : TwoSortRawAlgebra where
  Carrier := ScopedTerm
  var := ScopedTerm.var
  const := ScopedTerm.const
  u0 := ScopedTerm.u0
  u1 := ScopedTerm.u1
  pi := ScopedTerm.pi
  sigma := ScopedTerm.sigma
  id := ScopedTerm.id
  lam := ScopedTerm.lam
  app := ScopedTerm.app
  pair := ScopedTerm.pair
  fst := ScopedTerm.fst
  snd := ScopedTerm.snd
  refl := ScopedTerm.refl

/-- Structural interpretation of scoped two-sort syntax in any raw algebra. -/
def twoSortRawFold (target : TwoSortRawAlgebra.{uRawTarget}) :
    {n : Nat} → ScopedTerm n → target.Carrier n
  | _, .var index => target.var index
  | _, .const name => target.const name
  | _, .u0 => target.u0
  | _, .u1 => target.u1
  | _, .pi domain body =>
      target.pi (twoSortRawFold target domain) (twoSortRawFold target body)
  | _, .sigma domain body =>
      target.sigma (twoSortRawFold target domain) (twoSortRawFold target body)
  | _, .id type left right =>
      target.id (twoSortRawFold target type) (twoSortRawFold target left)
        (twoSortRawFold target right)
  | _, .lam body => target.lam (twoSortRawFold target body)
  | _, .app function argument =>
      target.app (twoSortRawFold target function) (twoSortRawFold target argument)
  | _, .pair left right =>
      target.pair (twoSortRawFold target left) (twoSortRawFold target right)
  | _, .fst pair => target.fst (twoSortRawFold target pair)
  | _, .snd pair => target.snd (twoSortRawFold target pair)
  | _, .refl term => target.refl (twoSortRawFold target term)

/-- The structural fold is a raw two-sort-algebra homomorphism. -/
def twoSortRawFoldHom (target : TwoSortRawAlgebra.{uRawTarget}) :
    TwoSortRawHom twoSortSyntaxAlgebra target where
  map := twoSortRawFold target
  preserves := by
    constructor <;> intros <;> rfl

/-- Any raw two-sort-algebra homomorphism agrees pointwise with structural fold. -/
theorem twoSortRawFold_unique_pointwise
    (target : TwoSortRawAlgebra.{uRawTarget})
    (hom : TwoSortRawHom twoSortSyntaxAlgebra target) :
    ∀ {n} (term : ScopedTerm n), hom.map term = twoSortRawFold target term := by
  intro n term
  induction term with
  | var index => exact hom.preserves.map_var index
  | const name => exact hom.preserves.map_const name
  | u0 => exact hom.preserves.map_u0
  | u1 => exact hom.preserves.map_u1
  | pi domain body domainIH bodyIH =>
      calc
        hom.map (ScopedTerm.pi domain body) =
            target.pi (hom.map domain) (hom.map body) := by
          simpa only [twoSortSyntaxAlgebra] using
            hom.preserves.map_pi domain body
        _ = target.pi (twoSortRawFold target domain)
            (twoSortRawFold target body) := by rw [domainIH, bodyIH]
        _ = twoSortRawFold target (ScopedTerm.pi domain body) := rfl
  | sigma domain body domainIH bodyIH =>
      calc
        hom.map (ScopedTerm.sigma domain body) =
            target.sigma (hom.map domain) (hom.map body) := by
          simpa only [twoSortSyntaxAlgebra] using
            hom.preserves.map_sigma domain body
        _ = target.sigma (twoSortRawFold target domain)
            (twoSortRawFold target body) := by rw [domainIH, bodyIH]
        _ = twoSortRawFold target (ScopedTerm.sigma domain body) := rfl
  | id type left right typeIH leftIH rightIH =>
      calc
        hom.map (ScopedTerm.id type left right) =
            target.id (hom.map type) (hom.map left) (hom.map right) := by
          simpa only [twoSortSyntaxAlgebra] using
            hom.preserves.map_id type left right
        _ = target.id (twoSortRawFold target type) (twoSortRawFold target left)
            (twoSortRawFold target right) := by rw [typeIH, leftIH, rightIH]
        _ = twoSortRawFold target (ScopedTerm.id type left right) := rfl
  | lam body bodyIH =>
      calc
        hom.map (ScopedTerm.lam body) = target.lam (hom.map body) := by
          simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_lam body
        _ = target.lam (twoSortRawFold target body) := by rw [bodyIH]
        _ = twoSortRawFold target (ScopedTerm.lam body) := rfl
  | app function argument functionIH argumentIH =>
      calc
        hom.map (ScopedTerm.app function argument) =
            target.app (hom.map function) (hom.map argument) := by
          simpa only [twoSortSyntaxAlgebra] using
            hom.preserves.map_app function argument
        _ = target.app (twoSortRawFold target function)
            (twoSortRawFold target argument) := by rw [functionIH, argumentIH]
        _ = twoSortRawFold target (ScopedTerm.app function argument) := rfl
  | pair left right leftIH rightIH =>
      calc
        hom.map (ScopedTerm.pair left right) =
            target.pair (hom.map left) (hom.map right) := by
          simpa only [twoSortSyntaxAlgebra] using
            hom.preserves.map_pair left right
        _ = target.pair (twoSortRawFold target left)
            (twoSortRawFold target right) := by rw [leftIH, rightIH]
        _ = twoSortRawFold target (ScopedTerm.pair left right) := rfl
  | fst pair pairIH =>
      calc
        hom.map (ScopedTerm.fst pair) = target.fst (hom.map pair) := by
          simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_fst pair
        _ = target.fst (twoSortRawFold target pair) := by rw [pairIH]
        _ = twoSortRawFold target (ScopedTerm.fst pair) := rfl
  | snd pair pairIH =>
      calc
        hom.map (ScopedTerm.snd pair) = target.snd (hom.map pair) := by
          simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_snd pair
        _ = target.snd (twoSortRawFold target pair) := by rw [pairIH]
        _ = twoSortRawFold target (ScopedTerm.snd pair) := rfl
  | refl term termIH =>
      calc
        hom.map (ScopedTerm.refl term) = target.refl (hom.map term) := by
          simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_refl term
        _ = target.refl (twoSortRawFold target term) := by rw [termIH]
        _ = twoSortRawFold target (ScopedTerm.refl term) := rfl

/-- The intrinsic raw two-sort syntax is initial among algebras of its complete
binding signature: every homomorphism out of it is the structural fold. -/
theorem twoSortRawFold_unique
    (target : TwoSortRawAlgebra.{uRawTarget})
    (hom : TwoSortRawHom twoSortSyntaxAlgebra target) :
    hom = twoSortRawFoldHom target := by
  apply TwoSortRawHom.ext
  exact twoSortRawFold_unique_pointwise target hom

/-- A nontrivial target algebra: structural node count, including binders. -/
abbrev twoSortNodeCountAlgebra : TwoSortRawAlgebra where
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
def twoSortNodeCount {n : Nat} (term : ScopedTerm n) : Nat :=
  twoSortRawFold twoSortNodeCountAlgebra term

/-- Positive nondegeneracy witness: interpretation traverses a binder and an
application rather than collapsing all syntax to one value. -/
theorem twoSortNodeCount_betaShape_positive :
    twoSortNodeCount
      (ScopedTerm.app (ScopedTerm.lam (ScopedTerm.var (0 : Fin 1))) ScopedTerm.u0) = 4 :=
  rfl

/-- The deliberately collapsed unit algebra is a valid target of fold. -/
abbrev twoSortUnitAlgebra : TwoSortRawAlgebra where
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
theorem no_unit_to_twoSort_syntax_hom :
    ¬ Nonempty (TwoSortRawHom twoSortUnitAlgebra twoSortSyntaxAlgebra) := by
  rintro ⟨hom⟩
  have u0Mapped := hom.preserves.map_u0 (n := 0)
  have u1Mapped := hom.preserves.map_u1 (n := 0)
  have collapsed : (ScopedTerm.u0 : ScopedTerm 0) = ScopedTerm.u1 := by
    exact u0Mapped.symm.trans u1Mapped
  cases collapsed

/-! ### Equality profiles and their quotient presentations

An optional equality extension inhabits this interface; it does not change the
intensional core.  Besides being a congruence for the complete raw signature,
an admissible equality profile supplies stability under simultaneous
substitution.  The condition relates substitutions pointwise, so it remains
suitable for nontrivial open terms rather than merely closed syntax.  Renaming
stability is derived below rather than supplied as a duplicate premise. -/

/-- An equality profile admissible for the intrinsically scoped two-sort syntax. -/
structure TwoSortEqualityProfile where
  Rel : {n : Nat} → ScopedTerm n → ScopedTerm n → Prop
  equivalence : ∀ n, Equivalence (@Rel n)
  congr_pi : ∀ {n} {A A' : ScopedTerm n} {B B' : ScopedTerm (n + 1)},
    Rel A A' → Rel B B' → Rel (.pi A B) (.pi A' B')
  congr_sigma : ∀ {n} {A A' : ScopedTerm n} {B B' : ScopedTerm (n + 1)},
    Rel A A' → Rel B B' → Rel (.sigma A B) (.sigma A' B')
  congr_id : ∀ {n} {A A' a a' b b' : ScopedTerm n},
    Rel A A' → Rel a a' → Rel b b' → Rel (.id A a b) (.id A' a' b')
  congr_lam : ∀ {n} {body body' : ScopedTerm (n + 1)},
    Rel body body' → Rel (.lam body) (.lam body')
  congr_app : ∀ {n} {f f' a a' : ScopedTerm n},
    Rel f f' → Rel a a' → Rel (.app f a) (.app f' a')
  congr_pair : ∀ {n} {a a' b b' : ScopedTerm n},
    Rel a a' → Rel b b' → Rel (.pair a b) (.pair a' b')
  congr_fst : ∀ {n} {pair pair' : ScopedTerm n},
    Rel pair pair' → Rel (.fst pair) (.fst pair')
  congr_snd : ∀ {n} {pair pair' : ScopedTerm n},
    Rel pair pair' → Rel (.snd pair) (.snd pair')
  congr_refl : ∀ {n} {term term' : ScopedTerm n},
    Rel term term' → Rel (.refl term) (.refl term')
  subst_closed : ∀ {n m}
    {leftSub rightSub :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m}
    {left right : ScopedTerm n},
    (∀ index, Rel (leftSub index) (rightSub index)) → Rel left right →
      Rel
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst leftSub left)
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst rightSub right)

namespace TwoSortEqualityProfile

/-- Renaming stability is forced by pointwise substitution stability: use the
renaming as a substitution whose images are variables.  It is therefore a
theorem of every admissible profile rather than an independently supplied
regularity premise. -/
theorem rename_closed (profile : TwoSortEqualityProfile) {n m : Nat}
    (ρ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.Ren n m)
    {left right : ScopedTerm n} (related : profile.Rel left right) :
    profile.Rel
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename ρ left)
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename ρ right) := by
  have substituted := profile.subst_closed
    (leftSub :=
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.renToSub ρ)
    (rightSub :=
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.renToSub ρ)
    (fun index => (profile.equivalence m).refl _)
    related
  simpa only [
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.subst_renToSub] using
      substituted

/-- The setoid presented by one equality profile at one de Bruijn depth. -/
def setoid (profile : TwoSortEqualityProfile) (n : Nat) : Setoid (ScopedTerm n) where
  r := profile.Rel
  iseqv := profile.equivalence n

/-- Map a unary syntax operation through an equality-profile quotient. -/
def mapOne (profile : TwoSortEqualityProfile) {n m : Nat}
    (operation : ScopedTerm n → ScopedTerm m)
    (respects : ∀ {left right}, profile.Rel left right →
      profile.Rel (operation left) (operation right)) :
    Quotient (profile.setoid n) → Quotient (profile.setoid m) :=
  Quotient.map' (s₁ := profile.setoid n) (s₂ := profile.setoid m)
    operation (fun _ _ related => respects related)

/-- Map a binary syntax operation through equality-profile quotients. -/
def mapTwo (profile : TwoSortEqualityProfile) {n₁ n₂ m : Nat}
    (operation : ScopedTerm n₁ → ScopedTerm n₂ → ScopedTerm m)
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
def mapThree (profile : TwoSortEqualityProfile) {n₁ n₂ n₃ m : Nat}
    (operation : ScopedTerm n₁ → ScopedTerm n₂ → ScopedTerm n₃ → ScopedTerm m)
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
def rename (profile : TwoSortEqualityProfile) {n m : Nat}
    (ρ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.Ren n m) :
    Quotient (profile.setoid n) → Quotient (profile.setoid m) :=
  profile.mapOne
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename ρ)
    (fun related => profile.rename_closed ρ related)

/-- A raw simultaneous substitution descends to the profile quotient.  The
more general quotient-valued environment is built later with the contextual
presentation; this operation already proves stability under every live
intrinsic substitution. -/
def substRaw (profile : TwoSortEqualityProfile) {n m : Nat}
    (σ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m) :
    Quotient (profile.setoid n) → Quotient (profile.setoid m) :=
  profile.mapOne
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst σ)
    (fun related => profile.subst_closed
      (fun index => (profile.equivalence m).refl (σ index)) related)

@[simp] theorem rename_mk (profile : TwoSortEqualityProfile) {n m : Nat}
    (ρ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.Ren n m)
    (term : ScopedTerm n) :
    profile.rename ρ (Quotient.mk (profile.setoid n) term) =
      Quotient.mk (profile.setoid m)
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename ρ term) :=
  rfl

@[simp] theorem substRaw_mk (profile : TwoSortEqualityProfile) {n m : Nat}
    (σ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m)
    (term : ScopedTerm n) :
    profile.substRaw σ (Quotient.mk (profile.setoid n) term) =
      Quotient.mk (profile.setoid m)
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst σ term) :=
  rfl

/-- Identity substitution remains identity after quotienting. -/
theorem substRaw_ids (profile : TwoSortEqualityProfile) {n : Nat}
    (term : Quotient (profile.setoid n)) :
    profile.substRaw
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.ids (n := n)) term =
      term := by
  refine Quotient.inductionOn term ?_
  intro syntaxTerm
  simp

/-- Composition of raw substitutions remains composition after quotienting. -/
theorem substRaw_comp (profile : TwoSortEqualityProfile) {n m k : Nat}
    (τ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub m k)
    (σ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m)
    (term : Quotient (profile.setoid n)) :
    profile.substRaw τ (profile.substRaw σ term) =
      profile.substRaw
        (fun index =>
          Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst τ (σ index))
        term := by
  refine Quotient.inductionOn term ?_
  intro syntaxTerm
  simp

/-- `finer.FinerThan coarser` means every equation of `finer` is also an
equation of `coarser`, hence there is a canonical quotient map from the finer
presentation to the coarser one. -/
def FinerThan (finer coarser : TwoSortEqualityProfile) : Prop :=
  ∀ {n} {left right : ScopedTerm n}, finer.Rel left right → coarser.Rel left right

/-- The canonical map induced by inclusion of equality profiles. -/
def quotientMap {finer coarser : TwoSortEqualityProfile}
    (includes : finer.FinerThan coarser) (n : Nat) :
    Quotient (finer.setoid n) → Quotient (coarser.setoid n) :=
  Quotient.map' id (fun _ _ related => includes related)

@[simp] theorem quotientMap_mk {finer coarser : TwoSortEqualityProfile}
    (includes : finer.FinerThan coarser) {n : Nat} (term : ScopedTerm n) :
    quotientMap includes n (Quotient.mk (finer.setoid n) term) =
      Quotient.mk (coarser.setoid n) term :=
  rfl

end TwoSortEqualityProfile

/-! ### Equality kernels forced by contextual interpretations -/

/-- Substitution action and its naturality for one raw interpretation.  This
is the exact extra structure needed beyond a raw-signature homomorphism for
the interpretation kernel to be stable under open substitution.  It is not
presented as a full CwF: context comprehension and typed terms enter at the
later semantic interpretation boundary. -/
structure TwoSortInterpretationSubstitutionAction
    (target : TwoSortRawAlgebra.{uRawTarget})
    (hom : TwoSortRawHom twoSortSyntaxAlgebra target) where
  semanticSubst : {n m : Nat} →
    (Fin n → target.Carrier m) → target.Carrier n → target.Carrier m
  map_subst : ∀ {n m}
    (substitution :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m)
    (term : ScopedTerm n),
    hom.map
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
          substitution term) =
      semanticSubst (fun index => hom.map (substitution index)) (hom.map term)

namespace TwoSortRawHom

/-- Equality of semantic images induces every congruence law automatically;
substitution naturality induces the open-substitution law.  Thus an
interpretation kernel is an admissible equality profile without separately
postulating its regularity fields. -/
def kernelProfile {target : TwoSortRawAlgebra.{uRawTarget}}
    (hom : TwoSortRawHom twoSortSyntaxAlgebra target)
    (action : TwoSortInterpretationSubstitutionAction target hom) :
    TwoSortEqualityProfile where
  Rel := fun left right => hom.map left = hom.map right
  equivalence := fun _ =>
    { refl := fun term => Eq.refl (hom.map term)
      symm := fun related => related.symm
      trans := fun first second => first.trans second }
  congr_pi := by
    intro n A A' B B' domainRelated bodyRelated
    calc
      hom.map (.pi A B) = target.pi (hom.map A) (hom.map B) := by
        simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_pi A B
      _ = target.pi (hom.map A') (hom.map B') := by
        rw [domainRelated, bodyRelated]
      _ = hom.map (.pi A' B') := by
        simpa only [twoSortSyntaxAlgebra] using
          (hom.preserves.map_pi A' B').symm
  congr_sigma := by
    intro n A A' B B' domainRelated bodyRelated
    calc
      hom.map (.sigma A B) = target.sigma (hom.map A) (hom.map B) := by
        simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_sigma A B
      _ = target.sigma (hom.map A') (hom.map B') := by
        rw [domainRelated, bodyRelated]
      _ = hom.map (.sigma A' B') := by
        simpa only [twoSortSyntaxAlgebra] using
          (hom.preserves.map_sigma A' B').symm
  congr_id := by
    intro n A A' left left' right right' typeRelated leftRelated rightRelated
    calc
      hom.map (.id A left right) =
          target.id (hom.map A) (hom.map left) (hom.map right) := by
        simpa only [twoSortSyntaxAlgebra] using
          hom.preserves.map_id A left right
      _ = target.id (hom.map A') (hom.map left') (hom.map right') := by
        rw [typeRelated, leftRelated, rightRelated]
      _ = hom.map (.id A' left' right') := by
        simpa only [twoSortSyntaxAlgebra] using
          (hom.preserves.map_id A' left' right').symm
  congr_lam := by
    intro n body body' related
    calc
      hom.map (.lam body) = target.lam (hom.map body) := by
        simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_lam body
      _ = target.lam (hom.map body') := by rw [related]
      _ = hom.map (.lam body') := by
        simpa only [twoSortSyntaxAlgebra] using
          (hom.preserves.map_lam body').symm
  congr_app := by
    intro n function function' argument argument' functionRelated argumentRelated
    calc
      hom.map (.app function argument) =
          target.app (hom.map function) (hom.map argument) := by
        simpa only [twoSortSyntaxAlgebra] using
          hom.preserves.map_app function argument
      _ = target.app (hom.map function') (hom.map argument') := by
        rw [functionRelated, argumentRelated]
      _ = hom.map (.app function' argument') := by
        simpa only [twoSortSyntaxAlgebra] using
          (hom.preserves.map_app function' argument').symm
  congr_pair := by
    intro n left left' right right' leftRelated rightRelated
    calc
      hom.map (.pair left right) =
          target.pair (hom.map left) (hom.map right) := by
        simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_pair left right
      _ = target.pair (hom.map left') (hom.map right') := by
        rw [leftRelated, rightRelated]
      _ = hom.map (.pair left' right') := by
        simpa only [twoSortSyntaxAlgebra] using
          (hom.preserves.map_pair left' right').symm
  congr_fst := by
    intro n pair pair' related
    calc
      hom.map (.fst pair) = target.fst (hom.map pair) := by
        simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_fst pair
      _ = target.fst (hom.map pair') := by rw [related]
      _ = hom.map (.fst pair') := by
        simpa only [twoSortSyntaxAlgebra] using
          (hom.preserves.map_fst pair').symm
  congr_snd := by
    intro n pair pair' related
    calc
      hom.map (.snd pair) = target.snd (hom.map pair) := by
        simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_snd pair
      _ = target.snd (hom.map pair') := by rw [related]
      _ = hom.map (.snd pair') := by
        simpa only [twoSortSyntaxAlgebra] using
          (hom.preserves.map_snd pair').symm
  congr_refl := by
    intro n term term' related
    calc
      hom.map (.refl term) = target.refl (hom.map term) := by
        simpa only [twoSortSyntaxAlgebra] using hom.preserves.map_refl term
      _ = target.refl (hom.map term') := by rw [related]
      _ = hom.map (.refl term') := by
        simpa only [twoSortSyntaxAlgebra] using
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
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
            leftSub left) =
          action.semanticSubst (fun index => hom.map (leftSub index))
            (hom.map left) := action.map_subst leftSub left
      _ = action.semanticSubst (fun index => hom.map (rightSub index))
            (hom.map right) := by rw [environmentsEqual, termsRelated]
      _ = hom.map
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
            rightSub right) := (action.map_subst rightSub right).symm

end TwoSortRawHom

/-- The identity interpretation carries the ordinary syntactic substitution
action. -/
def twoSortSyntaxSubstitutionAction :
    TwoSortInterpretationSubstitutionAction twoSortSyntaxAlgebra
      (TwoSortRawHom.id twoSortSyntaxAlgebra) where
  semanticSubst :=
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
  map_subst := by intros; rfl

/-- Syntactic equality recovered as the kernel of the identity contextual
interpretation, rather than assembled from a second list of regularity
proofs.  Reducibility retains the expected definitional equality interface
for clients of the profile. -/
abbrev syntacticEqualityProfile : TwoSortEqualityProfile :=
  (TwoSortRawHom.id twoSortSyntaxAlgebra).kernelProfile
    twoSortSyntaxSubstitutionAction

theorem syntacticEqualityProfile_rel_iff {n : Nat}
    (left right : ScopedTerm n) :
    syntacticEqualityProfile.Rel left right ↔ left = right := by
  rfl

/-- A raw algebra that identifies every variable with `u1` while keeping
`u0` distinct.  It is a valid algebra for the constructor signature, but its
interpretation kernel is not stable under open substitution. -/
abbrev substitutionUnstableTwoSortAlgebra : TwoSortRawAlgebra where
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

def substitutionUnstableTwoSortHom :
    TwoSortRawHom twoSortSyntaxAlgebra substitutionUnstableTwoSortAlgebra :=
  twoSortRawFoldHom substitutionUnstableTwoSortAlgebra

/-- Negative control: raw constructor preservation alone does not force
substitution regularity.  Replacing the related variable and `u1` by the same
`u0` environment separates their images, so no natural substitution action
can exist for this raw interpretation. -/
theorem substitutionUnstableTwoSortHom_has_no_substitution_action :
    ¬ Nonempty
      (TwoSortInterpretationSubstitutionAction substitutionUnstableTwoSortAlgebra
        substitutionUnstableTwoSortHom) := by
  rintro ⟨action⟩
  let substitution :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub 1 0 :=
    fun _ => .u0
  have related :
      substitutionUnstableTwoSortHom.map (.var (0 : Fin 1)) =
        substitutionUnstableTwoSortHom.map .u1 := by
    rfl
  have semanticRelated := congrArg
    (action.semanticSubst
      (fun _ : Fin 1 =>
        substitutionUnstableTwoSortHom.map (ScopedTerm.u0 : ScopedTerm 0)))
    related
  have substitutedRelated :
      substitutionUnstableTwoSortHom.map
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
            substitution (.var (0 : Fin 1))) =
        substitutionUnstableTwoSortHom.map
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
            substitution .u1) :=
    (action.map_subst substitution (.var (0 : Fin 1))).trans
      (semanticRelated.trans (action.map_subst substitution .u1).symm)
  change false = true at substitutedRelated
  cases substitutedRelated

/-- The quotient algebra selected by an equality profile. -/
def twoSortProfileQuotientAlgebra (profile : TwoSortEqualityProfile) :
    TwoSortRawAlgebra where
  Carrier := fun n => Quotient (profile.setoid n)
  var := fun {n} index => Quotient.mk (profile.setoid n) (.var index)
  const := fun {n} name => Quotient.mk (profile.setoid n) (.const name)
  u0 := fun {n} => Quotient.mk (profile.setoid n) .u0
  u1 := fun {n} => Quotient.mk (profile.setoid n) .u1
  pi := fun domain body => profile.mapTwo ScopedTerm.pi
    (fun domainRelated bodyRelated => profile.congr_pi domainRelated bodyRelated)
    domain body
  sigma := fun domain body => profile.mapTwo ScopedTerm.sigma
    (fun domainRelated bodyRelated =>
      profile.congr_sigma domainRelated bodyRelated) domain body
  id := fun type left right => profile.mapThree ScopedTerm.id
    (fun typeRelated leftRelated rightRelated =>
      profile.congr_id typeRelated leftRelated rightRelated) type left right
  lam := fun body => profile.mapOne ScopedTerm.lam
    (fun related => profile.congr_lam related) body
  app := fun function argument => profile.mapTwo ScopedTerm.app
    (fun functionRelated argumentRelated =>
      profile.congr_app functionRelated argumentRelated) function argument
  pair := fun left right => profile.mapTwo ScopedTerm.pair
    (fun leftRelated rightRelated =>
      profile.congr_pair leftRelated rightRelated) left right
  fst := fun pair => profile.mapOne ScopedTerm.fst
    (fun related => profile.congr_fst related) pair
  snd := fun pair => profile.mapOne ScopedTerm.snd
    (fun related => profile.congr_snd related) pair
  refl := fun term => profile.mapOne ScopedTerm.refl
    (fun related => profile.congr_refl related) term

/-- Canonical projection from raw two-sort syntax to a selected profile quotient. -/
def twoSortProfileQuotientHom (profile : TwoSortEqualityProfile) :
    TwoSortRawHom twoSortSyntaxAlgebra (twoSortProfileQuotientAlgebra profile) where
  map := fun {n} term => Quotient.mk (profile.setoid n) term
  preserves := by
    constructor <;> intros <;>
      rfl

/-- A raw interpretation respects a selected equality profile exactly when it
identifies every pair related by that profile. -/
def TwoSortRawHom.RespectsProfile {target : TwoSortRawAlgebra.{uRawTarget}}
    (hom : TwoSortRawHom twoSortSyntaxAlgebra target)
    (profile : TwoSortEqualityProfile) : Prop :=
  ∀ {n} {left right : ScopedTerm n}, profile.Rel left right →
    hom.map left = hom.map right

/-- The canonical quotient projection respects its defining profile. -/
theorem twoSortProfileQuotientHom_respects (profile : TwoSortEqualityProfile) :
    (twoSortProfileQuotientHom profile).RespectsProfile profile := by
  intro n left right related
  exact Quotient.sound related

abbrev TwoSortPiSigmaIdConv {n : Nat} :=
  @Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.Conv n

abbrev TwoSortPiSigmaIdRed {n : Nat} :=
  @Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red n

/-- Equivalence closure transports through any operation that transports one
scoped two-sort reduction step. -/
theorem twoSortPiSigmaIdConv_map {n m : Nat} (operation : ScopedTerm n → ScopedTerm m)
    (mapsRed : ∀ {left right}, TwoSortPiSigmaIdRed left right →
      TwoSortPiSigmaIdRed (operation left) (operation right))
    {left right : ScopedTerm n} (conversion : TwoSortPiSigmaIdConv left right) :
    TwoSortPiSigmaIdConv (operation left) (operation right) := by
  induction conversion with
  | rel left right step => exact .rel _ _ (mapsRed step)
  | refl term => exact .refl _
  | symm left right related inductionHypothesis =>
      exact .symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact .trans _ _ _ firstIH secondIH

theorem twoSortPiSigmaIdConv_congr_pi {n : Nat}
    {A A' : ScopedTerm n} {B B' : ScopedTerm (n + 1)}
    (domain : TwoSortPiSigmaIdConv A A') (body : TwoSortPiSigmaIdConv B B') :
    TwoSortPiSigmaIdConv (.pi A B) (.pi A' B') :=
  Relation.EqvGen.trans _ _ _
    (twoSortPiSigmaIdConv_map (fun term => .pi term B)
      (fun step => .congPiDom step) domain)
    (twoSortPiSigmaIdConv_map (fun term => .pi A' term)
      (fun step => .congPiCod step) body)

theorem twoSortPiSigmaIdConv_congr_sigma {n : Nat}
    {A A' : ScopedTerm n} {B B' : ScopedTerm (n + 1)}
    (domain : TwoSortPiSigmaIdConv A A') (body : TwoSortPiSigmaIdConv B B') :
    TwoSortPiSigmaIdConv (.sigma A B) (.sigma A' B') :=
  Relation.EqvGen.trans _ _ _
    (twoSortPiSigmaIdConv_map (fun term => .sigma term B)
      (fun step => .congSigmaDom step) domain)
    (twoSortPiSigmaIdConv_map (fun term => .sigma A' term)
      (fun step => .congSigmaCod step) body)

theorem twoSortPiSigmaIdConv_congr_id {n : Nat}
    {A A' a a' b b' : ScopedTerm n}
    (type : TwoSortPiSigmaIdConv A A')
    (left : TwoSortPiSigmaIdConv a a')
    (right : TwoSortPiSigmaIdConv b b') :
    TwoSortPiSigmaIdConv (.id A a b) (.id A' a' b') :=
  Relation.EqvGen.trans _ _ _
    (twoSortPiSigmaIdConv_map (fun term => .id term a b)
      (fun step => .congIdTy step) type)
    (Relation.EqvGen.trans _ _ _
      (twoSortPiSigmaIdConv_map (fun term => .id A' term b)
        (fun step => .congIdLeft step) left)
      (twoSortPiSigmaIdConv_map (fun term => .id A' a' term)
        (fun step => .congIdRight step) right))

theorem twoSortPiSigmaIdConv_congr_lam {n : Nat}
    {body body' : ScopedTerm (n + 1)}
    (conversion : TwoSortPiSigmaIdConv body body') :
    TwoSortPiSigmaIdConv (.lam body) (.lam body') :=
  twoSortPiSigmaIdConv_map ScopedTerm.lam (fun step => .congLam step) conversion

theorem twoSortPiSigmaIdConv_congr_app {n : Nat}
    {function function' argument argument' : ScopedTerm n}
    (functionConversion : TwoSortPiSigmaIdConv function function')
    (argumentConversion : TwoSortPiSigmaIdConv argument argument') :
    TwoSortPiSigmaIdConv (.app function argument) (.app function' argument') :=
  Relation.EqvGen.trans _ _ _
    (twoSortPiSigmaIdConv_map (fun term => .app term argument)
      (fun step => .congAppFun step) functionConversion)
    (twoSortPiSigmaIdConv_map (fun term => .app function' term)
      (fun step => .congAppArg step) argumentConversion)

theorem twoSortPiSigmaIdConv_congr_pair {n : Nat}
    {left left' right right' : ScopedTerm n}
    (leftConversion : TwoSortPiSigmaIdConv left left')
    (rightConversion : TwoSortPiSigmaIdConv right right') :
    TwoSortPiSigmaIdConv (.pair left right) (.pair left' right') :=
  Relation.EqvGen.trans _ _ _
    (twoSortPiSigmaIdConv_map (fun term => .pair term right)
      (fun step => .congPairFst step) leftConversion)
    (twoSortPiSigmaIdConv_map (fun term => .pair left' term)
      (fun step => .congPairSnd step) rightConversion)

theorem twoSortPiSigmaIdConv_congr_fst {n : Nat} {pair pair' : ScopedTerm n}
    (conversion : TwoSortPiSigmaIdConv pair pair') :
    TwoSortPiSigmaIdConv (.fst pair) (.fst pair') :=
  twoSortPiSigmaIdConv_map ScopedTerm.fst (fun step => .congFst step) conversion

theorem twoSortPiSigmaIdConv_congr_snd {n : Nat} {pair pair' : ScopedTerm n}
    (conversion : TwoSortPiSigmaIdConv pair pair') :
    TwoSortPiSigmaIdConv (.snd pair) (.snd pair') :=
  twoSortPiSigmaIdConv_map ScopedTerm.snd (fun step => .congSnd step) conversion

theorem twoSortPiSigmaIdConv_congr_refl {n : Nat} {term term' : ScopedTerm n}
    (conversion : TwoSortPiSigmaIdConv term term') :
    TwoSortPiSigmaIdConv (.refl term) (.refl term') :=
  twoSortPiSigmaIdConv_map ScopedTerm.refl (fun step => .congRefl step) conversion

/-- Pointwise convertible substitution environments yield convertible
instances.  The binder cases use the actual live `liftSub` and renaming
lemmas, so this is the contextual rather than merely closed conversion law. -/
theorem twoSortPiSigmaIdConv_subst_pointwise {n m : Nat}
    {leftSub rightSub :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m}
    (substitutions : ∀ index, TwoSortPiSigmaIdConv
      (leftSub index) (rightSub index)) :
    ∀ term : ScopedTerm n, TwoSortPiSigmaIdConv
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst leftSub term)
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst rightSub term) := by
  intro term
  induction term generalizing m with
  | var index => exact substitutions index
  | const name => exact .refl _
  | u0 => exact .refl _
  | u1 => exact .refl _
  | pi domain body domainIH bodyIH =>
      apply twoSortPiSigmaIdConv_congr_pi
      · exact domainIH substitutions
      · apply bodyIH
        intro index
        refine Fin.cases ?_ ?_ index
        · exact .refl _
        · intro predecessor
          exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.conv_rename
            Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk
            (substitutions predecessor)
  | sigma domain body domainIH bodyIH =>
      apply twoSortPiSigmaIdConv_congr_sigma
      · exact domainIH substitutions
      · apply bodyIH
        intro index
        refine Fin.cases ?_ ?_ index
        · exact .refl _
        · intro predecessor
          exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.conv_rename
            Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk
            (substitutions predecessor)
  | id type left right typeIH leftIH rightIH =>
      exact twoSortPiSigmaIdConv_congr_id (typeIH substitutions)
        (leftIH substitutions) (rightIH substitutions)
  | lam body bodyIH =>
      apply twoSortPiSigmaIdConv_congr_lam
      apply bodyIH
      intro index
      refine Fin.cases ?_ ?_ index
      · exact .refl _
      · intro predecessor
        exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.conv_rename
          Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk
          (substitutions predecessor)
  | app function argument functionIH argumentIH =>
      exact twoSortPiSigmaIdConv_congr_app (functionIH substitutions)
        (argumentIH substitutions)
  | pair left right leftIH rightIH =>
      exact twoSortPiSigmaIdConv_congr_pair (leftIH substitutions)
        (rightIH substitutions)
  | fst pair pairIH => exact twoSortPiSigmaIdConv_congr_fst (pairIH substitutions)
  | snd pair pairIH => exact twoSortPiSigmaIdConv_congr_snd (pairIH substitutions)
  | refl term termIH => exact twoSortPiSigmaIdConv_congr_refl (termIH substitutions)

/-- Both the substituted term and its simultaneous environment may vary by
scoped two-sort conversion. -/
theorem twoSortPiSigmaIdConv_subst_congr {n m : Nat}
    {leftSub rightSub :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m}
    {left right : ScopedTerm n}
    (substitutions : ∀ index, TwoSortPiSigmaIdConv
      (leftSub index) (rightSub index))
    (terms : TwoSortPiSigmaIdConv left right) :
    TwoSortPiSigmaIdConv
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst leftSub left)
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst rightSub right) :=
  Relation.EqvGen.trans _ _ _
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.conv_subst leftSub terms)
    (twoSortPiSigmaIdConv_subst_pointwise substitutions right)

/-- The actual scoped two-sort conversion relation as one admissible equality
profile.  It is evidence for the extension interface, not kernel selection. -/
def twoSortPiSigmaIdConversionProfile : TwoSortEqualityProfile where
  Rel := TwoSortPiSigmaIdConv
  equivalence := fun _ =>
    ⟨fun term => .refl term,
      fun relation => .symm _ _ relation,
      fun first second => .trans _ _ _ first second⟩
  congr_pi := twoSortPiSigmaIdConv_congr_pi
  congr_sigma := twoSortPiSigmaIdConv_congr_sigma
  congr_id := twoSortPiSigmaIdConv_congr_id
  congr_lam := twoSortPiSigmaIdConv_congr_lam
  congr_app := twoSortPiSigmaIdConv_congr_app
  congr_pair := twoSortPiSigmaIdConv_congr_pair
  congr_fst := twoSortPiSigmaIdConv_congr_fst
  congr_snd := twoSortPiSigmaIdConv_congr_snd
  congr_refl := twoSortPiSigmaIdConv_congr_refl
  subst_closed := fun substitutions conversion =>
    twoSortPiSigmaIdConv_subst_congr substitutions conversion

/-- Positive witness for the live intrinsic profile: β-conversion is one of
its genuine, nonsyntactic equations. -/
theorem twoSortPiSigmaIdConversionProfile_beta :
    twoSortPiSigmaIdConversionProfile.Rel
      (ScopedTerm.app (ScopedTerm.lam (ScopedTerm.var (0 : Fin 1))) ScopedTerm.u0)
      (ScopedTerm.u0 : ScopedTerm 0) := by
  exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.red_implies_conv
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red.betaPi
      (ScopedTerm.var (0 : Fin 1)) ScopedTerm.u0)

/-- The positive β witness becomes literal equality in the corresponding
profile quotient. -/
theorem twoSortPiSigmaIdProfile_beta_quotient :
    (twoSortProfileQuotientHom twoSortPiSigmaIdConversionProfile).map
        (ScopedTerm.app (ScopedTerm.lam (ScopedTerm.var (0 : Fin 1))) ScopedTerm.u0) =
      (twoSortProfileQuotientHom twoSortPiSigmaIdConversionProfile).map
        (ScopedTerm.u0 : ScopedTerm 0) :=
  Quotient.sound twoSortPiSigmaIdConversionProfile_beta

/-- Positive quotient witness: syntactic equality does not collapse the two
universe constructors. -/
theorem syntacticProfile_u0_ne_u1 :
    (twoSortProfileQuotientHom syntacticEqualityProfile).map
        (ScopedTerm.u0 : ScopedTerm 0) ≠
      (twoSortProfileQuotientHom syntacticEqualityProfile).map ScopedTerm.u1 := by
  intro equalClasses
  have termsEqual : (ScopedTerm.u0 : ScopedTerm 0) = ScopedTerm.u1 :=
    Quotient.exact equalClasses
  cases termsEqual

/-- Syntactic equality is the finest admissible equality profile. -/
theorem syntacticEqualityProfile_finer
    (profile : TwoSortEqualityProfile) :
    syntacticEqualityProfile.FinerThan profile := by
  intro n left right equal
  have termsEqual := (syntacticEqualityProfile_rel_iff left right).mp equal
  subst right
  exact (profile.equivalence n).refl left

/-- Negative witness distinguishing the live two-sort conversion profile from raw
syntax: β-conversion prevents an inclusion back into syntactic equality. -/
theorem twoSortPiSigmaIdProfile_not_finer_than_syntactic :
    ¬ twoSortPiSigmaIdConversionProfile.FinerThan syntacticEqualityProfile := by
  intro includes
  have syntaxEquality := includes twoSortPiSigmaIdConversionProfile_beta
  change ScopedTerm.app (ScopedTerm.lam (ScopedTerm.var (0 : Fin 1))) ScopedTerm.u0 =
    (ScopedTerm.u0 : ScopedTerm 0) at syntaxEquality
  cases syntaxEquality

/-- A profile that identifies the two universes cannot be interpreted by the
identity syntax homomorphism.  This is a negative witness that profile-respect
is a real restriction, not bookkeeping around an arbitrary raw fold. -/
theorem profile_equating_universes_blocks_identity
    (profile : TwoSortEqualityProfile)
    (collapses : profile.Rel (ScopedTerm.u0 : ScopedTerm 0) ScopedTerm.u1) :
    ¬ (TwoSortRawHom.id twoSortSyntaxAlgebra).RespectsProfile profile := by
  intro respects
  have termsEqual := respects collapses
  change (ScopedTerm.u0 : ScopedTerm 0) = ScopedTerm.u1 at termsEqual
  cases termsEqual

/-- Negative profile-order witness: any profile equating the universes is
strictly coarser than raw syntactic equality, so there is no inclusion of its
equations back into the syntactic profile. -/
theorem profile_equating_universes_not_finer_than_syntactic
    (profile : TwoSortEqualityProfile)
    (collapses : profile.Rel (ScopedTerm.u0 : ScopedTerm 0) ScopedTerm.u1) :
    ¬ profile.FinerThan syntacticEqualityProfile := by
  intro includes
  have termsEqual : (ScopedTerm.u0 : ScopedTerm 0) = ScopedTerm.u1 := includes collapses
  cases termsEqual

/-- Factor a profile-respecting interpretation through the selected quotient. -/
def TwoSortRawHom.factorThroughProfile
    {target : TwoSortRawAlgebra.{uRawTarget}}
    (profile : TwoSortEqualityProfile)
    (hom : TwoSortRawHom twoSortSyntaxAlgebra target)
    (respects : hom.RespectsProfile profile) :
    TwoSortRawHom (twoSortProfileQuotientAlgebra profile) target where
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
theorem TwoSortRawHom.factorThroughProfile_comp_projection
    {target : TwoSortRawAlgebra.{uRawTarget}}
    (profile : TwoSortEqualityProfile)
    (hom : TwoSortRawHom twoSortSyntaxAlgebra target)
    (respects : hom.RespectsProfile profile) :
    TwoSortRawHom.comp (twoSortProfileQuotientHom profile)
      (hom.factorThroughProfile profile respects) = hom := by
  apply TwoSortRawHom.ext
  intro n term
  rfl

/-- The factorization is unique among quotient-algebra homomorphisms. -/
theorem TwoSortRawHom.factorThroughProfile_unique
    {target : TwoSortRawAlgebra.{uRawTarget}}
    (profile : TwoSortEqualityProfile)
    (hom : TwoSortRawHom twoSortSyntaxAlgebra target)
    (factor : TwoSortRawHom (twoSortProfileQuotientAlgebra profile) target)
    (commutes : TwoSortRawHom.comp (twoSortProfileQuotientHom profile) factor = hom) :
    factor = hom.factorThroughProfile profile
      (by
        intro n left right related
        have mapped := congrArg
          (fun candidate : TwoSortRawHom twoSortSyntaxAlgebra target =>
            candidate.map left) commutes
        have mappedRight := congrArg
          (fun candidate : TwoSortRawHom twoSortSyntaxAlgebra target =>
            candidate.map right) commutes
        have quotientEqual :
            (twoSortProfileQuotientHom profile).map left =
              (twoSortProfileQuotientHom profile).map right :=
          Quotient.sound related
        exact mapped.symm.trans
          ((congrArg factor.map quotientEqual).trans mappedRight)) := by
  apply TwoSortRawHom.ext
  intro n quotient
  refine Quotient.inductionOn quotient ?_
  intro term
  have mapped := congrArg
    (fun candidate : TwoSortRawHom twoSortSyntaxAlgebra target => candidate.map term)
    commutes
  exact mapped

/-! ## §7d The equality-neutral native raw presentation

The preceding initiality precursor covers the live scoped two-sort signature.
This staged-reflective presentation additionally includes the operational
structure selected for investigation: stage-changing quotation, runtime
patterns, collections, and validated languages.  Cost and evidence remain in
an external decoration fibre below; they are native data without becoming
kernel-term constructors in this candidate.

This section forms their free *raw* extension.  A native algebra is a family
of complete `TwoSortRawAlgebra`s indexed by interpreter stage, together with the
six genuinely MeTTa-specific operations.  Consequently the two-sort operations
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

/-- Capture-avoiding renaming, including beneath two-sort binders and across
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

theorem nativeLiftRen_eq_twoSortLiftRen (rho : NativeRen source target) :
    nativeLiftRen rho =
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.liftRen rho := by
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
entire two-sort algebra, which makes two-sort operations available on every native
carrier rather than embedding two-sort as an opaque leaf. -/
structure NativeRawAlgebra where
  atStage : Nat → TwoSortRawAlgebra.{uRaw}
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
  twoSortFormers : ∀ stage, TwoSortRawPreserves (source.atStage stage)
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
  | var index => exact (hom.preserves.twoSortFormers _).map_var index
  | const name => exact (hom.preserves.twoSortFormers _).map_const name
  | u0 => exact (hom.preserves.twoSortFormers _).map_u0
  | u1 => exact (hom.preserves.twoSortFormers _).map_u1
  | pi domain body domainIH bodyIH =>
      rw [(hom.preserves.twoSortFormers _).map_pi, domainIH, bodyIH]
      rfl
  | sigma domain body domainIH bodyIH =>
      rw [(hom.preserves.twoSortFormers _).map_sigma, domainIH, bodyIH]
      rfl
  | id type left right typeIH leftIH rightIH =>
      rw [(hom.preserves.twoSortFormers _).map_id, typeIH, leftIH, rightIH]
      rfl
  | lam body bodyIH =>
      rw [(hom.preserves.twoSortFormers _).map_lam, bodyIH]
      rfl
  | app function argument functionIH argumentIH =>
      rw [(hom.preserves.twoSortFormers _).map_app, functionIH, argumentIH]
      rfl
  | pair left right leftIH rightIH =>
      rw [(hom.preserves.twoSortFormers _).map_pair, leftIH, rightIH]
      rfl
  | fst pair pairIH =>
      rw [(hom.preserves.twoSortFormers _).map_fst, pairIH]
      rfl
  | snd pair pairIH =>
      rw [(hom.preserves.twoSortFormers _).map_snd, pairIH]
      rfl
  | refl term termIH =>
      rw [(hom.preserves.twoSortFormers _).map_refl, termIH]
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

/-! ### Conservative inclusion of scoped two-sort -/

/-- Embed an scoped two-sort term at any native stage.  This is the structural
two-sort fold into that stage, so every two-sort constructor remains visible. -/
def embedTwoSort (stage : Nat) : {binders : Nat} → ScopedTerm binders →
    StagedReflectiveTm stage binders
  | _, .var index => .var index
  | _, .const name => .const name
  | _, .u0 => .u0
  | _, .u1 => .u1
  | _, .pi domain body => .pi (embedTwoSort stage domain) (embedTwoSort stage body)
  | _, .sigma domain body =>
      .sigma (embedTwoSort stage domain) (embedTwoSort stage body)
  | _, .id type left right =>
      .id (embedTwoSort stage type) (embedTwoSort stage left) (embedTwoSort stage right)
  | _, .lam body => .lam (embedTwoSort stage body)
  | _, .app function argument =>
      .app (embedTwoSort stage function) (embedTwoSort stage argument)
  | _, .pair left right => .pair (embedTwoSort stage left) (embedTwoSort stage right)
  | _, .fst pair => .fst (embedTwoSort stage pair)
  | _, .snd pair => .snd (embedTwoSort stage pair)
  | _, .refl term => .refl (embedTwoSort stage term)

/-- Embed an scoped two-sort simultaneous substitution independently at every
stage. -/
def embedTwoSortSub
    (substitution : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub
      source target) : NativeSub source target :=
  fun stage index => embedTwoSort stage (substitution index)

/-- Native renaming restricts exactly to the live scoped two-sort renaming. -/
theorem nativeRename_embedTwoSort (rho : NativeRen source target) (stage : Nat) :
    ∀ term : ScopedTerm source,
      nativeRename rho (embedTwoSort stage term) =
        embedTwoSort stage
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename rho term) := by
  intro term
  induction term generalizing target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename]
      congr 1
      · exact domainIH rho
      · rw [nativeLiftRen_eq_twoSortLiftRen rho]
        exact bodyIH _
  | sigma domain body domainIH bodyIH =>
      simp only [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename]
      congr 1
      · exact domainIH rho
      · rw [nativeLiftRen_eq_twoSortLiftRen rho]
        exact bodyIH _
  | id type left right typeIH leftIH rightIH =>
      simp [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename,
        typeIH rho, leftIH rho, rightIH rho]
  | lam body bodyIH =>
      simp only [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename]
      congr 1
      rw [nativeLiftRen_eq_twoSortLiftRen rho]
      exact bodyIH _
  | app function argument functionIH argumentIH =>
      simp [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename,
        functionIH rho, argumentIH rho]
  | pair left right leftIH rightIH =>
      simp [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename,
        leftIH rho, rightIH rho]
  | fst pair pairIH =>
      simp [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, pairIH rho]
  | snd pair pairIH =>
      simp [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, pairIH rho]
  | refl value valueIH =>
      simp [embedTwoSort, nativeRename,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, valueIH rho]

/-- Lifting an embedded two-sort substitution agrees with embedding the intrinsic
two-sort lift. -/
theorem nativeLiftSub_embedTwoSortSub
    (substitution : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub
      source target) :
    nativeLiftSub (embedTwoSortSub substitution) =
      embedTwoSortSub
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.liftSub
          substitution) := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    exact nativeRename_embedTwoSort nativeWk stage (substitution previous)

/-- Native simultaneous substitution restricts exactly to the live intrinsic
two-sort simultaneous substitution. -/
theorem nativeSubst_embedTwoSort
    (substitution : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub
      source target) (stage : Nat) :
    ∀ term : ScopedTerm source,
      nativeSubst (embedTwoSortSub substitution) (embedTwoSort stage term) =
        embedTwoSort stage
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
            substitution term) := by
  intro term
  induction term generalizing target with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst]
      congr 1
      · exact domainIH substitution
      · rw [nativeLiftSub_embedTwoSortSub]
        exact bodyIH
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.liftSub
            substitution)
  | sigma domain body domainIH bodyIH =>
      simp only [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst]
      congr 1
      · exact domainIH substitution
      · rw [nativeLiftSub_embedTwoSortSub]
        exact bodyIH
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.liftSub
            substitution)
  | id type left right typeIH leftIH rightIH =>
      simp [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        typeIH substitution, leftIH substitution, rightIH substitution]
  | lam body bodyIH =>
      simp only [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst]
      congr 1
      rw [nativeLiftSub_embedTwoSortSub]
      exact bodyIH
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.liftSub substitution)
  | app function argument functionIH argumentIH =>
      simp [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        functionIH substitution, argumentIH substitution]
  | pair left right leftIH rightIH =>
      simp [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        leftIH substitution, rightIH substitution]
  | fst pair pairIH =>
      simp [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        pairIH substitution]
  | snd pair pairIH =>
      simp [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        pairIH substitution]
  | refl value valueIH =>
      simp [embedTwoSort, nativeSubst,
        Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        valueIH substitution]

/-- Partial erasure of a native term to the two-sort fragment.  Every genuinely
native constructor is rejected; mixed terms containing one are rejected
recursively. -/
def StagedReflectiveTm.twoSortProjection :
    {stage binders : Nat} → StagedReflectiveTm stage binders → Option (ScopedTerm binders)
  | _, _, .var index => some (.var index)
  | _, _, .const name => some (.const name)
  | _, _, .u0 => some .u0
  | _, _, .u1 => some .u1
  | _, _, .pi domain body => do
      let domain' ← domain.twoSortProjection
      let body' ← body.twoSortProjection
      pure (.pi domain' body')
  | _, _, .sigma domain body => do
      let domain' ← domain.twoSortProjection
      let body' ← body.twoSortProjection
      pure (.sigma domain' body')
  | _, _, .id type left right => do
      let type' ← type.twoSortProjection
      let left' ← left.twoSortProjection
      let right' ← right.twoSortProjection
      pure (.id type' left' right')
  | _, _, .lam body => return .lam (← body.twoSortProjection)
  | _, _, .app function argument =>
      return .app (← function.twoSortProjection) (← argument.twoSortProjection)
  | _, _, .pair left right =>
      return .pair (← left.twoSortProjection) (← right.twoSortProjection)
  | _, _, StagedReflectiveTm.fst value =>
      return ScopedTerm.fst (← value.twoSortProjection)
  | _, _, StagedReflectiveTm.snd value =>
      return ScopedTerm.snd (← value.twoSortProjection)
  | _, _, StagedReflectiveTm.refl value =>
      return ScopedTerm.refl (← value.twoSortProjection)
  | _, _, .letE _ _ => none
  | _, _, .pattern _ => none
  | _, _, .empty => none
  | _, _, .superpose _ _ => none
  | _, _, .language _ => none
  | _, _, .quote _ _ => none

@[simp] theorem twoSortProjection_embedTwoSort (stage : Nat) {binders : Nat}
    (term : ScopedTerm binders) :
    (embedTwoSort stage term).twoSortProjection = some term := by
  induction term with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH => simp [embedTwoSort, domainIH, bodyIH,
      StagedReflectiveTm.twoSortProjection]
  | sigma domain body domainIH bodyIH => simp [embedTwoSort, domainIH, bodyIH,
      StagedReflectiveTm.twoSortProjection]
  | id type left right typeIH leftIH rightIH => simp [embedTwoSort,
      typeIH, leftIH, rightIH, StagedReflectiveTm.twoSortProjection]
  | lam body bodyIH => simp [embedTwoSort, bodyIH,
      StagedReflectiveTm.twoSortProjection]
  | app function argument functionIH argumentIH => simp [embedTwoSort,
      functionIH, argumentIH, StagedReflectiveTm.twoSortProjection]
  | pair left right leftIH rightIH => simp [embedTwoSort, leftIH,
      rightIH, StagedReflectiveTm.twoSortProjection]
  | fst pair pairIH => simp [embedTwoSort, pairIH,
      StagedReflectiveTm.twoSortProjection]
  | snd pair pairIH => simp [embedTwoSort, pairIH,
      StagedReflectiveTm.twoSortProjection]
  | refl term termIH => simp [embedTwoSort, termIH,
      StagedReflectiveTm.twoSortProjection]

/-- The scoped two-sort fragment embeds conservatively into every native
stage. -/
theorem embedTwoSort_injective (stage : Nat) {binders : Nat} :
    Function.Injective (embedTwoSort stage : ScopedTerm binders → StagedReflectiveTm stage binders) := by
  intro left right equal
  have projected := congrArg StagedReflectiveTm.twoSortProjection equal
  simpa using projected

/-- Raw syntactic equality is reflected exactly by the two-sort embedding. -/
theorem embedTwoSort_eq_iff (stage : Nat) {binders : Nat}
    (left right : ScopedTerm binders) :
    embedTwoSort stage left = embedTwoSort stage right ↔ left = right :=
  ⟨fun equal => embedTwoSort_injective stage equal,
    fun equal => congrArg (embedTwoSort stage) equal⟩

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
stage components erase to the same two-sort environment. -/
def TwoSortProjectionStageConstant (substitution : NativeSub source target) : Prop :=
  ∀ first second index,
    (substitution first index).twoSortProjection =
      (substitution second index).twoSortProjection

/-- Negative witness: valid native substitutions need not arise by copying one
stage-local environment to every stage. -/
theorem stageSensitiveSub_not_projection_constant :
    ¬ TwoSortProjectionStageConstant stageSensitiveSub := by
  intro constant
  have equalProjections := constant 0 1 (0 : Fin 1)
  change (some ScopedTerm.u0 : Option (ScopedTerm 0)) = some ScopedTerm.u1 at equalProjections
  cases equalProjections

/-- Positive native-only witness: the new presentation contains staged code. -/
def quotedTwoSortUniverse : StagedReflectiveTm 0 0 :=
  .quote oneToZeroQuotation (.u0 : StagedReflectiveTm 1 0)

/-- Negative image witness: quotation is not an alternative spelling of any
scoped two-sort term. -/
theorem quotedTwoSortUniverse_not_in_twoSort_image :
    ¬ ∃ term : ScopedTerm 0, embedTwoSort 0 term = quotedTwoSortUniverse := by
  rintro ⟨term, equal⟩
  have projected := congrArg StagedReflectiveTm.twoSortProjection equal
  rw [twoSortProjection_embedTwoSort] at projected
  change (some term : Option (ScopedTerm 0)) = none at projected
  cases projected

/-- A mixed term demonstrates that two-sort operations act on genuinely native
subterms rather than treating the two-sort fragment as an opaque leaf. -/
def mixedNativeApplication : StagedReflectiveTm 0 0 :=
  .app (.lam (.var (0 : Fin 1))) quotedTwoSortUniverse

theorem mixedNativeApplication_not_in_twoSort_image :
    ¬ ∃ term : ScopedTerm 0, embedTwoSort 0 term = mixedNativeApplication := by
  rintro ⟨term, equal⟩
  have projected := congrArg StagedReflectiveTm.twoSortProjection equal
  rw [twoSortProjection_embedTwoSort] at projected
  change (some term : Option (ScopedTerm 0)) = none at projected
  cases projected

/-- Any term rejected by the two-sort projection is outside the conservative two-sort
image.  This one lemma supplies the negative half for every genuinely native
constructor. -/
theorem twoSortProjection_none_not_in_twoSort_image
    {stage binders : Nat} (native : StagedReflectiveTm stage binders)
    (notPure : native.twoSortProjection = none) :
    ¬ ∃ pure : ScopedTerm binders, embedTwoSort stage pure = native := by
  rintro ⟨pure, equal⟩
  have projected := congrArg StagedReflectiveTm.twoSortProjection equal
  rw [twoSortProjection_embedTwoSort, notPure] at projected
  cases projected

/-- Positive Pattern witness in the native raw presentation. -/
def nativeRuntimePattern : StagedReflectiveTm 0 0 :=
  .pattern familiesPatternMarker

theorem nativeRuntimePattern_not_in_twoSort_image :
    ¬ ∃ pure : ScopedTerm 0, embedTwoSort 0 pure = nativeRuntimePattern :=
  twoSortProjection_none_not_in_twoSort_image nativeRuntimePattern rfl

/-- Positive collection witness containing two distinct two-sort universes. -/
def nativeUniverseSuperposition : StagedReflectiveTm 0 0 :=
  .superpose .u0 .u1

theorem nativeUniverseSuperposition_not_in_twoSort_image :
    ¬ ∃ pure : ScopedTerm 0, embedTwoSort 0 pure = nativeUniverseSuperposition :=
  twoSortProjection_none_not_in_twoSort_image nativeUniverseSuperposition rfl


/-! ### The scoped two-sort contextual refinement

The raw native ABT has more substitutions than scoped two-sort: a native
substitution supplies one variable image at every stage, because substitution
under quotation must select the quotation source stage.  Intrinsic two-sort embeds
as the stage-uniform part.  This section retains two-sort's actual hypothetical
judgment and typed simultaneous substitutions, proves their laws, and maps
them faithfully into the native support category.

This is deliberately not the modal typing presentation constructed below.
In particular, it does not manufacture a Fitch lock from quotation: the
negative non-fullness theorem below exhibits a native stage-sensitive
substitution that no scoped two-sort context morphism can supply. -/

namespace TwoSortPiSigmaIdRefinement

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open _root_.CategoryTheory
open scoped _root_.CategoryTheory

/-- Typed identity substitution for the live scoped two-sort judgment. -/
theorem ctxMor_ids (context : Ctx binders) :
    CtxMor context context (ids (n := binders)) := by
  intro index
  change HasType context (.var index) (subst ids (lookup context index))
  rw [subst_ids]
  exact HasType.var index

/-- Execution-order composition of scoped two-sort substitutions. -/
def twoSortSubComp (later : Sub middle target) (earlier : Sub source middle) :
    Sub source target :=
  fun index => subst later (earlier index)

/-- Typed context morphisms are closed under simultaneous-substitution
composition. -/
theorem ctxMor_comp {sourceContext : Ctx source}
    {middleContext : Ctx middle} {targetContext : Ctx target}
    {earlier : Sub source middle} {later : Sub middle target}
    (earlierTyped : CtxMor sourceContext middleContext earlier)
    (laterTyped : CtxMor middleContext targetContext later) :
    CtxMor sourceContext targetContext (twoSortSubComp later earlier) := by
  intro index
  have typed := typing_subst (earlierTyped index) laterTyped
  rw [subst_comp] at typed
  change HasType targetContext (subst later (earlier index))
    (subst (fun inner => subst later (earlier inner))
      (lookup sourceContext index))
  exact typed

/-- One intrinsically typed two-sort context, retaining its telescope length. -/
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

/-- Intrinsic two-sort contexts and typed substitutions form a category. -/
instance : CategoryTheory.Category ContextObject where
  Hom := TypedSub
  id object := ⟨ids, ctxMor_ids object.context⟩
  comp earlier later :=
    ⟨twoSortSubComp later.map earlier.map,
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

/-- Embedding commutes with composition of two-sort substitutions. -/
theorem embedTwoSortSub_comp (later : Sub middle target)
    (earlier : Sub source middle) :
    embedTwoSortSub (twoSortSubComp later earlier) =
      nativeSubComp (embedTwoSortSub later) (embedTwoSortSub earlier) := by
  funext stage index
  exact (nativeSubst_embedTwoSort later stage (earlier index)).symm

/-- Forget the telescope types while retaining the complete staged native
substitution.  This is the contextual refinement map into the support-indexed
ABT substitution category. -/
def toNativeSupport : CategoryTheory.Functor ContextObject NativeSupport where
  obj object := ⟨object.arity⟩
  map substitution := embedTwoSortSub substitution.map
  map_id object := by
    funext stage index
    rfl
  map_comp earlier later := embedTwoSortSub_comp later.map earlier.map

/-- The contextual refinement is faithful: native equality of embedded typed
substitutions reflects equality of the scoped two-sort maps. -/
theorem toNativeSupport_map_injective
    {source target : ContextObject} :
    Function.Injective
      (fun substitution : TypedSub source target =>
        toNativeSupport.map substitution) := by
  intro left right equal
  apply TypedSub.ext
  funext index
  have component := congrFun (congrFun equal 0) index
  exact embedTwoSort_injective 0 component

/-- Proof-relevant refinement of one scoped two-sort hypothetical judgment
into native raw syntax at a selected stage.  The original derivation is
retained together with exact source-term and source-type equations. -/
structure TypingAt (stage : Nat) (context : Ctx binders)
    (term type : StagedReflectiveTm stage binders) where
  sourceTerm : ScopedTerm binders
  sourceType : ScopedTerm binders
  sourceTyping : HasType context sourceTerm sourceType
  term_eq : term = embedTwoSort stage sourceTerm
  type_eq : type = embedTwoSort stage sourceType

/-- Embedded typing is reflected exactly; the refinement does not create new
two-sort derivations on the two-sort image. -/
theorem typingAt_embed_iff (stage : Nat) (context : Ctx binders)
    (term type : ScopedTerm binders) :
    Nonempty (TypingAt stage context (embedTwoSort stage term)
      (embedTwoSort stage type)) ↔ HasType context term type := by
  constructor
  · rintro ⟨refinement⟩
    have termEqual : term = refinement.sourceTerm :=
      embedTwoSort_injective stage refinement.term_eq
    have typeEqual : type = refinement.sourceType :=
      embedTwoSort_injective stage refinement.type_eq
    simpa [termEqual, typeEqual] using refinement.sourceTyping
  · intro typed
    exact ⟨⟨term, type, typed, rfl, rfl⟩⟩

/-- Typed simultaneous substitution commutes with the refinement map.  The
result uses two-sort's real `typing_subst` theorem and the previously proved ABT
substitution square. -/
def TypingAt.subst {stage : Nat} {sourceContext : Ctx source}
    {targetContext : Ctx target} {term type : StagedReflectiveTm stage source}
    (typing : TypingAt stage sourceContext term type)
    (substitution : Sub source target)
    (substitutionTyped : CtxMor sourceContext targetContext substitution) :
    TypingAt stage targetContext
      (nativeSubst (embedTwoSortSub substitution) term)
      (nativeSubst (embedTwoSortSub substitution) type) where
  sourceTerm :=
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
      substitution typing.sourceTerm
  sourceType :=
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst
      substitution typing.sourceType
  sourceTyping := typing_subst typing.sourceTyping substitutionTyped
  term_eq :=
    (congrArg (nativeSubst (embedTwoSortSub substitution)) typing.term_eq).trans
      (nativeSubst_embedTwoSort substitution stage typing.sourceTerm)
  type_eq :=
    (congrArg (nativeSubst (embedTwoSortSub substitution)) typing.type_eq).trans
      (nativeSubst_embedTwoSort substitution stage typing.sourceType)

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

/-- Positive contextual witness: two-sort's universe judgment embeds at every
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
an alternative encoding of one two-sort typed substitution. -/
theorem stageSensitiveEndSub_has_no_typedTwoSort_preimage :
    ¬ ∃ substitution : TypedSub oneUniverseContext oneUniverseContext,
      toNativeSupport.map substitution = stageSensitiveEndSub := by
  rintro ⟨substitution, equal⟩
  let index : Fin oneUniverseContext.arity := ⟨0, by decide⟩
  have atZero := congrFun (congrFun equal 0) index
  have atOne := congrFun (congrFun equal 1) index
  change embedTwoSort 0 (substitution.map index) =
    embedTwoSort 0 (ScopedTerm.var index) at atZero
  change embedTwoSort 1 (substitution.map index) =
    embedTwoSort 1 ScopedTerm.u0 at atOne
  have zeroSource : substitution.map index = ScopedTerm.var index :=
    embedTwoSort_injective 0 atZero
  have oneSource : substitution.map index = ScopedTerm.u0 :=
    embedTwoSort_injective 1 atOne
  have impossible : ScopedTerm.var index = .u0 :=
    zeroSource.symm.trans oneSource
  cases impossible

/-- Native quotation is outside the intrinsic typed refinement, independently
of which native type one proposes for it.  Typing quotation therefore uses the
genuine modal context/lock rules of the native judgment below. -/
theorem quotedTwoSortUniverse_has_no_intrinsic_typing :
    ¬ ∃ type : StagedReflectiveTm 0 0,
      Nonempty (TypingAt 0 .nil quotedTwoSortUniverse type) := by
  rintro ⟨type, refinement⟩
  rcases refinement with ⟨refinement⟩
  apply quotedTwoSortUniverse_not_in_twoSort_image
  exact ⟨refinement.sourceTerm, refinement.term_eq.symm⟩

end TwoSortPiSigmaIdRefinement

/-! ### A modal hypothetical judgment over the native ABT

Intrinsic two-sort supplies the dependent core, but quotation crosses interpreter
stages.  A variable occurring below a quotation therefore needs an image at
the quotation's source stage.  The native substitution algebra already
records exactly this data: `NativeSub source target` is indexed by stage.

The contextual presentation below follows that fact rather than pretending a
single-stage argument can be retyped at every stage.  Context entries and
substitutable arguments are stage-indexed families.  Conversion is an
explicit parameter whose only laws here are equivalence and substitution
stability.  This candidate's architecture later uses syntactic conversion as
its kernel core and exposes stronger policies only through explicit
extension. -/

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
two-sort, while `quote_intro` is a genuine modal rule and collections, Patterns,
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

/-! #### Intrinsic two-sort is a guest fragment, not the modal judgment itself

The embedding below is conditional only at conversion: a native policy must
contain every conversion used by scoped two-sort.  The raw constructors,
contexts, dependent binders, and typing rules then map structurally.  Keeping
this premise explicit prevents the two-sort conversion closure from being silently
declared to be the native kernel equality. -/

/-- Embed a live scoped two-sort telescope as a stage-uniform native modal
telescope. -/
def embedTwoSortContext :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx binders →
      Context binders
  | .nil => .nil
  | .snoc context type =>
      .snoc (embedTwoSortContext context) (fun stage => embedTwoSort stage type)

/-- Lookup in the embedded telescope is exactly embedded intrinsic lookup. -/
theorem lookup_embedTwoSortContext
    (context : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx binders)
    (stage : Nat) (index : Fin binders) :
    (embedTwoSortContext context).lookup stage index =
      embedTwoSort stage
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.lookup context index) := by
  induction context with
  | nil => exact Fin.elim0 index
  | @snoc binders context type contextIH =>
      refine Fin.cases ?_ ?_ index
      · change nativeRename nativeWk (embedTwoSort stage type) =
          embedTwoSort stage
            (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename
              Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk type)
        exact nativeRename_embedTwoSort nativeWk stage type
      · intro previous
        change nativeRename nativeWk
            ((embedTwoSortContext context).lookup stage previous) =
          embedTwoSort stage
            (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename
              Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk
              (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.lookup
                context previous))
        rw [contextIH previous]
        exact nativeRename_embedTwoSort nativeWk stage _

/-- Native newest-variable substitution of stage-uniform two-sort syntax is the
stagewise embedding of scoped two-sort's newest-variable substitution. -/
theorem subst0_embedTwoSort (argument : ScopedTerm binders) :
    subst0 (fun stage => embedTwoSort stage argument) =
      embedTwoSortSub
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst0 argument) := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

/-- Binder instantiation commutes with the two-sort-to-native embedding. -/
@[simp] theorem inst0_embedTwoSort (argument : ScopedTerm binders)
    (body : ScopedTerm (binders + 1)) (stage : Nat) :
    inst0 (fun current => embedTwoSort current argument) (embedTwoSort stage body) =
      embedTwoSort stage
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.inst0
          argument body) := by
  unfold inst0
  rw [subst0_embedTwoSort]
  exact nativeSubst_embedTwoSort
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst0 argument)
    stage body

/-- The dependent second projection uses the embedded first projection as
its newest-variable argument. -/
@[simp] theorem inst0_fst_embedTwoSort (pair : ScopedTerm binders)
    (body : ScopedTerm (binders + 1)) (stage : Nat) :
    inst0 (fun current => .fst (embedTwoSort current pair))
        (embedTwoSort stage body) =
      embedTwoSort stage
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.inst0
          (.fst pair) body) := by
  change inst0 (fun current => embedTwoSort current (.fst pair))
      (embedTwoSort stage body) = _
  exact inst0_embedTwoSort (.fst pair) body stage

/-- The exact additional premise needed to host scoped two-sort typing at one
native conversion policy.  It is inclusion, not identification, of the two
conversion relations. -/
def ExtendsTwoSortPiSigmaId (conversion : ConversionPolicy) : Prop :=
  ∀ {stage binders : Nat} {left right : ScopedTerm binders},
    TwoSortPiSigmaIdConv left right →
      conversion.Rel (embedTwoSort stage left) (embedTwoSort stage right)

/-- Every scoped two-sort typing derivation maps to the authored native modal
judgment when the selected native conversion contains two-sort conversion.  The
result is quantified over stages, which supplies the coherent term families
needed by dependent elimination under quotation. -/
theorem typing_embedTwoSort {conversion : ConversionPolicy}
    (containsTwoSort : ExtendsTwoSortPiSigmaId conversion)
    {context : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx binders}
    {term type : ScopedTerm binders}
    (typing :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType context term type) :
    ∀ stage,
      HasType conversion (embedTwoSortContext context)
        (embedTwoSort stage term) (embedTwoSort stage type) := by
  induction typing with
  | u0_type context =>
      intro stage
      exact .u0_type (embedTwoSortContext context)
  | @var binders context index =>
      intro stage
      simpa only [embedTwoSort, lookup_embedTwoSortContext] using
        (HasType.var (conversion := conversion)
          (context := embedTwoSortContext context) index)
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
      simpa only [embedTwoSort, inst0_embedTwoSort] using
        (HasType.app_elim
          (functionIH stage)
          (fun current => argumentIH current))
  | @pair_intro binders context left right domain bodyType
      leftTyping rightTyping leftIH rightIH =>
      intro stage
      have embeddedRight := rightIH stage
      rw [← inst0_embedTwoSort left bodyType stage] at embeddedRight
      simpa only [embedTwoSort] using
        (HasType.pair_intro
          (left := fun current => embedTwoSort current left)
          (right := fun current => embedTwoSort current right)
          (domain := fun current => embedTwoSort current domain)
          (bodyType := embedTwoSort stage bodyType)
          (leftIH stage) embeddedRight)
  | @fst_elim binders context pair domain bodyType pairTyping pairIH =>
      intro stage
      simpa only [embedTwoSort] using
        (HasType.fst_elim
          (pair := fun current => embedTwoSort current pair)
          (domain := fun current => embedTwoSort current domain)
          (bodyType := embedTwoSort stage bodyType)
          (pairIH stage))
  | @snd_elim binders context pair domain bodyType pairTyping pairIH =>
      intro stage
      simpa only [embedTwoSort, inst0_fst_embedTwoSort] using
        (HasType.snd_elim
          (pair := fun current => embedTwoSort current pair)
          (domain := fun current => embedTwoSort current domain)
          (bodyType := embedTwoSort stage bodyType)
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
      exact .conv (termIH stage) (containsTwoSort related)

/-- Syntactic native conversion cannot host scoped two-sort's beta rule.  This
is the negative witness showing why conversion inclusion is a real premise. -/
theorem syntacticConversion_does_not_extend_twoSortPiSigmaId :
    ¬ ExtendsTwoSortPiSigmaId syntacticConversion := by
  intro containsTwoSort
  have related :=
    containsTwoSort (stage := 0) twoSortPiSigmaIdConversionProfile_beta
  change embedTwoSort 0
      (ScopedTerm.app (ScopedTerm.lam (ScopedTerm.var (0 : Fin 1))) ScopedTerm.u0) =
    embedTwoSort 0 (ScopedTerm.u0 : ScopedTerm 0) at related
  have impossible := embedTwoSort_injective 0 related
  cases impossible

/-- Native quotation receives an authored modal typing that the intrinsic
two-sort refinement cannot express. -/
theorem quotedTwoSortUniverse_has_native_modal_type :
    HasType syntacticConversion .nil quotedTwoSortUniverse
      (.quote oneToZeroQuotation (.u1 : StagedReflectiveTm 1 0)) := by
  exact .quote_intro oneToZeroQuotation
    (.u0_type (.lock oneToZeroQuotation .nil))

/-- The positive modal typing and the intrinsic negative witness coexist: the
bridge relates the layers without identifying them. -/
theorem quotation_typing_separates_native_from_intrinsic :
    HasType syntacticConversion .nil quotedTwoSortUniverse
        (.quote oneToZeroQuotation (.u1 : StagedReflectiveTm 1 0)) ∧
      ¬ ∃ type : StagedReflectiveTm 0 0,
        Nonempty
          (TwoSortPiSigmaIdRefinement.TypingAt 0 .nil quotedTwoSortUniverse type) :=
  ⟨quotedTwoSortUniverse_has_native_modal_type,
    TwoSortPiSigmaIdRefinement.quotedTwoSortUniverse_has_no_intrinsic_typing⟩

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
      (nativeRawFold model.raw quotedTwoSortUniverse)
      (nativeRawFold model.raw
        (.quote oneToZeroQuotation (.u1 : StagedReflectiveTm 1 0))) :=
  fold_typing model quotedTwoSortUniverse_has_native_modal_type

end NativeTypedInitiality

/-! ### Faithful raw contact with the live runtime Pattern interface

The native syntax does not validate itself by mapping back into another copy
of its own datatype.  This decoder targets the actual MeTTaIL `Pattern`
carrier used by the current staged-reflective candidate presentation.  It characterizes precisely
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


/-- Negative source-image witness: staged quotation is not silently decoded
as a runtime Pattern. -/
theorem quotedTwoSortUniverse_not_runtimePattern_image :
    ¬ ∃ value : Pattern,
      (embedRuntimePattern value : StagedReflectiveTm 0 0) = quotedTwoSortUniverse := by
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
    (NativeDecoratedTm.withCost quotedTwoSortUniverse
        (stageRouteCost oneToZeroQuotation)).term = quotedTwoSortUniverse ∧
      NativeDecoratedTm.withCost quotedTwoSortUniverse
          (stageRouteCost oneToZeroQuotation) ≠
        NativeDecoratedTm.undecorated quotedTwoSortUniverse := by
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
  atStage := fun _ => twoSortNodeCountAlgebra
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
      twoSortNodeCountAlgebra]

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

/-! ### This candidate's equality architecture

Within this staged-reflective candidate, the intensional conversion policy is
the sole core equality.  Stronger equalities are explicit profile values
equipped with typed inclusions from this core.  No stronger profile is
selected as production equality here.  This record specifies one comparison
architecture; it does not select Prime's equality or settle its identity
scope.  Function extensionality, K/UIP, cubical composition, and univalence
require the corresponding profile and laws explicitly. -/

/-- The staged-reflective comparison architecture as data: one fixed
intensional core, a family of explicit extensions, and a strict noncollapsed
calibration point.  The field fixing the core and the absence of a selected
stronger profile are assumptions of this interface, not derived design
necessities. -/
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

/-- The architecture value used by this staged-reflective candidate.
`nativeBooleanEqualityProfile` is only the strict calibration witness, and
`selectedStrongerProfile = none` records that it is not this candidate's
production conversion.  This value is not a family-wide selection. -/
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

/-- This candidate architecture records no stronger production equality
profile; it does not resolve selection for other candidates. -/
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

/-- The two-sort fragment of the graded raw algebra at one interpreter stage. -/
abbrev nativeTwoSortGradedCostAlgebra (stage : Nat) : TwoSortRawAlgebra where
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
  atStage := nativeTwoSortGradedCostAlgebra
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
theorem primitiveLetTypingDerivation :
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

/-- Reflection depth for the two-sort fragment.  Ordinary type-theoretic
constructors combine the maximum depth of their children. -/
abbrev nativeTwoSortReflectiveDepthAlgebra : TwoSortRawAlgebra where
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
  atStage := fun _ => nativeTwoSortReflectiveDepthAlgebra
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


/-- Negative fragment witness: ordinary staged code is not misclassified as
a quoted language presentation. -/
theorem quotedTwoSortUniverse_not_quotedLanguage :
    quotedTwoSortUniverse.quotedLanguage? = none :=
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
  rejectsNonLanguage : quotedTwoSortUniverse.quotedLanguage? = none

def nativeQuoteCodeUnificationWitness : QuoteCodeUnificationWitness where
  quoteAtNext := nativeQuoteNext
  quoteAtNext_eq := by intros; rfl
  strictlyRaises := nativeQuoteNext_strictly_raises
  quoteLanguage := nativeQuotedLanguage
  languageUsesCommonQuote := by intros; rfl
  languageRoundtrip := quotedLanguage?_nativeQuotedLanguage
  rejectsNonLanguage := quotedTwoSortUniverse_not_quotedLanguage

/-- Positive witness: the extension's structural interpretation observes both
the two-sort application spine and the quotation node. -/
theorem mixedNativeApplication_node_count :
    nativeNodeCount mixedNativeApplication = 5 := rfl

/-- Unit carrier at every stage, used only as a negative initiality witness. -/
abbrev nativeUnitAlgebra : NativeRawAlgebra where
  atStage := fun _ => twoSortUnitAlgebra
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
  have mapsU0 := (hom.preserves.twoSortFormers 0).map_u0 (n := 0)
  have mapsU1 := (hom.preserves.twoSortFormers 0).map_u1 (n := 0)
  have universesEqual : (StagedReflectiveTm.u0 : StagedReflectiveTm 0 0) = .u1 :=
    mapsU0.symm.trans mapsU1
  cases universesEqual

/-- An equality profile is compatible with a native algebra at one stage when
the stage's two-sort fold identifies every equation in that profile.  This keeps
optional extensions explicit rather than selecting one in raw syntax. -/
def NativeRawAlgebra.CompatibleWithTwoSortProfileAt
    (target : NativeRawAlgebra.{uRawTarget}) (stage : Nat)
    (profile : TwoSortEqualityProfile) : Prop :=
  ∀ {binders} {left right : ScopedTerm binders}, profile.Rel left right →
    twoSortRawFold (target.atStage stage) left =
      twoSortRawFold (target.atStage stage) right

/-- Folding the embedded two-sort fragment through a native algebra agrees with
the ordinary two-sort fold into that stage. -/
theorem nativeRawFold_embedTwoSort
    (target : NativeRawAlgebra.{uRawTarget}) (stage : Nat)
    {binders : Nat} (term : ScopedTerm binders) :
    nativeRawFold target (embedTwoSort stage term) =
      twoSortRawFold (target.atStage stage) term := by
  induction term with
  | var index => rfl
  | const name => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH => simp [embedTwoSort, twoSortRawFold,
      nativeRawFold, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH => simp [embedTwoSort, twoSortRawFold,
      nativeRawFold, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH => simp [embedTwoSort, twoSortRawFold,
      nativeRawFold, typeIH, leftIH, rightIH]
  | lam body bodyIH => simp [embedTwoSort, twoSortRawFold, nativeRawFold, bodyIH]
  | app function argument functionIH argumentIH => simp [embedTwoSort, twoSortRawFold,
      nativeRawFold, functionIH, argumentIH]
  | pair left right leftIH rightIH => simp [embedTwoSort, twoSortRawFold,
      nativeRawFold, leftIH, rightIH]
  | fst pair pairIH => simp [embedTwoSort, twoSortRawFold, nativeRawFold, pairIH]
  | snd pair pairIH => simp [embedTwoSort, twoSortRawFold, nativeRawFold, pairIH]
  | refl term termIH => simp [embedTwoSort, twoSortRawFold, nativeRawFold, termIH]

/-- Positive equality-neutral point: the free native syntax accepts the finest
syntactic two-sort equality profile at every stage. -/
theorem nativeSyntax_compatible_syntactic (stage : Nat) :
    nativeSyntaxAlgebra.CompatibleWithTwoSortProfileAt stage
      syntacticEqualityProfile := by
  intro binders left right equal
  have termsEqual := (syntacticEqualityProfile_rel_iff left right).mp equal
  subst right
  rfl

/-- Negative equality witness: a profile collapsing the two two-sort universes
cannot be interpreted by the free native syntax at any stage. -/
theorem nativeSyntax_incompatible_with_universe_collapse
    (stage : Nat) (profile : TwoSortEqualityProfile)
    (collapses : profile.Rel (ScopedTerm.u0 : ScopedTerm 0) ScopedTerm.u1) :
    ¬ nativeSyntaxAlgebra.CompatibleWithTwoSortProfileAt stage profile := by
  intro compatible
  have equalUniverses := compatible collapses
  change (StagedReflectiveTm.u0 : StagedReflectiveTm stage 0) = .u1 at equalUniverses
  cases equalUniverses

/-! ## §8 The candidate and its audit -/

/-- Candidate data within the selected modal-CwF interface.  This structure
does not characterize all possible MeTTa type-theory architectures. -/
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


end Mettapedia.TypeTheory.Calculi.StagedScopedReflective
