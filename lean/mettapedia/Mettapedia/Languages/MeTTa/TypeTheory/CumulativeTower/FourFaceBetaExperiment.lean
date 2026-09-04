import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionReflection
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypedBetaSubjectReduction

/-!
# One typed beta law across four independent faces

This experiment follows one nondependent fragment of the cumulative tower
through four representations:

* an intrinsically typed simple-function syntax;
* the cumulative-tower DTT calculus;
* the declaration-aware first-order GSLT substitution checker;
* an extensional function semantics and its set-valued graph.

The semantic faces are defined without reference to checker acceptance or DTT
derivability.  The bridge proves that the canonical open identity beta step is
the same event in all four faces.  A singleton ground model supplies a negative
reflection control: extensional validity alone need not recover raw syntax.

This is a deliberately small experiment, not yet a semantic model of the full
cumulative tower and not an implementation of Megalodon HOTG.  Its set-valued
face isolates the exact preservation and reflection obligations that such a
realization must later discharge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FourFaceBetaExperiment

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Face 0: a small intrinsically typed function fragment -/

namespace IntrinsicSTT

/-- The simple types used only to select a nondependent comparison fragment. -/
inductive Ty where
  | atom : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- Typed de Bruijn variables.  Context lists put the newest variable first. -/
inductive Var : List Ty → Ty → Type where
  | zero {type context} : Var (type :: context) type
  | succ {context type other} : Var context type → Var (other :: context) type

/-- Intrinsically typed variables, lambdas, and applications. -/
inductive Term : List Ty → Ty → Type where
  | var {context type} : Var context type → Term context type
  | lam {domain context codomain} : Term (domain :: context) codomain →
      Term context (.arr domain codomain)
  | app {context domain codomain} :
      Term context (.arr domain codomain) → Term context domain →
      Term context codomain

universe u

variable {Γ Δ Θ : List Ty}
variable {A B C D : Ty}
variable {Ground : Type u}

abbrev Renaming (sourceContext targetContext : List Ty) : Type :=
  ∀ {selectedType}, Var sourceContext selectedType →
    Var targetContext selectedType

def weakening : Renaming Γ (B :: Γ) :=
  fun {_selectedType} typedVar => .succ typedVar

def liftRenaming (rho : Renaming Γ Δ) :
    Renaming (B :: Γ) (B :: Δ) :=
  fun {_selectedType} typedVar =>
    match typedVar with
    | .zero => .zero
    | .succ prior => .succ (rho prior)

def Term.rename : {sourceContext targetContext : List Ty} →
    Renaming sourceContext targetContext → {selectedType : Ty} →
      Term sourceContext selectedType → Term targetContext selectedType
  | _, _, rho, _, .var typedVar => .var (rho typedVar)
  | _, _, rho, _, .lam body =>
      .lam (Term.rename (liftRenaming rho) body)
  | _, _, rho, _, .app function argument =>
      .app (Term.rename rho function) (Term.rename rho argument)

abbrev Substitution (sourceContext targetContext : List Ty) : Type :=
  ∀ {selectedType}, Var sourceContext selectedType →
    Term targetContext selectedType

def liftSubstitution (sigma : Substitution Γ Δ) :
    Substitution (B :: Γ) (B :: Δ) :=
  fun {_selectedType} typedVar =>
    match typedVar with
    | .zero => .var .zero
    | .succ prior => (sigma prior).rename weakening

def Term.substitute : {sourceContext targetContext : List Ty} →
    Substitution sourceContext targetContext → {selectedType : Ty} →
      Term sourceContext selectedType → Term targetContext selectedType
  | _, _, sigma, _, .var typedVar => sigma typedVar
  | _, _, sigma, _, .lam body =>
      .lam (Term.substitute (liftSubstitution sigma) body)
  | _, _, sigma, _, .app function argument =>
      .app (Term.substitute sigma function) (Term.substitute sigma argument)

def newestSubstitution (argument : Term Γ A) :
    Substitution (A :: Γ) Γ :=
  fun {_selectedType} typedVar =>
    match typedVar with
    | .zero => argument
    | .succ prior => .var prior

/-- Intrinsic capture-avoiding opening of the newest variable. -/
def Term.instantiateNewest (body : Term (A :: Γ) B)
    (argument : Term Γ A) : Term Γ B :=
  body.substitute (newestSubstitution argument)

/-- A typed root beta claim.  Its indices rule out ill-typed endpoints. -/
structure BetaClaim (context : List Ty) (domain codomain : Ty) where
  body : Term (domain :: context) codomain
  argument : Term context domain

def BetaClaim.source
    (claim : BetaClaim Γ A B) : Term Γ B :=
  .app (.lam claim.body) claim.argument

def BetaClaim.target
    (claim : BetaClaim Γ A B) : Term Γ B :=
  claim.body.instantiateNewest claim.argument

/-! ## Independent extensional function semantics -/

/-- Interpret the single atomic type by an arbitrary carrier and arrows by
ordinary functions. -/
def Ty.denote (Ground : Type u) : Ty → Type u
  | .atom => Ground
  | .arr domain codomain => domain.denote Ground → codomain.denote Ground

/-- A semantic environment assigns a value to every typed variable. -/
structure Environment (Ground : Type u) (context : List Ty) where
  lookup : ∀ {selectedType},
    Var context selectedType → selectedType.denote Ground

@[ext] theorem Environment.ext
    {left right : Environment Ground Γ}
    (pointwise : ∀ (selectedType) (typedVar : Var Γ selectedType),
      left.lookup typedVar = right.lookup typedVar) :
    left = right := by
  cases left with
  | mk leftLookup =>
      cases right with
      | mk rightLookup =>
          congr
          funext selectedType typedVar
          exact pointwise selectedType typedVar

def Environment.extend (value : A.denote Ground)
    (environment : Environment Ground Γ) :
    Environment Ground (A :: Γ) where
  lookup := fun {_selectedType} typedVar =>
      match typedVar with
      | .zero => value
      | .succ prior => environment.lookup prior

/-- The shallow STT interpretation. -/
def Term.denote : {Ground : Type u} → {context : List Ty} →
    {selectedType : Ty} → Term context selectedType →
      Environment Ground context → selectedType.denote Ground
  | _, _, _, .var typedVar, environment => environment.lookup typedVar
  | _, _, _, .lam body, environment =>
      fun value => Term.denote body (Environment.extend value environment)
  | _, _, _, .app function argument, environment =>
      Term.denote function environment (Term.denote argument environment)

def renamingEnvironment (rho : Renaming Γ Δ)
    (environment : Environment Ground Δ) : Environment Ground Γ where
  lookup := fun typedVar => environment.lookup (rho typedVar)

def substitutionEnvironment (sigma : Substitution Γ Δ)
    (environment : Environment Ground Δ) : Environment Ground Γ where
  lookup := fun typedVar => (sigma typedVar).denote environment

@[simp] theorem Term.denote_rename
    (term : Term Γ A) (rho : Renaming Γ Δ)
    (environment : Environment Ground Δ) :
    (term.rename rho).denote environment =
      term.denote (renamingEnvironment rho environment) := by
  induction term generalizing Δ with
  | var typedVar => rfl
  | @lam context domain codomain body induction =>
      simp only [Term.rename, Term.denote]
      apply funext
      intro value
      rw [induction]
      apply congrArg (fun nextEnvironment => body.denote nextEnvironment)
      apply Environment.ext
      intro nextType typedVar
      cases typedVar <;> rfl
  | app function argument functionInduction argumentInduction =>
      simp [Term.rename, Term.denote, functionInduction,
        argumentInduction]

@[simp] theorem substitutionEnvironment_lift
    (sigma : Substitution Γ Δ)
    (environment : Environment Ground Δ)
    (value : B.denote Ground) :
    substitutionEnvironment (liftSubstitution sigma)
        (Environment.extend value environment) =
      Environment.extend value
        (substitutionEnvironment sigma environment) := by
  apply Environment.ext
  intro selectedType typedVar
  cases typedVar with
  | zero => rfl
  | succ prior =>
      simp only [substitutionEnvironment, liftSubstitution,
        Term.denote_rename]
      rfl

@[simp] theorem Term.denote_substitute
    (term : Term Γ A) (sigma : Substitution Γ Δ)
    (environment : Environment Ground Δ) :
    (term.substitute sigma).denote environment =
      term.denote (substitutionEnvironment sigma environment) := by
  induction term generalizing Δ with
  | var typedVar => rfl
  | @lam context domain codomain body induction =>
      simp only [Term.substitute, Term.denote]
      apply funext
      intro value
      rw [induction, substitutionEnvironment_lift]
  | app function argument functionInduction argumentInduction =>
      simp only [Term.substitute, Term.denote, functionInduction,
        argumentInduction]

@[simp] theorem substitutionEnvironment_newest
    (argument : Term Γ A)
    (environment : Environment Ground Γ) :
    substitutionEnvironment (newestSubstitution argument) environment =
      Environment.extend (argument.denote environment) environment := by
  apply Environment.ext
  intro selectedType typedVar
  cases typedVar <;> rfl

/-- Semantic substitution is exact, hence every intrinsic beta claim is valid
in every carrier interpretation. -/
theorem BetaClaim.shallowValid
    (claim : BetaClaim Γ A B)
    (environment : Environment Ground Γ) :
    claim.source.denote environment = claim.target.denote environment := by
  change
    claim.body.denote
        (Environment.extend (claim.argument.denote environment) environment) =
      (claim.body.substitute
        (newestSubstitution claim.argument)).denote environment
  rw [Term.denote_substitute, substitutionEnvironment_newest]

/-! ## The set-valued graph face -/

/-- The graph of a term's extensional environment-to-value map. -/
def Term.graph (term : Term Γ A) (Ground : Type u) :
    Set (Environment Ground Γ × A.denote Ground) :=
  { pair | pair.2 = term.denote pair.1 }

/-- Equality of set-valued graphs is exactly pointwise shallow equality. -/
theorem Term.graph_eq_iff
    (left right : Term Γ A) (Ground : Type u) :
    left.graph Ground = right.graph Ground ↔
      ∀ environment : Environment Ground Γ,
        left.denote environment = right.denote environment := by
  constructor
  · intro graphsEqual environment
    have member :
        ((environment, left.denote environment) :
          Environment Ground Γ × A.denote Ground) ∈ left.graph Ground := rfl
    rw [graphsEqual] at member
    exact member
  · intro pointwise
    ext pair
    simp only [Term.graph, Set.mem_setOf_eq]
    constructor
    · intro equalLeft
      exact equalLeft.trans (pointwise pair.1)
    · intro equalRight
      exact equalRight.trans (pointwise pair.1).symm

theorem BetaClaim.setGraphValid
    (claim : BetaClaim Γ A B) (Ground : Type u) :
    claim.source.graph Ground = claim.target.graph Ground :=
  (Term.graph_eq_iff claim.source claim.target Ground).2
    (fun environment => claim.shallowValid environment)

end IntrinsicSTT

/-! ## Face 1: faithful erasure into the cumulative-tower DTT fragment -/

namespace TowerDTT

open IntrinsicSTT

variable {sourceArity targetArity arity : Nat}
variable {context : List IntrinsicSTT.Ty}
variable {selectedType : IntrinsicSTT.Ty}

/-- All selected simple types are closed cumulative-tower types.  Their universe level is
retained rather than forced to a single syntactic level expression. -/
def levelOf : IntrinsicSTT.Ty → LevelExpr
  | .atom => Presentation.Tower.zero
  | .arr domain codomain => .max (levelOf domain) (levelOf codomain)

def eraseTypeAt (arity : Nat) :
    IntrinsicSTT.Ty → Presentation.Tower.Tm arity
  | .atom => .head .legacyGround
  | .arr domain codomain =>
      .pi (eraseTypeAt arity domain) (eraseTypeAt (arity + 1) codomain)

@[simp] theorem eraseTypeAt_rename (type : IntrinsicSTT.Ty)
    (rho : Presentation.Ren sourceArity targetArity) :
    Presentation.rename rho (eraseTypeAt sourceArity type) =
      eraseTypeAt targetArity type := by
  induction type generalizing sourceArity targetArity with
  | atom => rfl
  | arr domain codomain domainInduction codomainInduction =>
      simp [eraseTypeAt, Presentation.rename, domainInduction,
        codomainInduction]

@[simp] theorem eraseTypeAt_subst (type : IntrinsicSTT.Ty)
    (substitution : Presentation.Sub Presentation.Tower.Head
      sourceArity targetArity) :
    Presentation.subst substitution (eraseTypeAt sourceArity type) =
      eraseTypeAt targetArity type := by
  induction type generalizing sourceArity targetArity with
  | atom => rfl
  | arr domain codomain domainInduction codomainInduction =>
      simp [eraseTypeAt, Presentation.subst, domainInduction,
        codomainInduction]

theorem eraseTypeAt_hasType (type : IntrinsicSTT.Ty)
    (context : Presentation.Tower.Ctx arity) :
    Presentation.Tower.HasType context (eraseTypeAt arity type)
      (sortTm (levelOf type)) := by
  induction type generalizing arity with
  | atom => exact .headType .legacyGround
  | arr domain codomain domainInduction codomainInduction =>
      exact .piForm
        (domainInduction context) (.sort (levelOf domain))
        (codomainInduction (.snoc context (eraseTypeAt arity domain)))
          (.sort (levelOf codomain))
        (.sorts (levelOf domain) (levelOf codomain))

def eraseContext : (context : List IntrinsicSTT.Ty) →
    Presentation.Tower.Ctx context.length
  | [] => .nil
  | type :: context =>
      .snoc (eraseContext context) (eraseTypeAt context.length type)

def eraseVar : {context : List IntrinsicSTT.Ty} →
    {selectedType : IntrinsicSTT.Ty} →
      IntrinsicSTT.Var context selectedType → Fin context.length
  | _, _, .zero => 0
  | _, _, .succ prior => (eraseVar prior).succ

@[simp] theorem lookup_eraseContext
    (typedVar : IntrinsicSTT.Var context selectedType) :
    Presentation.Ctx.lookup (eraseContext context) (eraseVar typedVar) =
      eraseTypeAt context.length selectedType := by
  induction typedVar with
  | @zero type context =>
      simp [eraseContext, eraseVar, eraseTypeAt_rename]
  | @succ context type other prior induction =>
      simp [eraseContext, eraseVar, induction, eraseTypeAt_rename]

def eraseTerm : {context : List IntrinsicSTT.Ty} →
    {selectedType : IntrinsicSTT.Ty} →
      IntrinsicSTT.Term context selectedType →
        Presentation.Tower.Tm context.length
  | _, _, .var typedVar => .var (eraseVar typedVar)
  | _, _, .lam body => .lam (eraseTerm body)
  | _, _, .app function argument =>
      .app (eraseTerm function) (eraseTerm argument)

theorem eraseTerm_hasType
    (term : IntrinsicSTT.Term context selectedType) :
    Presentation.Tower.HasType (eraseContext context) (eraseTerm term)
      (eraseTypeAt context.length selectedType) := by
  induction term with
  | var typedVar =>
      change Presentation.Tower.HasType (eraseContext _)
        (.var (eraseVar typedVar)) (eraseTypeAt _ _)
      simpa only [lookup_eraseContext] using
        (Presentation.HasType.var (R := Presentation.Tower.rules)
          (Γ := eraseContext _) (eraseVar typedVar))
  | @lam context domain codomain body induction =>
      exact .lamIntro induction
  | @app context domain codomain function argument
      functionInduction argumentInduction =>
      have application :=
        Presentation.HasType.appElim functionInduction argumentInduction
      change Presentation.Tower.HasType (eraseContext _)
        (.app (eraseTerm function) (eraseTerm argument)) (eraseTypeAt _ _)
      simpa [eraseTypeAt, Presentation.inst0] using application

/-! ## One shared open identity beta instance -/

def canonicalContext : List IntrinsicSTT.Ty := [.atom]

def canonicalBody :
    IntrinsicSTT.Term (.atom :: canonicalContext) .atom :=
  .var .zero

def canonicalArgument : IntrinsicSTT.Term canonicalContext .atom :=
  .var .zero

def canonicalClaim :
    IntrinsicSTT.BetaClaim canonicalContext .atom .atom where
  body := canonicalBody
  argument := canonicalArgument

@[simp] theorem canonicalTarget_eq_argument :
    canonicalClaim.target = canonicalArgument :=
  rfl

/-- The native DTT beta rule and both typed endpoints are obtained from the
same intrinsic body and argument. -/
theorem canonical_typedBeta :
    StepCore Presentation.Tower.rules.computation
        Presentation.Tower.rules.headEq
        (eraseTerm canonicalClaim.source) (eraseTerm canonicalClaim.target) ∧
      Presentation.Tower.HasType (eraseContext canonicalContext)
        (eraseTerm canonicalClaim.source) (.head .legacyGround) ∧
      Presentation.Tower.HasType (eraseContext canonicalContext)
        (eraseTerm canonicalClaim.target) (.head .legacyGround) := by
  exact Presentation.HasType.typedBeta
    (eraseTerm_hasType canonicalBody) (eraseTerm_hasType canonicalArgument)

/-- The typed beta event is computational rather than raw syntactic equality. -/
theorem canonical_source_ne_target :
    eraseTerm canonicalClaim.source ≠ eraseTerm canonicalClaim.target := by
  intro equality
  cases equality

end TowerDTT

/-! ## Face 2: the declaration-aware deep GSLT checker -/

namespace DeepGSLT

open IntrinsicSTT
open TowerDTT
open DeclarationAwareSubstitutionCompiler
open DeclarationAwareSubstitutionLanguage

variable {context : List IntrinsicSTT.Ty}
variable {selectedType : IntrinsicSTT.Ty}

/-- Direct first-order erasure into the independent GSLT companion algebra. -/
def rawErase : {context : List IntrinsicSTT.Ty} →
    {selectedType : IntrinsicSTT.Ty} →
      IntrinsicSTT.Term context selectedType →
        DeclarationAwareSubstitutionCompiler.RawTerm
  | _, _, .var typedVar => .var (eraseVar typedVar).val
  | _, _, .lam body => .lam (rawErase body)
  | _, _, .app function argument =>
      .app (rawErase function) (rawErase argument)

/-- The two erasure routes commute before any checker is run. -/
@[simp] theorem rawErase_eq_eraseTower
    (term : IntrinsicSTT.Term context selectedType) :
    rawErase term =
      DeclarationAwareSubstitutionSemantics.erase (eraseTerm term) := by
  induction term with
  | var typedVar => rfl
  | lam body induction => simp [rawErase, eraseTerm,
      DeclarationAwareSubstitutionSemantics.erase,
      induction]
  | app function argument functionInduction argumentInduction =>
      simp [rawErase, eraseTerm,
        DeclarationAwareSubstitutionSemantics.erase, functionInduction,
        argumentInduction]

def rawBody : DeclarationAwareSubstitutionCompiler.RawTerm :=
  rawErase canonicalBody

def rawArgument : DeclarationAwareSubstitutionCompiler.RawTerm :=
  rawErase canonicalArgument

def canonicalTarget : Pattern :=
  encodeRaw (rawErase canonicalClaim.target)

@[simp] theorem canonicalTarget_eq_argument :
    canonicalTarget = encodeRaw rawArgument :=
  rfl

def canonicalGoal : Pattern :=
  rootBeta
    (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument))
    canonicalTarget

@[simp] theorem canonical_raw_substitution_commutes :
    substituteRaw 0 rawArgument rawBody = rawErase canonicalClaim.target :=
  rfl

/-- The proof-producing generic GSLT compiler accepts the same beta event. -/
theorem canonical_deep_checked :
    checkRaw DeclarationAwareSubstitutionLanguage.definition canonicalGoal
      (betaRawProof rawBody rawArgument) = true := by
  unfold canonicalGoal canonicalTarget
  rw [← canonical_raw_substitution_commutes]
  exact betaRawProof_accepts rawBody rawArgument

/-- No accepted artifact for the canonical source can name another target. -/
theorem canonical_deep_no_invention
    {target : Pattern} {proof : RawProof}
    (accepted :
      checkRaw DeclarationAwareSubstitutionLanguage.definition
        (rootBeta
          (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument)) target)
        proof = true) :
    target = canonicalTarget := by
  have reflected :=
    DeclarationAwareSubstitutionReflection.checkRaw_beta_reflects
      rawBody rawArgument accepted
  calc
    target = encodeRaw (substituteRaw 0 rawArgument rawBody) := reflected
    _ = canonicalTarget := by
      rw [canonical_raw_substitution_commutes]
      rfl

/-- A changed target is rejected even when the proof tree is the canonical
generated beta certificate. -/
theorem changed_target_rejected :
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (rootBeta
        (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument))
        (encodeRaw (.lam rawBody)))
      (betaRawProof rawBody rawArgument) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have targetEquality := betaRawProof_no_invention rawBody rawArgument accepted
  simp [rawBody, rawArgument, canonicalBody, canonicalArgument, eraseTerm,
    eraseVar, DeclarationAwareSubstitutionSemantics.erase, encodeRaw,
    DeclarationAwareSubstitutionSemantics.encode, substituteRaw] at targetEquality

end DeepGSLT

/-! ## Faces 3 and 4: shallow STT and set-valued validity -/

namespace ExtensionalFaces

open IntrinsicSTT
open TowerDTT

variable {context : List IntrinsicSTT.Ty}
variable {domain codomain : IntrinsicSTT.Ty}

/-- HOL-shaped shallow validity: equality under every carrier and environment. -/
def ShallowValid (claim :
    IntrinsicSTT.BetaClaim context domain codomain) : Prop :=
  ∀ (Ground : Type) (environment : Environment Ground context),
    claim.source.denote environment = claim.target.denote environment

/-- Set/HOTG-shaped validity: equality of graphs in every carrier model. -/
def SetGraphValid (claim :
    IntrinsicSTT.BetaClaim context domain codomain) : Prop :=
  ∀ Ground : Type,
    claim.source.graph Ground = claim.target.graph Ground

theorem shallow_iff_setGraph
    (claim : IntrinsicSTT.BetaClaim context domain codomain) :
    ShallowValid claim ↔ SetGraphValid claim := by
  constructor
  · intro valid Ground
    exact (Term.graph_eq_iff claim.source claim.target Ground).2
      (valid Ground)
  · intro valid Ground
    exact (Term.graph_eq_iff claim.source claim.target Ground).1
      (valid Ground)

theorem canonical_shallow_valid : ShallowValid canonicalClaim :=
  fun _Ground environment => canonicalClaim.shallowValid environment

theorem canonical_setGraph_valid : SetGraphValid canonicalClaim :=
  shallow_iff_setGraph canonicalClaim |>.1 canonical_shallow_valid

/-! ## Honest failure of reflection -/

def firstAtom : IntrinsicSTT.Term [.atom, .atom] .atom := .var .zero
def secondAtom : IntrinsicSTT.Term [.atom, .atom] .atom := .var (.succ .zero)

theorem firstAtom_ne_secondAtom : firstAtom ≠ secondAtom := by
  intro equality
  cases equality

/-- In the singleton Set model, two different variables have the same
extensional meaning.  One Set model is therefore sound but not reflective of
raw intensional syntax. -/
theorem singleton_model_not_reflective :
    (∀ environment : Environment Unit [.atom, .atom],
        firstAtom.denote environment = secondAtom.denote environment) ∧
      firstAtom ≠ secondAtom := by
  constructor
  · intro environment
    exact Unit.ext _ _
  · exact firstAtom_ne_secondAtom

end ExtensionalFaces

/-! ## A NIK profile whose scope and meaning are independently stated -/

namespace NIKProfile

open IntrinsicSTT
open TowerDTT
open DeepGSLT
open ExtensionalFaces
open DeclarationAwareSubstitutionCompiler
open DeclarationAwareSubstitutionLanguage

/-- Intrinsic tower scope for a proposed result of the shared beta source.
The target equality prevents the selected authority from accepting an
arbitrary result merely because the underlying beta theorem is inhabited. -/
def IntrinsicScope (target : Pattern) : Prop :=
  target = canonicalTarget ∧
    StepCore Presentation.Tower.rules.computation
        Presentation.Tower.rules.headEq
        (eraseTerm canonicalClaim.source) (eraseTerm canonicalClaim.target) ∧
      Presentation.Tower.HasType (eraseContext canonicalContext)
        (eraseTerm canonicalClaim.source) (.head .legacyGround) ∧
      Presentation.Tower.HasType (eraseContext canonicalContext)
        (eraseTerm canonicalClaim.target) (.head .legacyGround)

/-- The selected experimental theory keeps DTT scope and extensional meaning
separate. -/
def theory : TheoryFamily Unit where
  Signature := ValidatedCalculusLanguageDef
  signatureOf := fun _ => DeclarationAwareSubstitutionLanguage.definition
  Claim := fun _ => Pattern
  Scope := fun _ target => IntrinsicScope target
  Meaning := fun _ target =>
    target = canonicalTarget ∧
      ShallowValid canonicalClaim ∧ SetGraphValid canonicalClaim
  scope_sound := by
    intro _kind target intrinsic
    exact ⟨intrinsic.1, canonical_shallow_valid, canonical_setGraph_valid⟩

/-- Native certificates are ordinary declaration-aware GSLT proof trees. -/
def checker : Checker Pattern RawProof where
  check target proof :=
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (rootBeta
        (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument)) target)
      proof

/-- Exact replay is noncircular: soundness lands in native DTT scope, while
completeness is supplied by the independently generated GSLT certificate. -/
theorem checker_authority :
    checker.Authority IntrinsicScope where
  sound := by
    intro target proof accepted
    change checkRaw DeclarationAwareSubstitutionLanguage.definition
      (rootBeta
        (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument)) target)
      proof = true at accepted
    exact ⟨canonical_deep_no_invention accepted, canonical_typedBeta⟩
  complete := by
    intro target intrinsic
    have targetEquality : target = canonicalTarget := intrinsic.1
    subst target
    exact ⟨betaRawProof rawBody rawArgument, canonical_deep_checked⟩

def contract : AuthorityContract theory where
  Certificate := fun _ => RawProof
  checker := fun _ => checker
  scopeAuthority := fun _ => checker_authority

theorem accepted_projects_to_both_extensional_faces
    (target : Pattern) (proof : RawProof)
    (accepted : (contract.checker ()).check target proof = true) :
    target = canonicalTarget ∧
      ShallowValid canonicalClaim ∧ SetGraphValid canonicalClaim :=
  (contract.projection ()).sound target proof accepted

theorem canonical_certificate_replays :
    (contract.checker ()).check canonicalTarget
      (betaRawProof rawBody rawArgument) = true :=
  canonical_deep_checked

def changedTarget : Pattern := encodeRaw (.lam rawBody)

theorem changedTarget_ne_canonicalTarget :
    changedTarget ≠ canonicalTarget := by
  simp [changedTarget, canonicalTarget, rawBody, canonicalBody,
    canonicalArgument, eraseTerm, eraseVar,
    DeclarationAwareSubstitutionSemantics.erase, encodeRaw,
    DeclarationAwareSubstitutionSemantics.encode]

/-- The negative target is outside the intrinsic authority scope, not merely
rejected by one particular proof tree. -/
theorem changed_target_outside_scope :
    IntrinsicScope changedTarget → False :=
  fun scopeEvidence => changedTarget_ne_canonicalTarget scopeEvidence.1

end NIKProfile

/-! ## Axiom audit -/

#print axioms IntrinsicSTT.Term.denote_substitute
#print axioms IntrinsicSTT.BetaClaim.shallowValid
#print axioms IntrinsicSTT.Term.graph_eq_iff
#print axioms TowerDTT.canonical_typedBeta
#print axioms TowerDTT.canonical_source_ne_target
#print axioms DeepGSLT.canonical_deep_checked
#print axioms DeepGSLT.canonical_deep_no_invention
#print axioms DeepGSLT.changed_target_rejected
#print axioms ExtensionalFaces.shallow_iff_setGraph
#print axioms ExtensionalFaces.singleton_model_not_reflective
#print axioms NIKProfile.checker_authority
#print axioms NIKProfile.accepted_projects_to_both_extensional_faces
#print axioms NIKProfile.canonical_certificate_replays
#print axioms NIKProfile.changed_target_outside_scope

end FourFaceBetaExperiment
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
