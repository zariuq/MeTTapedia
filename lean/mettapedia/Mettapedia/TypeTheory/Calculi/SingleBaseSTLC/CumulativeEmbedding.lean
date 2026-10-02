import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Presentation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedBetaSubjectReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.SchemaElaboration

/-! # Simple types embedded in the cumulative Pi/Sigma/identity presentation -/
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
namespace TowerDTT

open IntrinsicSTT

variable {sourceArity targetArity arity : Nat}
variable {context : List IntrinsicSTT.Ty}
variable {selectedType : IntrinsicSTT.Ty}

/-- All selected simple types are closed cumulative-tower types.  Their universe level is
retained rather than forced to a single syntactic level expression. -/
def levelOf : IntrinsicSTT.Ty → LevelExpr Nat
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

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
