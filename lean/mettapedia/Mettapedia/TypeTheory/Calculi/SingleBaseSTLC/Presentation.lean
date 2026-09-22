import Mathlib.Data.Set.Basic

/-! # Intrinsically typed lambda calculus over one base type

Variables, capture-avoiding substitution and function interpretations are
independent of any programming-language candidate.
-/
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

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

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
