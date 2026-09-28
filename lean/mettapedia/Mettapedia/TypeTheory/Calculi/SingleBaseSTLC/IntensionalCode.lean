import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Conversion

/-!
# Constructing typed code and its extensionality boundary

Names retain the existing intrinsic syntax, including its context. Application
and explicit template instantiation construct code without executing it. The
independent function interpretation validates execution after construction.

An injective encoding of source syntax cannot respect beta conversion. This is
a restriction on combining two interfaces, not an inconsistency claim about a
language that keeps code and ordinary values distinct. These results concern
the simple function fragment; they do not certify an external evaluator or a
full dependent staged calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.IntensionalCode

universe u v

variable {Γ Δ Θ : List Ty} {A B : Ty} {Ground : Type u}

/-- A name of intrinsically typed, possibly open source code. -/
structure CodeName (context : List Ty) (type : Ty) where
  body : Term context type

namespace CodeName

/-- Exposing a name returns syntax, with no interpretation step. -/
def expose (name : CodeName Γ A) : Term Γ A := name.body

/-- Execute code in an explicitly supplied interpretation and environment. -/
def run (name : CodeName Γ A) (environment : Environment Ground Γ) :
    A.denote Ground :=
  name.body.denote environment

/-- Build an application node, retaining both operands as code. -/
def application (function : CodeName Γ (.arr A B))
    (argument : CodeName Γ A) : CodeName Γ B :=
  ⟨.app function.body argument.body⟩

/-- Fill a typed template's newest hole, lifting under every inner binder. -/
def splice (template : CodeName (A :: Γ) B)
    (argument : CodeName Γ A) : CodeName Γ B :=
  ⟨template.body.instantiateNewest argument.body⟩

/-- Change the explicit code context by a typed simultaneous substitution. -/
def reindex (name : CodeName Γ A) (substitution : Substitution Γ Δ) :
    CodeName Δ A :=
  ⟨name.body.substitute substitution⟩

theorem reindex_identity (name : CodeName Γ A) :
    name.reindex (Substitution.id Γ) = name := by
  cases name with
  | mk body => simp only [reindex, Term.substitute_id]

theorem reindex_comp (name : CodeName Γ A)
    (first : Substitution Γ Δ) (second : Substitution Δ Θ) :
    (name.reindex first).reindex second =
      name.reindex (Substitution.comp first second) := by
  simp only [reindex, Term.substitute_comp]

/-- Template filling commutes with a later change of the ambient context. -/
theorem reindex_splice (template : CodeName (A :: Γ) B)
    (argument : CodeName Γ A) (substitution : Substitution Γ Δ) :
    (template.splice argument).reindex substitution =
      (template.reindex (liftSubstitution substitution)).splice
        (argument.reindex substitution) := by
  simp only [splice, reindex, Term.substitute_instantiateNewest]

theorem run_application (function : CodeName Γ (.arr A B))
    (argument : CodeName Γ A) (environment : Environment Ground Γ) :
    (function.application argument).run environment =
      function.run environment (argument.run environment) :=
  rfl

/-- Interpretation commutes with explicit, capture-avoiding template filling. -/
theorem run_splice (template : CodeName (A :: Γ) B)
    (argument : CodeName Γ A) (environment : Environment Ground Γ) :
    (template.splice argument).run environment =
      template.run (environment.extend (argument.run environment)) := by
  simp only [splice, run, Term.instantiateNewest, Term.denote_substitute,
    substitutionEnvironment_newest]

theorem run_reindex (name : CodeName Γ A) (substitution : Substitution Γ Δ)
    (environment : Environment Ground Δ) :
    (name.reindex substitution).run environment =
      name.run (substitutionEnvironment substitution environment) :=
  Term.denote_substitute name.body substitution environment

/-- Direct execution and expose-then-interpret agree; exposure alone stays syntax. -/
theorem run_eq_interpret_expose (name : CodeName Γ A)
    (environment : Environment Ground Γ) :
    name.run environment = name.expose.denote environment :=
  rfl

end CodeName

/-! ## The application template and capture controls -/

/-- The ambient context contains `f : A -> B` and `a : A`. -/
abbrev ApplicationContext (A B : Ty) : List Ty := [.arr A B, A]

def functionCode : CodeName (ApplicationContext A B) (.arr A B) :=
  ⟨.var .zero⟩

def argumentCode : CodeName (ApplicationContext A B) A :=
  ⟨.var (.succ .zero)⟩

/-- The open code `f x`, where the newest variable is the template hole `x`. -/
def applicationTemplate : CodeName (A :: ApplicationContext A B) B :=
  ⟨.app (.var (.succ .zero)) (.var .zero)⟩

/-- Filling the hole gives exactly the application syntax `f a`. -/
theorem splice_application_template :
    (applicationTemplate (A := A) (B := B)).splice argumentCode =
      functionCode.application argumentCode :=
  rfl

/-- In `lambda y. x`, replacing `x` by ambient `a` keeps `a` free under `y`. -/
def captureTemplate : CodeName [.atom, .atom] (.arr .atom .atom) :=
  ⟨.lam (.var (.succ .zero))⟩

def ambientAtom : CodeName [.atom] .atom := ⟨.var .zero⟩

theorem splice_under_binder :
    (captureTemplate.splice ambientAtom).body =
      (.lam (.var (.succ .zero)) : Term [.atom] (.arr .atom .atom)) :=
  rfl

/-- A captured result is different from the actual template operation. -/
theorem splice_does_not_capture :
    (captureTemplate.splice ambientAtom).body ≠
      (.lam (.var .zero) : Term [.atom] (.arr .atom .atom)) := by
  intro equal
  cases equal

/-! ## A genuine obstruction to source-faithful extensional quotation -/

abbrev FunctionType : Ty := .arr .atom .atom

def identityCode : CodeName [] FunctionType := ⟨.lam (.var .zero)⟩

def identityWrapper : CodeName [] (.arr FunctionType FunctionType) :=
  ⟨.lam (.var .zero)⟩

/-- Building this code retains a beta redex; construction does not normalize it. -/
def redexCode : CodeName [] FunctionType :=
  identityWrapper.application identityCode

theorem constructed_redex_is_not_identity_syntax :
    redexCode.body ≠ identityCode.body := by
  intro equal
  cases equal

theorem constructed_redex_beta_converts :
    BetaConv redexCode.body identityCode.body :=
  .rel _ _ (.beta (.var .zero) identityCode.body)

/-- The independently defined semantics nevertheless gives equal functions. -/
theorem constructed_redex_runs_as_identity
    (environment : Environment Ground []) :
    redexCode.run environment = identityCode.run environment :=
  constructed_redex_beta_converts.denote environment

/-- Observing the source's outer constructor distinguishes the code values. -/
def isApplication {context : List Ty} {type : Ty} : Term context type → Bool
  | .app _ _ => true
  | .var _ => false
  | .lam _ => false

theorem code_observer_separates :
    isApplication redexCode.body = true ∧
      isApplication identityCode.body = false :=
  ⟨rfl, rfl⟩

/-- No injective source encoding can also identify all beta-convertible terms. -/
theorem no_injective_beta_extensional_quote {Target : Type v}
    (encode : Term [] FunctionType → Target)
    (faithful : Function.Injective encode) :
    ¬ (∀ {left right : Term [] FunctionType},
      BetaConv left right → encode left = encode right) := by
  intro extensional
  exact constructed_redex_is_not_identity_syntax
    (faithful (extensional constructed_redex_beta_converts))

/-- Even the two-observation source contract is incompatible with beta extensionality. -/
theorem no_beta_extensional_source_observer
    (observe : Term [] FunctionType → Bool)
    (separates : observe redexCode.body ≠ observe identityCode.body) :
    ¬ (∀ {left right : Term [] FunctionType},
      BetaConv left right → observe left = observe right) := by
  intro extensional
  exact separates (extensional constructed_redex_beta_converts)

/-- The open-code constructor cannot manufacture a closed base term. The base
may be interpreted as the empty type, while function code is inhabited above. -/
theorem no_closed_base_code : IsEmpty (CodeName [] .atom) := by
  refine ⟨fun name => ?_⟩
  let environment : Environment Empty [] :=
    ⟨fun {_} index => nomatch index⟩
  exact (name.run environment).elim

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.IntensionalCode
