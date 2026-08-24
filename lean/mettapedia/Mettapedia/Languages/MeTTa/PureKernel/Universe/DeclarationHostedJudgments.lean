import Mettapedia.Languages.MeTTa.PureKernel.Universe.AuthoredDeclarationSignature
import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareFormedTyping
import Mettapedia.Languages.MeTTa.PureKernel.Universe.SyntacticContextualCategory
import Mettapedia.Languages.MeTTa.PureKernel.Universe.TypingGeneration

/-!
# Prime judgments indexed by an authored declaration host

The finite structural checker is a capability of bare Prime, not the meaning
of every declaration-extended Prime program.  This module places the common
intrinsic judgments over the actual declaration world in which they are
formed.

An authored document first interprets to the established semantic signature.
`FormationHost` requires its declarations to be formed; `ComputationalHost`
separately requires preservation of authored computation.  This distinction
prevents declaration formation from silently granting reduction authority.

The existing exact checked fragment embeds monotonically into every formed
host.  Conversely, a host may form declared constants unavailable to the bare
fragment.  Both facts use the same `HasType`, contexts, and syntactic CwF; no
parallel object language or checker is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace DeclarationHostedJudgments

open AuthoredDeclarationSignature
open DeclarationAwareCheckedContext
open DeclarationAwareFormedTyping
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticContextual

/-! ## Hosted declaration worlds -/

/-- An authored Prime world whose declarations are formed.  Computation
preservation is intentionally absent. -/
structure FormationHost where
  source : SourceDocument
  formed : (interpret source).Formed Tower.rules

namespace FormationHost

def signature (host : FormationHost) : Signature Tower.Head :=
  interpret host.source

def rules (host : FormationHost) : Rules Tower.Head :=
  extendRules Tower.rules host.signature

/-- Retaining the authored source makes the host projection injective even
though interpretation to an extensional signature is not. -/
theorem source_injective : Function.Injective source := by
  intro first second sameSource
  cases first with
  | mk firstSource firstFormed =>
      cases second with
      | mk secondSource secondFormed =>
          dsimp at sameSource
          subst secondSource
          rfl

end FormationHost

/-- A formed host that additionally licenses every declared computation step.
This is the declaration-level computational capability, not a decision
procedure or an optimizer. -/
structure ComputationalHost where
  source : SourceDocument
  wellFormed : (interpret source).WellFormed Tower.rules

namespace ComputationalHost

def toFormationHost (host : ComputationalHost) : FormationHost where
  source := host.source
  formed := host.wellFormed.formed

def signature (host : ComputationalHost) : Signature Tower.Head :=
  interpret host.source

def rules (host : ComputationalHost) : Rules Tower.Head :=
  extendRules Tower.rules host.signature

@[simp] theorem toFormationHost_source (host : ComputationalHost) :
    host.toFormationHost.source = host.source := rfl

@[simp] theorem toFormationHost_rules (host : ComputationalHost) :
    host.toFormationHost.rules = host.rules := rfl

end ComputationalHost

/-! ## Full context formation in one host -/

/-- A level-annotated context formed by the full typing judgment of one
hosted calculus.  This is the host-indexed generalization of the existing
finite structural context evidence. -/
inductive ContextFormation (rules : Rules Tower.Head) :
    {n : Nat} -> Tower.Ctx n -> LevelSpine n -> Type where
  | nil : ContextFormation rules (.nil : Tower.Ctx 0) .nil
  | snoc {n : Nat} {context : Tower.Ctx n} {type : Tower.Tm n}
      {levels : LevelSpine n} {level : LevelExpr} :
      ContextFormation rules context levels ->
      HasType rules context type (.head (.sort level)) ->
      rules.isUniverse (.sort level) ->
      ContextFormation rules (.snoc context type) (.snoc levels level)

namespace ContextFormation

/-- Forget level annotations while retaining every full formation
derivation. -/
def toContextWellFormed {rules : Rules Tower.Head} :
    {n : Nat} -> {context : Tower.Ctx n} -> {levels : LevelSpine n} ->
      ContextFormation rules context levels ->
      ContextWellFormed rules context
  | _, _, _, .nil => .nil
  | _, _, _, .snoc prior typeFormation isUniverse =>
      .snoc prior.toContextWellFormed typeFormation isUniverse

/-- The exact structural checker fragment remains valid after installing any
declaration signature.  No declaration-specific judgment is inferred by this
embedding. -/
def includeSignature (signature : Signature Tower.Head) :
    {n : Nat} -> {context : Tower.Ctx n} -> {levels : LevelSpine n} ->
      StructuralContextFormation context levels ->
      ContextFormation (extendRules Tower.rules signature) context levels
  | _, _, _, .nil => .nil
  | _, _, _, .snoc prior typeFormation =>
      .snoc (ContextFormation.includeSignature signature prior)
        (Presentation.Declaration.HasType.includeSignature Tower.rules
          signature typeFormation.toHasType)
        (Tower.IsUniverse.sort _)

end ContextFormation

/-! ## Formed typing in one host -/

/-- The intrinsic meaning of a formed-typing query in an authored host. -/
structure HostedFormedTyping (host : FormationHost)
    (query : FormedTypingQuery) : Type where
  contextFormation :
    ContextFormation host.rules query.context query.levels
  typeFormation :
    HasType host.rules query.context query.type
      (.head (.sort query.level))
  subjectTyping :
    HasType host.rules query.context query.subject query.type

namespace HostedFormedTyping

/-- The retained context as an object of the existing syntactic contextual
category. -/
def formedContext {host : FormationHost} {query : FormedTypingQuery}
    (evidence : HostedFormedTyping host query) :
    FormedContext host.rules where
  arity := query.arity
  context := query.context
  wellFormed := evidence.contextFormation.toContextWellFormed

/-- The retained expected type in its selected universe. -/
def typeOver {host : FormationHost} {query : FormedTypingQuery}
    (evidence : HostedFormedTyping host query) :
    TypeOver evidence.formedContext where
  code := query.type
  level := .sort query.level
  isUniverse := Tower.IsUniverse.sort query.level
  formed := evidence.typeFormation

/-- Native construction returns a term in the host-indexed CwF directly. -/
def term {host : FormationHost} {query : FormedTypingQuery}
    (evidence : HostedFormedTyping host query) :
    Term evidence.formedContext evidence.typeOver where
  code := query.subject
  typed := evidence.subjectTyping

end HostedFormedTyping

/-- Every proof in the bare exact checked fragment has the same intrinsic
meaning in every formed declaration host.  This is the semantic monotonicity
behind conservative checker reuse. -/
def IntrinsicFormedTyping.includeHost (host : FormationHost)
    {query : FormedTypingQuery}
    (evidence : IntrinsicFormedTyping query) :
    HostedFormedTyping host query where
  contextFormation :=
    ContextFormation.includeSignature host.signature
      evidence.contextFormation
  typeFormation :=
    Presentation.Declaration.HasType.includeSignature Tower.rules
      host.signature evidence.typeFormation.toHasType
  subjectTyping :=
    Presentation.Declaration.HasType.includeSignature Tower.rules
      host.signature evidence.subjectTyping.toHasType

/-! ## Declaration-specific positive and negative boundaries -/

/-- A formed declaration produces an intrinsic hosted typing judgment for its
constant in the empty context.  The universe witness comes from declaration
formation; no generic checker rule is postulated. -/
theorem declared_constant_has_hosted_typing
    (host : FormationHost) {name : DeclName} {type : Tower.Tm 0}
    (declared : host.signature.typeOf? name = some type) :
    ∃ level : LevelExpr,
      Nonempty (HostedFormedTyping host
        { arity := 0
          context := .nil
          levels := .nil
          subject := .const name
          type := type
          level := level }) := by
  rcases host.formed.types declared with
    ⟨universeHead, isUniverse, typeFormation⟩
  cases isUniverse with
  | sort level =>
      refine ⟨level, ⟨?_⟩⟩
      exact
        { contextFormation := .nil
          typeFormation := by
            simpa [FormationHost.rules, FormationHost.signature] using
              typeFormation
          subjectTyping := by
            have constantTyping :
                HasType host.rules (.nil : Tower.Ctx 0) (.const name)
                  (liftClosed type) := by
              apply HasType.const
              change combinedType Tower.rules host.signature name = some type
              exact combinedType_of_signature Tower.rules host.signature
                rfl declared
            have liftClosedAtZero :
                (liftClosed type : Tower.Tm 0) = type := by
              unfold liftClosed
              have mapsEqual :
                  (Fin.elim0 : Ren 0 0) = idRen := by
                funext index
                exact Fin.elim0 index
              rw [mapsEqual, Presentation.rename_id]
            rw [liftClosedAtZero] at constantTyping
            exact constantTyping }

/-- Conversion and cumulative lifting cannot conjure an undeclared constant
inside a hosted world. -/
theorem missing_constant_has_no_hosted_type
    (host : FormationHost) (n : Nat) (context : Tower.Ctx n)
    (name : DeclName) (displayedType : Tower.Tm n)
    (missing : host.signature.typeOf? name = none) :
    ¬ HasType host.rules context (.const name) displayedType := by
  apply HasType.constantImpossibleWhenMissing
  change combinedType Tower.rules host.signature name = none
  simp [combinedType, Tower.rules, missing]

/-! ## Empty-host control -/

private def emptySource : SourceDocument := sourceCodec.quote []

private def emptyHost : FormationHost where
  source := emptySource
  formed := by
    have noEntry :
        ∀ name : DeclName, (interpret emptySource).entries name = none := by
      intro name
      simp [emptySource, interpret, semanticSignature,
        constantDeclarations, Signature.ofList, Signature.empty,
        Signature.insert]
    exact
      { fresh := by
          intro name entry lookup
          rw [noEntry name] at lookup
          cases lookup
        types := by
          intro name type lookup
          unfold Signature.typeOf? at lookup
          rw [noEntry name] at lookup
          cases lookup
        values := by
          intro name type value typeLookup valueLookup
          unfold Signature.typeOf? at typeLookup
          rw [noEntry name] at typeLookup
          cases typeLookup
        noSelfDelta := by
          intro name value lookup
          unfold Signature.valueOf? at lookup
          rw [noEntry name] at lookup
          cases lookup }

/-- Negative control specialized to the empty authored host. -/
theorem empty_host_has_no_constants (name : DeclName)
    (displayedType : Tower.Tm 0) :
    ¬ HasType emptyHost.rules (.nil : Tower.Ctx 0)
      (.const name) displayedType := by
  apply missing_constant_has_no_hosted_type
  simp [emptyHost, FormationHost.signature, emptySource, interpret,
    semanticSignature, constantDeclarations, Signature.ofList,
    Signature.empty, Signature.typeOf?]

#print axioms FormationHost.source_injective
#print axioms IntrinsicFormedTyping.includeHost
#print axioms declared_constant_has_hosted_typing
#print axioms missing_constant_has_no_hosted_type
#print axioms empty_host_has_no_constants

end DeclarationHostedJudgments
end Mettapedia.Languages.MeTTa.PureKernel.Universe
