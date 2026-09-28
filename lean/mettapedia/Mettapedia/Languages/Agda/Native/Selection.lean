import Mettapedia.OSLF.Syntax.FiniteRuleSearch
import Mettapedia.Languages.Agda.Structural.AdministrativeStatics

/-!
# Structural introduction-rule selection

This selector recovers local rule parameters from the proposed syntax. It
returns actual constructors of the existing static presentation; the shared
executor computes and checks all premises. Unsupported syntax and conversion
routes remain incomplete. No trusted typing result enters this interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Production

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRuleSearch
open Mettapedia.Languages.Agda.Structural
open Statics

instance opEquality : (s : sig.Srt) → DecidableEq (sig.Op s) :=
  fun s => @instDecidableEqOp s

instance rawTypeEquality {n : Nat} : DecidableEq (RawTy n) :=
  @decEqTerm sig opEquality _ _

instance rawTermEquality {n : Nat} : DecidableEq (RawTm n) :=
  @decEqTerm sig opEquality _ _

def parameter {n : Nat} : RawTy n → Option (TypeParameter n)
  | .op .el (.cons (.op .set (.cons (.op (.levelClosed k) .nil) .nil)) (.cons t .nil)) =>
      some ⟨k,t⟩
  | _ => none

def functionParameters {n : Nat} : RawTm n → Option (TypeParameter n × TypeBody n)
  | .op .pi (.cons A (.cons B .nil)) => do
      let domain ← parameter A
      let codomain ← parameter (n := n + 1) B
      return (domain, .bind codomain)
  | .op .piNoAbs (.cons A (.cons B .nil)) => do
      let domain ← parameter A
      let codomain ← parameter B
      return (domain, .noBind codomain)
  | _ => none

/-- A recoverable Pi annotation includes an exact check of its universe code.
Recovering its shape is not evidence that the annotation is well formed. -/
def functionType {n : Nat} (A : RawTy n) :
    Option { parts : TypeParameter n × TypeBody n // (piType parts.1 parts.2).code = A } := do
  let ann ← parameter A
  let parts ← functionParameters ann.term
  if exactCode : (piType parts.1 parts.2).code = A then
    return ⟨parts, exactCode⟩
  else none

def termBody {n : Nat} : (t : RawTm n) → Option { body : TermBody n // body.lambda = t }
  | .op .lam (.cons body .nil) => some ⟨.bind body, rfl⟩
  | .op .lamNoAbs (.cons body .nil) => some ⟨.noBind body, rfl⟩
  | _ => none

def typedAt {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n)
    {B : RawTy n} (shape : Statics.RuleShape (typed Γ t B)) :
    List (Statics.RuleShape (typed Γ t A)) :=
  if same : B = A then [same ▸ shape] else []

def typing {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n) :
    List (Statics.RuleShape (typed Γ t A)) :=
  match t with
  | .var v => typedAt Γ (.var v) A (.variable Γ v)
  | .op .sortTerm (.cons (.op .set (.cons (.op (.levelClosed k) .nil) .nil)) .nil) =>
      typedAt Γ (universeTerm k) A (.sort Γ k)
  | t =>
      match termBody t, functionType A with
      | some body, some parts =>
          [body.property ▸ parts.property ▸ Statics.RuleShape.lambda Γ parts.val.1 parts.val.2 body.val]
      | _, _ =>
          match functionParameters t with
          | some (domain, codomain) =>
              if exactTerm : codomain.pi domain = t then
                typedAt Γ t A (exactTerm ▸ Statics.RuleShape.pi Γ domain codomain)
              else []
          | none => []

def formation {n : Nat} (Γ : RawContext n) (A : RawTy n) :
    List (Statics.RuleShape (formed Γ A)) :=
  match parameter A with
  | some param =>
      if exactCode : param.code = A then [exactCode ▸ Statics.RuleShape.formation Γ param.level param.term]
      else []
  | none => []

def contexts : {n : Nat} → (Γ : RawContext n) → List (Statics.RuleShape (context Γ))
  | _, .nil => [.empty]
  | _, .snoc Γ A => [.extend Γ A]

def core : (j : Statics.Judgment) → List (Statics.RuleShape j)
  | .context ⟨_, Γ⟩ => contexts Γ
  | .type ⟨_, Γ⟩ A => formation Γ A
  | .term ⟨_, Γ⟩ A ⟨t⟩ => typing Γ t A
  | _ => []

/-- Recover a proposed result annotation by following a syntactic spine.
The returned annotation has no typing authority: the selected rules still
require typing of every argument and formation of the actual context. -/
def applicationArgument {n : Nat} : Elim (scope n) → Option (RawTm n)
  | .op .apply (.cons argument .nil) => some argument
  | _ => none

def spineAnnotation {n : Nat} (A : RawTy n) : Spine (scope n) → Option (RawTy n)
  | .var _ => none
  | .op .nil .nil => some A
  | .op .cons (.cons head (.cons rest .nil)) => do
      let argument ← applicationArgument head
      let parts ← functionType A
      spineAnnotation (parts.val.2.instantiate argument).code rest
  | .op .append (.cons first (.cons rest .nil)) => do
      let middle ← spineAnnotation A first
      spineAnnotation middle rest
termination_by spine => termSize spine
decreasing_by all_goals simp only [termSize, argsSize]; omega

def constantAnnotation {n : Nat} (t : RawTm n) : Option (RawTy n) :=
  match t with
  | .op .sortTerm (.cons (.op .set (.cons (.op (.levelClosed k) .nil) .nil)) .nil) =>
      some (universeType n (k + 1)).code
  | _ => do
      let parts ← functionParameters t
      return (universeType n (max parts.1.level parts.2.level)).code

/-- Annotation recovery for inferable heads. An unannotated lambda has no
principal annotation here and deliberately returns none. -/
def headAnnotation {n : Nat} (Γ : RawContext n) : RawTm n → Option (RawTy n)
  | .var v => some (ContextGeometry.lookup Γ v)
  | .op .eliminate (.cons head (.cons spine .nil)) => do
      let input ← headAnnotation Γ head
      spineAnnotation input spine
  | .op .lam _ | .op .lamNoAbs _ => none
  | .op .pi args => constantAnnotation (.op .pi args)
  | .op .piNoAbs args => constantAnnotation (.op .piNoAbs args)
  | .op (.defined _) _ | .op (.constructor _) _ | .op (.natLiteral _) _ => none
  | .op .sortTerm args => constantAnnotation (.op .sortTerm args)
  | .op .levelTerm _ => none
termination_by term => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

def eliminationRules : (j : Statics.Judgment) →
    List (AdministrativeStatics.RuleShape (.core j))
  | .term ⟨_, Γ⟩ output ⟨.op .eliminate (.cons head (.cons spine .nil))⟩ =>
      match headAnnotation Γ head with
      | some input => [.prior (.elimination Γ head input spine output)]
      | none => []
  | _ => []

def spineRules {n : Nat} (Γ : RawContext n) (input : RawTy n)
    (spine : Spine (scope n)) (output : RawTy n) :
    List (AdministrativeStatics.RuleShape (.spineAction Γ input spine output)) :=
  match spine with
  | .op .nil .nil =>
      if same : input = output then [same ▸ AdministrativeStatics.RuleShape.prior (.nil Γ input)]
      else []
  | .op .cons (.cons (.op .apply (.cons argument .nil)) (.cons rest .nil)) =>
      match functionType input with
      | some parts =>
          [parts.property ▸ AdministrativeStatics.RuleShape.prior
            (.cons Γ parts.val.1 parts.val.2 argument rest output)]
      | none => []
  | .op .append (.cons first (.cons rest .nil)) =>
      match spineAnnotation input first with
      | some middle => [.prior (.append Γ input first middle rest output)]
      | none => []
  | _ => []

/-- Core rule selection uses the enlarged presentation's same recursive
premise table. No parallel evaluator or substitution implementation is added. -/
def candidates (j : AdministrativeStatics.Judgment) :
    Candidates AdministrativeStatics.presentation j where
  rules := match j with
    | .core j => (core j).map (fun shape => .prior (.core shape)) ++ eliminationRules j
    | .spineAction Γ input spine output => spineRules Γ input spine output
    | _ => []
  exhaustive := false
  covers := by intro impossible; cases impossible

def run (fuel : Nat) (j : AdministrativeStatics.Judgment) :
    Verdict (AdministrativeStatics.Derivation j) :=
  search AdministrativeStatics.presentation candidates fuel j

end Mettapedia.Languages.Agda.Native.Production
