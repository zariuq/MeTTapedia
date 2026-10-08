import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationClosed
import Mettapedia.GSLT.Core.LambdaTheory
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The generated closed presentation of an arbitrary binding signature

Sorts and operators are declared independently of a semantic model. Every
argument retains its complete ordered binder context, represented by a
function object from that context product. Ordered argument vectors form
the operator domain. Formation is earned recursively from the generated
rules, and the resulting category has actual finite limits and exponentials.

This constructor presentation has no extra authored equations or operational
edge generators. Their interpretations and universal comparisons are
additional constructions, rather than premises of this definition.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax

universe v

abbrev Base := ULiftHom.{v} (ULift.{v} (Discrete Empty))

instance : IsEmpty Base.{v} :=
  ⟨fun object => isEmptyElim (ULiftHom.objDown object).down⟩

def symbols (binding : Mettapedia.OSLF.Binding.Signature) : Symbols.{v} where
  ObjectName := ULift.{v} binding.Srt
  ArrowName := ULift.{v} (Sigma binding.Op)
  EquationName := ULift.{v} Empty

variable (binding : Mettapedia.OSLF.Binding.Signature)

def sortCode (sort : binding.Srt) : ObjectCode Base.{v} (symbols binding) := .name ⟨sort⟩

def contextCode : Ctx binding → ObjectCode Base.{v} (symbols binding)
  | [] => .terminal
  | sort :: context => .product (sortCode binding sort) (contextCode context)

def powerCode (binders : Ctx binding) (sort : binding.Srt) :
    ObjectCode Base.{v} (symbols binding) :=
  .exponential (contextCode binding binders) (sortCode binding sort)

def familyCode : List (Ctx binding × binding.Srt) → ObjectCode Base.{v} (symbols binding)
  | [] => .terminal
  | arity :: rest => .product (powerCode binding arity.1 arity.2) (familyCode rest)

private theorem context_before (context : Ctx binding) :
    (contextCode.{v} binding context).before (fun _ => 0) (fun _ => 1) 1 := by
  induction context with
  | nil => trivial
  | cons sort context inductionHypothesis =>
      exact ⟨Nat.zero_lt_one, inductionHypothesis⟩

private theorem family_before (arities : List (Ctx binding × binding.Srt)) :
    (familyCode.{v} binding arities).before (fun _ => 0) (fun _ => 1) 1 := by
  induction arities with
  | nil => trivial
  | cons arity rest inductionHypothesis =>
      exact ⟨⟨context_before binding arity.1, Nat.zero_lt_one⟩, inductionHypothesis⟩

def signature : Mettapedia.CategoryTheory.RelativeClosedSyntax.Signature
    (C := Base.{v}) (symbols := symbols.{v} binding) where
  objectRank _ := 0
  arrowRank _ := 1
  source origin := familyCode binding (binding.arity origin.down.2)
  target origin := sortCode binding origin.down.1
  source_before _origin := family_before binding _
  target_before _ := Nat.zero_lt_one
  equationRank origin := nomatch origin.down
  equationSource origin := nomatch origin.down
  equationTarget origin := nomatch origin.down
  left origin := nomatch origin.down
  right origin := nomatch origin.down
  equation_before origin := nomatch origin.down

def sortFormed (sort : binding.Srt) :
    Derivation (signature.{v} binding) (.object (sortCode binding sort)) :=
  .objectName (signature := signature binding) (ULift.up sort)

def contextFormed : (context : Ctx binding) →
    Derivation (signature.{v} binding) (.object (contextCode binding context))
  | [] => .terminalObject
  | sort :: context => .productObject (sortFormed binding sort) (contextFormed context)

def powerFormed (binders : Ctx binding) (sort : binding.Srt) :
    Derivation (signature.{v} binding) (.object (powerCode binding binders sort)) :=
  .exponentialObject (contextFormed binding binders) (sortFormed binding sort)

def familyFormed : (arities : List (Ctx binding × binding.Srt)) →
    Derivation (signature.{v} binding) (.object (familyCode binding arities))
  | [] => .terminalObject
  | arity :: rest => .productObject (powerFormed binding arity.1 arity.2) (familyFormed rest)

def headers : HeaderFormation (signature.{v} binding) where
  source origin := familyFormed binding (binding.arity origin.down.2)
  target origin := sortFormed binding origin.down.1
  left origin := nomatch origin.down
  right origin := nomatch origin.down

def sortObject (sort : binding.Srt) : GeneratedCategory.Object (signature.{v} binding) :=
  ⟨sortCode binding sort, ⟨sortFormed binding sort⟩⟩

def contextObject (context : Ctx binding) : GeneratedCategory.Object (signature.{v} binding) :=
  ⟨contextCode binding context, ⟨contextFormed binding context⟩⟩

def powerObject (binders : Ctx binding) (sort : binding.Srt) :
    GeneratedCategory.Object (signature.{v} binding) :=
  ⟨powerCode binding binders sort, ⟨powerFormed binding binders sort⟩⟩

def familyObject (arities : List (Ctx binding × binding.Srt)) :
    GeneratedCategory.Object (signature.{v} binding) :=
  ⟨familyCode binding arities, ⟨familyFormed binding arities⟩⟩

def operator {sort : binding.Srt} (operation : binding.Op sort) :
    GeneratedCategory.RawHom (familyObject.{v} binding (binding.arity operation))
      (sortObject binding sort) :=
  ⟨.name ⟨⟨sort, operation⟩⟩,
    ⟨.arrowName (signature := signature binding) (ULift.up ⟨sort, operation⟩)
      ((headers binding).source (ULift.up ⟨sort, operation⟩))
      ((headers binding).target (ULift.up ⟨sort, operation⟩))⟩⟩

def theory : Mettapedia.GSLT.Core.LambdaTheory.{v, v} :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory (GeneratedCategory.Object (signature.{v} binding))

end Mettapedia.OSLF.Binding.ClosedPresentation
