/-
# GF Abstract Syntax

Abstract syntax defines the language-independent structure:
- Function signatures (type constructors)
- Tree operations
- Well-formedness conditions

In GF, abstract syntax captures meaning/structure independent of any language.
-/

import Mettapedia.Languages.GF.Core

namespace Mettapedia.Languages.GF.Abstract

open Core

/-! ## Abstract Function Signatures

GF abstract functions are typed constructors that build trees.
For example:
  DetCN : Det → CN → NP      (determiner + common noun → noun phrase)
  UseV : V → VP              (verb → verb phrase)
  PredVP : NP → VP → S       (subject + verb phrase → sentence)
-/

/-- Abstract function signature: name and type -/
structure FunctionSig where
  name : String
  type : Category
  deriving DecidableEq, Repr

namespace FunctionSig

/-- DetCN : Det → CN → NP -/
def DetCN : FunctionSig :=
  { name := "DetCN"
  , type := Category.arrow Category.Det (Category.arrow Category.CN Category.NP) }

/-- PredVP : NP → VP → S -/
def PredVP : FunctionSig :=
  { name := "PredVP"
  , type := Category.arrow Category.NP (Category.arrow Category.VP Category.S) }

/-- UseN : N → CN -/
def UseN : FunctionSig :=
  { name := "UseN"
  , type := Category.arrow (Category.base "N") Category.CN }

/-- ModCN : AP → CN → CN -/
def ModCN : FunctionSig :=
  { name := "ModCN"
  , type := Category.arrow Category.AP (Category.arrow Category.CN Category.CN) }

/-- PositA : A → AP -/
def PositA : FunctionSig :=
  { name := "PositA"
  , type := Category.arrow Category.A Category.AP }

end FunctionSig

/-! ## Abstract Tree Construction

Abstract trees with constructor applications.
For MVP, we use simplified representation.
-/

/-- Abstract tree node with function application -/
inductive AbstractNode where
  | leaf : String → Category → AbstractNode
  | apply : FunctionSig → List AbstractNode → AbstractNode
  deriving Repr

namespace AbstractNode

/-- Extract result category from function type -/
def extractResultCategory : Category → Category
  | Category.base s => Category.base s
  | Category.arrow _ result => extractResultCategory result

/-- Get the category of an abstract node -/
def category : AbstractNode → Category
  | leaf _ cat => cat
  | apply f _ => extractResultCategory f.type

end AbstractNode

/-! ## Well-formedness

Abstract trees must respect type signatures.
-/

/-- Check if arguments match function type -/
def argumentsMatch (funType : Category) (args : List Category) : Bool :=
  match funType, args with
  | Category.base _, [] => true
  | Category.arrow dom rest, arg :: args' =>
      dom == arg && argumentsMatch rest args'
  | _, _ => false

/-- Check if abstract tree is well-formed -/
partial def isWellFormed : AbstractNode → Bool
  | AbstractNode.leaf _ _ => true
  | AbstractNode.apply f args =>
      let argCats := args.map AbstractNode.category
      argumentsMatch f.type argCats &&
      args.all isWellFormed

/-! ## Example Abstract Trees

These demonstrate well-formed abstract syntax trees.
-/

namespace Examples

open AbstractNode FunctionSig

/-- Example: simple noun phrase "the house"
    DetCN the_Det house_CN
-/
def theHouse : AbstractNode :=
  apply DetCN [
    leaf "the_Det" Category.Det,
    leaf "house_CN" Category.CN
  ]

/-- Example: modified noun "big house"
    UseN (ModCN big_A house_N)
-/
def bigHouse : AbstractNode :=
  apply DetCN [
    leaf "the_Det" Category.Det,
    apply ModCN [
      apply PositA [leaf "big_A" Category.A],
      leaf "house_CN" Category.CN
    ]
  ]

end Examples

/-! ## Node Equivalence

Two abstract nodes are equivalent if they linearize identically for all parameters.
Unlike the old `AbstractEquiv` (which was vacuous), this compares actual tree
structure through a linearization function, making it meaningful.
-/

/-- Linearization function for abstract nodes -/
def NodeLinearize (Params : Type) := AbstractNode → Params → String

/-- Two nodes are equivalent under a linearization if they produce identical output -/
def NodeEquiv {Params : Type} (lin : NodeLinearize Params)
    (n₁ n₂ : AbstractNode) : Prop :=
  ∀ params : Params, lin n₁ params = lin n₂ params

namespace NodeEquiv

theorem refl {Params : Type} (lin : NodeLinearize Params) (n : AbstractNode) :
    NodeEquiv lin n n :=
  fun _ => Eq.refl _

theorem symm {Params : Type} {lin : NodeLinearize Params} {n₁ n₂ : AbstractNode} :
    NodeEquiv lin n₁ n₂ → NodeEquiv lin n₂ n₁ :=
  fun h params => (h params).symm

theorem trans {Params : Type} {lin : NodeLinearize Params} {n₁ n₂ n₃ : AbstractNode} :
    NodeEquiv lin n₁ n₂ → NodeEquiv lin n₂ n₃ → NodeEquiv lin n₁ n₃ :=
  fun h12 h23 params => (h12 params).trans (h23 params)

theorem is_equivalence {Params : Type} (lin : NodeLinearize Params) :
    Equivalence (NodeEquiv lin) :=
  ⟨refl lin, symm, trans⟩

end NodeEquiv

end Mettapedia.Languages.GF.Abstract
