import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticJudgmentalSigmaId
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedFamilies

/-!
# Native identity elimination in the conversion-enriched natural model

The syntactic natural model already constructs identity types and
reflexivity intrinsically. Prime's declaration-aware indexed-family theory
supplies the remaining operation: a fixed-left-endpoint identity eliminator
J, together with a proof-relevant iota rule.

This module connects those layers without adding another eliminator or
typing relation. A NativeIotaCell consists of one formed result fibre,
two intrinsically typed endpoints in that fibre, and the authored native
iota witness between their raw codes. It embeds directly into the
judgment-indexed computation of the natural model and is stable under every
typed context substitution.

The canonical J schema is then displayed as one such cell. Its iota step
is genuine computation rather than host-language equality, retains the
identity-rule witness, and remains available at every typed instance of the
schema. A wrong target is unconstructible already at the evidence layer.

This is deliberately an exact-image result. It does not claim that every
raw term convertible to a J redex can be inverted into the canonical typed
schema; that stronger coverage theorem belongs to the declaration
computation-preservation boundary.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace SyntacticJudgmentalIdentityEliminator

open CategoryTheory
open Declaration
open ProofRelevantStructuralComputation
open SyntacticContextual
open SyntacticJudgmentalPi
open SyntacticConversionEnrichment
open Mettapedia.TypeTheory.JudgmentalEquality
open NativeIndexedFamilies.Intrinsic

/-! ## The native iota root retained by the natural model -/

/-- The native indexed-family iota witness is an exact proof-relevant lift of
the root relation installed by its declaration signature. The underlying
Tower calculus has no root reductions and the signature has no delta values,
so every inhabited root step is precisely one authored iota witness. -/
def nativeIotaRetainedRoot : RetainedRoot rules where
  computation := proofRelevantIotaComputation
  support_iff := by
    intro n left right
    constructor
    · intro step
      cases step with
      | inherited inherited => exact inherited.elim
      | delta unfolding =>
          rw [rawSignature_valueOf_none] at unfolding
          contradiction
      | declared declared => exact declared
    · intro evidence
      exact .declared evidence

/-! ## Typed native-root cells -/

/-- One proof-relevant native iota equation inside a formed judgment fibre.
Both endpoint typings and the formed result type are construction data; the
evidence field retains which authored rule fired and all of its arguments. -/
structure NativeIotaCell (context : FormedContext rules) where
  resultType : TypeOver context
  source : Term context resultType
  target : Term context resultType
  evidence : IotaEvidence context.arity source.code target.code

namespace NativeIotaCell

/-- Package any declaration-aware typed iota receipt whose telescope has
already been proved formed. This is shared by identity and strictly-positive
family eliminators; no rule-specific reconstruction is needed. -/
def ofReceipt {context : FormedContext rules}
    {left right : Tower.Tm context.arity}
    (resultType : TypeOver context)
    (receipt : TypedIotaReceipt context.context left right resultType.code) :
    NativeIotaCell context where
  resultType := resultType
  source :=
    { code := left
      typed := receipt.sourceTyping }
  target :=
    { code := right
      typed := receipt.targetTyping }
  evidence := receipt.evidence

/-- A typed native-root cell is directly a judgment-indexed computation
step. No checker or subject-reduction reconstruction occurs here. -/
def toStep {context : FormedContext rules}
    (cell : NativeIotaCell context) :
    (termComputation nativeIotaRetainedRoot context).Step
      cell.source cell.target :=
  .root cell.evidence

/-- Every native iota cell generates a proof-relevant conversion in its
exact judgment fibre. -/
def toConversion {context : FormedContext rules}
    (cell : NativeIotaCell context) :
    ConversionEvidence (termComputation nativeIotaRetainedRoot context)
      cell.source cell.target :=
  .step cell.toStep

/-- Typed context substitution transports the complete native cell,
including the authored root witness. -/
def reindex {source target : FormedContext rules}
    (cell : NativeIotaCell target) (morphism : source ⟶ target) :
    NativeIotaCell source where
  resultType := cell.resultType.reindex morphism
  source := cell.source.reindex morphism
  target := cell.target.reindex morphism
  evidence := cell.evidence.substitute morphism.substitution

/-- Embedding into judgmental computation commutes strictly with typed
substitution. -/
theorem toStep_reindex {source target : FormedContext rules}
    (cell : NativeIotaCell target) (morphism : source ⟶ target) :
    (cell.reindex morphism).toStep =
      cell.toStep.substitute morphism.substitution :=
  rfl

@[simp] theorem reindex_source_code {source target : FormedContext rules}
    (cell : NativeIotaCell target) (morphism : source ⟶ target) :
    (cell.reindex morphism).source.code =
      Presentation.subst morphism.substitution cell.source.code :=
  rfl

@[simp] theorem reindex_target_code {source target : FormedContext rules}
    (cell : NativeIotaCell target) (morphism : source ⟶ target) :
    (cell.reindex morphism).target.code =
      Presentation.subst morphism.substitution cell.target.code :=
  rfl

end NativeIotaCell

/-! ## The formed declaration telescope of identity elimination -/

/-- Formation of the element-type binder. -/
def contextAWellFormed : ContextWellFormed rules contextA :=
  .snoc .nil (.headType (.sort elementLevel))
    (.sort (.succ elementLevel))

/-- Formation of the distinguished left endpoint binder. -/
def contextAXWellFormed : ContextWellFormed rules contextAX :=
  .snoc contextAWellFormed (HasType.var 0) (.sort elementLevel)

/-- Formation of the path-induction motive binder. -/
def contextAXPWellFormed : ContextWellFormed rules contextAXP :=
  .snoc contextAXWellFormed identityMotiveType_hasType
    (.sort identityMotiveLevel)

/-- Formation of the reflexivity-method binder. -/
def contextAXPDWellFormed : ContextWellFormed rules contextAXPD :=
  .snoc contextAXPWellFormed identityReflCaseType_hasType
    (.sort motiveLevel)

/-- The canonical identity-elimination telescope as an object of the
declaration-aware contextual category. -/
def formedIdentityContext : FormedContext rules where
  arity := 4
  context := contextAXPD
  wellFormed := contextAXPDWellFormed

/-- The result fibre of the canonical reflexivity computation is itself a
formed type. It is exactly the weakening of the reflexivity-method type
into the final declaration telescope. -/
theorem identityIotaResultType_hasType :
    NativeIndexedFamilies.Intrinsic.HasType contextAXPD
      identityIotaResultType (sortTm motiveLevel) := by
  have weakened := identityReflCaseType_hasType.weaken
    (extension := identityReflCaseType)
  convert weakened using 1 <;> rfl

/-- The formed result fibre shared by both endpoints of the canonical J
iota equation. -/
def identityIotaResult : TypeOver formedIdentityContext where
  code := identityIotaResultType
  level := .sort motiveLevel
  isUniverse := .sort motiveLevel
  formed := identityIotaResultType_hasType

/-- The canonical declaration-aware J receipt, viewed as one typed native
root cell of the syntactic natural model. -/
def identityIotaCell : NativeIotaCell formedIdentityContext :=
  NativeIotaCell.ofReceipt identityIotaResult identityIotaReceipt

/-- The natural-model image retains exactly the authored J redex. -/
@[simp] theorem identityIotaCell_source_code :
    identityIotaCell.source.code = identityIotaLeft :=
  rfl

/-- The natural-model image retains exactly the reflexivity method. -/
@[simp] theorem identityIotaCell_target_code :
    identityIotaCell.target.code = identityIotaRight :=
  rfl

/-- Canonical path induction computes on reflexivity inside one formed,
proof-relevant judgment fibre. -/
def identityIotaStep :
    (termComputation nativeIotaRetainedRoot formedIdentityContext).Step
      identityIotaCell.source identityIotaCell.target :=
  identityIotaCell.toStep

/-- The same native iota cell generates judgmental conversion without
identifying its endpoint syntax in Lean. -/
def identityIotaConversion :
    ConversionEvidence
      (termComputation nativeIotaRetainedRoot formedIdentityContext)
      identityIotaCell.source identityIotaCell.target :=
  identityIotaCell.toConversion

/-- Every typed instantiation of the declaration telescope receives the
same proof-relevant J computation by native substitution. -/
def identityIotaInstance {context : FormedContext rules}
    (substitution : context ⟶ formedIdentityContext) :
    NativeIotaCell context :=
  identityIotaCell.reindex substitution

/-- The canonical J computation is nontrivial at the syntax level. -/
theorem identityIota_endpoints_not_equal :
    identityIotaCell.source.code ≠ identityIotaCell.target.code := by
  decide

/-- Negative control: the authored identity iota evidence cannot rewrite the
canonical redex to the motive binder instead of the reflexivity method. -/
theorem wrongIdentityTarget_has_noEvidence :
    IsEmpty (IotaEvidence 4 identityIotaLeft (.var 1)) := by
  constructor
  intro evidence
  cases evidence

/-! ## Axiom audit -/

#print axioms nativeIotaRetainedRoot
#print axioms NativeIotaCell.ofReceipt
#print axioms NativeIotaCell.toStep
#print axioms NativeIotaCell.toConversion
#print axioms NativeIotaCell.reindex
#print axioms NativeIotaCell.toStep_reindex
#print axioms contextAXPDWellFormed
#print axioms identityIotaResultType_hasType
#print axioms identityIotaCell
#print axioms identityIotaConversion
#print axioms identityIota_endpoints_not_equal
#print axioms wrongIdentityTarget_has_noEvidence

end SyntacticJudgmentalIdentityEliminator
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
