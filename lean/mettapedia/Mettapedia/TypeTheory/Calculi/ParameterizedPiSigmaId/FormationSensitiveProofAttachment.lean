import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveHeadMap
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTelescopeSpine

/-!
# Formation-sensitive attachment along presentation morphisms

An open derivation may be transported along a presentation morphism and then
instantiated by a substitution typed in the target presentation.  This module
states that operation once, independently of HOL, a particular proof family,
or a fixed number of proof arguments.

The proof-relevant `Attachment` record retains the source judgment, the target
context formation, and the typed substitution.  Its target judgment is derived
from those fields.  Postcomposition composes typed substitutions and gives the
same target syntax as successive substitution.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace FormationSensitiveProofAttachment

open Presentation Presentation.FormationSensitive

variable {HeadOne HeadTwo : Type}

/-- Transport an open derivation through a presentation morphism and attach a
target-typed substitution. -/
theorem attachTyping {sourceRules : Rules HeadOne} {targetRules : Rules HeadTwo}
    {map : HeadOne → HeadTwo}
    (morphism : sourceRules.Morphism targetRules map)
    {k n : Nat} {sourceContext : Ctx HeadOne k}
    {targetContext : Ctx HeadTwo n} {body type : Tm HeadOne k}
    {substitution : Sub HeadTwo k n}
    (bodyTyped : Typing sourceRules sourceContext body type)
    (substitutionTyped : Presentation.FormationSensitive.CtxMor targetRules
      (sourceContext.mapHead map) targetContext substitution) :
    Typing targetRules targetContext
      (subst substitution (body.mapHead map))
      (subst substitution (type.mapHead map)) :=
  (bodyTyped.mapHead morphism).substitute substitutionTyped

/-- The complete formation-sensitive judgment version of `attachTyping`. -/
theorem attachJudgment {sourceRules : Rules HeadOne} {targetRules : Rules HeadTwo}
    {map : HeadOne → HeadTwo}
    (morphism : sourceRules.Morphism targetRules map)
    {k n : Nat} {sourceContext : Ctx HeadOne k}
    {targetContext : Ctx HeadTwo n} {body type : Tm HeadOne k}
    {substitution : Sub HeadTwo k n}
    (source : Judgment sourceRules sourceContext body type)
    (targetFormed : ContextFormation targetRules targetContext)
    (substitutionTyped : Presentation.FormationSensitive.CtxMor targetRules
      (sourceContext.mapHead map) targetContext substitution) :
    Judgment targetRules targetContext
      (subst substitution (body.mapHead map))
      (subst substitution (type.mapHead map)) :=
  (source.mapHead morphism).substitute targetFormed substitutionTyped

/-- Conversion is compatible with the same map-then-substitute attachment. -/
theorem attachConversion {sourceRules : Rules HeadOne}
    {targetRules : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (morphism : sourceRules.Morphism targetRules map)
    {k n : Nat} {left right : Tm HeadOne k}
    (substitution : Sub HeadTwo k n)
    (conversion : Conv sourceRules.headEq left right sourceRules.computation) :
    Conv targetRules.headEq
      (subst substitution (left.mapHead map))
      (subst substitution (right.mapHead map)) targetRules.computation :=
  (conversion.mapHead map morphism.headEq morphism.computation).substitute substitution

/-- Identity is a formation-sensitive context morphism. -/
theorem identityCtxMor {n : Nat} (rules : Rules HeadTwo) (context : Ctx HeadTwo n) :
    Presentation.FormationSensitive.CtxMor rules context context ids := by
  intro index
  simpa only [ids, subst_ids] using
    (Typing.var (R := rules) (Γ := context) index)

/-- Formation-sensitive context morphisms compose in the same order as raw
simultaneous substitutions. -/
theorem ctxMorComp {k n m : Nat} {rules : Rules HeadTwo}
    {source : Ctx HeadTwo k} {middle : Ctx HeadTwo n}
    {target : Ctx HeadTwo m} {sigma : Sub HeadTwo k n}
    {tau : Sub HeadTwo n m}
    (sigmaTyped : Presentation.FormationSensitive.CtxMor rules source middle sigma)
    (tauTyped : Presentation.FormationSensitive.CtxMor rules middle target tau) :
    Presentation.FormationSensitive.CtxMor rules source target (subComp tau sigma) := by
  intro index
  have transported := (sigmaTyped index).substitute tauTyped
  change Typing rules target (subst tau (sigma index))
    (subst (fun prior => subst tau (sigma prior)) (Ctx.lookup source index))
  rw [subst_comp] at transported
  exact transported

/-- Data retained by one attachment.  Its target derivation is computed, not
stored as an independent premise. -/
structure Attachment {sourceRules : Rules HeadOne} {targetRules : Rules HeadTwo}
    {map : HeadOne → HeadTwo}
    (morphism : sourceRules.Morphism targetRules map)
    {k n : Nat} (sourceContext : Ctx HeadOne k)
    (targetContext : Ctx HeadTwo n) (body type : Tm HeadOne k) where
  sourceJudgment : Judgment sourceRules sourceContext body type
  targetContextFormed : ContextFormation targetRules targetContext
  substitution : Sub HeadTwo k n
  substitutionTyped : Presentation.FormationSensitive.CtxMor targetRules
    (sourceContext.mapHead map) targetContext substitution

theorem Attachment.targetJudgment
    {sourceRules : Rules HeadOne} {targetRules : Rules HeadTwo}
    {map : HeadOne → HeadTwo}
    {morphism : sourceRules.Morphism targetRules map}
    {k n : Nat} {sourceContext : Ctx HeadOne k}
    {targetContext : Ctx HeadTwo n} {body type : Tm HeadOne k}
    (attachment : Attachment morphism sourceContext targetContext body type) :
    Judgment targetRules targetContext
      (subst attachment.substitution (body.mapHead map))
      (subst attachment.substitution (type.mapHead map)) :=
  attachJudgment morphism attachment.sourceJudgment
    attachment.targetContextFormed attachment.substitutionTyped

/-- Further target substitution preserves the original source derivation and
records the composite substitution. -/
def Attachment.postcompose
    {sourceRules : Rules HeadOne} {targetRules : Rules HeadTwo}
    {map : HeadOne → HeadTwo}
    {morphism : sourceRules.Morphism targetRules map}
    {k n m : Nat} {sourceContext : Ctx HeadOne k}
    {middle : Ctx HeadTwo n} {target : Ctx HeadTwo m}
    {body type : Tm HeadOne k}
    (attachment : Attachment morphism sourceContext middle body type)
    {tau : Sub HeadTwo n m}
    (targetFormed : ContextFormation targetRules target)
    (tauTyped : Presentation.FormationSensitive.CtxMor targetRules middle target tau) :
    Attachment morphism sourceContext target body type where
  sourceJudgment := attachment.sourceJudgment
  targetContextFormed := targetFormed
  substitution := subComp tau attachment.substitution
  substitutionTyped := ctxMorComp attachment.substitutionTyped tauTyped

theorem Attachment.targetTerm_postcompose
    {sourceRules : Rules HeadOne} {targetRules : Rules HeadTwo}
    {map : HeadOne → HeadTwo}
    {morphism : sourceRules.Morphism targetRules map}
    {k n m : Nat} {sourceContext : Ctx HeadOne k}
    {middle : Ctx HeadTwo n} {target : Ctx HeadTwo m}
    {body type : Tm HeadOne k}
    (attachment : Attachment morphism sourceContext middle body type)
    {tau : Sub HeadTwo n m}
    (targetFormed : ContextFormation targetRules target)
    (tauTyped : Presentation.FormationSensitive.CtxMor targetRules middle target tau) :
    subst (attachment.postcompose targetFormed tauTyped).substitution
        (body.mapHead map) =
      subst tau (subst attachment.substitution (body.mapHead map)) := by
  exact (subst_subComp tau attachment.substitution (body.mapHead map)).symm

theorem Attachment.targetType_postcompose
    {sourceRules : Rules HeadOne} {targetRules : Rules HeadTwo}
    {map : HeadOne → HeadTwo}
    {morphism : sourceRules.Morphism targetRules map}
    {k n m : Nat} {sourceContext : Ctx HeadOne k}
    {middle : Ctx HeadTwo n} {target : Ctx HeadTwo m}
    {body type : Tm HeadOne k}
    (attachment : Attachment morphism sourceContext middle body type)
    {tau : Sub HeadTwo n m}
    (targetFormed : ContextFormation targetRules target)
    (tauTyped : Presentation.FormationSensitive.CtxMor targetRules middle target tau) :
    subst (attachment.postcompose targetFormed tauTyped).substitution
        (type.mapHead map) =
      subst tau (subst attachment.substitution (type.mapHead map)) := by
  exact (subst_subComp tau attachment.substitution (type.mapHead map)).symm

/-! ## Same-syntax operation attachment -/

/-- Attach one target-only argument to an open source operation. -/
theorem instantiateOperation {Head : Type}
    {sourceRules targetRules : Rules Head}
    (morphism : sourceRules.Morphism targetRules (fun head => head))
    {n : Nat} {context : Ctx Head n}
    {domain result : Tm Head n} {body : Tm Head (n + 1)}
    {argument : Tm Head n}
    (bodyTyped : Typing sourceRules (.snoc context domain) body (rename wk result))
    (argumentTyped : Typing targetRules context argument domain) :
    Typing targetRules context (subst (consSub argument ids) body) result := by
  have identity : Presentation.FormationSensitive.CtxMor targetRules context context ids :=
    identityCtxMor targetRules context
  have argumentAtIdentity :
      Typing targetRules context argument (subst ids domain) := by
    simpa only [subst_ids] using argumentTyped
  have extended : Presentation.FormationSensitive.CtxMor targetRules (.snoc context domain) context
      (consSub argument ids) := identity.extend argumentAtIdentity
  have attached := attachTyping morphism bodyTyped (by
    simpa only [Ctx.mapHead_id] using extended)
  simpa only [Tm.mapHead_id, subst_consSub_rename_wk, subst_ids] using attached

/-- Attach two target-only arguments to a genuinely dependent two-entry
source telescope. -/
theorem instantiateOperation2 {Head : Type}
    {sourceRules targetRules : Rules Head}
    (morphism : sourceRules.Morphism targetRules (fun head => head))
    {n : Nat} {context : Ctx Head n}
    {firstDomain secondDomain result : Tm Head n}
    {body : Tm Head (n + 2)} {firstArgument secondArgument : Tm Head n}
    (bodyTyped : Typing sourceRules
      (.snoc (.snoc context firstDomain) (rename wk secondDomain)) body
      (rename wk (rename wk result)))
    (firstTyped : Typing targetRules context firstArgument firstDomain)
    (secondTyped : Typing targetRules context secondArgument secondDomain) :
    Typing targetRules context
      (subst (consSub secondArgument (consSub firstArgument ids)) body) result := by
  have identity : Presentation.FormationSensitive.CtxMor targetRules context context ids :=
    identityCtxMor targetRules context
  have firstAtIdentity :
      Typing targetRules context firstArgument (subst ids firstDomain) := by
    simpa only [subst_ids] using firstTyped
  have afterFirst : Presentation.FormationSensitive.CtxMor targetRules
      (.snoc context firstDomain) context
      (consSub firstArgument ids) := identity.extend firstAtIdentity
  have secondAfterFirst : Typing targetRules context secondArgument
      (subst (consSub firstArgument ids) (rename wk secondDomain)) := by
    simpa only [subst_consSub_rename_wk, subst_ids] using secondTyped
  have extended : Presentation.FormationSensitive.CtxMor targetRules
      (.snoc (.snoc context firstDomain) (rename wk secondDomain)) context
      (consSub secondArgument (consSub firstArgument ids)) :=
    afterFirst.extend secondAfterFirst
  have attached := attachTyping morphism bodyTyped (by
    simpa only [Ctx.mapHead_id] using extended)
  simpa only [Tm.mapHead_id, subst_consSub_rename_wk, subst_ids] using attached

#print axioms attachTyping
#print axioms attachJudgment
#print axioms attachConversion
#print axioms Attachment.postcompose
#print axioms Attachment.targetTerm_postcompose
#print axioms Attachment.targetType_postcompose
#print axioms instantiateOperation
#print axioms instantiateOperation2

end FormationSensitiveProofAttachment
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
