import Mettapedia.Languages.HOLLight.AdmittedSourcePayloads
import Mettapedia.Languages.HOLLight.NaturalPrimitiveProfiles
import Mettapedia.Languages.HOLLight.ConstructorSeparationProfile
import Mettapedia.Languages.HOLLight.ConstructorInjectivityProfile
import Mettapedia.Languages.HOLLight.RecursiveSpaceInductionProfile

/-!
# Checked native profiles at admitted payload instances

The law selector retains the six original source addresses. Each installation
uses the shared profile compiler, checks the actual source and definition
roots, and returns the emitted graph with its exact conclusion, dependencies
and receipt count. Constructor fields come from the separately checked payload
instance; no constructor-specific inference is added.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedPrimitiveProfiles

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open CachedSourceProfileTransport CachedSourceDefinitionTable

inductive Law where
  | naturalSeparation
  | naturalInjectivity
  | naturalInduction
  | constructorSeparation
  | constructorInjectivity
  | recursiveInduction
  deriving DecidableEq, Repr

def Law.all : List Law := [
  .naturalSeparation, .naturalInjectivity, .naturalInduction,
  .constructorSeparation, .constructorInjectivity, .recursiveInduction]

theorem Law.mem_all (law : Law) : law ∈ Law.all := by
  cases law <;> simp [Law.all]

def Law.profile (operations : RecursiveSpaceSourceReadback.Operations) : Law → Profile
  | .naturalSeparation => NaturalPrimitiveProfiles.separation operations.natural
  | .naturalInjectivity => NaturalPrimitiveProfiles.injectivity operations.natural
  | .naturalInduction => NaturalPrimitiveProfiles.induction operations.natural
  | .constructorSeparation => ConstructorSeparationProfile.profile operations.recursive
  | .constructorInjectivity => ConstructorInjectivityProfile.profile operations.recursive
  | .recursiveInduction => RecursiveSpaceInductionProfile.profile operations.recursive

def Law.sourceIndex (indices : RecursiveSpaceSourceReadback.CacheIndices) : Law → Nat
  | .naturalSeparation => indices.successorSeparation
  | .naturalInjectivity => indices.successorInjective
  | .naturalInduction => indices.naturalInduction
  | .constructorSeparation => indices.constructorSeparation
  | .constructorInjectivity => indices.constructorInjective
  | .recursiveInduction => indices.recursiveInduction

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

structure Installation (profile : Profile) (bindings : List Binding) (depth : Nat)
    (before : ProofExecution.State) (roots : List Nat) (premises : List Theorem)
    (origin : ProofExecution.Origin) where
  sources : CachedSourceExpansion.Sources before (profile.source :: theory bindings)
  alignment : (profile.sourceTask bindings depth).target = profile.unfolded
  after : ProofExecution.State
  root : Nat
  fact : Theorem
  installed : profile.install? bindings depth before roots origin = some (after, root)
  checked : GraphExpansion.BuildChecked emptyAxiomPolicy premises after
  found : after.cache[root]? = some fact
  closed : fact.sequent.hyp = ∅
  conclusion : fact.sequent.concl = CachedSourceExpansion.encode profile.native
  dependencies : fact.axioms = CachedHypothesisList.dependencies (sources.entries.map Prod.snd)
  receiptCount : after.receipts.size = before.receipts.size +
    (profile.compile bindings depth alignment origin).proof.certificate.1.length +
      2 * sources.entries.length

/-- The result is the actual computed installation. Correctness is obtained
from the existing compiler theorem after matching its output and cache slot. -/
def install? (profile : Profile) (bindings : List Binding) (depth : Nat)
    (before : ProofExecution.State) (roots : List Nat) (premises : List Theorem)
    (earlier : GraphExpansion.BuildChecked emptyAxiomPolicy premises before)
    (origin : ProofExecution.Origin) :
    Option (Installation profile bindings depth before roots premises origin) :=
  match matched : profile.matching? bindings depth with
  | none => none
  | some alignment =>
    match read : CachedSourceExpansion.readAll? before (profile.source :: theory bindings) roots with
    | none => none
    | some sources =>
      match installed : profile.install? bindings depth before roots origin with
      | none => none
      | some (after, root) =>
        match found : after.cache[root]? with
        | none => none
        | some fact =>
          have correct : GraphExpansion.BuildChecked emptyAxiomPolicy premises after ∧
              fact.sequent.hyp = ∅ ∧
              fact.sequent.concl = CachedSourceExpansion.encode profile.native ∧
              fact.axioms = CachedHypothesisList.dependencies (sources.entries.map Prod.snd) ∧
              after.receipts.size = before.receipts.size +
                (profile.compile bindings depth alignment.down origin).proof.certificate.1.length +
                  2 * sources.entries.length := by
            obtain ⟨expectedAfter, expectedRoot, expectedFact, computed, checked, expectedFound,
                closed, conclusion, dependencies, receiptCount⟩ :=
              profile.install_checked bindings depth alignment.down matched roots sources read earlier origin
            have sameOutput : (expectedAfter, expectedRoot) = (after, root) :=
              Option.some.inj (computed.symm.trans installed)
            rcases Prod.mk.inj sameOutput with ⟨rfl, rfl⟩
            have sameFact : expectedFact = fact := Option.some.inj (expectedFound.symm.trans found)
            cases sameFact
            exact ⟨checked, closed, conclusion, dependencies, receiptCount⟩
          some ⟨sources, alignment.down, after, root, fact, installed, correct.1, found,
            correct.2.1, correct.2.2.1, correct.2.2.2.1, correct.2.2.2.2⟩

theorem install?_available (profile : Profile) (bindings : List Binding) (depth : Nat)
    (before : ProofExecution.State) (roots : List Nat) (premises : List Theorem)
    (earlier : GraphExpansion.BuildChecked emptyAxiomPolicy premises before)
    (origin : ProofExecution.Origin)
    (alignment : (profile.sourceTask bindings depth).target = profile.unfolded)
    (matched : profile.matching? bindings depth = some ⟨alignment⟩)
    (sources : CachedSourceExpansion.Sources before (profile.source :: theory bindings))
    (read : CachedSourceExpansion.readAll? before (profile.source :: theory bindings) roots = some sources) :
    (install? profile bindings depth before roots premises earlier origin).isSome = true := by
  obtain ⟨after, root, fact, computed, _, found, _⟩ :=
    profile.install_checked bindings depth alignment matched roots sources read earlier origin
  unfold install?
  split
  · simp_all
  · split
    · simp_all
    · split
      · simp_all
      · split
        · simp_all
        · rfl

def Installation.certificate {profile : Profile} {bindings : List Binding} {depth : Nat}
    {before : ProofExecution.State} {roots : List Nat} {premises : List Theorem}
    {origin : ProofExecution.Origin}
    (result : Installation profile bindings depth before roots premises origin) : ProofSystem.Certificate :=
  GraphExpansion.finish result.after result.root

theorem Installation.certificate_checked {profile : Profile} {bindings : List Binding} {depth : Nat}
    {before : ProofExecution.State} {roots : List Nat} {premises : List Theorem}
    {origin : ProofExecution.Origin}
    (result : Installation profile bindings depth before roots premises origin) :
    GraphExpansion.BlockChecked emptyAxiomPolicy premises result.fact result.certificate :=
  GraphExpansion.finish_checked result.checked result.found

def installLaw? (operations : RecursiveSpaceSourceReadback.Operations)
    (indices : RecursiveSpaceSourceReadback.CacheIndices) (law : Law)
    (bindings : List Binding) (definitionRoots : List Nat) (depth : Nat)
    (before : ProofExecution.State) (premises : List Theorem)
    (earlier : GraphExpansion.BuildChecked emptyAxiomPolicy premises before)
    (origin : ProofExecution.Origin) :=
  install? (law.profile operations) bindings depth before
    (law.sourceIndex indices :: definitionRoots) premises earlier origin

def installAdmitted? {policy : AxiomPolicy} [DecidablePred policy]
    {before : ProofExecution.Registered.State} {operations : RecursiveSpaceSourceReadback.Operations}
    {parameter : Name} {fields : List (List (HOL.Ty AtomicTy))}
    (admitted : AdmittedSourcePayloads.Instance policy before operations parameter fields)
    (law : Law) (bindings : List Binding) (definitionRoots : List Nat) (depth : Nat)
    (state : ProofExecution.State) (premises : List Theorem)
    (earlier : GraphExpansion.BuildChecked emptyAxiomPolicy premises state)
    (origin : ProofExecution.Origin) :=
  installLaw? (AdmittedSourcePayloads.targetOperations operations parameter fields)
    admitted.source.indices law bindings definitionRoots depth state premises earlier origin

section PayloadTransport

open HOL

private def castPayload {number payload target space : HOL.Ty AtomicTy}
    (same : payload = target)
    (constructor : HOL.ClosedTerm Symbol
      (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)) :
    HOL.ClosedTerm Symbol (number ⇒ target ⇒ (number ⇒ space) ⇒ space) :=
  same ▸ constructor

private theorem castPayload_statement {number payload target space : HOL.Ty AtomicTy}
    (same : payload = target)
    (constructor : HOL.ClosedTerm Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)) :
    HOL.ConstructorInjectivity.statement (castPayload same constructor) =
      HOL.ConstructorInjectivity.statement constructor := by
  cases same
  rfl

private theorem weakenCtx_statement {number payload space : HOL.Ty AtomicTy}
    (context : HOL.Ctx AtomicTy)
    (constructor : HOL.ClosedTerm Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)) :
    HOL.weakenCtx context (HOL.ConstructorInjectivity.statement constructor) =
      HOL.ConstructorInjectivity.statement (HOL.weakenCtx context constructor) := by
  induction context with
  | nil => rfl
  | cons domain context ih =>
      simp only [HOL.weakenCtx_cons, ih, HOL.weaken, HOL.ConstructorInjectivity.rename_statement]

variable {policy : AxiomPolicy} [DecidablePred policy]
    {before : ProofExecution.Registered.State} {operations : RecursiveSpaceSourceReadback.Operations}
    {parameter : Name} {fields : List (List (HOL.Ty AtomicTy))}
    (admitted : AdmittedSourcePayloads.Instance policy before operations parameter fields)

/-- The source constructor at the exact predicate-handler payload expected
by the admitted inventory. Only its proved simple-type equality is used. -/
def constructor : HOL.ClosedTerm Symbol
    ((AdmittedSourcePayloads.targetOperations operations parameter fields).number.toHOL ⇒
      HOL.FiniteConstructorEncoding.payloadType fields ⇒
      ((AdmittedSourcePayloads.targetOperations operations parameter fields).number.toHOL ⇒
        (AdmittedSourcePayloads.targetOperations operations parameter fields).space.toHOL) ⇒
      (AdmittedSourcePayloads.targetOperations operations parameter fields).space.toHOL) :=
  castPayload admitted.payload_toHOL
    (AdmittedSourcePayloads.targetOperations operations parameter fields).recursive.construct

theorem constructor_statement :
    HOL.ConstructorInjectivity.statement (constructor admitted) =
      ConstructorInjectivityProfile.native
        (AdmittedSourcePayloads.targetOperations operations parameter fields).recursive :=
  (castPayload_statement admitted.payload_toHOL _).trans
    (ConstructorInjectivityProfile.native_is_statement _).symm

/-- This is precisely the premise shape of the generic admitted induction
consumer, including an arbitrary open surrounding context. -/
def injectivityAt (context : HOL.Ctx AtomicTy) {assumptions : List (HOL.Formula Symbol context)}
    (proof : HOL.ProofSyntax Symbol assumptions
      (HOL.weakenCtx context (ConstructorInjectivityProfile.native
        (AdmittedSourcePayloads.targetOperations operations parameter fields).recursive))) :
    HOL.ProofSyntax Symbol assumptions
      (HOL.ConstructorInjectivity.statement (HOL.weakenCtx context (constructor admitted))) :=
  HOL.ProofSyntax.castIndices rfl
    ((congrArg (HOL.weakenCtx context) (constructor_statement admitted).symm).trans
      (weakenCtx_statement context (constructor admitted))) proof

theorem injectivityAt_free (context : HOL.Ctx AtomicTy) {assumptions : List (HOL.Formula Symbol context)}
    (proof : HOL.ProofSyntax Symbol assumptions
      (HOL.weakenCtx context (ConstructorInjectivityProfile.native
        (AdmittedSourcePayloads.targetOperations operations parameter fields).recursive)))
    (free : proof.FunctionExtensionalityFree) :
    (injectivityAt admitted context proof).FunctionExtensionalityFree :=
  (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

end PayloadTransport

#print axioms Law.mem_all
#print axioms install?
#print axioms install?_available
#print axioms Installation.certificate_checked
#print axioms installAdmitted?
#print axioms constructor_statement
#print axioms injectivityAt_free

end Mettapedia.Languages.HOLLight.AdmittedPrimitiveProfiles
