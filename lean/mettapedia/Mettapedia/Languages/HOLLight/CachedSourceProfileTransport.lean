import Mettapedia.Languages.HOLLight.CachedSourceDefinitionClosure
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Checked source-profile transport

A profile supplies its retained conversion proof and exact native image.
The shared implementation constructs definition unfolding, certifies its
typed intermediate syntax, compiles the composed proof and discharges the
actual source cache entries. Profiles do not select a foundation or admit
new axioms. The interface is over the existing HOL source language.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CachedSourceProfileTransport

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL CachedSourceDefinitionTable

theorem readable_equal {Γ : Ctx AtomicTy} {type : Ty AtomicTy}
    {first second : Term Symbol Γ type}
    (firstReadable : ExactFormulaReadback.readable first = true)
    (secondReadable : ExactFormulaReadback.readable second = true)
    (encoded : ReverseTranslation.reverseTermOpen first = ReverseTranslation.reverseTermOpen second) :
    first = second := by
  have firstRead := ExactFormulaReadback.readable_translates first firstReadable
  rw [encoded] at firstRead
  exact firstRead.unique_eq (ExactFormulaReadback.readable_translates second secondReadable)

def sameReadable? {Γ : Ctx AtomicTy} {type : Ty AtomicTy} (first second : Term Symbol Γ type) :
    Option (PLift (first = second)) :=
  if firstReadable : ExactFormulaReadback.readable first = true then
    if secondReadable : ExactFormulaReadback.readable second = true then
      if encoded : DBTerm.same (ReverseTranslation.reverseTermOpen first)
          (ReverseTranslation.reverseTermOpen second) = true then
        some ⟨readable_equal firstReadable secondReadable ((DBTerm.same_eq_true_iff _ _).mp encoded)⟩
      else none
    else none
  else none

def supply {Γ : Ctx AtomicTy} {assumptions : List (Formula Symbol Γ)}
    {first second : Formula Symbol Γ} (premise : ProofSyntax Symbol assumptions first)
    (continuation : ProofSyntax Symbol [first] second) : ProofSyntax Symbol assumptions second :=
  ProofSyntax.substituteHypothesesCached
    (ProofSyntax.HypothesisSubstitution.Table.cons premise .nil).get continuation

theorem supply_free {Γ : Ctx AtomicTy} {assumptions : List (Formula Symbol Γ)}
    {first second : Formula Symbol Γ} (premise : ProofSyntax Symbol assumptions first)
    (continuation : ProofSyntax Symbol [first] second)
    (premiseFree : premise.FunctionExtensionalityFree)
    (continuationFree : continuation.FunctionExtensionalityFree) :
    (supply premise continuation).FunctionExtensionalityFree := by
  unfold supply
  rw [ProofSyntax.substituteHypothesesCached_eq]
  apply ProofSyntax.substituteHypotheses_free _ _ continuationFree
  intro occurrence
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
  exact premiseFree

structure Profile where
  source : ClosedFormula Symbol
  unfolded : ClosedFormula Symbol
  target : ClosedFormula Symbol
  native : ClosedFormula Symbol
  conversion : ProofSyntax Symbol [unfolded] target
  conversionFree : conversion.FunctionExtensionalityFree
  nativeImage : CachedSourceExpansion.encode target = CachedSourceExpansion.encode native

namespace Profile

def post (profile : Profile) (target native : ClosedFormula Symbol)
    (conversion : ProofSyntax Symbol [profile.target] target)
    (free : conversion.FunctionExtensionalityFree)
    (image : CachedSourceExpansion.encode target = CachedSourceExpansion.encode native) : Profile where
  source := profile.source
  unfolded := profile.unfolded
  target := target
  native := native
  conversion := supply profile.conversion conversion
  conversionFree := supply_free _ _ profile.conversionFree free
  nativeImage := image

def sourceTask (profile : Profile) (bindings : List Binding) (depth : Nat) :=
  CachedSourceDefinitionClosure.task bindings depth profile.source

def matching? (profile : Profile) (bindings : List Binding) (depth : Nat) :
    Option (PLift ((profile.sourceTask bindings depth).target = profile.unfolded)) :=
  sameReadable? (profile.sourceTask bindings depth).target profile.unfolded

def sourceProof (profile : Profile) (bindings : List Binding) (depth : Nat)
    (alignment : (profile.sourceTask bindings depth).target = profile.unfolded) :
    ProofSyntax Symbol (profile.source :: theory bindings) profile.target :=
  supply (ProofSyntax.castIndices rfl alignment (profile.sourceTask bindings depth).proof)
    profile.conversion

theorem sourceProof_free (profile : Profile) (bindings : List Binding) (depth : Nat)
    (alignment : (profile.sourceTask bindings depth).target = profile.unfolded) :
    (profile.sourceProof bindings depth alignment).FunctionExtensionalityFree := by
  apply supply_free _ _ ?_ profile.conversionFree
  exact (ProofSyntax.functionExtensionalityFree_castIndices rfl alignment _).mpr
    (profile.sourceTask bindings depth).proof_free

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def compile (profile : Profile) (bindings : List Binding) (depth : Nat)
    (alignment : (profile.sourceTask bindings depth).target = profile.unfolded)
    (origin : ProofExecution.Origin) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    (profile.sourceProof bindings depth alignment) (profile.sourceProof_free bindings depth alignment)
    ReverseTranslation.Naming.empty origin

theorem compile_conclusion (profile : Profile) (bindings : List Binding) (depth : Nat)
    (alignment : (profile.sourceTask bindings depth).target = profile.unfolded)
    (origin : ProofExecution.Origin) :
    (profile.compile bindings depth alignment origin).proof.result.sequent.concl =
      CachedSourceExpansion.encode profile.native :=
  (profile.compile bindings depth alignment origin).conclusion_exact.trans profile.nativeImage

theorem compile_axioms (profile : Profile) (bindings : List Binding) (depth : Nat)
    (alignment : (profile.sourceTask bindings depth).target = profile.unfolded)
    (origin : ProofExecution.Origin) :
    (profile.compile bindings depth alignment origin).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _
      (profile.compile bindings depth alignment origin).proof.accepted))

theorem compile_covered (profile : Profile) (bindings : List Binding) (depth : Nat)
    (alignment : (profile.sourceTask bindings depth).target = profile.unfolded)
    (origin : ProofExecution.Origin) {state : ProofExecution.State}
    (sources : CachedSourceExpansion.Sources state (profile.source :: theory bindings)) :
    (profile.compile bindings depth alignment origin).proof.result.sequent.hyp =
      (sources.entries.map (fun entry => entry.2.sequent.concl)).toFinset := by
  rw [(profile.compile bindings depth alignment origin).hypotheses_exact, sources.conclusions]
  simp only [ReverseTranslation.reverseHypotheses, List.map_map, Function.comp_def]
  rfl

def install? (profile : Profile) (bindings : List Binding) (depth : Nat)
    (state : ProofExecution.State) (roots : List Nat) (origin : ProofExecution.Origin) :
    Option (ProofExecution.State × Nat) := do
  let alignment ← profile.matching? bindings depth
  let sources ← CachedSourceExpansion.readAll? state (profile.source :: theory bindings) roots
  let compiled := profile.compile bindings depth alignment.down origin
  let (after, root) ← GraphExpansion.emitBlock emptyAxiomPolicy [] compiled.proof.certificate state
  CachedHypothesisList.closeAndRequire? emptyAxiomPolicy after (sources.entries.map Prod.fst) root origin

theorem install_checked (profile : Profile) (bindings : List Binding) (depth : Nat)
    (alignment : (profile.sourceTask bindings depth).target = profile.unfolded)
    (matched : profile.matching? bindings depth = some ⟨alignment⟩)
    {premises : List Theorem} {state : ProofExecution.State} (roots : List Nat)
    (sources : CachedSourceExpansion.Sources state (profile.source :: theory bindings))
    (read : CachedSourceExpansion.readAll? state (profile.source :: theory bindings) roots = some sources)
    (earlier : GraphExpansion.BuildChecked emptyAxiomPolicy premises state)
    (origin : ProofExecution.Origin) :
    ∃ after root fact,
      profile.install? bindings depth state roots origin = some (after, root) ∧
      GraphExpansion.BuildChecked emptyAxiomPolicy premises after ∧
      after.cache[root]? = some fact ∧ fact.sequent.hyp = ∅ ∧
      fact.sequent.concl = CachedSourceExpansion.encode profile.native ∧
      fact.axioms = CachedHypothesisList.dependencies (sources.entries.map Prod.snd) ∧
      after.receipts.size = state.receipts.size +
        (profile.compile bindings depth alignment origin).proof.certificate.1.length +
        2 * sources.entries.length := by
  let compiled := profile.compile bindings depth alignment origin
  have compiledBool : compiled.proof.result.sequent.concl.IsBool := by
    rw [profile.compile_conclusion]
    exact ReverseTranslation.reverseCanonical_isBool ReverseTranslation.Naming.empty _
  obtain ⟨middle, next, emitted, middleChecked, nextFound, _, firstPreserved⟩ :=
    GraphExpansion.emitBlock_checked earlier
      (show DerivationGraph.lookupPremises state.cache [] = some [] from rfl) compiled.proof.blockChecked
  obtain ⟨after, root, closed, afterChecked, rootFound, noHypotheses, closeSize⟩ :=
    CachedHypothesisList.closeAndRequire_checked sources.entries middleChecked nextFound
      (fun entry present => firstPreserved _ _ (sources.found entry present))
      (fun entry present => (sources.boolean entry present).trans compiledBool.symm)
      sources.closed (profile.compile_covered bindings depth alignment origin sources).le origin
  refine ⟨after, root, _, ?_, afterChecked, rootFound, noHypotheses, ?_, ?_, ?_⟩
  · unfold install?
    rw [matched, read]
    change ((GraphExpansion.emitBlock emptyAxiomPolicy [] compiled.proof.certificate state).bind fun next =>
      CachedHypothesisList.closeAndRequire? emptyAxiomPolicy next.1
        (sources.entries.map Prod.fst) next.2 origin) = some (after, root)
    rw [emitted]
    exact closed
  · exact (CachedHypothesisList.result_conclusion _ _).trans
      (profile.compile_conclusion bindings depth alignment origin)
  · rw [CachedHypothesisList.result_axioms, profile.compile_axioms, Finset.union_empty]
  · have compileSize := (GraphExpansion.emitBlock_size emitted).2
    change after.receipts.size = state.receipts.size + compiled.proof.certificate.1.length +
      2 * sources.entries.length
    omega

end Profile

#print axioms readable_equal
#print axioms supply_free
#print axioms Profile.sourceProof_free
#print axioms Profile.compile_conclusion
#print axioms Profile.install_checked

end Mettapedia.Languages.HOLLight.CachedSourceProfileTransport
