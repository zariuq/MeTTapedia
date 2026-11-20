import Mettapedia.Languages.HOLLight.CachedSourceProfileTransport
import Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment
import Mettapedia.Languages.HOLLight.QuantifierExpansion
import Mettapedia.Languages.HOLLight.InferenceOnlyReplay
import Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.RegisteredProofBlocks

/-!
# Checked named universal generalization from source definitions

The function-level conversion replaces T in the actual defining equation of
the named universal operator. It is constructed before a predicate is applied,
so constants or inner quantifiers in that predicate remain literal. Source
definition facts must be read and discharged by the existing primitive compiler;
their printed names do not grant a conversion or theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeNamedGeneralization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open StandardTheoryInterpretation CachedSourceDefinitionTable

def truthBinding : Binding where
  key := ⟨.prop, Interpretation.Symbols.truth⟩
  body := HOL.HOLLightBooleanDefinitions.truth

def universalBinding (domain : HOL.Ty AtomicTy) : Binding where
  key := ⟨(domain.arr .prop).arr .prop, Interpretation.Symbols.universal domain⟩
  body := .lam (.eq (.var .vz) (.lam (.const Interpretation.Symbols.truth)))

def functionEquation (domain : HOL.Ty AtomicTy) : HOL.ClosedFormula Symbol :=
  .eq (.const (Interpretation.Symbols.universal domain))
    (HOL.HOLLightBooleanDefinitions.universal domain)

def functionTask (domain : HOL.Ty AtomicTy) : CachedSourceExpansion.Task :=
  CachedSourceDefinitionTable.task [truthBinding] (universalBinding domain).equation

theorem truth_replacement :
    replacement [truthBinding] Interpretation.Symbols.truth = truthBinding.body :=
  image_here_body truthBinding []

theorem universal_retained (domain : HOL.Ty AtomicTy) :
    replacement [truthBinding] (Interpretation.Symbols.universal domain) =
      .const (Interpretation.Symbols.universal domain) := by
  apply image_missing
  intro binding member
  have same : binding = truthBinding := List.mem_singleton.mp member
  subst binding
  intro impossible
  have types := congrArg Sigma.fst impossible
  cases types

theorem functionTask_target (domain : HOL.Ty AtomicTy) :
    (functionTask domain).target = functionEquation domain := by
  simp only [functionTask, CachedSourceDefinitionTable.task, applyTerm, universalBinding,
    Binding.equation, HOL.substConst, HOL.weakenCtx_nil,
    functionEquation, HOL.HOLLightBooleanDefinitions.universal]
  rw [universal_retained, truth_replacement]
  rfl

theorem functionTask_source (domain : HOL.Ty AtomicTy) :
    (functionTask domain).source = (universalBinding domain).equation := rfl

theorem functionTask_theory (domain : HOL.Ty AtomicTy) :
    (functionTask domain).theory = [truthBinding.equation] := rfl

/-- The existing checked source-expansion compiler reads the actual universal
definition and truth definition, rather than accepting a conversion premise. -/
def functionConversion? (domain : HOL.Ty AtomicTy) (state : ProofExecution.State)
    (universalRoot truthRoot : Nat) (origin : ProofExecution.Origin) :
    Option (ProofExecution.State × Nat) :=
  (functionTask domain).compileAndClose? origin state [universalRoot, truthRoot]

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

theorem functionConversion_checked (domain : HOL.Ty AtomicTy)
    {premises : List Theorem} {state : ProofExecution.State}
    (universalRoot truthRoot : Nat)
    (sources : CachedSourceExpansion.Sources state
      [(universalBinding domain).equation, truthBinding.equation])
    (read : CachedSourceExpansion.readAll? state
      [(universalBinding domain).equation, truthBinding.equation] [universalRoot, truthRoot] = some sources)
    (earlier : GraphExpansion.BuildChecked emptyAxiomPolicy premises state)
    (origin : ProofExecution.Origin) :
    ∃ after root fact,
      functionConversion? domain state universalRoot truthRoot origin = some (after, root) ∧
      GraphExpansion.BuildChecked emptyAxiomPolicy premises after ∧
      after.cache[root]? = some fact ∧ fact.sequent.hyp = ∅ ∧
      fact.sequent.concl = CachedSourceExpansion.encode (functionEquation domain) ∧
      fact.axioms = CachedHypothesisList.dependencies (sources.entries.map Prod.snd) ∧
      ∀ (index : Nat) (old : Theorem), state.cache[index]? = some old → after.cache[index]? = some old := by
  obtain ⟨after, root, computed, checked, found, closed, conclusion, axioms, _, preserved⟩ :=
    CachedSourceExpansion.Task.compileAndClose_checked (functionTask domain) origin
      [universalRoot, truthRoot] sources read earlier
  refine ⟨after, root, _, computed, checked, found, closed, ?_, axioms, preserved⟩
  simpa only [functionTask_target] using conclusion

theorem missing_truth_refused (domain : HOL.Ty AtomicTy) (state : ProofExecution.State)
    (universalRoot truthRoot : Nat) (missing : state.cache[truthRoot]? = none)
    (origin : ProofExecution.Origin) :
    functionConversion? domain state universalRoot truthRoot origin = none := by
  have missingRead : CachedSourceExpansion.read? state truthRoot truthBinding.equation = none := by
    unfold CachedSourceExpansion.read?
    split
    · rfl
    · rename_i fact found
      have impossible : (none : Option Theorem) = some fact := missing.symm.trans found
      cases impossible
  have missingAll : CachedSourceExpansion.readAll? state
      [(universalBinding domain).equation, truthBinding.equation] [universalRoot, truthRoot] = none := by
    simp only [CachedSourceExpansion.readAll?, missingRead, bind, Option.bind_none]
    cases CachedSourceExpansion.read? state universalRoot (universalBinding domain).equation <;> rfl
  unfold functionConversion? CachedSourceExpansion.Task.compileAndClose?
  simp only [functionTask_source, functionTask_theory]
  rw [missingAll]
  rfl

def namedOperator (domain : Ty) : CanonicalTerm :=
  ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
    (.const (Interpretation.Symbols.universal domain.toHOL))

def inlineOperator (domain : Ty) : CanonicalTerm :=
  ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
    (HOL.HOLLightBooleanDefinitions.universal domain.toHOL)

structure CheckedBlock (policy : AxiomPolicy) [DecidablePred policy] (premises : List Theorem) where
  certificate : ProofSystem.Certificate
  result : Theorem
  checked : GraphExpansion.BlockChecked policy premises result certificate

/-- This only packages the existing primitive replay result. It supplies no
new rule, signature formation or source-model authority. -/
def checkBlock? (policy : AxiomPolicy) [DecidablePred policy] (premises : List Theorem)
    (certificate : ProofSystem.Certificate) : Option (CheckedBlock policy premises) :=
  match replayed : DerivationGraph.replayFrom (ruleWitness policy)
      premises.toArray certificate.1 with
  | none => none
  | some cache =>
      match found : cache[certificate.2]? with
      | none => none
      | some result => some ⟨certificate, result, cache, replayed, found⟩

structure NamedBlock (policy : AxiomPolicy) [DecidablePred policy]
    (input conversion : Theorem) (binder : SourceVar) where
  block : CheckedBlock policy [input, conversion]
  conclusion : block.result.sequent.concl.term =
    .app (namedOperator binder.ty).term (input.sequent.concl.abstractFree binder).term
  inferenceOnly : InferenceOnlyReplay.inferenceOnly block.certificate.1 = true

/-- GEN uses the existing primitive expansion; the named-operator conversion
is an actual external premise. The complete local certificate is rechecked
before returning its exact named conclusion. -/
def namedGenBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (input conversion : Theorem) (binder : SourceVar) (origin : ProofExecution.Origin) :
    Option (NamedBlock policy input conversion binder) := do
  let gen ← QuantifierExpansion.genBlock? policy input binder origin
  let (left, right) ← conversion.sequent.concl.destEquality?
  let _ ← if left.term.same (namedOperator binder.ty).term then some () else none
  let _ ← if right.term.same (inlineOperator binder.ty).term then some () else none
  if sameType : Ty.same left.ty right.ty = true then
    let sameType := (Ty.same_eq_true_iff _ _).mp sameType
    let initial := GraphExpansion.start [input, conversion]
    let (generalized, genRoot) ← GraphExpansion.emitBlock policy [0] gen initial
    let (reversed, reverseRoot) ← EqualityExpansion.emitSymmetry policy conversion left right sameType
      1 origin generalized
    let predicate := input.sequent.concl.abstractFree binder
    let (reflexive, reflexiveRoot) ← GraphExpansion.emit policy (.inference (.refl predicate)) [] origin reversed
    let reverseFact ← reflexive.cache[reverseRoot]?
    let reflexiveFact ← reflexive.cache[reflexiveRoot]?
    let (applied, appliedRoot) ← GraphExpansion.emit policy (.inference (.mkComb reverseFact reflexiveFact))
      [reverseRoot, reflexiveRoot] origin reflexive
    let application ← applied.cache[appliedRoot]?
    let generalizedFact ← applied.cache[genRoot]?
    let (final, finalRoot) ← GraphExpansion.emit policy (.inference (.eqMp application generalizedFact))
      [appliedRoot, genRoot] origin applied
    let block ← checkBlock? policy [input, conversion] (GraphExpansion.finish final finalRoot)
    if exact : block.result.sequent.concl.term.same
        (.app (namedOperator binder.ty).term predicate.term) = true then
      if only : InferenceOnlyReplay.inferenceOnly block.certificate.1 = true then
        return ⟨block, (DBTerm.same_eq_true_iff _ _).mp exact, only⟩
      else none
    else none
  else none

theorem captured_variable_refused (policy : AxiomPolicy) [DecidablePred policy]
    (input conversion : Theorem) (binder : SourceVar) (origin : ProofExecution.Origin)
    (captured : FreeInHypotheses binder input.sequent.hyp) :
    namedGenBlock? policy input conversion binder origin = none := by
  unfold namedGenBlock?
  rw [QuantifierExpansion.genBlock?_refuses_captured_variable policy input binder captured origin]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeNamedGeneralization
