import Mettapedia.Languages.VibeITP.Presentation.SimultaneousMeaning
import Mettapedia.Languages.VibeITP.Presentation.Soundness

/-!
# Legacy rules under the v2 theorem meaning

All operational rules and old theorem leaves transfer by their outer judgment
heads. Only modus ponens and single instantiation consume theorem premises;
their existing syntax inversions now use the v2 closure laws. No legacy rule,
meaning, validated package, or portable artifact is modified.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Spec

theorem mp_meaning (T : Theory) (a b ann : Pattern)
    (implication : MeaningV2 T (jThm (cApp patImpl (cCons a (cCons b cNil)) ann)))
    (premise : MeaningV2 T (jThm a)) : MeaningV2 T (jThm b) := by
  change ThmMV2 T _ at implication premise ⊢
  obtain ⟨source, encoded, derived⟩ := implication
  obtain ⟨symbol, arguments, rfl, symbolCode, argumentCode, _⟩ :=
    encTerm_eq_app T.sig source _ _ _ encoded.symm
  have symbolIsImpl : symbol = .builtin .impl := patBuiltinSym_eq symbolCode
  subst symbolIsImpl
  obtain ⟨antecedent, rest, rfl, firstCode, restCode⟩ :=
    encTermList_eq_cons T.sig arguments a _ argumentCode.symm
  obtain ⟨conclusion, tail, rfl, lastCode, tailCode⟩ :=
    encTermList_eq_cons T.sig rest b _ restCode.symm
  have empty := encTermList_eq_nil T.sig tail tailCode.symm
  subst empty
  obtain ⟨actual, actualCode, proof⟩ := premise
  have same : actual = antecedent := encTerm_inj T.sig (actualCode.symm.trans firstCode)
  subst same
  exact ⟨conclusion, lastCode, .modusPonens derived proof⟩

theorem single_instantiation_meaning (T : Theory) (phi fid fbs n v dv psi : Pattern)
    (h1 : MeaningV2 T (jThm phi))
    (h2 : MeaningV2 T (jSymDecl (cSym fid cKFvar fbs)))
    (h3 : MeaningV2 T (jLen fbs n)) (h4 : MeaningV2 T (jWf v))
    (h5 : MeaningV2 T (jDepth v dv)) (h6 : MeaningV2 T (jNLe dv n))
    (h7 : MeaningV2 T (jInst (cSym fid cKFvar fbs) v n cN0 phi psi))
    (h8 : MeaningV2 T (jDepth psi cN0)) : MeaningV2 T (jThm psi) := by
  change ThmMV2 T phi at h1
  change SymDeclM T.sig (cSym fid cKFvar fbs) at h2
  change LenM fbs n at h3
  change WfM T.sig v at h4
  change DepthM T.sig v dv at h5
  change NLeM dv n at h6
  change InstM T.sig (cSym fid cKFvar fbs) v n cN0 phi psi at h7
  change DepthM T.sig psi cN0 at h8
  change ThmMV2 T psi
  obtain ⟨source, rfl, derived⟩ := h1
  obtain ⟨symbol, known, rfl, kind, rfl⟩ := symDecl_inv h2
  have free : kindOf T.sig symbol = .fvar := encKind_inj kind.symm
  obtain ⟨value, rfl, formed⟩ := h4
  have arity := h3 _ (decList_encNatList _)
  rw [List.length_map] at arity
  have depth := h5 value rfl
  obtain ⟨actualDepth, depthRead, bounded⟩ := h6 _ arity
  rw [depth, decNat_encNat] at depthRead
  cases depthRead
  have declared : IsFvarOf T.sig symbol (bindersOf T.sig symbol).length :=
    ⟨known, free, symArity_eq T.sig symbol⟩
  obtain ⟨result, instantiated, rfl⟩ := h7 symbol _ value 0 source declared
    (by rw [encSym_eq, free]; rfl) (decNat_unique n _ arity) rfl rfl rfl
  have closed := encNat_eq_N0 (h8 result rfl)
  obtain ⟨info, allocated⟩ := Option.isSome_iff_exists.mp known
  have infoFree : info.kind = .fvar := by simpa [kindOf, allocated] using free
  have infoArity : (bindersOf T.sig symbol).length = info.arity := by
    simp [bindersOf, allocated, SymInfo.arity]
  refine ⟨result, rfl, DerivesWithExecutionV2.instantiate (symbol := symbol) derived formed ?_⟩
  simp only [instantiateStatement, allocated]
  rw [if_pos ⟨infoFree, by rw [← infoArity]; exact bounded⟩, ← infoArity, instantiated]
  simp only [closed, if_true]

set_option maxRecDepth 100000 in
theorem kernel_rule_classes {rule : FORule} (member : rule ∈ kernelRules) :
    rule = rMp ∨ rule = rInst ∨ legacyLeafRule rule = true := by
  have checked : kernelRules.all (fun rule =>
      decide (rule = rMp ∨ rule = rInst ∨ legacyLeafRule rule = true)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked rule member)

theorem legacy_kernel_sound (T : Theory) {allocated : Nat} (hosted : Hosted T allocated)
    {rule : FORule} (member : rule ∈ kernelRules) : RuleMeaningSoundV2 T rule := by
  rcases kernel_rule_classes member with rfl | rfl | leaf
  · exact sound_rMp (mp_meaning T)
  · exact sound_rInst (single_instantiation_meaning T)
  · exact transfer_legacy_leaf T rule leaf (kernelRules_meaningSound T hosted member)

theorem theory_rule_leaf (T : Theory) (allocated : Nat) {rule : FORule}
    (member : rule ∈ theoryRules T allocated) : legacyLeafRule rule = true := by
  simp only [theoryRules, List.mem_append] at member
  rcases member with (symbol | axiomRuleMember) | definition
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp symbol
    rfl
  · obtain ⟨index, statement, _, rfl⟩ := mem_axiomRules axiomRuleMember
    rfl
  · obtain ⟨index, declaration, _, rfl⟩ := mem_theoryDefinitionRules definition
    rfl

theorem legacy_theory_sound (T : Theory) (allocated : Nat) (hosted : Hosted T allocated)
    {rule : FORule} (member : rule ∈ theoryRules T allocated) : RuleMeaningSoundV2 T rule :=
  transfer_legacy_leaf T rule (theory_rule_leaf T allocated member) (ms_theoryRules T allocated hosted member)

theorem legacy_hosted_sound (T : Theory) (allocated : Nat) (hosted : Hosted T allocated)
    {rule : FORule} (member : rule ∈ kernelRules ++ theoryRules T allocated) : RuleMeaningSoundV2 T rule := by
  rcases List.mem_append.mp member with fixed | admitted
  · exact legacy_kernel_sound T hosted fixed
  · exact legacy_theory_sound T allocated hosted admitted

#print axioms legacy_kernel_sound
#print axioms legacy_theory_sound

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
