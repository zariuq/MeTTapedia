import Mettapedia.Languages.VibeITP.CheckingMachineV2
import Mettapedia.Languages.VibeITP.Native.ProtocolV2LogicalControls
import Mettapedia.Languages.VibeITP.Presentation.KernelControls

/-! Closed and separating controls for the definition-derived crossing fixture.
The mathematical article coverage is existential. The accompanying untrusted
exporter produces concrete articles and submits them to the same checker. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef _root_.CategoryTheory
open Spec SimultaneousInstantiation SimultaneousFormation

def F : SymId := .fresh 0
def G : SymId := .fresh 1
def D : SymId := .fresh 2
def f : Spec.Term := .app F []
def g : Spec.Term := .app G []

def freshInfo (index : Nat) : Option SymInfo :=
  if index < 2 then some (.fvarOf 0)
  else if index = 2 then some ⟨.constant, [0, 0]⟩ else none

def theory : Theory := ⟨sigOf freshInfo, [], [⟨D, [F, G], .eq f g⟩]⟩
def allocated : Nat := 3

theorem hosted : Hosted theory allocated := by
  constructor
  · intro builtin; rfl
  · intro index
    by_cases small : index < 2
    · simp [theory, sigOf, freshInfo, small, allocated]; omega
    · by_cases last : index = 2
      · subst index; decide +kernel
      · simp [theory, sigOf, freshInfo, small, last, allocated]; omega
  · intro symbol info present free binder member
    cases symbol with
    | builtin symbol =>
        have same : info = symbol.info := by simpa [theory, sigOf] using present.symm
        subst info
        simp [Builtin.info] at free
    | fresh index =>
        by_cases small : index < 2
        · simp [theory, sigOf, freshInfo, small] at present
          subst info
          simp [SymInfo.fvarOf] at member
        · by_cases last : index = 2
          · simp [theory, sigOf, freshInfo, last] at present
            subst info
            contradiction
          · simp [theory, sigOf, freshInfo, small, last] at present
  · intro claim member; simp [theory] at member
  · intro definition member
    have same : definition = ⟨D, [F, G], .eq f g⟩ := by simpa [theory] using member
    subst definition
    exact ⟨by decide +kernel, by decide +kernel, [0, 1], by decide +kernel⟩
def source : Spec.Term := definitionStatement theory.sig D [F, G] (.eq f g)
def crossing : Spec.Term := .eq (.app D [g, .natLit 7]) (.eq g (.natLit 7))
def sequential : Spec.Term := .eq (.app D [.natLit 7, .natLit 7]) (.eq (.natLit 7) (.natLit 7))
def replacements : List (SymId × Spec.Term) := [(F, g), (G, .natLit 7)]
def entries : List Entry := [⟨F, 0, g⟩, ⟨G, 0, .natLit 7⟩]

theorem no_axioms : theory.axioms = [] := by decide +kernel
theorem source_is_definition : theory.definitions = [⟨D, [F, G], .eq f g⟩] := rfl
theorem prepared : prepare theory.sig replacements = some entries := rfl
theorem formed : ∀ pair ∈ replacements, WellFormed theory.sig pair.2 = true := by decide +kernel
theorem traversed : go theory.sig entries 0 source = some crossing := by decide +kernel
theorem source_substitutes : statement theory.sig replacements source = some crossing := by decide +kernel

theorem source_derived : DerivesV2 theory source :=
  static_derives_v2 (.definition (d := ⟨D, [F, G], .eq f g⟩) List.mem_cons_self)

theorem crossing_derived : DerivesV2 theory crossing :=
  .instantiateMany source_derived formed source_substitutes

theorem crossing_presented :
    FODerivable (rulesV2 ++ theoryRules theory allocated) (jThm (encTerm theory.sig crossing)) :=
  complete_derivesV2
    (fun _ member => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))))
    (fun _ member => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
    (fun _ member => List.mem_append.mpr (Or.inr member)) hosted crossing_derived

theorem entries_formed : EntriesShape theory.sig entries :=
  prepare_shape theory.sig replacements entries
    (fun pair member => wellFormed_termShape theory.sig pair.2 (formed pair member)) prepared

theorem crossing_traversal_presented :
    FODerivable rulesV2 (jMany (encEntries theory.sig entries) (encNat 0)
      (encTerm theory.sig source) (encTerm theory.sig crossing)) :=
  complete_many (List.subset_append_left _ _) (List.subset_append_right _ _) theory.sig entries 0
    source crossing entries_formed (wellFormed_termShape theory.sig source (by decide +kernel)) traversed

theorem crossing_meaning : MeaningV2 theory (jThm (encTerm theory.sig crossing)) :=
  meaning_of_foDerivableV2 hosted crossing_presented

theorem crossing_has_article : ∃ article,
    checkRaw (validatedV2 theory allocated) (jThm (encTerm theory.sig crossing)) article = true :=
  (derivesV2_iff_checkRaw hosted crossing).mp crossing_derived

theorem module_recovered :
    Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable.readValidatedCalculus?
        (CheckingMachineV2.kernelModule theory allocated) = some (validatedV2 theory allocated) :=
  CheckingMachineV2.kernelModule_read theory allocated

theorem crossing_has_graph :
    ∃ (nodes : List (Mettapedia.Logic.DerivationGraph.Node Pattern
        (CertificateGSLT.BorrowedCursor.AdmittedInstance (validatedV2 theory allocated)) Nat))
      (cache : Array Pattern) (root : Nat),
      Mettapedia.Logic.DerivationGraph.replay
        (CertificateGSLT.BorrowedCursor.presentation (validatedV2 theory allocated)).ruleWitness nodes = some cache ∧
        cache[root]? = some (jThm (encTerm theory.sig crossing)) :=
  (CheckingMachineV2.derives_iff_graph hosted crossing).mp crossing_derived

theorem crossing_has_closed_arrow :
    Nonempty ((⟨[]⟩ : CertificateGSLT.ClassifyingContext (validatedV2 theory allocated)) ⟶
      ⟨[jThm (encTerm theory.sig crossing)]⟩) :=
  (CheckingMachineV2.derives_iff_classifyingArrow hosted crossing).mp crossing_derived

private theorem operation_meaning {goal : Pattern} {article : RawProof}
    (accepted : checkRaw (validatedV2 theory allocated) goal article = true) : MeaningV2 theory goal :=
  meaning_of_foDerivableV2 hosted
    ((checkRaw_exists_iff_foDerivable (validatedV2_presents theory allocated) goal).mp ⟨article, accepted⟩)

/-- Every article claiming that traversal revisits an inserted replacement is
refused, independently of the producer or chosen proof shape. -/
theorem sequential_traversal_refused (article : RawProof) :
    checkRaw (validatedV2 theory allocated)
      (jMany (encEntries theory.sig entries) (encNat 0) (encTerm theory.sig source)
        (encTerm theory.sig sequential)) article = false := by
  cases checked : checkRaw (validatedV2 theory allocated)
      (jMany (encEntries theory.sig entries) (encNat 0) (encTerm theory.sig source)
        (encTerm theory.sig sequential)) article with
  | false => rfl
  | true =>
      have meaning : ManyM theory.sig (encEntries theory.sig entries) (encNat 0)
          (encTerm theory.sig source) (encTerm theory.sig sequential) := operation_meaning checked
      have valid := prepare_shape theory.sig replacements entries
        (fun pair member => wellFormed_termShape theory.sig pair.2 (formed pair member)) prepared
      obtain ⟨output, computed, encoded⟩ := meaning entries 0 source valid rfl rfl rfl
      have same := Option.some.inj (traversed.symm.trans computed)
      have reads := encTerm_inj theory.sig encoded
      have different : sequential ≠ crossing := by decide +kernel
      exact False.elim (different (reads.trans same.symm))

theorem duplicate_lookup_first :
    lookup [⟨F, 0, g⟩, ⟨F, 0, .natLit 7⟩] F = some ⟨F, 0, g⟩ := rfl

theorem shadowed_open_value_refused :
    prepare theory.sig [(F, g), (F, .bvar 0)] = none := by decide +kernel

theorem constant_target_refused : prepare theory.sig [(D, g)] = none := by decide +kernel

theorem original_module_distinct :
    kernelDefinition.name ≠ fixedDefinitionV2.name := by decide +kernel

private theorem state_article (state : State)
    (invariant : Spec.ProtocolV2Invariant.Invariant state []) (claim : Spec.Term)
    (derived : DerivesV2 state.theory claim) :
    ∃ article, checkRaw (validatedV2 state.theory state.nextFresh)
      (jThm (encTerm state.theory.sig claim)) article = true :=
  (derivesV2_iff_checkRaw invariant.theory claim).mp derived

open Native.ProtocolV2LogicalControls in
theorem actual_byte_run_has_presented_article :
    ∃ article, checkRaw (validatedV2 finalState.theory finalState.nextFresh)
      (jThm (encTerm finalState.theory.sig Spec.ProtocolV2.Controls.crossingResult)) article = true :=
  state_article finalState final_invariant Spec.ProtocolV2.Controls.crossingResult registered_goal_derived

#print axioms crossing_has_article
#print axioms sequential_traversal_refused

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation.Controls
