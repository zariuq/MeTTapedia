import Mettapedia.Languages.VibeITP.Presentation.SimultaneousTraversalSoundness
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousLegacySoundness

/-! The additive v2 rules derive only statements of the independent v2
calculus. Preparation discharges every environment-reading premise before
the traversal result becomes a theorem. Theory axioms remain explicit. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Spec Spec.SimultaneousInstantiation SimultaneousFormation

theorem ms_rInstantiateManyNil (T : Theory) (phi : Pattern)
    (derived : MeaningV2 T (jThm phi)) (closed : MeaningV2 T (jDepth phi cN0)) :
    MeaningV2 T (jThm phi) := by
  obtain ⟨source, rfl, sourceDerived⟩ := derived
  have sourceClosed := encNat_eq_N0 (closed source rfl)
  refine ⟨source, rfl, .instantiateMany (replacements := []) sourceDerived ?_ ?_⟩
  · intro pair member; cases member
  · simp only [statement_nil, sourceClosed, if_true]

theorem ms_rInstantiateManyCons (T : Theory) (rep reps entry entries phi psi : Pattern)
    (derived : MeaningV2 T (jThm phi))
    (prepared : MeaningV2 T (jManyPrepare (cCons rep reps) (cCons entry entries)))
    (computed : MeaningV2 T (jMany (cCons entry entries) cN0 phi psi))
    (closed : MeaningV2 T (jDepth psi cN0)) : MeaningV2 T (jThm psi) := by
  obtain ⟨source, rfl, sourceDerived⟩ := derived
  obtain ⟨replacements, environment, _, environmentCode, formed, validated⟩ := prepared
  have environmentShape : EntriesShape T.sig environment :=
    prepare_shape T.sig replacements environment
      (fun pair member => wellFormed_termShape T.sig pair.2 (formed pair member)) validated
  obtain ⟨result, reduced, rfl⟩ := computed environment 0 source environmentShape environmentCode rfl rfl
  have resultClosed := encNat_eq_N0 (closed result rfl)
  have nonempty : environment.isEmpty = false := by
    cases environment with
    | nil => simp [cCons, cNil] at environmentCode
    | cons _ _ => rfl
  refine ⟨result, rfl, .instantiateMany sourceDerived formed ?_⟩
  simp only [statement, validated, nonempty, Bool.false_eq_true, if_false, reduced, resultClosed, if_true]

theorem simultaneousRules_meaningSound (T : Theory) {rule : FORule}
    (member : rule ∈ simultaneousRules) : RuleMeaningSoundV2 T rule := by
  simp only [simultaneousRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rManyPrepareNil (ms_rManyPrepareNil T)
  · exact sound_rManyPrepareCons (ms_rManyPrepareCons T)
  · exact sound_rManyHitFirst (ms_rManyHitFirst T)
  · exact sound_rManyHitLt (ms_rManyHitLt T)
  · exact sound_rManyHitGt (ms_rManyHitGt T)
  · exact sound_rManyMissNil (ms_rManyMissNil T)
  · exact sound_rManyMissLt (ms_rManyMissLt T)
  · exact sound_rManyMissGt (ms_rManyMissGt T)
  · exact sound_rManyNofv (ms_rManyNofv T)
  · exact sound_rManyConst (ms_rManyConst T)
  · exact sound_rManyAbsent (ms_rManyAbsent T)
  · exact sound_rManySelected (ms_rManySelected T)
  · exact sound_rManyArgsNil (ms_rManyArgsNil T)
  · exact sound_rManyArgsCons (ms_rManyArgsCons T)
  · exact sound_rInstantiateManyNil (ms_rInstantiateManyNil T)
  · exact sound_rInstantiateManyCons (ms_rInstantiateManyCons T)

theorem hostedRules_meaningSoundV2 (T : Theory) (allocated : Nat) (hosted : Hosted T allocated)
    {rule : FORule} (member : rule ∈ rulesV2 ++ theoryRules T allocated) : RuleMeaningSoundV2 T rule := by
  simp only [rulesV2, List.mem_append] at member
  rcases member with (old | added) | admitted
  · exact legacy_kernel_sound T hosted old
  · exact simultaneousRules_meaningSound T added
  · exact legacy_theory_sound T allocated hosted admitted

theorem meaning_of_foDerivableV2 {T : Theory} {allocated : Nat} (hosted : Hosted T allocated)
    {goal : Pattern} (derivation : FODerivable (rulesV2 ++ theoryRules T allocated) goal) :
    MeaningV2 T goal := by
  induction derivation with
  | rule rule member arguments length _ _ ih =>
      exact hostedRules_meaningSoundV2 T allocated hosted member arguments length ih

theorem derives_of_foDerivableV2 {T : Theory} {allocated : Nat} (hosted : Hosted T allocated)
    {statement : Spec.Term}
    (derivation : FODerivable (rulesV2 ++ theoryRules T allocated) (jThm (encTerm T.sig statement))) :
    DerivesV2 T statement := by
  obtain ⟨actual, encoded, derived⟩ := meaning_of_foDerivableV2 hosted derivation
  have same : statement = actual := encTerm_inj T.sig encoded
  exact same.symm ▸ derived

theorem checkRaw_sound_presentedV2 {T : Theory} {allocated : Nat} (hosted : Hosted T allocated)
    {definition : Mettapedia.GSLT.LanguageDef.ValidatedCalculusLanguageDef}
    (presents : Presents definition (rulesV2 ++ theoryRules T allocated))
    {statement : Spec.Term} {article : RawProof}
    (accepted : checkRaw definition (jThm (encTerm T.sig statement)) article = true) :
    DerivesV2 T statement :=
  derives_of_foDerivableV2 hosted ((checkRaw_exists_iff_foDerivable presents _).mp ⟨article, accepted⟩)

#print axioms simultaneousRules_meaningSound
#print axioms derives_of_foDerivableV2

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
