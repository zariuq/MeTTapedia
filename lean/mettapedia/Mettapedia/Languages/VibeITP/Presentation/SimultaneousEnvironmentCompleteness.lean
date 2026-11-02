import Mettapedia.Languages.VibeITP.Presentation.SimultaneousEnvironmentSoundness
import Mettapedia.Languages.VibeITP.Presentation.CompleteCorrespondence

/-! Every actually prepared replacement environment and first-match lookup
has a derivation in any rule set containing the original kernel and the
simultaneous schemas. Declaration and value-formation proofs are reused. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Spec Spec.SimultaneousInstantiation SimultaneousFormation

theorem complete_prepare {R : List FORule} (old : kernelRules ⊆ R) (added : simultaneousRules ⊆ R)
    {T : Theory} {allocated : Nat} (facts : theoryRules T allocated ⊆ R) (hosted : Hosted T allocated) :
    ∀ (replacements : List (SymId × Spec.Term)) (entries : List Entry),
      (∀ pair ∈ replacements, WellFormed T.sig pair.2 = true) →
      prepare T.sig replacements = some entries →
        FODerivable R (jManyPrepare (encReplacements T.sig replacements) (encEntries T.sig entries))
  | [], entries, _, accepted => by
      have same : [] = entries := Option.some.inj accepted
      subst entries
      exact intro_rManyPrepareNil (added (by simp [simultaneousRules]))
  | (symbol, value) :: rest, entries, formed, accepted => by
      cases declared : T.sig symbol with
      | none => simp [prepare, declared] at accepted
      | some info =>
          simp only [prepare, declared] at accepted
          split at accepted
          · rename_i guard
            cases remaining : prepare T.sig rest with
            | none => simp [remaining] at accepted
            | some tail =>
                have same : ⟨symbol, info.arity, value⟩ :: tail = entries := by
                  simpa only [remaining, Option.map_some, Option.some.injEq] using accepted
                subst entries
                have symbolCode : encSym T.sig symbol =
                    cSym (encNat (symNumber symbol)) cKFvar (encNatList info.binders) := by
                  rw [encSym_eq]
                  simp [kindOf, bindersOf, declared, guard.1, encKind]
                have known : (T.sig symbol).isSome = true := by simp [declared]
                have sourceFormed := formed (symbol, value) (List.mem_cons_self)
                have restFormed : ∀ pair ∈ rest, WellFormed T.sig pair.2 = true :=
                  fun pair member => formed pair (List.mem_cons_of_mem _ member)
                rw [encReplacements_cons, encEntries_cons]
                simp only [encReplacement, encEntry, symbolCode]
                exact intro_rManyPrepareCons (added (by simp [simultaneousRules]))
                  (isData_encNat _) (isData_encNatList _) (isData_encTerm _ _) (isData_encNat _)
                  (isData_encNat _) (isData_encReplacements _ _) (isData_encEntries _ _)
                  (by simpa only [symbolCode] using complete_symDecl old facts hosted symbol known)
                  (complete_len_natList old info.binders)
                  (complete_wf old facts hosted value sourceFormed)
                  (complete_depth old T.sig value) (complete_nle old _ _ guard.2)
                  (complete_prepare old added facts hosted rest tail restFormed remaining)
          · cases accepted

theorem complete_hit {R : List FORule} (old : kernelRules ⊆ R) (added : simultaneousRules ⊆ R)
    (sig : Sig) (entries : List Entry) (target : SymId) (entry : Entry)
    (valid : EntriesShape sig entries) (targetKind : kindOf sig target = .fvar)
    (found : lookup entries target = some entry) :
    FODerivable R (jManyHit (encEntries sig entries) (encSym sig target)
      (encNat entry.arity) (encTerm sig entry.value)) := by
  induction entries with
  | nil => simp [lookup] at found
  | cons first rest ih =>
      have firstValid := valid first (List.mem_cons_self)
      have restValid : EntriesShape sig rest := fun value member => valid value (List.mem_cons_of_mem _ member)
      by_cases hit : target = first.symbol
      · have same : first = entry := by simpa only [lookup, hit, if_true, Option.some.injEq] using found
        subst entry target
        simp only [encEntries_cons, encEntry, encSym_eq, firstValid.1.2.1]
        exact intro_rManyHitFirst (added (by simp [simultaneousRules]))
          (isData_encNat _) (isData_encNatList _) (isData_encNat _) (isData_encTerm _ _) (isData_encEntries _ _)
      · have next : lookup rest target = some entry := by simpa only [lookup, hit, if_false] using found
        have tail := ih restValid next
        have different : symNumber first.symbol ≠ symNumber target := by
          intro same
          exact hit (symNumber_inj same).symm
        have encodedTail : FODerivable R (jManyHit (encEntries sig rest)
            (cSym (encNat (symNumber target)) cKFvar (encNatList (bindersOf sig target)))
            (encNat entry.arity) (encTerm sig entry.value)) := by
          simpa only [encSym_eq, targetKind, encKind] using tail
        simp only [encEntries_cons, encEntry, encSym_eq, firstValid.1.2.1, targetKind]
        by_cases less : symNumber first.symbol < symNumber target
        · exact intro_rManyHitLt (added (by simp [simultaneousRules]))
            (isData_encNat _) (isData_encNatList _) (isData_encNat _) (isData_encTerm _ _) (isData_encEntries _ _)
            (isData_encNat _) (isData_encNatList _) (isData_encNat _) (isData_encTerm _ _)
            (complete_nlt old _ _ less) encodedTail
        · exact intro_rManyHitGt (added (by simp [simultaneousRules]))
            (isData_encNat _) (isData_encNatList _) (isData_encNat _) (isData_encTerm _ _) (isData_encEntries _ _)
            (isData_encNat _) (isData_encNatList _) (isData_encNat _) (isData_encTerm _ _)
            (complete_nlt old _ _ (by omega)) encodedTail

theorem complete_miss {R : List FORule} (old : kernelRules ⊆ R) (added : simultaneousRules ⊆ R)
    (sig : Sig) (entries : List Entry) (target : SymId)
    (valid : EntriesShape sig entries) (targetKind : kindOf sig target = .fvar)
    (absent : lookup entries target = none) :
    FODerivable R (jManyMiss (encEntries sig entries) (encSym sig target)) := by
  induction entries with
  | nil =>
      simp only [encEntries_nil, encSym_eq, targetKind]
      exact intro_rManyMissNil (added (by simp [simultaneousRules])) (isData_encNat _) (isData_encNatList _)
  | cons first rest ih =>
      have firstValid := valid first (List.mem_cons_self)
      have restValid : EntriesShape sig rest := fun value member => valid value (List.mem_cons_of_mem _ member)
      have different : target ≠ first.symbol := by
        intro same
        simp [lookup, same] at absent
      have next : lookup rest target = none := by simpa only [lookup, different, if_false] using absent
      have tail := ih restValid next
      have numbers : symNumber first.symbol ≠ symNumber target := by
        intro same
        exact different (symNumber_inj same).symm
      have encodedTail : FODerivable R (jManyMiss (encEntries sig rest)
          (cSym (encNat (symNumber target)) cKFvar (encNatList (bindersOf sig target)))) := by
        simpa only [encSym_eq, targetKind, encKind] using tail
      simp only [encEntries_cons, encEntry, encSym_eq, firstValid.1.2.1, targetKind]
      by_cases less : symNumber first.symbol < symNumber target
      · exact intro_rManyMissLt (added (by simp [simultaneousRules]))
          (isData_encNat _) (isData_encNatList _) (isData_encNat _) (isData_encTerm _ _) (isData_encEntries _ _)
          (isData_encNat _) (isData_encNatList _) (complete_nlt old _ _ less) encodedTail
      · exact intro_rManyMissGt (added (by simp [simultaneousRules]))
          (isData_encNat _) (isData_encNatList _) (isData_encNat _) (isData_encTerm _ _) (isData_encEntries _ _)
          (isData_encNat _) (isData_encNatList _) (complete_nlt old _ _ (by omega)) encodedTail

#print axioms complete_prepare
#print axioms complete_hit

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
