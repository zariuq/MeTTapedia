import Mettapedia.Languages.VibeITP.Presentation.SimultaneousRules
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousFormation
import Mettapedia.Languages.VibeITP.Presentation.KernelSoundness
import Mettapedia.Languages.VibeITP.Spec.DerivationV2

/-!
# Independent meanings of the additive simultaneous judgments

Preparation establishes actual decoded replacements and validates every value.
Traversal meanings retain an explicit formed-entry reading, just as the old
instantiation meaning retains its declared free-variable reading. These input
conditions are supplied by preparation at the theorem boundary. They cannot be
replaced by an arbitrary encoded list or by a cached output annotation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Spec Spec.SimultaneousInstantiation SimultaneousFormation

def encReplacement (sig : Sig) (replacement : SymId × Spec.Term) : Pattern :=
  pairPattern (encSym sig replacement.1) (encTerm sig replacement.2)

def encReplacements (sig : Sig) (replacements : List (SymId × Spec.Term)) : Pattern :=
  encList (replacements.map (encReplacement sig))

def encEntry (sig : Sig) (entry : Entry) : Pattern :=
  entryPattern (encSym sig entry.symbol) (encNat entry.arity) (encTerm sig entry.value)

def encEntries (sig : Sig) (entries : List Entry) : Pattern :=
  encList (entries.map (encEntry sig))

@[simp] theorem encReplacements_nil (sig : Sig) : encReplacements sig [] = cNil := rfl
@[simp] theorem encReplacements_cons (sig : Sig) (first : SymId × Spec.Term) (rest : List (SymId × Spec.Term)) :
    encReplacements sig (first :: rest) = cCons (encReplacement sig first) (encReplacements sig rest) := rfl
@[simp] theorem encEntries_nil (sig : Sig) : encEntries sig [] = cNil := rfl
@[simp] theorem encEntries_cons (sig : Sig) (first : Entry) (rest : List Entry) :
    encEntries sig (first :: rest) = cCons (encEntry sig first) (encEntries sig rest) := rfl

theorem encEntry_injective (sig : Sig) : Function.Injective (encEntry sig) := by
  intro first second same
  have parts : encSym sig first.symbol = encSym sig second.symbol ∧
      encNat first.arity = encNat second.arity ∧ encTerm sig first.value = encTerm sig second.value := by
    simpa [encEntry, entryPattern, cCons, cNil] using same
  have symbol := encSym_inj sig parts.1
  have arity := encNat_inj parts.2.1
  have value := encTerm_inj sig parts.2.2
  cases first
  cases second
  cases symbol
  cases arity
  cases value
  rfl

theorem encEntries_injective (sig : Sig) : Function.Injective (encEntries sig) := by
  intro first second same
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons entry rest => simp [cNil, cCons] at same
  | cons entry rest ih =>
      cases second with
      | nil => simp [cNil, cCons] at same
      | cons entry' rest' =>
          have parts : encEntry sig entry = encEntry sig entry' ∧ encEntries sig rest = encEntries sig rest' := by
            simpa [cCons] using same
          exact congrArg₂ List.cons (encEntry_injective sig parts.1) (ih parts.2)

theorem encEntries_eq_cons (sig : Sig) (entries : List Entry) (head tail : Pattern)
    (same : encEntries sig entries = cCons head tail) :
    ∃ first rest, entries = first :: rest ∧ head = encEntry sig first ∧ tail = encEntries sig rest := by
  cases entries with
  | nil => simp [cNil, cCons] at same
  | cons first rest =>
      have parts : encEntry sig first = head ∧ encEntries sig rest = tail := by
        simpa [cCons] using same
      exact ⟨first, rest, rfl, parts.1.symm, parts.2.symm⟩

theorem isData_encEntry (sig : Sig) (entry : Entry) : IsData (encEntry sig entry) :=
  IsData.app2 _ (isData_encSym sig entry.symbol)
    (IsData.app2 _ (isData_encNat entry.arity)
      (IsData.app2 _ (isData_encTerm sig entry.value) (IsData.app0 _)))

theorem isData_encEntries (sig : Sig) (entries : List Entry) : IsData (encEntries sig entries) := by
  apply isData_encList
  intro item member
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  exact isData_encEntry sig entry

theorem isData_encReplacements (sig : Sig) (replacements : List (SymId × Spec.Term)) :
    IsData (encReplacements sig replacements) := by
  apply isData_encList
  intro item member
  obtain ⟨replacement, _, rfl⟩ := List.mem_map.mp member
  exact IsData.app2 _ (isData_encSym sig replacement.1)
    (IsData.app2 _ (isData_encTerm sig replacement.2) (IsData.app0 _))

def PrepareM (sig : Sig) (replacements entries : Pattern) : Prop :=
  ∃ source prepared,
    replacements = encReplacements sig source ∧ entries = encEntries sig prepared ∧
    (∀ pair ∈ source, WellFormed sig pair.2 = true) ∧ prepare sig source = some prepared

def HitM (sig : Sig) (entries symbol arity value : Pattern) : Prop :=
  ∀ prepared target, EntriesShape sig prepared → entries = encEntries sig prepared → symbol = encSym sig target →
    ∃ entry, lookup prepared target = some entry ∧ arity = encNat entry.arity ∧ value = encTerm sig entry.value

def MissM (sig : Sig) (entries symbol : Pattern) : Prop :=
  ∀ prepared target, EntriesShape sig prepared → entries = encEntries sig prepared → symbol = encSym sig target →
    lookup prepared target = none

def ManyM (sig : Sig) (entries offset source result : Pattern) : Prop :=
  ∀ prepared position term, EntriesShape sig prepared → entries = encEntries sig prepared →
    offset = encNat position → source = encTerm sig term →
      ∃ output, go sig prepared position term = some output ∧ result = encTerm sig output

def ManyArgsM (sig : Sig) (entries offset binders source result : Pattern) : Prop :=
  ∀ prepared position bs terms, EntriesShape sig prepared → entries = encEntries sig prepared →
    offset = encNat position → binders = encNatList bs → source = encTermList sig terms →
      ∃ output, argumentList sig prepared position bs terms = some output ∧
        result = encTermList sig output ∧ terms.length = bs.length

def ThmMV2 (T : Theory) (encoded : Pattern) : Prop :=
  ∃ statement, encoded = encTerm T.sig statement ∧ DerivesV2 T statement

def MeaningV2 (T : Theory) : Pattern → Prop
  | .apply "VManyPrepare" [replacements, entries] => PrepareM T.sig replacements entries
  | .apply "VManyHit" [entries, symbol, arity, value] => HitM T.sig entries symbol arity value
  | .apply "VManyMiss" [entries, symbol] => MissM T.sig entries symbol
  | .apply "VMany" [entries, offset, source, result] => ManyM T.sig entries offset source result
  | .apply "VManyArgs" [entries, offset, binders, source, result] => ManyArgsM T.sig entries offset binders source result
  | .apply "VThm" [statement] => ThmMV2 T statement
  | other => Meaning T other

def reservedHeads : List String := ["VManyPrepare", "VManyHit", "VManyMiss", "VMany", "VManyArgs", "VThm"]

/-- A fixed outer judgment head unaffected by the v2 meaning override. -/
def oldJudgment : Pattern → Bool
  | .apply head _ => !reservedHeads.contains head
  | _ => false

def oldRule (rule : FORule) : Bool :=
  rule.premises.all oldJudgment && oldJudgment rule.conclusion

theorem oldJudgment_instantiates (bindings : Bindings) (pattern : Pattern)
    (old : oldJudgment pattern = true) : oldJudgment (applyBindings bindings pattern) = true := by
  cases pattern <;> try simp [oldJudgment] at old
  simpa [oldJudgment, applyBindings] using old

theorem meaning_of_old (T : Theory) (pattern : Pattern) (old : oldJudgment pattern = true) :
    MeaningV2 T pattern = Meaning T pattern := by
  cases pattern <;> try simp [oldJudgment] at old
  rename_i head arguments
  simp [reservedHeads] at old
  unfold MeaningV2
  split <;> simp_all

def RuleMeaningSoundV2 (T : Theory) (rule : FORule) : Prop :=
  ∀ arguments : List Pattern, arguments.length = rule.vars.length →
    (∀ premise ∈ rule.instPremises arguments, MeaningV2 T premise) → MeaningV2 T (rule.instConclusion arguments)

/-- Every legacy operational rule transfers through its fixed outer heads.
Its internal data and computational soundness proof are reused unchanged. -/
theorem transfer_old_rule (T : Theory) (rule : FORule) (old : oldRule rule = true)
    (sound : RuleMeaningSound T rule) : RuleMeaningSoundV2 T rule := by
  obtain ⟨premises, conclusion⟩ := Bool.and_eq_true_iff.mp old
  intro arguments length interpreted
  change MeaningV2 T (applyBindings (rule.bindings arguments) rule.conclusion)
  rw [meaning_of_old T _ (oldJudgment_instantiates _ _ conclusion)]
  apply sound arguments length
  intro premise member
  obtain ⟨schema, inRule, rfl⟩ := List.mem_map.mp member
  have equal := meaning_of_old T (applyBindings (rule.bindings arguments) schema)
    (oldJudgment_instantiates (rule.bindings arguments) schema (List.all_eq_true.mp premises schema inRule))
  rw [← equal]
  exact interpreted _ (List.mem_map.mpr ⟨schema, inRule, rfl⟩)

def newHeads : List String := ["VManyPrepare", "VManyHit", "VManyMiss", "VMany", "VManyArgs"]

def legacyJudgment : Pattern → Bool
  | .apply head _ => !newHeads.contains head
  | _ => false

def legacyLeafRule (rule : FORule) : Bool :=
  rule.premises.all oldJudgment && legacyJudgment rule.conclusion

theorem legacyJudgment_instantiates (bindings : Bindings) (pattern : Pattern)
    (legacy : legacyJudgment pattern = true) : legacyJudgment (applyBindings bindings pattern) = true := by
  cases pattern <;> try simp [legacyJudgment] at legacy
  simpa [legacyJudgment, applyBindings] using legacy

/-- Old theorem conclusions embed into v2; all other legacy conclusions retain
their meaning. No assertion about the new judgment heads follows from this. -/
theorem legacy_meaning_embeds (T : Theory) (pattern : Pattern)
    (legacy : legacyJudgment pattern = true) (meaning : Meaning T pattern) : MeaningV2 T pattern := by
  cases pattern <;> try simp [legacyJudgment] at legacy
  rename_i head arguments
  by_cases theoremHead : head = "VThm"
  · subst head
    cases arguments with
    | nil => exact meaning
    | cons statement rest =>
        cases rest with
        | nil =>
            obtain ⟨source, encoded, derived⟩ := meaning
            exact ⟨source, encoded, static_derives_v2 derived⟩
        | cons _ _ => exact meaning
  · have ordinary : oldJudgment (.apply head arguments) = true := by
      simpa [oldJudgment, reservedHeads, newHeads, theoremHead] using legacy
    rw [meaning_of_old T _ ordinary]
    exact meaning

theorem transfer_legacy_leaf (T : Theory) (rule : FORule) (legacy : legacyLeafRule rule = true)
    (sound : RuleMeaningSound T rule) : RuleMeaningSoundV2 T rule := by
  obtain ⟨premises, conclusion⟩ := Bool.and_eq_true_iff.mp legacy
  intro arguments length interpreted
  apply legacy_meaning_embeds T _ (legacyJudgment_instantiates (rule.bindings arguments) _ conclusion)
  apply sound arguments length
  intro premise member
  obtain ⟨schema, inRule, rfl⟩ := List.mem_map.mp member
  have equal := meaning_of_old T (applyBindings (rule.bindings arguments) schema)
    (oldJudgment_instantiates (rule.bindings arguments) schema (List.all_eq_true.mp premises schema inRule))
  rw [← equal]
  exact interpreted _ (List.mem_map.mpr ⟨schema, inRule, rfl⟩)

section Unfold
variable (T : Theory)
@[simp] theorem Mv2_prepare (replacements entries : Pattern) :
    MeaningV2 T (jManyPrepare replacements entries) = PrepareM T.sig replacements entries := rfl
@[simp] theorem Mv2_hit (entries symbol arity value : Pattern) :
    MeaningV2 T (jManyHit entries symbol arity value) = HitM T.sig entries symbol arity value := rfl
@[simp] theorem Mv2_miss (entries symbol : Pattern) :
    MeaningV2 T (jManyMiss entries symbol) = MissM T.sig entries symbol := rfl
@[simp] theorem Mv2_many (entries offset source result : Pattern) :
    MeaningV2 T (jMany entries offset source result) = ManyM T.sig entries offset source result := rfl
@[simp] theorem Mv2_args (entries offset binders source result : Pattern) :
    MeaningV2 T (jManyArgs entries offset binders source result) = ManyArgsM T.sig entries offset binders source result := rfl
@[simp] theorem Mv2_thm (statement : Pattern) : MeaningV2 T (jThm statement) = ThmMV2 T statement := rfl
end Unfold

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
