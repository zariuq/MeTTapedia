import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCalculus
import Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection
import Std.Data.String.ToNat

/-!
# Generic validity of replay presentations, and the bootstrap tower

The reflexive cell (`BootstrapCell.ReplayCalculus`) relates a validated
calculus to any validated presentation of its replay rules.  This module
constructs that presentation for every validated calculus satisfying
explicit freshness conditions, and proves it valid.  Because the conditions
are inherited by the presentation, the construction iterates: the bootstrap
tower exists at every level.

**The presentation** (`replayPresentation cache profile definition`): a
companion cache over one data sort whose constructor table (`replayTable`)
extends the calculus's own data constructors by its judgment heads (which
occur nested inside acceptance judgments), the certificate constructor of
arity three, and one nullary atom per rule identifier, skipping names already
present.  Its only judgment is `Accepts/2`; its rules are the replay rules.

**Freshness** (`Fresh profile definition`), all decidable on concrete data:
* no formal of a rule is named like a child formal numbered at or beyond the
  rule's own formal count (`ChildNamesFresh`);
* the arities assigned to the calculus's constructors, judgment heads, the
  certificate constructor and the rule atoms are consistent;
* the acceptance head is nonempty, unused, and not a reserved metasyntax head.

Validity of the calculus does not imply these conditions: child formals of a
rule with `m` formals are named `#m`, `#(m+1)`, ..., so a formal named `#k`
with `k ≥ m` collides with one of them; and a rule identifier spelled like a
constructor of nonzero arity clashes with the rule's nullary atom.

**Theorems.**
* `replayPresentation_valid`: the presentation of a validated, fresh calculus
  is valid, so `replayCell` is a validated calculus whose rules are the
  replay rules, and the correspondence of the reflexive cell applies to it
  (`replayCell_checkRaw`).
* `fresh_replayPresentation`: the presentation is fresh for the next level's
  profile whenever the next profile keeps the certificate constructor and its
  acceptance head avoids every name used so far.
* `TowerProfiles.level`: for a family of acceptance heads that avoids the
  calculus's names and each other, every level of the tower is a validated
  calculus, and level `n + 1` is the replay presentation of level `n`.
  `TowerProfiles.tower_checkRaw` relates consecutive levels, and
  `TowerProfiles.tower_agrees` relates every level to the base calculus.

**Controls.**  A modus ponens calculus satisfies the conditions, and its
tower accepts the encoded derivation of `P(B)` and rejects the encoded wrong
goal `P(A)` at every level (`mpTower_accepts`, `mpTower_rejects_wrong_goal`).
Two valid variants violate them and have invalid presentations: a formal
named `#2` (`collidingCalculus_presentation_invalid`) and a rule identified
as `I`, the binary constructor (`atomClashCalculus_presentation_invalid`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection
open Mettapedia.GSLT.LanguageDef.BootstrapCell

/-! ## Child formal names -/

theorem childName_injective : Function.Injective childName := by
  intro first second equal
  exact Nat.repr_injective ((String.append_right_inj "#").mp equal)

theorem childName_ne_empty (index : Nat) : childName index ≠ "" := by
  intro equal
  have sizes := congrArg String.utf8ByteSize equal
  have hashSize : "#".utf8ByteSize = 1 := by decide
  have emptySize : "".utf8ByteSize = 0 := by decide
  rw [childName, String.utf8ByteSize_append, hashSize, emptySize, Nat.add_comm] at sizes
  exact Nat.succ_ne_zero _ sizes

theorem mem_childFormalsFrom {formal : String × Nat} :
    (next : Nat) → (premises : List Pattern) →
      formal ∈ childFormalsFrom next premises →
        ∃ offset, offset < premises.length ∧ formal = (childName (next + offset), 0)
  | _, [], member => by
      rw [childFormalsFrom] at member
      cases member
  | next, _ :: premises, member => by
      rw [childFormalsFrom, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨0, Nat.succ_pos _, rfl⟩
      · obtain ⟨offset, bound, rfl⟩ := mem_childFormalsFrom (next + 1) premises member
        exact ⟨offset + 1, Nat.succ_lt_succ bound, by rw [Nat.add_right_comm, Nat.add_assoc]⟩

theorem childFormalsFrom_names_nodup :
    (next : Nat) → (premises : List Pattern) →
      ((childFormalsFrom next premises).map Prod.fst).Nodup
  | _, [] => by simp [childFormalsFrom]
  | next, _ :: premises => by
      rw [childFormalsFrom, List.map_cons, List.nodup_cons]
      refine ⟨?_, childFormalsFrom_names_nodup (next + 1) premises⟩
      intro member
      obtain ⟨formal, formalMember, nameEq⟩ := List.mem_map.mp member
      obtain ⟨offset, _, rfl⟩ := mem_childFormalsFrom (next + 1) premises formalMember
      have := childName_injective nameEq
      omega

/-- No formal of a rule is named like a child formal numbered at or beyond the
rule's own formal count. -/
def ChildNamesFresh (rule : RuleSchema) : Prop :=
  ∀ formal ∈ rule.metavariables, ∀ index, formal.1 = childName index →
    index < rule.metavariables.length

/-- The formal names of a replay rule are distinct. -/
theorem replayNames_nodup {rule : RuleSchema}
    (namesNodup : (rule.metavariables.map Prod.fst).Nodup) (fresh : ChildNamesFresh rule) :
    ((rule.metavariables ++ childFormalsFrom rule.metavariables.length rule.premises).map
      Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨namesNodup, childFormalsFrom_names_nodup _ _, ?_⟩
  intro name member childNameValue childMember equal
  obtain ⟨formal, formalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨child, childFormalMember, rfl⟩ := List.mem_map.mp childMember
  obtain ⟨offset, _, rfl⟩ := mem_childFormalsFrom _ _ childFormalMember
  have := fresh formal formalMember _ equal
  omega

/-- The replay rule inherits the freshness of child names. -/
theorem childNamesFresh_replayRule (profile : CellProfile) {rule : RuleSchema}
    (fresh : ChildNamesFresh rule) : ChildNamesFresh (replayRule profile rule) := by
  intro formal member index nameEq
  change formal ∈ rule.metavariables ++ childFormalsFrom rule.metavariables.length
    rule.premises at member
  change index < (rule.metavariables ++
    childFormalsFrom rule.metavariables.length rule.premises).length
  rw [List.length_append, childFormalsFrom_length]
  rcases List.mem_append.mp member with member | member
  · have := fresh formal member index nameEq
    omega
  · obtain ⟨offset, bound, rfl⟩ := mem_childFormalsFrom _ _ member
    have := childName_injective nameEq
    omega

/-! ## Arity tables -/

/-- Every name has one arity. -/
def ArityConsistent (entries : ArityTable) : Prop :=
  ∀ entry ∈ entries, ∀ other ∈ entries, entry.1 = other.1 → entry.2 = other.2

theorem ArityConsistent.mono {entries larger : ArityTable}
    (consistent : ArityConsistent larger) (subset : ∀ entry ∈ entries, entry ∈ larger) :
    ArityConsistent entries :=
  fun entry member other otherMember =>
    consistent entry (subset entry member) other (subset other otherMember)

/-- Append the entries whose names are not yet present, in order. -/
def extendTable : ArityTable → ArityTable → ArityTable
  | table, [] => table
  | table, entry :: rest =>
      if entry.1 ∈ table.map Prod.fst then extendTable table rest
      else extendTable (table ++ [entry]) rest

theorem extendTable_names_nodup :
    (table new : ArityTable) → (table.map Prod.fst).Nodup →
      ((extendTable table new).map Prod.fst).Nodup
  | table, [], nodup => nodup
  | table, entry :: rest, nodup => by
      rw [extendTable]
      split
      · exact extendTable_names_nodup table rest nodup
      · rename_i absent
        apply extendTable_names_nodup
        rw [List.map_append, List.nodup_append]
        refine ⟨nodup, List.nodup_singleton _, ?_⟩
        intro name member name' member' equal
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at member'
        subst member' equal
        exact absent member

theorem mem_extendTable_of_mem {entry : String × Nat} :
    (table new : ArityTable) → entry ∈ table → entry ∈ extendTable table new
  | _, [], member => member
  | table, next :: rest, member => by
      rw [extendTable]
      split
      · exact mem_extendTable_of_mem table rest member
      · exact mem_extendTable_of_mem _ rest (List.mem_append_left _ member)

theorem mem_of_mem_extendTable {entry : String × Nat} :
    (table new : ArityTable) → entry ∈ extendTable table new → entry ∈ table ++ new
  | _, [], member => List.mem_append_left _ member
  | table, next :: rest, member => by
      rw [extendTable] at member
      split at member
      · rcases List.mem_append.mp (mem_of_mem_extendTable table rest member) with
          member | member
        · exact List.mem_append_left _ member
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
      · have := mem_of_mem_extendTable _ rest member
        simpa [List.append_assoc] using this

theorem mem_extendTable_of_consistent :
    (table new : ArityTable) → ArityConsistent (table ++ new) →
      ∀ entry ∈ table ++ new, entry ∈ extendTable table new
  | table, [], _, entry, member => by
      rw [List.append_nil] at member
      exact member
  | table, next :: rest, consistent, entry, member => by
      rw [extendTable]
      split
      · rename_i present
        obtain ⟨old, oldMember, oldName⟩ := List.mem_map.mp present
        have sameArity := consistent old (List.mem_append_left _ oldMember) next
          (List.mem_append_right _ List.mem_cons_self) oldName
        have nextInTable : next ∈ table := by
          have : old = next := Prod.ext oldName sameArity
          exact this ▸ oldMember
        have restConsistent : ArityConsistent (table ++ rest) :=
          consistent.mono fun other otherMember => by
            rcases List.mem_append.mp otherMember with otherMember | otherMember
            · exact List.mem_append_left _ otherMember
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ otherMember)
        rcases List.mem_append.mp member with member | member
        · exact mem_extendTable_of_mem table rest member
        · rcases List.mem_cons.mp member with rfl | member
          · exact mem_extendTable_of_mem table rest nextInTable
          · exact mem_extendTable_of_consistent table rest restConsistent entry
              (List.mem_append_right _ member)
      · have reassociated : table ++ next :: rest = (table ++ [next]) ++ rest := by simp
        rw [reassociated] at consistent member
        exact mem_extendTable_of_consistent _ rest consistent entry member

/-! ## The companion cache language -/

theorem cacheLanguage_entries (cache : CacheProfile) (table : ArityTable) :
    (cacheLanguage cache table).terms.map (fun term => (term.label, term.params.length)) =
      table := by
  simp [cacheLanguage, dataConstructor, List.map_map, Function.comp_def]

theorem cacheLanguage_labels (cache : CacheProfile) (table : ArityTable) :
    (cacheLanguage cache table).terms.map (·.label) = table.map Prod.fst := by
  simp [cacheLanguage, dataConstructor, List.map_map, Function.comp_def]

theorem cacheLanguage_validate (cache : CacheProfile) (table : ArityTable)
    (nodup : (table.map Prod.fst).Nodup) : (cacheLanguage cache table).validate = [] := by
  have labels := cacheLanguage_labels cache table
  unfold LanguageDef.validate
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact LanguageDef.duplicateErrors_eq_nil_of_nodup _ _ _ (by simp [cacheLanguage, LanguageDef.typeNames])
  · rw [labels]
    exact LanguageDef.duplicateErrors_eq_nil_of_nodup _ _ _ nodup
  · exact LanguageDef.duplicateErrors_eq_nil_of_nodup _ _ _ (by simp [cacheLanguage])
  · exact LanguageDef.duplicateErrors_eq_nil_of_nodup _ _ _ (by simp [cacheLanguage])
  · rw [List.flatMap_eq_nil_iff]
    intro term member
    simp only [cacheLanguage, List.mem_map] at member
    obtain ⟨⟨label, arity⟩, _, rfl⟩ := member
    simp only [LanguageDef.validateTerm, dataConstructor, cacheLanguage, LanguageDef.typeNames,
      TermParam.typeExpr, TypeDecl.plain, List.map_cons, List.map_nil, List.mem_singleton,
      if_true, List.nil_append, List.append_nil, LanguageDef.validateSyntaxPattern_nil,
      List.flatMap_eq_nil_iff, List.mem_map, List.mem_range]
    rintro _ ⟨index, _, rfl⟩
    exact LanguageDef.validateTypeExpr_eq_nil_of_baseNames _ _ _ (by simp [TypeExpr.baseNames])
  · simp [cacheLanguage]
  · simp [cacheLanguage]

theorem filter_eq_nil_of_forall {α : Type} {keep : α → Bool} :
    (values : List α) → (∀ value ∈ values, keep value = false) → values.filter keep = []
  | [], _ => rfl
  | value :: values, dropped => by
      rw [List.filter_cons, dropped value List.mem_cons_self]
      exact filter_eq_nil_of_forall values fun other member =>
        dropped other (List.mem_cons_of_mem _ member)

theorem filter_label_dataConstructor (cache : CacheProfile) :
    (table : ArityTable) → (table.map Prod.fst).Nodup →
      ∀ {head : String} {arity : Nat}, (head, arity) ∈ table →
        (table.map fun entry => dataConstructor cache entry.1 entry.2).filter
            (fun declaration => declaration.label == head) =
          [dataConstructor cache head arity]
  | [], _, _, _, member => by simp at member
  | (label, labelArity) :: rest, nodup, head, arity, member => by
      rw [List.map_cons, List.nodup_cons] at nodup
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        have restFiltered : (rest.map fun entry => dataConstructor cache entry.1 entry.2).filter
            (fun declaration => declaration.label == label) = [] := by
          apply filter_eq_nil_of_forall
          intro declaration declarationMember
          obtain ⟨⟨other, otherArity⟩, otherMember, rfl⟩ := List.mem_map.mp declarationMember
          exact Bool.eq_false_iff.mpr fun same =>
            nodup.1 (List.mem_map.mpr ⟨_, otherMember, beq_iff_eq.mp same⟩)
        rw [List.map_cons, List.filter_cons, restFiltered]
        exact if_pos (beq_iff_eq.mpr rfl)
      · have headInRest : head ∈ rest.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) member
        have different : label ≠ head := fun same => nodup.1 (same ▸ headInRest)
        rw [List.map_cons, List.filter_cons]
        exact (if_neg (fun same => different (beq_iff_eq.mp same))).trans
          (filter_label_dataConstructor cache rest nodup.2 member)

theorem languageHasConstructorArity_cacheLanguage (cache : CacheProfile) {table : ArityTable}
    (nodup : (table.map Prod.fst).Nodup) {head : String} {arity : Nat}
    (member : (head, arity) ∈ table) :
    languageHasConstructorArity (cacheLanguage cache table) head arity = true := by
  unfold languageHasConstructorArity
  have filtered := filter_label_dataConstructor cache table nodup member
  have terms : (cacheLanguage cache table).terms =
      table.map fun entry => dataConstructor cache entry.1 entry.2 := rfl
  rw [terms, filtered]
  exact beq_iff_eq.mpr (by simp only [dataConstructor, List.length_map, List.length_range])


/-! ## Fixed constructors resolve in a larger language -/

theorem exists_term_of_languageHasConstructorArity {language : LanguageDef} {head : String}
    {arity : Nat} (resolves : languageHasConstructorArity language head arity = true) :
    ∃ term ∈ language.terms, term.label = head ∧ term.params.length = arity := by
  unfold languageHasConstructorArity at resolves
  split at resolves
  · rename_i term filtered
    have member : term ∈ language.terms.filter (fun declaration => declaration.label == head) := by
      rw [filtered]
      exact List.mem_singleton_self _
    rw [List.mem_filter] at member
    exact ⟨term, member.1, by simpa using member.2, by simpa using resolves⟩
  · exact absurd resolves Bool.false_ne_true

/-- Fixed-constructor validity transfers to a language resolving every
constructor the source language resolves. -/
theorem fixedConstructorsValid_mono {source target : LanguageDef}
    (resolves : ∀ head arity, languageHasConstructorArity source head arity = true →
      languageHasConstructorArity target head arity = true)
    (pattern : Pattern) :
    fixedConstructorsValid source pattern = true → fixedConstructorsValid target pattern = true :=
  Pattern.rec
    (motive_1 := fun pattern =>
      fixedConstructorsValid source pattern = true → fixedConstructorsValid target pattern = true)
    (motive_2 := fun patterns =>
      fixedConstructorListsValid source patterns = true →
        fixedConstructorListsValid target patterns = true)
    (fun _ _ => by rw [fixedConstructorsValid])
    (fun _ _ => by rw [fixedConstructorsValid])
    (fun head arguments transfer valid => by
      rw [fixedConstructorsValid, Bool.and_eq_true] at valid ⊢
      exact ⟨resolves _ _ valid.1, transfer valid.2⟩)
    (fun _ _ transfer valid => by
      rw [fixedConstructorsValid] at valid ⊢
      exact transfer valid)
    (fun _ _ _ transfer valid => by
      rw [fixedConstructorsValid] at valid ⊢
      exact transfer valid)
    (fun _ _ transferBody transferReplacement valid => by
      rw [fixedConstructorsValid, Bool.and_eq_true] at valid ⊢
      exact ⟨transferBody valid.1, transferReplacement valid.2⟩)
    (fun _ _ _ transfer valid => by
      rw [fixedConstructorsValid] at valid ⊢
      exact transfer valid)
    (fun _ => by rw [fixedConstructorListsValid])
    (fun _ _ transferHead transferTail valid => by
      rw [fixedConstructorListsValid, Bool.and_eq_true] at valid ⊢
      exact ⟨transferHead valid.1, transferTail valid.2⟩)
    pattern

theorem fixedConstructorListsValid_cons (language : LanguageDef) (pattern : Pattern)
    (patterns : List Pattern) :
    fixedConstructorListsValid language (pattern :: patterns) =
      (fixedConstructorsValid language pattern && fixedConstructorListsValid language patterns) := by
  rw [fixedConstructorListsValid]

theorem fixedConstructorsValid_bindAt (language : LanguageDef) (name : String) :
    (depth : Nat) → fixedConstructorsValid language (bindAt depth (.fvar name)) = true
  | 0 => by rw [bindAt, fixedConstructorsValid]
  | depth + 1 => by
      rw [bindAt, fixedConstructorsValid]
      exact fixedConstructorsValid_bindAt language name depth

theorem fixedConstructorListsValid_boundVariables (language : LanguageDef) :
    (formals : List (String × Nat)) →
      fixedConstructorListsValid language (boundVariables formals) = true
  | [] => by rw [boundVariables, List.map_nil, fixedConstructorListsValid]
  | formal :: formals => by
      have rest := fixedConstructorListsValid_boundVariables language formals
      rw [boundVariables, List.map_cons, fixedConstructorListsValid_cons,
        fixedConstructorsValid_bindAt]
      exact rest

/-! ## Occurrences, scope and binder metadata of replay patterns -/

theorem occurrences_apply (depth : Nat) (head : String) (arguments : List Pattern) :
    patternMetavariableOccurrencesAt depth (.apply head arguments) =
      patternsMetavariableOccurrencesAt depth arguments := by
  rw [patternMetavariableOccurrencesAt]

theorem occurrences_collection (depth : Nat) (kind : CollType) (elements : List Pattern)
    (rest : Option String) :
    patternMetavariableOccurrencesAt depth (.collection kind elements rest) =
      patternsMetavariableOccurrencesAt depth elements := by
  rw [patternMetavariableOccurrencesAt]

theorem occurrences_nil (depth : Nat) : patternsMetavariableOccurrencesAt depth [] = [] := by
  rw [patternsMetavariableOccurrencesAt]

theorem occurrences_cons (depth : Nat) (pattern : Pattern) (patterns : List Pattern) :
    patternsMetavariableOccurrencesAt depth (pattern :: patterns) =
      patternMetavariableOccurrencesAt depth pattern ++
        patternsMetavariableOccurrencesAt depth patterns := by
  rw [patternsMetavariableOccurrencesAt]

theorem occurrences_bindAt (name : String) :
    (depth bound : Nat) →
      patternMetavariableOccurrencesAt depth (bindAt bound (.fvar name)) = [(name, depth + bound)]
  | depth, 0 => by rw [bindAt, patternMetavariableOccurrencesAt_fvar, Nat.add_zero]
  | depth, bound + 1 => by
      rw [bindAt, patternMetavariableOccurrencesAt, occurrences_bindAt name (depth + 1) bound,
        Nat.add_right_comm, Nat.add_assoc]

theorem occurrences_boundVariables :
    (formals : List (String × Nat)) →
      patternsMetavariableOccurrencesAt 0 (boundVariables formals) = formals
  | [] => by rw [boundVariables, List.map_nil, occurrences_nil]
  | formal :: formals => by
      have rest := occurrences_boundVariables formals
      rw [boundVariables, List.map_cons, occurrences_cons, occurrences_bindAt] at *
      rw [rest, Nat.zero_add]
      rfl

theorem occurrences_acceptsJudgment (profile : CellProfile) (goal code : Pattern) :
    patternMetavariableOccurrencesAt 0 (acceptsJudgment profile goal code) =
      patternMetavariableOccurrencesAt 0 goal ++ patternMetavariableOccurrencesAt 0 code := by
  rw [acceptsJudgment, occurrences_apply, occurrences_cons, occurrences_cons, occurrences_nil,
    List.append_nil]

theorem occurrences_certificateCode (profile : CellProfile) (id : RuleId)
    (arguments children : List Pattern) :
    patternMetavariableOccurrencesAt 0 (certificateCode profile id arguments children) =
      patternsMetavariableOccurrencesAt 0 arguments ++
        patternsMetavariableOccurrencesAt 0 children := by
  rw [certificateCode, occurrences_apply, occurrences_cons, occurrences_cons, occurrences_cons,
    occurrences_nil, ruleAtom, occurrences_apply, occurrences_nil, occurrences_collection,
    occurrences_collection, List.append_nil, List.nil_append]

theorem mem_replayPremisesFrom (profile : CellProfile) {replayPremise : Pattern} :
    (next : Nat) → (premises : List Pattern) →
      replayPremise ∈ replayPremisesFrom profile next premises →
        ∃ premise ∈ premises, ∃ offset,
          replayPremise = acceptsJudgment profile premise (.fvar (childName (next + offset)))
  | _, [], member => by simp [replayPremisesFrom] at member
  | next, premise :: premises, member => by
      rw [replayPremisesFrom, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨premise, List.mem_cons_self, 0, by rw [Nat.add_zero]⟩
      · obtain ⟨other, otherMember, offset, rfl⟩ :=
          mem_replayPremisesFrom profile (next + 1) premises member
        exact ⟨other, List.mem_cons_of_mem _ otherMember, offset + 1, by
          rw [Nat.add_right_comm, Nat.add_assoc]⟩

theorem mem_occurrences_replayPremisesFrom (profile : CellProfile)
    {occurrence : String × Nat} :
    (next : Nat) → (premises : List Pattern) →
      occurrence ∈ patternsMetavariableOccurrencesAt 0 (replayPremisesFrom profile next premises) →
        (∃ premise ∈ premises, occurrence ∈ patternMetavariableOccurrencesAt 0 premise) ∨
          occurrence ∈ childFormalsFrom next premises
  | _, [], member => by
      rw [replayPremisesFrom, occurrences_nil] at member
      simp at member
  | next, premise :: premises, member => by
      rw [replayPremisesFrom, occurrences_cons, occurrences_acceptsJudgment,
        patternMetavariableOccurrencesAt_fvar] at member
      rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact Or.inl ⟨premise, List.mem_cons_self, member⟩
        · rw [List.mem_singleton] at member
          subst member
          exact Or.inr (by rw [childFormalsFrom]; exact List.mem_cons_self)
      · rcases mem_occurrences_replayPremisesFrom profile (next + 1) premises member with
          ⟨other, otherMember, occurs⟩ | childMember
        · exact Or.inl ⟨other, List.mem_cons_of_mem _ otherMember, occurs⟩
        · exact Or.inr (by rw [childFormalsFrom]; exact List.mem_cons_of_mem _ childMember)

/-- The formals of a replay rule, the rule's own followed by one child per
premise. -/
abbrev replayFormals (rule : RuleSchema) : List (String × Nat) :=
  rule.metavariables ++ childFormalsFrom rule.metavariables.length rule.premises

theorem occurrences_replayConclusion (profile : CellProfile) (rule : RuleSchema) :
    patternMetavariableOccurrencesAt 0 (replayRule profile rule).conclusion =
      patternMetavariableOccurrencesAt 0 rule.conclusion ++ replayFormals rule := by
  change patternMetavariableOccurrencesAt 0 (acceptsJudgment profile rule.conclusion
    (certificateCode profile rule.id (boundVariables rule.metavariables)
      (boundVariables (childFormalsFrom rule.metavariables.length rule.premises)))) = _
  rw [occurrences_acceptsJudgment, occurrences_certificateCode, occurrences_boundVariables,
    occurrences_boundVariables]

theorem isWellScopedAt_bindAt (pattern : Pattern) :
    (depth bound : Nat) →
      (bindAt bound pattern).isWellScopedAt depth = pattern.isWellScopedAt (depth + bound)
  | depth, 0 => by rw [bindAt, Nat.add_zero]
  | depth, bound + 1 => by
      rw [bindAt, Pattern.isWellScopedAt, isWellScopedAt_bindAt pattern (depth + 1) bound,
        Nat.add_right_comm, Nat.add_assoc]

theorem isWellScopedListAt_boundVariables (depth : Nat) :
    (formals : List (String × Nat)) →
      Pattern.isWellScopedListAt depth (boundVariables formals) = true
  | [] => by rw [boundVariables, List.map_nil, Pattern.isWellScopedListAt]
  | formal :: formals => by
      have rest := isWellScopedListAt_boundVariables depth formals
      rw [boundVariables, List.map_cons, Pattern.isWellScopedListAt, isWellScopedAt_bindAt,
        Pattern.isWellScopedAt, Bool.true_and]
      exact rest

theorem isWellScoped_acceptsJudgment (profile : CellProfile) (goal code : Pattern) :
    (acceptsJudgment profile goal code).isWellScoped =
      (goal.isWellScoped && code.isWellScoped) := by
  simp only [acceptsJudgment, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Bool.and_true]

theorem isWellScoped_certificateCode (profile : CellProfile) (id : RuleId)
    (arguments children : List (String × Nat)) :
    (certificateCode profile id (boundVariables arguments)
      (boundVariables children)).isWellScoped = true := by
  simp only [certificateCode, ruleAtom, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, isWellScopedListAt_boundVariables, Bool.and_true]

theorem noCollectionRest_bindAt (name : String) :
    (depth : Nat) → patternHasNoCollectionRest (bindAt depth (.fvar name)) = true
  | 0 => by rw [bindAt, patternHasNoCollectionRest]
  | depth + 1 => by
      rw [bindAt, patternHasNoCollectionRest]
      exact noCollectionRest_bindAt name depth

theorem patternsHaveNoCollectionRest_cons (pattern : Pattern) (patterns : List Pattern) :
    patternsHaveNoCollectionRest (pattern :: patterns) =
      (patternHasNoCollectionRest pattern && patternsHaveNoCollectionRest patterns) := by
  rw [patternsHaveNoCollectionRest]

theorem patternsHaveNoCollectionRest_nil : patternsHaveNoCollectionRest [] = true := by
  rw [patternsHaveNoCollectionRest]

theorem noCollectionRest_boundVariables :
    (formals : List (String × Nat)) → patternsHaveNoCollectionRest (boundVariables formals) = true
  | [] => by rw [boundVariables, List.map_nil, patternsHaveNoCollectionRest_nil]
  | formal :: formals => by
      have rest := noCollectionRest_boundVariables formals
      rw [boundVariables, List.map_cons, patternsHaveNoCollectionRest_cons,
        noCollectionRest_bindAt]
      exact rest

theorem noCollectionRest_acceptsJudgment (profile : CellProfile) (goal code : Pattern) :
    patternHasNoCollectionRest (acceptsJudgment profile goal code) =
      (patternHasNoCollectionRest goal && patternHasNoCollectionRest code) := by
  rw [acceptsJudgment, patternHasNoCollectionRest, patternsHaveNoCollectionRest_cons,
    patternsHaveNoCollectionRest_cons, patternsHaveNoCollectionRest_nil, Bool.and_true]

theorem noCollectionRest_certificateCode (profile : CellProfile) (id : RuleId)
    (arguments children : List (String × Nat)) :
    patternHasNoCollectionRest
      (certificateCode profile id (boundVariables arguments) (boundVariables children)) = true := by
  rw [certificateCode, patternHasNoCollectionRest, patternsHaveNoCollectionRest_cons,
    patternsHaveNoCollectionRest_cons, patternsHaveNoCollectionRest_cons,
    patternsHaveNoCollectionRest_nil, ruleAtom, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest_nil, patternHasNoCollectionRest, patternHasNoCollectionRest,
    noCollectionRest_boundVariables, noCollectionRest_boundVariables]
  rfl

theorem canonical_boundVariables :
    (formals : List (String × Nat)) →
      Pattern.hasCanonicalBinderMetadataList (boundVariables formals) = true
  | [] => by rw [boundVariables, List.map_nil, Pattern.hasCanonicalBinderMetadataList]
  | formal :: formals => by
      have rest := canonical_boundVariables formals
      rw [boundVariables, List.map_cons, Pattern.hasCanonicalBinderMetadataList,
        hasCanonicalBinderMetadata_bindAt, Pattern.hasCanonicalBinderMetadata, Bool.true_and]
      exact rest

theorem canonical_acceptsJudgment (profile : CellProfile) (goal code : Pattern) :
    (acceptsJudgment profile goal code).hasCanonicalBinderMetadata =
      (goal.hasCanonicalBinderMetadata && code.hasCanonicalBinderMetadata) := by
  simp only [acceptsJudgment, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Bool.and_true]

theorem canonical_certificateCode (profile : CellProfile) (id : RuleId)
    (arguments children : List (String × Nat)) :
    (certificateCode profile id (boundVariables arguments)
      (boundVariables children)).hasCanonicalBinderMetadata = true := by
  simp only [certificateCode, ruleAtom, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, canonical_boundVariables, Bool.and_true]

/-! ## Every replay rule of a valid, fresh rule is locally valid -/

theorem eraseDups_nodup_iff (values : List String) :
    (values.eraseDups.length == values.length) = true ↔ values.Nodup :=
  Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup values

/-- **Local validity of a replay rule.** -/
theorem replayRule_isLocallyValid (profile : CellProfile) {rule : RuleSchema}
    (valid : RuleSchema.isLocallyValid rule = true) (fresh : ChildNamesFresh rule) :
    RuleSchema.isLocallyValid (replayRule profile rule) = true := by
  simp only [RuleSchema.isLocallyValid, Bool.and_eq_true] at valid ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨idNonempty, namesNonempty⟩, namesDistinct⟩, occurrencesDeclared⟩, _⟩,
    wellScoped⟩, noRest⟩, canonical⟩ := valid
  have ruleOccurrence : ∀ pattern ∈ rule.premises ++ [rule.conclusion],
      ∀ occurrence ∈ patternMetavariableOccurrencesAt 0 pattern,
        occurrence ∈ rule.metavariables := by
    intro pattern member occurrence occurs
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp occurrencesDeclared) occurrence
      (mem_patternsMetavariableOccurrencesAt _ member occurs))
  have patternFact {check : Pattern → Bool}
      (holds : (rule.premises ++ [rule.conclusion]).all check = true) :
      ∀ pattern ∈ rule.premises ++ [rule.conclusion], check pattern = true :=
    List.all_eq_true.mp holds
  have occurrencesEq : RuleSchema.occurrences (replayRule profile rule) =
      patternsMetavariableOccurrencesAt 0
          (replayPremisesFrom profile rule.metavariables.length rule.premises) ++
        (patternMetavariableOccurrencesAt 0 rule.conclusion ++ replayFormals rule) := by
    rw [RuleSchema.occurrences, RuleSchema.patterns, patternsMetavariableOccurrencesAt_append,
      occurrences_cons, occurrences_nil, List.append_nil, occurrences_replayConclusion]
    rfl
  refine ⟨⟨⟨⟨⟨⟨⟨idNonempty, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro name member
    change name ∈ (replayFormals rule).map (fun formal => formal.1) at member
    rw [List.map_append, List.mem_append] at member
    rcases member with member | member
    · exact (List.all_eq_true.mp namesNonempty) name member
    · obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨offset, _, rfl⟩ := mem_childFormalsFrom _ _ childMember
      exact bne_iff_ne.mpr (childName_ne_empty _)
  · apply (eraseDups_nodup_iff _).mpr
    exact replayNames_nodup ((eraseDups_nodup_iff _).mp namesDistinct) fresh
  · rw [List.all_eq_true, occurrencesEq]
    intro occurrence member
    apply List.contains_iff_mem.mpr
    change occurrence ∈ replayFormals rule
    rcases List.mem_append.mp member with member | member
    · rcases mem_occurrences_replayPremisesFrom profile _ _ member with
        ⟨premise, premiseMember, occurs⟩ | childMember
      · exact List.mem_append_left _
          (ruleOccurrence premise (List.mem_append_left _ premiseMember) occurrence occurs)
      · exact List.mem_append_right _ childMember
    · rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ (ruleOccurrence rule.conclusion
          (List.mem_append_right _ (List.mem_singleton_self _)) occurrence member)
      · exact member
  · rw [List.all_eq_true, occurrencesEq]
    intro formal member
    apply List.contains_iff_mem.mpr
    exact List.mem_append_right _ (List.mem_append_right _ member)
  · rw [List.all_eq_true]
    intro pattern member
    change pattern ∈ replayPremisesFrom profile rule.metavariables.length rule.premises ++
      [(replayRule profile rule).conclusion] at member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨premise, premiseMember, offset, rfl⟩ :=
        mem_replayPremisesFrom profile _ _ member
      rw [isWellScoped_acceptsJudgment,
        patternFact wellScoped premise (List.mem_append_left _ premiseMember)]
      rfl
    · rw [List.mem_singleton] at member
      subst member
      change (acceptsJudgment profile rule.conclusion
        (certificateCode profile rule.id (boundVariables rule.metavariables)
          (boundVariables (childFormalsFrom rule.metavariables.length rule.premises)))).isWellScoped
          = true
      rw [isWellScoped_acceptsJudgment, isWellScoped_certificateCode,
        patternFact wellScoped rule.conclusion (List.mem_append_right _ (List.mem_singleton_self _))]
      rfl
  · rw [List.all_eq_true]
    intro pattern member
    change pattern ∈ replayPremisesFrom profile rule.metavariables.length rule.premises ++
      [(replayRule profile rule).conclusion] at member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨premise, premiseMember, offset, rfl⟩ :=
        mem_replayPremisesFrom profile _ _ member
      rw [noCollectionRest_acceptsJudgment,
        patternFact noRest premise (List.mem_append_left _ premiseMember),
        patternHasNoCollectionRest]
      rfl
    · rw [List.mem_singleton] at member
      subst member
      change patternHasNoCollectionRest (acceptsJudgment profile rule.conclusion
        (certificateCode profile rule.id (boundVariables rule.metavariables)
          (boundVariables (childFormalsFrom rule.metavariables.length rule.premises)))) = true
      rw [noCollectionRest_acceptsJudgment, noCollectionRest_certificateCode,
        patternFact noRest rule.conclusion (List.mem_append_right _ (List.mem_singleton_self _))]
      rfl
  · rw [List.all_eq_true]
    intro pattern member
    change pattern ∈ replayPremisesFrom profile rule.metavariables.length rule.premises ++
      [(replayRule profile rule).conclusion] at member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨premise, premiseMember, offset, rfl⟩ :=
        mem_replayPremisesFrom profile _ _ member
      rw [canonical_acceptsJudgment,
        patternFact canonical premise (List.mem_append_left _ premiseMember)]
      rfl
    · rw [List.mem_singleton] at member
      subst member
      change (acceptsJudgment profile rule.conclusion
        (certificateCode profile rule.id (boundVariables rule.metavariables)
          (boundVariables (childFormalsFrom rule.metavariables.length rule.premises)))).hasCanonicalBinderMetadata
          = true
      rw [canonical_acceptsJudgment, canonical_certificateCode,
        patternFact canonical rule.conclusion (List.mem_append_right _ (List.mem_singleton_self _))]
      rfl


/-! ## The presentation and its freshness conditions -/

/-- The calculus's own data constructors, with their arities. -/
def baseEntries (definition : CalculusLanguageDef) : ArityTable :=
  definition.terms.map fun term => (term.label, term.params.length)

/-- The constructors a replay presentation declares beyond the calculus's
own: the judgment heads, nested inside acceptance judgments; the certificate
constructor; and one nullary atom per rule identifier. -/
def newEntries (profile : CellProfile) (definition : CalculusLanguageDef) : ArityTable :=
  definition.judgments.map (fun judgment => (judgment.head, judgment.arity)) ++
    (profile.certificate, 3) :: definition.rules.map (fun rule => (rule.id.value, 0))

/-- The constructor table of the replay presentation. -/
def replayTable (profile : CellProfile) (definition : CalculusLanguageDef) : ArityTable :=
  extendTable (baseEntries definition) (newEntries profile definition)

/-- **The replay presentation** of a calculus: its replay rules, with the one
judgment `Accepts/2`, over a companion cache whose constructor table is
`replayTable`. -/
def replayPresentation (cache : CacheProfile) (profile : CellProfile)
    (definition : CalculusLanguageDef) : CalculusLanguageDef :=
  cacheDefinition cache (replayTable profile definition)
    [{ head := profile.accepts, arity := 2 }] (replayRules profile definition.rules)

/-- Freshness conditions under which the replay presentation is valid. -/
structure Fresh (profile : CellProfile) (definition : CalculusLanguageDef) : Prop where
  childNames : ∀ rule ∈ definition.rules, ChildNamesFresh rule
  consistent : ArityConsistent (baseEntries definition ++ newEntries profile definition)
  acceptsNonempty : profile.accepts ≠ ""
  acceptsFresh :
    profile.accepts ∉ (baseEntries definition ++ newEntries profile definition).map Prod.fst
  acceptsUnreserved : profile.accepts ∉ [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]

theorem baseEntries_names_nodup (definition : ValidatedCalculusLanguageDef) :
    ((baseEntries definition.1).map Prod.fst).Nodup := by
  have valid := definition.2
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    Bool.and_eq_true] at valid
  have labels := LanguageDef.constructorLabels_nodup_of_validate_eq_nil _
    (List.isEmpty_iff.mp valid.1.1.1.1.1)
  simpa [baseEntries, List.map_map, Function.comp_def] using labels

theorem replayTable_names_nodup (profile : CellProfile) (definition : ValidatedCalculusLanguageDef) :
    ((replayTable profile definition.1).map Prod.fst).Nodup :=
  extendTable_names_nodup _ _ (baseEntries_names_nodup definition)

theorem mem_replayTable (profile : CellProfile) (definition : CalculusLanguageDef)
    (fresh : Fresh profile definition) {entry : String × Nat}
    (member : entry ∈ baseEntries definition ++ newEntries profile definition) :
    entry ∈ replayTable profile definition :=
  mem_extendTable_of_consistent _ _ fresh.consistent entry member

theorem replayTable_names_subset (profile : CellProfile) (definition : CalculusLanguageDef)
    {name : String} (member : name ∈ (replayTable profile definition).map Prod.fst) :
    name ∈ (baseEntries definition ++ newEntries profile definition).map Prod.fst := by
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
  exact List.mem_map_of_mem (mem_of_mem_extendTable _ _ entryMember)

theorem resolves_in_replayTable (cache : CacheProfile) (profile : CellProfile)
    (definition : ValidatedCalculusLanguageDef) (fresh : Fresh profile definition.1)
    {head : String} {arity : Nat}
    (member : (head, arity) ∈ baseEntries definition.1 ++ newEntries profile definition.1) :
    languageHasConstructorArity (cacheLanguage cache (replayTable profile definition.1))
      head arity = true :=
  languageHasConstructorArity_cacheLanguage cache (replayTable_names_nodup profile definition)
    (mem_replayTable profile definition.1 fresh member)

theorem base_resolves (cache : CacheProfile) (profile : CellProfile)
    (definition : ValidatedCalculusLanguageDef) (fresh : Fresh profile definition.1) :
    ∀ head arity, languageHasConstructorArity definition.1.toLanguageDef head arity = true →
      languageHasConstructorArity (cacheLanguage cache (replayTable profile definition.1))
        head arity = true := by
  intro head arity resolves
  obtain ⟨term, termMember, rfl, rfl⟩ := exists_term_of_languageHasConstructorArity resolves
  exact resolves_in_replayTable cache profile definition fresh
    (List.mem_append_left _ (List.mem_map_of_mem (f := fun term : GrammarRule =>
      (term.label, term.params.length)) termMember))

theorem fixedConstructorListsValid_mono {source target : LanguageDef}
    (resolves : ∀ head arity, languageHasConstructorArity source head arity = true →
      languageHasConstructorArity target head arity = true) :
    (patterns : List Pattern) → fixedConstructorListsValid source patterns = true →
      fixedConstructorListsValid target patterns = true
  | [], _ => by rw [fixedConstructorListsValid]
  | pattern :: patterns, valid => by
      rw [fixedConstructorListsValid_cons, Bool.and_eq_true] at valid ⊢
      exact ⟨fixedConstructorsValid_mono resolves pattern valid.1,
        fixedConstructorListsValid_mono resolves patterns valid.2⟩

theorem mem_of_lookupJudgment? {definition : CalculusLanguageDef} {head : String}
    {arity : Nat} {declaration : JudgmentDecl}
    (lookup : definition.lookupJudgment? head arity = some declaration) :
    declaration ∈ definition.judgments ∧ declaration.head = head ∧
      declaration.arity = arity := by
  unfold CalculusLanguageDef.lookupJudgment? at lookup
  split at lookup
  · rename_i found filtered
    have same : found = declaration := Option.some.inj lookup
    have member : found ∈ definition.judgments.filter
        (fun candidate => candidate.head == head && candidate.arity == arity) := by
      rw [filtered]
      exact List.mem_singleton_self _
    rw [List.mem_filter, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at member
    subst same
    exact ⟨member.1, member.2.1, member.2.2⟩
  · cases lookup

/-- A judgment of the calculus is valid nested data in the companion cache. -/
theorem fixedConstructorsValid_judgment (cache : CacheProfile) (profile : CellProfile)
    (definition : ValidatedCalculusLanguageDef) (fresh : Fresh profile definition.1)
    {judgment : Pattern} (valid : definition.1.judgmentSchemaValid judgment = true) :
    fixedConstructorsValid (cacheLanguage cache (replayTable profile definition.1))
      judgment = true := by
  cases judgment with
  | apply head arguments =>
      rw [CalculusLanguageDef.judgmentSchemaValid, Bool.and_eq_true] at valid
      rw [fixedConstructorsValid, Bool.and_eq_true]
      obtain ⟨declaration, lookup⟩ := Option.isSome_iff_exists.mp valid.1
      obtain ⟨declarationMember, rfl, arityEq⟩ := mem_of_lookupJudgment? lookup
      refine ⟨?_, fixedConstructorListsValid_mono
        (base_resolves cache profile definition fresh) arguments valid.2⟩
      rw [← arityEq]
      exact resolves_in_replayTable cache profile definition fresh
        (List.mem_append_right _ (List.mem_append_left _
          (List.mem_map_of_mem (f := fun judgment : JudgmentDecl =>
            (judgment.head, judgment.arity)) declarationMember)))
  | bvar _ => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | fvar _ => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | lambda _ _ => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | multiLambda _ _ _ => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | subst _ _ => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | collection _ _ _ => simp [CalculusLanguageDef.judgmentSchemaValid] at valid

theorem lookupJudgment?_replayPresentation (cache : CacheProfile) (profile : CellProfile)
    (definition : CalculusLanguageDef) :
    (replayPresentation cache profile definition).lookupJudgment? profile.accepts 2 =
      some { head := profile.accepts, arity := 2 } := by
  have filtered : ([{ head := profile.accepts, arity := 2 }] : List JudgmentDecl).filter
      (fun declaration => declaration.head == profile.accepts && declaration.arity == 2) =
        [{ head := profile.accepts, arity := 2 }] := by
    rw [List.filter_cons, if_pos (by
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr rfl, beq_iff_eq.mpr rfl⟩), List.filter_nil]
  unfold CalculusLanguageDef.lookupJudgment?
  change (match ([{ head := profile.accepts, arity := 2 }] : List JudgmentDecl).filter
      (fun declaration => declaration.head == profile.accepts && declaration.arity == 2) with
    | [declaration] => some declaration
    | _ => none) = _
  rw [filtered]

theorem judgmentSchemaValid_acceptsJudgment (cache : CacheProfile) (profile : CellProfile)
    (definition : CalculusLanguageDef) (goal code : Pattern) :
    (replayPresentation cache profile definition).judgmentSchemaValid
        (acceptsJudgment profile goal code) =
      (fixedConstructorsValid (cacheLanguage cache (replayTable profile definition)) goal &&
        fixedConstructorsValid (cacheLanguage cache (replayTable profile definition)) code) := by
  rw [acceptsJudgment, CalculusLanguageDef.judgmentSchemaValid]
  change (((replayPresentation cache profile definition).lookupJudgment? profile.accepts
    2).isSome && fixedConstructorListsValid
      (replayPresentation cache profile definition).toLanguageDef [goal, code]) = _
  rw [lookupJudgment?_replayPresentation, Option.isSome_some, Bool.true_and]
  change fixedConstructorListsValid (cacheLanguage cache (replayTable profile definition))
    [goal, code] = _
  rw [fixedConstructorListsValid_cons, fixedConstructorListsValid_cons,
    fixedConstructorListsValid, Bool.and_true]

theorem getElem?_append_of_some {α : Type} {formals extra : List α} {index : Nat} {value : α}
    (present : formals[index]? = some value) : (formals ++ extra)[index]? = some value := by
  have bound : index < formals.length := (List.getElem?_eq_some_iff.mp present).1
  rw [List.getElem?_append_left bound, present]

/-- Side conditions index a prefix of the formals, so appending child formals
keeps them valid. -/
theorem isValidFor_append {formals extra : List (String × Nat)} :
    (condition : RuleSideCondition) →
      RuleSideCondition.isValidFor formals condition = true →
        RuleSideCondition.isValidFor (formals ++ extra) condition = true
  | .explicitSubstitution ambient body replacement result, valid => by
      unfold RuleSideCondition.isValidFor at valid ⊢
      dsimp only at valid ⊢
      cases bodyFound : formals[body]? with
      | none => simp [bodyFound] at valid
      | some bodyFormal =>
          cases replacementFound : formals[replacement]? with
          | none => simp [bodyFound, replacementFound] at valid
          | some replacementFormal =>
              cases resultFound : formals[result]? with
              | none => simp [bodyFound, replacementFound, resultFound] at valid
              | some resultFormal =>
                  rw [getElem?_append_of_some bodyFound, getElem?_append_of_some replacementFound,
                    getElem?_append_of_some resultFound]
                  simpa [bodyFound, replacementFound, resultFound] using valid
  | .unusedBinderElimination ambient body result, valid => by
      unfold RuleSideCondition.isValidFor at valid ⊢
      dsimp only at valid ⊢
      cases bodyFound : formals[body]? with
      | none => simp [bodyFound] at valid
      | some bodyFormal =>
          cases resultFound : formals[result]? with
          | none => simp [bodyFound, resultFound] at valid
          | some resultFormal =>
              rw [getElem?_append_of_some bodyFound, getElem?_append_of_some resultFound]
              simpa [bodyFound, resultFound] using valid

/-- **Contextual validity of a replay rule** in the replay presentation. -/
theorem replayRule_isValidIn (cache : CacheProfile) (profile : CellProfile)
    (definition : ValidatedCalculusLanguageDef) (fresh : Fresh profile definition.1)
    {rule : RuleSchema} (member : rule ∈ definition.1.rules) :
    RuleSchema.isValidIn (replayPresentation cache profile definition.1)
      (replayRule profile rule) = true := by
  have ruleValid := rule_isValidIn_of_mem definition member
  simp only [RuleSchema.isValidIn, Bool.and_eq_true] at ruleValid ⊢
  obtain ⟨localValid, judgmentsValid, sidesValid⟩ := ruleValid
  have judgmentValid : ∀ pattern ∈ rule.premises ++ [rule.conclusion],
      fixedConstructorsValid (cacheLanguage cache (replayTable profile definition.1))
        pattern = true :=
    fun pattern patternMember => fixedConstructorsValid_judgment cache profile definition fresh
      ((List.all_eq_true.mp judgmentsValid) pattern patternMember)
  refine ⟨replayRule_isLocallyValid profile localValid (fresh.childNames rule member), ?_, ?_⟩
  · rw [List.all_eq_true]
    intro pattern patternMember
    change pattern ∈ replayPremisesFrom profile rule.metavariables.length rule.premises ++
      [(replayRule profile rule).conclusion] at patternMember
    rcases List.mem_append.mp patternMember with patternMember | patternMember
    · obtain ⟨premise, premiseMember, offset, rfl⟩ :=
        mem_replayPremisesFrom profile _ _ patternMember
      rw [judgmentSchemaValid_acceptsJudgment,
        judgmentValid premise (List.mem_append_left _ premiseMember), fixedConstructorsValid]
      rfl
    · rw [List.mem_singleton] at patternMember
      subst patternMember
      change (replayPresentation cache profile definition.1).judgmentSchemaValid
        (acceptsJudgment profile rule.conclusion
          (certificateCode profile rule.id (boundVariables rule.metavariables)
            (boundVariables (childFormalsFrom rule.metavariables.length rule.premises)))) = true
      rw [judgmentSchemaValid_acceptsJudgment,
        judgmentValid rule.conclusion (List.mem_append_right _ (List.mem_singleton_self _)),
        Bool.true_and, certificateCode, fixedConstructorsValid, Bool.and_eq_true]
      refine ⟨resolves_in_replayTable cache profile definition fresh
        (List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)), ?_⟩
      rw [fixedConstructorListsValid_cons, fixedConstructorListsValid_cons,
        fixedConstructorListsValid_cons, ruleAtom, fixedConstructorsValid,
        fixedConstructorsValid, fixedConstructorsValid,
        fixedConstructorListsValid_boundVariables, fixedConstructorListsValid_boundVariables]
      have atom := resolves_in_replayTable cache profile definition fresh
        (head := rule.id.value) (arity := 0)
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun rule : RuleSchema => (rule.id.value, 0)) member))))
      simp [atom, fixedConstructorListsValid]
  · rw [List.all_eq_true]
    intro condition conditionMember
    exact isValidFor_append condition ((List.all_eq_true.mp sidesValid) condition conditionMember)

theorem ruleIds_replayRules (profile : CellProfile) (rules : List RuleSchema) :
    (replayRules profile rules).map (·.id) = rules.map (·.id) := by
  rw [replayRules, List.map_map]
  rfl

/-- **Generic validity of replay presentations.**  The replay presentation of
a validated calculus satisfying the freshness conditions is valid. -/
theorem replayPresentation_valid (cache : CacheProfile) (profile : CellProfile)
    (definition : ValidatedCalculusLanguageDef) (fresh : Fresh profile definition.1) :
    (replayPresentation cache profile definition.1).isValid = true := by
  have valid := definition.2
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨⟨_, _⟩, idsDistinct⟩, _⟩, _⟩, _⟩ := valid
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact List.isEmpty_iff.mpr
      (cacheLanguage_validate cache _ (replayTable_names_nodup profile definition))
  · rw [List.all_eq_true]
    intro replayed replayedMember
    change replayed ∈ (definition.1.rules).map (replayRule profile) at replayedMember
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp replayedMember
    have ruleValid := rule_isValidIn_of_mem definition ruleMember
    simp only [RuleSchema.isValidIn, Bool.and_eq_true] at ruleValid
    exact replayRule_isLocallyValid profile ruleValid.1 (fresh.childNames rule ruleMember)
  · change (((replayRules profile definition.1.rules).map (·.id)).eraseDups.length ==
      ((replayRules profile definition.1.rules).map (·.id)).length) = true
    rw [ruleIds_replayRules]
    exact idsDistinct
  · have absent : profile.accepts ∉ (replayTable profile definition.1).map Prod.fst :=
      fun member => fresh.acceptsFresh (replayTable_names_subset profile definition.1 member)
    have notConstructor : (cacheLanguage cache (replayTable profile definition.1)).terms.any
        (fun declaration => declaration.label == profile.accepts) = false := by
      rw [Bool.eq_false_iff]
      intro found
      obtain ⟨declaration, declarationMember, sameLabel⟩ := List.any_eq_true.mp found
      apply absent
      rw [← cacheLanguage_labels cache]
      exact (beq_iff_eq.mp sameLabel) ▸ List.mem_map_of_mem declarationMember
    have notReserved : [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead].contains
        profile.accepts = false :=
      Bool.eq_false_iff.mpr fun found =>
        fresh.acceptsUnreserved (List.contains_iff_mem.mp found)
    have nonempty : (profile.accepts != "") = true := bne_iff_ne.mpr fresh.acceptsNonempty
    change ((([{ head := profile.accepts, arity := 2 }] : List JudgmentDecl).all
          (fun judgment => judgment.head != "") &&
        ([profile.accepts].eraseDups.length == [profile.accepts].length)) &&
      [profile.accepts].all (fun head =>
        !((cacheLanguage cache (replayTable profile definition.1)).terms.any
            fun declaration => declaration.label == head) &&
          !([Pattern.zipHead, Pattern.mapHead, Pattern.evalHead].contains head))) = true
    have singleton : ([profile.accepts].eraseDups.length == [profile.accepts].length) = true :=
      beq_iff_eq.mpr rfl
    simp only [List.all_cons, List.all_nil, notConstructor, notReserved, nonempty, singleton,
      Bool.and_true, Bool.not_false]
  · rw [List.all_eq_true]
    intro replayed replayedMember
    change replayed ∈ (definition.1.rules).map (replayRule profile) at replayedMember
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp replayedMember
    exact replayRule_isValidIn cache profile definition fresh ruleMember
  · rfl

/-- The replay presentation as a validated calculus. -/
def replayCell (cache : CacheProfile) (profile : CellProfile)
    (definition : ValidatedCalculusLanguageDef) (fresh : Fresh profile definition.1) :
    ValidatedCalculusLanguageDef :=
  ⟨replayPresentation cache profile definition.1,
    replayPresentation_valid cache profile definition fresh⟩

theorem replayCell_rules (cache : CacheProfile) (profile : CellProfile)
    (definition : ValidatedCalculusLanguageDef) (fresh : Fresh profile definition.1) :
    (replayCell cache profile definition fresh).1.rules =
      replayRules profile definition.1.rules := rfl

/-- **The reflexive cell, for every fresh validated calculus.**  The generic
checker run on the replay presentation agrees with the checker run on the
calculus. -/
theorem replayCell_checkRaw (cache : CacheProfile) (profile : CellProfile)
    (definition : ValidatedCalculusLanguageDef) (fresh : Fresh profile definition.1)
    (goal : Pattern) (certificate : RawProof) :
    checkRaw (replayCell cache profile definition fresh)
        (acceptsJudgment profile goal (quoteProof profile definition.1 certificate))
        (replayProof profile definition.1 certificate) =
      checkRaw definition goal certificate :=
  checkRaw_replayProof profile definition (replayCell cache profile definition fresh)
    (replayCell_rules cache profile definition fresh) goal certificate


/-! ## The tower at every level -/

theorem baseEntries_replayPresentation (cache : CacheProfile) (profile : CellProfile)
    (definition : CalculusLanguageDef) :
    baseEntries (replayPresentation cache profile definition) =
      replayTable profile definition :=
  cacheLanguage_entries cache (replayTable profile definition)

theorem newEntries_replayPresentation (cache : CacheProfile) (profile next : CellProfile)
    (definition : CalculusLanguageDef) :
    newEntries next (replayPresentation cache profile definition) =
      (profile.accepts, 2) :: (next.certificate, 3) ::
        definition.rules.map (fun rule => (rule.id.value, 0)) := by
  simp [newEntries, replayPresentation, replayRules, List.map_map, Function.comp_def,
    replayRule]

/-- Every entry of the next level is the new acceptance head or already in the
replay table. -/
theorem nextEntry_cases (cache : CacheProfile) (profile next : CellProfile)
    (definition : CalculusLanguageDef) (fresh : Fresh profile definition)
    (sameCertificate : next.certificate = profile.certificate) {entry : String × Nat}
    (member : entry ∈ baseEntries (replayPresentation cache profile definition) ++
      newEntries next (replayPresentation cache profile definition)) :
    entry = (profile.accepts, 2) ∨ entry ∈ replayTable profile definition := by
  rw [baseEntries_replayPresentation, newEntries_replayPresentation, sameCertificate] at member
  rcases List.mem_append.mp member with member | member
  · exact Or.inr member
  · rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl rfl
    · right
      apply mem_replayTable profile definition fresh
      exact List.mem_append_right _ (List.mem_append_right _ member)

/-- **Freshness is inherited.**  The replay presentation is fresh for the next
level's profile when that profile keeps the certificate constructor and its
acceptance head avoids every name used so far. -/
theorem fresh_replayPresentation (cache : CacheProfile) (profile next : CellProfile)
    (definition : CalculusLanguageDef) (fresh : Fresh profile definition)
    (sameCertificate : next.certificate = profile.certificate)
    (nextNonempty : next.accepts ≠ "")
    (nextUnreserved : next.accepts ∉ [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead])
    (nextFresh :
      next.accepts ∉ (baseEntries definition ++ newEntries profile definition).map Prod.fst)
    (nextDistinct : next.accepts ≠ profile.accepts) :
    Fresh next (replayPresentation cache profile definition) where
  childNames := by
    intro replayed replayedMember
    change replayed ∈ definition.rules.map (replayRule profile) at replayedMember
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp replayedMember
    exact childNamesFresh_replayRule profile (fresh.childNames rule ruleMember)
  consistent := by
    have tableConsistent : ArityConsistent (replayTable profile definition) :=
      fresh.consistent.mono fun entry member => mem_of_mem_extendTable _ _ member
    have acceptsAbsent : profile.accepts ∉ (replayTable profile definition).map Prod.fst :=
      fun member => fresh.acceptsFresh (replayTable_names_subset profile definition member)
    intro entry member other otherMember sameName
    rcases nextEntry_cases cache profile next definition fresh sameCertificate member with
      rfl | entryMember <;>
    rcases nextEntry_cases cache profile next definition fresh sameCertificate otherMember with
      rfl | otherInTable
    · rfl
    · have otherName : other.1 = profile.accepts := sameName.symm
      exact (acceptsAbsent (otherName ▸ List.mem_map_of_mem (f := Prod.fst) otherInTable)).elim
    · have entryName : entry.1 = profile.accepts := sameName
      exact (acceptsAbsent (entryName ▸ List.mem_map_of_mem (f := Prod.fst) entryMember)).elim
    · exact tableConsistent entry entryMember other otherInTable sameName
  acceptsNonempty := nextNonempty
  acceptsFresh := by
    intro member
    obtain ⟨entry, entryMember, nameEq⟩ := List.mem_map.mp member
    rcases nextEntry_cases cache profile next definition fresh sameCertificate entryMember with
      rfl | entryInTable
    · exact nextDistinct nameEq.symm
    · exact nextFresh (nameEq ▸ replayTable_names_subset profile definition
        (List.mem_map_of_mem (f := Prod.fst) entryInTable))
  acceptsUnreserved := nextUnreserved

/-- Profiles for every level of a tower over a base calculus: an acceptance
head per level, one certificate constructor, and a cache profile per level. -/
structure TowerProfiles (definition : CalculusLanguageDef) where
  accepts : Nat → String
  certificate : String
  cache : Nat → CacheProfile
  injective : Function.Injective accepts
  nonempty : ∀ level, accepts level ≠ ""
  unreserved : ∀ level, accepts level ∉ [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  fresh : ∀ level, accepts level ∉
    (baseEntries definition ++ newEntries ⟨accepts 0, certificate⟩ definition).map Prod.fst

namespace TowerProfiles

variable {definition : ValidatedCalculusLanguageDef} (profiles : TowerProfiles definition.1)

/-- The profile of a level. -/
def profile (level : Nat) : CellProfile := ⟨profiles.accepts level, profiles.certificate⟩

/-- The names a level may use: the base calculus's names and the acceptance
heads of the levels below. -/
def Names (level : Nat) (name : String) : Prop :=
  name ∈ (baseEntries definition.1 ++ newEntries (profiles.profile 0) definition.1).map Prod.fst ∨
    ∃ below, below < level ∧ name = profiles.accepts below

/-- One level of the tower, with the invariant that makes the next level
valid. -/
structure Level (level : Nat) where
  calculus : ValidatedCalculusLanguageDef
  fresh : Fresh (profiles.profile level) calculus.1
  names : ∀ name ∈ (baseEntries calculus.1 ++ newEntries (profiles.profile level) calculus.1).map
    Prod.fst, profiles.Names level name

/-- The next level: the replay presentation of the current one. -/
def Level.next {level : Nat} (current : profiles.Level level) : profiles.Level (level + 1) where
  calculus := replayCell (profiles.cache level) (profiles.profile level) current.calculus
    current.fresh
  fresh := by
    apply fresh_replayPresentation (profiles.cache level) (profiles.profile level)
      (profiles.profile (level + 1)) current.calculus.1 current.fresh rfl
      (profiles.nonempty (level + 1)) (profiles.unreserved (level + 1))
    · intro member
      rcases current.names _ member with base | ⟨below, bound, same⟩
      · exact profiles.fresh (level + 1) base
      · have := profiles.injective same
        omega
    · intro same
      have := profiles.injective same
      omega
  names := by
    intro name member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    rcases nextEntry_cases (profiles.cache level) (profiles.profile level)
        (profiles.profile (level + 1)) current.calculus.1 current.fresh rfl entryMember with
      rfl | entryInTable
    · exact Or.inr ⟨level, Nat.lt_succ_self level, rfl⟩
    · rcases current.names entry.1 (replayTable_names_subset _ _
          (List.mem_map_of_mem (f := Prod.fst) entryInTable)) with base | ⟨below, bound, same⟩
      · exact Or.inl base
      · exact Or.inr ⟨below, Nat.lt_succ_of_lt bound, same⟩

/-- The base level: the calculus itself. -/
def base (childNames : ∀ rule ∈ definition.1.rules, ChildNamesFresh rule)
    (consistent : ArityConsistent
      (baseEntries definition.1 ++ newEntries (profiles.profile 0) definition.1)) :
    profiles.Level 0 where
  calculus := definition
  fresh :=
    { childNames
      consistent
      acceptsNonempty := profiles.nonempty 0
      acceptsFresh := profiles.fresh 0
      acceptsUnreserved := profiles.unreserved 0 }
  names := fun _ member => Or.inl member

variable (childNames : ∀ rule ∈ definition.1.rules, ChildNamesFresh rule)
  (consistent : ArityConsistent
    (baseEntries definition.1 ++ newEntries (profiles.profile 0) definition.1))

/-- **The bootstrap tower**: every level is a validated calculus, and level
`n + 1` is the replay presentation of level `n`. -/
def level : (n : Nat) → profiles.Level n
  | 0 => profiles.base childNames consistent
  | n + 1 => (level n).next

theorem level_zero : (profiles.level childNames consistent 0).calculus = definition := rfl

theorem level_rules (n : Nat) :
    (profiles.level childNames consistent (n + 1)).calculus.1.rules =
      replayRules (profiles.profile n) (profiles.level childNames consistent n).calculus.1.rules :=
  rfl

/-- **The tower at every level**: each level's checker accepts the replay
certificate of a certificate for its acceptance judgment exactly when the
level below accepts the certificate. -/
theorem tower_checkRaw (n : Nat) (goal : Pattern) (certificate : RawProof) :
    checkRaw (profiles.level childNames consistent (n + 1)).calculus
        (acceptsJudgment (profiles.profile n) goal
          (quoteProof (profiles.profile n) (profiles.level childNames consistent n).calculus.1
            certificate))
        (replayProof (profiles.profile n) (profiles.level childNames consistent n).calculus.1
          certificate) =
      checkRaw (profiles.level childNames consistent n).calculus goal certificate :=
  replayCell_checkRaw (profiles.cache n) (profiles.profile n)
    (profiles.level childNames consistent n).calculus
    (profiles.level childNames consistent n).fresh goal certificate

/-- The goal and certificate at level `n` that encode a check at level zero. -/
def encode : (n : Nat) → Pattern → RawProof → Pattern × RawProof
  | 0, goal, certificate => (goal, certificate)
  | n + 1, goal, certificate =>
      let lower := encode n goal certificate
      (acceptsJudgment (profiles.profile n) lower.1
          (quoteProof (profiles.profile n) (profiles.level childNames consistent n).calculus.1
            lower.2),
        replayProof (profiles.profile n) (profiles.level childNames consistent n).calculus.1
          lower.2)

/-- **Every level agrees with the base calculus** on the encoded checks. -/
theorem tower_agrees (goal : Pattern) (certificate : RawProof) :
    (n : Nat) →
      checkRaw (profiles.level childNames consistent n).calculus
          (profiles.encode childNames consistent n goal certificate).1
          (profiles.encode childNames consistent n goal certificate).2 =
        checkRaw definition goal certificate
  | 0 => rfl
  | n + 1 =>
      (profiles.tower_checkRaw childNames consistent n _ _).trans
        (tower_agrees goal certificate n)

end TowerProfiles


/-! ## A decidable sufficient condition for fresh child names -/

/-- A formal whose name does not begin with `#` is never named like a child
formal. -/
theorem childNamesFresh_of_noHash {rule : RuleSchema}
    (noHash : ∀ formal ∈ rule.metavariables, formal.1.toList.head? ≠ some '#') :
    ChildNamesFresh rule := by
  intro formal member index nameEq
  exact absurd (by rw [nameEq, childName, String.toList_append]; rfl) (noHash formal member)

/-! ## Controls -/

section Controls

/-- A modus ponens calculus over the constructors `A`, `B` and `I/2`, with
the judgment `P/1`: axioms `P(A)` and `P(I(A,B))`, and modus ponens. -/
def modusPonens (rules : List RuleSchema) : CalculusLanguageDef :=
  cacheDefinition { dataSort := "Formula", cacheName := "ModusPonens" }
    [("A", 0), ("B", 0), ("I", 2)] [{ head := "P", arity := 1 }] rules

def judgmentP (formula : Pattern) : Pattern := .apply "P" [formula]
def formulaA : Pattern := .apply "A" []
def formulaB : Pattern := .apply "B" []
def implication (antecedent consequent : Pattern) : Pattern :=
  .apply "I" [antecedent, consequent]

/-- Modus ponens with formals named `x` and `y`. -/
def modusPonensRule (first second : String) : RuleSchema where
  id := ⟨"m"⟩
  metavariables := [(first, 0), (second, 0)]
  premises := [judgmentP (.fvar first), judgmentP (implication (.fvar first) (.fvar second))]
  conclusion := judgmentP (.fvar second)

def axiomRule (id : String) (conclusion : Pattern) : RuleSchema where
  id := ⟨id⟩
  metavariables := []
  premises := []
  conclusion := judgmentP conclusion

def mpCalculus : CalculusLanguageDef :=
  modusPonens [axiomRule "a" formulaA, axiomRule "i" (implication formulaA formulaB),
    modusPonensRule "x" "y"]

theorem mpCalculus_valid : mpCalculus.isValid = true := by
  decide +kernel

def mpValidated : ValidatedCalculusLanguageDef := ⟨mpCalculus, mpCalculus_valid⟩

/-- The certificate of `P(B)`: modus ponens on the two axioms. -/
def mpCertificate : RawProof :=
  .node ⟨⟨"m"⟩, [formulaA, formulaB]⟩ [.node ⟨⟨"a"⟩, []⟩ [], .node ⟨⟨"i"⟩, []⟩ []]

theorem mp_accepts : checkRaw mpValidated (judgmentP formulaB) mpCertificate = true := by
  decide +kernel

theorem mp_rejects_wrong_goal :
    checkRaw mpValidated (judgmentP formulaA) mpCertificate = false := by
  decide +kernel

/-- Acceptance heads `@Accepts0`, `@Accepts1`, ...: they begin with `@`, which
no name of the calculus does. -/
def mpAccepts (level : Nat) : String := "@Accepts" ++ toString level

theorem mpAccepts_head (level : Nat) : (mpAccepts level).toList.head? = some '@' := by
  rw [mpAccepts, String.toList_append]
  rfl

theorem mpAccepts_ne {name : String} (other : name.toList.head? ≠ some '@') (level : Nat) :
    mpAccepts level ≠ name := fun same => other (same ▸ mpAccepts_head level)

theorem mpNames_head :
    ∀ name ∈ (baseEntries mpCalculus ++
        newEntries ⟨mpAccepts 0, "Certificate"⟩ mpCalculus).map Prod.fst,
      name.toList.head? ≠ some '@' := by
  decide +kernel

theorem reservedHeads_head :
    ∀ name ∈ [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead],
      name.toList.head? ≠ some '@' := by
  decide +kernel

/-- Tower profiles for the modus ponens calculus. -/
def mpProfiles : TowerProfiles mpValidated.1 where
  accepts := mpAccepts
  certificate := "Certificate"
  cache := fun level => { dataSort := "ReplayData", cacheName := "Replay" ++ toString level }
  injective := fun first second same =>
    Nat.repr_injective ((String.append_right_inj "@Accepts").mp same)
  nonempty := fun level empty => by
    have := mpAccepts_head level
    rw [empty] at this
    exact absurd this (by decide)
  unreserved := fun level member =>
    mpAccepts_ne (reservedHeads_head _ member) level rfl
  fresh := fun level member => mpAccepts_ne (mpNames_head _ member) level rfl

theorem mp_childNames : ∀ rule ∈ mpValidated.1.rules, ChildNamesFresh rule := by
  intro rule member
  apply childNamesFresh_of_noHash
  revert rule
  decide +kernel

theorem mp_consistent : ArityConsistent
    (baseEntries mpValidated.1 ++ newEntries (mpProfiles.profile 0) mpValidated.1) := by
  unfold ArityConsistent
  decide +kernel

/-- The bootstrap tower over the modus ponens calculus, at every level. -/
def mpTower (level : Nat) : mpProfiles.Level level :=
  mpProfiles.level mp_childNames mp_consistent level

/-- **Positive control.**  At every level of the tower, the encoded check of
`P(B)` with the modus ponens certificate is accepted. -/
theorem mpTower_accepts (level : Nat) :
    checkRaw (mpTower level).calculus
        (mpProfiles.encode mp_childNames mp_consistent level (judgmentP formulaB)
          mpCertificate).1
        (mpProfiles.encode mp_childNames mp_consistent level (judgmentP formulaB)
          mpCertificate).2 = true :=
  (mpProfiles.tower_agrees mp_childNames mp_consistent _ _ level).trans mp_accepts

/-- **Negative control.**  At every level, the encoded check of the wrong goal
`P(A)` is rejected. -/
theorem mpTower_rejects_wrong_goal (level : Nat) :
    checkRaw (mpTower level).calculus
        (mpProfiles.encode mp_childNames mp_consistent level (judgmentP formulaA)
          mpCertificate).1
        (mpProfiles.encode mp_childNames mp_consistent level (judgmentP formulaA)
          mpCertificate).2 = false :=
  (mpProfiles.tower_agrees mp_childNames mp_consistent _ _ level).trans mp_rejects_wrong_goal

/-- The first level is a validated calculus distinct from the base: its only
judgment is the acceptance head of level zero. -/
theorem mpTower_one_judgments :
    (mpTower 1).calculus.1.judgments = [{ head := mpAccepts 0, arity := 2 }] := rfl

/-- **Negative control: child-name collision.**  Modus ponens with formals
named `#2` and `y` is a valid calculus, but its first child formal is also
named `#2`, so its replay presentation is invalid. -/
def collidingCalculus : CalculusLanguageDef :=
  modusPonens [axiomRule "a" formulaA, axiomRule "i" (implication formulaA formulaB),
    modusPonensRule "#2" "y"]

theorem collidingCalculus_valid : collidingCalculus.isValid = true := by
  decide +kernel

theorem collidingCalculus_not_fresh :
    ¬ ∀ rule ∈ collidingCalculus.rules, ChildNamesFresh rule := by
  intro fresh
  have bound := fresh (modusPonensRule "#2" "y") (by decide) ("#2", 0)
    List.mem_cons_self 2 rfl
  exact absurd bound (by decide)

theorem collidingCalculus_presentation_invalid :
    (replayPresentation { dataSort := "ReplayData", cacheName := "Replay" }
      ⟨mpAccepts 0, "Certificate"⟩ collidingCalculus).isValid = false := by
  decide +kernel

/-- **Negative control: atom clash.**  The same calculus with the implication
axiom identified as `I`, the name of the binary constructor, is valid; the
rule's atom would be a nullary `I`, so the arities are inconsistent and the
replay presentation is invalid. -/
def atomClashCalculus : CalculusLanguageDef :=
  modusPonens [axiomRule "a" formulaA, axiomRule "I" (implication formulaA formulaB),
    modusPonensRule "x" "y"]

theorem atomClashCalculus_valid : atomClashCalculus.isValid = true := by
  decide +kernel

theorem atomClashCalculus_inconsistent :
    ¬ ArityConsistent (baseEntries atomClashCalculus ++
      newEntries ⟨mpAccepts 0, "Certificate"⟩ atomClashCalculus) := by
  intro consistent
  have := consistent ("I", 2) (by decide +kernel) ("I", 0) (by decide +kernel) rfl
  exact absurd this (by decide)

theorem atomClashCalculus_presentation_invalid :
    (replayPresentation { dataSort := "ReplayData", cacheName := "Replay" }
      ⟨mpAccepts 0, "Certificate"⟩ atomClashCalculus).isValid = false := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation
