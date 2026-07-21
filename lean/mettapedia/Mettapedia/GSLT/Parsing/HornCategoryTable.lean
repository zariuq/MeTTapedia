import Mettapedia.GSLT.Parsing.HornSpecialization

/-!
# Constructive category tables for Horn parser compilation

The executable compiler discovers a finite list of ground grammar terms from
its root worklist.  This module assigns those terms fresh parser categories and
proves that the resulting table passes the same fail-closed check consumed by
Horn specialization.  Category names are an implementation representation;
their unary encoding makes injectivity structural and independent of a guest
language.
-/

namespace Mettapedia.GSLT.Parsing.HornCategoryTable

open HornCertificate HornSpecialization

def categoryName (index : Nat) : CompilerCorrespondence.Category :=
  String.ofList (List.replicate (index + 1) 'g')

theorem categoryName_injective : Function.Injective categoryName := by
  intro left right equal
  have lists := String.ofList_injective equal
  have lengths := congrArg List.length lists
  simp at lengths
  omega

def categoryLabels (grammars : List Term) :
    List CompilerCorrespondence.Category :=
  (List.range grammars.length).map categoryName

theorem categoryLabels_length (grammars : List Term) :
    (categoryLabels grammars).length = grammars.length := by
  simp [categoryLabels]

theorem categoryLabels_nodup (grammars : List Term) :
    (categoryLabels grammars).Nodup := by
  change List.Pairwise (fun left right => left ≠ right)
    (List.map categoryName (List.range grammars.length))
  rw [List.pairwise_map]
  exact List.nodup_range.imp fun unequal equal =>
    unequal (categoryName_injective equal)

def makeCategoryTable (grammars : List Term) : CategoryTable :=
  grammars.zip (categoryLabels grammars)

/-- Reject duplicate or nonground discovered grammar terms before assigning
categories.  Nothing is silently discarded or deduplicated. -/
def buildCategoryTable (grammars : List Term) : Option CategoryTable :=
  if grammars.Nodup ∧
      ∀ grammar ∈ grammars, termVariables grammar = [] then
    some (makeCategoryTable grammars)
  else none

private theorem fst_mem_of_mem_zip {α β : Type} {entry : α × β}
    {left : List α} {right : List β} (member : entry ∈ left.zip right) :
    entry.1 ∈ left := by
  induction left generalizing right with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp at member
      | cons rightHead rightTail =>
          simp only [List.zip_cons_cons, List.mem_cons] at member
          rcases member with equal | tailMember
          · subst entry
            simp
          · exact List.mem_cons_of_mem head (inductionHypothesis tailMember)

private theorem exists_pair_of_mem_left {α β : Type} {value : α}
    {left : List α} {right : List β}
    (sameLength : left.length = right.length) (member : value ∈ left) :
    ∃ paired, (value, paired) ∈ left.zip right := by
  induction left generalizing right with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          have tailLength : tail.length = rightTail.length := by
            simpa using sameLength
          simp only [List.mem_cons] at member
          rcases member with equal | tailMember
          · subst value
            exact ⟨rightHead, by simp⟩
          · obtain ⟨paired, pairedMember⟩ :=
              inductionHypothesis tailLength tailMember
            exact ⟨paired, List.mem_cons_of_mem _ pairedMember⟩

theorem buildCategoryTable_valid {grammars : List Term}
    {table : CategoryTable}
    (accepted : buildCategoryTable grammars = some table) :
    categoryTableValid table = true := by
  simp only [buildCategoryTable] at accepted
  split at accepted
  next admitted =>
    injection accepted with tableEq
    subst table
    unfold categoryTableValid makeCategoryTable
    rw [List.unzip_zip (categoryLabels_length grammars).symm]
    simp only [decide_eq_true_eq]
    exact ⟨admitted.1, categoryLabels_nodup grammars, by
      intro entry member
      exact admitted.2 entry.1 (fst_mem_of_mem_zip member)⟩
  next rejected => simp at accepted

theorem lookupCategory_sound {grammar : Term}
    {category : CompilerCorrespondence.Category} {table : CategoryTable}
    (accepted : lookupCategory grammar table = some category) :
    (grammar, category) ∈ table := by
  induction table with
  | nil => simp [lookupCategory] at accepted
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨candidate, candidateCategory⟩
      by_cases equal : grammar = candidate
      · simp [lookupCategory, equal] at accepted
        subst candidate
        subst candidateCategory
        simp
      · simp only [lookupCategory, equal, ↓reduceIte] at accepted
        exact List.mem_cons_of_mem _ (inductionHypothesis accepted)

theorem lookupCategory_complete_of_mem
    {grammar : Term} {category : CompilerCorrespondence.Category}
    {table : CategoryTable}
    (keysUnique : table.unzip.1.Nodup)
    (member : (grammar, category) ∈ table) :
    lookupCategory grammar table = some category := by
  induction table with
  | nil => simp at member
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨candidate, candidateCategory⟩
      simp only [List.unzip_cons] at keysUnique
      have uniqueParts := List.pairwise_cons.mp keysUnique
      simp only [List.mem_cons] at member
      rcases member with equal | tailMember
      · injection equal with grammarEq categoryEq
        subst candidate
        subst candidateCategory
        simp [lookupCategory]
      · have tailUnique : tail.unzip.1.Nodup := by
          exact uniqueParts.2
        have different : grammar ≠ candidate := by
          intro equal
          subst grammar
          have candidateInTail : candidate ∈ tail.unzip.1 := by
            have mapped : candidate ∈ tail.map Prod.fst :=
              List.mem_map.mpr ⟨(candidate, category), tailMember, rfl⟩
            simpa using mapped
          exact (uniqueParts.1 candidate candidateInTail) rfl
        simp only [lookupCategory, different, ↓reduceIte]
        exact inductionHypothesis tailUnique tailMember

theorem makeCategoryTable_covers {grammars : List Term} {grammar : Term}
    (member : grammar ∈ grammars) :
    ∃ category, (grammar, category) ∈ makeCategoryTable grammars := by
  exact exists_pair_of_mem_left (categoryLabels_length grammars).symm member

theorem buildCategoryTable_covers {grammars : List Term}
    {table : CategoryTable} (accepted : buildCategoryTable grammars = some table)
    {grammar : Term} (member : grammar ∈ grammars) :
    ∃ category, lookupCategory grammar table = some category := by
  have valid := buildCategoryTable_valid accepted
  simp only [categoryTableValid, decide_eq_true_eq] at valid
  simp only [buildCategoryTable] at accepted
  split at accepted
  next admitted =>
    injection accepted with tableEq
    subst table
    obtain ⟨category, pairMember⟩ := makeCategoryTable_covers member
    exact ⟨category,
      lookupCategory_complete_of_mem valid.1 pairMember⟩
  next rejected => simp at accepted

theorem buildCategoryTable_lookup_source {grammars : List Term}
    {table : CategoryTable} (accepted : buildCategoryTable grammars = some table)
    {grammar : Term} {category : CompilerCorrespondence.Category}
    (found : lookupCategory grammar table = some category) :
    grammar ∈ grammars := by
  have pairMember := lookupCategory_sound found
  simp only [buildCategoryTable] at accepted
  split at accepted
  next admitted =>
    injection accepted with tableEq
    subst table
    exact fst_mem_of_mem_zip pairMember
  next rejected => simp at accepted

theorem buildCategoryTable_lookup_iff {grammars : List Term}
    {table : CategoryTable} (accepted : buildCategoryTable grammars = some table)
    (grammar : Term) :
    (∃ category, lookupCategory grammar table = some category) ↔
      grammar ∈ grammars := by
  constructor
  · rintro ⟨category, found⟩
    exact buildCategoryTable_lookup_source accepted found
  · exact buildCategoryTable_covers accepted

/-! ## Executable positive and negative controls -/

def grammarA : Term := .app "char" (Terms.ofList [.integer 97])
def grammarB : Term := .app "char" (Terms.ofList [.integer 98])

theorem twoGroundGrammars_are_admitted :
    (buildCategoryTable [grammarA, grammarB]).isSome = true := by
  decide

theorem duplicateGrammar_is_rejected :
    buildCategoryTable [grammarA, grammarA] = none := by
  decide

theorem symbolicGrammar_is_rejected :
    buildCategoryTable [.var 0] = none := by
  decide

theorem twoGroundGrammar_table_is_valid :
    categoryTableValid (makeCategoryTable [grammarA, grammarB]) = true := by
  exact buildCategoryTable_valid (grammars := [grammarA, grammarB]) (by decide)

theorem twoGroundGrammar_table_covers_second :
    ∃ category,
      lookupCategory grammarB (makeCategoryTable [grammarA, grammarB]) =
        some category := by
  exact buildCategoryTable_covers
    (grammars := [grammarA, grammarB]) (table := makeCategoryTable [grammarA, grammarB])
    (by decide) (by simp)

end Mettapedia.GSLT.Parsing.HornCategoryTable
