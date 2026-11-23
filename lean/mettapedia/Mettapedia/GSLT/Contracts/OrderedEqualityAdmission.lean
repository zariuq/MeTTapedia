import Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
import Mettapedia.GSLT.Contracts.EquationEpochs
import Mettapedia.GSLT.LanguageDef.DefinitionalNormalForms
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction

/-!
# Reusing ordered query plans when a theory adds equations

The occurrence list is captured at one cut. The comparison may acquire new
identifications while the rows and query remain fixed. Count, first-occurrence
and presence readouts then admit different reuse tests. These tests concern
ground equality on keys. Body evaluation, general unification and concurrent
publication have separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.OrderedEqualityAdmission

open CanonicalSuccessorClasses (NormalForms)
open EquationEpochs (Extends)

universe u

section OrderedReads

variable {Row : Type u} (oldMatch currentMatch : Row → Bool)

/-- Occurrences newly eligible under the current theory, in source order. -/
def newMatches (rows : List Row) : List Row :=
  rows.filter (fun row => currentMatch row && !oldMatch row)

theorem count_adds_new (rows : List Row)
    (grows : ∀ row, oldMatch row = true → currentMatch row = true) :
    (rows.filter currentMatch).length =
      (rows.filter oldMatch).length + (newMatches oldMatch currentMatch rows).length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    unfold newMatches at ih
    cases old : oldMatch row with
    | true => simp [newMatches, old, grows row old, ih, Nat.succ_add]
    | false =>
      cases current : currentMatch row <;> simp [newMatches, old, current, ih, Nat.add_assoc]

theorem count_reuse_iff (rows : List Row)
    (grows : ∀ row, oldMatch row = true → currentMatch row = true) :
    (rows.filter oldMatch).length = (rows.filter currentMatch).length ↔
      (newMatches oldMatch currentMatch rows).isEmpty = true := by
  rw [count_adds_new oldMatch currentMatch rows grows, List.isEmpty_iff]
  constructor
  · intro same
    exact List.length_eq_zero_iff.mp (by omega)
  · intro noNew
    simp [noNew]

theorem ordered_reuse_iff (rows : List Row)
    (grows : ∀ row, oldMatch row = true → currentMatch row = true) :
    rows.filter oldMatch = rows.filter currentMatch ↔
      (newMatches oldMatch currentMatch rows).isEmpty = true := by
  constructor
  · intro same
    exact (count_reuse_iff oldMatch currentMatch rows grows).mp (congrArg List.length same)
  · intro none
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      cases old : oldMatch row with
      | true =>
        have current := grows row old
        have tail : (newMatches oldMatch currentMatch rest).isEmpty = true := by
          simpa [newMatches, old, current] using none
        simp [old, current, ih tail]
      | false =>
        cases current : currentMatch row with
        | true => simp [newMatches, old, current] at none
        | false =>
          have tail : (newMatches oldMatch currentMatch rest).isEmpty = true := by
            simpa [newMatches, old, current] using none
          simp [old, current, ih tail]

/-- A previous witness remains first unless an earlier row becomes eligible. -/
def firstReusable : List Row → Bool
  | [] => true
  | row :: rest =>
    if oldMatch row then true
    else if currentMatch row then false
    else firstReusable rest

theorem first_reuse_iff (rows : List Row)
    (grows : ∀ row, oldMatch row = true → currentMatch row = true) :
    rows.find? oldMatch = rows.find? currentMatch ↔
      firstReusable oldMatch currentMatch rows = true := by
  induction rows with
  | nil => simp [firstReusable]
  | cons row rest ih =>
    cases old : oldMatch row with
    | true => simp [firstReusable, old, grows row old]
    | false =>
      cases current : currentMatch row with
      | false => simpa [firstReusable, old, current] using ih
      | true =>
        simp only [List.find?_cons, old, current, Bool.false_eq_true, ↓reduceIte,
          firstReusable]
        constructor
        · intro same
          have wasMatch := List.find?_some same
          simp [old] at wasMatch
        · intro impossible
          cases impossible

/-- A previously established presence survives every enlargement of equality
on the same rows. Previously observed absence needs a current absence test. -/
theorem presence_reuse_iff (rows : List Row)
    (grows : ∀ row, oldMatch row = true → currentMatch row = true) :
    rows.any oldMatch = rows.any currentMatch ↔
      (rows.any oldMatch || !rows.any currentMatch) = true := by
  cases old : rows.any oldMatch with
  | false => cases current : rows.any currentMatch <;> simp
  | true =>
    obtain ⟨row, member, matched⟩ := List.any_eq_true.mp old
    have current := List.any_eq_true.mpr ⟨row, member, grows row matched⟩
    simp [current]

end OrderedReads

section Equations

variable {Term Row : Type u} {oldTheory currentTheory : Setoid Term}

/-- The comparison uses a canonical key certified against the theory. The
row itself, including its identity and position, remains available. -/
def keyMatches (forms : NormalForms currentTheory) [DecidableEq forms.Key]
    (label : Row → Term) (query : Term) (row : Row) : Bool :=
  decide (forms.key (label row) = forms.key query)

theorem matches_iff (forms : NormalForms currentTheory) [DecidableEq forms.Key]
    (label : Row → Term) (query : Term) (row : Row) :
    keyMatches forms label query row = true ↔ currentTheory.r (label row) query := by
  simp only [keyMatches, decide_eq_true_eq, forms.key_eq_iff]

theorem match_grows (old : NormalForms oldTheory) (current : NormalForms currentTheory)
    [DecidableEq old.Key] [DecidableEq current.Key]
    (growth : Extends oldTheory currentTheory) (label : Row → Term) (query : Term) (row : Row)
    (matched : keyMatches old label query row = true) :
    keyMatches current label query row = true :=
  (matches_iff current label query row).mpr (growth ((matches_iff old label query row).mp matched))

end Equations

section ModuleExample

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations

private def cold : Pattern := .apply "Cold" []
private def warm : Pattern := .apply "Warm" []
private def probe (key : Pattern) : Pattern := .apply "Probe" [key]
private def hit : Pattern := .apply "Hit" []

private def base := engineBasePremises RelationEnv.empty

def probeRule : RewriteRule :=
  { name := "ProbeCold", typeContext := [], premises := [], left := probe cold, right := hit }

def coldEquation : Equation :=
  { name := "ColdAlias", typeContext := [], premises := [], left := cold, right := warm }

def probeLanguage : LanguageDef :=
  { name := "Example", types := ["Key", "Answer"], equations := [], rewrites := [probeRule]
    terms := [
      { label := "Cold", category := "Key", params := [], syntaxPattern := [.terminal "cold"] },
      { label := "Warm", category := "Key", params := [], syntaxPattern := [.terminal "warm"] },
      { label := "Probe", category := "Answer", params := [.simple "value" (.base "Key")],
        syntaxPattern := [.terminal "probe", .nonTerminal "value"] },
      { label := "Hit", category := "Answer", params := [], syntaxPattern := [.terminal "hit"] }] }

def withAlias : LanguageDef := { probeLanguage with equations := [coldEquation] }

private def aliasRow : Row := ⟨"Cold", [], warm⟩

private theorem aliasAcyclic : Acyclic [aliasRow] := by
  constructor
  · intro row member
    have same : row = aliasRow := by simpa using member
    subst row
    exact ⟨List.nodup_nil, .constructor .nil⟩
  · simp
  · intro row member
    have same : row = aliasRow := by simpa using member
    subst row
    exact (checkAvoids_iff aliasRow.head aliasRow.body).mp (by decide +kernel)
  · simp

private theorem aliasPresented : Presents withAlias [aliasRow] :=
  presents_of_forall₂ (.cons ⟨rfl, rfl, rfl⟩ .nil)

private def rawForms : NormalForms (equationSetoid base probeLanguage) where
  normal := id
  sound state := .refl state
  same same := (equationEquiv_iff_eq_of_no_generators (by rfl) _ _).mp same

private def aliasForms : NormalForms (equationSetoid base withAlias) where
  normal := expand [aliasRow]
  sound state := Relation.EqvGen.symm _ _ (equationEquiv_expand (base := base) [aliasRow]
    (fun row member => ⟨aliasAcyclic.wellFormed row member, aliasPresented.authored row member⟩) state)
  same same := (equationEquiv_iff_expand_eq (base := base) aliasAcyclic aliasPresented
    (by rfl) (by rfl) (by rfl) _ _).mp same

private theorem aliasExtends :
    Extends (equationSetoid base probeLanguage) (equationSetoid base withAlias) := by
  intro left right same
  have raw := rawForms.same same
  change left = right at raw
  subst right
  exact Relation.EqvGen.refl left

/-- The new theory exposes the old authored redex at a new representative. -/
theorem warm_modulo_step : StepModuloEquations base withAlias (probe warm) hit := by
  refine ⟨probe cold, hit, aliasForms.key_eq_iff.mp (by decide +kernel), ?_, .refl _⟩
  apply (step_iff_mem_rootReducts base withAlias (by decide +kernel) _ _).mpr
  decide +kernel

/-- The structural runner alone returns an empty frontier on the new input. -/
theorem raw_warm_frontier : rootReducts withAlias (probe warm) = [] := by decide +kernel

/-- Even an exact canonicalizer can lose a redex when used with raw rule
matching at its chosen representative. -/
theorem normalize_only_misses_redex :
    rootReducts withAlias (aliasForms.normal (probe warm)) = [] ∧
      StepModuloEquations base withAlias (probe warm) hit :=
  ⟨by decide +kernel, warm_modulo_step⟩

private def oldOnCold : Nat × Pattern → Bool := keyMatches rawForms Prod.snd cold
private def currentOnCold : Nat × Pattern → Bool := keyMatches aliasForms Prod.snd cold

private theorem onCold_grows (row : Nat × Pattern) (ready : oldOnCold row = true) :
    currentOnCold row = true :=
  match_grows rawForms aliasForms aliasExtends Prod.snd cold row ready

/-- The same added equation can invalidate a count while preserving the
first occurrence. A repeated Cold retains its own occurrence. -/
theorem keeps_first_changes_count :
    let rows := [(0, cold), (1, warm), (2, cold)]
    rows.find? oldOnCold = rows.find? currentOnCold ∧
      (rows.filter oldOnCold).length = 2 ∧ (rows.filter currentOnCold).length = 3 := by
  dsimp only
  exact ⟨(first_reuse_iff _ _ _ onCold_grows).mpr (by decide +kernel), by decide +kernel⟩

theorem earlier_match_changes_first :
    let rows := [(0, warm), (1, cold)]
    rows.find? oldOnCold ≠ rows.find? currentOnCold ∧
      rows.any oldOnCold = rows.any currentOnCold := by
  decide +kernel

theorem new_presence_invalidates_absence :
    let rows := [(0, warm)]
    rows.any oldOnCold = false ∧ rows.any currentOnCold = true := by
  decide +kernel

/-- A plan selected for first occurrence can stay valid even when the plan
selected for a count must be refreshed. -/
theorem scoped_admission_decisions :
    let rows := [(0, cold), (1, warm), (2, cold)]
    firstReusable oldOnCold currentOnCold rows = true ∧
      (newMatches oldOnCold currentOnCold rows).isEmpty = false := by
  decide +kernel

end ModuleExample

#print axioms count_reuse_iff
#print axioms ordered_reuse_iff
#print axioms first_reuse_iff
#print axioms presence_reuse_iff
#print axioms match_grows
#print axioms normalize_only_misses_redex
#print axioms keeps_first_changes_count

end Mettapedia.GSLT.Contracts.OrderedEqualityAdmission
