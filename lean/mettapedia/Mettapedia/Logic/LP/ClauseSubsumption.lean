import Mettapedia.Logic.LP.DirectionalMatching
import Mettapedia.Logic.LP.Matching
import Mettapedia.Logic.LP.FirstOrderBridge

/-!
# Checked clause-subsumption witnesses

A literal is a polarity and an existing LP atom. Clauses are lists of literal
occurrences. Set subsumption permits one target occurrence to cover several
source literals; occurrence subsumption requires distinct selected indices.
Both contracts use one substitution and protect all variables of the target
clause, including variables in literals not selected by this witness.

Equality predicates are treated syntactically like any other predicate here;
this is not matching modulo equality or a superposition calculus. The semantic
implication theorem uses arbitrary first-order structures via FirstOrderBridge.
-/

namespace Mettapedia.Logic.LP.ClauseSubsumption

universe u v w
variable {σ : LPSignature.{u, u, v, u}}

abbrev SignedAtom (σ : LPSignature) := Bool × Atom σ
abbrev Clause (σ : LPSignature) := List (SignedAtom σ)

def apply (substitution : Subst σ) (literal : SignedAtom σ) : SignedAtom σ :=
  (literal.1, substitution.applyAtom literal.2)

def clauseVars [DecidableEq σ.vars] : Clause σ → Finset σ.vars
  | [] => ∅
  | literal :: rest => literal.2.freeVars ∪ clauseVars rest

@[simp] theorem mem_clauseVars [DecidableEq σ.vars] (clause : Clause σ) (x : σ.vars) :
    x ∈ clauseVars clause ↔ ∃ literal ∈ clause, x ∈ literal.2.freeVars := by
  induction clause with
  | nil => simp [clauseVars]
  | cons literal rest ih => simp [clauseVars, ih]

/-- Constructor checks produce equations between corresponding arguments. -/
def literalConstraints [DecidableEq σ.relationSymbols]
    (left right : SignedAtom σ) : Option (List (Term σ × Term σ)) :=
  if left.1 = right.1 then
    if h : left.2.symbol = right.2.symbol then
      some (finToList (fun i => (left.2.args i, (h ▸ right.2.args) i)))
    else none
  else none

def constraints [DecidableEq σ.relationSymbols] :
    Clause σ → Clause σ → Option (List (Term σ × Term σ))
  | [], [] => some []
  | left :: rest, right :: tail => do
    let first ← literalConstraints left right
    let later ← constraints rest tail
    return first ++ later
  | _, _ => none

def selected (target : Clause σ) (indices : List (Fin target.length)) : Clause σ :=
  indices.map target.get

theorem selected_mem (target : Clause σ) (indices : List (Fin target.length))
    (literal : SignedAtom σ) (member : literal ∈ selected target indices) :
    literal ∈ target := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact List.get_mem target index

/-- The caller supplies candidate occurrence indices. False selects set
    subsumption; true also checks occurrence consumption. -/
def check [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (indices : List (Fin target.length)) :
    Option (Subst σ) := do
  if consume && !decide indices.Nodup then none else do
    let equations ← constraints source (selected target indices)
    RigidUnification.solve (fun x => x ∈ clauseVars target) equations

def Covers (substitution : Subst σ) (source target : Clause σ) : Prop :=
  ∀ literal ∈ source, apply substitution literal ∈ target

theorem literalConstraints_sound [DecidableEq σ.relationSymbols]
    (left right : SignedAtom σ) (equations : List (Term σ × Term σ))
    (accepted : literalConstraints left right = some equations) (answer : Subst σ)
    (solves : Unifies answer equations) : apply answer left = apply answer right := by
  rcases left with ⟨polarity, ⟨head, args⟩⟩
  rcases right with ⟨otherPolarity, ⟨otherHead, targets⟩⟩
  unfold literalConstraints at accepted
  split at accepted
  next sign =>
    dsimp only at sign
    subst otherPolarity
    split at accepted
    next same =>
      dsimp only at same
      subst otherHead
      simp only [Option.some.injEq] at accepted
      subst equations
      change (polarity, Atom.mk head (fun i => answer.applyTerm (args i))) =
        (polarity, Atom.mk head (fun i => answer.applyTerm (targets i)))
      congr 2
      funext i
      exact solves _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    next => simp at accepted
  next => simp at accepted

theorem constraints_sound [DecidableEq σ.relationSymbols]
    (source target : Clause σ) (equations : List (Term σ × Term σ))
    (accepted : constraints source target = some equations) (answer : Subst σ)
    (solves : Unifies answer equations) :
    source.map (apply answer) = target.map (apply answer) := by
  induction source generalizing target equations with
  | nil =>
    cases target with
    | nil => rfl
    | cons _ _ => simp [constraints] at accepted
  | cons literal rest ih =>
    cases target with
    | nil => simp [constraints] at accepted
    | cons other tail =>
      cases hc : literalConstraints literal other with
      | none => simp [constraints, hc] at accepted
      | some first =>
        cases ht : constraints rest tail with
        | none => simp [constraints, hc, ht] at accepted
        | some later =>
          have equal : first ++ later = equations := by
            simpa [constraints, hc, ht] using accepted
          subst equations
          have head := literalConstraints_sound literal other first hc answer
            (fun pair member => solves pair (List.mem_append_left _ member))
          have tailEq := ih tail later ht (fun pair member =>
            solves pair (List.mem_append_right _ member))
          simp only [List.map_cons, head, tailEq]

theorem fixes_literal [DecidableEq σ.vars] (target : Clause σ) (answer : Subst σ)
    (fixed : RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer)
    (literal : SignedAtom σ) (member : literal ∈ target) : apply answer literal = literal := by
  rcases literal with ⟨polarity, ⟨head, args⟩⟩
  change (polarity, Atom.mk head (fun i => answer.applyTerm (args i))) =
    (polarity, Atom.mk head args)
  congr 2
  funext i
  apply Subst.applyTerm_eq_self
  intro x present
  apply fixed x
  apply (mem_clauseVars target x).mpr
  refine ⟨(polarity, Atom.mk head args), member, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, present⟩

/-- A checked candidate is a complete clause witness, not independent
    successes for its literals. The protected target remains unchanged. -/
theorem check_sound [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (indices : List (Fin target.length))
    (answer : Subst σ) (accepted : check consume source target indices = some answer) :
    RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer ∧
      Covers answer source target ∧ (consume = true → indices.Nodup) := by
  unfold check at accepted
  split at accepted
  next => simp at accepted
  next admissible =>
    cases hc : constraints source (selected target indices) with
    | none => simp [hc] at accepted
    | some equations =>
      simp only [hc] at accepted
      obtain ⟨fixed, solves⟩ := RigidUnification.solve_sound _ equations answer accepted
      refine ⟨fixed, ?_, ?_⟩
      · intro literal member
        have same := constraints_sound source (selected target indices) equations hc answer solves
        have selectedImage : apply answer literal ∈ (selected target indices).map (apply answer) :=
          same ▸ List.mem_map.mpr ⟨literal, member, rfl⟩
        obtain ⟨other, selectedMember, equal⟩ := List.mem_map.mp selectedImage
        have targetMember := selected_mem target indices other selectedMember
        rw [fixes_literal target answer fixed other targetMember] at equal
        exact equal ▸ targetMember
      · intro consumes
        simpa [consumes] using admissible

theorem literalConstraints_complete [DecidableEq σ.relationSymbols]
    (left right : SignedAtom σ) (answer : Subst σ)
    (same : apply answer left = apply answer right) :
    ∃ equations, literalConstraints left right = some equations ∧ Unifies answer equations := by
  rcases left with ⟨polarity, ⟨head, args⟩⟩
  rcases right with ⟨otherPolarity, ⟨otherHead, targets⟩⟩
  simp only [apply, Subst.applyAtom, Prod.mk.injEq, Atom.mk.injEq] at same
  obtain ⟨rfl, rfl, children⟩ := same
  simp only [heq_eq_eq] at children
  refine ⟨finToList (fun i => (args i, targets i)), by simp [literalConstraints], ?_⟩
  intro pair member
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  exact congrFun children i

theorem constraints_complete [DecidableEq σ.relationSymbols]
    (source target : Clause σ) (answer : Subst σ)
    (same : source.map (apply answer) = target.map (apply answer)) :
    ∃ equations, constraints source target = some equations ∧ Unifies answer equations := by
  induction source generalizing target with
  | nil =>
    cases target with
    | nil => exact ⟨[], by simp [constraints], by simp [Unifies]⟩
    | cons _ _ => simp at same
  | cons literal rest ih =>
    cases target with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨first, head, solvedHead⟩ := literalConstraints_complete literal other answer same.1
      obtain ⟨later, body, solvedBody⟩ := ih tail same.2
      refine ⟨first ++ later, by simp [constraints, head, body], ?_⟩
      intro pair member
      rcases List.mem_append.mp member with member | member
      · exact solvedHead pair member
      · exact solvedBody pair member

/-- A valid occurrence alignment is accepted. The unifier may choose another
    most-general representative, whose usability is established by soundness. -/
theorem check_complete [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (indices : List (Fin target.length))
    (answer : Subst σ)
    (fixed : RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer)
    (aligned : source.map (apply answer) = selected target indices)
    (distinct : consume = true → indices.Nodup) :
    ∃ result, check consume source target indices = some result := by
  have targetFixed : (selected target indices).map (apply answer) = selected target indices := by
    conv_rhs => rw [← List.map_id (selected target indices)]
    apply List.map_congr_left
    intro literal member
    exact fixes_literal target answer fixed literal (selected_mem target indices literal member)
  obtain ⟨equations, collected, solves⟩ := constraints_complete source (selected target indices)
    answer (aligned.trans targetFixed.symm)
  obtain ⟨result, accepted⟩ := RigidUnification.solve_complete _ equations ⟨answer, fixed, solves⟩
  refine ⟨result, ?_⟩
  have guard : (consume && !decide indices.Nodup) = false := by
    cases h : consume <;> simp [distinct, h]
  simp [check, guard, collected, accepted]

/-- All finite occurrence selections, retaining authored order. Repeated
    indices are intentional for set subsumption. -/
def selections (targetLength : Nat) : Nat → List (List (Fin targetLength))
  | 0 => [[]]
  | count + 1 => (List.finRange targetLength).flatMap fun index =>
      (selections targetLength count).map (index :: ·)

theorem mem_selections {targetLength count : Nat} (indices : List (Fin targetLength)) :
    indices ∈ selections targetLength count ↔ indices.length = count := by
  induction count generalizing indices with
  | zero => simp [selections]
  | succ count ih =>
    cases indices with
    | nil => simp [selections]
    | cons index rest => simp [selections, ih]

def searchCandidates [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) :
    List (List (Fin target.length)) → Option (List (Fin target.length) × Subst σ)
  | [] => none
  | indices :: rest => match check consume source target indices with
    | some answer => some (indices, answer)
    | none => searchCandidates consume source target rest

def search [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) :
    Option (List (Fin target.length) × Subst σ) :=
  searchCandidates consume source target (selections target.length source.length)

theorem searchCandidates_sound [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (candidates : List (List (Fin target.length)))
    (indices : List (Fin target.length)) (answer : Subst σ)
    (accepted : searchCandidates consume source target candidates = some (indices, answer)) :
    check consume source target indices = some answer := by
  induction candidates with
  | nil => simp [searchCandidates] at accepted
  | cons candidate rest ih =>
    cases hc : check consume source target candidate with
    | none => exact ih (by simpa [searchCandidates, hc] using accepted)
    | some result =>
      have same : candidate = indices ∧ result = answer := by
        simpa [searchCandidates, hc] using accepted
      simpa [same.1, same.2] using hc

theorem searchCandidates_complete [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (candidates : List (List (Fin target.length)))
    (indices : List (Fin target.length)) (answer : Subst σ)
    (member : indices ∈ candidates) (accepted : check consume source target indices = some answer) :
    ∃ result, searchCandidates consume source target candidates = some result := by
  induction candidates with
  | nil => simp at member
  | cons candidate rest ih =>
    cases hc : check consume source target candidate with
    | some result => exact ⟨(candidate, result), by simp [searchCandidates, hc]⟩
    | none =>
      have inRest : indices ∈ rest := by
        rcases List.mem_cons.mp member with equal | member
        · subst candidate; simp [hc] at accepted
        · exact member
      obtain ⟨result, found⟩ := ih inRest
      exact ⟨result, by simpa [searchCandidates, hc] using found⟩

/-- Set coverage supplies a target occurrence for every source literal;
    no ordering constraint or target-literal consumption is smuggled in. -/
theorem alignment_of_covers (source target : Clause σ) (answer : Subst σ)
    (covers : Covers answer source target) :
    ∃ indices : List (Fin target.length), source.map (apply answer) = selected target indices := by
  induction source with
  | nil => exact ⟨[], rfl⟩
  | cons literal rest ih =>
    obtain ⟨index, equal⟩ := List.mem_iff_get.mp (covers literal (by simp))
    obtain ⟨indices, aligned⟩ := ih (fun l hl => covers l (List.mem_cons_of_mem _ hl))
    refine ⟨index :: indices, ?_⟩
    change apply answer literal :: rest.map (apply answer) =
      target.get index :: selected target indices
    rw [equal, aligned]

/-- Exhaustive candidate selection is complete for set theta-subsumption
    under the stated shared protection environment. -/
theorem search_set_complete [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (source target : Clause σ) (answer : Subst σ)
    (fixed : RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer)
    (covers : Covers answer source target) :
    ∃ result, search false source target = some result := by
  obtain ⟨indices, aligned⟩ := alignment_of_covers source target answer covers
  obtain ⟨result, accepted⟩ := check_complete false source target indices answer fixed aligned (by simp)
  have lengthEq : indices.length = source.length := by
    simpa [selected] using (congrArg List.length aligned).symm
  exact searchCandidates_complete false source target _ indices result
    ((mem_selections indices).mpr lengthEq) accepted

theorem search_sound [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (indices : List (Fin target.length))
    (answer : Subst σ) (accepted : search consume source target = some (indices, answer)) :
    RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer ∧
      Covers answer source target ∧ (consume = true → indices.Nodup) :=
  check_sound consume source target indices answer
    (searchCandidates_sound consume source target _ indices answer accepted)

theorem search_alignment_complete [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (indices : List (Fin target.length))
    (answer : Subst σ)
    (fixed : RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer)
    (aligned : source.map (apply answer) = selected target indices)
    (distinct : consume = true → indices.Nodup) :
    ∃ result, search consume source target = some result := by
  obtain ⟨result, accepted⟩ := check_complete consume source target indices answer fixed aligned distinct
  have lengthEq : indices.length = source.length := by
    simpa [selected] using (congrArg List.length aligned).symm
  exact searchCandidates_complete consume source target _ indices result
    ((mem_selections indices).mpr lengthEq) accepted

theorem search_set_none_iff [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (source target : Clause σ) :
    search false source target = none ↔ ¬∃ answer,
      RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer ∧ Covers answer source target := by
  constructor
  · rintro rejected ⟨answer, fixed, covers⟩
    obtain ⟨result, accepted⟩ := search_set_complete source target answer fixed covers
    simp [rejected] at accepted
  · intro impossible
    cases h : search false source target with
    | none => rfl
    | some result =>
      have sound := search_sound false source target result.1 result.2 h
      exact False.elim (impossible ⟨result.2, sound.1, sound.2.1⟩)

section Semantics

open FirstOrderBridge

variable {Model : Type w} [(language σ).Structure Model]

def literalHolds (assignment : σ.vars → Model) (literal : SignedAtom σ) : Prop :=
  if literal.1 then realizeAtom assignment literal.2 else ¬realizeAtom assignment literal.2

def Holds (assignment : σ.vars → Model) (clause : Clause σ) : Prop :=
  ∃ literal ∈ clause, literalHolds assignment literal

def Universal (clause : Clause σ) : Prop := ∀ assignment : σ.vars → Model, Holds assignment clause

theorem literalHolds_apply (assignment : σ.vars → Model) (answer : Subst σ)
    (literal : SignedAtom σ) :
    literalHolds assignment (apply answer literal) ↔
      literalHolds (fun x => realizeTerm assignment (answer x)) literal := by
  simp only [literalHolds, apply, realizeAtom_applyAtom]

/-- Set theta-subsumption implies the universally closed source clause entails
    the universally closed target in every first-order structure. -/
theorem covers_entails (source target : Clause σ) (answer : Subst σ)
    (covers : Covers answer source target)
    (valid : Universal (Model := Model) source) : Universal (Model := Model) target := by
  intro assignment
  obtain ⟨literal, member, trueAt⟩ := valid (fun x => realizeTerm assignment (answer x))
  exact ⟨apply answer literal, covers literal member,
    (literalHolds_apply assignment answer literal).mpr trueAt⟩

theorem check_entails [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (indices : List (Fin target.length))
    (answer : Subst σ) (accepted : check consume source target indices = some answer)
    (valid : Universal (Model := Model) source) : Universal (Model := Model) target :=
  covers_entails source target answer (check_sound consume source target indices answer accepted).2.1 valid

theorem search_entails [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (consume : Bool) (source target : Clause σ) (indices : List (Fin target.length))
    (answer : Subst σ) (accepted : search consume source target = some (indices, answer))
    (valid : Universal (Model := Model) source) : Universal (Model := Model) target :=
  covers_entails source target answer (search_sound consume source target indices answer accepted).2.1 valid

end Semantics

end Mettapedia.Logic.LP.ClauseSubsumption
