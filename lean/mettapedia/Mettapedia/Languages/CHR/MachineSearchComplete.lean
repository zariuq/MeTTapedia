import Mettapedia.Languages.CHR.MachineSearch

/-! Completeness of the machine's partner search. If occurrences for the
remaining heads fit them (the active constraint at its own position, other
store occurrences elsewhere, distinct and not yet used) and some environment
extending the current one instantiates each head to its occurrence, then the
search reaches the complete selection with exactly those picks, under an
environment that the given one extends. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem head_instantiate_some {environment : Environment} {head : Head} {constraint : Constraint}
    (instantiated : head.instantiate environment = some constraint) :
    head.name = constraint.name ∧ instantiateTerms environment head.arguments = some constraint.arguments := by
  unfold Head.instantiate at instantiated
  rw [instantiateTerms_eq]
  cases arguments : head.arguments.mapM (Term.instantiate environment) with
  | none => simp [arguments] at instantiated
  | some values =>
    simp only [arguments, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at instantiated
    subst instantiated
    exact ⟨rfl, rfl⟩

section Fitting

variable (store : Store) (position active : Nat) (values : List Value)

/-- An occurrence fits the head at `index`: it is the active constraint at
the active position, and a store occurrence of the head's key elsewhere. -/
def Fits (index : Nat) (head : Head) (occurrence : Occurrence) : Prop :=
  if index = position then occurrence.id = active ∧ occurrence.constraint.arguments = values
  else ⟨occurrence.id, occurrence.constraint.arguments⟩ ∈ slot (Head.key head) store ∧ occurrence.id ≠ active

def AllFit : Nat → List Head → List Occurrence → Prop
  | _, [], [] => True
  | index, head :: heads, occurrence :: occurrences =>
    Fits store position active values index head occurrence ∧ AllFit (index + 1) heads occurrences
  | _, _, _ => False

def picksOf (heads : List Head) (occurrences : List Occurrence) : List Pick :=
  List.zipWith (fun head occurrence => ⟨Head.key head, occurrence.id⟩) heads occurrences

theorem selections_complete (target : Environment) :
    ∀ (index : Nat) (heads : List Head) (occurrences : List Occurrence)
      (environment : Environment) (picks : List Pick) (used : List Nat),
      List.Forall₂ (fun head occurrence => head.instantiate target = some occurrence.constraint) heads occurrences →
      AllFit store position active values index heads occurrences →
      (occurrences.map Occurrence.id).Nodup →
      (∀ occurrence ∈ occurrences, occurrence.id ∉ used) →
      Extends target environment →
      ∃ bound, (bound, picks ++ picksOf heads occurrences) ∈
          selections store position active values index heads environment picks used ∧
        Extends target bound
  | index, [], [], environment, picks, used, _, _, _, _, grown =>
    ⟨environment, by simp [selections, picksOf], grown⟩
  | index, head :: heads, occurrence :: occurrences, environment, picks, used,
      instantiated, fitting, distinct, unused, grown => by
    obtain ⟨instantiatedHead, instantiatedRest⟩ := List.forall₂_cons.mp instantiated
    obtain ⟨fits, fitsRest⟩ := fitting
    obtain ⟨sameName, arguments⟩ := head_instantiate_some instantiatedHead
    obtain ⟨bound, matched, covered⟩ :=
      matchTerms_complete head.arguments occurrence.constraint.arguments environment target grown arguments
    have notUsed : occurrence.id ∉ used := unused occurrence (by simp)
    rw [List.map_cons, List.nodup_cons] at distinct
    have restUnused : ∀ later ∈ occurrences, later.id ∉ occurrence.id :: used := by
      intro later member inside
      rcases List.mem_cons.mp inside with same | old
      · exact distinct.1 (same ▸ List.mem_map_of_mem member)
      · exact unused later (by simp [member]) old
    obtain ⟨final, reached, coveredFinal⟩ :=
      selections_complete target (index + 1) heads occurrences bound
        (picks ++ [⟨Head.key head, occurrence.id⟩]) (occurrence.id :: used)
        instantiatedRest fitsRest distinct.2 restUnused covered
    refine ⟨final, ?_, coveredFinal⟩
    rw [selections_cons, List.mem_flatMap]
    have member : (⟨occurrence.id, occurrence.constraint.arguments⟩ : Occ) ∈
        candidates index position active values head store := by
      unfold Fits at fits
      unfold candidates
      by_cases here : index = position
      · simp only [here, if_true] at fits ⊢
        simp [fits.1, fits.2]
      · simp only [here, if_false] at fits ⊢
        exact fits.1
    have accepted : ¬ (occurrence.id ∈ used ∨ (index ≠ position ∧ occurrence.id = active)) := by
      unfold Fits at fits
      rintro (old | ⟨elsewhere, isActive⟩)
      · exact notUsed old
      · simp only [elsewhere, if_false] at fits
        exact fits.2 isActive
    refine ⟨_, member, ?_⟩
    simp only [contribution, accepted, if_false, matched]
    simpa [picksOf, List.append_assoc] using reached

end Fitting

#print axioms selections_complete

end Mettapedia.Languages.CHR.Machine
