import Mettapedia.Languages.ProcessCalculi.MORK.MatchLookupLocality

/-!
# Structural matching as simultaneous binding requirements

Shape inspection determines a finite list of variable occurrences. Each
occurrence requires the variable's lookup to equal the subject at that
position. Solving the requirements preserves earlier bindings. Solving in
another order can change the table's order while preserving every lookup.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MatchRequirements

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

abbrev Requirement := String × Atom

mutual

def collect : Atom → Atom → Option (List Requirement)
  | .var name, value => some [(name, value)]
  | .symbol first, .symbol second => if first == second then some [] else none
  | .grounded first, .grounded second => if first == second then some [] else none
  | .expression patterns, .expression values => collectList patterns values
  | _, _ => none

def collectList : List Atom → List Atom → Option (List Requirement)
  | [], [] => some []
  | pattern :: patterns, value :: values =>
      (collect pattern value).bind fun first =>
        (collectList patterns values).map fun rest => first ++ rest
  | _, _ => none

end

def solve (initial : Subst) : List Requirement → Option Subst
  | [] => some initial
  | (name, value) :: rest =>
      (matchAtom initial (.var name) value).bind fun middle => solve middle rest

theorem solve_append (initial : Subst) (first rest : List Requirement) :
    solve initial (first ++ rest) = (solve initial first).bind fun middle => solve middle rest := by
  induction first generalizing initial with
  | nil => rfl
  | cons demand later ih =>
    cases demand with
    | mk name value =>
      simp only [List.cons_append, solve, Option.bind_assoc]
      exact congrArg (Option.bind (matchAtom initial (.var name) value))
        (funext fun middle => ih middle)

mutual

theorem match_decomposes : ∀ (pattern value : Atom) (initial : Subst),
    matchAtom initial pattern value = (collect pattern value).bind (solve initial)
  | .var name, value, initial => by
    simp [collect, solve]
  | .symbol first, .symbol second, initial => by
    simp only [matchAtom, collect]
    split <;> rfl
  | .grounded first, .grounded second, initial => by
    simp only [matchAtom, collect]
    split <;> rfl
  | .expression patterns, .expression values, initial =>
    matchList_decomposes patterns values initial
  | .symbol _, .var _, _ | .symbol _, .grounded _, _ | .symbol _, .expression _, _
  | .grounded _, .var _, _ | .grounded _, .symbol _, _ | .grounded _, .expression _, _
  | .expression _, .var _, _ | .expression _, .symbol _, _ | .expression _, .grounded _, _ => rfl

theorem matchList_decomposes : ∀ (patterns values : List Atom) (initial : Subst),
    matchAtom.matchAtomList initial patterns values = (collectList patterns values).bind (solve initial)
  | [], [], _ => rfl
  | [], _ :: _, _ | _ :: _, [], _ => rfl
  | pattern :: patterns, value :: values, initial => by
    simp only [matchAtom.matchAtomList, collectList]
    rw [match_decomposes pattern value initial]
    cases first : collect pattern value with
    | none => rfl
    | some head =>
      simp only [Option.bind_some]
      cases tail : collectList patterns values with
      | none =>
        simp only [Option.map_none, Option.bind_none]
        cases extended : solve initial head with
        | none => rfl
        | some middle => simpa only [Option.bind_none, tail]
            using matchList_decomposes patterns values middle
      | some rest =>
        simp only [Option.map_some, Option.bind_some, solve_append]
        cases extended : solve initial head with
        | none => rfl
        | some middle => simpa only [Option.bind_some, tail]
            using matchList_decomposes patterns values middle

end

def Satisfies (table : Subst) (requirements : List Requirement) : Prop :=
  ∀ demand ∈ requirements, table.lookup demand.1 = some demand.2

structure Solves (initial : Subst) (requirements : List Requirement) (final : Subst) : Prop where
  keeps : final.lookupExtends initial
  satisfies : Satisfies final requirements
  outside : ∀ name, (∀ value, (name, value) ∉ requirements) → final.lookup name = initial.lookup name

private theorem requirement_lookup {initial final : Subst} {name : String} {value : Atom}
    (solved : matchAtom initial (.var name) value = some final) :
    final.lookup name = some value := by
  simp only [matchAtom] at solved
  cases seen : initial.lookup name with
  | none =>
    simp only [seen, Option.some.injEq] at solved
    subst final
    simp [Subst.lookup]
  | some prior =>
    simp only [seen] at solved
    split at solved
    · rename_i same
      cases solved
      rw [seen, Atom.eq_of_beq_eq_true same]
    · cases solved

theorem solve_sound {initial final : Subst} {requirements : List Requirement}
    (solved : solve initial requirements = some final) : Solves initial requirements final := by
  induction requirements generalizing initial with
  | nil =>
    cases solved
    exact ⟨Subst.lookupExtends_refl _, by simp [Satisfies], fun _ _ => rfl⟩
  | cons demand rest ih =>
    obtain ⟨name, value⟩ := demand
    cases found : matchAtom initial (.var name) value with
    | none => simp [solve, found] at solved
    | some middle =>
      have remaining : solve middle rest = some final := by simpa only [solve, found, Option.bind_some] using solved
      have result := ih remaining
      refine ⟨Subst.lookupExtends_trans (matchAtom_lookupExtends found) result.keeps, ?_, ?_⟩
      · intro demand member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact result.keeps name value (requirement_lookup found)
        · exact result.satisfies demand inRest
      · intro key absent
        have distinct : key ≠ name := by
          rintro rfl
          exact absent value (List.mem_cons_self ..)
        rw [result.outside key (fun site member => absent site (List.mem_cons_of_mem _ member))]
        exact matchAtom_lookup_outside found key (by simp [atomFreeVars, distinct])

private theorem requirement_from_witness (initial witness : Subst) (name : String) (value : Atom)
    (kept : witness.lookupExtends initial) (required : witness.lookup name = some value) :
    ∃ middle, matchAtom initial (.var name) value = some middle ∧ witness.lookupExtends middle := by
  cases seen : initial.lookup name with
  | some prior =>
    have equal : prior = value := Option.some.inj ((kept name prior seen).symm.trans required)
    subst prior
    exact ⟨initial, by simp [matchAtom, seen], kept⟩
  | none =>
    refine ⟨(name, value) :: initial, by simp [matchAtom, seen], ?_⟩
    intro key found whereFound
    by_cases same : key = name
    · subst key
      have exactValue : value = found := by simpa [Subst.lookup] using whereFound
      rw [← exactValue]
      exact required
    · exact kept key found (by simpa [Subst.lookup, Ne.symm same] using whereFound)

theorem solve_complete (initial witness : Subst) (requirements : List Requirement)
    (kept : witness.lookupExtends initial) (satisfies : Satisfies witness requirements) :
    ∃ final, solve initial requirements = some final := by
  induction requirements generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons demand rest ih =>
    obtain ⟨name, value⟩ := demand
    obtain ⟨middle, head, extended⟩ := requirement_from_witness initial witness name value kept
      (satisfies (name, value) (List.mem_cons_self ..))
    obtain ⟨final, tail⟩ := ih middle extended (fun demand member =>
      satisfies demand (List.mem_cons_of_mem _ member))
    exact ⟨final, by simp only [solve, head, Option.bind_some, tail]⟩

theorem same_support_same_lookups {initial left right : Subst} {first second : List Requirement}
    (one : Solves initial first left) (two : Solves initial second right)
    (same : ∀ demand, demand ∈ first ↔ demand ∈ second) :
    left.lookup = right.lookup := by
  funext name
  by_cases needed : ∃ value, (name, value) ∈ first
  · obtain ⟨value, member⟩ := needed
    exact (one.satisfies (name, value) member).trans
      (two.satisfies (name, value) ((same (name, value)).mp member)).symm
  · have absent : ∀ value, (name, value) ∉ first := fun value member => needed ⟨value, member⟩
    exact (one.outside name absent).trans
      (two.outside name (fun value member => absent value ((same (name, value)).mpr member))).symm

theorem reschedule_success {initial final : Subst} {first second : List Requirement}
    (solved : solve initial first = some final)
    (same : ∀ demand, demand ∈ first ↔ demand ∈ second) :
    ∃ other, solve initial second = some other ∧ other.lookup = final.lookup := by
  have one := solve_sound solved
  obtain ⟨other, computed⟩ := solve_complete initial final second one.keeps
    (fun demand member => one.satisfies demand ((same demand).mpr member))
  exact ⟨other, computed, same_support_same_lookups (solve_sound computed) one
    (fun demand => (same demand).symm)⟩

theorem rescheduling_preserves_match (initial : Subst) (first second : List Requirement)
    (same : ∀ demand, demand ∈ first ↔ demand ∈ second) :
    Option.Rel (fun a b : Subst => a.lookup = b.lookup) (solve initial first) (solve initial second) := by
  cases found : solve initial first with
  | some final =>
    obtain ⟨other, ran, lookups⟩ := reschedule_success found same
    rw [ran]
    exact .some lookups.symm
  | none =>
    cases observed : solve initial second with
    | none => exact .none
    | some other =>
      obtain ⟨final, ran, _⟩ := reschedule_success observed (fun demand => (same demand).symm)
      rw [found] at ran
      cases ran

/-- Reordering the captures preserves their use under any later
substitution, including a later binding of a variable captured as a value. -/
theorem rescheduled_match_preserves_composition {initial final : Subst} {first second : List Requirement}
    (solved : solve initial first = some final)
    (same : ∀ demand, demand ∈ first ↔ demand ∈ second) :
    ∃ other, solve initial second = some other ∧
      ∀ (later : Subst) (body : Atom),
        applySubst (other.compose later) body = applySubst (final.compose later) body := by
  obtain ⟨other, ready, resolved⟩ := reschedule_success solved same
  refine ⟨other, ready, fun later body => ?_⟩
  simp only [applySubst_compose]
  apply congrArg (applySubst later)
  simp only [applySubst_eq_subst, resolved]

end Mettapedia.Languages.ProcessCalculi.MORK.MatchRequirements
