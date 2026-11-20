import Mettapedia.Languages.MeTTa.PeTTa.LibTransformRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OneAfterAnother

/-!
# Independent Atom openings beside retained caller variables

A finite family of rules uses different tagged namespaces above the retained
source's bound. One substitution realizes every requested local assignment and
preserves the caller on all source terms. Untagged source names remain legal;
only existing tagged names need a bound. Terms and local answers may be open.

The conclusion is the existing joint-firing freshness predicate. It does not
assert matching, guard admission or a native runtime correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomFreshNamespaces

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst vars)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open RuleSyntax OneFrame JointFirings LibTransformStep

/-- Only names actually carrying a namespace occupy a namespace coordinate. -/
def Bounded (bound : Nat) (term : Atom) : Prop :=
  ∀ name ∈ vars term, ∀ scope original, untag name = some (scope, original) → scope < bound

def opening (bound index : Nat) : Subst := tagging (bound + index)

/-- Keep caller coordinates and interpret each new namespace independently.
An unbound local variable stays a variable, rather than inheriting the caller's
value at the same original spelling. -/
def combine (bound : Nat) (caller : Subst) (requested : Nat → Subst) : Subst :=
  fun name => match untag name with
    | none => caller name
    | some (scope, original) =>
        if bound ≤ scope then some ((requested (scope - bound) original).getD (.var original))
        else caller name

theorem combine_tag (bound index : Nat) (caller : Subst) (requested : Nat → Subst)
    (name : String) :
    combine bound caller requested (tag (bound + index) name) =
      some ((requested index name).getD (.var name)) := by
  simp [combine, untag_tag]

theorem combine_opening (bound : Nat) (caller : Subst) (requested : Nat → Subst)
    (index : Nat) : ∀ term : Atom,
    subst (combine bound caller requested) (subst (opening bound index) term) =
      subst (requested index) term
  | .var name => by simp [opening, tagging, subst, combine_tag]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression items => by
      simp only [subst]
      exact congrArg Atom.expression (children items)
where
  children : ∀ items : List Atom,
      subst.substList (combine bound caller requested) (subst.substList (opening bound index) items) =
        subst.substList (requested index) items
    | [] => rfl
    | first :: rest => by
        simp only [subst.substList, combine_opening bound caller requested index first, children rest]

theorem source_agrees (bound : Nat) (caller : Subst) (requested : Nat → Subst)
    (term : Atom) (below : Bounded bound term) :
    subst (combine bound caller requested) term = subst caller term := by
  apply Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_congr_on_vars
  intro name member
  unfold combine
  cases decoded : untag name with
  | none => rfl
  | some address =>
      have low := below name member address.1 address.2 decoded
      simp [show ¬ bound ≤ address.1 by omega]

theorem bounded_rename (scope : Nat) (term : Atom) : Bounded (scope + 1) (rename scope term) := by
  intro name member found original decoded
  rw [vars_rename] at member
  obtain ⟨localName, _, rfl⟩ := List.mem_map.mp member
  rw [untag_tag] at decoded
  cases decoded
  exact Nat.lt_succ_self scope

theorem opening_avoids_source (bound index : Nat) (term source : Atom)
    (below : Bounded bound source) :
    ∀ name ∈ vars (subst (opening bound index) term), name ∉ vars source := by
  rw [show subst (opening bound index) term = rename (bound + index) term from subst_tagging _ _]
  intro name member retained
  rw [vars_rename] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  have low := below _ retained (bound + index) original (untag_tag _ _)
  omega

abbrev X := frames atomAction
abbrev E := ext atomAction

def Keeps (bound : Nat) (caller assignment : Subst) : Prop :=
  ∀ term : Atom, Bounded bound term → subst assignment term = subst caller term

def Requested (bound : Nat) (requested : Nat → Subst) (past : Finset Nat)
    (assignment : Subst) : Prop :=
  ∀ index ∈ past, ∀ term : Atom,
    subst assignment (subst (opening bound index) term) = subst (requested index) term

variable {O : Type*} {P : Program (Terms Atom)}

/-- Every member receives its own assignment, jointly with all retained caller
information. Repeated use of one schema is allowed with different openings. -/
theorem realized (bound : Nat) (caller : Subst)
    (family : List (Nat × OneMember atomAction O P))
    (distinct : (family.map Prod.fst).Nodup)
    (correct : ∀ entry ∈ family, entry.2.opening = opening bound entry.1)
    (requested : Nat → Subst) (past : Finset Nat)
    (apart : ∀ index ∈ past, index ∉ family.map Prod.fst) :
    Realized X PUnit.unit (family.map Prod.snd)
      (fun assignment => Keeps bound caller assignment ∧ Requested bound requested past assignment) := by
  induction family generalizing requested past with
  | nil =>
      exact ⟨combine bound caller requested, source_agrees bound caller requested,
        fun index _ term => combine_opening bound caller requested index term⟩
  | cons entry rest ih =>
      obtain ⟨index, member⟩ := entry
      have unique := List.nodup_cons.mp distinct
      change ∀ locals : Subst,
        Realized X PUnit.unit (rest.map Prod.snd) (fun assignment =>
          (Keeps bound caller assignment ∧ Requested bound requested past assignment) ∧
            ∀ term ∈ member.rule.terms,
              subst assignment (subst member.opening term) = subst locals term)
      intro locals
      have laterCorrect : ∀ entry ∈ rest, entry.2.opening = opening bound entry.1 :=
        fun entry inside => correct entry (List.mem_cons_of_mem _ inside)
      have laterApart : ∀ i ∈ insert index past, i ∉ rest.map Prod.fst := by
        intro i inside inRest
        rcases Finset.mem_insert.mp inside with rfl | inPast
        · exact unique.1 inRest
        · exact apart i inPast (List.mem_cons_of_mem _ inRest)
      have later := ih unique.2 laterCorrect (Function.update requested index locals)
        (insert index past) laterApart
      apply Realized.mono X (rest.map Prod.snd) (fun assignment solved => ?_) later
      refine ⟨⟨solved.1, ?_⟩, ?_⟩
      · intro i inside term
        have different : i ≠ index := by
          intro same
          exact apart i inside (by simp [same])
        simpa only [Function.update_of_ne different] using
          solved.2 i (Finset.mem_insert_of_mem inside) term
      · intro term _
        rw [correct (index, member) List.mem_cons_self]
        simpa using solved.2 index (Finset.mem_insert_self _ _) term

theorem fresh (bound : Nat) (knowledge : EquationStore Atom) (present : Finset O)
    (label : O → Atom) (family : List (Nat × OneMember atomAction O P))
    (distinct : (family.map Prod.fst).Nodup)
    (correct : ∀ entry ∈ family, entry.2.opening = opening bound entry.1)
    (below : ∀ term, (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms Atom) O).Mentions term →
      Bounded bound term) :
    Bag.Fresh X (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms Atom) O)
      (⟨PUnit.unit, family.map Prod.snd⟩ : Bag O E P PUnit.unit) := by
  intro target caller
  cases target
  have all := realized bound caller family distinct correct (fun _ => atomAction.identity) ∅
    (fun _ inside => False.elim (Finset.notMem_empty _ inside))
  exact Realized.mono X (family.map Prod.snd) (fun assignment kept term mentioned => by
    change subst assignment (subst atomAction.identity term) = subst caller term
    change subst assignment (subst Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty term) = _
    rw [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_empty]
    exact kept.1 term (below term mentioned)) all

def nameBound (name : String) : Nat :=
  match untag name with
  | none => 0
  | some (scope, _) => scope + 1

def namesBound : List String → Nat
  | [] => 0
  | name :: rest => max (nameBound name) (namesBound rest)

theorem nameBound_le {name : String} {names : List String} (member : name ∈ names) :
    nameBound name ≤ namesBound names := by
  induction names with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

def supportBound (terms : List Atom) : Nat := namesBound (terms.flatMap vars)

/-- The bound is computed from the actual finite support, including arbitrary
source variable spellings and repeated occurrences. -/
theorem bounded_of_mem {terms : List Atom} {term : Atom} (inside : term ∈ terms) :
    Bounded (supportBound terms) term := by
  intro name member scope original decoded
  have inSupport : name ∈ terms.flatMap vars := List.mem_flatMap.mpr ⟨term, inside, member⟩
  have lower := nameBound_le inSupport
  have positive : scope < nameBound name := by simp [nameBound, decoded]
  exact positive.trans_le lower

noncomputable def sourceTerms (knowledge : EquationStore Atom) (present : Finset O)
    (label : O → Atom) : List Atom :=
  knowledge.map Prod.fst ++ knowledge.map Prod.snd ++ present.toList.map label

theorem mentioned_in_source {knowledge : EquationStore Atom} {present : Finset O}
    {label : O → Atom} {term : Atom}
    (mentioned : (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms Atom) O).Mentions term) :
    term ∈ sourceTerms knowledge present label := by
  rcases mentioned with left | right | ⟨occurrence, present, rfl⟩
  · exact List.mem_append_left _ (List.mem_append_left _ left)
  · exact List.mem_append_left _ (List.mem_append_right _ right)
  · exact List.mem_append_right _ (List.mem_map_of_mem (Finset.mem_toList.mpr present))

/-- No groundness or externally chosen namespace bound is required. -/
theorem fresh_from_support (knowledge : EquationStore Atom) (present : Finset O)
    (label : O → Atom) (family : List (Nat × OneMember atomAction O P))
    (distinct : (family.map Prod.fst).Nodup)
    (correct : ∀ entry ∈ family,
      entry.2.opening = opening (supportBound (sourceTerms knowledge present label)) entry.1) :
    Bag.Fresh X (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms Atom) O)
      (⟨PUnit.unit, family.map Prod.snd⟩ : Bag O E P PUnit.unit) :=
  fresh _ knowledge present label family distinct correct
    (fun _ mentioned => bounded_of_mem (mentioned_in_source mentioned))

end Mettapedia.Languages.MeTTa.PeTTa.AtomFreshNamespaces
