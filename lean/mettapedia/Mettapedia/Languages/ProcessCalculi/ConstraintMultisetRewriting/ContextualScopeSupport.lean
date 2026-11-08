import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRows
import Mettapedia.OSLF.Syntax.ContextualSupportSubstitution
import Mettapedia.OSLF.Syntax.ContextualFamilyObservations

/-!
# Finite scope footprints of contextual binding terms

A declaration family need not be finite. Its individual terms still have
finite support. An initial interpretation records the scopes owned by each
captured name; extending the actual sum family gives fresh locals their
allocated scope and retains that interpretation on older captures.

Private template keys have no live scope before opening. The same key used
inside an already live term is not private and must be accounted for.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScopeSupport

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {V W Local Shared : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}

def names (scopes : V → Finset Nat) : List V → Finset Nat
  | [] => ∅
  | name :: rest => scopes name ∪ names scopes rest

theorem mem_names (scopes : V → Finset Nat) (values : List V) (scope : Nat) :
    scope ∈ names scopes values ↔ ∃ name ∈ values, scope ∈ scopes name := by
  induction values with
  | nil => simp [names]
  | cons head rest ih => simp [names, ih, or_and_right, exists_or]

theorem names_subset_iff (scopes : V → Finset Nat) (values : List V) (occupied : Finset Nat) :
    names scopes values ⊆ occupied ↔ ∀ name ∈ values, scopes name ⊆ occupied := by
  constructor
  · intro bounded name member scope inside
    exact bounded ((mem_names scopes values scope).mpr ⟨name, member, inside⟩)
  · intro bounded scope member
    obtain ⟨name, present, inside⟩ := (mem_names scopes values scope).mp member
    exact bounded name present inside

theorem names_append (scopes : V → Finset Nat) (first second : List V) :
    names scopes (first ++ second) = names scopes first ∪ names scopes second := by
  induction first with
  | nil => simp [names]
  | cons name rest ih => simp only [names, List.cons_append, ih, Finset.union_assoc]

def term (scopes : V → Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S source) Γ sort) : Finset Nat := names scopes (support value)

def Covered (scopes : V → Finset Nat) (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S source) Γ sort) : Prop := term scopes value ⊆ occupied

theorem covered_iff (scopes : V → Finset Nat) (occupied : Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S source) Γ sort) :
    Covered scopes occupied value ↔ ∀ name ∈ support value, scopes name ⊆ occupied :=
  names_subset_iff scopes (support value) occupied

theorem Covered.mono {scopes : V → Finset Nat} {first second : Finset Nat}
    {Γ : Ctx S} {sort : S.Srt} {value : Term (signature S source) Γ sort}
    (covered : Covered scopes first value) (subset : first ⊆ second) : Covered scopes second value :=
  Finset.Subset.trans covered subset

theorem term_generator (scopes : V → Finset Nat) (name : V) :
    term scopes (generator source name) = scopes name := by
  simp only [term, support_generator, names, Finset.union_empty]

theorem covered_instantiate (outScopes : W → Finset Nat) (occupied : Finset Nat)
    (assignment : Assignment source target) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S source) Γ sort)
    (images : ∀ name ∈ support value, Covered outScopes occupied (assignment name)) :
    Covered outScopes occupied (instantiate assignment value) := by
  apply (covered_iff outScopes occupied _).mpr
  exact bounded_instantiate (fun name => outScopes name ⊆ occupied) assignment value
    (fun name member => (covered_iff outScopes occupied _).mp (images name member))

def Respects (inScopes : V → Finset Nat) (outScopes : W → Finset Nat)
    (assignment : Assignment source target) : Prop :=
  ∀ name, Covered outScopes (inScopes name) (assignment name)

theorem covered_instantiate_of_respects (inScopes : V → Finset Nat)
    (outScopes : W → Finset Nat) (occupied : Finset Nat)
    (assignment : Assignment source target) (respects : Respects inScopes outScopes assignment)
    {Γ : Ctx S} {sort : S.Srt} {value : Term (signature S source) Γ sort}
    (covered : Covered inScopes occupied value) :
    Covered outScopes occupied (instantiate assignment value) := by
  apply covered_instantiate outScopes occupied assignment value
  intro name member
  exact (respects name).mono ((covered_iff inScopes occupied value).mp covered name member)

def privateScopes (scopes : Shared → Finset Nat) : Local ⊕ Shared → Finset Nat :=
  Sum.elim (fun _ => ∅) scopes

def activeScopes (scopes : Shared → Finset Nat) : ScopedVar Local ⊕ Shared → Finset Nat :=
  Sum.elim (fun name => {name.scope}) scopes

theorem respects_capturedSource (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    (scopes : Shared → Finset Nat) :
    Respects scopes (privateScopes (Local := Local) scopes)
      (ContextualSelectionViews.capturedSource locals captures) := by
  intro name
  change term (privateScopes scopes) (generator (ContextualSelectionViews.source locals captures) (.inr name)) ⊆ scopes name
  rw [term_generator (S := S)]
  exact Finset.Subset.refl _

theorem respects_capturedTarget (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    (scopes : Shared → Finset Nat) :
    Respects scopes (activeScopes (Local := Local) scopes)
      (ContextualSelectionViews.capturedTarget locals captures) := by
  intro name
  change term (activeScopes scopes) (generator (ContextualSelectionViews.target locals captures) (.inr name)) ⊆ scopes name
  rw [term_generator (S := S)]
  exact Finset.Subset.refl _

theorem respects_liftCaptures {Next : Type} (locals : Local → MetaArity S)
    {captures : Shared → MetaArity S} {next : Next → MetaArity S}
    (inScopes : Shared → Finset Nat) (outScopes : Next → Finset Nat)
    (assignment : Assignment captures next) (respects : Respects inScopes outScopes assignment) :
    Respects (privateScopes (Local := Local) inScopes)
      (privateScopes (Local := Local) outScopes) (ContextualStoredRows.liftCaptures locals assignment) := by
  intro name
  cases name with
  | inl name =>
      change term (privateScopes outScopes)
        (generator (ContextualSelectionViews.source locals next) (.inl name)) ⊆ ∅
      rw [term_generator (S := S)]
      exact Finset.Subset.refl _
  | inr name =>
      exact covered_instantiate_of_respects outScopes _ _
        (ContextualSelectionViews.capturedSource locals next)
        (respects_capturedSource locals next outScopes) (respects name)

theorem covered_termAt (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    (scopes : Shared → Finset Nat) {occupied : Finset Nat} {scope : Nat}
    (allocated : scope ∈ occupied) {Γ : Ctx S} {sort : S.Srt}
    {value : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort}
    (covered : Covered (privateScopes scopes) occupied value) :
    Covered (activeScopes scopes) occupied (ContextualFreshening.termAt locals captures scope value) := by
  apply (covered_iff _ _ _).mpr
  intro name member
  rw [ContextualFreshening.support_termAt] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  cases original with
  | inl name =>
      exact Finset.singleton_subset_iff.mpr allocated
  | inr name =>
      exact (covered_iff _ _ _).mp covered (.inr name) present

def observation (scopes : V → Finset Nat) (value : Observation S source) : Finset Nat :=
  term scopes value.2.2

def observations (scopes : V → Finset Nat) (values : List (Observation S source)) : Finset Nat :=
  names (observation scopes) values

theorem observations_subset_iff (scopes : V → Finset Nat)
    (values : List (Observation S source)) (occupied : Finset Nat) :
    observations scopes values ⊆ occupied ↔
      ∀ value ∈ values, Covered scopes occupied value.2.2 :=
  names_subset_iff (observation scopes) values occupied

theorem observations_map (inScopes : V → Finset Nat) (outScopes : W → Finset Nat)
    (occupied : Finset Nat) (assignment : Assignment source target)
    (respects : Respects inScopes outScopes assignment) (values : List (Observation S source))
    (covered : observations inScopes values ⊆ occupied) :
    observations outScopes (values.map (instantiateObservation assignment)) ⊆ occupied := by
  apply (observations_subset_iff _ _ _).mpr
  intro value member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact covered_instantiate_of_respects inScopes outScopes occupied assignment respects
    ((observations_subset_iff _ _ _).mp covered original present)

def row (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    (scopes : Shared → Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : ContextualStoredRows.Row locals captures Γ sort) : Finset Nat :=
  term (privateScopes scopes) (ContextualStoredRows.asTemplate locals captures value)

theorem row_map {Next : Type} (locals : Local → MetaArity S)
    {captures : Shared → MetaArity S} {next : Next → MetaArity S}
    (inScopes : Shared → Finset Nat) (outScopes : Next → Finset Nat)
    (assignment : Assignment captures next) (respects : Respects inScopes outScopes assignment)
    {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    (value : ContextualStoredRows.Row locals captures Γ sort)
    (covered : row locals captures inScopes value ⊆ occupied) :
    row locals next outScopes (value.map locals assignment) ⊆ occupied := by
  unfold row
  rw [ContextualStoredRows.asTemplate_map]
  exact covered_instantiate_of_respects _ _ occupied
    (ContextualStoredRows.liftCaptures locals assignment)
    (respects_liftCaptures locals inScopes outScopes assignment respects) covered

theorem row_shared (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    (scopes : Shared → Finset Nat) {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {value : Term (signature S captures) Γ sort} (covered : Covered scopes occupied value) :
    row locals captures scopes (.shared value) ⊆ occupied :=
  covered_instantiate_of_respects scopes _ occupied _ (respects_capturedSource locals captures scopes) covered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScopeSupport
