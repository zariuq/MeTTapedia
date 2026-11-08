import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution

/-!
# Named spaces on the candidate step: a labelling convention and one law

Space names are ordinary terms. An occurrence is labelled `atSpace s p`, where `s` is a term
in space position and `p` its payload; a port of a rule instance is a pair (space term, payload
term) placed by the same `atSpace`. Nothing else is added to `OccurrenceStep`: the step relation,
`Selection.Valid` and `Selection.result` are used unchanged.

**Superseded (2026-11-03).** The law below (`Resolved`, `LocatedStep`) is withdrawn: it refuses
atomic indirection (read a space handle and use it in the same firing) and search across held
spaces. It is replaced by selection relative to the actor's reach (`ReachAdmits`, `ReachStep` in
`NamedSpacesReach`). Its theorems remain true of the firings it admits, which are reach steps
(`located_step_is_reach_step`); `NamedSpacesReachDeputy` uses them for rules with literal spaces.

## The one law

A port whose space position is a free variable unifies with an occurrence in any space:
`take (atSpace X p)` takes from whichever space a selection picks, and binds `X` to it
(`Controls.unresolved_takes_from_either_space`). That is ambient authority. The law
(`Resolved`) asks that the store before the step entail, for every space position of the rule
(take, read, produce, absent, count), one rigid name. It is an ask on the information before
resources are selected, stable under refinement (`ResolvesTo.of_refines`). A space written as a
name discharges it from the text alone (`resolvesTo_name`), so for written names it is a
formation obligation; for a space supplied by data it is checked at admission. It cannot be one
of the rule's own checks: those are asked after the port equations, which resolve the space of
every selection, each to its own name (`resolution_after_selection_is_vacuous`, in
`NamedSpacesControls`). Tells are not consulted: a port whose space only a tell of the same rule
fixes is written with that term instead.

## What is proved

* **The flat step is the one-space case** (`flat_step_is_one_space`): placing every term of a
  rule and of the store at one rigid name preserves and reflects steps exactly, results included.
* **The rigid locations of `InteractionFormation` are the case of constant spaces**
  (`rigid_location_is_constant_space`, `rigid_step_iff`): the located pairs `N × T` under
  `LocatedSubstitution.action` embed exactly; every port of the image has a written name
  (`fromRigid_toRule`), so the law holds by formation (`fromRigid_resolved`).
* **With the law the step is per space.** Every taken, read and made occurrence lies at the name
  its port resolves to (`taken_at_port_space`, `read_at_port_space`, `made_at_port_space`); an
  absence or count check matches only occurrences at its own space (`check_matches_at_space`);
  occurrences at other spaces neither leave nor arrive (`frame_survives`, `frame_no_arrival`);
  well-located configurations stay well located (`LocatedStep.wellLocated`); and validity depends
  only on the occurrences at the rule's spaces (`valid_iff_of_agree_on_spaces`).

Both directions of the embeddings are by one lemma (`Embedding.valid_iff`, `result_map`)
about any injective map of term syntaxes that commutes with substitution and reflects the declared
equality.

## Controls (`Controls`)

A first-order term profile with names (`Tm`, syntactic equality) inhabits the interface. A rule
taking `atSpace X p` with `X` free is valid at two selections in two different spaces, and every
solution of each selection's problem sends `X` to that selection's space
(`unresolved_takes_from_either_space`, `unresolved_space_differs_by_selection`); it is not
resolved (`unresolved_rule_not_resolved`). Written at a name, the same rule takes only from that
space (`resolved_rule_takes_only_there`, `resolved_rule_refuses_other_space`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uN uO uU

/-! ## Space positions as terms -/

/-- Space positions as ordinary terms of an existing syntax: `atSpace s p` places payload `p` in
the space denoted by the term `s`, and `name n` is a rigid space name. `atSpace` is a free
constructor for the declared equality, and distinct names are never equal. -/
structure SpaceTerms {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) (N : Type uN) where
  atSpace : T → T → T
  name : N → T
  apply_atSpace : ∀ σ s p, A.apply σ (atSpace s p) = atSpace (A.apply σ s) (A.apply σ p)
  E_atSpace : ∀ s p s' p', A.E (atSpace s p) (atSpace s' p') ↔ A.E s s' ∧ A.E p p'
  atSpace_injective : ∀ s p s' p', atSpace s p = atSpace s' p' → s = s' ∧ p = p'
  apply_name : ∀ σ n, A.apply σ (name n) = name n
  E_name : ∀ n n', A.E (name n) (name n') ↔ n = n'

/-! ## An embedding lemma for term syntaxes -/

section Embedding

variable {T : Type uT} {U : Type uU} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- A map of term syntaxes that commutes with substitution, preserves and reflects the declared
equalities, and is injective. -/
structure Embedding (B : SubstitutionAction U S) (A : SubstitutionAction T S) (φ : U → T) :
    Prop where
  apply_comm : ∀ σ u, A.apply σ (φ u) = φ (B.apply σ u)
  E_iff : ∀ u v, A.E (φ u) (φ v) ↔ B.E u v
  injective : Function.Injective φ

/-- Map both sides of every equation. -/
def mapStore (φ : U → T) (store : EquationStore U) : EquationStore T :=
  store.map fun e => (φ e.1, φ e.2)

/-- Map the equations of a configuration; occurrences are untouched. -/
def mapConfiguration (φ : U → T) (C : Configuration U O) : Configuration T O :=
  ⟨mapStore φ C.equations, C.present⟩

theorem mapStore_append (φ : U → T) (one two : EquationStore U) :
    mapStore φ (one ++ two) = mapStore φ one ++ mapStore φ two :=
  List.map_append

omit [DecidableEq O] in
theorem mapStore_equations (φ : U → T) (label : O → U) :
    ∀ (patterns : List U) (selected : List O),
      mapStore φ (Selection.equations label patterns selected) =
        Selection.equations (fun o => φ (label o)) (patterns.map φ) selected
  | [], _ => by simp [mapStore, Selection.equations]
  | _ :: _, [] => by simp [mapStore, Selection.equations]
  | p :: ps, o :: os => by
      have rest := mapStore_equations φ label ps os
      simp only [mapStore, Selection.equations, List.zipWith_cons_cons, List.map_cons] at rest ⊢
      rw [rest]

omit [DecidableEq O] in
theorem problem_map (φ : U → T) (label : O → U) (rule : RuleInstance U)
    (selection : Selection O) (C : Configuration U O) :
    mapStore φ (selection.problem label rule C) =
      selection.problem (fun o => φ (label o)) (rule.map φ) (mapConfiguration φ C) := by
  simp only [Selection.problem, mapStore_append, mapStore_equations]
  rfl

theorem fire_moves_eq (store : Finset O) (selection : Selection O) :
    fire store (selection.commit (T := T)) = fire store (selection.commit (T := U)) := rfl

theorem result_map (φ : U → T) (label : O → U) (rule : RuleInstance U)
    (selection : Selection O) (C : Configuration U O) :
    selection.result (fun o => φ (label o)) (rule.map φ) (mapConfiguration φ C) =
      mapConfiguration φ (selection.result label rule C) := by
  simp only [Selection.result, mapConfiguration]
  rw [problem_map]
  rfl

/-- Enabling the occurrence moves of a selection, which have no predicate queries, does not read
    labels. -/
theorem enabled_moves_iff (label₁ : O → T) (label₂ : O → U) (store : Finset O)
    (selection : Selection O) :
    Enabled label₁ store (selection.commit (T := T)) ↔
      Enabled label₂ store (selection.commit (T := U)) := by
  constructor
  · intro h
    exact ⟨h.taken_subset, h.kept_subset, h.apart, h.fresh, by simp [Selection.commit]⟩
  · intro h
    exact ⟨h.taken_subset, h.kept_subset, h.apart, h.fresh, by simp [Selection.commit]⟩

variable {B : SubstitutionAction U S} {A : SubstitutionAction T S} {φ : U → T}

theorem Embedding.solves_iff (h : Embedding B A φ) (σ : S) (e : Equation U) :
    A.Solves σ (φ e.1, φ e.2) ↔ B.Solves σ e := by
  simp only [SubstitutionAction.Solves, h.apply_comm, h.E_iff]

theorem Embedding.models_iff (h : Embedding B A φ) (σ : S) (store : EquationStore U) :
    A.Models σ (mapStore φ store) ↔ B.Models σ store := by
  constructor
  · intro all e member
    exact (h.solves_iff σ e).mp (all _ (List.mem_map.mpr ⟨e, member, rfl⟩))
  · intro all e member
    obtain ⟨e', member', rfl⟩ := List.mem_map.mp member
    exact (h.solves_iff σ e').mpr (all e' member')

omit [DecidableEq O] in
theorem Embedding.matching_map (h : Embedding B A φ) (σ : S) (label : O → U) (store : Finset O)
    (p : U) :
    Check.matches A σ (fun o => φ (label o)) store (φ p) = Check.matches B σ label store p := by
  classical
  ext o
  simp only [Check.matches, Finset.mem_filter, h.apply_comm, h.E_iff]

omit [DecidableEq O] in
theorem Embedding.holds_map (h : Embedding B A φ) (σ : S) (label : O → U) (store : Finset O) :
    ∀ check : Check U,
      (check.map φ).Holds A σ (fun o => φ (label o)) store ↔ check.Holds B σ label store
  | .equal l r => h.solves_iff σ (l, r)
  | .absent p => by
      simp only [Check.map, Check.Holds, h.apply_comm, h.E_iff]
  | .count p n => by
      simp only [Check.map, Check.Holds]
      rw [h.matching_map]

theorem Embedding.valid_iff (h : Embedding B A φ) (label : O → U) (rule : RuleInstance U)
    (C : Configuration U O) (selection : Selection O) :
    selection.Valid A (fun o => φ (label o)) (rule.map φ) (mapConfiguration φ C) ↔
      selection.Valid B label rule C := by
  have models : ∀ σ,
      A.Models σ (selection.problem (fun o => φ (label o)) (rule.map φ) (mapConfiguration φ C)) ↔
        B.Models σ (selection.problem label rule C) := by
    intro σ
    rw [← problem_map]
    exact h.models_iff σ _
  constructor
  · intro v
    refine ⟨v.take_distinct, v.output_distinct, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [RuleInstance.map] using v.take_length
    · simpa [RuleInstance.map] using v.read_length
    · have outputs : (selection.made.map label).map φ = rule.produce.map φ := by
        rw [List.map_map]
        exact v.outputs
      exact List.map_injective_iff.mpr h.injective outputs
    · exact (enabled_moves_iff _ _ _ _).mp v.occurrences
    · obtain ⟨σ, solved⟩ := v.consistent
      exact ⟨σ, (models σ).mp solved⟩
    · intro check member σ solved
      have mapped := v.checks (check.map φ) (List.mem_map.mpr ⟨check, member, rfl⟩) σ
        ((models σ).mpr solved)
      exact (h.holds_map σ label C.present check).mp mapped
  · intro v
    refine ⟨v.take_distinct, v.output_distinct, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [RuleInstance.map] using v.take_length
    · simpa [RuleInstance.map] using v.read_length
    · change selection.made.map (fun o => φ (label o)) = rule.produce.map φ
      rw [← v.outputs, List.map_map]
      rfl
    · exact (enabled_moves_iff _ _ _ _).mpr v.occurrences
    · obtain ⟨σ, solved⟩ := v.consistent
      exact ⟨σ, (models σ).mpr solved⟩
    · intro check member σ solved
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (h.holds_map σ label C.present original).mpr
        (v.checks original present σ ((models σ).mp solved))

omit [DecidableEq O] in
theorem Embedding.mapConfiguration_injective (h : Embedding B A φ) {C D : Configuration U O}
    (same : mapConfiguration φ C = mapConfiguration φ D) : C = D := by
  obtain ⟨equationsC, presentC⟩ := C
  obtain ⟨equationsD, presentD⟩ := D
  simp only [mapConfiguration, Configuration.mk.injEq] at same
  obtain ⟨stores, presents⟩ := same
  have pairInjective : Function.Injective (fun e : Equation U => (φ e.1, φ e.2)) := by
    intro e e' same
    simp only [Prod.mk.injEq] at same
    exact Prod.ext (h.injective same.1) (h.injective same.2)
  have : equationsC = equationsD := List.map_injective_iff.mpr pairInjective stores
  subst this
  subst presents
  rfl

/-- **Steps transport exactly along an embedding**, in both directions. -/
theorem Embedding.step_iff (h : Embedding B A φ) (label : O → U) (rule : RuleInstance U)
    (C D : Configuration U O) :
    Step A (fun o => φ (label o)) (rule.map φ) (mapConfiguration φ C) (mapConfiguration φ D) ↔
      Step B label rule C D := by
  constructor
  · rintro ⟨selection, valid, after⟩
    refine ⟨selection, (h.valid_iff label rule C selection).mp valid, ?_⟩
    rw [result_map] at after
    exact h.mapConfiguration_injective after
  · rintro ⟨selection, valid, rfl⟩
    exact ⟨selection, (h.valid_iff label rule C selection).mpr valid,
      (result_map φ label rule selection C).symm⟩

end Embedding

/-! ## The flat step is the one-space case -/

section OneSpace

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} (sts : SpaceTerms A N)

/-- Placing every term at one rigid space name embeds the term syntax in itself. -/
theorem oneSpace_embedding (c : N) : Embedding A A (sts.atSpace (sts.name c)) where
  apply_comm σ u := by rw [sts.apply_atSpace, sts.apply_name]
  E_iff u v := by
    rw [sts.E_atSpace]
    exact ⟨fun same => same.2, fun same => ⟨A.equivalence.refl _, same⟩⟩
  injective u v same := (sts.atSpace_injective _ _ _ _ same).2

/-- **The flat step is the one-space special case**: placing the rule, the store and every
label at one rigid name preserves and reflects steps, with the same selections. -/
theorem flat_step_is_one_space (c : N) (payload : O → T) (rule : RuleInstance T)
    (C D : Configuration T O) :
    Step A (fun o => sts.atSpace (sts.name c) (payload o)) (rule.map (sts.atSpace (sts.name c)))
        (mapConfiguration (sts.atSpace (sts.name c)) C)
        (mapConfiguration (sts.atSpace (sts.name c)) D) ↔
      Step A payload rule C D :=
  (oneSpace_embedding sts c).step_iff payload rule C D

theorem flat_valid_is_one_space (c : N) (payload : O → T) (rule : RuleInstance T)
    (C : Configuration T O) (selection : Selection O) :
    selection.Valid A (fun o => sts.atSpace (sts.name c) (payload o))
        (rule.map (sts.atSpace (sts.name c))) (mapConfiguration (sts.atSpace (sts.name c)) C) ↔
      selection.Valid A payload rule C :=
  (oneSpace_embedding sts c).valid_iff payload rule C selection

omit [DecidableEq O] in
/-- Placing a store at one space changes none of its solutions. -/
theorem oneSpace_store_equivalent (c : N) (store : EquationStore T) :
    A.Equivalent (mapStore (sts.atSpace (sts.name c)) store) store :=
  fun σ => (oneSpace_embedding sts c).models_iff σ store

end OneSpace

/-! ## Located rules: every port names its space by a term -/

section Located

variable {T : Type uT}

/-- A check of a located rule: an equality ask is about data; absence and count look at the
occurrences of one space. -/
inductive LocatedCheck (T : Type uT) where
  | equal (left right : T)
  | absent (space payload : T)
  | count (space payload : T) (number : Nat)

/-- A rule instance whose ports are pairs of a space term and a payload term. -/
structure LocatedRule (T : Type uT) where
  take : List (T × T)
  read : List (T × T)
  tell : EquationStore T
  checks : List (LocatedCheck T)
  produce : List (T × T)

/-- The space a check looks at, if any. -/
def LocatedCheck.space? : LocatedCheck T → Option T
  | .equal _ _ => none
  | .absent s _ => some s
  | .count s _ _ => some s

/-- Every space position of a rule: its take, read and produce ports and its absence and count
checks. -/
def LocatedRule.spaces (r : LocatedRule T) : List T :=
  r.take.map Prod.fst ++ r.read.map Prod.fst ++ r.produce.map Prod.fst ++
    r.checks.filterMap LocatedCheck.space?

theorem take_space_mem {r : LocatedRule T} {port : T × T} (member : port ∈ r.take) :
    port.1 ∈ r.spaces :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨port, member, rfl⟩)))

theorem read_space_mem {r : LocatedRule T} {port : T × T} (member : port ∈ r.read) :
    port.1 ∈ r.spaces :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨port, member, rfl⟩)))

theorem produce_space_mem {r : LocatedRule T} {port : T × T} (member : port ∈ r.produce) :
    port.1 ∈ r.spaces :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨port, member, rfl⟩))

theorem check_space_mem {r : LocatedRule T} {check : LocatedCheck T} (member : check ∈ r.checks)
    {s : T} (space : check.space? = some s) : s ∈ r.spaces :=
  List.mem_append_right _ (List.mem_filterMap.mpr ⟨check, member, space⟩)

variable {S : Type uS} {N : Type uN} {A : SubstitutionAction T S} (sts : SpaceTerms A N)

/-- A port as a term. -/
def place (port : T × T) : T := sts.atSpace port.1 port.2

/-- A located check as an ordinary check. -/
def LocatedCheck.toCheck : LocatedCheck T → Check T
  | .equal l r => .equal l r
  | .absent s p => .absent (sts.atSpace s p)
  | .count s p k => .count (sts.atSpace s p) k

/-- The ordinary rule instance of a located rule: every port is an `atSpace` term. -/
def LocatedRule.toRule (r : LocatedRule T) : RuleInstance T where
  take := r.take.map (place sts)
  read := r.read.map (place sts)
  tell := r.tell
  checks := r.checks.map (LocatedCheck.toCheck sts)
  produce := r.produce.map (place sts)

/-- **The labelling convention**: an occurrence carries a space term and a payload. -/
def located {O : Type uO} (space payload : O → T) : O → T :=
  fun o => sts.atSpace (space o) (payload o)

end Located

/-! ## The rigid locations of `InteractionFormation` are constant spaces -/

section Rigid

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} (sts : SpaceTerms A N)

/-- A located pair of the rigid model as a term at a written space name. -/
def rigid (pair : N × T) : T := sts.atSpace (sts.name pair.1) pair.2

theorem rigid_embedding : Embedding (LocatedSubstitution.action A) A (rigid sts) where
  apply_comm σ u := by
    simp only [rigid, sts.apply_atSpace, sts.apply_name, LocatedSubstitution.action]
  E_iff u v := by
    simp only [rigid, sts.E_atSpace, sts.E_name, LocatedSubstitution.action]
  injective u v same := by
    obtain ⟨names, payloads⟩ := sts.atSpace_injective _ _ _ _ same
    have related : A.E (sts.name u.1) (sts.name v.1) := by
      rw [names]
      exact A.equivalence.refl _
    exact Prod.ext ((sts.E_name _ _).mp related) payloads

/-- **The rigid locations of `InteractionFormation` are the constant-space case**: a selection is
valid for a rule over located pairs exactly when it is valid for the image rule, whose every
space is a written name, at the image configuration. -/
theorem rigid_location_is_constant_space (location : O → N) (payload : O → T)
    (rule : RuleInstance (N × T)) (C : Configuration (N × T) O) (selection : Selection O) :
    selection.Valid A (located sts (fun o => sts.name (location o)) payload)
        (rule.map (rigid sts)) (mapConfiguration (rigid sts) C) ↔
      selection.Valid (LocatedSubstitution.action A) (fun o => (location o, payload o)) rule C :=
  (rigid_embedding sts).valid_iff (fun o => (location o, payload o)) rule C selection

theorem rigid_step_iff (location : O → N) (payload : O → T) (rule : RuleInstance (N × T))
    (C D : Configuration (N × T) O) :
    Step A (located sts (fun o => sts.name (location o)) payload) (rule.map (rigid sts))
        (mapConfiguration (rigid sts) C) (mapConfiguration (rigid sts) D) ↔
      Step (LocatedSubstitution.action A) (fun o => (location o, payload o)) rule C D :=
  (rigid_embedding sts).step_iff (fun o => (location o, payload o)) rule C D

/-- The image of a rigid check. -/
def fromRigidCheck : Check (N × T) → LocatedCheck T
  | .equal l r => .equal (rigid sts l) (rigid sts r)
  | .absent p => .absent (sts.name p.1) p.2
  | .count p k => .count (sts.name p.1) p.2 k

/-- The image of a rigid rule as a located rule: every space is a written name. -/
def fromRigid (rule : RuleInstance (N × T)) : LocatedRule T where
  take := rule.take.map fun p => (sts.name p.1, p.2)
  read := rule.read.map fun p => (sts.name p.1, p.2)
  tell := mapStore (rigid sts) rule.tell
  checks := rule.checks.map (fromRigidCheck sts)
  produce := rule.produce.map fun p => (sts.name p.1, p.2)

theorem fromRigid_toRule (rule : RuleInstance (N × T)) :
    (fromRigid sts rule).toRule sts = rule.map (rigid sts) := by
  have checks : (LocatedCheck.toCheck sts ∘ fromRigidCheck sts) = Check.map (rigid sts) := by
    funext c
    cases c <;> rfl
  have ports : (place sts ∘ fun p : N × T => (sts.name p.1, p.2)) = rigid sts := rfl
  simp only [LocatedRule.toRule, fromRigid, RuleInstance.map, List.map_map, checks, ports]
  rfl

end Rigid

/-! ## The resolved-location law -/

section Law

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} (sts : SpaceTerms A N)

/-- The store resolves a space term to a name: every solution sends the term to that name. -/
def ResolvesTo (store : EquationStore T) (s : T) (n : N) : Prop :=
  A.Entails store fun σ => A.E (A.apply σ s) (sts.name n)

/-- The store resolves a space term to some name. -/
def Resolves (store : EquationStore T) (s : T) : Prop := ∃ n, ResolvesTo sts store s n

/-- **The resolved-location law**: the store before the step resolves every space position of
the rule (take, read and produce ports, absence and count checks). Superseded by `ReachAdmits`
(`NamedSpacesReach`). -/
def Resolved (store : EquationStore T) (r : LocatedRule T) : Prop :=
  ∀ s ∈ r.spaces, Resolves sts store s

/-- Every present occurrence lies at a space its configuration resolves. -/
def WellLocated (space : O → T) (C : Configuration T O) : Prop :=
  ∀ o ∈ C.present, Resolves sts C.equations (space o)

/-- The located step: the candidate step on the ordinary rule of a located rule, admitted only
under the law. It is not a second step relation. Superseded by `ReachStep` (`NamedSpacesReach`). -/
def LocatedStep (space payload : O → T) (r : LocatedRule T)
    (before after : Configuration T O) : Prop :=
  Resolved sts before.equations r ∧ Step A (located sts space payload) (r.toRule sts) before after

/-- The names a rule's space positions resolve to. -/
def Footprint (store : EquationStore T) (r : LocatedRule T) (n : N) : Prop :=
  ∃ s ∈ r.spaces, ResolvesTo sts store s n

/-- Two configurations agree on the spaces of a rule: same equations, and the same occurrences
among those at a name of the rule's footprint. -/
def AgreeOn (space : O → T) (r : LocatedRule T) (C D : Configuration T O) : Prop :=
  C.equations = D.equations ∧
    ∀ o, (∃ n, Footprint sts C.equations r n ∧ ResolvesTo sts C.equations (space o) n) →
      (o ∈ C.present ↔ o ∈ D.present)

variable {sts}

omit [DecidableEq O] in
/-- A written name discharges the law from the text alone. -/
theorem resolvesTo_name (store : EquationStore T) (n : N) :
    ResolvesTo sts store (sts.name n) n := by
  intro σ _
  rw [sts.apply_name]
  exact A.equivalence.refl _

omit [DecidableEq O] in
/-- **The law is stable**: refining the store never unresolves a space. -/
theorem ResolvesTo.of_refines {stronger weaker : EquationStore T}
    (refinement : A.Refines stronger weaker) {s : T} {n : N}
    (resolved : ResolvesTo sts weaker s n) : ResolvesTo sts stronger s n :=
  A.entails_of_refines refinement resolved

omit [DecidableEq O] in
theorem ResolvesTo.congr {store : EquationStore T} {s s' : T} (same : A.E s s') {n : N}
    (resolved : ResolvesTo sts store s n) : ResolvesTo sts store s' n := by
  intro σ solved
  exact A.equivalence.trans (A.equivalence.symm (A.preserves σ same)) (resolved σ solved)

omit [DecidableEq O] in
/-- Under one solution, two resolved terms related by the declared equality have one name. -/
theorem ResolvesTo.name_eq {store : EquationStore T} {σ : S} (solved : A.Models σ store)
    {s s' : T} {n n' : N} (first : ResolvesTo sts store s n)
    (second : ResolvesTo sts store s' n') (same : A.E (A.apply σ s) (A.apply σ s')) : n = n' := by
  apply (sts.E_name n n').mp
  exact A.equivalence.trans (A.equivalence.symm (first σ solved))
    (A.equivalence.trans same (second σ solved))

omit [DecidableEq O] in
/-- A consistent store resolves a term to at most one name. -/
theorem ResolvesTo.unique {store : EquationStore T} (consistent : A.Consistent store) {s : T}
    {n n' : N} (first : ResolvesTo sts store s n) (second : ResolvesTo sts store s n') :
    n = n' := by
  obtain ⟨σ, solved⟩ := consistent
  exact first.name_eq solved second (A.equivalence.refl _)

omit [DecidableEq O] in
/-- Rules from the rigid model satisfy the law at every store: their spaces are written. -/
theorem fromRigid_resolved (store : EquationStore T) (rule : RuleInstance (N × T)) :
    Resolved sts store (fromRigid sts rule) := by
  intro s member
  simp only [LocatedRule.spaces, fromRigid, List.map_map, List.mem_append, List.mem_map,
    List.mem_filterMap] at member
  rcases member with ((⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩) | ⟨c, cm, cs⟩
  · exact ⟨p.1, resolvesTo_name store p.1⟩
  · exact ⟨p.1, resolvesTo_name store p.1⟩
  · exact ⟨p.1, resolvesTo_name store p.1⟩
  · obtain ⟨c', _, rfl⟩ := cm
    cases c' with
    | equal l r => cases cs
    | absent p =>
        simp only [fromRigidCheck, LocatedCheck.space?, Option.some.injEq] at cs
        subst cs
        exact ⟨p.1, resolvesTo_name store p.1⟩
    | count p k =>
        simp only [fromRigidCheck, LocatedCheck.space?, Option.some.injEq] at cs
        subst cs
        exact ⟨p.1, resolvesTo_name store p.1⟩

omit [DecidableEq O] in
/-- Occurrences of the rigid model are well located in every configuration. -/
theorem rigid_wellLocated (location : O → N) (C : Configuration T O) :
    WellLocated sts (fun o => sts.name (location o)) C :=
  fun o _ => ⟨location o, resolvesTo_name C.equations (location o)⟩

private theorem forall₂_exists_left {α β : Type*} {R : α → β → Prop} {l : List α} {l' : List β}
    (related : List.Forall₂ R l l') {b : β} (member : b ∈ l') : ∃ a ∈ l, R a b := by
  induction related with
  | nil => cases member
  | @cons first second left right pair rest ih =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨first, List.mem_cons_self, pair⟩
      · obtain ⟨other, present, rel⟩ := ih tail
        exact ⟨other, List.mem_cons_of_mem _ present, rel⟩

variable {space payload : O → T} {r : LocatedRule T} {before : Configuration T O}
  {selection : Selection O}

theorem valid_before_consistent
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before) :
    A.Consistent before.equations := by
  obtain ⟨σ, solved⟩ := valid.consistent
  exact ⟨σ, valid.refines σ solved⟩

/-- In a solution of the problem, each port's space agrees with its occurrence's space. -/
theorem port_spaces (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    {σ : S} (solved : A.Models σ (selection.problem (located sts space payload) (r.toRule sts) before)) :
    List.Forall₂ (fun port o => A.E (A.apply σ port.1) (A.apply σ (space o))) r.take
        selection.taken ∧
      List.Forall₂ (fun port o => A.E (A.apply σ port.1) (A.apply σ (space o))) r.read
        selection.read := by
  obtain ⟨_, takes, reads, _⟩ := Selection.models_problem A valid solved
  simp only [LocatedRule.toRule, List.forall₂_map_left_iff] at takes reads
  refine ⟨takes.imp fun port o same => ?_, reads.imp fun port o same => ?_⟩
  · simp only [place, located, sts.apply_atSpace, sts.E_atSpace] at same
    exact same.1
  · simp only [place, located, sts.apply_atSpace, sts.E_atSpace] at same
    exact same.1

/-- **A taken occurrence lies at the name its port resolves to.** -/
theorem taken_at_port_space
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    (resolved : Resolved sts before.equations r) (wellLocated : WellLocated sts space before)
    {o : O} (taken : o ∈ selection.taken) :
    ∃ port ∈ r.take, ∃ n, ResolvesTo sts before.equations port.1 n ∧
      ResolvesTo sts before.equations (space o) n := by
  obtain ⟨σ, solved⟩ := valid.consistent
  obtain ⟨port, member, same⟩ := forall₂_exists_left (port_spaces valid solved).1 taken
  obtain ⟨n, portAt⟩ := resolved port.1 (take_space_mem member)
  obtain ⟨m, occurrenceAt⟩ :=
    wellLocated o (valid.occurrences.taken_subset (by simpa [Selection.commit] using taken))
  have names : n = m :=
    portAt.name_eq (Selection.models_problem A valid solved).1 occurrenceAt same
  subst names
  exact ⟨port, member, n, portAt, occurrenceAt⟩

/-- **A read occurrence lies at the name its port resolves to.** -/
theorem read_at_port_space
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    (resolved : Resolved sts before.equations r) (wellLocated : WellLocated sts space before)
    {o : O} (read : o ∈ selection.read) :
    ∃ port ∈ r.read, ∃ n, ResolvesTo sts before.equations port.1 n ∧
      ResolvesTo sts before.equations (space o) n := by
  obtain ⟨σ, solved⟩ := valid.consistent
  obtain ⟨port, member, same⟩ := forall₂_exists_left (port_spaces valid solved).2 read
  obtain ⟨n, portAt⟩ := resolved port.1 (read_space_mem member)
  obtain ⟨m, occurrenceAt⟩ :=
    wellLocated o (valid.occurrences.kept_subset (by simpa [Selection.commit] using read))
  have names : n = m :=
    portAt.name_eq (Selection.models_problem A valid solved).1 occurrenceAt same
  subst names
  exact ⟨port, member, n, portAt, occurrenceAt⟩

/-- **A made occurrence carries the space term of its produce port**, which the store resolves. -/
theorem made_at_port_space
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    (resolved : Resolved sts before.equations r) {o : O} (made : o ∈ selection.made) :
    ∃ port ∈ r.produce, port.1 = space o ∧ ∃ n, ResolvesTo sts before.equations port.1 n := by
  have output : located sts space payload o ∈ (r.toRule sts).produce := by
    rw [← valid.outputs]
    exact List.mem_map.mpr ⟨o, made, rfl⟩
  simp only [LocatedRule.toRule, List.mem_map] at output
  obtain ⟨port, member, same⟩ := output
  exact ⟨port, member, (sts.atSpace_injective _ _ _ _ same).1,
    resolved port.1 (produce_space_mem member)⟩

omit [DecidableEq O] in
/-- **A check looks only at its space**: under a solution of the store, an occurrence matching
a pattern placed at a resolved space lies at that space. -/
theorem check_matches_at_space (wellLocated : WellLocated sts space before) {s p : T} {n : N}
    (checkAt : ResolvesTo sts before.equations s n) {σ : S}
    (solved : A.Models σ before.equations) {o : O} (present : o ∈ before.present)
    (matching : A.E (A.apply σ (sts.atSpace s p)) (A.apply σ (located sts space payload o))) :
    ResolvesTo sts before.equations (space o) n := by
  obtain ⟨m, occurrenceAt⟩ := wellLocated o present
  simp only [located, sts.apply_atSpace, sts.E_atSpace] at matching
  have names : n = m := checkAt.name_eq solved occurrenceAt matching.1
  subst names
  exact occurrenceAt

/-- **Frame, leaving**: an occurrence at a name outside the rule's footprint survives. -/
theorem frame_survives
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    (resolved : Resolved sts before.equations r) (wellLocated : WellLocated sts space before)
    {o : O} (present : o ∈ before.present) {k : N}
    (at_k : ResolvesTo sts before.equations (space o) k)
    (outside : ¬ Footprint sts before.equations r k) :
    o ∈ (selection.result (located sts space payload) (r.toRule sts) before).present := by
  apply mem_fire.mpr
  left
  refine ⟨present, fun takenMember => outside ?_⟩
  have taken : o ∈ selection.taken := by simpa [Selection.commit] using takenMember
  obtain ⟨port, member, n, portAt, occurrenceAt⟩ :=
    taken_at_port_space valid resolved wellLocated taken
  have names : k = n := ResolvesTo.unique (valid_before_consistent valid) at_k occurrenceAt
  subst names
  exact ⟨port.1, take_space_mem member, portAt⟩

/-- **Frame, arriving**: no occurrence arrives at a name outside the rule's footprint. -/
theorem frame_no_arrival
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    (resolved : Resolved sts before.equations r) {o : O}
    (after : o ∈ (selection.result (located sts space payload) (r.toRule sts) before).present)
    {k : N} (at_k : ResolvesTo sts before.equations (space o) k)
    (outside : ¬ Footprint sts before.equations r k) : o ∈ before.present := by
  rcases mem_fire.mp after with ⟨present, _⟩ | madeMember
  · exact present
  · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
    obtain ⟨port, member, same, n, portAt⟩ := made_at_port_space valid resolved made
    rw [same] at portAt
    have names : k = n := ResolvesTo.unique (valid_before_consistent valid) at_k portAt
    subst names
    exact absurd ⟨port.1, produce_space_mem member, same ▸ portAt⟩ outside

/-- **The located step keeps configurations well located.** -/
theorem LocatedStep.wellLocated {after : Configuration T O}
    (step : LocatedStep sts space payload r before after)
    (wellLocated : WellLocated sts space before) : WellLocated sts space after := by
  obtain ⟨resolved, selection, valid, rfl⟩ := step
  intro o present
  rcases mem_fire.mp present with ⟨old, _⟩ | madeMember
  · obtain ⟨n, at_n⟩ := wellLocated o old
    exact ⟨n, ResolvesTo.of_refines valid.refines at_n⟩
  · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
    obtain ⟨port, _, same, n, portAt⟩ := made_at_port_space valid resolved made
    exact ⟨n, ResolvesTo.of_refines valid.refines (same ▸ portAt)⟩

omit [DecidableEq O] in
theorem AgreeOn.symm {C D : Configuration T O} (agree : AgreeOn sts space r C D) :
    AgreeOn sts space r D C := by
  refine ⟨agree.1.symm, fun o atFootprint => ?_⟩
  rw [← agree.1] at atFootprint
  exact (agree.2 o atFootprint).symm

/-- One direction of per-space validity. -/
theorem valid_of_agree {C D : Configuration T O}
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    (resolved : Resolved sts C.equations r) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (agree : AgreeOn sts space r C D)
    (fresh : Disjoint selection.made.toFinset D.present) :
    selection.Valid A (located sts space payload) (r.toRule sts) D := by
  obtain ⟨equal, same⟩ := agree
  have problems : selection.problem (located sts space payload) (r.toRule sts) D =
      selection.problem (located sts space payload) (r.toRule sts) C := by
    simp only [Selection.problem, equal]
  have inC : ∀ o ∈ selection.taken, o ∈ D.present := by
    intro o taken
    obtain ⟨port, member, n, portAt, occurrenceAt⟩ := taken_at_port_space valid resolved wellC taken
    exact (same o ⟨n, ⟨port.1, take_space_mem member, portAt⟩, occurrenceAt⟩).mp
      (valid.occurrences.taken_subset (by simpa [Selection.commit] using taken))
  have readInD : ∀ o ∈ selection.read, o ∈ D.present := by
    intro o read
    obtain ⟨port, member, n, portAt, occurrenceAt⟩ := read_at_port_space valid resolved wellC read
    exact (same o ⟨n, ⟨port.1, read_space_mem member, portAt⟩, occurrenceAt⟩).mp
      (valid.occurrences.kept_subset (by simpa [Selection.commit] using read))
  refine ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
    valid.outputs, ⟨?_, ?_, valid.occurrences.apart, fresh, by simp [Selection.commit]⟩, ?_, ?_⟩
  · intro o member
    exact inC o (by simpa [Selection.commit] using member)
  · intro o member
    exact readInD o (by simpa [Selection.commit] using member)
  · rw [problems]
    exact valid.consistent
  · intro check member σ solved
    rw [problems] at solved
    have beforeC : A.Models σ C.equations := (Selection.models_problem A valid solved).1
    have beforeD : A.Models σ D.equations := equal ▸ beforeC
    have holdsC := valid.checks check member σ solved
    simp only [LocatedRule.toRule, List.mem_map] at member
    obtain ⟨located_check, checkMember, rfl⟩ := member
    cases located_check with
    | equal l r => exact holdsC
    | absent s p =>
        obtain ⟨n, checkAt⟩ := resolved s (check_space_mem checkMember rfl)
        intro o presentD matching
        have atD : ResolvesTo sts D.equations (space o) n :=
          check_matches_at_space wellD (equal ▸ checkAt) beforeD presentD matching
        have presentC : o ∈ C.present :=
          (same o ⟨n, ⟨s, check_space_mem checkMember rfl, checkAt⟩, equal ▸ atD⟩).mpr presentD
        exact holdsC o presentC matching
    | count s p k =>
        obtain ⟨n, checkAt⟩ := resolved s (check_space_mem checkMember rfl)
        change (Check.matches A σ (located sts space payload) D.present (sts.atSpace s p)).card = k
        have matching : Check.matches A σ (located sts space payload) D.present (sts.atSpace s p) =
            Check.matches A σ (located sts space payload) C.present (sts.atSpace s p) := by
          classical
          ext o
          simp only [Check.matches, Finset.mem_filter]
          constructor
          · rintro ⟨presentD, matching⟩
            have atD : ResolvesTo sts D.equations (space o) n :=
              check_matches_at_space wellD (equal ▸ checkAt) beforeD presentD matching
            exact ⟨(same o ⟨n, ⟨s, check_space_mem checkMember rfl, checkAt⟩, equal ▸ atD⟩).mpr
              presentD, matching⟩
          · rintro ⟨presentC, matching⟩
            have atC : ResolvesTo sts C.equations (space o) n :=
              check_matches_at_space wellC checkAt beforeC presentC matching
            exact ⟨(same o ⟨n, ⟨s, check_space_mem checkMember rfl, checkAt⟩, atC⟩).mp presentC,
              matching⟩
        rw [matching]
        exact holdsC

/-- **With the law, the step is per space**: validity depends only on the store and on the
occurrences at the names of the rule's footprint (given output identities fresh for both). -/
theorem valid_iff_of_agree_on_spaces {C D : Configuration T O}
    (resolved : Resolved sts C.equations r) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (agree : AgreeOn sts space r C D)
    (freshC : Disjoint selection.made.toFinset C.present)
    (freshD : Disjoint selection.made.toFinset D.present) :
    selection.Valid A (located sts space payload) (r.toRule sts) C ↔
      selection.Valid A (located sts space payload) (r.toRule sts) D := by
  constructor
  · intro valid
    exact valid_of_agree valid resolved wellC wellD agree freshD
  · intro valid
    have resolvedD : Resolved sts D.equations r := agree.1 ▸ resolved
    exact valid_of_agree valid resolvedD wellD wellC agree.symm freshC

end Law

/-! ## Controls: a first-order term profile with space names -/

namespace Controls

/-- First-order terms with variables, space names, symbols, application and placement. -/
inductive Tm where
  | var (index : Nat)
  | nm (name : Nat)
  | sym (symbol : String)
  | app (head argument : Tm)
  | loc (space payload : Tm)
  deriving DecidableEq

/-- Substitution of terms for variables. -/
def Tm.subst (σ : Nat → Tm) : Tm → Tm
  | .var i => σ i
  | .nm n => .nm n
  | .sym a => .sym a
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .loc s p => .loc (s.subst σ) (p.subst σ)

theorem Tm.subst_var (t : Tm) : t.subst Tm.var = t := by
  induction t with
  | var => rfl
  | nm => rfl
  | sym => rfl
  | app f x ihf ihx => simp [Tm.subst, ihf, ihx]
  | loc s p ihs ihp => simp [Tm.subst, ihs, ihp]

theorem Tm.subst_subst (outer inner : Nat → Tm) (t : Tm) :
    (t.subst inner).subst outer = t.subst fun i => (inner i).subst outer := by
  induction t with
  | var => rfl
  | nm => rfl
  | sym => rfl
  | app f x ihf ihx => simp [Tm.subst, ihf, ihx]
  | loc s p ihs ihp => simp [Tm.subst, ihs, ihp]

/-- The first-order profile with syntactic equality. -/
def action : SubstitutionAction Tm (Nat → Tm) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply σ t := t.subst σ
  identity := Tm.var
  compose outer inner i := (inner i).subst outer
  apply_identity := Tm.subst_var
  apply_compose outer inner t := (Tm.subst_subst outer inner t).symm
  preserves σ {_ _} same := congrArg (Tm.subst σ) same

@[simp] theorem action_E (t u : Tm) : action.E t u ↔ t = u := Iff.rfl
@[simp] theorem action_apply (σ : Nat → Tm) (t : Tm) : action.apply σ t = t.subst σ := rfl

/-- Space names are the `nm` constants; placement is `loc`. -/
def spaces : SpaceTerms action Nat where
  atSpace := Tm.loc
  name := Tm.nm
  apply_atSpace _ _ _ := rfl
  E_atSpace s p s' p' := by
    show Tm.loc s p = Tm.loc s' p' ↔ s = s' ∧ p = p'
    simp
  atSpace_injective _ _ _ _ same := by simpa using same
  apply_name _ _ := rfl
  E_name n n' := by
    show Tm.nm n = Tm.nm n' ↔ n = n'
    simp

theorem models_iff (σ : Nat → Tm) (store : EquationStore Tm) :
    action.Models σ store ↔ ∀ e ∈ store, e.1.subst σ = e.2.subst σ := Iff.rfl

/-- Two occurrences with equal payloads, one in space 1 and one in space 2. -/
def twoSpaces : Nat → Tm := fun o => if o = 0 then .nm 1 else .nm 2

def letter : Nat → Tm := fun _ => .sym "letter"

def twoWorld : Configuration Tm Nat := ⟨[], {0, 1}⟩

/-- Takes a letter from whatever space the variable `0` denotes: no name is written. -/
def grabAnywhere : LocatedRule Tm := ⟨[(.var 0, .sym "letter")], [], [], [], []⟩

/-- Takes a letter from space 1, written by name. -/
def grabAtOne : LocatedRule Tm := ⟨[(.nm 1, .sym "letter")], [], [], [], []⟩

def takeFirst : Selection Nat := ⟨[0], [], []⟩
def takeSecond : Selection Nat := ⟨[1], [], []⟩

theorem takeFirst_enabled (label : Nat → Tm) :
    Enabled label twoWorld.present (takeFirst.commit (T := Tm)) :=
  ⟨by simp [Selection.commit, takeFirst, twoWorld], by simp [Selection.commit, takeFirst],
    by simp [Selection.commit, takeFirst], by simp [Selection.commit, takeFirst],
    by simp [Selection.commit]⟩

theorem takeSecond_enabled (label : Nat → Tm) :
    Enabled label twoWorld.present (takeSecond.commit (T := Tm)) :=
  ⟨by simp [Selection.commit, takeSecond, twoWorld], by simp [Selection.commit, takeSecond],
    by simp [Selection.commit, takeSecond], by simp [Selection.commit, takeSecond],
    by simp [Selection.commit]⟩

/-- **Without the law, a rule that writes no name takes from either space.** -/
theorem unresolved_takes_from_either_space :
    takeFirst.Valid action (located spaces twoSpaces letter) (grabAnywhere.toRule spaces)
        twoWorld ∧
      takeSecond.Valid action (located spaces twoSpaces letter) (grabAnywhere.toRule spaces)
        twoWorld := by
  constructor
  · refine ⟨by simp [takeFirst], by simp [takeFirst], rfl, rfl, rfl, takeFirst_enabled _,
      ⟨fun _ => .nm 1, ?_⟩, by simp [grabAnywhere, LocatedRule.toRule]⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, grabAnywhere, LocatedRule.toRule,
      takeFirst, twoWorld, place, located, spaces, twoSpaces, letter, Tm.subst]
  · refine ⟨by simp [takeSecond], by simp [takeSecond], rfl, rfl, rfl, takeSecond_enabled _,
      ⟨fun _ => .nm 2, ?_⟩, by simp [grabAnywhere, LocatedRule.toRule]⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, grabAnywhere, LocatedRule.toRule,
      takeSecond, twoWorld, place, located, spaces, twoSpaces, letter, Tm.subst]

/-- Every solution of each selection's problem sends the variable to that selection's space. -/
theorem unresolved_space_differs_by_selection :
    (∀ σ, action.Models σ (takeFirst.problem (located spaces twoSpaces letter)
        (grabAnywhere.toRule spaces) twoWorld) → σ 0 = .nm 1) ∧
      (∀ σ, action.Models σ (takeSecond.problem (located spaces twoSpaces letter)
        (grabAnywhere.toRule spaces) twoWorld) → σ 0 = .nm 2) := by
  constructor
  · intro σ solved
    simpa [SubstitutionAction.Solves, Selection.problem, Selection.equations,
      grabAnywhere, LocatedRule.toRule, takeFirst, twoWorld, place, located, spaces, twoSpaces,
      letter, Tm.subst] using solved
  · intro σ solved
    simpa [SubstitutionAction.Solves, Selection.problem, Selection.equations,
      grabAnywhere, LocatedRule.toRule, takeSecond, twoWorld, place, located, spaces, twoSpaces,
      letter, Tm.subst] using solved

/-- The variable's space is not resolved by the empty store: the law refuses the rule. -/
theorem unresolved_rule_not_resolved : ¬ Resolved spaces [] grabAnywhere := by
  intro resolved
  obtain ⟨n, at_n⟩ := resolved (.var 0) (by simp [LocatedRule.spaces, grabAnywhere])
  have := at_n (fun _ => .nm (n + 1)) (by simp)
  simp [spaces, Tm.subst] at this

theorem unresolved_rule_has_no_located_step (after : Configuration Tm Nat) :
    ¬ LocatedStep spaces twoSpaces letter grabAnywhere twoWorld after :=
  fun step => unresolved_rule_not_resolved step.1

/-- Positive control: written at a name, the rule satisfies the law. -/
theorem resolved_rule_resolved (store : EquationStore Tm) : Resolved spaces store grabAtOne := by
  intro s member
  simp only [LocatedRule.spaces, grabAtOne, List.map_cons, List.map_nil, List.filterMap_nil,
    List.cons_append, List.nil_append, List.mem_singleton] at member
  subst member
  exact ⟨1, resolvesTo_name store 1⟩

/-- Written at space 1, the rule takes the letter there. -/
theorem resolved_rule_takes_only_there :
    LocatedStep spaces twoSpaces letter grabAtOne twoWorld
      (takeFirst.result (located spaces twoSpaces letter) (grabAtOne.toRule spaces) twoWorld) := by
  refine ⟨resolved_rule_resolved [], takeFirst, ?_, rfl⟩
  refine ⟨by simp [takeFirst], by simp [takeFirst], rfl, rfl, rfl, takeFirst_enabled _,
    ⟨Tm.var, ?_⟩, by simp [grabAtOne, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, grabAtOne, LocatedRule.toRule,
    takeFirst, twoWorld, place, located, spaces, twoSpaces, letter, Tm.subst]

/-- Negative control: written at space 1, the rule cannot take the letter in space 2. -/
theorem resolved_rule_refuses_other_space :
    ¬ takeSecond.Valid action (located spaces twoSpaces letter) (grabAtOne.toRule spaces)
      twoWorld := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.consistent
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations,
    grabAtOne, LocatedRule.toRule, takeSecond, twoWorld, place, located, spaces, twoSpaces,
    letter, Tm.subst] at solved

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces
