import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition

/-!
# Renaming unknowns: a bisimulation of the step, and scope extension

At the one frame there is no binder: an unknown is private when no context mentions it. Its name is
then unobservable, and this module proves that renaming is a bisimulation of the step of every
program, and that a private unknown's scope extends past a neighbour that does not mention it.

## Renamings

A **renaming** (`Renaming`) is a substitution with an inverse, on terms and on substitutions. At
first-order terms every permutation of the unknowns is one (`permutation`). A renaming acts on a
state (`renameState`: every term of the knowledge and every label) and on a firing
(`renameFiring`: the opening, followed by the renaming).

## Equivariance

* `information_rename`: the information of the renamed firing at the renamed state is the renamed
  information; `holds_rename_iff`, `fresh_rename_iff`: guards and freshness are read through the
  renaming.
* **`admits_rename_iff`**: the renamed firing is admitted at the renamed state exactly when the
  firing is admitted at the state; **`result_rename`**: its result is the renamed result.
* **`succ_rename_iff`, the bisimulation**: the successors of a renamed state are exactly the renamed
  successors, for every program. So `t = renameState π s` is a bisimulation relating every state to
  its renaming, and reachable success under a barb that the renaming fixes is the same on both
  (`reaches_rename_iff`).

## Scope extension

* `renameState_beside`: renaming two systems side by side renames each.
* `beside_rename_of_fixed`: a renaming that fixes every term a neighbour mentions does not change it
  beside any system.
* **`scope_extension`**: so renaming the system alone beside such a neighbour is renaming the whole
  composition, and **`reaches_scope_extension`**: reachable success beside the neighbour is the same
  for the system and for its renaming. The side condition is needed
  (`RenamingControls.scope_extension_needs_fixed`): renaming the unknown the neighbour constrains
  turns a composition whose success is unreachable into one that succeeds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)
open Mettapedia.Logic.LP

universe uT uS uO

section Renamings

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- **A renaming**: a substitution with an inverse, on terms and on substitutions. -/
structure Renaming where
  forward : S
  backward : S
  back_forward : ∀ t, A.apply backward (A.apply forward t) = t
  forward_back : ∀ t, A.apply forward (A.apply backward t) = t
  compose_back : ∀ σ : S, A.compose forward (A.compose backward σ) = σ
  compose_forward : ∀ σ : S, A.compose backward (A.compose forward σ) = σ

variable {A}

/-- The inverse renaming. -/
def Renaming.symm (π : Renaming A) : Renaming A :=
  ⟨π.backward, π.forward, π.forward_back, π.back_forward, π.compose_forward, π.compose_back⟩

/-- Rename every term of a store. -/
def renameStore (π : Renaming A) (K : EquationStore T) : EquationStore T :=
  K.map fun e => (A.apply π.forward e.1, A.apply π.forward e.2)

theorem models_renameStore (π : Renaming A) (σ : S) (K : EquationStore T) :
    A.Models σ (renameStore π K) ↔ A.Models (A.compose σ π.forward) K := by
  constructor
  · intro solved e member
    have h := solved _ (List.mem_map.mpr ⟨e, member, rfl⟩)
    show A.E (A.apply (A.compose σ π.forward) e.1) (A.apply (A.compose σ π.forward) e.2)
    rw [A.apply_compose, A.apply_compose]
    exact h
  · intro solved e member
    obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp member
    have h : A.E (A.apply (A.compose σ π.forward) e₀.1) (A.apply (A.compose σ π.forward) e₀.2) :=
      solved e₀ inside
    rw [A.apply_compose, A.apply_compose] at h
    exact h

theorem models_congr_apply {σ₁ σ₂ : S} (same : ∀ t, A.apply σ₁ t = A.apply σ₂ t)
    (K : EquationStore T) : A.Models σ₁ K ↔ A.Models σ₂ K := by
  constructor
  · intro solved e member
    have h : A.E (A.apply σ₁ e.1) (A.apply σ₁ e.2) := solved e member
    rw [same, same] at h
    exact h
  · intro solved e member
    have h : A.E (A.apply σ₂ e.1) (A.apply σ₂ e.2) := solved e member
    rw [← same, ← same] at h
    exact h

/-- Undoing a renaming acts as the substitution itself. -/
theorem apply_undo (π : Renaming A) (σ : S) (t : T) :
    A.apply (A.compose (A.compose σ π.backward) π.forward) t = A.apply σ t := by
  rw [A.apply_compose, A.apply_compose, π.back_forward]

theorem renameStore_symm (π : Renaming A) (K : EquationStore T) :
    renameStore π.symm (renameStore π K) = K := by
  unfold renameStore
  rw [List.map_map]
  conv_rhs => rw [← List.map_id K]
  apply List.map_congr_left
  intro e _
  show (A.apply π.backward (A.apply π.forward e.1), A.apply π.backward (A.apply π.forward e.2)) = e
  rw [π.back_forward, π.back_forward]

end Renamings

/-! ## Renaming states and firings -/

variable {T : Type uT} {S : Type uS} {A : SubstitutionAction T S} {O : Type uO} [DecidableEq O]

/-- **Rename a state**: every term of its knowledge and every label. -/
def renameState (π : Renaming A) (s : State (Terms T) O) : State (Terms T) O :=
  ⟨PUnit.unit, renameStore π s.knowledge, s.present, fun o => A.apply π.forward (s.label o)⟩

/-- **Rename a firing**: its opening, followed by the renaming. -/
def renameFiring (π : Renaming A) {P : Program (Terms T)} (f : Firing O (ext A) P PUnit.unit) :
    Firing O (ext A) P PUnit.unit :=
  ⟨f.rule, f.member, f.ext, A.compose π.forward f.opening, f.selection, f.seen⟩

omit [DecidableEq O] in
theorem renameState_symm (π : Renaming A) (s : State (Terms T) O) :
    renameState π.symm (renameState π s) = s := by
  apply state_ext
  · exact renameStore_symm π s.knowledge
  · rfl
  · funext o
    exact π.back_forward (s.label o)

omit [DecidableEq O] in
theorem renameFiring_symm (π : Renaming A) {P : Program (Terms T)} (g : Firing O (ext A) P PUnit.unit) :
    renameFiring π (renameFiring π.symm g) = g := by
  obtain ⟨r, m, e, opening, selection, seen⟩ := g
  show (⟨r, m, e, A.compose π.forward (A.compose π.backward opening), selection, seen⟩ :
    Firing O (ext A) P PUnit.unit) = ⟨r, m, e, opening, selection, seen⟩
  rw [π.compose_back]

section Equivariance

variable {P : Program (Terms T)} (π : Renaming A) (f : Firing O (ext A) P PUnit.unit)
  (s : State (Terms T) O)

omit [DecidableEq O] in
theorem opened_take_rename :
    ((renameFiring π f).opened (frames A)).take = (f.opened (frames A)).take.map (A.apply π.forward) := by
  show f.rule.body.take.map (A.apply (A.compose π.forward f.opening)) =
    (f.rule.body.take.map (A.apply f.opening)).map (A.apply π.forward)
  rw [List.map_map]
  exact List.map_congr_left fun t _ => A.apply_compose _ _ _

omit [DecidableEq O] in
theorem opened_read_rename :
    ((renameFiring π f).opened (frames A)).read = (f.opened (frames A)).read.map (A.apply π.forward) := by
  show f.rule.body.read.map (A.apply (A.compose π.forward f.opening)) =
    (f.rule.body.read.map (A.apply f.opening)).map (A.apply π.forward)
  rw [List.map_map]
  exact List.map_congr_left fun t _ => A.apply_compose _ _ _

omit [DecidableEq O] in
theorem opened_produce_rename :
    ((renameFiring π f).opened (frames A)).produce =
      (f.opened (frames A)).produce.map (A.apply π.forward) := by
  show f.rule.body.produce.map (A.apply (A.compose π.forward f.opening)) =
    (f.rule.body.produce.map (A.apply f.opening)).map (A.apply π.forward)
  rw [List.map_map]
  exact List.map_congr_left fun t _ => A.apply_compose _ _ _

omit [DecidableEq O] in
theorem opened_tell_rename :
    ((renameFiring π f).opened (frames A)).tell = renameStore π (f.opened (frames A)).tell := by
  show f.rule.body.tell.map (fun pair => (A.apply (A.compose π.forward f.opening) pair.1,
      A.apply (A.compose π.forward f.opening) pair.2)) =
    (f.rule.body.tell.map fun pair => (A.apply f.opening pair.1, A.apply f.opening pair.2)).map
      fun e => (A.apply π.forward e.1, A.apply π.forward e.2)
  rw [List.map_map]
  exact List.map_congr_left fun e _ => by
    show (A.apply (A.compose π.forward f.opening) e.1, A.apply (A.compose π.forward f.opening) e.2) =
      (A.apply π.forward (A.apply f.opening e.1), A.apply π.forward (A.apply f.opening e.2))
    rw [A.apply_compose, A.apply_compose]

omit [DecidableEq O] in
theorem opened_checks_rename :
    ((renameFiring π f).opened (frames A)).checks =
      (f.opened (frames A)).checks.map (Check.map (A.apply π.forward)) := by
  show f.rule.body.checks.map (Check.map (A.apply (A.compose π.forward f.opening))) =
    (f.rule.body.checks.map (Check.map (A.apply f.opening))).map (Check.map (A.apply π.forward))
  rw [List.map_map]
  refine List.map_congr_left fun c _ => ?_
  cases c with
  | equal l r =>
      show Check.equal (A.apply (A.compose π.forward f.opening) l) (A.apply (A.compose π.forward f.opening) r) =
        Check.equal (A.apply π.forward (A.apply f.opening l)) (A.apply π.forward (A.apply f.opening r))
      rw [A.apply_compose, A.apply_compose]
  | predicate quantifier p =>
      show Check.predicate quantifier (A.apply (A.compose π.forward f.opening) p) =
        Check.predicate quantifier (A.apply π.forward (A.apply f.opening p))
      rw [A.apply_compose]
  | count p n =>
      show Check.count (A.apply (A.compose π.forward f.opening) p) n =
        Check.count (A.apply π.forward (A.apply f.opening p)) n
      rw [A.apply_compose]

omit [DecidableEq O] in
theorem collectOpened_rename :
    (renameFiring π f).collectOpened (frames A) = (f.collectOpened (frames A)).map (A.apply π.forward) := by
  show f.rule.collect.map (A.apply (A.compose π.forward f.opening)) =
    (f.rule.collect.map (A.apply f.opening)).map (A.apply π.forward)
  rw [List.map_map]
  exact List.map_congr_left fun t _ => A.apply_compose _ _ _

omit [DecidableEq O] in
theorem row_rename (o : O) :
    (renameFiring π f).row (frames A) (renameState π s) o = A.apply π.forward (f.row (frames A) s o) := by
  show A.apply A.identity (A.apply π.forward (s.label o)) =
    A.apply π.forward (A.apply A.identity (s.label o))
  rw [A.apply_identity, A.apply_identity]

omit [DecidableEq O] in
theorem zipWith_rename (row row' : O → T) (renamed : ∀ o, row' o = A.apply π.forward (row o)) :
    ∀ (l : List T) (m : List O),
      (l.map (A.apply π.forward)).zipWith (fun p o => (p, row' o)) m =
        renameStore π (l.zipWith (fun p o => (p, row o)) m)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, o :: os => by
      simp only [List.map_cons, List.zipWith_cons_cons, renameStore] at *
      rw [renamed o]
      congr 1
      exact zipWith_rename row row' renamed ps os

omit [DecidableEq O] in
theorem applyStore_weaken {a : PUnit.{1}} (e : (ext A).Ext a) (K : EquationStore T) :
    (frames A).applyStore (a := a) (b := (ext A).target e) ((ext A).weaken e) K = K :=
  Frames.applyStore_id (X := frames A) (a := a) K

omit [DecidableEq O] in
/-- **The information of the renamed firing at the renamed state is the renamed information.** -/
theorem information_rename :
    (renameFiring π f).information (frames A) (renameState π s) =
      renameStore π (f.information (frames A) s) := by
  unfold Firing.information Firing.matching
  rw [opened_take_rename, opened_read_rename, opened_tell_rename,
    zipWith_rename π (f.row (frames A) s) _ (row_rename π f s),
    zipWith_rename π (f.row (frames A) s) _ (row_rename π f s), applyStore_weaken, applyStore_weaken]
  simp only [renameStore, renameState, renameFiring, List.map_append]

omit [DecidableEq O] in
theorem matchesAt_rename {σ : S} {row row' : O → T} (renamed : ∀ o, row' o = A.apply π.forward (row o))
    (present : Finset O) (p : T) :
    matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ row' present (A.apply π.forward p) =
      matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) (A.compose σ π.forward) row present p := by
  ext o
  rw [mem_matchesAt, mem_matchesAt]
  show (o ∈ present ∧ A.E (A.apply σ (A.apply π.forward p)) (A.apply σ (row' o))) ↔
    (o ∈ present ∧ A.E (A.apply (A.compose σ π.forward) p) (A.apply (A.compose σ π.forward) (row o)))
  rw [renamed o, A.apply_compose, A.apply_compose]

omit [DecidableEq O] in
theorem checkHolds_rename {σ : S} {row row' : O → T} (renamed : ∀ o, row' o = A.apply π.forward (row o))
    (present : Finset O) (c : Check T) :
    checkHolds (frames A) (a := PUnit.unit) (b := PUnit.unit) σ row' present (Check.map (A.apply π.forward) c) ↔
      checkHolds (frames A) (a := PUnit.unit) (b := PUnit.unit) (A.compose σ π.forward) row present c := by
  cases c with
  | equal l r =>
      show A.E (A.apply σ (A.apply π.forward l)) (A.apply σ (A.apply π.forward r)) ↔
        A.E (A.apply (A.compose σ π.forward) l) (A.apply (A.compose σ π.forward) r)
      rw [A.apply_compose, A.apply_compose]
  | predicate quantifier p =>
      show quantifier.Holds present (fun o => A.E (A.apply σ (A.apply π.forward p)) (A.apply σ (row' o))) ↔
        quantifier.Holds present
          (fun o => A.E (A.apply (A.compose σ π.forward) p) (A.apply (A.compose σ π.forward) (row o)))
      simp only [renamed, A.apply_compose]
  | count p n =>
      show (matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ row' present
          (A.apply π.forward p)).card = n ↔
        (matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) (A.compose σ π.forward) row present p).card = n
      rw [matchesAt_rename π renamed present p]

omit [DecidableEq O] in
/-- **Guards are read through the renaming.** -/
theorem holds_rename_iff (σ : S) :
    (renameFiring π f).Holds (frames A) (renameState π s) (b := PUnit.unit) σ ↔
      f.Holds (frames A) s (b := PUnit.unit) (A.compose σ π.forward) := by
  unfold Firing.Holds
  rw [opened_checks_rename, collectOpened_rename, List.forall_mem_map]
  apply and_congr
  · exact forall₂_congr fun c _ => checkHolds_rename π (row_rename π f s) s.present c
  · rw [List.zip_map_left, List.forall_mem_map]
    refine forall₂_congr fun q _ => ?_
    show matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ
        ((renameFiring π f).row (frames A) (renameState π s)) s.present (A.apply π.forward q.1) = q.2 ↔ _
    rw [matchesAt_rename π (row_rename π f s)]

omit [DecidableEq O] in
theorem holds_congr_apply {σ₁ σ₂ : S} (same : ∀ t, A.apply σ₁ t = A.apply σ₂ t) :
    f.Holds (frames A) s (b := PUnit.unit) σ₁ ↔ f.Holds (frames A) s (b := PUnit.unit) σ₂ := by
  have matches' : ∀ p, matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ₁
      (f.row (frames A) s) s.present p =
      matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ₂ (f.row (frames A) s) s.present p := by
    intro p
    ext o
    rw [mem_matchesAt, mem_matchesAt]
    show (o ∈ s.present ∧ A.E (A.apply σ₁ p) (A.apply σ₁ (f.row (frames A) s o))) ↔
      (o ∈ s.present ∧ A.E (A.apply σ₂ p) (A.apply σ₂ (f.row (frames A) s o)))
    rw [same, same]
  unfold Firing.Holds
  apply and_congr
  · refine forall₂_congr fun c _ => ?_
    cases c with
    | equal l r =>
        show A.E (A.apply σ₁ l) (A.apply σ₁ r) ↔ A.E (A.apply σ₂ l) (A.apply σ₂ r)
        rw [same, same]
    | predicate quantifier p =>
        show quantifier.Holds s.present (fun o => A.E (A.apply σ₁ p) (A.apply σ₁ (f.row (frames A) s o))) ↔
          quantifier.Holds s.present (fun o => A.E (A.apply σ₂ p) (A.apply σ₂ (f.row (frames A) s o)))
        simp only [same]
    | count p n =>
        show (matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ₁ _ _ p).card = n ↔
          (matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ₂ _ _ p).card = n
        rw [matches' p]
  · refine forall₂_congr fun q _ => ?_
    show matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ₁ _ _ q.1 = q.2 ↔
      matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ₂ _ _ q.1 = q.2
    rw [matches' q.1]

omit [DecidableEq O] in
theorem mentions_rename {t : T} :
    (renameState π s).Mentions t ↔ ∃ t₀, s.Mentions t₀ ∧ t = A.apply π.forward t₀ := by
  constructor
  · rintro (first | second | ⟨o, present, rfl⟩)
    · obtain ⟨e, member, rfl⟩ := List.mem_map.mp first
      obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp member
      exact ⟨e₀.1, Or.inl (List.mem_map.mpr ⟨e₀, inside, rfl⟩), rfl⟩
    · obtain ⟨e, member, rfl⟩ := List.mem_map.mp second
      obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp member
      exact ⟨e₀.2, Or.inr (Or.inl (List.mem_map.mpr ⟨e₀, inside, rfl⟩)), rfl⟩
    · exact ⟨s.label o, Or.inr (Or.inr ⟨o, present, rfl⟩), rfl⟩
  · rintro ⟨t₀, first | second | ⟨o, present, rfl⟩, rfl⟩
    · obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp first
      exact Or.inl (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨e₀, inside, rfl⟩, rfl⟩)
    · obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp second
      exact Or.inr (Or.inl (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨e₀, inside, rfl⟩, rfl⟩))
    · exact Or.inr (Or.inr ⟨o, present, rfl⟩)

omit [DecidableEq O] in
/-- **Freshness is read through the renaming.** -/
theorem fresh_rename_iff :
    (renameFiring π f).Fresh (frames A) (renameState π s) ↔ f.Fresh (frames A) s := by
  constructor
  · intro fresh b g h
    obtain ⟨u, onState, onRule⟩ := fresh b (A.compose g π.backward) h
    refine ⟨A.compose u π.forward, fun t₀ mentioned => ?_, fun t member => ?_⟩
    · have viaU : A.E (A.apply u (A.apply A.identity (A.apply π.forward t₀)))
          (A.apply (A.compose g π.backward) (A.apply π.forward t₀)) :=
        onState _ ((mentions_rename π s).mpr ⟨t₀, mentioned, rfl⟩)
      rw [A.apply_identity, A.apply_compose, π.back_forward] at viaU
      show A.E (A.apply (A.compose u π.forward) (A.apply A.identity t₀)) (A.apply g t₀)
      rw [A.apply_identity, A.apply_compose]
      exact viaU
    · have viaU : A.E (A.apply u (A.apply (A.compose π.forward f.opening) t)) (A.apply h t) :=
        onRule t member
      rw [A.apply_compose] at viaU
      show A.E (A.apply (A.compose u π.forward) (A.apply f.opening t)) (A.apply h t)
      rw [A.apply_compose]
      exact viaU
  · intro fresh b g h
    obtain ⟨u, onState, onRule⟩ := fresh b (A.compose g π.forward) h
    refine ⟨A.compose u π.backward, fun t mentioned => ?_, fun t member => ?_⟩
    · obtain ⟨t₀, mentioned₀, rfl⟩ := (mentions_rename π s).mp mentioned
      have viaU : A.E (A.apply u (A.apply A.identity t₀)) (A.apply (A.compose g π.forward) t₀) :=
        onState t₀ mentioned₀
      rw [A.apply_identity, A.apply_compose] at viaU
      show A.E (A.apply (A.compose u π.backward) (A.apply A.identity (A.apply π.forward t₀)))
        (A.apply g (A.apply π.forward t₀))
      rw [A.apply_identity, A.apply_compose, π.back_forward]
      exact viaU
    · have viaU : A.E (A.apply u (A.apply f.opening t)) (A.apply h t) := onRule t member
      show A.E (A.apply (A.compose u π.backward) (A.apply (A.compose π.forward f.opening) t))
        (A.apply h t)
      rw [A.apply_compose, A.apply_compose, π.back_forward]
      exact viaU

/-- **The renamed firing is admitted at the renamed state exactly when the firing is admitted.** -/
theorem admits_rename_iff :
    (step (frames A) O (ext A) P).Admits (s := renameState π s) (renameFiring π f) ↔
      (step (frames A) O (ext A) P).Admits (s := s) f := by
  have solvable : (frames A).Solvable (a := PUnit.unit) (renameStore π (f.information (frames A) s)) ↔
      (frames A).Solvable (a := PUnit.unit) (f.information (frames A) s) := by
    constructor
    · rintro ⟨_, σ, solved⟩
      exact ⟨PUnit.unit, A.compose σ π.forward, (models_renameStore π σ _).mp solved⟩
    · rintro ⟨_, σ, solved⟩
      refine ⟨PUnit.unit, A.compose σ π.backward, (models_renameStore π _ _).mpr ?_⟩
      exact (models_congr_apply (apply_undo π σ) _).mpr solved
  have entails : (frames A).Entails (a := PUnit.unit) (renameStore π (f.information (frames A) s))
        (fun _ σ => (renameFiring π f).Holds (frames A) (renameState π s) (b := PUnit.unit) σ) ↔
      (frames A).Entails (a := PUnit.unit) (f.information (frames A) s)
        (fun _ σ => f.Holds (frames A) s (b := PUnit.unit) σ) := by
    constructor
    · intro asked b σ solved
      have renamedSolved : A.Models (A.compose σ π.backward) (renameStore π (f.information (frames A) s)) :=
        (models_renameStore π _ _).mpr ((models_congr_apply (apply_undo π σ) _).mpr solved)
      have holds := (holds_rename_iff π f s _).mp (asked PUnit.unit _ renamedSolved)
      exact (holds_congr_apply f s (apply_undo π σ)).mp holds
    · intro asked b σ solved
      exact (holds_rename_iff π f s σ).mpr
        (asked PUnit.unit _ ((models_renameStore π σ _).mp solved))
  show (renameFiring π f).Admits (frames A) (renameState π s) ↔ f.Admits (frames A) s
  unfold Firing.Admits Firing.Shapes
  rw [fresh_rename_iff, information_rename]
  constructor
  · rintro ⟨⟨fresh, rest⟩, enabled, solvable', asked⟩
    exact ⟨⟨fresh, rest⟩, enabled, solvable.mp solvable', entails.mp asked⟩
  · rintro ⟨⟨fresh, rest⟩, enabled, solvable', asked⟩
    exact ⟨⟨fresh, rest⟩, enabled, solvable.mpr solvable', entails.mpr asked⟩

theorem relabel_rename (g : T → T) (old : O → T) (o : O) :
    ∀ (made : List O) (rows : List T),
      relabel (Tm := Terms T) (a := PUnit.unit) (fun o => g (old o)) made (rows.map g) o =
        g (relabel (Tm := Terms T) (a := PUnit.unit) old made rows o)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | o' :: rest, t :: ts => by
      simp only [List.map_cons, relabel]
      split_ifs
      · rfl
      · exact relabel_rename g old o rest ts

/-- **The result of the renamed firing is the renamed result.** -/
theorem result_rename :
    (renameFiring π f).result (frames A) (renameState π s) = renameState π (f.result (frames A) s) := by
  apply state_ext
  · exact information_rename π f s
  · rfl
  · funext o
    show relabel ((renameFiring π f).row (frames A) (renameState π s)) f.selection.made
        ((renameFiring π f).opened (frames A)).produce o =
      A.apply π.forward (relabel (f.row (frames A) s) f.selection.made (f.opened (frames A)).produce o)
    rw [opened_produce_rename]
    have rows : (renameFiring π f).row (frames A) (renameState π s) =
        fun o => A.apply π.forward (f.row (frames A) s o) := funext (row_rename π f s)
    rw [rows]
    exact relabel_rename (A.apply π.forward) (f.row (frames A) s) o _ _

end Equivariance

/-! ## The bisimulation -/

section Bisimulation

variable {P : Program (Terms T)} (π : Renaming A)

/-- **The successors of a renamed state are exactly the renamed successors**, for every program. -/
theorem succ_rename_iff (s t : State (Terms T) O) :
    Succ (step (frames A) O (ext A) P).toStep (renameState π s) t ↔
      ∃ s', Succ (step (frames A) O (ext A) P).toStep s s' ∧ t = renameState π s' := by
  constructor
  · rintro ⟨g, admitted, rfl⟩
    have back : (step (frames A) O (ext A) P).Admits (s := renameState π.symm (renameState π s))
        (renameFiring π.symm g) := (admits_rename_iff π.symm g (renameState π s)).mpr admitted
    rw [renameState_symm] at back
    refine ⟨_, ⟨renameFiring π.symm g, back, rfl⟩, ?_⟩
    show g.result (frames A) (renameState π s) = renameState π ((renameFiring π.symm g).result (frames A) s)
    rw [← result_rename, renameFiring_symm]
  · rintro ⟨s', ⟨f, admitted, rfl⟩, rfl⟩
    exact ⟨renameFiring π f, (admits_rename_iff π f s).mpr admitted, result_rename π f s⟩

/-- Runs lift to the renamed state. -/
theorem reach_rename {s s' : State (Terms T) O}
    (run : Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s s') :
    Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (renameState π s)
      (renameState π s') := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih => exact ih.tail ((succ_rename_iff π _ _).mpr ⟨_, last, rfl⟩)

/-- Runs from the renamed state are renamed runs. -/
theorem reach_of_rename {s : State (Terms T) O} {t : State (Terms T) O}
    (run : Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (renameState π s) t) :
    ∃ s', Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s s' ∧
      t = renameState π s' := by
  induction run with
  | refl => exact ⟨s, Relation.ReflTransGen.refl, rfl⟩
  | tail _ last ih =>
      obtain ⟨s', run', rfl⟩ := ih
      obtain ⟨s'', step', rfl⟩ := (succ_rename_iff π _ _).mp last
      exact ⟨s'', run'.tail step', rfl⟩

omit [DecidableEq O] in
theorem succeeds_rename_iff {barb : T → Prop} (fixed : ∀ t, barb (A.apply π.forward t) ↔ barb t)
    (s : State (Terms T) O) : Succeeds barb (renameState π s) ↔ Succeeds barb s := by
  constructor
  · rintro ⟨o, present, holds⟩
    exact ⟨o, present, (fixed _).mp holds⟩
  · rintro ⟨o, present, holds⟩
    exact ⟨o, present, (fixed _).mpr holds⟩

/-- **Reachable success is the same at a state and at its renaming**, for a barb the renaming
fixes. -/
theorem reaches_rename_iff {barb : T → Prop} (fixed : ∀ t, barb (A.apply π.forward t) ↔ barb t)
    (s : State (Terms T) O) :
    (∃ t, Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (renameState π s) t ∧
        Succeeds barb t) ↔
      ∃ t, Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t ∧ Succeeds barb t := by
  constructor
  · rintro ⟨t, run, holds⟩
    obtain ⟨s', run', rfl⟩ := reach_of_rename π run
    exact ⟨s', run', (succeeds_rename_iff π fixed s').mp holds⟩
  · rintro ⟨t, run, holds⟩
    exact ⟨_, reach_rename π run, (succeeds_rename_iff π fixed t).mpr holds⟩

end Bisimulation

/-! ## Scope extension -/

section ScopeExtension

variable (π : Renaming A)

/-- **Renaming two systems side by side renames each.** -/
theorem renameState_beside (D C : State (Terms T) O) :
    renameState π (beside D C) = beside (renameState π D) (renameState π C) := by
  apply state_ext
  · show renameStore π (D.knowledge ++ C.knowledge) = renameStore π D.knowledge ++ renameStore π C.knowledge
    simp only [renameStore, List.map_append]
  · rfl
  · funext o
    show A.apply π.forward (if o ∈ D.present then D.label o else C.label o) =
      if o ∈ D.present then A.apply π.forward (D.label o) else A.apply π.forward (C.label o)
    split_ifs <;> rfl

/-- **A renaming that fixes every term a neighbour mentions does not change the neighbour beside
any system.** -/
theorem beside_rename_of_fixed {D : State (Terms T) O}
    (fixed : ∀ t, D.Mentions t → A.apply π.forward t = t) (C : State (Terms T) O) :
    beside (renameState π D) C = beside D C := by
  apply state_ext
  · show renameStore π D.knowledge ++ C.knowledge = D.knowledge ++ C.knowledge
    congr 1
    unfold renameStore
    conv_rhs => rw [← List.map_id D.knowledge]
    apply List.map_congr_left
    intro e member
    show (A.apply π.forward e.1, A.apply π.forward e.2) = e
    rw [fixed e.1 (Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩)),
      fixed e.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩)))]
  · rfl
  · funext o
    show (if o ∈ D.present then A.apply π.forward (D.label o) else C.label o) =
      if o ∈ D.present then D.label o else C.label o
    split_ifs with inD
    · exact fixed _ (Or.inr (Or.inr ⟨o, inD, rfl⟩))
    · rfl

/-- **Scope extension**: beside a neighbour whose terms the renaming fixes, renaming the system is
renaming the whole composition. -/
theorem scope_extension {D : State (Terms T) O} (fixed : ∀ t, D.Mentions t → A.apply π.forward t = t)
    (C : State (Terms T) O) : renameState π (beside D C) = beside D (renameState π C) := by
  rw [renameState_beside, beside_rename_of_fixed π fixed]

/-- **Reachable success beside such a neighbour is the same for the system and for its renaming**,
for every program and every barb the renaming fixes. -/
theorem reaches_scope_extension {P : Program (Terms T)} {barb : T → Prop}
    (fixedBarb : ∀ t, barb (A.apply π.forward t) ↔ barb t) {D : State (Terms T) O}
    (fixed : ∀ t, D.Mentions t → A.apply π.forward t = t) (C : State (Terms T) O) :
    (∃ t, Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (beside D (renameState π C)) t ∧
        Succeeds barb t) ↔
      ∃ t, Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (beside D C) t ∧
        Succeeds barb t := by
  rw [← scope_extension π fixed]
  exact reaches_rename_iff π fixedBarb (beside D C)

end ScopeExtension

/-! ## At first-order terms every permutation of the unknowns is a renaming -/

section Permutations

variable {sig : LPSignature}

/-- The substitution that renames each unknown along a permutation. -/
def permSubst (e : sig.vars ≃ sig.vars) : Subst sig := fun v => Term.var (e v)

theorem permSubst_cancel (e : sig.vars ≃ sig.vars) (t : Term sig) :
    Subst.applyTerm (permSubst e.symm) (Subst.applyTerm (permSubst e) t) = t := by
  rw [← Subst.applyTerm_comp]
  have identity : Subst.comp (permSubst e.symm) (permSubst e) = Subst.id sig := by
    funext v
    show Subst.applyTerm (permSubst e.symm) (Term.var (e v)) = Term.var v
    show Term.var (e.symm (e v)) = Term.var v
    rw [e.symm_apply_apply]
  rw [identity, Subst.applyTerm_id]

/-- **A permutation of the unknowns is a renaming.** -/
def permutation (e : sig.vars ≃ sig.vars) : Renaming (FirstOrder.action sig) where
  forward := permSubst e
  backward := permSubst e.symm
  back_forward t := permSubst_cancel e t
  forward_back t := by
    have := permSubst_cancel e.symm t
    rwa [e.symm_symm] at this
  compose_back σ := by
    funext v
    show Subst.applyTerm (permSubst e) (Subst.applyTerm (permSubst e.symm) (σ v)) = σ v
    have := permSubst_cancel e.symm (σ v)
    rwa [e.symm_symm] at this
  compose_forward σ := by
    funext v
    exact permSubst_cancel e (σ v)

end Permutations

#print axioms models_renameStore
#print axioms information_rename
#print axioms holds_rename_iff
#print axioms fresh_rename_iff
#print axioms admits_rename_iff
#print axioms result_rename
#print axioms succ_rename_iff
#print axioms reaches_rename_iff
#print axioms renameState_beside
#print axioms beside_rename_of_fixed
#print axioms scope_extension
#print axioms reaches_scope_extension
#print axioms permutation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope
