import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Congruence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.CheckAccepts

/-!
# Renaming the occurrence identities is a law

An occurrence identity is an address: no rule can name one. Renaming the identities of a state by a
permutation (`renameState`) moves each row, with its label, to the renamed identity.

**The step is equivariant.** A firing renamed by the same permutation (`renameFiring`: the same rule,
extension and opening; the selected identities and the claimed collected rows renamed)

* sees the same terms, so its opening is fresh exactly when the original is (`fresh_renameFiring`);
* has the same information (`information_renameFiring`), the same checks and collect query at every solution
  (`holds_renameFiring`), and is enabled exactly when the original is (`enabled_renameSelection`);
* is admitted exactly when the original is (`admits_renameFiring`), with the renamed result
  (`result_renameFiring`).

Contexts commute with renaming, the context's added identities renamed too (`apply_rename`,
`applies_rename`), and may- and must-barbs do not see identities (`mayBarb_renameState`,
`mustBarb_renameState`).

**Law 1** (`rename_congruent`): for every frame action, extensions, program, state and permutation,
and every barb family that does not see identities, a system and its renamed copy are congruent.
`rename_congruent_mayBarb` is the instance for the chosen barbs. Two different systems are thus
related (non-vacuity), for instance one row at identity `0` against the same row at identity `1`.

The hypothesis on contexts that matters is that an added row's identity is absent from the system:
`AtOneFrame.overlap_separates` shows that a context allowed to overwrite a present identity separates a
state from its renamed copy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

section States

variable {O : Type uOcc}

/-- **A state with its identities renamed**: the row at `o` moves to `π o`. -/
def renameState (π : Equiv.Perm O) (s : State Tm O) : State Tm O :=
  ⟨s.frame, s.knowledge, s.present.map π.toEmbedding, fun o => s.label (π.symm o)⟩

theorem renameState_symm (π : Equiv.Perm O) (s : State Tm O) :
    renameState π.symm (renameState π s) = s := by
  cases s with
  | mk frame knowledge present label =>
      have presentSame : (present.map π.toEmbedding).map π.symm.toEmbedding = present := by
        ext o
        rw [Finset.mem_map_equiv, Finset.mem_map_equiv]
        simp
      simp only [renameState, presentSame, Equiv.symm_symm, Equiv.symm_apply_apply]

/-- **A renamed state mentions the same terms.** -/
theorem mentions_renameState (π : Equiv.Perm O) (s : State Tm O) (t : Tm s.frame) :
    (renameState π s).Mentions t ↔ s.Mentions t := by
  constructor
  · rintro (inside | inside | ⟨o, present, same⟩)
    · exact Or.inl inside
    · exact Or.inr (Or.inl inside)
    · obtain ⟨o', present', rfl⟩ := Finset.mem_map.mp present
      refine Or.inr (Or.inr ⟨o', present', ?_⟩)
      rw [← same]
      simp [renameState]
  · rintro (inside | inside | ⟨o, present, same⟩)
    · exact Or.inl inside
    · exact Or.inr (Or.inl inside)
    · refine Or.inr (Or.inr ⟨π o, Finset.mem_map_of_mem _ present, ?_⟩)
      rw [← same]
      simp [renameState]

variable (X : Frames Tm Hom)

/-- **May-barbs do not see identities.** -/
theorem mayBarb_renameState (π : Equiv.Perm O) (p : Pattern Tm) (s : State Tm O) :
    MayBarb X p (renameState π s) ↔ MayBarb X p s := by
  constructor
  · rintro ⟨o, present, b, σ, h, known, equated⟩
    obtain ⟨o', present', rfl⟩ := Finset.mem_map.mp present
    exact ⟨o', present', b, σ, h, known, by simpa [renameState] using equated⟩
  · rintro ⟨o, present, b, σ, h, known, equated⟩
    exact ⟨π o, Finset.mem_map_of_mem _ present, b, σ, h, known, by simpa [renameState] using equated⟩

/-- **Must-barbs do not see identities.** -/
theorem mustBarb_renameState (π : Equiv.Perm O) (p : Pattern Tm) (s : State Tm O) :
    MustBarb X p (renameState π s) ↔ MustBarb X p s := by
  constructor
  · rintro ⟨o, present, every⟩
    obtain ⟨o', present', rfl⟩ := Finset.mem_map.mp present
    exact ⟨o', present', fun b σ known => by simpa [renameState] using every b σ known⟩
  · rintro ⟨o, present, every⟩
    exact ⟨π o, Finset.mem_map_of_mem _ present, fun b σ known => by
      simpa [renameState] using every b σ known⟩

end States

section Firings

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}

/-- **A firing with its identities renamed**: the same rule, extension and opening; the selected
identities and the claimed collected rows renamed. -/
def renameFiring (π : Equiv.Perm O) {P : Program Tm} {a : Obj} (f : Firing O E P a) :
    Firing O E P a :=
  ⟨f.rule, f.member, f.ext, f.opening,
    ⟨f.selection.taken.map π, f.selection.read.map π, f.selection.made.map π⟩,
    f.seen.map (Finset.map π.toEmbedding)⟩

omit [DecidableEq O] in
theorem fresh_renameFiring (π : Equiv.Perm O) {P : Program Tm} {s : State Tm O}
    (f : Firing O E P s.frame) :
    (renameFiring π f).Fresh X (renameState π s) ↔ f.Fresh X s := by
  constructor
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b g h
    exact ⟨u, fun t mentioned => state t ((mentions_renameState π s t).mpr mentioned), rule⟩
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b g h
    exact ⟨u, fun t mentioned => state t ((mentions_renameState π s t).mp mentioned), rule⟩

omit [DecidableEq O] in
/-- **A renamed firing has the same information.** -/
theorem information_renameFiring (π : Equiv.Perm O) {P : Program Tm} {s : State Tm O}
    (f : Firing O E P s.frame) :
    (renameFiring π f).information X (renameState π s) = f.information X s := by
  have rows : ∀ (patterns : List (Tm (E.target f.ext))) (selected : List O),
      patterns.zipWith (fun p o => (p, X.act (E.weaken f.ext) (s.label (π.symm o))))
          (selected.map π) =
        patterns.zipWith (fun p o => (p, X.act (E.weaken f.ext) (s.label o))) selected := by
    intro patterns selected
    rw [List.zipWith_map_right]
    simp only [Equiv.symm_apply_apply]
  show X.applyStore (E.weaken f.ext) s.knowledge ++
      (f.opened X).take.zipWith (fun p o => (p, X.act (E.weaken f.ext) (s.label (π.symm o))))
        (f.selection.taken.map π) ++
      (f.opened X).read.zipWith (fun p o => (p, X.act (E.weaken f.ext) (s.label (π.symm o))))
        (f.selection.read.map π) ++
      (f.opened X).tell = _
  rw [rows, rows]
  rfl

omit [DecidableEq O] in
/-- The rows a solution equates with a pattern, after renaming, are the renamed rows. -/
theorem matchesAt_rename {a b : Obj} (σ : Hom a b) (row : O → Tm a) (W : Finset O) (p : Tm a)
    (π : Equiv.Perm O) :
    matchesAt X σ (fun o => row (π.symm o)) (W.map π.toEmbedding) p =
      (matchesAt X σ row W p).map π.toEmbedding := by
  ext o
  rw [mem_matchesAt, Finset.mem_map_equiv, Finset.mem_map_equiv, mem_matchesAt]

omit [DecidableEq O] in
theorem checkHolds_rename {a b : Obj} (σ : Hom a b) (row : O → Tm a) (W : Finset O)
    (c : Check (Tm a)) (π : Equiv.Perm O) :
    checkHolds X σ (fun o => row (π.symm o)) (W.map π.toEmbedding) c ↔ checkHolds X σ row W c := by
  cases c with
  | equal left right => exact Iff.rfl
  | predicate quantifier pattern =>
      rw [checkHolds_predicate_iff, checkHolds_predicate_iff, matchesAt_rename]
      cases quantifier <;> simp [Quantifier.Accepts]
  | count pattern number =>
      show (matchesAt X σ (fun o => row (π.symm o)) (W.map π.toEmbedding) pattern).card = number ↔
        (matchesAt X σ row W pattern).card = number
      rw [matchesAt_rename, Finset.card_map]

omit [DecidableEq O] in
/-- **A renamed firing has the same checks and collect query at every solution.** -/
theorem holds_renameFiring (π : Equiv.Perm O) {P : Program Tm} {s : State Tm O}
    (f : Firing O E P s.frame) {b : Obj} (σ : Hom (E.target f.ext) b) :
    (renameFiring π f).Holds X (renameState π s) σ ↔ f.Holds X s σ := by
  apply and_congr
  · exact forall₂_congr fun c _ => checkHolds_rename X σ (f.row X s) s.present c π
  · show (∀ q ∈ (f.collectOpened X).zip (f.seen.map (Finset.map π.toEmbedding)),
        matchesAt X σ (fun o => f.row X s (π.symm o)) (s.present.map π.toEmbedding) q.1 = q.2) ↔
      ∀ q ∈ (f.collectOpened X).zip f.seen, matchesAt X σ (f.row X s) s.present q.1 = q.2
    rw [List.zip_map_right, List.forall_mem_map]
    apply forall₂_congr
    intro q _
    simp only [Prod.map_fst, Prod.map_snd, id_eq]
    rw [matchesAt_rename]
    exact Finset.map_inj

theorem toFinset_map_perm (π : Equiv.Perm O) (l : List O) :
    (l.map π).toFinset = l.toFinset.map π.toEmbedding := by
  ext o
  rw [List.mem_toFinset, Finset.mem_map_equiv, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, inside, rfl⟩
    simpa using inside
  · intro inside
    exact ⟨π.symm o, inside, by simp⟩

/-- The commit of a renamed selection. -/
theorem commit_renameSelection (π : Equiv.Perm O) (selection : Selection O) :
    (⟨selection.taken.map π, selection.read.map π, selection.made.map π⟩ : Selection O).commit
        (T := Unit) =
      ⟨selection.taken.toFinset.map π.toEmbedding, selection.read.toFinset.map π.toEmbedding,
        selection.made.toFinset.map π.toEmbedding, []⟩ := by
  simp only [Selection.commit, toFinset_map_perm]

/-- **A renamed selection is enabled at the renamed store exactly when the original is.** -/
theorem enabled_renameSelection (π : Equiv.Perm O) (W : Finset O) (selection : Selection O) :
    Enabled (fun _ : O => ()) (W.map π.toEmbedding)
        ((⟨selection.taken.map π, selection.read.map π, selection.made.map π⟩ : Selection O).commit
          (T := Unit)) ↔
      Enabled (fun _ : O => ()) W (selection.commit (T := Unit)) := by
  rw [commit_renameSelection]
  constructor
  · rintro ⟨taken, kept, apart, fresh, -⟩
    exact ⟨Finset.map_subset_map.mp taken, Finset.map_subset_map.mp kept,
      (Finset.disjoint_map _).mp apart, (Finset.disjoint_map _).mp fresh,
      fun q member => by simp [Selection.commit] at member⟩
  · rintro ⟨taken, kept, apart, fresh, -⟩
    exact ⟨Finset.map_subset_map.mpr taken, Finset.map_subset_map.mpr kept,
      (Finset.disjoint_map _).mpr apart, (Finset.disjoint_map _).mpr fresh,
      fun q member => absurd member List.not_mem_nil⟩

/-- **A renamed firing is admitted at the renamed state exactly when the original is.** -/
theorem admits_renameFiring (π : Equiv.Perm O) {P : Program Tm} {s : State Tm O}
    (f : Firing O E P s.frame) :
    (renameFiring π f).Admits X (renameState π s) ↔ f.Admits X s := by
  have info := information_renameFiring X π f
  refine and_congr (and_congr (fresh_renameFiring X π f) ?_)
    (and_congr (enabled_renameSelection π s.present f.selection) (and_congr ?_ ?_))
  · simp only [renameFiring, List.nodup_map_iff π.injective, List.length_map]
  · exact (congrArg (X.Solvable (a := E.target f.ext)) info).to_iff
  · rw [info]
    exact forall₂_congr fun _ σ => imp_congr_right fun _ => holds_renameFiring X π f σ

/-- Relabelling commutes with renaming. -/
theorem relabel_rename (π : Equiv.Perm O) {a : Obj} (old : O → Tm a) :
    ∀ (made : List O) (rows : List (Tm a)) (o : O),
      relabel (fun o => old (π.symm o)) (made.map π) rows o = relabel old made rows (π.symm o)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | m :: rest, t :: ts, o => by
      simp only [List.map_cons, relabel]
      by_cases same : o = π m
      · subst same
        simp
      · have other : π.symm o ≠ m := fun h => same (by rw [← h]; simp)
        rw [if_neg same, if_neg other]
        exact relabel_rename π old rest ts o

theorem fire_rename (π : Equiv.Perm O) (W : Finset O) (selection : Selection O) :
    fire (W.map π.toEmbedding)
        ((⟨selection.taken.map π, selection.read.map π, selection.made.map π⟩ : Selection O).commit
          (T := Unit)) =
      (fire W (selection.commit (T := Unit))).map π.toEmbedding := by
  rw [commit_renameSelection]
  simp only [fire, Selection.commit, Finset.map_union, Finset.map_sdiff]

/-- **A renamed firing has the renamed result.** -/
theorem result_renameFiring (π : Equiv.Perm O) {P : Program Tm} {s : State Tm O}
    (f : Firing O E P s.frame) :
    (renameFiring π f).result X (renameState π s) = renameState π (f.result X s) := by
  show (⟨E.target f.ext, (renameFiring π f).information X (renameState π s),
      fire (s.present.map π.toEmbedding)
        ((⟨f.selection.taken.map π, f.selection.read.map π, f.selection.made.map π⟩ :
          Selection O).commit (T := Unit)),
      relabel (fun o => f.row X s (π.symm o)) (f.selection.made.map π) (f.opened X).produce⟩ :
        State Tm O) =
    ⟨E.target f.ext, f.information X s, (fire s.present (f.selection.commit (T := Unit))).map
      π.toEmbedding, fun o => relabel (f.row X s) f.selection.made (f.opened X).produce (π.symm o)⟩
  rw [information_renameFiring, fire_rename]
  congr 1
  funext o
  exact relabel_rename π (f.row X s) _ _ o

/-- **Reductions are equivariant.** -/
theorem reduces_rename (π : Equiv.Perm O) {S S' : System Tm O} (moved : Reduces X O E S S') :
    Reduces X O E ⟨S.program, renameState π S.state⟩ ⟨S'.program, renameState π S'.state⟩ := by
  obtain ⟨same, f, admitted, reached⟩ := moved
  refine ⟨same, renameFiring π f, (admits_renameFiring X π f).mpr admitted, ?_⟩
  show (renameFiring π f).result X (renameState π S.state) = renameState π S'.state
  rw [result_renameFiring]
  exact congrArg (renameState π) reached

/-- **Contexts commute with renaming**, their added identities renamed too. -/
theorem apply_rename (π : Equiv.Perm O) (c : Basic Tm O E) (P : Program Tm) (s : State Tm O) :
    (c.rename π).apply X ⟨P, renameState π s⟩ =
      ⟨(c.apply X ⟨P, s⟩).program, renameState π (c.apply X ⟨P, s⟩).state⟩ := by
  cases c with
  | rows ids label =>
      show (⟨P, addRows (renameState π s) (ids.map π.toEmbedding)
          (fun o => label s.frame (π.symm o))⟩ : System Tm O) =
        ⟨P, renameState π (addRows s ids (label s.frame))⟩
      simp only [addRows, renameState, Finset.map_union, Finset.mem_map_equiv]
  | rules added => rfl
  | tell equations => rfl
  | extend extension => rfl

omit [DecidableEq O] in
theorem applies_rename (π : Equiv.Perm O) (c : Basic Tm O E) (P : Program Tm) (s : State Tm O) :
    (c.rename π).Applies ⟨P, renameState π s⟩ ↔ c.Applies ⟨P, s⟩ := by
  unfold Basic.Applies
  rw [Basic.ids_rename]
  exact Finset.disjoint_map π.toEmbedding

end Firings

/-! ## Law 1 -/

section Law

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

/-- **Law 1: renaming the identities.** For a barb family that does not see identities, every system
is congruent to its copy with renamed identities. -/
theorem rename_congruent (invariant : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (π : Equiv.Perm O) (S : System Tm O) :
    Congruent X O E obs S ⟨S.program, renameState π S.state⟩ := by
  let R : System Tm O → System Tm O → Prop := fun S T =>
    T.program = S.program ∧ ∃ π : Equiv.Perm O, T.state = renameState π S.state
  have shape : ∀ {S T : System Tm O} (π : Equiv.Perm O), T.program = S.program →
      T.state = renameState π S.state → T = ⟨S.program, renameState π S.state⟩ := by
    intro S T π program state
    obtain ⟨TP, Ts⟩ := T
    simp only [System.mk.injEq]
    exact ⟨program, state⟩
  have candidate : Candidate X O E obs R := {
    symm := by
      rintro S T ⟨program, π, state⟩
      refine ⟨program.symm, π.symm, ?_⟩
      rw [state, renameState_symm]
    barbs := by
      rintro S T ⟨-, π, state⟩ β holds
      rw [state, invariant]
      exact holds
    reduces := by
      rintro S T ⟨program, π, state⟩ S' moved
      have same := shape π program state
      subst same
      exact ⟨⟨S'.program, renameState π S'.state⟩, reduces_rename X π moved, rfl, π, rfl⟩
    context := by
      rintro S T ⟨program, π, state⟩ c applies
      have same := shape π program state
      subst same
      refine ⟨π, (applies_rename π c S.program S.state).mpr applies, ?_⟩
      rw [apply_rename]
      exact ⟨rfl, π, rfl⟩ }
  exact candidate.le_congruent ⟨rfl, π, rfl⟩

/-- **Law 1 for the chosen barbs.** -/
theorem rename_congruent_mayBarb (π : Equiv.Perm O) (P : Program Tm) (s : State Tm O) :
    Congruent X O E (MayBarb X) ⟨P, s⟩ ⟨P, renameState π s⟩ :=
  rename_congruent (fun π p s => mayBarb_renameState X π p s) π ⟨P, s⟩

end Law

#print axioms renameState_symm
#print axioms mentions_renameState
#print axioms mayBarb_renameState
#print axioms mustBarb_renameState
#print axioms fresh_renameFiring
#print axioms information_renameFiring
#print axioms holds_renameFiring
#print axioms enabled_renameSelection
#print axioms admits_renameFiring
#print axioms relabel_rename
#print axioms result_renameFiring
#print axioms reduces_rename
#print axioms apply_rename
#print axioms applies_rename
#print axioms rename_congruent
#print axioms rename_congruent_mayBarb

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
