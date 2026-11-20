import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.AbsorptionMoves

/-!
# Backward: a firing at one more row `5` is answered without it

A firing of any rule at `fiveMore a d` is answered at `a` by `dropRow`, a positive rule: the same rule
without its checks and collect query, whose takes and reads of the row `d` become tells of `5`, with the same
opening; when the firing
keeps `d`, the answer also makes one row `5` at an identity missing from everything
(`answer_backward`). The informations have the same equations (`mem_information_dropRow`), and the
results are statically equivalent: equal when `d` is taken, and equal up to exchanging the made row
with `d` when it is kept.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves fresh_identity)

/-- **The rule without its checks, its takes and reads of `d` turned into tells of `5`, making
`extra` more rows.** -/
def dropRow (r : Rule Tm) (T Rd : List ℕ) (d : ℕ) (extra : List (Term atoms)) : Rule Tm :=
  ⟨r.locals, ⟨(keepAway (r.body.take.zip T) d).map Prod.fst,
    (keepAway (r.body.read.zip Rd) d).map Prod.fst,
    r.body.tell ++ (atRow (r.body.take.zip T) d ++ atRow (r.body.read.zip Rd) d).map
      (fun q => (q.1, c 5)), [], r.body.produce ++ extra⟩, []⟩

theorem terms_dropRow (r : Rule Tm) (T Rd : List ℕ) (d : ℕ) {extra : List (Term atoms)}
    (constant : ∀ t ∈ extra, IsConst t) (t : Term atoms)
    (inside : t ∈ (dropRow r T Rd d extra).terms) : t ∈ r.terms ∨ IsConst t := by
  -- A pattern of a dropped pair is a take or read pattern of the rule.
  have dropped : ∀ q ∈ atRow (r.body.take.zip T) d ++ atRow (r.body.read.zip Rd) d,
      q.1 ∈ r.terms := by
    intro q member
    rcases List.mem_append.mp member with fromTake | fromRead
    · exact AtOneFrame.mem_terms (Or.inl (List.of_mem_zip (mem_atRow.mp fromTake).1).1)
    · exact AtOneFrame.mem_terms (Or.inr (Or.inl (List.of_mem_zip (mem_atRow.mp fromRead).1).1))
  have h : t ∈ (keepAway (r.body.take.zip T) d).map Prod.fst ++
      (keepAway (r.body.read.zip Rd) d).map Prod.fst ++
      (r.body.tell ++ (atRow (r.body.take.zip T) d ++ atRow (r.body.read.zip Rd) d).map
        (fun q => (q.1, c 5))).map Prod.fst ++
      (r.body.tell ++ (atRow (r.body.take.zip T) d ++ atRow (r.body.read.zip Rd) d).map
        (fun q => (q.1, c 5))).map Prod.snd ++
      ([] : List (Check (Term atoms))).flatMap checkTerms ++ (r.body.produce ++ extra) ++ [] := inside
  rcases List.mem_append.mp h with h | none
  swap
  · exact absurd none List.not_mem_nil
  rcases List.mem_append.mp h with h | made
  swap
  · rcases List.mem_append.mp made with old | new
    · exact Or.inl (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl old)))))))
    · exact Or.inr (constant t new)
  rcases List.mem_append.mp h with h | none
  swap
  · exact absurd none (by simp)
  rcases List.mem_append.mp h with h | second
  swap
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp second
    rcases List.mem_append.mp member with old | new
    · exact Or.inl (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_map_of_mem old))))))
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp new
      exact Or.inr ⟨5, rfl⟩
  rcases List.mem_append.mp h with h | first
  swap
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp first
    rcases List.mem_append.mp member with old | new
    · exact Or.inl (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inl (List.mem_map_of_mem old)))))
    · obtain ⟨q, fromPair, rfl⟩ := List.mem_map.mp new
      exact Or.inl (dropped q fromPair)
  rcases List.mem_append.mp h with take | read
  · obtain ⟨q, member, rfl⟩ := List.mem_map.mp take
    exact Or.inl (AtOneFrame.mem_terms (Or.inl (List.of_mem_zip (mem_keepAway.mp member).1).1))
  · obtain ⟨q, member, rfl⟩ := List.mem_map.mp read
    exact Or.inl (AtOneFrame.mem_terms (Or.inr (Or.inl
      (List.of_mem_zip (mem_keepAway.mp member).1).1)))

/-- The answering firing. -/
def dropFiring {a : State Tm ℕ} {d : ℕ} (g : Firing ℕ E everyRule (fiveMore a d).frame)
    (extra : List (Term atoms)) (ms : List ℕ) : Firing ℕ E everyRule a.frame :=
  ⟨dropRow g.rule g.selection.taken g.selection.read d extra, Set.mem_univ _, g.ext, g.opening,
    ⟨(keepAway (g.rule.body.take.zip g.selection.taken) d).map Prod.snd,
      (keepAway (g.rule.body.read.zip g.selection.read) d).map Prod.snd, g.selection.made ++ ms⟩, []⟩

/-- **The answer has the equations of the firing.** -/
theorem mem_information_dropRow {a : State Tm ℕ} {d : ℕ}
    (g : Firing ℕ E everyRule (fiveMore a d).frame) (extra : List (Term atoms)) (ms : List ℕ)
    (e : Equation (Term atoms)) :
    e ∈ (dropFiring g extra ms).information X a ↔ e ∈ g.information X (fiveMore a d) := by
  let f := dropFiring g extra ms
  have rowAgree : ∀ o, o ≠ d → f.row X a o = g.row X (fiveMore a d) o := fun o other => by
    show Subst.applyTerm (Subst.id atoms) (a.label o) =
      Subst.applyTerm (Subst.id atoms) ((fiveMore a d).label o)
    rw [label_fiveMore_of_ne other]
  have rowD : g.row X (fiveMore a d) d = c 5 := by
    show Subst.applyTerm (Subst.id atoms) ((fiveMore a d).label d) = c 5
    rw [label_fiveMore_self]
    rfl
  have fTake : (f.opened X).take.zip f.selection.taken =
      (keepAway (g.rule.body.take.zip g.selection.taken) d).map
        fun q => (Subst.applyTerm g.opening q.1, q.2) := zip_map_pairs _ _
  have fRead : (f.opened X).read.zip f.selection.read =
      (keepAway (g.rule.body.read.zip g.selection.read) d).map
        fun q => (Subst.applyTerm g.opening q.1, q.2) := zip_map_pairs _ _
  have gTake : (g.opened X).take.zip g.selection.taken =
      (g.rule.body.take.zip g.selection.taken).map
        fun q => (Subst.applyTerm g.opening q.1, q.2) := zip_map_left' _ _ _
  have gRead : (g.opened X).read.zip g.selection.read =
      (g.rule.body.read.zip g.selection.read).map
        fun q => (Subst.applyTerm g.opening q.1, q.2) := zip_map_left' _ _ _
  have fTell : ∀ e, e ∈ (f.opened X).tell ↔ e ∈ (g.opened X).tell ∨
      ∃ q ∈ atRow (g.rule.body.take.zip g.selection.taken) d ++
        atRow (g.rule.body.read.zip g.selection.read) d, e = (Subst.applyTerm g.opening q.1, c 5) := by
    intro e
    show e ∈ (g.rule.body.tell ++ (atRow (g.rule.body.take.zip g.selection.taken) d ++
        atRow (g.rule.body.read.zip g.selection.read) d).map (fun q => (q.1, c 5))).map
          (fun pair => (Subst.applyTerm g.opening pair.1, Subst.applyTerm g.opening pair.2)) ↔
      e ∈ g.rule.body.tell.map
          (fun pair => (Subst.applyTerm g.opening pair.1, Subst.applyTerm g.opening pair.2)) ∨ _
    simp only [List.map_append, List.mem_append, List.map_map, List.mem_map, Function.comp]
    constructor
    · rintro (old | ⟨q, member, rfl⟩ | ⟨q, member, rfl⟩)
      · exact Or.inl old
      · exact Or.inr ⟨q, Or.inl member, rfl⟩
      · exact Or.inr ⟨q, Or.inr member, rfl⟩
    · rintro (old | ⟨q, (member | member), rfl⟩)
      · exact Or.inl old
      · exact Or.inr (Or.inl ⟨q, member, rfl⟩)
      · exact Or.inr (Or.inr ⟨q, member, rfl⟩)
  rw [mem_information, mem_information, mem_matching, mem_matching, mem_matching, mem_matching,
    fTake, fRead, gTake, gRead, fTell]
  simp only [List.mem_map, List.mem_append]
  constructor
  · rintro (old | ⟨p, o, ⟨q, member, same⟩, rfl⟩ | ⟨p, o, ⟨q, member, same⟩, rfl⟩ |
      (told | ⟨q, (member | member), rfl⟩))
    · exact Or.inl old
    · obtain ⟨inZip, other⟩ := mem_keepAway.mp member
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact Or.inr (Or.inl ⟨_, _, ⟨q, inZip, rfl⟩, by rw [rowAgree q.2 other]⟩)
    · obtain ⟨inZip, other⟩ := mem_keepAway.mp member
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact Or.inr (Or.inr (Or.inl ⟨_, _, ⟨q, inZip, rfl⟩, by rw [rowAgree q.2 other]⟩))
    · exact Or.inr (Or.inr (Or.inr told))
    · obtain ⟨inZip, atD⟩ := mem_atRow.mp member
      refine Or.inr (Or.inl ⟨_, _, ⟨q, inZip, rfl⟩, ?_⟩)
      show (Subst.applyTerm g.opening q.1, c 5) = (Subst.applyTerm g.opening q.1,
        g.row X (fiveMore a d) q.2)
      rw [atD, rowD]
    · obtain ⟨inZip, atD⟩ := mem_atRow.mp member
      refine Or.inr (Or.inr (Or.inl ⟨_, _, ⟨q, inZip, rfl⟩, ?_⟩))
      show (Subst.applyTerm g.opening q.1, c 5) = (Subst.applyTerm g.opening q.1,
        g.row X (fiveMore a d) q.2)
      rw [atD, rowD]
  · rintro (old | ⟨p, o, ⟨q, member, same⟩, rfl⟩ | ⟨p, o, ⟨q, member, same⟩, rfl⟩ | told)
    · exact Or.inl old
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      by_cases atD : q.2 = d
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨q, Or.inl (mem_atRow.mpr ⟨member, atD⟩), ?_⟩)))
        show (Subst.applyTerm g.opening q.1, g.row X (fiveMore a d) q.2) =
          (Subst.applyTerm g.opening q.1, c 5)
        rw [atD, rowD]
      · exact Or.inr (Or.inl ⟨_, _, ⟨q, mem_keepAway.mpr ⟨member, atD⟩, rfl⟩,
          by rw [rowAgree q.2 atD]⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      by_cases atD : q.2 = d
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨q, Or.inr (mem_atRow.mpr ⟨member, atD⟩), ?_⟩)))
        show (Subst.applyTerm g.opening q.1, g.row X (fiveMore a d) q.2) =
          (Subst.applyTerm g.opening q.1, c 5)
        rw [atD, rowD]
      · exact Or.inr (Or.inr (Or.inl ⟨_, _, ⟨q, mem_keepAway.mpr ⟨member, atD⟩, rfl⟩,
          by rw [rowAgree q.2 atD]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl told)))

/-- The identities a firing takes away from `d` are those it takes, other than `d`. -/
theorem mem_keepAway_snd {ps : List (Term atoms)} {T : List ℕ} (lengths : ps.length = T.length)
    {d o : ℕ} : o ∈ (keepAway (ps.zip T) d).map Prod.snd ↔ o ∈ T ∧ o ≠ d := by
  constructor
  · intro inside
    obtain ⟨q, member, rfl⟩ := List.mem_map.mp inside
    obtain ⟨inZip, other⟩ := mem_keepAway.mp member
    exact ⟨(List.of_mem_zip inZip).2, other⟩
  · rintro ⟨taken, other⟩
    obtain ⟨p, paired⟩ := exists_zip_right ps T lengths o taken
    exact List.mem_map.mpr ⟨(p, o), mem_keepAway.mpr ⟨paired, other⟩, rfl⟩

/-- **The answer is admitted**, making the rows `extra` at the identities `ms`. -/
theorem admits_dropFiring {a : State Tm ℕ} {d : ℕ} (freshD : d ∉ a.present)
    (g : Firing ℕ E everyRule (fiveMore a d).frame) (admitted : g.Admits X (fiveMore a d))
    (extra : List (Term atoms)) (ms : List ℕ) (constant : ∀ t ∈ extra, IsConst t)
    (lengths : extra.length = ms.length) (nodup : (g.selection.made ++ ms).Nodup)
    (apart : ∀ o ∈ ms, o ∉ a.present) : (dropFiring g extra ms).Admits X a := by
  obtain ⟨⟨fresh, takenNodup, -, takeLength, readLength, produceLength, -⟩, enabled, solvable, -⟩ :=
    admitted
  have takenPresent : ∀ o ∈ g.selection.taken, o ∈ (fiveMore a d).present := fun o member =>
    enabled.taken_subset (by simpa [Selection.commit] using member)
  have readPresent : ∀ o ∈ g.selection.read, o ∈ (fiveMore a d).present := fun o member =>
    enabled.kept_subset (by simpa [Selection.commit] using member)
  have inA : ∀ o, o ∈ (fiveMore a d).present → o ≠ d → o ∈ a.present := fun o present other => by
    rcases Finset.mem_union.mp present with old | new
    · exact old
    · exact absurd (Finset.mem_singleton.mp new) other
  refine (admits_iff _).mpr ⟨?_, ⟨?_, nodup, ?_, ?_, ?_, rfl⟩, ?_, ?_,
    fun check inside => absurd inside List.not_mem_nil,
    fun q inside => absurd inside List.not_mem_nil⟩
  · refine fresh_transfer g (dropFiring g extra ms) fresh (fun _ => rfl) (fun t mentioned => ?_)
      (terms_dropRow g.rule g.selection.taken g.selection.read d constant)
    rcases mentioned with inside | inside | ⟨o, present, rfl⟩
    · exact Or.inl (Or.inl inside)
    · exact Or.inl (Or.inr (Or.inl inside))
    · refine Or.inl (Or.inr (Or.inr ⟨o, Finset.mem_union_left _ present, ?_⟩))
      exact label_fiveMore_of_ne (fun same => freshD (same ▸ present))
  · exact nodup_keepAway takeLength takenNodup d
  · show ((keepAway (g.rule.body.take.zip g.selection.taken) d).map Prod.fst).length =
      ((keepAway (g.rule.body.take.zip g.selection.taken) d).map Prod.snd).length
    simp
  · show ((keepAway (g.rule.body.read.zip g.selection.read) d).map Prod.fst).length =
      ((keepAway (g.rule.body.read.zip g.selection.read) d).map Prod.snd).length
    simp
  · show (g.rule.body.produce ++ extra).length = (g.selection.made ++ ms).length
    simp [produceLength, lengths]
  · refine ⟨fun o inside => ?_, fun o inside => ?_, ?_, ?_, fun q inside => ?_⟩
    · have member : o ∈ (keepAway (g.rule.body.take.zip g.selection.taken) d).map Prod.snd := by
        simpa [dropFiring, Selection.commit] using inside
      obtain ⟨taken, other⟩ := (mem_keepAway_snd takeLength).mp member
      exact inA o (takenPresent o taken) other
    · have member : o ∈ (keepAway (g.rule.body.read.zip g.selection.read) d).map Prod.snd := by
        simpa [dropFiring, Selection.commit] using inside
      obtain ⟨read, other⟩ := (mem_keepAway_snd readLength).mp member
      exact inA o (readPresent o read) other
    · rw [Finset.disjoint_left]
      intro o inside inside'
      have member : o ∈ (keepAway (g.rule.body.take.zip g.selection.taken) d).map Prod.snd := by
        simpa [dropFiring, Selection.commit] using inside
      have member' : o ∈ (keepAway (g.rule.body.read.zip g.selection.read) d).map Prod.snd := by
        simpa [dropFiring, Selection.commit] using inside'
      exact Finset.disjoint_left.mp enabled.apart
        (by simpa [Selection.commit] using ((mem_keepAway_snd takeLength).mp member).1)
        (by simpa [Selection.commit] using ((mem_keepAway_snd readLength).mp member').1)
    · rw [Finset.disjoint_left]
      intro o inside present
      have made : o ∈ g.selection.made ∨ o ∈ ms := by simpa [dropFiring, Selection.commit] using inside
      rcases made with made | new
      · exact Finset.disjoint_left.mp enabled.fresh (by simpa [Selection.commit] using made)
          (Finset.mem_union_left _ present)
      · exact apart o new present
    · simp [dropFiring, Selection.commit] at inside
  · obtain ⟨β, σ, solved⟩ := solvable
    cases β
    exact ⟨PUnit.unit, σ, fun e inside =>
      solved e ((mem_information_dropRow g extra ms e).mp inside)⟩

/-- The informations of the answer and of the firing have the same solutions and mention the same
unknowns. -/
theorem knowledge_dropFiring {a : State Tm ℕ} {d : ℕ} (g : Firing ℕ E everyRule (fiveMore a d).frame)
    (extra : List (Term atoms)) (ms : List ℕ) :
    X.Equivalent (a := PUnit.unit) ((dropFiring g extra ms).result X a).knowledge
        (g.result X (fiveMore a d)).knowledge ∧
      ∀ w, KnowsVar ((dropFiring g extra ms).result X a) w ↔
        KnowsVar (g.result X (fiveMore a d)) w := by
  have same := mem_information_dropRow g extra ms
  refine ⟨fun _ σ => ⟨fun solved e inside => solved e ((same e).mpr inside),
    fun solved e inside => solved e ((same e).mp inside)⟩, fun w => ?_⟩
  unfold KnowsVar
  constructor
  · rintro (inside | inside)
    · obtain ⟨e, member, side⟩ := List.mem_map.mp inside
      exact Or.inl (List.mem_map.mpr ⟨e, (same e).mp member, side⟩)
    · obtain ⟨e, member, side⟩ := List.mem_map.mp inside
      exact Or.inr (List.mem_map.mpr ⟨e, (same e).mp member, side⟩)
  · rintro (inside | inside)
    · obtain ⟨e, member, side⟩ := List.mem_map.mp inside
      exact Or.inl (List.mem_map.mpr ⟨e, (same e).mpr member, side⟩)
    · obtain ⟨e, member, side⟩ := List.mem_map.mp inside
      exact Or.inr (List.mem_map.mpr ⟨e, (same e).mpr member, side⟩)

/-- **Backward**: a firing of every rule at `fiveMore a d` is answered at `a` by a firing whose result
is statically equivalent. -/
theorem answer_backward {a : State Tm ℕ} {d : ℕ} (freshD : d ∉ a.present)
    (g : Firing ℕ E everyRule (fiveMore a d).frame) (admitted : g.Admits X (fiveMore a d)) :
    ∃ f : Firing ℕ E everyRule a.frame, f.rule ∈ positiveRules ∧ f.Admits X a ∧
      Static (f.result X a) (g.result X (fiveMore a d)) := by
  obtain ⟨-, -, madeNodup, takeLength, -, produceLength, -⟩ := admitted.1
  have enabled := admitted.2.1
  have madeOut : ∀ o ∈ g.selection.made, o ∉ (fiveMore a d).present := fun o made present =>
    Finset.disjoint_left.mp enabled.fresh (by simpa [Selection.commit] using made) present
  have dNotMade : d ∉ g.selection.made := fun made =>
    madeOut d made (Finset.mem_union_right _ (Finset.mem_singleton_self d))
  have madeNotA : ∀ o ∈ g.selection.made, o ∉ a.present := fun o made present =>
    madeOut o made (Finset.mem_union_left _ present)
  have produceLength' : g.selection.made.length = (g.opened X).produce.length := by
    rw [← produceLength]
    exact (List.length_map _).symm
  have rowAgree : ∀ (extra : List (Term atoms)) (ms : List ℕ) (o : ℕ), o ≠ d →
      (dropFiring g extra ms).row X a o = g.row X (fiveMore a d) o := fun extra ms o other => by
    show Subst.applyTerm (Subst.id atoms) (a.label o) =
      Subst.applyTerm (Subst.id atoms) ((fiveMore a d).label o)
    rw [label_fiveMore_of_ne other]
  have rowD : g.row X (fiveMore a d) d = c 5 := by
    show Subst.applyTerm (Subst.id atoms) ((fiveMore a d).label d) = c 5
    rw [label_fiveMore_self]
    rfl
  have keepIff : ∀ o, o ∈ (keepAway (g.rule.body.take.zip g.selection.taken) d).map Prod.snd ↔
      o ∈ g.selection.taken ∧ o ≠ d := fun o => mem_keepAway_snd takeLength
  by_cases dTaken : d ∈ g.selection.taken
  · -- The firing takes `d`: answer with its takes and reads of `d` turned into tells.
    refine ⟨dropFiring g [] [], positive_of_nil rfl rfl,
      admits_dropFiring freshD g admitted [] [] (by simp) rfl
      (by simpa using madeNodup) (by simp), ?_⟩
    obtain ⟨equivalent, knows⟩ := knowledge_dropFiring g [] []
    refine static_of_perm (fun β σ => (equivalent β σ)) knows 1 ?_ ?_
    · rw [map_one]
      ext o
      show o ∈ fire (a.present ∪ {d}) (g.selection.commit (T := Unit)) ↔
        o ∈ fire a.present ((dropFiring g [] []).selection.commit (T := Unit))
      rw [mem_fire, mem_fire]
      simp only [dropFiring, Selection.commit, List.mem_toFinset, List.append_nil, Finset.mem_union,
        Finset.mem_singleton]
      constructor
      · rintro (⟨old | isD, notTaken⟩ | made)
        · exact Or.inl ⟨old, fun kept => notTaken ((keepIff o).mp kept).1⟩
        · exact absurd (isD ▸ dTaken) notTaken
        · exact Or.inr made
      · rintro (⟨old, notKept⟩ | made)
        · refine Or.inl ⟨Or.inl old, fun taken => notKept ((keepIff o).mpr ⟨taken, ?_⟩)⟩
          exact fun same => freshD (same ▸ old)
        · exact Or.inr made
    · intro o inside
      show relabel (g.row X (fiveMore a d)) g.selection.made
          (g.rule.body.produce.map (Subst.applyTerm g.opening)) o =
        relabel ((dropFiring g [] []).row X a) (g.selection.made ++ [])
          ((g.rule.body.produce ++ []).map (Subst.applyTerm g.opening)) o
      simp only [List.append_nil]
      by_cases made : o ∈ g.selection.made
      · exact relabel_eq_of_mem _ _ _ _ o produceLength' made
      · have old : o ∈ a.present := by
          rcases mem_fire.mp inside with ⟨old, -⟩ | isMade
          · exact old
          · exact absurd (by simpa [dropFiring, Selection.commit] using isMade) made
        rw [Firing.relabel_of_not_mem _ _ _ made, Firing.relabel_of_not_mem _ _ _ made]
        exact (rowAgree [] [] o (fun same => freshD (same ▸ old))).symm
  · -- The firing keeps `d`: the answer also makes one row `5`.
    obtain ⟨m, mFresh⟩ : ∃ m, m ∉ a.present ∪ {d} ∪ g.selection.made.toFinset :=
      ⟨_, fresh_identity _⟩
    have mNotA : m ∉ a.present := fun h => mFresh (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have mNotD : m ≠ d := fun h => mFresh (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_singleton.mpr h)))
    have mNotMade : m ∉ g.selection.made := fun h =>
      mFresh (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
    refine ⟨dropFiring g [c 5] [m], positive_of_nil rfl rfl,
      admits_dropFiring freshD g admitted [c 5] [m]
      (fun t inside => ⟨5, List.mem_singleton.mp inside⟩) rfl
      (List.nodup_append.mpr ⟨madeNodup, List.nodup_singleton m, fun o made o' same => by
        rw [List.mem_singleton] at same
        subst same
        exact fun equal => mNotMade (equal ▸ made)⟩)
      (fun o inside => by rw [List.mem_singleton.mp inside]; exact mNotA), ?_⟩
    obtain ⟨equivalent, knows⟩ := knowledge_dropFiring g [c 5] [m]
    have fPresent : ∀ o, o ∈ ((dropFiring g [c 5] [m]).result X a).present ↔
        (o ∈ a.present ∧ o ∉ g.selection.taken) ∨ o ∈ g.selection.made ∨ o = m := by
      intro o
      show o ∈ fire a.present ((dropFiring g [c 5] [m]).selection.commit (T := Unit)) ↔ _
      rw [mem_fire]
      simp only [dropFiring, Selection.commit, List.mem_toFinset, List.mem_append, List.mem_singleton]
      constructor
      · rintro (⟨old, notKept⟩ | made | isM)
        · refine Or.inl ⟨old, fun taken => notKept ((keepIff o).mpr ⟨taken, ?_⟩)⟩
          exact fun same => freshD (same ▸ old)
        · exact Or.inr (Or.inl made)
        · exact Or.inr (Or.inr isM)
      · rintro (⟨old, notTaken⟩ | made | isM)
        · exact Or.inl ⟨old, fun kept => notTaken ((keepIff o).mp kept).1⟩
        · exact Or.inr (Or.inl made)
        · exact Or.inr (Or.inr isM)
    have gPresent : ∀ o, o ∈ (g.result X (fiveMore a d)).present ↔
        ((o ∈ a.present ∨ o = d) ∧ o ∉ g.selection.taken) ∨ o ∈ g.selection.made := by
      intro o
      show o ∈ fire (a.present ∪ {d}) (g.selection.commit (T := Unit)) ↔ _
      rw [mem_fire]
      simp only [Selection.commit, List.mem_toFinset, Finset.mem_union, Finset.mem_singleton]
    refine static_of_perm (fun β σ => (equivalent β σ)) knows (Equiv.swap m d) ?_ ?_
    · ext o
      rw [Finset.mem_map_equiv, Equiv.symm_swap, gPresent, fPresent]
      by_cases isD : o = d
      · subst isD
        rw [Equiv.swap_apply_right]
        exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => Or.inl ⟨Or.inr rfl, dTaken⟩⟩
      · by_cases isM : o = m
        · subst isM
          rw [Equiv.swap_apply_left]
          constructor
          · rintro (⟨old | same, -⟩ | made)
            · exact absurd old mNotA
            · exact absurd same mNotD
            · exact absurd made mNotMade
          · rintro (⟨old, -⟩ | made | same)
            · exact absurd old freshD
            · exact absurd made dNotMade
            · exact absurd same.symm mNotD
        · rw [Equiv.swap_apply_of_ne_of_ne isM isD]
          constructor
          · rintro (⟨old | same, notTaken⟩ | made)
            · exact Or.inl ⟨old, notTaken⟩
            · exact absurd same isD
            · exact Or.inr (Or.inl made)
          · rintro (⟨old, notTaken⟩ | made | same)
            · exact Or.inl ⟨Or.inl old, notTaken⟩
            · exact Or.inr made
            · exact absurd same isM
    · intro o inside
      have fProduce : ((dropFiring g [c 5] [m]).opened X).produce =
          (g.opened X).produce ++ [c 5] := by
        show (g.rule.body.produce ++ [c 5]).map (Subst.applyTerm g.opening) =
          g.rule.body.produce.map (Subst.applyTerm g.opening) ++ [c 5]
        rw [List.map_append]
        rfl
      show relabel (g.row X (fiveMore a d)) g.selection.made (g.opened X).produce
          (Equiv.swap m d o) =
        relabel ((dropFiring g [c 5] [m]).row X a) (g.selection.made ++ [m])
          ((dropFiring g [c 5] [m]).opened X).produce o
      rw [fProduce]
      rcases (fPresent o).mp inside with ⟨old, -⟩ | made | isM
      · have other : o ≠ d := fun same => freshD (same ▸ old)
        have notM : o ≠ m := fun same => mNotA (same ▸ old)
        have notMade : o ∉ g.selection.made := fun made => madeNotA o made old
        rw [Equiv.swap_apply_of_ne_of_ne notM other, relabel_append_other _ m _ _ _ o notMade notM,
          Firing.relabel_of_not_mem _ _ _ notMade, Firing.relabel_of_not_mem _ _ _ notMade]
        exact (rowAgree [c 5] [m] o other).symm
      · have other : o ≠ d := fun same => dNotMade (same ▸ made)
        have notM : o ≠ m := fun same => mNotMade (same ▸ made)
        rw [Equiv.swap_apply_of_ne_of_ne notM other,
          relabel_append_of_mem _ m _ _ _ o produceLength' made]
        exact relabel_eq_of_mem _ _ _ _ o produceLength' made
      · subst isM
        rw [Equiv.swap_apply_left, relabel_append_last _ o _ _ _ produceLength' mNotMade,
          Firing.relabel_of_not_mem _ _ _ dNotMade, rowD]

#print axioms terms_dropRow
#print axioms mem_information_dropRow
#print axioms mem_keepAway_snd
#print axioms admits_dropFiring
#print axioms knowledge_dropFiring
#print axioms answer_backward

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
