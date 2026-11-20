import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics

/-!
# Alternatives as worlds: the other coherent semantics of spaces and alternatives

This module is a design that the reference semantics does **not** take, built as far as its laws. The
reference semantics (`Semantics`) lets alternatives share the world, so what a program answers is a set
of bags (`Outcomes`). Here each alternative is a world of its own: it reads the spaces as they were
when it was made, sees only its own writes, and the writes are merged where the alternatives are
collected. Nothing in the elaboration uses it.

* **The step** (`WStep`) is the reference semantics' `Move`, made by one alternative in a world whose
  spaces are its own view; the alternatives it makes inherit the view its move left, and its record of
  writes (`Writes.record`). The scope and handle counters stay shared, so fresh names stay fresh.
* **The merge** (`Writes.merge`): the additions of two alternatives add up; their removals are united,
  so a copy of a row that both remove (each from its own view) is removed once
  (`merge_removes_once`). It is commutative (`merge_comm`), associative (`merge_assoc`), has the empty
  writes as unit (`merge_none`), and is idempotent on removals (`merge_self_removed`). Where the
  alternatives are collected, the spaces are the base with every alternative's writes merged onto it
  (`collected`, `collected_pair`).
* **The two semantics coincide on what writes no space** (`step_embed`, `runs_embed`, `wstep_shared`,
  `answers_embed`): a run of the reference semantics in which no step changes the spaces is a run of
  this one, alternative by alternative, with the same answers; and a step of this one after which no
  alternative's view differs from the start is a step of the reference semantics. So the two differ
  only where an alternative writes a space: the race (`ExampleRace`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Worlds

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}

/-- Spaces: a bag of rows at every address. -/
abbrev Spaces (κ : Keys S) (Γ : Ctx S) (star : S.Srt) := Term S Γ star → Multiset (Row κ Γ star)

/-- **The writes of an alternative**: the rows it added and the rows it removed, at every address. -/
structure Writes (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  added : Spaces κ Γ star
  removed : Spaces κ Γ star

namespace Writes

/-- No writes. -/
def none : Writes κ Γ star := ⟨fun _ => 0, fun _ => 0⟩

open Classical in
/-- **The merge of two collected alternatives' writes**: additions add up; removals are united. -/
noncomputable def merge (a b : Writes κ Γ star) : Writes κ Γ star :=
  ⟨fun h => a.added h + b.added h, fun h => a.removed h ∪ b.removed h⟩

open Classical in
/-- The spaces after writes: the removed rows taken out of the base, the added rows put in. -/
noncomputable def onto (base : Spaces κ Γ star) (wr : Writes κ Γ star) : Spaces κ Γ star :=
  fun h => base h - wr.removed h + wr.added h

open Classical in
/-- The writes after a move that changed the view from `before` to `after`. -/
noncomputable def record (wr : Writes κ Γ star) (before after : Spaces κ Γ star) : Writes κ Γ star :=
  ⟨fun h => wr.added h + (after h - before h), fun h => wr.removed h + (before h - after h)⟩

end Writes

open Writes

/-! ## The laws of the merge -/

theorem merge_comm (a b : Writes κ Γ star) : a.merge b = b.merge a := by
  classical
  unfold Writes.merge
  congr 1 <;> funext h
  · exact add_comm _ _
  · exact Multiset.union_comm _ _

theorem merge_assoc (a b c : Writes κ Γ star) : (a.merge b).merge c = a.merge (b.merge c) := by
  classical
  unfold Writes.merge
  congr 1 <;> funext h
  · exact add_assoc _ _ _
  · exact sup_assoc (a.removed h) (b.removed h) (c.removed h)

theorem merge_none (a : Writes κ Γ star) : a.merge Writes.none = a := by
  classical
  rcases a with ⟨added, removed⟩
  unfold Writes.merge Writes.none
  congr 1 <;> funext h
  · exact add_zero _
  · exact Multiset.union_zero

/-- **Merging writes with themselves keeps the removals**: a removal seen twice is one removal. -/
theorem merge_self_removed (a : Writes κ Γ star) : (a.merge a).removed = a.removed := by
  classical
  funext h
  exact sup_idem (a.removed h)

/-- **A copy of a row two alternatives both remove is removed once**: from a space holding the row
twice, each alternative removed one copy of it from its own view, and the merged space keeps one. -/
theorem merge_removes_once (base : Spaces κ Γ star) (h : Term S Γ star) (r : Row κ Γ star)
    (a b : Writes κ Γ star) (twice : base h = {r, r}) (ra : a.removed h = {r}) (rb : b.removed h = {r})
    (na : a.added h = 0) (nb : b.added h = 0) : Writes.onto base (a.merge b) h = {r} := by
  classical
  unfold Writes.onto Writes.merge
  simp only [twice, ra, rb, na, nb, add_zero]
  rw [show ({r} : Multiset (Row κ Γ star)) ∪ {r} = {r} from sup_idem ({r} : Multiset (Row κ Γ star)),
    Multiset.sub_singleton, Multiset.insert_eq_cons, Multiset.erase_cons_head]

/-! ## The step -/

/-- An alternative in its own world: its branch, the spaces as it sees them, and its writes. -/
structure WAlt (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  branch : Branch κ Γ star Ty
  view : Spaces κ Γ star
  writes : Writes κ Γ star

/-- A configuration of alternatives as worlds: the shared counters, the spaces at the start, and the
alternatives. -/
structure WConfig (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  scope : ℕ
  handles : ℕ
  base : Spaces κ Γ star
  alts : Multiset (WAlt κ Γ star Ty)

variable (D : Discipline S Γ star) (P : Program κ Γ star D.Ty) (supply : ℕ → Term S Γ star)

/-- **One step**: a live alternative makes a move of the reference semantics in its own world; the
alternatives it makes see the spaces as its move left them and carry its writes. -/
inductive WStep : WConfig κ Γ star D.Ty → WConfig κ Γ star D.Ty → Prop
  | move (scope handles : ℕ) (base : Spaces κ Γ star) (a : WAlt κ Γ star D.Ty)
      (rest : Multiset (WAlt κ Γ star D.Ty)) (w' : World κ Γ star) (bs : Multiset (Branch κ Γ star D.Ty))
      (live : Solvable a.branch.store) (moved : Move D P supply ⟨scope, handles, a.view⟩ a.branch w' bs) :
      WStep ⟨scope, handles, base, a ::ₘ rest⟩
        ⟨w'.scope, w'.handles, base,
          bs.map (fun b => ⟨b, w'.spaces, a.writes.record a.view w'.spaces⟩) + rest⟩

/-- Runs of alternatives as worlds. -/
abbrev WRuns := Relation.ReflTransGen (WStep D P supply)

variable {D}

/-- The alternatives seen as a configuration of the reference semantics over the base spaces. -/
def WConfig.shared (C : WConfig κ Γ star D.Ty) : Config κ Γ star D.Ty :=
  ⟨⟨C.scope, C.handles, C.base⟩, C.alts.map WAlt.branch⟩

/-- **The answers**: the reading sets of the finished live alternatives, as a bag. -/
noncomputable def WConfig.answers (C : WConfig κ Γ star D.Ty) : Multiset (Set (Term S Γ star)) :=
  C.shared.answers

/-- No live alternative can move in its own world. -/
def WConfig.Quiescent (C : WConfig κ Γ star D.Ty) : Prop :=
  ∀ a ∈ C.alts, Solvable a.branch.store → ∀ w' bs, ¬ Move D P supply ⟨C.scope, C.handles, a.view⟩ a.branch w' bs

open Classical in
/-- **Where the alternatives are collected**: the base with every alternative's removals united and
additions added. -/
noncomputable def WConfig.collected (C : WConfig κ Γ star D.Ty) : Spaces κ Γ star :=
  fun h => C.base h - (C.alts.map fun a => a.writes.removed h).sup + (C.alts.map fun a => a.writes.added h).sum

/-- Two collected alternatives: their writes merged onto the base. -/
theorem collected_pair (scope handles : ℕ) (base : Spaces κ Γ star) (a b : WAlt κ Γ star D.Ty) :
    WConfig.collected (⟨scope, handles, base, {a, b}⟩ : WConfig κ Γ star D.Ty) =
      Writes.onto base (a.writes.merge b.writes) := by
  classical
  funext h
  simp only [WConfig.collected, Writes.onto, Writes.merge, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.sup_cons, Multiset.sup_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, Multiset.sup_eq_union]

/-! ## The shared semantics on runs that write no space -/

/-- A configuration of the reference semantics as worlds: every alternative sees the shared spaces and
has written nothing. -/
def embed (C : Config κ Γ star D.Ty) : WConfig κ Γ star D.Ty :=
  ⟨C.world.scope, C.world.handles, C.world.spaces, C.branches.map fun b => ⟨b, C.world.spaces, Writes.none⟩⟩

theorem sub_self_rows [DecidableEq (Row κ Γ star)] (m : Multiset (Row κ Γ star)) : m - m = 0 :=
  Multiset.ext.mpr fun r => by simp [Multiset.count_sub]

theorem record_still (s : Spaces κ Γ star) : Writes.none.record s s = (Writes.none : Writes κ Γ star) := by
  classical
  unfold Writes.record Writes.none
  congr 1 <;> funext h <;> simp [sub_self_rows]

variable {P supply}

/-- **A step that writes no space is a step of alternatives as worlds.** -/
theorem step_embed {C C' : Config κ Γ star D.Ty} (step : Step D P supply C C')
    (still : C'.world.spaces = C.world.spaces) : WStep D P supply (embed C) (embed C') := by
  cases step with
  | move w w' b rest bs live moved =>
      have source : embed (⟨w, b ::ₘ rest⟩ : Config κ Γ star D.Ty) =
          ⟨w.scope, w.handles, w.spaces,
            ⟨b, w.spaces, Writes.none⟩ ::ₘ rest.map fun b' => ⟨b', w.spaces, Writes.none⟩⟩ := by
        simp only [embed, Multiset.map_cons]
      have target : embed (⟨w', bs + rest⟩ : Config κ Γ star D.Ty) =
          ⟨w'.scope, w'.handles, w.spaces,
            bs.map (fun b' => ⟨b', w'.spaces, Writes.none.record w.spaces w'.spaces⟩) +
              rest.map fun b' => ⟨b', w.spaces, Writes.none⟩⟩ := by
        have still' : w'.spaces = w.spaces := still
        simp only [embed, still', record_still, Multiset.map_add]
      rw [source, target]
      exact WStep.move w.scope w.handles w.spaces ⟨b, w.spaces, Writes.none⟩
        (rest.map fun b' => ⟨b', w.spaces, Writes.none⟩) w' bs live moved

/-- **A run that writes no space is a run of alternatives as worlds.** -/
theorem runs_embed {C C' : Config κ Γ star D.Ty}
    (runs : Relation.ReflTransGen (fun C₁ C₂ => Step D P supply C₁ C₂ ∧ C₂.world.spaces = C₁.world.spaces) C C') :
    WRuns D P supply (embed C) (embed C') := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step_embed step.1 step.2)

/-- A move leaves the spaces as they are, or makes exactly one alternative (an addition or a removal). -/
theorem spaces_kept_or_single {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {bs : Multiset (Branch κ Γ star D.Ty)} (moved : Move D P supply w b w' bs) :
    w'.spaces = w.spaces ∨ ∃ b', bs = {b'} := by
  cases moved <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩

/-- **A step of alternatives as worlds in which no alternative has written is a step of the shared
semantics**, from and to the configurations seen as worlds. -/
theorem wstep_shared {C : Config κ Γ star D.Ty} {W' : WConfig κ Γ star D.Ty}
    (wstep : WStep D P supply (embed C) W') (still : ∀ a ∈ W'.alts, a.view = W'.base) :
    ∃ C', Step D P supply C C' ∧ W' = embed C' := by
  classical
  generalize hW : embed C = W at wstep
  cases wstep with
  | move scope handles base a rest w' bs live moved =>
      have hscope : scope = C.world.scope := (congrArg WConfig.scope hW).symm
      have hhandles : handles = C.world.handles := (congrArg WConfig.handles hW).symm
      have hbase : base = C.world.spaces := (congrArg WConfig.base hW).symm
      have halts : C.branches.map (fun b => (⟨b, C.world.spaces, Writes.none⟩ : WAlt κ Γ star D.Ty)) = a ::ₘ rest :=
        congrArg WConfig.alts hW
      obtain ⟨b, member, rfl, rfl⟩ := (Multiset.map_eq_cons _ _ _ _).mpr halts
      subst hscope hhandles hbase
      have world : (⟨C.world.scope, C.world.handles, C.world.spaces⟩ : World κ Γ star) = C.world := rfl
      rw [world] at moved
      have kept : w'.spaces = C.world.spaces := by
        rcases spaces_kept_or_single moved with same | ⟨b', rfl⟩
        · exact same
        · exact still _ (Multiset.mem_add.mpr (.inl (Multiset.mem_map.mpr ⟨b', Multiset.mem_singleton_self _, rfl⟩)))
      refine ⟨⟨w', bs + C.branches.erase b⟩, ?_, ?_⟩
      · exact Step.of_eq (Multiset.cons_erase member).symm rfl live moved
      · simp only [embed, kept, record_still, Multiset.map_add]

/-- **The same answers.** -/
theorem answers_embed (C : Config κ Γ star D.Ty) : (embed C).answers = C.answers := by
  rcases C with ⟨⟨scope, handles, spaces⟩, branches⟩
  simp only [WConfig.answers, WConfig.shared, embed, Multiset.map_map]
  congr 2
  exact Multiset.map_id' branches

#print axioms merge_comm
#print axioms merge_assoc
#print axioms merge_none
#print axioms merge_self_removed
#print axioms merge_removes_once
#print axioms collected_pair
#print axioms step_embed
#print axioms runs_embed
#print axioms wstep_shared
#print axioms answers_embed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Worlds
