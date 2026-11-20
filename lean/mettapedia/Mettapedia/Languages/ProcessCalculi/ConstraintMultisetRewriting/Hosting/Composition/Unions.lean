import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

/-!
# When a program keeps its answers in a union

A neighbour that is itself a hosted program is rows **and** schemas: its hosted system is united with
the program's (`hosted_union`), and the union answers as the union of the programs does
(`union_answers`). What the union answers is a law of the source language, stated here at the source.

* `SeparateFrom D P Q supply spaces q`: **along the runs of `P` from the query, no equation of `Q`
  matches a call**: for every live alternative of every configuration a run of `P` reaches, at a call,
  no copy of a left side of `Q` unifies with the call.
* `move_union`, `move_of_union`: under that condition at an alternative, its moves in `P` and in
  `P.union Q` are the same, up to alternatives that are dead when they are made (the copies of `Q`'s
  equations whose left sides do not unify with the call).
* `runs_union`, `runs_of_union`: so the runs of `P` and of `P.union Q` from the query are the same up
  to dead alternatives (`WithDead`), and their configurations have the same answers, as bags
  (`answers_withDead`).
* `union_conservative`: **the union answers as `P`**: the answers of `P.union Q` and of `P` from the
  query are the same, as sets; configuration by configuration the bags are the same.
* `unionCorrespondence`: the same as an operational correspondence between the two source systems,
  one step for one step; `unionHostReadback`: composed with the readback of the hosting at the union,
  the step of the translated union reads back to the source of `P`, with no further proof.
* `union_keeps`: on the step, from the start of the union of the two hosted systems, the answers shown
  are, as a set, the source's answers of `P`.

The condition is on calls and matching, and it is the same closed-world rule as the unmatched call's:
an equation that matches a call of the other program gives that call another answer. Instance:
`(= (g) d)` with the program whose one left side is `(g a)` (`Controls.separate_instance`,
`Controls.union_keeps_d`). Control: no equation, united with `(= (g) d)`, on the query `(g)`: the
separation fails at the start (`Controls.not_separate`), `P0` answers `(g)` (`Controls.p0_only_g`) and
the union answers `d` (`Controls.union_answers_only_d`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Classical

section Unions

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  {P Q : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **No equation of `Q` matches the alternative's call**, if the alternative is at a call. -/
def NoMatchIn (Q : SourceLanguage.Program κ Γ star D.Ty) (n : ℕ) (b : Branch κ Γ star D.Ty) : Prop :=
  ∀ t, b.focus = .eval (.apply t) → ∀ e ∈ Q.equations,
    ¬ Solvable (b.store ++ [(instantiate (copyAt κ n) e.lhs, t)])

/-! ## One move -/

/-- **A move in `P` is a move in the union**, up to alternatives that are dead when they are made. -/
theorem move_union {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (move : Move D P supply w b w' bs) (sep : NoMatchIn Q w.scope b) :
    ∃ dead, Move D (P.union Q) supply w b w' (bs + dead) ∧ ∀ d ∈ dead, ¬ Solvable d.store := by
  cases move
  case apply K t fs ps matched =>
    obtain ⟨e, eMember, solvable⟩ := matched
    refine ⟨((Q.equations.map (callBranch D w.scope K t fs ps) : List (Branch κ Γ star D.Ty)) :
      Multiset (Branch κ Γ star D.Ty)), ?_, ?_⟩
    · have moved := Move.apply (D := D) (P := P.union Q) (supply := supply) w K t fs ps
        ⟨e, List.mem_append_left _ eMember, solvable⟩
      have same : (((P.union Q).equations.map (callBranch D w.scope K t fs ps) :
          List (Branch κ Γ star D.Ty)) : Multiset (Branch κ Γ star D.Ty)) =
          ((P.equations.map (callBranch D w.scope K t fs ps) : List (Branch κ Γ star D.Ty)) :
            Multiset (Branch κ Γ star D.Ty)) +
          ((Q.equations.map (callBranch D w.scope K t fs ps) : List (Branch κ Γ star D.Ty)) :
            Multiset (Branch κ Γ star D.Ty)) := by
        show (((P.equations ++ Q.equations).map (callBranch D w.scope K t fs ps) :
          List (Branch κ Γ star D.Ty)) : Multiset (Branch κ Γ star D.Ty)) = _
        rw [List.map_append, Multiset.coe_add]
      rw [← same]
      exact moved
    · intro d member
      obtain ⟨e', inQ, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      exact sep t rfl e' inQ
  case unmatched K t fs ps none =>
    refine ⟨0, ?_, fun d member => absurd member (Multiset.notMem_zero d)⟩
    rw [add_zero]
    exact Move.unmatched w K t fs ps (fun e member => by
      rcases List.mem_append.mp member with inP | inQ
      · exact none e inP
      · exact sep t rfl e inQ)
  all_goals
    refine ⟨0, ?_, fun d member => absurd member (Multiset.notMem_zero d)⟩
    rw [add_zero]
    constructor <;> assumption

/-- **A move in the union is a move in `P`**, up to alternatives that are dead when they are made. -/
theorem move_of_union {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {bs' : Multiset (Branch κ Γ star D.Ty)} (move : Move D (P.union Q) supply w b w' bs')
    (sep : NoMatchIn Q w.scope b) :
    ∃ bs dead, bs' = bs + dead ∧ Move D P supply w b w' bs ∧ ∀ d ∈ dead, ¬ Solvable d.store := by
  cases move
  case apply K t fs ps matched =>
    obtain ⟨e, eMember, solvable⟩ := matched
    rcases List.mem_append.mp eMember with inP | inQ
    · refine ⟨_, ((Q.equations.map (callBranch D w.scope K t fs ps) : List (Branch κ Γ star D.Ty)) :
        Multiset (Branch κ Γ star D.Ty)), ?_, Move.apply w K t fs ps ⟨e, inP, solvable⟩, ?_⟩
      · show (((P.equations ++ Q.equations).map (callBranch D w.scope K t fs ps) :
          List (Branch κ Γ star D.Ty)) : Multiset (Branch κ Γ star D.Ty)) = _
        rw [List.map_append, Multiset.coe_add]
      · intro d member
        obtain ⟨e', inQ', rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
        exact sep t rfl e' inQ'
    · exact absurd solvable (sep t rfl e inQ)
  case unmatched K t fs ps none =>
    exact ⟨_, 0, (add_zero _).symm,
      Move.unmatched w K t fs ps (fun e member => none e (List.mem_append_left _ member)),
      fun d member => absurd member (Multiset.notMem_zero d)⟩
  all_goals
    refine ⟨_, 0, (add_zero _).symm, ?_, fun d member => absurd member (Multiset.notMem_zero d)⟩
    constructor <;> assumption

/-! ## Configurations up to dead alternatives -/

/-- **`C'` is `C` with more dead alternatives.** -/
def WithDead (C C' : Config κ Γ star D.Ty) : Prop :=
  C'.world = C.world ∧ ∃ dead : Multiset (Branch κ Γ star D.Ty), C'.branches = C.branches + dead ∧
    ∀ d ∈ dead, ¬ Solvable d.store

/-- **Dead alternatives do not answer**: the two configurations have the same answers, as bags. -/
theorem answers_withDead {C C' : Config κ Γ star D.Ty} (rel : WithDead C C') :
    C'.answers (D := D) = C.answers (D := D) := by
  obtain ⟨_, dead, branches, allDead⟩ := rel
  unfold Config.answers
  rw [branches, Multiset.filter_add, Multiset.map_add,
    Multiset.filter_eq_nil.mpr (fun d member holds => allDead d member holds.2), Multiset.map_zero,
    add_zero]

/-- A step of `P` is a step of the union, up to dead alternatives. -/
theorem step_union {C C₁ C' : Config κ Γ star D.Ty} (step : SourceLanguage.Step D P supply C C₁)
    (rel : WithDead C C') (sep : ∀ b ∈ C.branches, Solvable b.store → NoMatchIn Q C.world.scope b) :
    ∃ C₁', SourceLanguage.Step D (P.union Q) supply C' C₁' ∧ WithDead C₁ C₁' := by
  obtain ⟨w, w', b, rest, bs, live, move⟩ := step
  obtain ⟨world, dead, branches, allDead⟩ := rel
  obtain ⟨dead₁, move', allDead₁⟩ := move_union (Q := Q) move (sep b (Multiset.mem_cons_self _ _) live)
  refine ⟨⟨w', (bs + dead₁) + (rest + dead)⟩, ?_, rfl, dead₁ + dead, ?_, ?_⟩
  · obtain ⟨world', branches'⟩ := C'
    simp only at world branches
    subst world branches
    rw [Multiset.cons_add]
    exact .move _ w' b (rest + dead) (bs + dead₁) live move'
  · show bs + dead₁ + (rest + dead) = bs + rest + (dead₁ + dead)
    exact add_add_add_comm bs dead₁ rest dead
  · intro d member
    rcases Multiset.mem_add.mp member with one | two
    · exact allDead₁ d one
    · exact allDead d two

/-- A step of the union is a step of `P`, up to dead alternatives. -/
theorem step_of_union {C C' C₁' : Config κ Γ star D.Ty}
    (step : SourceLanguage.Step D (P.union Q) supply C' C₁') (rel : WithDead C C')
    (sep : ∀ b ∈ C.branches, Solvable b.store → NoMatchIn Q C.world.scope b) :
    ∃ C₁, SourceLanguage.Step D P supply C C₁ ∧ WithDead C₁ C₁' := by
  obtain ⟨w, w', b, rest', bs', live, move'⟩ := step
  obtain ⟨world, dead, branches, allDead⟩ := rel
  simp only at world branches
  have inC : b ∈ C.branches := by
    have inside : b ∈ C.branches + dead := branches ▸ Multiset.mem_cons_self b rest'
    rcases Multiset.mem_add.mp inside with inC | inDead
    · exact inC
    · exact absurd live (allDead b inDead)
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem inC
  have restEq : rest' = rest + dead := by
    rw [split, Multiset.cons_add] at branches
    exact (Multiset.cons_inj_right b).mp branches
  obtain ⟨bs, dead₁, same, move, allDead₁⟩ :=
    move_of_union (P := P) (Q := Q) move' (by rw [world]; exact sep b inC live)
  refine ⟨⟨w', bs + rest⟩, ?_, rfl, dead₁ + dead, ?_, ?_⟩
  · obtain ⟨cw, cb⟩ := C
    simp only at world split
    subst world split
    exact .move _ w' b rest bs live move
  · show bs' + rest' = bs + rest + (dead₁ + dead)
    rw [same, restEq]
    exact add_add_add_comm bs dead₁ rest dead
  · intro d member
    rcases Multiset.mem_add.mp member with one | two
    · exact allDead₁ d one
    · exact allDead d two

/-! ## Whole runs and answers -/

/-- **Along the runs of `P` from the query, no equation of `Q` matches a call.** -/
def SeparateFrom (D : Discipline S Γ star) (P Q : SourceLanguage.Program κ Γ star D.Ty)
    (supply : ℕ → Term S Γ star) (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (q : Comp κ Γ star D.Ty) : Prop :=
  ∀ C, Runs D P supply (Config.initial spaces q) C → ∀ b ∈ C.branches, Solvable b.store →
    NoMatchIn Q C.world.scope b

variable {spaces : Term S Γ star → Multiset (Row κ Γ star)} {q : Comp κ Γ star D.Ty}

/-- **Every run of `P` is a run of the union**, up to dead alternatives. -/
theorem runs_union (sep : SeparateFrom D P Q supply spaces q) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ C', Runs D (P.union Q) supply (Config.initial spaces q) C' ∧ WithDead C C' := by
  induction runs with
  | refl =>
      exact ⟨_, .refl, rfl, 0, (add_zero _).symm, fun d member => absurd member (Multiset.notMem_zero d)⟩
  | tail runs step ih =>
      obtain ⟨C', runs', rel⟩ := ih
      obtain ⟨C₁', step', rel'⟩ := step_union step rel (sep _ runs)
      exact ⟨C₁', runs'.tail step', rel'⟩

/-- **Every run of the union is a run of `P`**, up to dead alternatives. -/
theorem runs_of_union (sep : SeparateFrom D P Q supply spaces q) {C' : Config κ Γ star D.Ty}
    (runs : Runs D (P.union Q) supply (Config.initial spaces q) C') :
    ∃ C, Runs D P supply (Config.initial spaces q) C ∧ WithDead C C' := by
  induction runs with
  | refl =>
      exact ⟨_, .refl, rfl, 0, (add_zero _).symm, fun d member => absurd member (Multiset.notMem_zero d)⟩
  | tail _ step ih =>
      obtain ⟨C, runs, rel⟩ := ih
      obtain ⟨C₁, step', rel'⟩ := step_of_union step rel (sep _ runs)
      exact ⟨C₁, runs.tail step', rel'⟩

/-- **The union answers as `P`**, when no equation of `Q` matches a call along the runs of `P`. -/
theorem union_conservative (sep : SeparateFrom D P Q supply spaces q) :
    Answers.sourceAnswers D (P.union Q) supply spaces q = Answers.sourceAnswers D P supply spaces q := by
  ext A
  constructor
  · rintro ⟨C', runs, member⟩
    obtain ⟨C, runs', rel⟩ := runs_of_union sep runs
    exact ⟨C, runs', (answers_withDead rel) ▸ member⟩
  · rintro ⟨C, runs, member⟩
    obtain ⟨C', runs', rel⟩ := runs_union sep runs
    exact ⟨C', runs', (answers_withDead rel).symm ▸ member⟩

/-- **The source of `P` and the source of the union correspond, step for step**, on the
configurations reached from the query, up to dead alternatives: an operational correspondence
(`GSLT.IndexedOperational.OperationalCorrespondence`) with no silent step either way. -/
def unionCorrespondence (sep : SeparateFrom D P Q supply spaces q) :
    Mettapedia.GSLT.IndexedOperational.OperationalCorrespondence (Divergence.sourceSystem D P supply)
      (Divergence.sourceSystem D (P.union Q) supply) where
  related C C' := Runs D P supply (Config.initial spaces q) C ∧ WithDead C C'
  readStep := by
    rintro C C' C₁' ⟨runs, rel⟩ step
    obtain ⟨C₁, step', rel'⟩ := step_of_union step rel (sep _ runs)
    exact .inr ⟨C₁, step', runs.tail step', rel'⟩
  forward := by
    rintro C C₁ C' ⟨runs, rel⟩ step
    obtain ⟨C₁', step', rel'⟩ := step_union step rel (sep _ runs)
    exact ⟨C₁', ⟨.cons ⟨step'⟩ (.refl _)⟩, runs.tail step, rel'⟩

/-- **Composed, with no further proof**: the step of the translated union reads back to the source of
`P` alone. It is the composite (`OperationalReadback.comp`) of the correspondence between the two
sources and the readback of the hosting at the union. -/
def unionHostReadback (N : Nodes S Γ star) (sep : SeparateFrom D P Q supply spaces q)
    (equations : ∀ e ∈ (P.union Q).equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) :
    Mettapedia.GSLT.IndexedOperational.OperationalReadback (Divergence.sourceSystem D P supply)
      (Divergence.hostSystem N (P.union Q)) :=
  (unionCorrespondence sep).toOperationalReadback.comp
    (Divergence.arrowReadback N spaces q equations qScoped qDistinct arrowQ)

/-- **On the step, the union of the two hosted systems shows the answers of `P`.** -/
theorem union_keeps (N : Nodes S Γ star) (sep : SeparateFrom D P Q supply spaces q)
    (equations : ∀ e ∈ (P.union Q).equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) :
    stepAnswersFrom N (P.union Q) (((hosted N P).union (hosted N Q)).start N q) =
      Answers.sourceAnswers D P supply spaces q := by
  rw [union_answers N (supply := supply) spaces q equations qScoped qDistinct arrowQ, union_conservative sep]

#print axioms move_union
#print axioms move_of_union
#print axioms answers_withDead
#print axioms runs_union
#print axioms runs_of_union
#print axioms union_conservative
#print axioms unionCorrespondence
#print axioms unionHostReadback
#print axioms union_keeps

end Unions

/-! ## An instance and the control -/

namespace Controls

open SourceLanguage.Elaboration SourceLanguage.Toolkit

/-- **An instance of the separation**: `(= (g) d)` and the program whose one left side is `(g a)`, on
the query `(g)`: the only call along the runs is `(g)`, and `(g a)` does not unify with it. -/
theorem separate_instance : SeparateFrom D Q (rowProgram gaT) supply sp q := by
  intro C runs b member _ t focus e eMember solvable
  rw [List.mem_singleton.mp eMember] at solvable
  rcases inv_runs (P := Q) rfl runs b member with rfl | rfl | rfl
  · cases focus
    obtain ⟨X, target, σ, solved⟩ := solvable
    exact tuple_length_ne σ (ts := [sym "g", sym "a"]) (ts' := [sym "g"]) (by decide)
      (solved _ (List.mem_singleton_self _))
  · cases focus
  · cases focus

/-- **So the union of the two hosted systems shows the answers of `(= (g) d)` alone.** -/
theorem union_keeps_d :
    stepAnswersFrom N (Q.union (rowProgram gaT)) (((hosted N Q).union (hosted N (rowProgram gaT))).start N q) =
      Answers.sourceAnswers D Q supply sp q := by
  refine union_keeps N separate_instance ?_ Q_scoped.2.1 Q_scoped.2.2.1 Q_scoped.2.2.2
  intro e member
  have cases' : e = eg ∨ e = ⟨[301], gaT, .fail⟩ := by
    simpa [Program.union, Q, rowProgram] using member
  rcases cases' with rfl | rfl
  · exact ⟨by decide, by decide, trivial⟩
  · exact ⟨by decide, by decide, trivial⟩

/-- **The control**: with no equation, united with `(= (g) d)`, the separation fails at the start: the
equation matches the query's call. -/
theorem not_separate : ¬ SeparateFrom D P0 Q supply sp q :=
  fun sep => sep _ .refl B0 (Multiset.mem_singleton_self _) live_nil gT rfl eg (List.mem_singleton_self _)
    live_gg

#print axioms separate_instance
#print axioms union_keeps_d
#print axioms not_separate

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition
