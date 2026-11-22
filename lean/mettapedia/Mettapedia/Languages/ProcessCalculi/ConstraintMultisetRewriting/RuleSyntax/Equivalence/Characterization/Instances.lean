import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Programs

/-!
# The laws and the separations as instances of the characterization, at one frame

## The static equivalence is an equivalence relation

`static_refl`, `static_symm` and `static_trans` (through `static_iff`), and its two generators: renaming identities
(`static_rename`, Law 1) and equivalence modulo the knowledge with the same support
(`static_of_modulo`, Law 2).

## The laws of programs

* **Law 3** (`answersStatic_of_subset`): a program answers every firing of a smaller one by the same
  firing; programs with the same rules are congruent (`same_rules_static`), so union is commutative,
  associative and idempotent (`union_static`).
* **Law 4** (`neverFires_answers`): a rule that never fires and the empty program answer each other
  statically, vacuously; congruence beside every program follows (`neverFires_static`).
* **Law 7** (`readTakeMake_answers`): the read and the take-and-make answer each other statically
  (the folder's `readTakeMake_core` gives the answering firing; `static_iff` turns its congruent results
  into statically equivalent ones); congruence follows by the method (`readTakeMake_static`).
* **Laws 5 and 6, the other way** (`entailedGuard_answers`, `entailedTell_answers`): from the laws,
  the characterization yields that the two rules answer each other's firings with statically
  equivalent results.

## The separations, as failures of answering

At the state a context reaches (with the same identities, `Congruent.basic_same`), a firing of the
one side that the other side cannot answer statically (`answers_of_congruent`) separates them:

* `absence_separates_static`: after a row `9`, the unguarded spawn fires and the guarded one cannot;
* `dormant_separates_static`: after a row `9`, the rule that takes it fires and the empty program has no
  firing;
* `guard_not_entailed_static`, `tell_not_entailed_static`: at a row `6`, the rule that reads and makes
  `5` fires; with the guard `x = 5`, or the tell `x = 5`, it cannot;
* `tell_unkept_static`: the rule that tells `y = y` fires with a result that mentions `y`; the rule that
  does nothing answers only with a result that mentions nothing.

## The two worked pairs

* **Equivalent, and not an instance of the seven laws** (`subsumed_example`): `{spawn}` and
  `{spawn, spawnGuarded}`: a rule whose every firing a less guarded rule of the program reproduces may
  be added, beside every program, at every state. The guard is an absence query, which no law covers.
* **Not equivalent, with the separating context computed** (`touch_separates`): `take x, make x`
  ("touch any row") against the empty program, at the empty store. Neither moves there; the
  characterization asks for the rule's firings at every state a context reaches, and the least such
  context is one row (the rule's take pattern, any label); after it, touch fires and the empty program
  cannot answer. The congruence counts this firing although it only renews a row: it is strong.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves pat y idle tellX unmentioned mentionsY empty spawn spawnGuarded
  nineRow spawn_moves spawn_answers guarded_stuck_nine takeNine readMake rowSix readMake_moves
  guarded_readMake_stuck told_readMake_stuck result_rows_empty deadRule deadRule_neverFires)

/-! ## The static equivalence is an equivalence relation -/

theorem renameState_one (s : State Tm ℕ) : renameState (1 : Equiv.Perm ℕ) s = s := by
  obtain ⟨frame, knowledge, present, label⟩ := s
  have same : present.map (1 : Equiv.Perm ℕ).toEmbedding = present := by
    ext o
    rw [Finset.mem_map_equiv]
    exact Iff.rfl
  simp only [renameState, same]
  rfl

/-- **Law 2 is the static equivalence with no renaming.** -/
theorem static_of_modulo {s t : State Tm ℕ} (modulo : Modulo X s t) : Static s t :=
  Or.inr ⟨1, by rw [renameState_one]; exact modulo⟩

/-- **Law 1 is the static equivalence with no change modulo the knowledge.** -/
theorem static_rename (π : Equiv.Perm ℕ) (s : State Tm ℕ) : Static s (renameState π s) :=
  Or.inr ⟨π, Modulo.refl _⟩

theorem static_refl (s : State Tm ℕ) : Static s s := static_of_modulo (Modulo.refl s)

/-- The static equivalence is symmetric, through the characterization. -/
theorem static_symm {s t : State Tm ℕ} (static : Static s t) : Static t s :=
  (static_iff t s).mp ((static_iff s t).mpr static).symm

/-- The static equivalence is transitive, through the characterization. -/
theorem static_trans {s t u : State Tm ℕ} (first : Static s t) (second : Static t u) : Static s u :=
  (static_iff s u).mp (((static_iff s t).mpr first).trans ((static_iff t u).mpr second))

theorem bounded_union_singleton (r : Rule Tm) : Bounded (∅ ∪ {r}) :=
  bounded_of_finite (Set.finite_empty.union (Set.finite_singleton r))

/-! ## Law 3 -/

/-- **A program answers every firing of a smaller program by the same firing.** -/
theorem answersStatic_of_subset {P P' : Program Tm} (sub : P ⊆ P') : AnswersStatic P P' :=
  fun _ f admitted =>
    ⟨⟨f.rule, sub f.member, f.ext, f.opening, f.selection, f.seen⟩, admitted, static_refl _⟩

/-- Programs with the same rules are congruent beside every program, at every state. -/
theorem same_rules_static {P P' : Program Tm} (sub : P ⊆ P') (sub' : P' ⊆ P) (Q : Program Tm)
    (s : State Tm ℕ) : Cong ⟨P ∪ Q, s⟩ ⟨P' ∪ Q, s⟩ :=
  congruent_of_answersStatic (answersStatic_of_subset sub) (answersStatic_of_subset sub') Q s

/-- **Law 3 by the method**: union is commutative, associative and idempotent. -/
theorem union_static (P P' P'' Q : Program Tm) (s : State Tm ℕ) :
    Cong ⟨(P ∪ P') ∪ Q, s⟩ ⟨(P' ∪ P) ∪ Q, s⟩ ∧
      Cong ⟨((P ∪ P') ∪ P'') ∪ Q, s⟩ ⟨(P ∪ (P' ∪ P'')) ∪ Q, s⟩ ∧
      Cong ⟨(P ∪ P) ∪ Q, s⟩ ⟨P ∪ Q, s⟩ :=
  ⟨same_rules_static (Set.union_comm P P').le (Set.union_comm P' P).le Q s,
    same_rules_static (Set.union_assoc P P' P'').le (Set.union_assoc P P' P'').ge Q s,
    same_rules_static (Set.union_self P).le (Set.union_self P).ge Q s⟩

/-! ## Law 4 -/

/-- **A rule that never fires and the empty program answer each other**, vacuously. -/
theorem neverFires_answers {r : Rule Tm} (dead : NeverFires X r) :
    AnswersStatic {r} ∅ ∧ AnswersStatic ∅ {r} :=
  ⟨fun _ f admitted => absurd admitted (not_admits_of_neverFires dead f f.member),
    fun _ f _ => absurd f.member (Set.notMem_empty _)⟩

/-- **Law 4 by the method.** -/
theorem neverFires_static {r : Rule Tm} (dead : NeverFires X r) (Q : Program Tm) (s : State Tm ℕ) :
    Cong ⟨{r} ∪ Q, s⟩ ⟨∅ ∪ Q, s⟩ :=
  congruent_of_answersStatic (neverFires_answers dead).1 (neverFires_answers dead).2 Q s

/-- The rule that tells `1 = 2` may be dropped beside every program. -/
theorem dead_example_static (Q : Program Tm) (s : State Tm ℕ) : Cong ⟨{deadRule} ∪ Q, s⟩ ⟨∅ ∪ Q, s⟩ :=
  neverFires_static deadRule_neverFires Q s

/-! ## Law 7 -/

/-- **The read and the take-and-make answer each other statically.** -/
theorem readTakeMake_answers (r : Rule Tm) (p : Term atoms) :
    AnswersStatic {withRead r p} {withTakeMake r p} ∧ AnswersStatic {withTakeMake r p} {withRead r p} := by
  have invariantRename : ∀ (π : Equiv.Perm ℕ) β s, MayBarb X β (renameState π s) ↔ MayBarb X β s :=
    fun π β s => mayBarb_renameState X π β s
  have invariantModulo : ∀ {s t : State Tm ℕ}, Modulo X s t → ∀ β, MayBarb X β s → MayBarb X β t :=
    fun related β => mayBarb_modulo related β
  constructor
  · rintro s ⟨rule, member, ext, ι, ⟨tl, rd, ml⟩, seen⟩ admitted
    have isRule : rule = withRead r p := member
    subst rule
    have readLength : 1 = rd.length := admitted.1.2.2.2.2.1
    obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp readLength.symm
    obtain ⟨m, fresh⟩ := Infinite.exists_notMem_finset (s.present ∪ ml.toFinset)
    have mFresh : m ∉ s.present := fun inside => fresh (Finset.mem_union_left _ inside)
    have mNew : m ∉ ml := fun inside =>
      fresh (Finset.mem_union_right _ (List.mem_toFinset.mpr inside))
    obtain ⟨admitsIff, results⟩ := readTakeMake_core (r := r) (p := p) (s := s) invariantRename
      invariantModulo ext ι tl ml o m seen mFresh mNew
    exact ⟨takeMakeFiring r p ext ι tl ml o m seen, admitsIff.mp admitted,
      (static_iff _ _).mp (results admitted ∅)⟩
  · rintro s ⟨rule, member, ext, ι, ⟨tl', rd, ml'⟩, seen⟩ admitted
    have isRule : rule = withTakeMake r p := member
    subst rule
    obtain ⟨⟨-, -, mlNodup, takeLength, readLength, produceLength, -⟩, enabled, -, -⟩ := id admitted
    have takeLength' : r.body.take.length + 1 = tl'.length := by simpa using takeLength
    have produceLength' : r.body.produce.length + 1 = ml'.length := by simpa using produceLength
    have rdEmpty : rd = [] := List.length_eq_zero_iff.mp (by simpa using readLength.symm)
    subst rdEmpty
    have tlNonempty : tl' ≠ [] := fun empty => by rw [empty] at takeLength'; simp at takeLength'
    have mlNonempty : ml' ≠ [] := fun empty => by rw [empty] at produceLength'; simp at produceLength'
    obtain ⟨tl, o, rfl⟩ : ∃ tl o, tl' = tl ++ [o] :=
      ⟨tl'.dropLast, tl'.getLast tlNonempty, (List.dropLast_append_getLast tlNonempty).symm⟩
    obtain ⟨ml, m, rfl⟩ : ∃ ml m, ml' = ml ++ [m] :=
      ⟨ml'.dropLast, ml'.getLast mlNonempty, (List.dropLast_append_getLast mlNonempty).symm⟩
    have mFresh : m ∉ s.present := fun inside =>
      Finset.disjoint_left.mp enabled.fresh (by simp [Selection.commit]) inside
    have mNew : m ∉ ml := fun inside =>
      (List.nodup_append.mp mlNodup).2.2 m inside m (List.mem_singleton_self m) rfl
    obtain ⟨admitsIff, results⟩ := readTakeMake_core (r := r) (p := p) (s := s) invariantRename
      invariantModulo ext ι tl ml o m seen mFresh mNew
    have admittedF := admitsIff.mpr admitted
    exact ⟨readFiring r p ext ι tl ml o seen, admittedF,
      static_symm ((static_iff _ _).mp (results admittedF ∅))⟩

/-- **Law 7 by the method.** -/
theorem readTakeMake_static (r : Rule Tm) (p : Term atoms) (Q : Program Tm) (s : State Tm ℕ) :
    Cong ⟨{withRead r p} ∪ Q, s⟩ ⟨{withTakeMake r p} ∪ Q, s⟩ :=
  congruent_of_answersStatic (readTakeMake_answers r p).1 (readTakeMake_answers r p).2 Q s

/-! ## Laws 5 and 6, the other way -/

/-- **From Law 5 at one frame**: the guarded and the unguarded rule answer each other's firings with
statically equivalent results. -/
theorem entailedGuard_answers {r : Rule Tm} {l t : Tm r.locals}
    (entailed : X.Entails (a := r.locals) r.body.tell (fun b h =>
      X.E (a := b) (X.act (a := r.locals) (b := b) h l) (X.act (a := r.locals) (b := b) h t))) :
    AnswersStatic {withGuard r l t} {r} ∧ AnswersStatic {r} {withGuard r l t} :=
  (programs_iff (bounded_singleton _) (bounded_singleton _)).mp fun s => by
    have law := AtOneFrame.entailedGuard_congruent_oneFrame (obs := MayBarb X) entailed ∅ s
    rw [Set.empty_union, Set.empty_union] at law
    exact law

/-- **From Law 6**: a rule telling an entailed equation with kept sides and the rule without it answer
each other's firings with statically equivalent results. -/
theorem entailedTell_answers {r : Rule Tm} {e : Equation (Tm r.locals)}
    (entailed : X.Entails (a := r.locals) r.body.tell (fun b h =>
      X.E (a := b) (X.act (a := r.locals) (b := b) h e.1) (X.act (a := r.locals) (b := b) h e.2)))
    (leftKept : e.1 ∈ keptTerms r) (rightKept : e.2 ∈ keptTerms r) :
    AnswersStatic {withTell r e} {r} ∧ AnswersStatic {r} {withTell r e} :=
  (programs_iff (bounded_singleton _) (bounded_singleton _)).mp fun s => by
    have law := entailedTell_congruent (E := E) (obs := MayBarb X)
      (fun related β => mayBarb_modulo related β) entailed leftKept rightKept ∅ s
    rw [Set.empty_union, Set.empty_union] at law
    exact law

/-! ## The separations, as failures of answering -/

/-- The may-barbs see neither a renaming of identities nor a change modulo the knowledge. -/
theorem cong_basic_same {S T : Sys} (related : Cong S T) (c : Basic Tm ℕ E) (applyS : c.Applies S)
    (applyT : c.Applies T) : Cong (c.apply X S) (c.apply X T) :=
  related.basic_same (fun π p s => mayBarb_renameState X π p s)
    (fun related p => mayBarb_modulo related p) c applyS applyT

/-- **Absence**: after a row `9`, the unguarded spawn fires, and the guarded one has no firing to
answer it. -/
theorem absence_separates_static : ¬ Cong ⟨{spawnGuarded}, empty⟩ ⟨{spawn}, empty⟩ := by
  intro related
  have nine : Cong ⟨{spawnGuarded}, addRows empty {0} (fun _ => c 9)⟩
      ⟨{spawn}, addRows empty {0} (fun _ => c 9)⟩ :=
    cong_basic_same related nineRow (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
  obtain ⟨T, -, f, admitted, -⟩ := spawn_moves (P := {spawn}) (Set.mem_singleton _)
    (addRows empty {0} (fun _ => c 9))
    ⟨PUnit.unit, Subst.id atoms, fun e inside => absurd inside List.not_mem_nil⟩
  obtain ⟨g, admittedG, -⟩ := answers_of_congruent (bounded_singleton _) (bounded_singleton _)
    nine.symm f admitted
  exact guarded_stuck_nine (∅ ∪ {0}) (fun o => if o ∈ ({0} : Finset ℕ) then c 9 else c 0)
    ⟨0, by simp, by simp⟩ ⟨_, reduces_of_admits g admittedG⟩

/-- The rule that takes a `9` fires after a row `9`. -/
theorem takeNine_fires : ∃ f : Firing ℕ E ({takeNine} : Program Tm)
    (addRows empty {0} (fun _ => c 9)).frame, f.Admits X (addRows empty {0} (fun _ => c 9)) := by
  let s := addRows empty {0} (fun _ => c 9)
  let f : Firing ℕ E ({takeNine} : Program Tm) s.frame :=
    ⟨takeNine, Set.mem_singleton _, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩
  refine ⟨f, (admits_iff f).mpr ⟨?_, ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩⟩
  · apply fresh_of_ground action s f
    intro t member σ
    simp [f, takeNine, Rule.terms] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [f, s, Selection.commit, addRows, empty]
    · simp [f, Selection.commit]
    · simp [f, Selection.commit]
    · simp [f, s, Selection.commit, addRows, empty]
    · intro q inside
      simp [f, Selection.commit] at inside
  · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
    have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++
        [(Subst.applyTerm (Subst.id atoms) (c 9),
          Subst.applyTerm (Subst.id atoms) (if (0 : ℕ) ∈ ({0} : Finset ℕ) then c 9 else c 0))] ++
        [] ++ [] := inside
    simp only [List.nil_append, List.append_nil, List.mem_singleton] at unfolded
    subst unfolded
    rfl
  · intro check inside
    exact absurd inside List.not_mem_nil
  · intro q inside
    exact absurd inside List.not_mem_nil

/-- **A dormant rule**: after a row `9`, the rule that takes it fires, and the empty program has no
firing. -/
theorem dormant_separates_static : ¬ Cong ⟨{takeNine}, empty⟩ ⟨∅, empty⟩ := by
  intro related
  have nine : Cong ⟨{takeNine}, addRows empty {0} (fun _ => c 9)⟩
      ⟨∅, addRows empty {0} (fun _ => c 9)⟩ :=
    cong_basic_same related nineRow (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
  obtain ⟨f, admitted⟩ := takeNine_fires
  obtain ⟨g, -, -⟩ := answers_of_congruent (bounded_singleton _) bounded_empty nine f admitted
  exact Set.notMem_empty _ g.member

/-- **A guard that is not entailed**: at a row `6`, the rule that reads and makes `5` fires, and the
rule with the guard `x = 5` cannot. -/
theorem guard_not_entailed_static :
    ¬ Cong ⟨∅ ∪ {withGuard readMake x (c 5)}, rowSix⟩ ⟨∅ ∪ {readMake}, rowSix⟩ := by
  intro related
  obtain ⟨T, -, f, admitted, -⟩ := readMake_moves
  obtain ⟨g, admittedG, -⟩ := answers_of_congruent (bounded_union_singleton _)
    (bounded_union_singleton _) related.symm f admitted
  exact guarded_readMake_stuck ⟨_, reduces_of_admits g admittedG⟩

/-- **A tell that is not entailed**: the same with the tell `x = 5`. -/
theorem tell_not_entailed_static :
    ¬ Cong ⟨∅ ∪ {withTell readMake (x, c 5)}, rowSix⟩ ⟨∅ ∪ {readMake}, rowSix⟩ := by
  intro related
  obtain ⟨T, -, f, admitted, -⟩ := readMake_moves
  obtain ⟨g, admittedG, -⟩ := answers_of_congruent (bounded_union_singleton _)
    (bounded_union_singleton _) related.symm f admitted
  exact told_readMake_stuck ⟨_, reduces_of_admits g admittedG⟩

/-- **A tell whose sides are not kept**: the rule that tells `y = y` fires at the empty store with a
result that mentions `y`; the rule that does nothing answers only with a result that mentions
nothing. -/
theorem tell_unkept_static : ¬ Cong ⟨{withTell idle (y, y)}, unmentioned⟩ ⟨{idle}, unmentioned⟩ := by
  intro related
  let f : Firing ℕ E ({withTell idle (y, y)} : Program Tm) unmentioned.frame :=
    ⟨withTell idle (y, y), Set.mem_singleton _, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, []⟩
  have admitted : f.Admits X unmentioned := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_,
      fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩
    · intro b g h
      refine ⟨h, fun t mentioned => ?_, fun t inside => ?_⟩
      · rcases mentioned with none | none | ⟨o, present, -⟩
        · exact absurd none List.not_mem_nil
        · exact absurd none List.not_mem_nil
        · exact absurd present (Finset.notMem_empty o)
      · have isY : t = y := by simpa [f, idle, Rule.terms] using inside
        subst isY
        rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [f, Selection.commit]
    · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++ [] ++ [] ++ [(y, y)] := inside
      simp only [List.nil_append, List.mem_singleton] at unfolded
      subst unfolded
      rfl
  have leftKnowledge : (f.result X unmentioned).knowledge = [(y, y)] := rfl
  have leftMentions : (f.result X unmentioned).Mentions (.var 1) := by
    left
    rw [leftKnowledge]
    exact List.mem_singleton_self _
  obtain ⟨g, admittedG, static⟩ := answers_of_congruent (bounded_singleton _) (bounded_singleton _)
    related f admitted
  obtain ⟨rule, member, ext, ι, selection, seen⟩ := g
  have isIdle : rule = idle := member
  subst isIdle
  have rightRows := result_rows_empty _ admittedG rfl rfl
  have rightKnowledge : (Firing.result X unmentioned
      (⟨idle, member, ext, ι, selection, seen⟩ : Firing ℕ E ({idle} : Program Tm)
        unmentioned.frame)).knowledge = [] := rfl
  refine not_static_of_mentions (solvable_nil rightKnowledge) leftMentions ?_ (static_symm static)
  rintro (inside | inside | ⟨o, present, -⟩)
  · rw [rightKnowledge] at inside
    exact absurd inside List.not_mem_nil
  · rw [rightKnowledge] at inside
    exact absurd inside List.not_mem_nil
  · rw [rightRows] at present
    exact absurd present (Finset.notMem_empty o)

/-! ## The two worked pairs -/

/-- **An equivalent pair outside the seven laws**: adding the rule "make `5` where no `9` is
present" to the program "make `5`" changes nothing, beside every program, at every state. Every
firing of the guarded rule is reproduced by the unguarded one with the same result. -/
theorem subsumed_example (Q : Program Tm) (s : State Tm ℕ) :
    Cong ⟨{spawn} ∪ Q, s⟩ ⟨({spawn} ∪ {spawnGuarded}) ∪ Q, s⟩ := by
  refine congruent_of_answersStatic ?_ ?_ Q s
  · intro s f admitted
    exact ⟨reprogram f (Or.inl f.member), admitted, static_refl _⟩
  · rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    rcases (Set.mem_union _ _ _).mp member with isSpawn | isGuarded
    · exact ⟨⟨rule, isSpawn, ext, ι, selection, seen⟩, admitted, static_refl _⟩
    · have same : rule = spawnGuarded := isGuarded
      subst same
      refine ⟨⟨spawn, Set.mem_singleton _, ext, ι, selection, seen⟩,
        spawn_answers s ext ι selection seen admitted, ?_⟩
      have results : (⟨spawn, Set.mem_singleton _, ext, ι, selection, seen⟩ :
          Firing ℕ E ({spawn} : Program Tm) s.frame).result X s =
          (⟨spawnGuarded, member, ext, ι, selection, seen⟩ :
            Firing ℕ E ({spawn} ∪ {spawnGuarded} : Program Tm) s.frame).result X s := rfl
      rw [results]
      exact static_refl _

/-- **Touch any row**: take `x`, make `x`. -/
def touch : Rule Tm := ⟨PUnit.unit, ⟨[x], [], [], [], [x]⟩, []⟩

/-- After a context adds a row `7` to the empty store, touch fires. -/
theorem touch_fires : ∃ f : Firing ℕ E ({touch} : Program Tm)
    (addRows empty {0} (fun _ => c 7)).frame, f.Admits X (addRows empty {0} (fun _ => c 7)) := by
  let s := addRows empty {0} (fun _ => c 7)
  let f : Firing ℕ E ({touch} : Program Tm) s.frame :=
    ⟨touch, Set.mem_singleton _, PUnit.unit, fun v => .var (8 + v), ⟨[0], [], [1]⟩, []⟩
  refine ⟨f, (admits_iff f).mpr ⟨?_, ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩⟩
  · refine fresh_shift f (N := 8) (fun t mentioned => ?_) fun v => rfl
    rcases mentioned with inside | inside | ⟨o, -, rfl⟩
    · exact absurd inside List.not_mem_nil
    · exact absurd inside List.not_mem_nil
    · show size (if o ∈ ({0} : Finset ℕ) then c 7 else c 0) ≤ 8
      split <;> simp [size, c]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [f, s, Selection.commit, addRows, empty]
    · simp [f, Selection.commit]
    · simp [f, Selection.commit]
    · simp [f, s, Selection.commit, addRows, empty]
    · intro q inside
      simp [f, Selection.commit] at inside
  · refine ⟨PUnit.unit, fun _ => c 7, fun e inside => ?_⟩
    have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++
        [(Subst.applyTerm (fun v => .var (8 + v)) x,
          Subst.applyTerm (Subst.id atoms) (if (0 : ℕ) ∈ ({0} : Finset ℕ) then c 7 else c 0))] ++
        [] ++ [] := inside
    simp only [List.nil_append, List.append_nil, List.mem_singleton] at unfolded
    subst unfolded
    rfl
  · intro check inside
    exact absurd inside List.not_mem_nil
  · intro q inside
    exact absurd inside List.not_mem_nil

/-- **Touch is not the empty program**: at the empty store neither moves; the least context that
enables touch adds one row; after it, touch fires and the empty program cannot answer. -/
theorem touch_separates : ¬ Cong ⟨{touch}, empty⟩ ⟨∅, empty⟩ := by
  intro related
  have seven : Cong ⟨{touch}, addRows empty {0} (fun _ => c 7)⟩ ⟨∅, addRows empty {0} (fun _ => c 7)⟩ :=
    cong_basic_same related (.rows {0} fun _ _ => c 7) (Finset.disjoint_empty_right _)
      (Finset.disjoint_empty_right _)
  obtain ⟨f, admitted⟩ := touch_fires
  obtain ⟨g, -, -⟩ := answers_of_congruent (bounded_singleton _) bounded_empty seven f admitted
  exact Set.notMem_empty _ g.member

#print axioms renameState_one
#print axioms static_of_modulo
#print axioms static_rename
#print axioms static_refl
#print axioms static_symm
#print axioms static_trans
#print axioms answersStatic_of_subset
#print axioms same_rules_static
#print axioms union_static
#print axioms neverFires_answers
#print axioms neverFires_static
#print axioms dead_example_static
#print axioms readTakeMake_answers
#print axioms readTakeMake_static
#print axioms entailedGuard_answers
#print axioms entailedTell_answers
#print axioms absence_separates_static
#print axioms takeNine_fires
#print axioms dormant_separates_static
#print axioms guard_not_entailed_static
#print axioms tell_not_entailed_static
#print axioms tell_unkept_static
#print axioms subsumed_example
#print axioms touch_fires
#print axioms touch_separates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
