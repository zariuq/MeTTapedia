import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Sharing

/-!
# Confinement along runs: dead worlds and what they publish are no neighbours

`Worlds.Bag` confines a world whose knowledge has no solution move by move
(`dead_world_confined`). This module follows whole runs, in which such a world is copied and
publishes, and its published rows stay in the space.

* `DeadRow`: a row published from a world whose knowledge has no solution. `DeadBeside X W V`: the bag
  `V` is the bag `W` together with worlds whose knowledge has no solution and with dead rows in the
  space.
* `DeadBeside.move`: every move of `V` is a move of the dead part alone, after which `V` is still
  `W` beside dead worlds and rows, or a move of `W`, after which the same holds of the results.
  `DeadBeside.runs`: so every run of `V` is a run of `W`, up to the dead part.
* **`confined`**: for an observation that no world with unsolvable knowledge shows, **what the bag
  reaches beside dead worlds and dead rows, it reaches without them.**
* **`dead_world_is_no_neighbour`**: a bag with a world whose knowledge has no solution reaches the
  observation exactly when the bag without that world does. With `succeeds_beside`, a dead world is a
  unit of side by side, for reachable success.
* `dead_world_is_no_neighbour_mayBarb`: the instance for a may-barb, which no dead world shows
  (`Equivalence.not_mayBarb_of_unsolvable`).
* `must_barb_not_silent`: the control for that hypothesis: a dead world that holds a row shows every
  must-barb.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (System Pattern MayBarb MustBarb not_mayBarb_of_unsolvable mustBarb_of_unsolvable)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open Hosting.Alternatives.Worlds (snapshot)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A dead row**: a row published from a world whose knowledge has no solution. -/
def DeadRow (X : Frames Tm Hom) (O : Type uOcc) (r : Rule Tm) : Prop :=
  ∃ (s : State Tm O) (atom : Tm s.frame), ¬ X.Solvable s.knowledge ∧ r = snapshot s atom

/-- **`V` is `W` beside dead worlds and dead rows**: the worlds of `V` are those of `W` and worlds whose
knowledge has no solution; the space of `V` holds the rows of `W`'s space, and beyond them only dead
rows. -/
structure DeadBeside {O : Type uOcc} (X : Frames Tm Hom) (W V : Bag Tm O) : Prop where
  worlds : ∃ Ds : Multiset (System Tm O), (∀ D ∈ Ds, ¬ X.Solvable D.state.knowledge) ∧
    V.worlds = W.worlds + Ds
  space : W.space ⊆ V.space
  rows : ∀ r ∈ V.space, r ∈ W.space ∨ DeadRow X O r

variable {O : Type uOcc} [DecidableEq O] {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom}
  {J : Joining X O}

/-- **Every move beside dead worlds and dead rows is a move of the dead part or a move of the bag
without it.** -/
theorem DeadBeside.move {W V V' : Bag Tm O} (beside : DeadBeside X W V) (move : Move X J (events X O E) V V') :
    DeadBeside X W V' ∨ ∃ W', Move X J (events X O E) W W' ∧ DeadBeside X W' V' := by
  obtain ⟨ww, wsp⟩ := W
  obtain ⟨⟨Ds, dead, hworlds⟩, hspace, hrows⟩ := beside
  cases move with
  | fire rest space S choice =>
      obtain ⟨f, admitted⟩ := choice
      have worldsEq : S ::ₘ rest = ww + Ds := hworlds
      have rowsOf : ∀ r ∈ space, r ∈ wsp ∨ DeadRow X O r := hrows
      have member : S ∈ ww + Ds := by
        rw [← worldsEq]
        exact Multiset.mem_cons_self S rest
      rcases Multiset.mem_add.mp member with inW | inD
      · obtain ⟨w1, rfl⟩ := Multiset.exists_cons_of_mem inW
        have restIs : w1 + Ds = rest :=
          (Multiset.cons_inj_right S).mp ((Multiset.cons_add S w1 Ds).symm.trans worldsEq.symm)
        subst restIs
        have ruleIn : f.rule ∈ S.program ∪ wsp := by
          rcases (Set.mem_union _ _ _).mp f.member with inP | inSpace
          · exact Set.mem_union_left _ inP
          · rcases rowsOf _ inSpace with old | ⟨s, atom, deadS, isRow⟩
            · exact Set.mem_union_right _ old
            · exact (snapshot_dead_never_fires atom deadS f isRow admitted).elim
        exact Or.inr ⟨⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ w1, wsp⟩,
          Move.fire (family := events X O E) w1 wsp S ⟨⟨f.rule, ruleIn, f.ext, f.opening, f.selection, f.seen⟩, admitted⟩,
          ⟨⟨Ds, dead, (Multiset.cons_add _ _ _).symm⟩, hspace, hrows⟩⟩
      · exact (not_admits_of_unsolvable (dead S inD) f admitted).elim
  | fork rest space S =>
      have worldsEq : S ::ₘ rest = ww + Ds := hworlds
      have member : S ∈ ww + Ds := by
        rw [← worldsEq]
        exact Multiset.mem_cons_self S rest
      rcases Multiset.mem_add.mp member with inW | inD
      · obtain ⟨w1, rfl⟩ := Multiset.exists_cons_of_mem inW
        have restIs : w1 + Ds = rest :=
          (Multiset.cons_inj_right S).mp ((Multiset.cons_add S w1 Ds).symm.trans worldsEq.symm)
        subst restIs
        have copied : S ::ₘ S ::ₘ (w1 + Ds) = S ::ₘ S ::ₘ w1 + Ds := by
          rw [Multiset.cons_add, Multiset.cons_add]
        exact Or.inr ⟨⟨S ::ₘ S ::ₘ w1, wsp⟩, Move.fork (family := events X O E) w1 wsp S,
          ⟨⟨Ds, dead, copied⟩, hspace, hrows⟩⟩
      · obtain ⟨d1, rfl⟩ := Multiset.exists_cons_of_mem inD
        have restIs : ww + d1 = rest :=
          (Multiset.cons_inj_right S).mp ((Multiset.add_cons S ww d1).symm.trans worldsEq.symm)
        subst restIs
        have copied : S ::ₘ S ::ₘ (ww + d1) = ww + S ::ₘ S ::ₘ d1 := by
          rw [Multiset.add_cons, Multiset.add_cons]
        refine Or.inl ⟨⟨S ::ₘ S ::ₘ d1, fun D inside => ?_, copied⟩, hspace, hrows⟩
        rcases Multiset.mem_cons.mp inside with same | later
        · rw [same]
          exact dead S (Multiset.mem_cons_self S d1)
        · exact dead D later
  | publish rest space S o present =>
      have worldsEq : S ::ₘ rest = ww + Ds := hworlds
      have spaceOf : wsp ⊆ space := hspace
      have rowsOf : ∀ r ∈ space, r ∈ wsp ∨ DeadRow X O r := hrows
      have member : S ∈ ww + Ds := by
        rw [← worldsEq]
        exact Multiset.mem_cons_self S rest
      rcases Multiset.mem_add.mp member with inW | inD
      · obtain ⟨w1, rfl⟩ := Multiset.exists_cons_of_mem inW
        have restIs : w1 + Ds = rest :=
          (Multiset.cons_inj_right S).mp ((Multiset.cons_add S w1 Ds).symm.trans worldsEq.symm)
        subst restIs
        refine Or.inr ⟨⟨(⟨S.program, withoutRow S.state o⟩ : System Tm O) ::ₘ w1,
            insert (snapshot S.state (S.state.label o)) wsp⟩,
          Move.publish (family := events X O E) w1 wsp S o present,
          ⟨⟨Ds, dead, (Multiset.cons_add _ _ _).symm⟩, Set.insert_subset_insert spaceOf,
            fun r inside => ?_⟩⟩
        rcases Set.mem_insert_iff.mp inside with isRow | old
        · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl isRow))
        · rcases rowsOf r old with inW' | deadRow
          · exact Or.inl (Set.mem_insert_of_mem _ inW')
          · exact Or.inr deadRow
      · obtain ⟨d1, rfl⟩ := Multiset.exists_cons_of_mem inD
        have restIs : ww + d1 = rest :=
          (Multiset.cons_inj_right S).mp ((Multiset.add_cons S ww d1).symm.trans worldsEq.symm)
        subst restIs
        refine Or.inl ⟨⟨(⟨S.program, withoutRow S.state o⟩ : System Tm O) ::ₘ d1,
            fun D inside => ?_, (Multiset.add_cons _ _ _).symm⟩,
          fun r inW' => Set.mem_insert_of_mem _ (spaceOf inW'), fun r inside => ?_⟩
        · rcases Multiset.mem_cons.mp inside with same | later
          · rw [same]
            exact dead S (Multiset.mem_cons_self S d1)
          · exact dead D (Multiset.mem_cons_of_mem later)
        · rcases Set.mem_insert_iff.mp inside with isRow | old
          · exact Or.inr ⟨S.state, S.state.label o, dead S (Multiset.mem_cons_self S d1), isRow⟩
          · exact rowsOf r old
  | merge rest space S T alive =>
      have worldsEq : S ::ₘ T ::ₘ rest = ww + Ds := hworlds
      have memberS : S ∈ ww + Ds := by
        rw [← worldsEq]
        exact Multiset.mem_cons_self S (T ::ₘ rest)
      rcases Multiset.mem_add.mp memberS with inW | inD
      · obtain ⟨w1, rfl⟩ := Multiset.exists_cons_of_mem inW
        have tail : w1 + Ds = T ::ₘ rest :=
          (Multiset.cons_inj_right S).mp ((Multiset.cons_add S w1 Ds).symm.trans worldsEq.symm)
        have memberT : T ∈ w1 + Ds := by
          rw [tail]
          exact Multiset.mem_cons_self T rest
        rcases Multiset.mem_add.mp memberT with inW1 | inD1
        · obtain ⟨w2, rfl⟩ := Multiset.exists_cons_of_mem inW1
          have restIs : w2 + Ds = rest :=
            (Multiset.cons_inj_right T).mp ((Multiset.cons_add T w2 Ds).symm.trans tail)
          subst restIs
          exact Or.inr ⟨⟨(⟨S.program ∪ T.program, J.join S.state T.state⟩ : System Tm O) ::ₘ w2, wsp⟩,
            Move.merge (family := events X O E) w2 wsp S T alive,
            ⟨⟨Ds, dead, (Multiset.cons_add _ _ _).symm⟩, hspace, hrows⟩⟩
        · exact (dead T inD1 (J.right_alive _ _ alive)).elim
      · exact (dead S inD (J.left_alive _ _ alive)).elim

/-- **Every run beside dead worlds and dead rows is a run of the bag without them**, up to the dead
part. -/
theorem DeadBeside.runs {W V V' : Bag Tm O} (beside : DeadBeside X W V)
    (run : Relation.ReflTransGen (Move X J (events X O E)) V V') :
    ∃ W', Relation.ReflTransGen (Move X J (events X O E)) W W' ∧ DeadBeside X W' V' := by
  induction run with
  | refl => exact ⟨W, .refl, beside⟩
  | tail _ last ih =>
      obtain ⟨W₁, run₁, beside₁⟩ := ih
      rcases beside₁.move last with stays | ⟨W₂, moved, beside₂⟩
      · exact ⟨W₁, run₁, stays⟩
      · exact ⟨W₂, run₁.tail moved, beside₂⟩

omit [DecidableEq O] in
/-- What is shown beside dead worlds is shown without them, for an observation no dead world shows. -/
theorem DeadBeside.shows {barb : State Tm O → Prop}
    (silent : ∀ s : State Tm O, ¬ X.Solvable s.knowledge → ¬ barb s) {W V : Bag Tm O}
    (beside : DeadBeside X W V) (shows : Shows barb V) : Shows barb W := by
  obtain ⟨S, member, holds⟩ := shows
  obtain ⟨Ds, dead, worldsEq⟩ := beside.worlds
  rw [worldsEq] at member
  rcases Multiset.mem_add.mp member with inW | inD
  · exact ⟨S, inW, holds⟩
  · exact (silent S.state (dead S inD) holds).elim

/-- **Confinement along runs**: for an observation that no world with unsolvable knowledge shows, what
a bag reaches beside dead worlds and dead rows, it reaches without them. -/
theorem confined {barb : State Tm O → Prop}
    (silent : ∀ s : State Tm O, ¬ X.Solvable s.knowledge → ¬ barb s) {W V : Bag Tm O}
    (beside : DeadBeside X W V) (succeeds : (bagParallel X J (events X O E) barb).Succeeds V) :
    (bagParallel X J (events X O E) barb).Succeeds W := by
  obtain ⟨V', run, shows⟩ := succeeds
  obtain ⟨W', run', beside'⟩ := beside.runs run
  exact ⟨W', run', beside'.shows silent shows⟩

/-- **A dead world is no neighbour**: a bag with a world whose knowledge has no solution reaches the
observation exactly when the bag without that world does. -/
theorem dead_world_is_no_neighbour {barb : State Tm O → Prop}
    (silent : ∀ s : State Tm O, ¬ X.Solvable s.knowledge → ¬ barb s) {D : System Tm O}
    (dead : ¬ X.Solvable D.state.knowledge) (ws : Multiset (System Tm O)) (R : Program Tm) :
    (bagParallel X J (events X O E) barb).Succeeds ⟨D ::ₘ ws, R⟩ ↔ (bagParallel X J (events X O E) barb).Succeeds ⟨ws, R⟩ := by
  have worldsEq : D ::ₘ ws = ws + {D} :=
    ((add_comm ws {D}).trans (Multiset.singleton_add D ws)).symm
  constructor
  · have deadOnly : ∀ D' ∈ ({D} : Multiset (System Tm O)), ¬ X.Solvable D'.state.knowledge := by
      intro D' inside
      rw [Multiset.mem_singleton.mp inside]
      exact dead
    exact confined silent
      ⟨⟨{D}, deadOnly, worldsEq⟩, fun _ inside => inside, fun _ inside => Or.inl inside⟩
  · intro succeeds
    have beside := succeeds_beside (X := X) (J := J) (family := events X O E)
      (events_program_monotone X E) barb (⟨{D}, ∅⟩ : Bag Tm O) succeeds
    have same : (⟨ws, R⟩ : Bag Tm O).beside ⟨{D}, ∅⟩ = ⟨D ::ₘ ws, R⟩ :=
      Bag.ext worldsEq.symm (Set.union_empty R)
    rw [same] at beside
    exact beside

/-- **A dead world is no neighbour, for a may-barb.** -/
theorem dead_world_is_no_neighbour_mayBarb (p : Pattern Tm) {D : System Tm O}
    (dead : ¬ X.Solvable D.state.knowledge) (ws : Multiset (System Tm O)) (R : Program Tm) :
    (bagParallel X J (events X O E) (MayBarb X p)).Succeeds ⟨D ::ₘ ws, R⟩ ↔
      (bagParallel X J (events X O E) (MayBarb X p)).Succeeds ⟨ws, R⟩ :=
  dead_world_is_no_neighbour (fun _ unsolvable => not_mayBarb_of_unsolvable unsolvable) dead ws R

omit [DecidableEq O] in
/-- **Control for the hypothesis on the observation**: a must-barb is shown by every world whose
knowledge has no solution and that holds a row (`Equivalence.mustBarb_of_unsolvable`), so a bag with
such a world shows every must-barb, whatever the bag without it shows. -/
theorem must_barb_not_silent (p : Pattern Tm) {D : System Tm O}
    (dead : ¬ X.Solvable D.state.knowledge) {o : O} (present : o ∈ D.state.present)
    (ws : Multiset (System Tm O)) (R : Program Tm) :
    Shows (MustBarb X p) (⟨D ::ₘ ws, R⟩ : Bag Tm O) :=
  ⟨D, Multiset.mem_cons_self D ws, mustBarb_of_unsolvable dead present⟩

#print axioms must_barb_not_silent
#print axioms DeadBeside.move
#print axioms DeadBeside.runs
#print axioms DeadBeside.shows
#print axioms confined
#print axioms dead_world_is_no_neighbour
#print axioms dead_world_is_no_neighbour_mayBarb

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
