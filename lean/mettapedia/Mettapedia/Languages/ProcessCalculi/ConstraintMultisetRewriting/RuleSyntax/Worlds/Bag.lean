import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Local
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Worlds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Calculi

/-!
# Located knowledge with a supplied local event system

`Bag` holds a multiset of worlds and a set of shared closed rules. Each world
retains its own program, frame, knowledge and occurrence store. The local
step is a parameter: `Move.fire` uses an actual choice and successor of that
event system at the visible program. Commit and guard choices belong to the
supplied family. The existing single-firing construction is `events`.

Fork, publication and merge remain separate constructors. Publication carries
the source world's knowledge in a snapshot; merge requires joint solvability.

Adding worlds while keeping the shared space fixed preserves every local
policy (`Move.add_right`, `Move.cons`). Unioning shared rule spaces preserves
execution under the separate `ProgramMonotone` licence (`Move.beside`);
persistence and success beside a neighbour use that same licence. Confinement
of an inconsistent world uses `NoEventsAtInconsistent`.

`one_world_local_moves` identifies the actual local event at a singleton.
`one_world_moves` recovers the existing single-firing reduction as an explicit
instance. Side-by-side composition is commutative and associative; world
multisets cancel and the shared set is idempotent. These occurrence and
program representations do not assert preservation of counted origins.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (System Reduces reduces_iff)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open Hosting.Alternatives.Worlds (snapshot)
open NullsOnTheStep.ParallelClosed (ParallelCalculus)

universe uO uT uH uE uOcc uA uC

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## The state -/

/-- **A bag of worlds (a candidate state)**: the worlds, each a system of the present step, and the
closed rows of a shared space, each a rule. -/
@[ext]
structure Bag (Tm : Obj → Type uT) (O : Type uOcc) where
  worlds : Multiset (System Tm O)
  space : Program Tm

section Algebra

variable {O : Type uOcc}

/-- **Side by side**: the worlds of both, and the rows of both spaces. -/
def Bag.beside (W U : Bag Tm O) : Bag Tm O := ⟨W.worlds + U.worlds, W.space ∪ U.space⟩

/-- The bag with no world and no row. -/
def Bag.empty : Bag Tm O := ⟨0, ∅⟩

theorem Bag.beside_comm (W U : Bag Tm O) : W.beside U = U.beside W :=
  Bag.ext (add_comm _ _) (Set.union_comm _ _)

theorem Bag.beside_assoc (W U V : Bag Tm O) : (W.beside U).beside V = W.beside (U.beside V) :=
  Bag.ext (add_assoc _ _ _) (Set.union_assoc _ _ _)

theorem Bag.beside_empty (W : Bag Tm O) : W.beside Bag.empty = W :=
  Bag.ext (add_zero _) (Set.union_empty _)

/-- **Worlds cancel**: side by side with the same bag, equal bags of worlds come from equal bags of
worlds. -/
theorem beside_worlds_cancel {W U U' : Bag Tm O}
    (same : (W.beside U).worlds = (W.beside U').worlds) : U.worlds = U'.worlds :=
  add_left_cancel same

/-- **The space is idempotent**: beside a bag that holds the rows `R`, holding `R` again adds
nothing. -/
theorem space_idempotent (ws : Multiset (System Tm O)) (R : Program Tm) :
    (⟨0, R⟩ : Bag Tm O).beside ⟨ws, R⟩ = (⟨0, R⟩ : Bag Tm O).beside ⟨ws, ∅⟩ :=
  Bag.ext rfl ((Set.union_self R).trans (Set.union_empty R).symm)

/-- Two worlds of a bag, in either order. -/
theorem swap_worlds (a b : System Tm O) (s : Multiset (System Tm O)) (R : Program Tm) :
    (⟨a ::ₘ b ::ₘ s, R⟩ : Bag Tm O) = ⟨b ::ₘ a ::ₘ s, R⟩ :=
  congrArg (fun m => (⟨m, R⟩ : Bag Tm O)) (Multiset.cons_swap a b s)

/-- **Some world shows the observation.** -/
def Shows (barb : State Tm O → Prop) (W : Bag Tm O) : Prop := ∃ S ∈ W.worlds, barb S.state

theorem Shows.beside {barb : State Tm O → Prop} {W : Bag Tm O} (shows : Shows barb W) (U : Bag Tm O) :
    Shows barb (W.beside U) := by
  obtain ⟨S, member, holds⟩ := shows
  exact ⟨S, Multiset.mem_add.mpr (Or.inl member), holds⟩

end Algebra

/-! ## Moves -/

/-- **A joining of worlds**: an operation that makes one state of two, alive only if both were. -/
structure Joining (X : Frames Tm Hom) (O : Type uOcc) where
  join : State Tm O → State Tm O → State Tm O
  left_alive : ∀ s t, X.Solvable (join s t).knowledge → X.Solvable s.knowledge
  right_alive : ∀ s t, X.Solvable (join s t).knowledge → X.Solvable t.knowledge

variable {O : Type uOcc} [DecidableEq O] {Action : Type uA}

/-- The state of a world after its row `o` has been published. -/
def withoutRow (s : State Tm O) (o : O) : State Tm O :=
  ⟨s.frame, s.knowledge, s.present.erase o, s.label⟩

/-- **A move of a bag of worlds (a candidate step)**: a world fires a rule of its own or of the space;
a world is copied; a world publishes one of its rows to the space as a closed row; two worlds whose
joint knowledge is solvable are merged. -/
inductive Move (X : Frames Tm Hom) (J : Joining X O) (family : LocalSteps Tm O Action) :
    Bag Tm O → Bag Tm O → Prop
  | fire (rest : Multiset (System Tm O)) (space : Program Tm) (S : System Tm O)
      (choice : (family (S.program ∪ space)).Choice S.state) :
      Move X J family ⟨S ::ₘ rest, space⟩
        ⟨(⟨S.program, (family (S.program ∪ space)).next S.state choice⟩ : System Tm O) ::ₘ rest, space⟩
  | fork (rest : Multiset (System Tm O)) (space : Program Tm) (S : System Tm O) :
      Move X J family ⟨S ::ₘ rest, space⟩ ⟨S ::ₘ S ::ₘ rest, space⟩
  | publish (rest : Multiset (System Tm O)) (space : Program Tm) (S : System Tm O) (o : O)
      (present : o ∈ S.state.present) :
      Move X J family ⟨S ::ₘ rest, space⟩
        ⟨(⟨S.program, withoutRow S.state o⟩ : System Tm O) ::ₘ rest,
          insert (snapshot S.state (S.state.label o)) space⟩
  | merge (rest : Multiset (System Tm O)) (space : Program Tm) (S T : System Tm O)
      (alive : X.Solvable (J.join S.state T.state).knowledge) :
      Move X J family ⟨S ::ₘ T ::ₘ rest, space⟩
        ⟨(⟨S.program ∪ T.program, J.join S.state T.state⟩ : System Tm O) ::ₘ rest, space⟩

variable {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom} {J : Joining X O}
  {family : LocalSteps Tm O Action}

/-! ## Every move is a move beside any bag -/

/-- **Closed beside**: a move of a bag is a move of the bag beside any other, whatever the other
holds. -/
theorem Move.beside (monotone : ProgramMonotone family) {W W' : Bag Tm O}
    (move : Move X J family W W') (U : Bag Tm O) :
    Move X J family (W.beside U) (W'.beside U) := by
  cases move with
  | fire rest space S choice =>
      obtain ⟨nextChoice,same⟩ := monotone (S.program ∪ space) (S.program ∪ (space ∪ U.space))
        (Set.union_subset_union_right _ Set.subset_union_left) S.state _ ⟨choice,rfl⟩
      show Move X J family ⟨S ::ₘ rest + U.worlds, space ∪ U.space⟩
        ⟨(⟨S.program, (family (S.program ∪ space)).next S.state choice⟩ : System Tm O) ::ₘ rest + U.worlds, space ∪ U.space⟩
      simp only [Multiset.cons_add]
      have moved := Move.fire (X := X) (J := J) (family := family) (rest + U.worlds) (space ∪ U.space) S nextChoice
      rw [same] at moved
      exact moved
  | fork rest space S =>
      show Move X J family ⟨S ::ₘ rest + U.worlds, space ∪ U.space⟩
        ⟨S ::ₘ S ::ₘ rest + U.worlds, space ∪ U.space⟩
      simp only [Multiset.cons_add]
      exact Move.fork (rest + U.worlds) (space ∪ U.space) S
  | publish rest space S o present =>
      show Move X J family ⟨S ::ₘ rest + U.worlds, space ∪ U.space⟩
        ⟨(⟨S.program, withoutRow S.state o⟩ : System Tm O) ::ₘ rest + U.worlds,
          insert (snapshot S.state (S.state.label o)) space ∪ U.space⟩
      simp only [Multiset.cons_add, Set.insert_union]
      exact Move.publish (rest + U.worlds) (space ∪ U.space) S o present
  | merge rest space S T alive =>
      show Move X J family ⟨S ::ₘ T ::ₘ rest + U.worlds, space ∪ U.space⟩
        ⟨(⟨S.program ∪ T.program, J.join S.state T.state⟩ : System Tm O) ::ₘ rest + U.worlds,
          space ∪ U.space⟩
      simp only [Multiset.cons_add]
      exact Move.merge (rest + U.worlds) (space ∪ U.space) S T alive

theorem Move.add_right {W W' : Bag Tm O} (move : Move X J family W W')
    (more : Multiset (System Tm O)) :
    Move X J family ⟨W.worlds + more, W.space⟩ ⟨W'.worlds + more, W'.space⟩ := by
  cases move with
  | fire rest space S choice =>
      simpa only [Multiset.cons_add] using Move.fire (X := X) (J := J) (family := family) (rest + more) space S choice
  | fork rest space S =>
      simpa only [Multiset.cons_add] using Move.fork (X := X) (J := J) (family := family) (rest + more) space S
  | publish rest space S o present =>
      simpa only [Multiset.cons_add] using Move.publish (X := X) (J := J) (family := family) (rest + more) space S o present
  | merge rest space S T alive =>
      simpa only [Multiset.cons_add] using Move.merge (X := X) (J := J) (family := family) (rest + more) space S T alive

/-- Adding a world without changing the shared program preserves every local policy. -/
theorem Move.cons {W W' : Bag Tm O} (move : Move X J family W W') (D : System Tm O) :
    Move X J family ⟨D ::ₘ W.worlds, W.space⟩ ⟨D ::ₘ W'.worlds, W'.space⟩ := by
  have key : ∀ V : Bag Tm O, (⟨V.worlds + {D}, V.space⟩ : Bag Tm O) = ⟨D ::ₘ V.worlds, V.space⟩ := fun V =>
    Bag.ext ((add_comm V.worlds {D}).trans (Multiset.singleton_add D V.worlds)) rfl
  have moved := Move.add_right move {D}
  rw [key W, key W'] at moved
  exact moved

/-! ## The calculus of bags is persistent -/

/-- **The bags as a calculus with a parallel composition**: a move; side by side, for every two bags;
success when some world shows the observation; equality as the static equivalence. -/
def bagParallel (X : Frames Tm Hom) (J : Joining X O) (family : LocalSteps Tm O Action)
    (barb : State Tm O → Prop) : ParallelCalculus.{max uO uT uOcc} where
  Term := Bag Tm O
  step := Move X J family
  par := Bag.beside
  composable _ _ := True
  success := Shows barb
  same := Eq

/-- **Persistent**: every move is a move beside, success is kept beside, and the static equivalence is
equality. -/
theorem bagParallel_persistent (monotone : ProgramMonotone family) (barb : State Tm O → Prop) :
    (bagParallel X J family barb).Persistent where
  closed _ _ U move := Move.beside monotone move U
  persists _ U shows := Shows.beside shows U
  respects := ParallelCalculus.respects_of_eq fun _ _ same => same

/-- **No neighbour switches a bag off.** -/
theorem not_switchable (monotone : ProgramMonotone family) (barb : State Tm O → Prop) :
    ¬ (bagParallel X J family barb).Switchable :=
  (bagParallel_persistent monotone barb).not_switchable

/-- **Reachable success survives every neighbour**: whatever the rules of the bag, checks included,
and whatever the neighbour holds, its knowledge included. -/
theorem succeeds_beside (monotone : ProgramMonotone family) (barb : State Tm O → Prop)
    {W : Bag Tm O} (U : Bag Tm O) (succeeds : (bagParallel X J family barb).Succeeds W) :
    (bagParallel X J family barb).Succeeds (W.beside U) :=
  (bagParallel_persistent monotone barb).succeeds_par U succeeds

/-! ## The present step is the one-world case -/

/-- A reduction of a system is a move of every bag that holds it. -/
theorem move_of_reduces {S S' : System Tm O} (reduces : Reduces X O E S S')
    (rest : Multiset (System Tm O)) (R : Program Tm) :
    Move X J (events X O E) ⟨S ::ₘ rest, R⟩ ⟨S' ::ₘ rest, R⟩ := by
  obtain ⟨program', state'⟩ := S'
  obtain ⟨same, f, admitted, reached⟩ := reduces_iff.mp reduces
  have sameProgram : program' = S.program := same
  have sameState : f.result X S.state = state' := reached
  subst sameProgram
  subst sameState
  exact Move.fire (family := events X O E) rest R S ⟨widen Set.subset_union_left f, admitted⟩

/-- Runs of a system are runs of every bag that holds it. -/
theorem runs_of_system {S S' : System Tm O} (run : Relation.ReflTransGen (Reduces X O E) S S')
    (rest : Multiset (System Tm O)) (R : Program Tm) :
    Relation.ReflTransGen (Move X J (events X O E)) ⟨S ::ₘ rest, R⟩ ⟨S' ::ₘ rest, R⟩ := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (move_of_reduces last rest R)

/-- **A system that reaches the observation makes every bag that holds it succeed.** -/
theorem succeeds_of_world (barb : State Tm O → Prop) {S S' : System Tm O}
    (run : Relation.ReflTransGen (Reduces X O E) S S') (shows : barb S'.state)
    (rest : Multiset (System Tm O)) (R : Program Tm) :
    (bagParallel X J (events X O E) barb).Succeeds ⟨S ::ₘ rest, R⟩ :=
  ⟨(⟨S' ::ₘ rest, R⟩ : Bag Tm O), runs_of_system run rest R, S', Multiset.mem_cons_self S' rest,
    shows⟩

/-- With one world and an empty space, a move is exactly an event of the supplied local system. -/
theorem one_world_local_moves (S S' : System Tm O) :
    Move X J family ⟨{S}, ∅⟩ ⟨{S'}, ∅⟩ ↔
      S'.program = S.program ∧ Advances family S.program S.state S'.state := by
  constructor
  · intro move
    generalize hW : (⟨{S}, ∅⟩ : Bag Tm O) = W at move
    generalize hW' : (⟨{S'}, ∅⟩ : Bag Tm O) = W' at move
    cases move with
    | fire rest space S₀ choice =>
        injection hW with hws hspace
        injection hW' with hws' _
        obtain ⟨rfl, rfl⟩ := (Multiset.singleton_eq_cons_iff rest).mp hws
        subst hspace
        obtain ⟨rfl, -⟩ := (Multiset.singleton_eq_cons_iff 0).mp hws'
        exact ⟨rfl, by simpa only [Set.union_empty] using
          (show Advances family (S.program ∪ ∅) S.state _ from ⟨choice,rfl⟩)⟩
    | fork rest space S₀ =>
        injection hW' with hws' _
        have cards := congrArg Multiset.card hws'
        rw [Multiset.card_singleton, Multiset.card_cons, Multiset.card_cons] at cards
        omega
    | publish rest space S₀ o present =>
        injection hW' with _ hspace'
        exact absurd hspace'.symm (Set.insert_nonempty _ _).ne_empty
    | merge rest space S₀ T alive =>
        injection hW with hws _
        have cards := congrArg Multiset.card hws
        rw [Multiset.card_singleton, Multiset.card_cons, Multiset.card_cons] at cards
        omega
  · obtain ⟨program',state'⟩ := S'
    rintro ⟨same,advanced⟩
    change program' = S.program at same
    subst program'
    have inUnion : Advances family (S.program ∪ ∅) S.state state' := by
      simpa only [Set.union_empty] using advanced
    obtain ⟨choice,reached⟩ := inUnion
    subst state'
    exact Move.fire 0 ∅ S choice

/-- The existing single-firing construction is recovered as an explicit local instance. -/
theorem one_world_moves (S S' : System Tm O) :
    Move X J (events X O E) ⟨{S}, ∅⟩ ⟨{S'}, ∅⟩ ↔ Reduces X O E S S' := by
  rw [one_world_local_moves]
  constructor
  · rintro ⟨same,advanced⟩
    obtain ⟨firing,admitted,reached⟩ := (events_advances_iff X E S.program S.state S'.state).mp advanced
    exact reduces_iff.mpr ⟨same,firing,admitted,reached⟩
  · intro reduced
    obtain ⟨same,firing,admitted,reached⟩ := reduces_iff.mp reduced
    exact ⟨same,(events_advances_iff X E S.program S.state S'.state).mpr ⟨firing,admitted,reached⟩⟩

/-! ## A world whose knowledge has no solution is confined -/

/-- **No firing of any program is admitted at a state whose knowledge has no solution.** -/
theorem not_admits_of_unsolvable {P : Program Tm} {s : State Tm O} (dead : ¬ X.Solvable s.knowledge)
    (f : Firing O E P s.frame) : ¬ f.Admits X s := by
  rintro ⟨-, -, ⟨b, σ, solved⟩, -⟩
  exact dead ⟨b, _, Firing.knowledge_solved f solved⟩

/-- **Confinement.** Let a bag hold a world `D` whose knowledge has no solution. Every move of the bag
is a move the other worlds make without `D`, with `D` carried along unchanged; or a copy of `D`; or a
publication from `D`. In particular `D` takes no firing and no merge. -/
theorem dead_world_confined (safe : NoEventsAtInconsistent X family)
    {D : System Tm O} (dead : ¬ X.Solvable D.state.knowledge)
    {ws : Multiset (System Tm O)} {R : Program Tm} {W' : Bag Tm O}
    (move : Move X J family ⟨D ::ₘ ws, R⟩ W') :
    (∃ U : Bag Tm O, Move X J family ⟨ws, R⟩ U ∧ W' = ⟨D ::ₘ U.worlds, U.space⟩) ∨
      W' = ⟨D ::ₘ D ::ₘ ws, R⟩ ∨
      ∃ o ∈ D.state.present, W' = ⟨(⟨D.program, withoutRow D.state o⟩ : System Tm O) ::ₘ ws,
        insert (snapshot D.state (D.state.label o)) R⟩ := by
  generalize hW : (⟨D ::ₘ ws, R⟩ : Bag Tm O) = W at move
  cases move with
  | fire rest space S choice =>
      injection hW with hws hR
      subst hR
      rcases Multiset.cons_eq_cons.mp hws with ⟨rfl, rfl⟩ | ⟨-, cs, rfl, rfl⟩
      · exact (safe _ _ dead).elim choice
      · exact Or.inl ⟨⟨(⟨S.program, (family (S.program ∪ R)).next S.state choice⟩ : System Tm O) ::ₘ cs, R⟩,
          Move.fire cs R S choice, swap_worlds _ _ _ _⟩
  | fork rest space S =>
      injection hW with hws hR
      subst hR
      rcases Multiset.cons_eq_cons.mp hws with ⟨rfl, rfl⟩ | ⟨-, cs, rfl, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ⟨⟨S ::ₘ S ::ₘ cs, R⟩, Move.fork cs R S,
          congrArg (fun m => (⟨m, R⟩ : Bag Tm O))
            ((congrArg (fun m => S ::ₘ m) (Multiset.cons_swap S D cs)).trans
              (Multiset.cons_swap S D (S ::ₘ cs)))⟩
  | publish rest space S o present =>
      injection hW with hws hR
      subst hR
      rcases Multiset.cons_eq_cons.mp hws with ⟨rfl, rfl⟩ | ⟨-, cs, rfl, rfl⟩
      · exact Or.inr (Or.inr ⟨o, present, rfl⟩)
      · exact Or.inl ⟨⟨(⟨S.program, withoutRow S.state o⟩ : System Tm O) ::ₘ cs,
            insert (snapshot S.state (S.state.label o)) R⟩,
          Move.publish cs R S o present, swap_worlds _ _ _ _⟩
  | merge rest space S T alive =>
      injection hW with hws hR
      subst hR
      rcases Multiset.cons_eq_cons.mp hws with ⟨rfl, -⟩ | ⟨-, cs, rfl, later⟩
      · exact (dead (J.left_alive _ _ alive)).elim
      · rcases Multiset.cons_eq_cons.mp later with ⟨rfl, -⟩ | ⟨-, cs', rfl, rfl⟩
        · exact (dead (J.right_alive _ _ alive)).elim
        · exact Or.inl ⟨⟨(⟨S.program ∪ T.program, J.join S.state T.state⟩ : System Tm O) ::ₘ cs', R⟩,
            Move.merge cs' R S T alive, swap_worlds _ _ _ _⟩

#print axioms Bag.beside_comm
#print axioms Bag.beside_assoc
#print axioms Bag.beside_empty
#print axioms beside_worlds_cancel
#print axioms space_idempotent
#print axioms Move.beside
#print axioms Move.cons
#print axioms bagParallel_persistent
#print axioms not_switchable
#print axioms succeeds_beside
#print axioms move_of_reduces
#print axioms succeeds_of_world
#print axioms one_world_moves
#print axioms not_admits_of_unsolvable
#print axioms dead_world_confined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
