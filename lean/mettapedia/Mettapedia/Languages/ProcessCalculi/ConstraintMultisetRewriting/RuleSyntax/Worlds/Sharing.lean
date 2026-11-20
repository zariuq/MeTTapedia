import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Bag
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual

/-!
# What a closed row carries, and what its use costs

A row of the shared space of a bag of worlds (`Bag`) is a rule
(`Hosting.Alternatives.Worlds.snapshot`): the publishing world's frame as its unknowns, the
publishing world's knowledge as its told equations, the published atom as its made row. A world uses
it by firing it.

## The joint information of a shared premise

* `snapshot_information`, `snapshot_models_iff`: **the information of a firing of a closed row is the
  reader's knowledge, along the extension, together with the publisher's knowledge at publication,
  along the opening.** One solution has to solve both.
* `import_knows`: every solution of the reader's knowledge after the firing solves the publisher's
  knowledge along the opening: the reader knows of the copy what the publisher knew of the row.
  `import_label`: the copy is the atom along the opening.
* `snapshot_importable`: over a frame action with a weakly terminal frame, a closed row is fired with
  a fresh opening **exactly when the reader's knowledge is solvable and the publisher's knowledge at
  publication was**: the opening keeps the two apart, so their joint solvability is the solvability of
  each.
* `import_conservative`: such a firing adds no relation between what the reader mentions and the
  publisher's unknowns: every solution of the reader's knowledge and every solution of the publisher's
  extend together to a solution of the result, which reads the copy as the publisher's solution reads
  the atom.

## Confinement of a published row

* `snapshot_dead_never_fires`: **a row published from a world whose knowledge has no solution is fired
  by no world**, at any state.
* `dead_row_unused`: so, with such a row in the space, every admitted firing of every world is a firing
  of a rule of the world or of the rest of the space; and every firing without the row is a firing with
  it (`widen`). The row disables nothing.

## Order of a publication and a firing

* `fire_publish_commute`: **a firing in one world and a publication from another reach one bag in
  either order.** In one order the firing happens while the published row is already in the space: it
  is the same firing, of the larger space.
* `not_before_publication`: the converse fails where the two interact: a firing of the published row
  itself exists only after the publication.
* `fire_fire_commute`: firings in two worlds reach one bag in either order.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (System)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open Hosting.Alternatives.Worlds (snapshot)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## The joint information of a shared premise -/

section Information

variable {O : Type uOcc} {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **The information of a firing of a closed row**: the reader's knowledge along the extension, then
the publisher's knowledge along the opening. -/
theorem snapshot_information (s t : State Tm O) (atom : Tm s.frame) (member : snapshot s atom ∈ P)
    (ext : E.Ext t.frame) (opening : Hom s.frame (E.target ext)) (selection : Selection O)
    (seen : List (Finset O)) :
    Firing.information X t
        (⟨snapshot s atom, member, ext, opening, selection, seen⟩ : Firing O E P t.frame) =
      X.applyStore (E.weaken ext) t.knowledge ++ X.applyStore opening s.knowledge := by
  show X.applyStore (E.weaken ext) t.knowledge ++ [] ++ [] ++ X.applyStore opening s.knowledge = _
  rw [List.append_nil, List.append_nil]

/-- **The joint information of a shared premise**: a solution of the information of a firing of a
closed row solves the reader's knowledge along the extension and the publisher's knowledge along the
opening, both at once. -/
theorem snapshot_models_iff (s t : State Tm O) (atom : Tm s.frame) (member : snapshot s atom ∈ P)
    (ext : E.Ext t.frame) (opening : Hom s.frame (E.target ext)) (selection : Selection O)
    (seen : List (Finset O)) {b : Obj} (σ : Hom (E.target ext) b) :
    X.Models σ (Firing.information X t
        (⟨snapshot s atom, member, ext, opening, selection, seen⟩ : Firing O E P t.frame)) ↔
      X.Models (X.comp σ (E.weaken ext)) t.knowledge ∧ X.Models (X.comp σ opening) s.knowledge := by
  rw [snapshot_information, Frames.models_append, Frames.models_applyStore, Frames.models_applyStore]

end Information

variable {O : Type uOcc} [DecidableEq O] {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom}

section Premise

variable {P : Program Tm}

/-- **The reader knows of the copy what the publisher knew of the row**: every solution of the
knowledge after a firing of a closed row solves the reader's old knowledge along the extension and the
publisher's knowledge along the opening. -/
theorem import_knows (s t : State Tm O) (atom : Tm s.frame) (member : snapshot s atom ∈ P)
    (ext : E.Ext t.frame) (opening : Hom s.frame (E.target ext)) (selection : Selection O)
    (seen : List (Finset O)) {b : Obj} (σ : Hom (E.target ext) b)
    (solved : X.Models σ (Firing.result X t
      (⟨snapshot s atom, member, ext, opening, selection, seen⟩ : Firing O E P t.frame)).knowledge) :
    X.Models (X.comp σ (E.weaken ext)) t.knowledge ∧ X.Models (X.comp σ opening) s.knowledge :=
  (snapshot_models_iff s t atom member ext opening selection seen σ).mp solved

/-- **A row published from a world whose knowledge has no solution is fired by no world.** -/
theorem snapshot_dead_never_fires {s : State Tm O} (atom : Tm s.frame)
    (dead : ¬ X.Solvable s.knowledge) {t : State Tm O} (f : Firing O E P t.frame)
    (isRow : f.rule = snapshot s atom) : ¬ f.Admits X t := by
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  have same : rule = snapshot s atom := isRow
  subst same
  rintro ⟨-, -, ⟨b, σ, solved⟩, -⟩
  exact dead ⟨b, _, ((snapshot_models_iff s t atom member ext opening selection seen σ).mp solved).2⟩

/-- **Such a row disables nothing and enables nothing**: with it in the space, every admitted firing
is a firing of a rule of the program or of the rest of the space. -/
theorem dead_row_unused {R : Program Tm} {s : State Tm O} (atom : Tm s.frame)
    (dead : ¬ X.Solvable s.knowledge) {t : State Tm O}
    (f : Firing O E (P ∪ insert (snapshot s atom) R) t.frame) (admitted : f.Admits X t) :
    f.rule ∈ P ∪ R := by
  rcases (Set.mem_union _ _ _).mp f.member with inP | inSpace
  · exact Set.mem_union_left R inP
  · rcases Set.mem_insert_iff.mp inSpace with isRow | inR
    · exact (snapshot_dead_never_fires atom dead f isRow admitted).elim
    · exact Set.mem_union_right P inR

/-- **The copy is the atom along the opening.** -/
theorem import_label (s t : State Tm O) (atom : Tm s.frame) (member : snapshot s atom ∈ P)
    (ext : E.Ext t.frame) (opening : Hom s.frame (E.target ext)) (o : O) (seen : List (Finset O))
    (admitted : Firing.Admits X t
      (⟨snapshot s atom, member, ext, opening, ⟨[], [], [o]⟩, seen⟩ : Firing O E P t.frame)) :
    (Firing.result X t
      (⟨snapshot s atom, member, ext, opening, ⟨[], [], [o]⟩, seen⟩ : Firing O E P t.frame)).label o =
        X.act opening atom :=
  Firing.result_label_made _ admitted.1 List.mem_cons_self

/-- **A closed row is fired with a fresh opening exactly when the reader's knowledge is solvable and
the publisher's knowledge at publication was**, over a frame action with a weakly terminal frame. -/
theorem snapshot_importable {terminalFrame : Obj} (terminal : Frames.WeaklyTerminal Hom terminalFrame)
    (s t : State Tm O) (atom : Tm s.frame) (member : snapshot s atom ∈ P) (ext : E.Ext t.frame)
    (opening : Hom s.frame (E.target ext)) (o : O)
    (fresh : Firing.Fresh X t
      (⟨snapshot s atom, member, ext, opening, ⟨[], [], [o]⟩, []⟩ : Firing O E P t.frame))
    (new : o ∉ t.present) :
    Firing.Admits X t
        (⟨snapshot s atom, member, ext, opening, ⟨[], [], [o]⟩, []⟩ : Firing O E P t.frame) ↔
      X.Solvable t.knowledge ∧ X.Solvable s.knowledge := by
  constructor
  · rintro ⟨-, -, ⟨b, σ, solved⟩, -⟩
    obtain ⟨reader, publisher⟩ :=
      (snapshot_models_iff s t atom member ext opening ⟨[], [], [o]⟩ [] σ).mp solved
    exact ⟨⟨b, _, reader⟩, ⟨b, _, publisher⟩⟩
  · rintro ⟨reader, publisher⟩
    obtain ⟨g, known⟩ := (Frames.solvable_iff_into terminal t.knowledge).mp reader
    obtain ⟨h, told⟩ := (Frames.solvable_iff_into terminal s.knowledge).mp publisher
    obtain ⟨u, solved, -, -⟩ := information_amalgamates
      (⟨snapshot s atom, member, ext, opening, ⟨[], [], [o]⟩, []⟩ : Firing O E P t.frame) fresh rfl rfl
      g h known told
    refine ⟨⟨fresh, List.nodup_nil, List.nodup_singleton o, rfl, rfl, rfl, rfl⟩, ?_,
      ⟨terminalFrame, u, solved⟩, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, new]
    · intro b σ _
      exact ⟨fun c inside => absurd inside List.not_mem_nil,
        fun q inside => absurd inside List.not_mem_nil⟩

omit [DecidableEq O] in
/-- **Using a closed row adds no relation between what the reader mentions and the publisher's
unknowns**: every solution of the reader's knowledge and every solution of the publisher's knowledge
extend together to a solution of the information, which agrees with the first on what the reader
mentions and reads the copy as the second reads the atom. -/
theorem import_conservative (s t : State Tm O) (atom : Tm s.frame) (member : snapshot s atom ∈ P)
    (ext : E.Ext t.frame) (opening : Hom s.frame (E.target ext)) (o : O)
    (fresh : Firing.Fresh X t
      (⟨snapshot s atom, member, ext, opening, ⟨[], [], [o]⟩, []⟩ : Firing O E P t.frame))
    {b : Obj} (g : Hom t.frame b) (h : Hom s.frame b) (known : X.Models g t.knowledge)
    (told : X.Models h s.knowledge) :
    ∃ u : Hom (E.target ext) b,
      X.Models u (Firing.information X t
        (⟨snapshot s atom, member, ext, opening, ⟨[], [], [o]⟩, []⟩ : Firing O E P t.frame)) ∧
      (∀ x, t.Mentions x → X.E (X.act u (X.act (E.weaken ext) x)) (X.act g x)) ∧
      X.E (X.act u (X.act opening atom)) (X.act h atom) := by
  obtain ⟨u, solved, state, rule⟩ := information_amalgamates
    (⟨snapshot s atom, member, ext, opening, ⟨[], [], [o]⟩, []⟩ : Firing O E P t.frame) fresh rfl rfl
    g h known told
  exact ⟨u, solved, state, rule atom
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self atom)))⟩

end Premise

/-! ## Order of a publication and a firing -/

variable {J : Joining X O}

/-- A move between bags that are equal to the given ones. -/
theorem Move.cast {W W' V V' : Bag Tm O} (move : Move X J (events X O E) W W') (source : W = V) (target : W' = V') :
    Move X J (events X O E) V V' := by
  subst source
  subst target
  exact move

/-- **A firing in one world and a publication from another reach one bag in either order.** -/
theorem fire_publish_commute (rest : Multiset (System Tm O)) (R : Program Tm) (S T : System Tm O)
    (f : Firing O E (S.program ∪ R) S.state.frame) (admitted : f.Admits X S.state) (o : O)
    (present : o ∈ T.state.present) :
    Move X J (events X O E) ⟨S ::ₘ T ::ₘ rest, R⟩
        ⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ T ::ₘ rest, R⟩ ∧
      Move X J (events X O E) ⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ T ::ₘ rest, R⟩
        ⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ
            (⟨T.program, withoutRow T.state o⟩ : System Tm O) ::ₘ rest,
          insert (snapshot T.state (T.state.label o)) R⟩ ∧
      Move X J (events X O E) ⟨S ::ₘ T ::ₘ rest, R⟩
        ⟨S ::ₘ (⟨T.program, withoutRow T.state o⟩ : System Tm O) ::ₘ rest,
          insert (snapshot T.state (T.state.label o)) R⟩ ∧
      Move X J (events X O E)
        ⟨S ::ₘ (⟨T.program, withoutRow T.state o⟩ : System Tm O) ::ₘ rest,
          insert (snapshot T.state (T.state.label o)) R⟩
        ⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ
            (⟨T.program, withoutRow T.state o⟩ : System Tm O) ::ₘ rest,
          insert (snapshot T.state (T.state.label o)) R⟩ :=
  ⟨Move.fire (family := events X O E) (T ::ₘ rest) R S ⟨f, admitted⟩,
    Move.cast (Move.publish (family := events X O E) ((⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ rest) R T o present)
      (swap_worlds _ _ _ _) (swap_worlds _ _ _ _),
    Move.cast (Move.publish (family := events X O E) (S ::ₘ rest) R T o present) (swap_worlds _ _ _ _) (swap_worlds _ _ _ _),
    Move.fire (family := events X O E) ((⟨T.program, withoutRow T.state o⟩ : System Tm O) ::ₘ rest)
      (insert (snapshot T.state (T.state.label o)) R) S
      ⟨widen (Set.union_subset_union_right _ (Set.subset_insert _ _)) f, admitted⟩⟩

omit [DecidableEq O] in
/-- **The firing that uses a published row exists only after the publication**: while the row is
neither a rule of the world nor a row of the space, no firing of the world has it as its rule. -/
theorem not_before_publication {P R : Program Tm} {row : Rule Tm} (missing : row ∉ P ∪ R) {a : Obj}
    (f : Firing O E (P ∪ R) a) : f.rule ≠ row := fun same => missing (same ▸ f.member)

/-- **Firings in two worlds reach one bag in either order.** -/
theorem fire_fire_commute (rest : Multiset (System Tm O)) (R : Program Tm) (S T : System Tm O)
    (f : Firing O E (S.program ∪ R) S.state.frame) (admittedF : f.Admits X S.state)
    (g : Firing O E (T.program ∪ R) T.state.frame) (admittedG : g.Admits X T.state) :
    Move X J (events X O E) ⟨S ::ₘ T ::ₘ rest, R⟩
        ⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ T ::ₘ rest, R⟩ ∧
      Move X J (events X O E) ⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ T ::ₘ rest, R⟩
        ⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ
          (⟨T.program, g.result X T.state⟩ : System Tm O) ::ₘ rest, R⟩ ∧
      Move X J (events X O E) ⟨S ::ₘ T ::ₘ rest, R⟩
        ⟨S ::ₘ (⟨T.program, g.result X T.state⟩ : System Tm O) ::ₘ rest, R⟩ ∧
      Move X J (events X O E) ⟨S ::ₘ (⟨T.program, g.result X T.state⟩ : System Tm O) ::ₘ rest, R⟩
        ⟨(⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ
          (⟨T.program, g.result X T.state⟩ : System Tm O) ::ₘ rest, R⟩ :=
  ⟨Move.fire (family := events X O E) (T ::ₘ rest) R S ⟨f, admittedF⟩,
    Move.cast (Move.fire (family := events X O E) ((⟨S.program, f.result X S.state⟩ : System Tm O) ::ₘ rest) R T ⟨g, admittedG⟩)
      (swap_worlds _ _ _ _) (swap_worlds _ _ _ _),
    Move.cast (Move.fire (family := events X O E) (S ::ₘ rest) R T ⟨g, admittedG⟩) (swap_worlds _ _ _ _) (swap_worlds _ _ _ _),
    Move.fire (family := events X O E) ((⟨T.program, g.result X T.state⟩ : System Tm O) ::ₘ rest) R S ⟨f, admittedF⟩⟩

#print axioms snapshot_information
#print axioms snapshot_models_iff
#print axioms import_knows
#print axioms snapshot_dead_never_fires
#print axioms dead_row_unused
#print axioms import_label
#print axioms snapshot_importable
#print axioms import_conservative
#print axioms fire_publish_commute
#print axioms not_before_publication
#print axioms fire_fire_commute

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
