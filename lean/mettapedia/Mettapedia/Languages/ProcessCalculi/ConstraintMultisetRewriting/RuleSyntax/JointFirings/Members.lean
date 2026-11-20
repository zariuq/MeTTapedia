import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Singletons
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition

/-!
# The members of a bag, one at a time

What a jointly admitted bag says about each of its members, over every frame action in which the frame
of a rule's unknowns maps into every frame (at one frame, the identity substitution; at declaration
frames, any assignment).

* **Joint realization gives each member** (`Realized.member`): the instantiation of one member's rule is
  realized, the others being instantiated in any way; and any choice of instantiations, one for each
  member, is realized at once (`Realized.pick`).
* **Each member of a jointly fresh bag is opened freshly** (`Bag.fresh_member`).
* **Under the reading that asks the guards of each member at its own information, every member of an
  admitted bag is admitted by the step of the program** (`Bag.admits_member`). So such a bag can begin
  with any of its members.
* **The same states can step** (`can_fire_iff`): some firing of the program is admitted at a state
  exactly when some bag with a member is admitted there under that reading. With bags that have a
  member, the bag step therefore stops exactly where the step of the program stops; with the bag
  without members it would stop nowhere that has solvable knowledge (`Bag.admits_nil_iff`).

Under the reading that asks the guards at the joint information this fails: `Knowledge` exhibits a bag
that is admitted while no firing of the program is.

`relabel_append` is the fact about labels that firing one after another needs: relabelling by two lists
of made identities in turn is relabelling by their concatenation, when the two lists are apart.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Joint realization, member by member -/

section Realization

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  {a : Obj} {x : E.Ext a} {b : Obj}

/-- What is jointly realized is realized. -/
theorem Realized.exists (inhabited : ∀ r : Rule Tm, Nonempty (Hom r.locals b))
    (l : List (Member O E P x)) :
    ∀ {Q : Hom (E.target x) b → Prop}, Realized X b l Q → ∃ u, Q u := by
  induction l with
  | nil =>
      intro Q realized
      exact (realized_nil X Q).mp realized
  | cons m rest ih =>
      intro Q realized
      obtain ⟨h⟩ := inhabited m.rule
      obtain ⟨u, holds, -⟩ := ih ((realized_cons X m rest Q).mp realized h)
      exact ⟨u, holds⟩

/-- **Joint realization gives each member**: any instantiation of the unknowns of one member's rule is
realized along its opening. -/
theorem Realized.member (inhabited : ∀ r : Rule Tm, Nonempty (Hom r.locals b))
    (l : List (Member O E P x)) :
    ∀ {Q : Hom (E.target x) b → Prop} {m : Member O E P x}, m ∈ l → Realized X b l Q →
      ∀ h : Hom m.rule.locals b,
        ∃ u, Q u ∧ ∀ t ∈ m.rule.terms, X.E (X.act u (X.act m.opening t)) (X.act h t) := by
  induction l with
  | nil =>
      intro Q m inside
      exact absurd inside List.not_mem_nil
  | cons m' rest ih =>
      intro Q m inside realized h
      rcases List.mem_cons.mp inside with same | inRest
      · subst same
        obtain ⟨u, holds, here⟩ :=
          Realized.exists X inhabited rest ((realized_cons X _ rest Q).mp realized h)
        exact ⟨u, holds, here⟩
      · obtain ⟨other⟩ := inhabited m'.rule
        obtain ⟨u, ⟨holds, -⟩, here⟩ :=
          ih inRest ((realized_cons X m' rest Q).mp realized other) h
        exact ⟨u, holds, here⟩

/-- **Any choice of instantiations, one for each member, is realized at once.** -/
theorem Realized.pick (choice : (m : Member O E P x) → Hom m.rule.locals b)
    (l : List (Member O E P x)) :
    ∀ {Q : Hom (E.target x) b → Prop}, Realized X b l Q →
      ∃ u, Q u ∧ ∀ m ∈ l, ∀ t ∈ m.rule.terms,
        X.E (X.act u (X.act m.opening t)) (X.act (choice m) t) := by
  induction l with
  | nil =>
      intro Q realized
      obtain ⟨u, holds⟩ := (realized_nil X Q).mp realized
      exact ⟨u, holds, fun m inside => absurd inside List.not_mem_nil⟩
  | cons m' rest ih =>
      intro Q realized
      obtain ⟨u, ⟨holds, here⟩, later⟩ := ih ((realized_cons X m' rest Q).mp realized (choice m'))
      refine ⟨u, holds, fun m inside => ?_⟩
      rcases List.mem_cons.mp inside with same | inRest
      · rw [same]
        exact here
      · exact later m inRest

end Realization

/-! ## Each member of an admitted bag -/

namespace Bag

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  {s : State Tm O} {f : Bag O E P s.frame}

/-- **Each member of a jointly fresh bag is opened freshly.** -/
theorem fresh_member (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    (fresh : f.Fresh X s) {m : Member O E P f.ext} (inside : m ∈ f.members) : m.firing.Fresh X s :=
  fun b g h => Realized.member X (fun r => inhabited r b) f.members inside (fresh b g) h

variable [DecidableEq O]

/-- **Under the reading that asks each member's guards at its own information, every member of an
admitted bag is admitted by the step of the program.** -/
theorem admits_member (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    (own : f.AdmitsOwn X s) {m : Member O E P f.ext} (inside : m ∈ f.members) :
    m.firing.Admits X s := by
  obtain ⟨⟨fresh, taken, made, lengths⟩, enabled, solvable, asks⟩ := own
  exact ⟨⟨fresh_member X inhabited fresh inside, (List.nodup_flatMap.mp taken).1 m inside,
      (List.nodup_flatMap.mp made).1 m inside, lengths m inside⟩,
    enabled_member enabled inside, solvable_member X inside solvable, asks m inside⟩

end Bag

/-! ## The same states can step -/

section CanFire

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm}

/-- **Some firing of the program is admitted exactly when some bag with a member is**, under the
reading that asks each member's guards at its own information. -/
theorem can_fire_iff (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    (s : State Tm O) :
    (∃ g : Firing O E P s.frame, g.Admits X s) ↔
      ∃ f : Bag O E P s.frame, f.members ≠ [] ∧ f.AdmitsOwn X s := by
  constructor
  · rintro ⟨g, admitted⟩
    exact ⟨Bag.single g, List.cons_ne_nil _ _,
      (Bag.admitsOwn_single X s (Member.ofFiring g)).mpr admitted⟩
  · rintro ⟨f, nonempty, own⟩
    obtain ⟨m, inside⟩ := List.exists_mem_of_ne_nil f.members nonempty
    exact ⟨m.firing, Bag.admits_member X inhabited own inside⟩

end CanFire

/-! ## Relabelling by two lists in turn -/

section Relabel

variable {O : Type uOcc} [DecidableEq O] {a : Obj}

/-- **Relabelling by two lists of made identities in turn is relabelling by their concatenation**, when
no identity of the first list is in the second. -/
theorem relabel_append (old : O → Tm a) :
    ∀ (made₁ : List O) (rows₁ : List (Tm a)) (made₂ : List O) (rows₂ : List (Tm a)),
      made₁.length = rows₁.length → (∀ o ∈ made₁, o ∉ made₂) → ∀ o : O,
      relabel old (made₁ ++ made₂) (rows₁ ++ rows₂) o = relabel (relabel old made₁ rows₁) made₂ rows₂ o
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, lengths, _, _ => by simp at lengths
  | _ :: _, [], _, _, lengths, _, _ => by simp at lengths
  | o' :: rest, t :: ts, made₂, rows₂, lengths, apart, o => by
      have later := relabel_append old rest ts made₂ rows₂ (Nat.succ.inj lengths)
        (fun o'' inside => apart o'' (List.mem_cons_of_mem _ inside)) o
      by_cases same : o = o'
      · have outside : o ∉ made₂ := by
          rw [same]
          exact apart o' List.mem_cons_self
        rw [Firing.relabel_of_not_mem _ made₂ rows₂ outside]
        simp only [List.cons_append, relabel, if_pos same]
      · have base : relabel old rest ts o = relabel old (o' :: rest) (t :: ts) o := by
          simp only [relabel, if_neg same]
        have moved := Scope.relabel_congr base made₂ rows₂
        have first : relabel old (o' :: rest ++ made₂) (t :: ts ++ rows₂) o =
            relabel old (rest ++ made₂) (ts ++ rows₂) o := by
          simp only [List.cons_append, relabel, if_neg same]
        exact first.trans (later.trans moved)

end Relabel

#print axioms Realized.exists
#print axioms Realized.member
#print axioms Realized.pick
#print axioms Bag.fresh_member
#print axioms Bag.admits_member
#print axioms can_fire_iff
#print axioms relabel_append

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
