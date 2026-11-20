import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema

/-!
# A state with a binder on each datum

The occurrence store and constraint frame are unchanged in shape, but a label
may be shared or schematic. Only a shared value or a closure's captured
arguments belong to the ambient frame; a schema's private body and equations
do not become ambient unknowns merely because they are stored.

The scope probe uses actual ambient terms as its occurrence carrier and identity
labels. This reuses the single-firing freshness predicate without requiring an
arbitrary padding term at an empty ambient frame. It is a scope view, not an
additional executed firing or a quotient of physical resources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)

universe uO uT uH uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace Row

def ambientTerms {a : Obj} : Row Tm a → List (Tm a)
  | .shared term => [term]
  | .schematic closure => closure.args

def act (X : Frames Tm Hom) {a b : Obj} (w : Hom a b) : Row Tm a → Row Tm b
  | .shared term => .shared (X.act w term)
  | .schematic closure => .schematic (closure.act X w)

theorem ambientTerms_act (X : Frames Tm Hom) {a b : Obj} (w : Hom a b) (row : Row Tm a) :
    (row.act X w).ambientTerms = row.ambientTerms.map (X.act w) := by
  cases row <;> rfl

theorem readsAt_act_iff (X : Frames Tm Hom) {a b c : Obj} (w : Hom a b) (σ : Hom b c)
    (value : Tm c) (row : Row Tm a) :
    ReadsAt X σ value (row.act X w) ↔ ReadsAt X (X.comp σ w) value row := by
  cases row with
  | shared term => simp only [ReadsAt, act, X.act_comp]
  | schematic closure => exact Closure.readsAt_act_iff X w closure σ value

end Row

structure State (Tm : Obj → Type uT) (O : Type uOcc) where
  frame : Obj
  knowledge : EquationStore (Tm frame)
  present : Finset O
  label : O → Row Tm frame

namespace State

variable {O : Type uOcc}

def ofShared (s : RuleSyntax.State Tm O) : State Tm O :=
  ⟨s.frame, s.knowledge, s.present, fun o => .shared (s.label o)⟩

noncomputable def ambientTerms (s : State Tm O) : List (Tm s.frame) :=
  s.present.toList.flatMap (fun o => (s.label o).ambientTerms)

noncomputable def scope (s : State Tm O) : RuleSyntax.State Tm (Tm s.frame) := by
  classical
  exact ⟨s.frame, s.knowledge, s.ambientTerms.toFinset, id⟩

theorem mem_scope_present (s : State Tm O) (term : Tm s.frame) :
    term ∈ s.scope.present ↔ ∃ o ∈ s.present, term ∈ (s.label o).ambientTerms := by
  classical
  simp [scope, ambientTerms]

theorem scope_mentions_iff (s : State Tm O) (term : Tm s.frame) :
    s.scope.Mentions term ↔
      term ∈ s.knowledge.map Prod.fst ∨ term ∈ s.knowledge.map Prod.snd ∨
        ∃ o ∈ s.present, term ∈ (s.label o).ambientTerms := by
  change (term ∈ s.knowledge.map Prod.fst ∨ term ∈ s.knowledge.map Prod.snd ∨
    ∃ value ∈ s.scope.present, value = term) ↔ _
  simp only [exists_eq_right, mem_scope_present]

theorem shared_scope_mentions_iff (s : RuleSyntax.State Tm O) (term : Tm s.frame) :
    (ofShared s).scope.Mentions term ↔ s.Mentions term := by
  refine (scope_mentions_iff (ofShared s) term).trans ?_
  simp only [ofShared, Row.ambientTerms, RuleSyntax.State.Mentions]
  constructor
  · rintro (known | known | ⟨o, present, same⟩)
    · exact Or.inl known
    · exact Or.inr (Or.inl known)
    · exact Or.inr (Or.inr ⟨o, present, (List.mem_singleton.mp same).symm⟩)
  · rintro (known | known | ⟨o, present, same⟩)
    · exact Or.inl known
    · exact Or.inr (Or.inl known)
    · exact Or.inr (Or.inr ⟨o, present, List.mem_singleton.mpr same.symm⟩)

def act (X : Frames Tm Hom) {b : Obj} (s : State Tm O) (w : Hom s.frame b) : State Tm O :=
  ⟨b, X.applyStore w s.knowledge, s.present, fun o => (s.label o).act X w⟩

end State

#print axioms Row.readsAt_act_iff
#print axioms State.scope_mentions_iff
#print axioms State.shared_scope_mentions_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
