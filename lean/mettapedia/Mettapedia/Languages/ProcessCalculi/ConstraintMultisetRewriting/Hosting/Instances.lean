import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Rules

/-!
# What a firing does to the solutions of the knowledge

For a firing of any program of `RuleSyntax.step` at the contextual frames that takes one row and
makes one row (`Simple`), the solutions of its information are exactly the pairs of a solution `g`
of the knowledge and an instantiation `h` of the rule's unknowns that solves the rule's tells and
sends the take pattern to `g`'s reading of the taken row:

* `simple_restrict`: every solution of the information restricts to such a pair;
* `simple_amalgamate`: every such pair comes from a solution of the information, which reads the
  made row as `h` reads the rule's made row and every row of the state as `g` reads it.

The second direction is the step's freshness (`Firing.Fresh`, an amalgamation property of the
opening) and nothing else, so it holds for every admitted firing, whatever the extension and the
opening. `simple_label_made`, `simple_label_other` and `simple_present` say where the rows go.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {S : Signature}

/-- Models at the contextual frames, unfolded. -/
theorem contextual_models_iff {F G : Interface.Frames.Frame S} (σ : Assignment F.arity G.arity)
    (store : EquationStore (Observation S F.arity)) :
    (Interface.Frames.contextual S).Models σ store ↔
      ∀ e ∈ store, instantiateObservation σ e.1 = instantiateObservation σ e.2 :=
  Iff.rfl

section Generic

variable {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
  {s : RuleSyntax.State (RuleSyntax.Contextual.Terms S) ℕ}
  (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog s.frame)

/-- **A simple firing**: it takes the row `o` by its one take pattern `pat`, reads nothing, and makes
the row `o'` labelled by its one made row `out`. -/
structure Simple (o o' : ℕ) (pat out : Observation S f.rule.locals.arity) : Prop where
  taken : f.selection.taken = [o]
  noRead : f.selection.read = []
  madeOne : f.selection.made = [o']
  take : f.rule.body.take = [pat]
  noReadPattern : f.rule.body.read = []
  produce : f.rule.body.produce = [out]

variable {f} {o o' : ℕ} {pat out : Observation S f.rule.locals.arity}

/-- The information of a simple firing, spelled out. -/
theorem simple_information (simple : Simple f o o' pat out) :
    f.information (Interface.Frames.contextual S) s =
      (Interface.Frames.contextual S).applyStore ((RuleSyntax.Contextual.declarations S).weaken f.ext)
          s.knowledge ++
        [(instantiateObservation f.opening pat, f.row (Interface.Frames.contextual S) s o)] ++ [] ++
        f.rule.body.tell.map fun e => (instantiateObservation f.opening e.1, instantiateObservation f.opening e.2) := by
  simp only [RuleSyntax.Firing.information, RuleSyntax.Firing.matching, RuleSyntax.Firing.opened,
    RuleInstance.map, simple.take, simple.taken, simple.noRead, simple.noReadPattern, List.map_cons,
    List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_right]
  rfl

/-- **Restriction**: a solution of the information gives a solution of the knowledge and an
instantiation of the rule's unknowns that solves its tells and sends the take pattern to the
knowledge's reading of the taken row. -/
theorem simple_restrict (simple : Simple f o o' pat out) {B : Interface.Frames.Frame S}
    (u : Assignment ((RuleSyntax.Contextual.declarations S).target f.ext).arity B.arity)
    (solved : (Interface.Frames.contextual S).Models u (f.information (Interface.Frames.contextual S) s)) :
    (Interface.Frames.contextual S).Models
        (Assignment.compose u ((RuleSyntax.Contextual.declarations S).weaken f.ext)) s.knowledge ∧
      (Interface.Frames.contextual S).Models (Assignment.compose u f.opening) f.rule.body.tell ∧
      instantiateObservation (Assignment.compose u f.opening) pat =
        instantiateObservation (Assignment.compose u ((RuleSyntax.Contextual.declarations S).weaken f.ext))
          (s.label o) := by
  rw [simple_information simple] at solved
  refine ⟨?_, ?_, ?_⟩
  · intro e member
    have transported := solved _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨e, member, rfl⟩))))
    change instantiateObservation u (instantiateObservation _ e.1) =
      instantiateObservation u (instantiateObservation _ e.2) at transported
    rw [instantiateObservation_comp, instantiateObservation_comp] at transported
    exact transported
  · intro e member
    have told := solved _ (List.mem_append_right _ (List.mem_map.mpr ⟨e, member, rfl⟩))
    change instantiateObservation u (instantiateObservation f.opening e.1) =
      instantiateObservation u (instantiateObservation f.opening e.2) at told
    rw [instantiateObservation_comp, instantiateObservation_comp] at told
    exact told
  · have taken := solved _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton_self _))))
    change instantiateObservation u (instantiateObservation f.opening pat) =
      instantiateObservation u (instantiateObservation _ (s.label o)) at taken
    rw [instantiateObservation_comp, instantiateObservation_comp] at taken
    exact taken

/-- **Amalgamation**: a solution of the knowledge and an instantiation of the rule's unknowns that
solves its tells and sends the take pattern to the knowledge's reading of the taken row come from one
solution of the information, which reads every row of the state as the knowledge's solution does and
the rule's terms as the instantiation does. Only the freshness of the opening is used. -/
theorem simple_amalgamate (simple : Simple f o o' pat out)
    (fresh : f.Fresh (Interface.Frames.contextual S) s) (present : o ∈ s.present)
    {B : Interface.Frames.Frame S} (g : Assignment s.frame.arity B.arity)
    (h : Assignment f.rule.locals.arity B.arity)
    (known : (Interface.Frames.contextual S).Models g s.knowledge)
    (told : (Interface.Frames.contextual S).Models h f.rule.body.tell)
    (matched : instantiateObservation h pat = instantiateObservation g (s.label o)) :
    ∃ u : Assignment ((RuleSyntax.Contextual.declarations S).target f.ext).arity B.arity,
      (Interface.Frames.contextual S).Models u (f.information (Interface.Frames.contextual S) s) ∧
      instantiateObservation u (instantiateObservation f.opening out) = instantiateObservation h out ∧
      (∀ i ∈ s.present, instantiateObservation u (f.row (Interface.Frames.contextual S) s i) =
        instantiateObservation g (s.label i)) ∧
      ∀ t ∈ f.rule.terms, instantiateObservation u (instantiateObservation f.opening t) =
        instantiateObservation h t := by
  obtain ⟨u, onState, onRule⟩ := fresh B g h
  have state : ∀ t, s.Mentions t →
      instantiateObservation u (instantiateObservation ((RuleSyntax.Contextual.declarations S).weaken f.ext) t) =
        instantiateObservation g t := onState
  have rule : ∀ t ∈ f.rule.terms,
      instantiateObservation u (instantiateObservation f.opening t) = instantiateObservation h t := onRule
  have patTerm : pat ∈ f.rule.terms := by
    unfold RuleSyntax.Rule.terms
    rw [simple.take]
    simp
  have outTerm : out ∈ f.rule.terms := by
    unfold RuleSyntax.Rule.terms
    rw [simple.produce]
    simp
  have tellFirst : ∀ e ∈ f.rule.body.tell, e.1 ∈ f.rule.terms := by
    intro e member
    unfold RuleSyntax.Rule.terms
    simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨e, member, rfl⟩))))
  have tellSecond : ∀ e ∈ f.rule.body.tell, e.2 ∈ f.rule.terms := by
    intro e member
    unfold RuleSyntax.Rule.terms
    simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨e, member, rfl⟩)))
  refine ⟨u, ?_, rule out outTerm, fun i member => state _ (Or.inr (Or.inr ⟨i, member, rfl⟩)), rule⟩
  rw [simple_information simple]
  intro e member
  rcases List.mem_append.mp member with front | told'
  · rcases List.mem_append.mp front with front' | none
    · rcases List.mem_append.mp front' with old | taken
      · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp old
        change instantiateObservation u (instantiateObservation _ original.1) =
          instantiateObservation u (instantiateObservation _ original.2)
        rw [state _ (Or.inl (List.mem_map_of_mem inside)), state _ (Or.inr (Or.inl (List.mem_map_of_mem inside)))]
        exact known original inside
      · rw [List.mem_singleton.mp taken]
        change instantiateObservation u (instantiateObservation f.opening pat) =
          instantiateObservation u (instantiateObservation _ (s.label o))
        rw [rule pat patTerm, state _ (Or.inr (Or.inr ⟨o, present, rfl⟩))]
        exact matched
    · cases none
  · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp told'
    change instantiateObservation u (instantiateObservation f.opening original.1) =
      instantiateObservation u (instantiateObservation f.opening original.2)
    rw [rule _ (tellFirst original inside), rule _ (tellSecond original inside)]
    exact told original inside

/-- The made row of a simple firing is the opened made row of its rule. -/
theorem simple_label_made (simple : Simple f o o' pat out)
    (shapes : f.Shapes (Interface.Frames.contextual S) s) :
    (f.result (Interface.Frames.contextual S) s).label o' = instantiateObservation f.opening out := by
  apply RuleSyntax.Firing.result_label_made f shapes
  simp only [RuleSyntax.Firing.opened, RuleInstance.map, simple.madeOne, simple.produce, List.map_cons,
    List.map_nil, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
  rfl

/-- Every other row keeps its label, read at the extended frame. -/
theorem simple_label_other (simple : Simple f o o' pat out) {i : ℕ} (other : i ≠ o') :
    (f.result (Interface.Frames.contextual S) s).label i = f.row (Interface.Frames.contextual S) s i := by
  apply RuleSyntax.Firing.result_label_other
  rw [simple.madeOne]
  simpa using other

/-- The rows after a simple firing: the taken row is gone, the made row is there. -/
theorem simple_present (simple : Simple f o o' pat out) :
    (f.result (Interface.Frames.contextual S) s).present = insert o' (s.present.erase o) := by
  change fire s.present (f.selection.commit (T := Unit)) = _
  ext i
  simp only [fire, Selection.commit, simple.taken, simple.madeOne, List.toFinset_cons, List.toFinset_nil,
    insert_empty_eq, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert,
    Finset.mem_erase]
  tauto

end Generic

#print axioms simple_restrict
#print axioms simple_amalgamate
#print axioms simple_label_made
#print axioms simple_present

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
