import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.RelabelTransport

/-!
# Exact admission and results on the shared-row image

No guard, occurrence, equation or opening is discarded by the embedding. The
scope probe agrees with the original source scope; shared selections add no
schema information. Region queries reduce to the original pattern observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared

open Interface (Frames)
open PredicateQueryAdmission (RegionQuery)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : RuleSyntax.Program Tm}

theorem selected_information_empty (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).uses.flatMap (fun selected =>
      RowUse.information X (E.weaken (lift s f).ext) selected.2) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro selected member
  rcases List.mem_append.mp member with taken | read
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp taken
    rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp read
    rfl

theorem information_eq (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).information X = f.information X s := by
  unfold Firing.information
  rw [selected_information_empty, taken_values, read_values]
  dsimp only [lift, Rule.ofShared, State.ofShared]
  simp only [RuleSyntax.Firing.information,
    RuleSyntax.Firing.matching, RuleSyntax.Firing.opened, RuleInstance.map,
    Frames.applyStore, List.zip_eq_zipWith, List.zipWith_map_right]
  exact congrArg
    (fun initial : EquationStore (Tm (E.target f.ext)) =>
      initial ++ f.matching X s (f.opened X).take f.selection.taken ++
        f.matching X s (f.opened X).read f.selection.read ++ (f.opened X).tell)
    (List.append_nil (X.applyStore (E.weaken f.ext) s.knowledge))

theorem selected_wellFormed (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) :
    ∀ selected ∈ (lift s f).uses, selected.1.WellFormed := by
  intro selected member
  rcases List.mem_append.mp member with taken | read
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp taken
    rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp read
    rfl

theorem shapes_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).Shapes X ↔ f.Shapes X s := by
  constructor
  · rintro ⟨fresh, takes, made, takeLength, readLength, makeLength, collectLength, _, _⟩
    refine ⟨(fresh_iff X s f).mp fresh, takes, made, takeLength, readLength, ?_, collectLength⟩
    simpa only [lift, Rule.ofShared, List.length_nil, Nat.add_zero] using makeLength
  · rintro ⟨fresh, takes, made, takeLength, readLength, makeLength, collectLength⟩
    refine ⟨(fresh_iff X s f).mpr fresh, takes, made, takeLength, readLength, ?_, collectLength,
      selected_wellFormed s f, ?_⟩
    · simpa only [lift, Rule.ofShared, List.length_nil, Nat.add_zero] using makeLength
    · intro output member
      change output ∈ [] at member
      cases member

theorem checkHolds_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) {b : Obj} (σ : Hom (E.target f.ext) b)
    (condition : Check (Tm f.rule.locals)) :
    (lift s f).checkHolds X σ condition ↔
      RuleSyntax.checkHolds X σ (f.row X s) s.present (condition.map (X.act f.opening)) := by
  cases condition with
  | equal left right => exact Iff.rfl
  | predicate quantifier pattern =>
    exact Regions.shared_predicate_iff X (X.act f.opening pattern) quantifier σ (f.row X s) s.present
  | count pattern number =>
    exact Regions.shared_count_iff X (X.act f.opening pattern) number σ (f.row X s) s.present

theorem holds_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) {b : Obj} (σ : Hom (E.target f.ext) b) :
    (lift s f).Holds X σ ↔ f.Holds X s σ := by
  constructor
  · rintro ⟨checks, queries⟩
    change (∀ condition ∈ f.rule.body.checks, (lift s f).checkHolds X σ condition) at checks
    refine ⟨?_, ?_⟩
    · change ∀ condition ∈ f.rule.body.checks.map (Check.map (X.act f.opening)),
        RuleSyntax.checkHolds X σ (f.row X s) s.present condition
      exact (List.forall_mem_map (f := Check.map (X.act f.opening))
        (l := f.rule.body.checks)
        (P := fun condition => RuleSyntax.checkHolds X σ (f.row X s) s.present condition)).mpr
        (fun condition member => (checkHolds_iff X s f σ condition).mp (checks condition member))
    · intro query member
      exact (Regions.shared_collect_iff X query.1 query.2 σ (f.row X s) s.present).mp
        (queries query member)
  · rintro ⟨checks, queries⟩
    change (∀ condition ∈ f.rule.body.checks.map (Check.map (X.act f.opening)),
      RuleSyntax.checkHolds X σ (f.row X s) s.present condition) at checks
    refine ⟨?_, ?_⟩
    · intro condition member
      exact (checkHolds_iff X s f σ condition).mpr
        (checks (condition.map (X.act f.opening)) (List.mem_map.mpr ⟨condition, member, rfl⟩))
    · intro query member
      exact (Regions.shared_collect_iff X query.1 query.2 σ (f.row X s) s.present).mpr
        (queries query member)

theorem entails_holds_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) :
    X.Entails ((lift s f).information X) (fun _ σ => (lift s f).Holds X σ) ↔
      X.Entails (f.information X s) (fun _ σ => f.Holds X s σ) := by
  rw [information_eq]
  constructor
  · intro entailed b σ solved
    exact (holds_iff X s f σ).mp (entailed b σ solved)
  · intro entailed b σ solved
    exact (holds_iff X s f σ).mpr (entailed b σ solved)

variable [DecidableEq O]

private theorem relabel_shared {a : Obj} (old : O → Tm a) :
    ∀ (made : List O) (rows : List (Tm a)) (o : O),
      RuleSyntax.relabel (Tm := fun a => Row Tm a) (fun o => Row.shared (old o)) made
          (rows.map Row.shared) o = Row.shared (RuleSyntax.relabel old made rows o) := by
  intro made
  induction made with
  | nil => intro rows o; rfl
  | cons head rest ih =>
    intro rows o
    cases rows with
    | nil => rfl
    | cons row later =>
      by_cases same : o = head
      · simp only [RuleSyntax.relabel, List.map_cons, if_pos same]
      · simp only [RuleSyntax.relabel, List.map_cons, if_neg same]
        exact ih later o

theorem admits_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).Admits X ↔ f.Admits X s := by
  change ((lift s f).Shapes X ∧ _ ∧ _ ∧ _) ↔ (f.Shapes X s ∧ _ ∧ _ ∧ _)
  rw [shapes_iff, entails_holds_iff, information_eq]
  exact Iff.rfl

theorem result_eq (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).result X = State.ofShared (f.result X s) := by
  have labels : ((lift s f).result X).label = (State.ofShared (f.result X s)).label := by
    funext o
    change RuleSyntax.relabel (Tm := fun a => Row Tm a) (fun o => Row.shared (f.row X s o))
      f.selection.made ((Rule.ofShared f.rule).outputs X f.opening) o = _
    rw [Rule.outputs_ofShared]
    change RuleSyntax.relabel (Tm := fun a => Row Tm a) (fun o => Row.shared (f.row X s o))
      f.selection.made (f.rule.body.produce.map (fun term => Row.shared (X.act f.opening term))) o =
        Row.shared (RuleSyntax.relabel (f.row X s) f.selection.made (f.opened X).produce o)
    have outputs : f.rule.body.produce.map (fun term => Row.shared (X.act f.opening term)) =
        (f.opened X).produce.map Row.shared := by
      simp only [RuleSyntax.Firing.opened, RuleInstance.map, List.map_map]
      rfl
    rw [outputs]
    exact relabel_shared (f.row X s) f.selection.made (f.opened X).produce o
  change (⟨E.target f.ext, (lift s f).information X, _, _⟩ : State Tm O) =
    ⟨E.target f.ext, f.information X s, _, _⟩
  rw [information_eq]
  exact congrArg (fun label => (⟨E.target f.ext, f.information X s,
    MeTTaCalculus.OccurrenceCommits.fire s.present (f.selection.commit (T := Unit)), label⟩ : State Tm O)) labels

#print axioms information_eq
#print axioms shapes_iff
#print axioms holds_iff
#print axioms admits_iff
#print axioms result_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared
