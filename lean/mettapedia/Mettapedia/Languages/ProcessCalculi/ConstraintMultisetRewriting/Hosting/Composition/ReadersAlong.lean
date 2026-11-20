import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readers

/-!
# The reading neighbours along the runs from the ordinary starts

`Readers.Flex.readEqn_not_disciplined` and `Readers.Counter.counter_not_disciplined` fail the every-state
conditions at states that a run of the union reaches only if it starts there. Asked along the runs from
the start of a query (`AlongRuns.DisciplinedAlong`, `AlongRuns.BothWaysAlong`), the conditions hold of
both rules. So the conditions along the runs are strictly weaker than the every-state ones.

**The heads of the rows.** `HeadedIn N T w`: every present row of `w` is a node whose former satisfies
`T`. `MakesIn N T R`: every row a rule of `R` makes is such a node. A firing of such a program keeps the
property (`headedIn_fire`, `headedIn_run`). The start of every query has only alternatives' rows and
equation rows (`headedIn_start`); every rule of a translated program makes an alternative's row
(`translate_makes`). Negative examples: the state `Readers.Flex.flexState` has a row whose label is an
unknown applied to a node (`flexState_not_headed`), and a rule that makes a row that is one unknown
makes no node (`bare_not_makes`).

**The reading rule.** At a state whose rows are nodes, a row that `Controls.readEqn` reads is an
equation row written as one, and reading it tells nothing (`readEqn_at`). So `readEqn` is disciplined
for both directions along the runs from the start of every query of every program (`readEqn_along`,
`readEqn_bothWays_along`), and it does fire there: `Controls.readEqn_fires` is its firing at the start
of the query `(g)` of `(= (g) d)`.

**The rule that rewrites its own data.** At a state whose rows are alternatives' rows and equation rows,
`Readers.Counter.decRule` has no admitted firing (`dec_not_admitted`); so from the start of every query it
never fires along a run of the union (`counter_never_fires`), and it meets the condition along those runs
with no firing to ask it of (`counter_along_start`). Beside its own closed row `value((ret a))` it
fires and meets the condition (`ReadersClosed.counter_fires_closed`,
`ReadersClosed.counter_along_closed`). Beside its own row `value($x)` holding the query's own name it
fails at the start itself (`Readers.Counter.counter_not_along`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.ReadersAlong

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns
open Classical

/-! ## The heads of the rows -/

section Heads

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-- **The rows of a state are nodes with formers in `T`.** -/
def HeadedIn (T : Tag → Prop) (w : HostState S) : Prop :=
  ∀ o ∈ w.present, ∃ (k : Tag) (args : Fin k.arity → Term (signature S w.frame.arity) Γ star),
    T k ∧ w.label o = observe (N.node k args)

/-- **A program makes only nodes with formers in `T`.** -/
def MakesIn (T : Tag → Prop) (Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) : Prop :=
  ∀ r ∈ Prog, ∀ p ∈ r.body.produce,
    ∃ (k : Tag) (args : Fin k.arity → Term (signature S r.locals.arity) Γ star), T k ∧ p = observe (N.node k args)

theorem MakesIn.mono {T T' : Tag → Prop} {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (makes : MakesIn N T Prog) (sub : ∀ k, T k → T' k) : MakesIn N T' Prog := by
  intro r member p inside
  obtain ⟨k, args, tk, same⟩ := makes r member p inside
  exact ⟨k, args, sub k tk, same⟩

theorem MakesIn.union {T : Tag → Prop} {Prog₁ Prog₂ : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (makes₁ : MakesIn N T Prog₁) (makes₂ : MakesIn N T Prog₂) : MakesIn N T (Prog₁ ∪ Prog₂) := by
  intro r member
  rcases member with left | right
  · exact makes₁ r left
  · exact makes₂ r right

/-- A relabelled made identity carries one of the made rows. -/
theorem relabel_mem {Obj : Type*} {Tm : Obj → Type*} {a : Obj} (old : ℕ → Tm a) :
    ∀ (made : List ℕ) (rows : List (Tm a)) {o : ℕ}, made.length = rows.length → o ∈ made →
      RuleSyntax.relabel old made rows o ∈ rows
  | [], _, _, _, inside => absurd inside List.not_mem_nil
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | o' :: rest, t :: ts, o, lengths, inside => by
      by_cases same : o = o'
      · simp [RuleSyntax.relabel, same]
      · simp only [RuleSyntax.relabel, if_neg same]
        exact List.mem_cons_of_mem _
          (relabel_mem old rest ts (Nat.succ.inj lengths) ((List.mem_cons.mp inside).resolve_left same))

/-- **A firing of a program that makes nodes with formers in `T` keeps the rows such nodes.** -/
theorem headedIn_fire {T : Tag → Prop} {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (makes : MakesIn N T Prog) {w : HostState S}
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog w.frame}
    (shapes : f.Shapes (Interface.Frames.contextual S) w) (headed : HeadedIn N T w) :
    HeadedIn N T (f.result (Interface.Frames.contextual S) w) := by
  intro o present
  by_cases isMade : o ∈ f.selection.made
  · have lengths : f.selection.made.length = (f.opened (Interface.Frames.contextual S)).produce.length := by
      simp only [RuleSyntax.Firing.opened, RuleInstance.map, List.length_map]
      exact shapes.2.2.2.2.2.1.symm
    have inRows := relabel_mem (Obj := Interface.Frames.Frame S) (Tm := RuleSyntax.Contextual.Terms S)
      (f.row (Interface.Frames.contextual S) w) f.selection.made _ lengths isMade
    simp only [RuleSyntax.Firing.opened, RuleInstance.map] at inRows
    obtain ⟨p, pIn, same⟩ := List.mem_map.mp inRows
    obtain ⟨k, args, tk, rfl⟩ := makes f.rule f.member p pIn
    refine ⟨k, fun i => instantiate f.opening (args i), tk, ?_⟩
    refine same.symm.trans ?_
    show observe (instantiate f.opening (N.node k args)) = _
    rw [N.instantiate_node]
  · have old : o ∈ w.present := by
      rcases mem_fire.mp present with ⟨old, _⟩ | made
      · exact old
      · exact absurd (List.mem_toFinset.mp made) isMade
    obtain ⟨k, args, tk, label⟩ := headed o old
    refine ⟨k, fun i => instantiate ((RuleSyntax.Contextual.declarations S).weaken f.ext) (args i), tk, ?_⟩
    rw [RuleSyntax.Firing.result_label_other f isMade]
    show instantiateObservation _ (w.label o) = _
    rw [label]
    show observe (instantiate _ (N.node k args)) = _
    rw [N.instantiate_node]

/-- **Along the runs of such a program the rows stay such nodes.** -/
theorem headedIn_run {T : Tag → Prop} {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (makes : MakesIn N T Prog) {w₀ w : HostState S} (headed : HeadedIn N T w₀)
    (run : Relation.ReflTransGen (FiresIn Prog) w₀ w) : HeadedIn N T w := by
  induction run with
  | refl => exact headed
  | tail _ fires ih =>
      obtain ⟨f, admitted, rfl⟩ := fires
      exact headedIn_fire N makes admitted.1 ih

/-- **The start of every query has only alternatives' rows and equation rows.** -/
theorem headedIn_start {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    HeadedIn N (fun k => k = .alt ∨ k = .eqn) (start N P q) := by
  intro o _
  by_cases h : o < P.equations.length
  · refine ⟨.eqn, ![instantiate (rowNames o) (P.equations.get ⟨o, h⟩).lhs], .inr rfl, ?_⟩
    show startLabel N P q o = _
    unfold startLabel
    rw [dif_pos h]
  · refine ⟨.alt, ![encFocus N (instantiate queryNames) (.eval q),
      encStack N (instantiate queryNames) ([] : List (SourceLanguage.Frame κ Γ star Ty))], .inl rfl, ?_⟩
    show startLabel N P q o = _
    unfold startLabel
    rw [dif_neg h]
    rfl

/-- **Every rule of a translated program makes an alternative's row.** -/
theorem translate_makes {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) :
    MakesIn N (fun k => k = .alt) (translate N P) := by
  intro r member p inside
  rcases (mem_translate N).mp member with control | ⟨e, _, rfl⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨.alt, _, rfl, List.mem_singleton.mp inside⟩
  · exact ⟨.alt, _, rfl, List.mem_singleton.mp inside⟩

end Heads

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readers

/-- **A negative example**: the row `$F[eqn((g))]` of `Readers.Flex.flexState` is an unknown applied to a
node, not a node. -/
theorem flexState_not_headed (T : Tag → Prop) : ¬ HeadedIn N T Flex.flexState := by
  intro headed
  obtain ⟨k, args, _, label⟩ := headed 1 Flex.present1
  rw [Flex.label_row] at label
  have terms := observe_injective label
  have tops := congrArg Flex.top terms
  have clash : (none : Option (MOp ())) = some (.tup (k.arity + 1)) := tops
  simp at clash

/-- A rule that makes a row that is one unknown. -/
def bareRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms MSig) where
  locals := controlFrame [] ()
  body := { take := [], read := [], tell := [], checks := [], produce := [observe (unk .datum)] }
  collect := []

/-- **A negative example**: a program whose rule makes a row that is one unknown makes no node. -/
theorem bare_not_makes (T : Tag → Prop) :
    ¬ MakesIn N T ({bareRule} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)) := by
  intro makes
  obtain ⟨k, args, _, same⟩ := makes bareRule (Set.mem_singleton _) _ (List.mem_singleton_self _)
  have tops := congrArg Flex.top (observe_injective same)
  have clash : (none : Option (MOp ())) = some (.tup (k.arity + 1)) := tops
  simp at clash

/-! ## The reading rule along the runs -/

section Reading

/-- The rows of the states the union with `readEqn` reaches. -/
abbrev readTags : Tag → Prop := fun k => k = .alt ∨ k = .eqn ∨ k = .outside

theorem readEqn_makes : MakesIn N (fun k => k = .outside)
    ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)) := by
  intro r member p inside
  obtain rfl := Set.mem_singleton_iff.mp member
  exact ⟨.outside, ![], rfl, List.mem_singleton.mp inside⟩

theorem union_makes (P : SourceLanguage.Program mkeys [] () MTy) :
    MakesIn N readTags (translate N P ∪ ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig))) :=
  MakesIn.union N ((translate_makes N P).mono N fun _ isAlt => .inl isAlt)
    ((readEqn_makes).mono N fun _ isOutside => .inr (.inr isOutside))

/-- **Every state the union with `readEqn` reaches from the start has nodes for rows.** -/
theorem reached_headed (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy)
    {w : HostState MSig}
    (run : Relation.ReflTransGen
      (FiresIn (translate N P ∪ ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig))))
      (Hosting.start N P q) w) : HeadedIn N readTags w :=
  headedIn_run N (union_makes P)
    (fun o present => by
      obtain ⟨k, args, tk, label⟩ := headedIn_start N P q o present
      exact ⟨k, args, tk.elim (fun isAlt => .inl isAlt) (fun isEqn => .inr (.inl isEqn)), label⟩) run

/-- **Reading an equation row written as one tells nothing**: a solution of the knowledge extends to a
solution of the reading firing's information that reads every row of the state as before. -/
theorem readEqn_amalgamate {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)} {w : HostState MSig}
    {member : readEqn ∈ Prog} {ext : (RuleSyntax.Contextual.declarations MSig).Ext w.frame}
    {opening : Assignment readEqn.locals.arity ((RuleSyntax.Contextual.declarations MSig).target ext).arity}
    {o o' : ℕ} {seen : List (Finset ℕ)}
    (fresh : RuleSyntax.Firing.Fresh (Interface.Frames.contextual MSig) w
      (⟨readEqn, member, ext, opening, ⟨[], [o], [o']⟩, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) Prog w.frame))
    (present : o ∈ w.present) {t₀ : Term (signature MSig w.frame.arity) [] ()}
    (label : w.label o = observe (eqnN N t₀))
    {B : Interface.Frames.Frame MSig} (g : Assignment w.frame.arity B.arity)
    (known : (Interface.Frames.contextual MSig).Models g w.knowledge) :
    ∃ u : Assignment ((RuleSyntax.Contextual.declarations MSig).target ext).arity B.arity,
      (Interface.Frames.contextual MSig).Models u
        (RuleSyntax.Firing.information (Interface.Frames.contextual MSig) w
          (⟨readEqn, member, ext, opening, ⟨[], [o], [o']⟩, seen⟩ :
            RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) Prog w.frame)) ∧
      ∀ i ∈ w.present, instantiateObservation u
          (instantiateObservation ((RuleSyntax.Contextual.declarations MSig).weaken ext) (w.label i)) =
        instantiateObservation g (w.label i) := by
  obtain ⟨u, onState, onRule⟩ := fresh B g
    (fill (instantiate g t₀) (instantiate g t₀) (instantiate g t₀) (instantiate g t₀) (instantiate g t₀))
  have state : ∀ t, w.Mentions t →
      instantiateObservation u (instantiateObservation ((RuleSyntax.Contextual.declarations MSig).weaken ext) t) =
        instantiateObservation g t := onState
  have patTerm : (observe (eqnN N (unk .datum)) : Observation MSig (unknownArity (S := MSig) [] ())) ∈
      readEqn.terms :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))))))
  have onPat : instantiateObservation u (instantiateObservation opening (observe (eqnN N (unk .datum)))) =
      instantiateObservation
        (fill (instantiate g t₀) (instantiate g t₀) (instantiate g t₀) (instantiate g t₀) (instantiate g t₀))
        (observe (eqnN N (unk .datum))) := onRule _ patTerm
  refine ⟨u, ?_, fun i inside => state _ (Or.inr (Or.inr ⟨i, inside, rfl⟩))⟩
  intro e inside
  have inside' : e ∈ ((Interface.Frames.contextual MSig).applyStore
        ((RuleSyntax.Contextual.declarations MSig).weaken ext) w.knowledge ++ [] ++
      [(instantiateObservation opening (observe (eqnN N (unk .datum))),
        instantiateObservation ((RuleSyntax.Contextual.declarations MSig).weaken ext) (w.label o))]) ++ [] :=
    inside
  rcases List.mem_append.mp inside' with front | none
  · rcases List.mem_append.mp front with front' | read
    · rcases List.mem_append.mp front' with old | none
      · obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp old
        change instantiateObservation u (instantiateObservation _ original.1) =
          instantiateObservation u (instantiateObservation _ original.2)
        rw [state _ (Or.inl (List.mem_map_of_mem inStore)), state _ (Or.inr (Or.inl (List.mem_map_of_mem inStore)))]
        exact known original inStore
      · cases none
    · rw [List.mem_singleton.mp read]
      change instantiateObservation u (instantiateObservation opening (observe (eqnN N (unk .datum)))) =
        instantiateObservation u (instantiateObservation _ (w.label o))
      rw [onPat, state _ (Or.inr (Or.inr ⟨o, present, rfl⟩)), label]
      show observe (instantiate _ (eqnN N (unk .datum))) = observe (instantiate g (eqnN N t₀))
      rw [instantiate_eqnN, instantiate_eqnN, instantiate_unk]
      rfl
  · cases none

/-- **At a state whose rows are nodes, every admitted firing of `readEqn` takes nothing, tells nothing of
the rows, and makes a row that never reads as an alternative's row or as an equation row.** -/
theorem readEqn_at {T : Tag → Prop} {w : HostState MSig} (headed : HeadedIn N T w)
    {P : SourceLanguage.Program mkeys [] () MTy} {n : ℕ} {b : Branch mkeys [] () MTy} {a : ℕ}
    {others : Finset ℕ} (beside : Beside N P n b w a others)
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig)
      ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)) w.frame)
    (admitted : f.Admits (Interface.Frames.contextual MSig) w) :
    Apart P a w f ∧
      NeverReads (IsAlternative N) (f.result (Interface.Frames.contextual MSig) w) f.selection.made.toFinset ∧
      NeverReads (IsEquationRow N) (f.result (Interface.Frames.contextual MSig) w) f.selection.made.toFinset := by
  have rule : f.rule = readEqn := f.member
  obtain ⟨rl, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  simp only at rule
  subst rule
  have shapes := admitted.1
  have noTake : taken = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  obtain ⟨o, oneRead⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.1.symm
  obtain ⟨o', oneMade⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.2.1.symm
  simp only at oneRead oneMade
  subst noTake oneRead oneMade
  have oPresent : o ∈ w.present :=
    admitted.2.1.kept_subset (List.mem_toFinset.mpr (List.mem_singleton_self o))
  -- the row read is a node; the read equation makes it an equation row
  obtain ⟨k, args, _, label⟩ := headed o oPresent
  obtain ⟨B₁, u₁, solved₁⟩ := admitted.2.2.1
  have readEq : instantiateObservation u₁ (instantiateObservation opening (observe (eqnN N (unk .datum)))) =
      instantiateObservation u₁
        (instantiateObservation ((RuleSyntax.Contextual.declarations MSig).weaken ext) (w.label o)) :=
    RuleSyntax.Firing.read_solved (X := Interface.Frames.contextual MSig) _ solved₁
      (p := instantiateObservation opening (observe (eqnN N (unk .datum)))) (o := o) (List.mem_singleton_self _)
  rw [label] at readEq
  change observe (instantiate u₁ (instantiate opening (eqnN N (unk .datum)))) =
    observe (instantiate u₁ (instantiate _ (N.node k args))) at readEq
  rw [instantiate_eqnN, instantiate_eqnN, N.instantiate_node, N.instantiate_node] at readEq
  have isEqn : Tag.eqn = k := N.tag_eq (observe_injective readEq)
  subst isEqn
  have asEqn : w.label o = observe (eqnN N (args ⟨0, by decide⟩)) := by
    rw [label]
    refine congrArg (fun x => observe (N.node .eqn x)) (funext fun i => ?_)
    rw [show i = ⟨0, by decide⟩ from Fin.ext (Nat.lt_one_iff.mp i.isLt)]
    rfl
  refine ⟨⟨fun i inside => absurd inside List.not_mem_nil, ?_⟩, ?_⟩
  · intro B g known
    obtain ⟨u, solved, onRows⟩ := readEqn_amalgamate shapes.1 oPresent asEqn g known
    exact ⟨u, solved, fun i inside => onRows i (beside.rows_sub N inside)⟩
  · have madeLabel : (RuleSyntax.Firing.result (Interface.Frames.contextual MSig) w
        (⟨readEqn, member, ext, opening, ⟨[], [o], [o']⟩, seen⟩ :
          RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) {readEqn} w.frame)).label o' =
        instantiateObservation opening (observe (N.node .outside ![])) := by
      apply RuleSyntax.Firing.result_label_made _ shapes
      simp only [RuleSyntax.Firing.opened, RuleInstance.map, readEqn, List.map_cons, List.map_nil,
        List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
      rfl
    have quiet := outside_never (w := RuleSyntax.Firing.result (Interface.Frames.contextual MSig) w
      (⟨readEqn, member, ext, opening, ⟨[], [o], [o']⟩, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) {readEqn} w.frame))
      (F := readEqn.locals) opening madeLabel
    rw [List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
    exact quiet

/-- **`readEqn` is disciplined along the runs from the start of every query of every program.** -/
theorem readEqn_along (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy) :
    DisciplinedAlong N (D := D) P ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig))
      (Hosting.start N P q) := by
  intro w reached n b a others f beside _ admitted
  obtain ⟨apart, madeAlt, _⟩ := readEqn_at (reached_headed P q reached) beside f admitted
  exact ⟨apart, madeAlt⟩

/-- **`readEqn` is disciplined for both directions along the runs from the start of every query of every
program.** -/
theorem readEqn_bothWays_along (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy) :
    BothWaysAlong N (D := D) P ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig))
      (Hosting.start N P q) := by
  intro w reached n b a others f beside _ _ admitted
  exact readEqn_at (reached_headed P q reached) beside f admitted

/-- **The conditions along the runs are strictly weaker than the every-state ones**: `readEqn` meets
the condition for both directions along the runs from every start, it fires there (at the start of the
query `(g)` of `(= (g) d)`), and it is not disciplined at every state. -/
theorem readEqn_strictly_weaker :
    (∀ (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy),
      BothWaysAlong N (D := D) P ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig))
        (Hosting.start N P q)) ∧
    readFiring.Admits (Interface.Frames.contextual MSig) (Hosting.start N Q q) ∧
    ¬ Disciplined N (D := D) P0 ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)) :=
  ⟨readEqn_bothWays_along, readEqn_fires, Flex.readEqn_not_disciplined⟩

end Reading

/-! ## The rule that rewrites its own data, from the ordinary starts -/

section Counting

/-- **At a state whose rows are alternatives' rows and equation rows, `decRule` has no admitted
firing**: its take pattern is a `value` node. -/
theorem dec_not_admitted {w : HostState MSig} (headed : HeadedIn N (fun k => k = .alt ∨ k = .eqn) w)
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) Counter.neighbour w.frame) :
    ¬ f.Admits (Interface.Frames.contextual MSig) w := by
  intro admitted
  have rule : f.rule = Counter.decRule := f.member
  obtain ⟨rl, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  simp only at rule
  subst rule
  have shapes := admitted.1
  obtain ⟨o, oneTake⟩ := List.length_eq_one_iff.mp shapes.2.2.2.1.symm
  simp only at oneTake
  subst oneTake
  have oPresent : o ∈ w.present :=
    admitted.2.1.taken_subset (List.mem_toFinset.mpr (List.mem_singleton_self o))
  obtain ⟨k, args, tk, label⟩ := headed o oPresent
  obtain ⟨B₁, u₁, solved₁⟩ := admitted.2.2.1
  have takeEq : instantiateObservation u₁
      (instantiateObservation opening (observe (valueN N (retN N (unk .datum))))) =
      instantiateObservation u₁
        (instantiateObservation ((RuleSyntax.Contextual.declarations MSig).weaken ext) (w.label o)) :=
    RuleSyntax.Firing.take_solved (X := Interface.Frames.contextual MSig) _ solved₁
      (p := instantiateObservation opening (observe (valueN N (retN N (unk .datum))))) (o := o)
      (List.mem_singleton_self _)
  rw [label] at takeEq
  change observe (instantiate u₁ (instantiate opening (valueN N (retN N (unk .datum))))) =
    observe (instantiate u₁ (instantiate ((RuleSyntax.Contextual.declarations MSig).weaken ext)
      (N.node k args))) at takeEq
  have rhs : instantiate u₁ (instantiate ((RuleSyntax.Contextual.declarations MSig).weaken ext) (N.node k args)) =
      N.node k (fun i => instantiate u₁ (instantiate ((RuleSyntax.Contextual.declarations MSig).weaken ext)
        (args i))) := by
    rw [N.instantiate_node, N.instantiate_node]
  rw [rhs, instantiate_valueN, instantiate_valueN] at takeEq
  have isValue : Tag.value = k := N.tag_eq (observe_injective takeEq)
  subst isValue
  rcases tk with clash | clash <;> exact absurd clash (by decide)

/-- Every state the union with `decRule` reaches from the start has only alternatives' rows and
equation rows. -/
theorem counter_reached_headed (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy)
    {w : HostState MSig}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ Counter.neighbour)) (Hosting.start N P q) w) :
    HeadedIn N (fun k => k = .alt ∨ k = .eqn) w := by
  induction run with
  | refl => exact headedIn_start N P q
  | tail _ fires ih =>
      rcases (firesIn_union _ _ _ _).mp fires with hosted | ⟨f, admitted, rfl⟩
      · obtain ⟨f, admitted, rfl⟩ := hosted
        exact headedIn_fire N ((translate_makes N P).mono N fun _ isAlt => .inl isAlt) admitted.1 ih
      · exact absurd admitted (dec_not_admitted ih f)

/-- **From the start of every query, `decRule` never fires along a run of the union.** -/
theorem counter_never_fires (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy)
    {w : HostState MSig}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ Counter.neighbour)) (Hosting.start N P q) w) :
    ¬ ∃ w', FiresIn Counter.neighbour w w' := by
  rintro ⟨w', f, admitted, _⟩
  exact dec_not_admitted (counter_reached_headed P q run) f admitted

/-- **So it meets the condition along those runs**, with no firing to ask it of. -/
theorem counter_along_start (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy) :
    DisciplinedAlong N (D := D) P Counter.neighbour (Hosting.start N P q) := by
  intro w reached n b a others f _ _ admitted
  exact absurd admitted (dec_not_admitted (counter_reached_headed P q reached) f)

end Counting

#print axioms bare_not_makes
#print axioms relabel_mem
#print axioms headedIn_fire
#print axioms headedIn_run
#print axioms headedIn_start
#print axioms translate_makes
#print axioms flexState_not_headed
#print axioms reached_headed
#print axioms readEqn_amalgamate
#print axioms readEqn_at
#print axioms readEqn_along
#print axioms readEqn_bothWays_along
#print axioms readEqn_strictly_weaker
#print axioms dec_not_admitted
#print axioms counter_reached_headed
#print axioms counter_never_fires
#print axioms counter_along_start

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.ReadersAlong
