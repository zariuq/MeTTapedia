import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Scoping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice

/-!
# Programs with calls through function variables, on the run theorems of the translation

The run theorems of the translation (`Hosting.arrow_runs_forward_of_scoped`, `arrow_answers_of_scoped`,
`arrow_runs_reflected_of_scoped`) ask three things of every equation: it is scoped, its own site and its
binder sites are distinct, and its right-hand side is of the fragment with arrows.

For a surface program **without declarations, read by value, whose bodies are text without `run` marks**,
elaborated under a clause that passes each argument of a tuple whose head is not a symbol evaluated at an
arrow or as text (`Clause.Arrows`, `Clause.Faithful`; the clause by value is one, `byValue_arrows`,
`byValue_faithful`, and so is the clause by a declared type, `declared_arrows`, `declared_faithful`):

* the right-hand side of every equation is of the fragment with arrows (`elabH_arrow`);
* its own site and its binder sites are distinct, with no hypothesis (`elabEquationH_asked`);
* it is scoped when the equation `Elaboration.elaborate` makes is (`elabEquationH_asked`);
* so the three run theorems apply to every run of the program and a query text
  (`static_runs_forward`, `static_answers`, `static_runs_reflected`). The instance is `twice`
  (`twice_asked`, `twice_answers_hosted`).

**Outside the hypotheses**, the code leaves the fragment: a declared value type is checked
(`declared_value_outside`), a variable passed by name runs (`byName_outside`), a `run` mark runs
(`runMark_outside`), the run-time clause runs the tuple (`ExampleTwiceAtRunTime.not_arrows`). The
hypothesis "without declarations" is sufficient, not necessary: a program whose only declaration holds a
parameter is in the fragment (`ExampleHolding.byValue_hosted`).

**What does not carry over** (`wellFormed_not_carried`): `WellFormed` also asks that no two equations
share a binder site. The clause adds arrows where `Elaboration.elaborate` has none, and their sites can
meet another equation's: a program whose elaboration is well formed and whose elaboration under the
clause by value is not. It still satisfies what the run theorems ask. The patterns clause of `WellFormed`
is not treated here in general; for a given program the kernel decides it
(`ExampleTwice.program_wellFormed`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Elaboration
open Hosting

/-! ## The fragment with arrows -/

/-- A clause whose code is of the fragment with arrows: the tuple is called as it stands, or each of
its arguments is evaluated at an arrow or passed as text. -/
def Clause.Arrows : Clause → Prop
  | .asWritten => True
  | .atRunTime => False
  | .static pass => ∀ head i a,
      (∃ u, pass head i a = .text u) ∨ pass head i a = .evaluate none ∨ pass head i a = .byName

theorem byValue_arrows : Clause.byValue.Arrows := by
  intro head i a
  cases a with
  | holdMark o u => exact .inl ⟨u, rfl⟩
  | runMark o inner => exact .inr (.inl rfl)
  | var o x => exact .inr (.inl rfl)
  | symbol o f => exact .inr (.inl rfl)
  | call o f args => exact .inr (.inl rfl)
  | inert o => exact .inr (.inl rfl)
  | other o elements => exact .inr (.inl rfl)

/-- Under a declared type, an argument that is not a mark is passed as its text or evaluated. -/
theorem declared_unmarked (holds : Name mkeys → ℕ → Bool) (head : HView) (i : ℕ) (o : MData) :
    (match head with
      | .var _ x => if holds x i then Pass.text o else Pass.evaluate none
      | _ => Pass.evaluate none) = Pass.text o ∨
    (match head with
      | .var _ x => if holds x i then Pass.text o else Pass.evaluate none
      | _ => Pass.evaluate none) = Pass.evaluate none := by
  cases head with
  | var ho x =>
      dsimp only
      split
      · exact .inl rfl
      · exact .inr rfl
  | holdMark o' u => exact .inr rfl
  | runMark o' inner => exact .inr rfl
  | symbol o' f => exact .inr rfl
  | call o' f args => exact .inr rfl
  | inert o' => exact .inr rfl
  | other o' elements => exact .inr rfl

/-- Under a declared type, what an argument that is not a mark is passed as, when it is passed as text,
is its text. -/
theorem declared_unmarked_text (holds : Name mkeys → ℕ → Bool) (head : HView) (i : ℕ) (o u : MData)
    (same : (match head with
      | .var _ x => if holds x i then Pass.text o else Pass.evaluate none
      | _ => Pass.evaluate none) = Pass.text u) : u = o := by
  rcases declared_unmarked holds head i o with text | evaluated
  · exact Pass.text.inj (same.symm.trans text)
  · exact absurd (same.symm.trans evaluated) (by intro clash; cases clash)

/-- The clause by the declared type of the variable passes as text only what an argument holds or is. -/
theorem declared_faithful (holds : Name mkeys → ℕ → Bool) : (Clause.declared holds).Faithful := by
  intro head i a u passed
  cases a with
  | holdMark o inside => exact .inl ⟨o, by rw [Pass.text.inj passed]⟩
  | runMark o inner => exact absurd passed (by intro clash; cases clash)
  | var o x => exact .inr (declared_unmarked_text holds head i _ u passed)
  | symbol o f => exact .inr (declared_unmarked_text holds head i _ u passed)
  | call o f args => exact .inr (declared_unmarked_text holds head i _ u passed)
  | inert o => exact .inr (declared_unmarked_text holds head i _ u passed)
  | other o elements => exact .inr (declared_unmarked_text holds head i _ u passed)

/-- Its code is of the fragment with arrows. -/
theorem declared_arrows (holds : Name mkeys → ℕ → Bool) : (Clause.declared holds).Arrows := by
  intro head i a
  have unmarked : ∀ o : MData,
      (∃ u, (match head with
        | .var _ x => if holds x i then Pass.text o else Pass.evaluate none
        | _ => Pass.evaluate none) = Pass.text u) ∨
      (match head with
        | .var _ x => if holds x i then Pass.text o else Pass.evaluate none
        | _ => Pass.evaluate none) = Pass.evaluate none := by
    intro o
    rcases declared_unmarked holds head i o with text | evaluated
    · exact .inl ⟨o, text⟩
    · exact .inr evaluated
  cases a with
  | holdMark o inside => exact .inl ⟨inside, rfl⟩
  | runMark o inner => exact .inr (.inl rfl)
  | var o x => exact (unmarked _).imp id .inl
  | symbol o f => exact (unmarked _).imp id .inl
  | call o f args => exact (unmarked _).imp id .inl
  | inert o => exact (unmarked _).imp id .inl
  | other o elements => exact (unmarked _).imp id .inl

/-- Without declarations and by value, a position is evaluated at an arrow unless a `hold` mark stands
there. -/
theorem passOf_plain (π : Params) (byValue : ∀ f i, π.strategy f i = .value) (f : String) (i : ℕ) :
    ∀ a : View, (∃ u, passOf π [] f i a = .text u) ∨ passOf π [] f i a = .evaluate none
  | .holdMark _ u => .inl ⟨u, rfl⟩
  | .runMark _ _ => .inr rfl
  | .var _ _ => .inr (by simp [passOf, declOf, byValue])
  | .symbol _ _ => .inr (by simp [passOf, declOf, byValue])
  | .call _ _ _ => .inr (by simp [passOf, declOf, byValue])
  | .inert _ => .inr (by simp [passOf, declOf, byValue])
  | .other _ => .inr (by simp [passOf, declOf, byValue])

variable (cl : Clause) (π : Params)

mutual
/-- **The code is of the fragment with arrows**: without declarations, by value, on text without `run`
marks whose variables hold values. -/
theorem elabH_arrow (arrows : cl.Arrows) (byValue : ∀ f i, π.strategy f i = .value)
    (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ v : HView, ValueTextH modes v → ArrowComp (elabH cl π [] modes path v)
  | .holdMark _ _, _ => trivial
  | .runMark _ _, valued => absurd valued (by simp [ValueTextH])
  | .var o x, valued => by
      simp only [ValueTextH] at valued
      simp only [elabH, varAt, valued]
      trivial
  | .symbol _ _, _ => trivial
  | .call _ f args, valued => by
      simp only [elabH]
      exact elabArgsH_arrow arrows byValue _
        (fun i a => (passOf_plain π byValue f i a.forget).imp id .inl) _
        (fun done => by simp [finish, declOf, ArrowComp]) modes path 0 args [] valued
  | .inert _, _ => trivial
  | .other _ [], _ => trivial
  | .other o (head :: args), valued => by
      have parts : ValueTextH modes head ∧ ValueTextH.ValueArgsH modes args := valued
      have atHead := elabH_arrow arrows byValue modes (path ++ [args.length]) head parts.1
      have atArgs := fun (pass : ℕ → HView → Pass)
          (passPlain : ∀ i a, (∃ u, pass i a = .text u) ∨ pass i a = .evaluate none ∨ pass i a = .byName)
          (fin : List MData → Comp mkeys [] () MTy) (finArrow : ∀ done, ArrowComp (fin done)) =>
        elabArgsH_arrow arrows byValue pass passPlain fin finArrow modes path 0 args [] parts.2
      cases cl with
      | asWritten => trivial
      | atRunTime => exact absurd arrows id
      | static pass =>
          simp only [elabH]
          split
          · exact atArgs (pass head) (arrows head) _ (fun _ => trivial)
          · exact ⟨atHead, atArgs (pass head) (arrows head) _ (fun _ => trivial)⟩

theorem elabArgsH_arrow (arrows : cl.Arrows) (byValue : ∀ f i, π.strategy f i = .value)
    (pass : ℕ → HView → Pass)
    (passPlain : ∀ i a, (∃ u, pass i a = .text u) ∨ pass i a = .evaluate none ∨ pass i a = .byName)
    (fin : List MData → Comp mkeys [] () MTy) (finArrow : ∀ done, ArrowComp (fin done))
    (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ (i : ℕ) (args : List HView) (done : List MData), ValueTextH.ValueArgsH modes args →
      ArrowComp (elabArgsH cl π [] pass fin modes path i args done)
  | _, [], done, _ => by
      simp only [elabArgsH]
      exact finArrow _
  | i, a :: rest, done, ⟨first, others⟩ => by
      have later := fun done' =>
        elabArgsH_arrow arrows byValue pass passPlain fin finArrow modes path (i + 1) rest done' others
      have here := elabH_arrow arrows byValue modes (path ++ [i]) a first
      rcases passPlain i a with ⟨u, passed⟩ | passed | passed
      · simp only [elabArgsH, passed]
        exact later _
      · simp only [elabArgsH, passed]
        exact ⟨here, later _⟩
      · simp only [elabArgsH, passed]
        exact later _
end

/-! ## What the run theorems ask, of an equation -/

/-- Without declarations, the body of an equation that is text without a `run` mark at its root is the
text's code under the clause. -/
theorem elabBodyH_text (e : SEquation) (t : MData) (body : e.body = .text t)
    (valued : ValueTextH (paramModes π [] e) (hview t)) :
    elabBodyH cl π [] e = elabH cl π [] (paramModes π [] e) (1 :: e.site) (hview t) := by
  unfold elabBodyH
  rw [body]
  dsimp only
  cases shape : hview t with
  | holdMark o u => rfl
  | runMark o inner =>
      rw [shape] at valued
      exact absurd valued (by simp [ValueTextH])
  | var o x => rfl
  | symbol o f => rfl
  | call o f args => rfl
  | inert o => rfl
  | other o elements => rfl

/-- The same for the elaboration's body. -/
theorem elabBody_text (e : SEquation) (t : MData) (body : e.body = .text t)
    (valued : ValueTextH (paramModes π [] e) (hview t)) :
    elabBody π [] e = elabText π [] (paramModes π [] e) (1 :: e.site) (hview t).forget := by
  unfold elabBody
  rw [body]
  dsimp only
  rw [← forget_hview t]
  cases shape : hview t with
  | holdMark o u => rfl
  | runMark o inner =>
      rw [shape] at valued
      exact absurd valued (by simp [ValueTextH])
  | var o x => rfl
  | symbol o f => rfl
  | call o f args => rfl
  | inert o => rfl
  | other o elements => rfl

/-- **What the run theorems ask of an equation**, under a clause of the fragment with arrows: scoped when
the elaboration's equation is; its site and its binder sites distinct; of the fragment. -/
theorem elabEquationH_asked (faithful : cl.Faithful) (arrows : cl.Arrows)
    (byValue : ∀ f i, π.strategy f i = .value) (e : SEquation) (t : MData) (body : e.body = .text t)
    (valued : ValueTextH (paramModes π [] e) (hview t)) (present : (elabEquation π [] e).Scoped) :
    (elabEquationH cl π [] e).Scoped ∧
      ((elabEquationH cl π [] e).site :: (elabEquationH cl π [] e).rhs.sites).Nodup ∧
      ArrowComp (elabEquationH cl π [] e).rhs := by
  have rhsH : (elabEquationH cl π [] e).rhs = elabH cl π [] (paramModes π [] e) (1 :: e.site) (hview t) :=
    elabBodyH_text cl π e t body valued
  have rhs0 : (elabEquation π [] e).rhs =
      elabText π [] (paramModes π [] e) (1 :: e.site) (hview t).forget := elabBody_text π e t body valued
  have scoped0 : (elabText π [] (paramModes π [] e) (1 :: e.site) (hview t).forget).Scoped [e.site] := by
    rw [← rhs0]
    exact present.2
  refine ⟨⟨present.1, ?_⟩, ?_, ?_⟩
  · rw [rhsH]
    exact elabH_scoped_of cl π [] faithful _ _ (hview t) [e.site] (hview_coherent t) scoped0
  · rw [rhsH]
    refine List.nodup_cons.mpr ⟨fun member => ?_, elabH_nodup cl π [] _ _ _⟩
    obtain ⟨i, r, same⟩ := elabH_sites cl π [] _ _ _ _ member
    have lengths := congrArg List.length same
    simp only [elabEquationH, List.length_append, List.length_cons] at lengths
    omega
  · rw [rhsH]
    exact elabH_arrow cl π arrows byValue _ _ _ valued

/-- **What the run theorems ask of a program.** -/
theorem elaborateH_asked (faithful : cl.Faithful) (arrows : cl.Arrows)
    (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram) (noDecls : P.decls = [])
    (texts : ∀ e ∈ P.equations, ∃ t, e.body = .text t ∧ ValueTextH (paramModes π [] e) (hview t))
    (present : ∀ e ∈ P.equations, (elabEquation π [] e).Scoped) :
    ∀ e ∈ (elaborateH cl π P).equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs := by
  intro e member
  simp only [elaborateH, noDecls, List.mem_map] at member
  obtain ⟨s, inside, rfl⟩ := member
  obtain ⟨t, body, valued⟩ := texts s inside
  exact elabEquationH_asked cl π faithful arrows byValue s t body valued (present s inside)

/-- **What the run theorems ask of a query text** whose names are unopened names of the site `[3]`. -/
theorem elabQueryH_asked (faithful : cl.Faithful) (arrows : cl.Arrows)
    (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram) (noDecls : P.decls = []) (t : MData)
    (names : NamesIn (κ := mkeys) [[3]] t) (valued : ValueTextH (fun _ => .value) (hview t)) :
    (elabQueryH cl π P (.text t)).Scoped [[3]] ∧ ([3] :: (elabQueryH cl π P (.text t)).sites).Nodup ∧
      ArrowComp (elabQueryH cl π P (.text t)) := by
  have code : elabQueryH cl π P (.text t) = elabH cl π [] (fun _ => .value) [3] (hview t) := by
    simp only [elabQueryH, elabCompH, noDecls]
  rw [code]
  refine ⟨?_, ?_, elabH_arrow cl π arrows byValue _ _ _ valued⟩
  · exact elabH_scoped cl π [] faithful _ _ (hview t) [[3]]
      (NamesWithinH.mono (fun x hx => names x hx) _ (hview_within t))
  · refine List.nodup_cons.mpr ⟨fun member => ?_, elabH_nodup cl π [] _ _ _⟩
    obtain ⟨i, r, same⟩ := elabH_sites cl π [] _ _ _ _ member
    have lengths := congrArg List.length same
    simp only [List.length_append, List.length_cons, List.length_nil] at lengths
    omega

/-! ## The run theorems, applied -/

variable (N : Nodes MSig [] ()) (τ : Typing) (supply : ℕ → MClosed)
  (spaces : MClosed → Multiset (Row mkeys [] ()))

/-- **Every source run is followed by runs of the step.** -/
theorem static_runs_forward (faithful : cl.Faithful) (arrows : cl.Arrows)
    (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram) (noDecls : P.decls = [])
    (texts : ∀ e ∈ P.equations, ∃ t, e.body = .text t ∧ ValueTextH (paramModes π [] e) (hview t))
    (present : ∀ e ∈ P.equations, (elabEquation π [] e).Scoped) (t : MData)
    (names : NamesIn (κ := mkeys) [[3]] t) (valued : ValueTextH (fun _ => .value) (hview t))
    {C : Config mkeys [] () MTy}
    (runs : Runs τ.discipline (elaborateH cl π P) supply
      (Config.initial spaces (elabQueryH cl π P (.text t))) C) :
    ∃ L, ArrowFrontier (D := τ.discipline) N (elaborateH cl π P) C L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N (elaborateH cl π P))
        (Hosting.start N (elaborateH cl π P) (elabQueryH cl π P (.text t))) x.2.1 := by
  obtain ⟨qScoped, qDistinct, qArrow⟩ := elabQueryH_asked cl π faithful arrows byValue P noDecls t names valued
  exact arrow_runs_forward_of_scoped N (D := τ.discipline) (P := elaborateH cl π P) (supply := supply) spaces _
    (elaborateH_asked cl π faithful arrows byValue P noDecls texts present) qScoped qDistinct qArrow runs

/-- **The answers of every configuration a source run reaches, as a bag, are those of a frontier reached
by the step.** -/
theorem static_answers (faithful : cl.Faithful) (arrows : cl.Arrows)
    (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram) (noDecls : P.decls = [])
    (texts : ∀ e ∈ P.equations, ∃ t, e.body = .text t ∧ ValueTextH (paramModes π [] e) (hview t))
    (present : ∀ e ∈ P.equations, (elabEquation π [] e).Scoped) (t : MData)
    (names : NamesIn (κ := mkeys) [[3]] t) (valued : ValueTextH (fun _ => .value) (hview t))
    {C : Config mkeys [] () MTy}
    (runs : Runs τ.discipline (elaborateH cl π P) supply
      (Config.initial spaces (elabQueryH cl π P (.text t))) C) :
    ∃ L : Multiset (Branch mkeys [] () τ.discipline.Ty × HostState MSig × ℕ),
      C.answers (D := τ.discipline) = frontierAnswers N L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N (elaborateH cl π P))
        (Hosting.start N (elaborateH cl π P) (elabQueryH cl π P (.text t))) x.2.1 := by
  obtain ⟨qScoped, qDistinct, qArrow⟩ := elabQueryH_asked cl π faithful arrows byValue P noDecls t names valued
  exact arrow_answers_of_scoped N (D := τ.discipline) (P := elaborateH cl π P) (supply := supply) spaces _
    (elaborateH_asked cl π faithful arrows byValue P noDecls texts present) qScoped qDistinct qArrow runs

/-- **Every run of the step from the translation's start is a source run.** -/
theorem static_runs_reflected (faithful : cl.Faithful) (arrows : cl.Arrows)
    (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram) (noDecls : P.decls = [])
    (texts : ∀ e ∈ P.equations, ∃ t, e.body = .text t ∧ ValueTextH (paramModes π [] e) (hview t))
    (present : ∀ e ∈ P.equations, (elabEquation π [] e).Scoped) (t : MData)
    (names : NamesIn (κ := mkeys) [[3]] t) (valued : ValueTextH (fun _ => .value) (hview t))
    {s : HostState MSig}
    (run : Relation.ReflTransGen (Fires N (elaborateH cl π P))
      (Hosting.start N (elaborateH cl π P) (elabQueryH cl π P (.text t))) s) :
    ∃ (C : Config mkeys [] () MTy) (b : Branch mkeys [] () MTy) (a : ℕ),
      Runs τ.discipline (elaborateH cl π P) supply (Config.initial spaces (elabQueryH cl π P (.text t))) C ∧
        b ∈ C.branches ∧ Represents N (elaborateH cl π P) C.world.scope b s a ∧ ArrowBranch b := by
  obtain ⟨qScoped, qDistinct, qArrow⟩ := elabQueryH_asked cl π faithful arrows byValue P noDecls t names valued
  exact arrow_runs_reflected_of_scoped N (D := τ.discipline) (P := elaborateH cl π P) (supply := supply) spaces _
    (elaborateH_asked cl π faithful arrows byValue P noDecls texts present) qScoped qDistinct qArrow run

/-! ## Deciding the hypothesis on text -/

mutual
/-- Text without `run` marks whose variables hold values: decided. -/
def decValueTextH (modes : Name mkeys → VarMode) : (v : HView) → Decidable (ValueTextH modes v)
  | .holdMark _ _ => isTrue trivial
  | .runMark _ _ => isFalse (by simp [ValueTextH])
  | .var _ x => inferInstanceAs (Decidable (modes x = .value))
  | .symbol _ _ => isTrue trivial
  | .call _ _ args => decValueArgsH modes args
  | .inert _ => isTrue trivial
  | .other _ elements => decValueArgsH modes elements

def decValueArgsH (modes : Name mkeys → VarMode) :
    (args : List HView) → Decidable (ValueTextH.ValueArgsH modes args)
  | [] => isTrue trivial
  | a :: rest =>
      letI := decValueTextH modes a
      letI := decValueArgsH modes rest
      inferInstanceAs (Decidable (_ ∧ _))
end

instance (modes : Name mkeys → VarMode) (v : HView) : Decidable (ValueTextH modes v) := decValueTextH modes v

/-! ## The instance: `twice` -/

open ExampleTwice in
/-- The hypotheses on the text of `twice`. -/
theorem twice_texts : ∀ e ∈ surface.equations,
    ∃ t, e.body = .text t ∧ ValueTextH (paramModes byValue [] e) (hview t) :=
  List.forall_mem_cons.mpr ⟨⟨_, rfl, by decide⟩,
    List.forall_mem_cons.mpr ⟨⟨_, rfl, by decide⟩, fun _ member => nomatch member⟩⟩

open ExampleTwice in
/-- The equations the elaboration makes of the text of `twice` are scoped. -/
theorem twice_present : ∀ e ∈ surface.equations, (elabEquation byValue [] e).Scoped :=
  List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, fun _ member => nomatch member⟩⟩

open ExampleTwice in
/-- **The program of `twice` under the clause by value satisfies what the run theorems ask**, by the
general theorem. -/
theorem twice_asked :
    ∀ e ∈ program.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs :=
  elaborateH_asked .byValue byValue byValue_faithful byValue_arrows (fun _ _ => rfl) surface rfl twice_texts
    twice_present

open ExampleTwice in
/-- **The answers of every configuration a run of `(twice inc Z)` reaches are those of a frontier
reached by the step**, by the general theorem. -/
theorem twice_answers_hosted {C : Config mkeys [] () MTy}
    (runs : Runs untyped.discipline program ExampleTwice.supply
      (Config.initial sp (elabQueryH .byValue byValue surface (.text (tuple [sym "twice", sym "inc", sym "Z"])))) C) :
    ∃ L : Multiset (Branch mkeys [] () untyped.discipline.Ty × HostState MSig × ℕ),
      C.answers (D := untyped.discipline) = frontierAnswers mettaNodes L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires mettaNodes program)
        (Hosting.start mettaNodes program
          (elabQueryH .byValue byValue surface (.text (tuple [sym "twice", sym "inc", sym "Z"])))) x.2.1 :=
  static_answers .byValue byValue mettaNodes untyped ExampleTwice.supply sp byValue_faithful byValue_arrows
    (fun _ _ => rfl) surface rfl twice_texts twice_present _ (by decide) (by decide) runs

open ExampleTwice in
/-- **The code of `twice` by value runs nothing**, by the general law. -/
theorem twice_runs_nothing :
    Laws.reruns (elabH .byValue byValue [] (paramModes byValue [] twiceS) [1, 241]
      (hview (tuple [fT, tuple [fT, xT]]))) = [] :=
  valuesH_never_run .byValue byValue [] (by intro clash; cases clash) _ _ _ (by decide)

open ExampleTwice in
/-- **Naming `inc` does not change the code of its call**, by the general law: under the clause by
value, the call of an argument through a variable that holds a value and the direct call of `inc` on it
are one code, at the variable and at the symbol. -/
theorem naming_inc (modes : Name mkeys → VarMode) (path : List ℕ) (o o' ho : MData) (x : Name mkeys)
    (args : List HView) (value : modes x = .value) :
    ∃ code : MData → Comp mkeys [] () MTy,
      elabH .byValue byValue [] modes path (.other o (.var ho x :: args)) = code ho ∧
        elabH .byValue byValue [] modes path (.call o' "inc" args) = code (sym "inc") :=
  naming byValue [] (fun _ _ a => passByValue a) modes path o o' ho x "inc" args value
    (fun i a => passOf_byValue byValue (fun _ _ => rfl) "inc" i a) rfl

/-! ## Outside the hypotheses -/

/-- A declared value type is checked: the code leaves the fragment with arrows. -/
theorem declared_value_outside :
    ¬ ArrowComp (elabH .byValue ExampleTwice.byValue [⟨"g", [.value "Number"], .undefined⟩] (fun _ => .value) []
      (hview (tuple [sym "g", sym "a"]))) :=
  fun arrows => arrows.1

/-- A variable passed by name runs where a value is wanted: the code leaves the fragment with arrows. -/
theorem byName_outside :
    ¬ ArrowComp (elabH .byValue ⟨fun _ _ => .name, false, false⟩ [] (fun _ => .name) []
      (hview (Toolkit.foD [] [9] 0))) :=
  fun arrows => arrows

/-- A `run` mark on a variable runs it: the code leaves the fragment with arrows. -/
theorem runMark_outside :
    ¬ ArrowComp (elabH .byValue ExampleTwice.byValue [] (fun _ => .value) []
      (hview (run (Toolkit.foD [] [9] 0)))) :=
  fun arrows => arrows

/-! ## What does not carry over -/

namespace NotCarried

open Toolkit

/-- `(= (h $f $x) ($f ($f $x)))` at the site `[5]`. -/
def hS : SEquation :=
  ⟨[5], "h", [foD [] [5] 0, foD [] [5] 1], .text (tuple [foD [] [5] 0, tuple [foD [] [5] 0, foD [] [5] 1]])⟩

/-- `(= (g $y) (c $y))` at the site `[5, 0]`. -/
def gS : SEquation := ⟨[5, 0], "g", [foD [] [5, 0] 0], .text (tuple [sym "c", foD [] [5, 0] 0])⟩

def surface : SProgram := ⟨[], [hS, gS]⟩

end NotCarried

open NotCarried in
/-- **`WellFormed` does not carry over.** The elaboration of this program is well formed; its elaboration
under the clause by value is not, because the arrow the clause adds in the body of `h` has the site of
the arrow in the body of `g`; and it satisfies what the run theorems ask. -/
theorem wellFormed_not_carried :
    WellFormed (elaborate ExampleTwice.byValue NotCarried.surface) ∧
      ¬ WellFormed (elaborateH .byValue ExampleTwice.byValue NotCarried.surface) ∧
      ∀ e ∈ (elaborateH .byValue ExampleTwice.byValue NotCarried.surface).equations,
        e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs := by
  refine ⟨by decide, by decide, ?_⟩
  exact elaborateH_asked .byValue ExampleTwice.byValue byValue_faithful byValue_arrows (fun _ _ => rfl)
    NotCarried.surface rfl
    (List.forall_mem_cons.mpr ⟨⟨_, rfl, by decide⟩,
      List.forall_mem_cons.mpr ⟨⟨_, rfl, by decide⟩, fun _ member => nomatch member⟩⟩)
    (List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, fun _ member => nomatch member⟩⟩)

#print axioms byValue_arrows
#print axioms declared_faithful
#print axioms declared_arrows
#print axioms elabH_arrow
#print axioms elabEquationH_asked
#print axioms elaborateH_asked
#print axioms elabQueryH_asked
#print axioms static_runs_forward
#print axioms static_answers
#print axioms static_runs_reflected
#print axioms twice_asked
#print axioms twice_answers_hosted
#print axioms twice_runs_nothing
#print axioms naming_inc
#print axioms declared_value_outside
#print axioms byName_outside
#print axioms runMark_outside
#print axioms wellFormed_not_carried

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables
