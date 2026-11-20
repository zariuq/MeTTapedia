import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.RuleClasses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derivations

/-!
# Named source equations as held rule occurrences

A source program is a list of equations, so an equation written twice is two equations. Its
translation (`Hosting.translate`) is a set of rules: the control rules and one schema per equation.
An equation written twice gives one schema, and the set keeps it once. This module presents the
same translated program with the equations **held as rule occurrences**, one occurrence per
position in the equation list, and relates the source's named moves to the firings of that
presentation.

## The two constructions compared

Both are steps of rules over a store, in the five choices:

* **the set presentation** (`Hosting.hostStep`): a bag store of rows (occurrence identities with
  labels); one match per step; guards asked after the firing's own tells; the rules fixed beside the
  store as a **set** (control rules and schemas); one knowledge store.
* **the held presentation** (`heldStep` at the states `heldState`): the same bag store of rows; one
  match per step; guards asked after the firing's own tells; the **control rules fixed beside the
  store** (the ambient program) and the **equation schemas held in the store** as persistent rule
  occurrences, the occurrence `i` holding the schema of the equation at position `i`
  (`RuleOccurrences.rstep` with the code system `RuleOccurrences.ofRules`); one knowledge store.

The source's names of firings (`Hosting.Alternatives.RuleName`: the control rules by their tags, an
equation by its position) become the **origins** of held firings (`origin`): a control rule's tag
names that rule of the ambient program, and the equation at position `i` names the occurrence `i`.

## What is shown

* `heldStep_succ_iff`, `heldStep_closed`: between held states the two presentations have the same
  transitions, for every source program (an instance of `RuleOccurrences.program_eq`).
* `origin_injective`: distinct names have distinct origins. No hypothesis on the equations: two
  equations with one schema keep their two positions.
* `firesNamed_iff_heldFires`: **a named firing of the translated program is a held firing by the
  name's origin**, with the same taken and made rows and the held state over the same result, and
  conversely. Control rules stay ambient; only equation occurrences are held.
* `use_named`: from a state that represents an alternative of the first fragment, every admitted held
  firing has the origin of a name, so it is a named firing.
* `held_of_namedMove`, `namedMove_of_held`: in the source's own terms, a named move of a represented
  alternative of the first fragment to a live child is a held firing by the name's origin whose
  result represents the child, and every held firing from a represented alternative is the named
  move of a name whose origin it uses, with the result representing the move's child.
* `heldFires_firesAt`: forgetting the origin of a held firing leaves a firing of the set
  presentation by the origin's rule.

## What is not shown here

Classes of histories, answers and multiplicities are in `CountedClasses` and `CountedFibres`; the
closed example of an equation written twice is in `CountedExample`. Nothing here is about programs
outside the first fragment (`let`, effects, reflection), and nothing compares concurrent executions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Counted

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Hosting Hosting.Alternatives
open RuleOccurrences
open LogicOverTheStep.StepSpan (Succ)

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S} {Ty : Type}

/-! ## The held presentation -/

section Presentation

/-- **The rules of a program's equations**: one schema per equation, as a set. -/
def equationRules (P : SourceLanguage.Program κ Γ star Ty) : CProgram S :=
  {r | ∃ e ∈ P.equations, r = schema N e}

/-- The translation is the control rules and the equations' rules. -/
theorem translate_eq (P : SourceLanguage.Program κ Γ star Ty) :
    translate N P = controlRules N ∪ equationRules N P :=
  rfl

/-- **The identities of the held occurrences**: the positions of the equations. -/
abbrev heldIds (P : SourceLanguage.Program κ Γ star Ty) : Finset ℕ :=
  Finset.range P.equations.length

/-- **The rule the occurrence `i` holds**: the schema of the equation at position `i`. Identities
past the end of the list are not held (`heldIds`), so no firing uses the rule given there. -/
def heldRule (P : SourceLanguage.Program κ Γ star Ty) (i : ℕ) : CRule S :=
  ((P.equations[i]?).map (schema N)).getD (retRule N)

variable {N} in
theorem heldRule_of_get {P : SourceLanguage.Program κ Γ star Ty} {i : ℕ}
    {e : SourceLanguage.Equation κ Γ star Ty} (get : P.equations[i]? = some e) :
    heldRule N P i = schema N e := by
  simp [heldRule, get]

variable {N} in
theorem heldRule_lt {P : SourceLanguage.Program κ Γ star Ty} {i : ℕ} (small : i < P.equations.length) :
    heldRule N P i = schema N P.equations[i] :=
  heldRule_of_get (List.getElem?_eq_getElem small)

/-- **The held occurrences offer exactly the equations' rules.** -/
theorem offers (P : SourceLanguage.Program κ Γ star Ty) :
    Offers (equationRules N P) (heldIds P) (heldRule N P) := by
  intro r
  constructor
  · rintro ⟨e, member, rfl⟩
    obtain ⟨i, small, rfl⟩ := List.getElem_of_mem member
    exact ⟨i, Finset.mem_range.mpr small, heldRule_lt small⟩
  · rintro ⟨i, held, rfl⟩
    have small := Finset.mem_range.mp held
    exact ⟨P.equations[i], List.getElem_mem small, heldRule_lt small⟩

/-- **The held state over a state of the step**: its frame, knowledge and rows, and the equation
occurrences `0, …, m - 1`, each holding its equation's schema persistently, without arguments. -/
abbrev heldState (P : SourceLanguage.Program κ Γ star Ty) (s : HostState S) :
    RState (RuleSyntax.Contextual.Terms S) ℕ ℕ (CRule S) Unit :=
  holding s (heldIds P) (heldRule N P) (fun _ => ())

/-- **The held-rule step**: the control rules are its ambient program; the equations are held by the
state. It does not depend on the source program: the program is in the state. -/
abbrev heldStep :=
  rstep (Interface.Frames.contextual S) ℕ ℕ (RuleSyntax.Contextual.declarations S)
    (ofRules (Tm := RuleSyntax.Contextual.Terms S) Unit) (controlRules N)

/-- A firing of the held-rule step at the held state over `s`. -/
abbrev HeldFiring (P : SourceLanguage.Program κ Γ star Ty) (s : HostState S) :=
  RFiring ℕ ℕ (RuleSyntax.Contextual.declarations S) (ofRules (Tm := RuleSyntax.Contextual.Terms S) Unit)
    (heldState N P s)

/-- **The same transitions**: between held states, the held-rule step moves exactly as the step of
the translated program. -/
theorem heldStep_succ_iff (P : SourceLanguage.Program κ Γ star Ty) (s t : HostState S) :
    Succ (heldStep N).toStep (heldState N P s) (heldState N P t) ↔ Succ (hostStep N P).toStep s t :=
  program_eq ℕ (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S) (offers N P)
    (fun _ => ()) s t

/-- **The held-rule step never leaves the held states.** -/
theorem heldStep_closed (P : SourceLanguage.Program κ Γ star Ty) {s : HostState S}
    {u : RState (RuleSyntax.Contextual.Terms S) ℕ ℕ (CRule S) Unit}
    (moved : Succ (heldStep N).toStep (heldState N P s) u) :
    ∃ t, u = heldState N P t ∧ Succ (hostStep N P).toStep s t :=
  holding_closed ℕ (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S) (offers N P)
    (fun _ => ()) moved

end Presentation

/-! ## Origins of names -/

section Origins

/-- **The origin a name denotes**: a control rule's tag denotes that rule of the ambient program, and
the equation at position `i` denotes the held occurrence `i`. -/
def origin : RuleName → Use (CRule S) ℕ
  | .ret => .ambient (retRule N)
  | .unmatched => .ambient (unmatchedRule N)
  | .left => .ambient (choiceLeftRule N)
  | .right => .ambient (choiceRightRule N)
  | .eqn i => .held i

theorem ret_ne_unmatched : retRule N ≠ unmatchedRule N :=
  checks_ne (by show (0 : ℕ) ≠ 1; omega)

theorem ret_ne_left : retRule N ≠ choiceLeftRule N :=
  ne_of_headTag N (List.cons_ne_nil _ _) (retRule_headTag N) (choiceLeftRule_headTag N) (by decide)

theorem ret_ne_right : retRule N ≠ choiceRightRule N :=
  ne_of_headTag N (List.cons_ne_nil _ _) (retRule_headTag N) (choiceRightRule_headTag N) (by decide)

theorem unmatched_ne_left : unmatchedRule N ≠ choiceLeftRule N :=
  checks_ne (by show (1 : ℕ) ≠ 0; omega)

theorem unmatched_ne_right : unmatchedRule N ≠ choiceRightRule N :=
  checks_ne (by show (1 : ℕ) ≠ 0; omega)

/-- **Distinct names have distinct origins**, for every program: equations keep their positions,
and the four control rules of the fragment are pairwise distinct. -/
theorem origin_injective : Function.Injective (origin N) := by
  have h₁ := ret_ne_unmatched N
  have h₂ := ret_ne_left N
  have h₃ := ret_ne_right N
  have h₄ := unmatched_ne_left N
  have h₅ := unmatched_ne_right N
  have h₆ := left_ne_right N
  intro n m same
  cases n <;> cases m <;> simp only [origin, Use.ambient.injEq, Use.held.injEq, reduceCtorEq] at same
  all_goals first
    | rfl
    | exact congrArg RuleName.eqn same
    | exact absurd same h₁
    | exact absurd same h₂
    | exact absurd same h₃
    | exact absurd same h₄
    | exact absurd same h₅
    | exact absurd same h₆
    | exact absurd same.symm h₁
    | exact absurd same.symm h₂
    | exact absurd same.symm h₃
    | exact absurd same.symm h₄
    | exact absurd same.symm h₅
    | exact absurd same.symm h₆

variable {N}

/-- **A name that denotes a rule has an available origin, and the origin's rule is that rule.** -/
theorem origin_available {P : SourceLanguage.Program κ Γ star Ty} {n : RuleName} {r : CRule S}
    (named : ruleNamed N P n = some r) (s : HostState S) :
    (heldState N P s).Available (controlRules N) (origin N n) ∧
      (heldState N P s).codeOf (origin N n) = r := by
  cases n with
  | ret =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      exact ⟨(mem_controlRules N).mpr (Or.inl rfl), rfl⟩
  | unmatched =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      exact ⟨(mem_controlRules N).mpr (Or.inr (Or.inl rfl)), rfl⟩
  | left =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      exact ⟨(mem_controlRules N).mpr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  | right =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      exact ⟨(mem_controlRules N).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
  | eqn i =>
      obtain ⟨e, get, rfl⟩ := Option.map_eq_some_iff.mp named
      obtain ⟨small, -⟩ := List.getElem?_eq_some_iff.mp get
      exact ⟨Finset.mem_range.mpr small, heldRule_of_get get⟩

/-- **An available origin of a name denotes its rule**: the name denotes the origin's rule. -/
theorem ruleNamed_of_available {P : SourceLanguage.Program κ Γ star Ty} {n : RuleName}
    {s : HostState S} (available : (heldState N P s).Available (controlRules N) (origin N n)) :
    ruleNamed N P n = some ((heldState N P s).codeOf (origin N n)) := by
  cases n with
  | ret => rfl
  | unmatched => rfl
  | left => rfl
  | right => rfl
  | eqn i =>
      have small : i < P.equations.length := Finset.mem_range.mp available
      show (P.equations[i]?).map (schema N) = some (heldRule N P i)
      rw [heldRule_lt small, List.getElem?_eq_getElem small]
      rfl

end Origins

/-! ## Named firings are held firings by their origins -/

section Firings

/-- **A held firing by an origin**: an admitted firing of the held-rule step at the held state over
`s`, by the origin `u`, taking the row `o` and making the row `o'`, whose result is the held state
over `s'`. -/
def HeldFires (P : SourceLanguage.Program κ Γ star Ty) (u : Use (CRule S) ℕ)
    (s : HostState S) (o : ℕ) (s' : HostState S) (o' : ℕ) : Prop :=
  ∃ f : HeldFiring N P s, f.use = u ∧ f.Admits (Interface.Frames.contextual S) (controlRules N) ∧
    f.selection.taken = [o] ∧ f.selection.made = [o'] ∧
      f.result (Interface.Frames.contextual S) = heldState N P s'

variable {N}

/-- The rule a held firing fires belongs to the translated program. -/
theorem heldFiring_member {P : SourceLanguage.Program κ Γ star Ty} {s : HostState S} {f : HeldFiring N P s}
    (admitted : f.Admits (Interface.Frames.contextual S) (controlRules N)) :
    (heldState N P s).codeOf f.use ∈ translate N P :=
  member_of_admits (Interface.Frames.contextual S) (offers N P) (fun _ => ()) admitted

/-- **Forgetting the origin**: an admitted held firing is an admitted firing of the translated program
by the origin's rule, with the same selection, and its result is the held state over that firing's
result. -/
theorem heldFiring_project {P : SourceLanguage.Program κ Γ star Ty} {s : HostState S} {f : HeldFiring N P s}
    (admitted : f.Admits (Interface.Frames.contextual S) (controlRules N)) :
    (toProgram f (heldFiring_member admitted)).Admits (Interface.Frames.contextual S) s ∧
      f.result (Interface.Frames.contextual S) =
        heldState N P ((toProgram f (heldFiring_member admitted)).result (Interface.Frames.contextual S) s) := by
  obtain ⟨baseAdmitted, -, none, -, noRemoved, -⟩ :=
    (admits_toProgram_iff (Interface.Frames.contextual S) f (heldFiring_member admitted) (controlRules N)).mp
      admitted
  exact ⟨baseAdmitted,
    result_holding (Interface.Frames.contextual S) f (heldFiring_member admitted) none noRemoved⟩

/-- **A held firing is a firing of the set presentation by its origin's rule.** -/
theorem heldFires_firesAt {P : SourceLanguage.Program κ Γ star Ty} {u : Use (CRule S) ℕ}
    {s s' : HostState S} {o o' : ℕ} (fired : HeldFires N P u s o s' o') :
    FiresAt (translate N P) ((heldState N P s).codeOf u) s o s' o' := by
  obtain ⟨f, use, admitted, taken, made, result⟩ := fired
  obtain ⟨baseAdmitted, endpoint⟩ := heldFiring_project admitted
  refine ⟨toProgram f (heldFiring_member admitted), ?_, baseAdmitted, taken, made,
    holding_injective (endpoint.symm.trans result)⟩
  show (heldState N P s).codeOf f.use = (heldState N P s).codeOf u
  rw [use]

/-- **Lifting a firing of the set presentation along an origin**: a firing by a rule lifts, along
every available origin of that rule, to a held firing by that origin. -/
theorem heldFires_of_firesAt {P : SourceLanguage.Program κ Γ star Ty} {u : Use (CRule S) ℕ}
    {r : CRule S} {s s' : HostState S} {o o' : ℕ}
    (available : (heldState N P s).Available (controlRules N) u) (code : (heldState N P s).codeOf u = r)
    (fired : FiresAt (translate N P) r s o s' o') : HeldFires N P u s o s' o' := by
  obtain ⟨g, rule, admitted, taken, made, result⟩ := fired
  obtain ⟨f, member, use, same, fAdmitted, fResult⟩ :=
    lift_admits (Interface.Frames.contextual S) g admitted available (code.trans rule.symm)
  refine ⟨f, use, fAdmitted, ?_, ?_, ?_⟩
  · exact (congrArg (fun g' : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P)
      s.frame => g'.selection.taken) same).trans taken
  · exact (congrArg (fun g' : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P)
      s.frame => g'.selection.made) same).trans made
  · rw [fResult, result]

/-- **A named firing is a held firing by the name's origin.** -/
theorem heldFires_of_firesNamed {P : SourceLanguage.Program κ Γ star Ty} {n : RuleName}
    {s s' : HostState S} {o o' : ℕ} (fired : FiresNamed N P n s o s' o') :
    HeldFires N P (origin N n) s o s' o' := by
  obtain ⟨r, named, firedAt⟩ := fired
  obtain ⟨available, code⟩ := origin_available named s
  exact heldFires_of_firesAt available code firedAt

/-- **A held firing by a name's origin is a named firing.** -/
theorem firesNamed_of_heldFires {P : SourceLanguage.Program κ Γ star Ty} {n : RuleName}
    {s s' : HostState S} {o o' : ℕ} (fired : HeldFires N P (origin N n) s o s' o') :
    FiresNamed N P n s o s' o' := by
  have available : (heldState N P s).Available (controlRules N) (origin N n) := by
    obtain ⟨f, use, admitted, _⟩ := fired
    have shapes := admitted.1.2.2.available
    rw [use] at shapes
    exact shapes
  exact ⟨_, ruleNamed_of_available available, heldFires_firesAt fired⟩

/-- **Named firings and held firings by origins are the same transitions**: for every name, every
state and every pair of rows, with the same result. No hypothesis on the program. -/
theorem firesNamed_iff_heldFires {P : SourceLanguage.Program κ Γ star Ty} {n : RuleName}
    {s s' : HostState S} {o o' : ℕ} :
    FiresNamed N P n s o s' o' ↔ HeldFires N P (origin N n) s o s' o' :=
  ⟨heldFires_of_firesNamed, firesNamed_of_heldFires⟩

variable (N) in
/-- **Every held firing from an alternative of the first fragment has the origin of a name**: an
equation occurrence, or one of the four control rules that the fragment uses (no `let` rule fires
there, `Hosting.Alternatives.no_bind_firing`). -/
theorem use_named {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {k : ℕ}
    {b : Branch κ Γ star D.Ty} {s : HostState S} {a : ℕ} (rep : Represents N P k b s a)
    (plain : PlainBranch b) {f : HeldFiring N P s}
    (admitted : f.Admits (Interface.Frames.contextual S) (controlRules N)) :
    ∃ n, f.use = origin N n := by
  obtain ⟨baseAdmitted, -⟩ := heldFiring_project admitted
  obtain ⟨notStart, notValue⟩ := no_bind_firing N rep plain baseAdmitted
  have rule : (toProgram f (heldFiring_member admitted)).rule = (heldState N P s).codeOf f.use := rfl
  have available := admitted.1.2.2.available
  rcases hu : f.use with c | i
  · rw [hu] at available rule
    have rule' : (toProgram f (heldFiring_member admitted)).rule = c := rule
    have inControl : c ∈ controlRules N := available
    have isStart : c ≠ bindStartRule N := fun same => notStart (rule'.trans same)
    have isValue : c ≠ bindValueRule N := fun same => notValue (rule'.trans same)
    rcases (mem_controlRules N).mp inControl with h | h | h | h | h | h
    · exact ⟨.ret, congrArg Use.ambient h⟩
    · exact ⟨.unmatched, congrArg Use.ambient h⟩
    · exact ⟨.left, congrArg Use.ambient h⟩
    · exact ⟨.right, congrArg Use.ambient h⟩
    · exact absurd h isStart
    · exact absurd h isValue
  · exact ⟨.eqn i, rfl⟩

variable (N) in
/-- **A named source move is a held firing by the name's origin**: a named move of a represented
alternative of the first fragment to a live child is a held firing by the name's origin, to any
fresh row, whose result represents the child. -/
theorem held_of_namedMove {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
    (plainP : PlainProgram P) {w w' : World κ Γ star} {b b' : Branch κ Γ star D.Ty} {n : RuleName}
    (move : NamedMove P w b n w' b') {s : HostState S} {a : ℕ} (rep : Represents N P w.scope b s a)
    (plain : PlainBranch b) (live : Solvable b'.store) {k : ℕ} (hk : k ∉ s.present) :
    ∃ s', HeldFires N P (origin N n) s a s' k ∧ Represents N P w'.scope b' s' k ∧ PlainBranch b' := by
  obtain ⟨s', fired, rep', plain'⟩ := simulation_named N plainP move rep plain live hk
  exact ⟨s', heldFires_of_firesNamed fired, rep', plain'⟩

variable (N) in
/-- **A held firing from a represented alternative is a named source move**: its origin is the origin
of a name, the alternative makes that name's move, and the result represents the move's child. -/
theorem namedMove_of_held {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
    (plainP : PlainProgram P) {w : World κ Γ star} {b : Branch κ Γ star D.Ty} {u : Use (CRule S) ℕ}
    {s s' : HostState S} {a a' : ℕ} (rep : Represents N P w.scope b s a) (plain : PlainBranch b)
    (fired : HeldFires N P u s a s' a') :
    ∃ (n : RuleName) (w' : World κ Γ star) (b' : Branch κ Γ star D.Ty), u = origin N n ∧
      NamedMove P w b n w' b' ∧ Represents N P w'.scope b' s' a' ∧ PlainBranch b' := by
  have copy := fired
  obtain ⟨f, use, admitted, -⟩ := copy
  obtain ⟨n, named⟩ := use_named N rep plain admitted
  have same : u = origin N n := use.symm.trans named
  subst same
  obtain ⟨w', b', move, rep', plain'⟩ := reflection_named N plainP rep plain (firesNamed_of_heldFires fired)
  exact ⟨n, w', b', rfl, move, rep', plain'⟩

end Firings

#print axioms offers
#print axioms heldStep_succ_iff
#print axioms heldStep_closed
#print axioms origin_injective
#print axioms origin_available
#print axioms ruleNamed_of_available
#print axioms heldFiring_project
#print axioms heldFires_firesAt
#print axioms heldFires_of_firesAt
#print axioms firesNamed_iff_heldFires
#print axioms use_named
#print axioms held_of_namedMove
#print axioms namedMove_of_held

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Counted
