import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# A candidate step in which the rules a firing may use are held by the state

Over a frame action (`Interface.Frames`) with its extensions, this module defines a **candidate** for
the step of the calculus: the state holds finitely many rule occurrences beside its rows, and a
firing fires a rule the state holds, or a rule of an ambient program.

## Two ways a rule is offered

* **A rule occurrence** is local and finite: it has an identity, it is held by the state
  (`RState.rules`, a finite set of identities, as the rows are), it is labelled by a held rule at the
  state's frame, it can be made by a firing, and it is taken by its own firing when it is linear.
* **The ambient program** (`ambient`, a set of codes, a parameter of the step) is static: it may be
  infinite, no firing changes it, and no query inspects it. It is to rules what the signature is to
  terms.

A firing names its **use** (`Use`): a code of the ambient program, or a held occurrence.

## Syntax

* **A code system** (`Codes`): what each code of a rule unfolds to (`Spec`), and which terms denote
  which codes at each frame (`denotes`; nothing, where rules are not terms). A spec has its own frame
  of unknowns and, at that frame, the body of a rule of the present step (take and read patterns,
  tells, checks, made rows: the tree's `RuleInstance`), collect patterns, **parameters**, **rule
  queries** (a zone and a pattern), the **rules it makes** (a code with arguments at the spec's frame,
  a mode and a zone: `Held`), the **rules it installs** (a term at the spec's frame, read as the
  code it denotes, with arguments, a mode and a zone: `Install`), the **rules it removes** (a zone
  and a term, read as the code it denotes), and the **rows it publishes** (a term, a mode and a zone:
  the made rule is the closed row of the term under the firing's information, `Codes.close`, with no
  arguments). A code may make any code, itself included: a code system is a coalgebra, not a
  well-founded tree.
* **A held rule** (`Held`) at a frame: a code, **arguments** at the frame (the rule's closure: each
  parameter is equated with its argument when the rule fires), a **mode** (`persistent`: kept when it
  fires; `linear`: taken when it fires) and a **zone**.
* **A state** (`RState`): a state of the present step (frame, knowledge, present rows, labels) and
  the rule occurrences it holds, each labelled by a held rule at the frame.
* **A firing** (`RFiring`): a use, an extension of the frame, an opening of the code's unknowns into
  the extended frame, a selection of rows, the seen set of each collect pattern, the identities of the
  rule occurrences it makes, the codes it installs, the rule occurrences it removes, and the codes of
  the closed rows it publishes.

## What is derived

* The firing **read as a firing of the present step** of the one rule its spec contains (`base`).
* **The information** (`information`): that of `base` (the knowledge carried along the extension, the
  take and read equations, the opened tells), then **the closure's equations** (`env`): each opened
  parameter with its argument carried along the extension.
* **Freshness** (`Fresh`): as in the present step, over the terms the state mentions, which now
  include the arguments of its held rules, and every term of the spec.
* **The shapes** (`Shapes`): freshness; those of the rows, as in the present step (`RowShapes`); and
  those of the rule occurrences (`RuleShapes`): the use is available (its code belongs to the ambient
  program, or its occurrence is held), one argument per parameter, one installed code per install,
  distinct made rule identities, one per made or installed rule, each new to the state; distinct
  removed occurrences, one per removal, each held in the zone the removal names.
* **The guard predicate** (`Holds`): that of `base`; every rule query (no held rule of the zone has a
  take pattern that an instantiation of its code's unknowns agreeing with its arguments equates with
  the opened pattern); every opened install term denoting its installed code; and every opened
  removal term denoting the code of the occurrence removed for it.
* **Admission** (`Admits`): the shapes, the enabling of the row selection, solvable information, and
  the guard predicate at every solution of the information.
* **The result** (`result`): the extended frame, the information as knowledge, the fired rows with
  made rows labelled by the opened made rows; the held rules less the used occurrence when it is
  linear and less the removed ones (`kept`), the made and installed occurrences labelled by the
  opened made and installed rules (`madeLabels`), and every other held rule carried along the
  extension.

`rstep X O R E codes ambient` is an `Interface.Step.Standard` whose admission is this derived
predicate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Syntax -/

/-- **How a held rule is used when it fires**: kept (`persistent`) or taken (`linear`). -/
inductive Mode where
  | persistent
  | linear
  deriving DecidableEq

/-- **A held rule at a frame**: a code, arguments at the frame (the closure: each parameter of the
code is equated with its argument when the rule fires), a mode and a zone. A rule that a code makes is
given in the same way at the frame of the code's unknowns. -/
structure Held (Tm : Obj → Type uT) (C : Type uC) (Z : Type uZ) (a : Obj) where
  code : C
  args : List (Tm a)
  mode : Mode
  zone : Z

/-- **A rule installed from a term**: a term at a frame, read as the code it denotes, with arguments
at that frame, a mode and a zone. -/
structure Install (Tm : Obj → Type uT) (Z : Type uZ) (a : Obj) where
  term : Tm a
  args : List (Tm a)
  mode : Mode
  zone : Z

/-- **What a code unfolds to**: its own frame of unknowns and, at that frame, the body of a rule
(the tree's `RuleInstance`), collect patterns, parameters, rule queries (a zone and a pattern: no held
rule of the zone could take a row of the pattern), the rules it makes, the rules it installs, and the
rules it removes (a zone and a term: one held rule of the zone whose code the term denotes). -/
structure Spec (Tm : Obj → Type uT) (C : Type uC) (Z : Type uZ) where
  locals : Obj
  body : RuleInstance (Tm locals)
  collect : List (Tm locals)
  params : List (Tm locals)
  unmatched : List (Z × Tm locals)
  makes : List (Held Tm C Z locals)
  installs : List (Install Tm Z locals)
  removes : List (Z × Tm locals)
  publishes : List (Tm locals × Mode × Z)

/-- **A code system**: what each code unfolds to, which terms denote which codes at each frame, and
the code of the **closed row** of a term under a knowledge at a frame, where the system has one
(`close`): the rule whose unknowns are that frame, that tells that knowledge and makes that term. A
code may make any code, itself included. -/
structure Codes (Tm : Obj → Type uT) (C : Type uC) (Z : Type uZ) where
  unfold : C → Spec Tm C Z
  denotes : (b : Obj) → Tm b → C → Prop
  close : (a : Obj) → EquationStore (Tm a) → Tm a → Option C

namespace Spec

variable {C : Type uC} {Z : Type uZ}

/-- The rule of the present step that a spec contains: its frame, its body and its collect query. -/
abbrev toRule (sp : Spec Tm C Z) : Rule Tm := ⟨sp.locals, sp.body, sp.collect⟩

/-- **The spec of a rule of the present step**: no parameters, no rule queries, no made, installed or
removed rules. -/
abbrev ofRule (r : Rule Tm) : Spec Tm C Z := ⟨r.locals, r.body, r.collect, [], [], [], [], [], []⟩

/-- **The closed row** of a term under a knowledge at a frame, as a rule of the present step: its
unknowns are the frame, it tells the knowledge and makes the term. -/
abbrev closedRow (a : Obj) (knowledge : EquationStore (Tm a)) (t : Tm a) : Rule Tm :=
  ⟨a, ⟨[], [], knowledge, [], [t]⟩, []⟩

theorem toRule_ofRule (r : Rule Tm) : (ofRule r : Spec Tm C Z).toRule = r := rfl

/-- Every term of a spec: the terms of its rule, its parameters, its rule-query patterns, the
arguments of the rules it makes, the terms and arguments of the rules it installs, and the terms of
the rules it removes. -/
def terms (sp : Spec Tm C Z) : List (Tm sp.locals) :=
  sp.toRule.terms ++ (sp.params ++ sp.unmatched.map Prod.snd ++ sp.makes.flatMap Held.args ++
    sp.installs.map Install.term ++ sp.installs.flatMap Install.args ++ sp.removes.map Prod.snd ++
    sp.publishes.map Prod.fst)

/-- **A plain spec**: no parameters, no rule queries, no installed or removed rules, and the rules
it makes have no arguments. Its terms are those of its rule. -/
structure Plain (sp : Spec Tm C Z) : Prop where
  params : sp.params = []
  unmatched : sp.unmatched = []
  installs : sp.installs = []
  makes : ∀ h ∈ sp.makes, h.args = []
  removes : sp.removes = []
  publishes : sp.publishes = []

theorem terms_of_plain {sp : Spec Tm C Z} (plain : sp.Plain) : sp.terms = sp.toRule.terms := by
  have none : sp.makes.flatMap Held.args = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    exact plain.makes
  unfold terms
  rw [plain.params, plain.unmatched, plain.installs, plain.removes, plain.publishes, none]
  simp

theorem plain_ofRule (r : Rule Tm) : (ofRule r : Spec Tm C Z).Plain :=
  ⟨rfl, rfl, rfl, fun _ inside => absurd inside List.not_mem_nil, rfl, rfl⟩

end Spec

/-- **A held rule carried along a morphism of frames**: its arguments are acted on. -/
def Held.act (X : Frames Tm Hom) {C : Type uC} {Z : Type uZ} {a b : Obj} (w : Hom a b)
    (h : Held Tm C Z a) : Held Tm C Z b :=
  ⟨h.code, h.args.map (X.act w), h.mode, h.zone⟩

/-- **A state that holds rules**: a state of the present step and the finitely many rule occurrences
it holds, each labelled by a held rule at the frame. -/
structure RState (Tm : Obj → Type uT) (O : Type uOcc) (R : Type uR) (C : Type uC) (Z : Type uZ)
    extends State Tm O where
  rules : Finset R
  held : R → Held Tm C Z frame

/-- **What a firing uses**: a code of the ambient program, or a rule occurrence the state holds. -/
inductive Use (C : Type uC) (R : Type uR) where
  | ambient (code : C)
  | held (occurrence : R)

namespace RState

variable {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}

/-- The code a use fires. -/
def codeOf (s : RState Tm O R C Z) : Use C R → C
  | .ambient c => c
  | .held ρ => (s.held ρ).code

/-- The arguments of a use: those of the held rule; a rule of the ambient program has none. -/
def argsOf (s : RState Tm O R C Z) : Use C R → List (Tm s.frame)
  | .ambient _ => []
  | .held ρ => (s.held ρ).args

/-- **A use is available**: its code belongs to the ambient program, or its occurrence is held. -/
def Available (s : RState Tm O R C Z) (ambient : Set C) : Use C R → Prop
  | .ambient c => c ∈ ambient
  | .held ρ => ρ ∈ s.rules

/-- The terms a state mentions: its knowledge, the labels of its present rows, and the arguments of
the rules it holds. -/
def Mentions (s : RState Tm O R C Z) (t : Tm s.frame) : Prop :=
  s.toState.Mentions t ∨ ∃ ρ ∈ s.rules, t ∈ (s.held ρ).args

/-- **A closed state**: no held rule has arguments. It mentions what its rows and knowledge do. -/
def Closed (s : RState Tm O R C Z) : Prop := ∀ ρ ∈ s.rules, (s.held ρ).args = []

theorem mentions_of_closed {s : RState Tm O R C Z} (closed : s.Closed) (t : Tm s.frame) :
    s.Mentions t ↔ s.toState.Mentions t := by
  constructor
  · rintro (inside | ⟨ρ, held, member⟩)
    · exact inside
    · rw [closed ρ held] at member
      exact absurd member List.not_mem_nil
  · intro inside
    exact Or.inl inside

theorem argsOf_of_closed {s : RState Tm O R C Z} (closed : s.Closed) {ambient : Set C} {u : Use C R}
    (available : s.Available ambient u) : s.argsOf u = [] := by
  cases u with
  | ambient c => rfl
  | held ρ => exact closed ρ available

end RState

/-- **A firing**: what it uses, an extension of the frame, an opening of the code's unknowns into the
extended frame, a selection of rows, the rows each collect pattern claims to see, the identities of
the rule occurrences it makes and installs, the codes it installs, and the rule occurrences it
removes. -/
structure RFiring (O : Type uOcc) (R : Type uR) {C : Type uC} {Z : Type uZ}
    (E : Extensions.{uO, uH, uE} Hom) (codes : Codes Tm C Z) (s : RState Tm O R C Z) where
  use : Use C R
  ext : E.Ext s.frame
  opening : Hom (codes.unfold (s.codeOf use)).locals (E.target ext)
  selection : Selection O
  seen : List (Finset O)
  madeRules : List R
  installed : List C
  removedRules : List R
  published : List C

/-- Assign values to the listed identities, in order; every other identity keeps its old value. -/
def assign {ι : Type*} {β : Type*} [DecidableEq ι] (old : ι → β) : List ι → List β → ι → β
  | i :: is, v :: vs, j => if j = i then v else assign old is vs j
  | _, _, j => old j

theorem assign_of_not_mem {ι : Type*} {β : Type*} [DecidableEq ι] (old : ι → β) :
    ∀ (is : List ι) (vs : List β) {j : ι}, j ∉ is → assign old is vs j = old j
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | i :: rest, v :: vs, j, absent => by
      have other : j ≠ i := fun same => absent (List.mem_cons.mpr (Or.inl same))
      have later : j ∉ rest := fun inside => absent (List.mem_cons.mpr (Or.inr inside))
      simp only [assign, if_neg other]
      exact assign_of_not_mem old rest vs later

theorem assign_zip {ι : Type*} {β : Type*} [DecidableEq ι] (old : ι → β) :
    ∀ (is : List ι) (vs : List β), is.Nodup → is.length = vs.length →
      ∀ x ∈ is.zip vs, assign old is vs x.1 = x.2
  | [], _, _, _, _, inside => by simp at inside
  | _ :: _, [], _, lengths, _, _ => by simp at lengths
  | i :: rest, v :: vs, nodup, lengths, x, inside => by
      rcases List.mem_cons.mp inside with first | later
      · subst first
        simp [assign]
      · have notHead : x.1 ≠ i := by
          intro same
          have inRest : x.1 ∈ rest := (List.of_mem_zip later).1
          exact (List.nodup_cons.mp nodup).1 (same ▸ inRest)
        simp only [assign, if_neg notHead]
        exact assign_zip old rest vs (List.nodup_cons.mp nodup).2 (Nat.succ.inj lengths) x later

namespace RFiring

variable (X : Frames Tm Hom) {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {s : RState Tm O R C Z}
  (f : RFiring O R E codes s)

/-- The spec of the rule it fires. -/
abbrev spec : Spec Tm C Z := codes.unfold (s.codeOf f.use)

/-- **The firing read as a firing of the present step** of the one rule its spec contains. -/
abbrev base : Firing O E ({f.spec.toRule} : Program Tm) s.frame :=
  ⟨f.spec.toRule, Set.mem_singleton _, f.ext, f.opening, f.selection, f.seen⟩

/-- **The closure's equations**: each opened parameter with its argument, carried along the
extension. -/
def env : EquationStore (Tm (E.target f.ext)) :=
  (f.spec.params.map (X.act f.opening)).zip ((s.argsOf f.use).map (X.act (E.weaken f.ext)))

/-- **The information**: that of the firing read in the present step, then the closure's equations. -/
def information : EquationStore (Tm (E.target f.ext)) :=
  (f.base.information X s.toState : EquationStore (Tm (E.target f.ext))) ++ f.env X

/-- **Freshness of the opening**: every instantiation of the state's frame and every instantiation of
the code's unknowns are realized by one instantiation of the extended frame, on what the state
mentions and on the spec's terms. -/
def Fresh : Prop :=
  ∀ (b : Obj) (g : Hom s.frame b) (h : Hom f.spec.locals b), ∃ u : Hom (E.target f.ext) b,
    (∀ t, s.Mentions t → X.E (X.act u (X.act (E.weaken f.ext) t)) (X.act g t)) ∧
      ∀ t ∈ f.spec.terms, X.E (X.act u (X.act f.opening t)) (X.act h t)

/-- **The shapes of the rows**, as in the present step: distinct takes and made rows, one row per
pattern, one made row per made identity, one seen set per collect pattern. -/
def RowShapes : Prop :=
  f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
    f.spec.body.take.length = f.selection.taken.length ∧
    f.spec.body.read.length = f.selection.read.length ∧
    f.spec.body.produce.length = f.selection.made.length ∧
    f.spec.collect.length = f.seen.length

/-- **The shapes of the rule occurrences**: the use is available, one argument per parameter, one
installed code per install, distinct made rule identities, one per made or installed rule, each new
to the state; distinct removed occurrences, one per removal, each held in the zone its removal
names. -/
structure RuleShapes (ambient : Set C) : Prop where
  available : s.Available ambient f.use
  arguments : f.spec.params.length = (s.argsOf f.use).length
  installed : f.installed.length = f.spec.installs.length
  madeNodup : f.madeRules.Nodup
  madeLength :
    f.spec.makes.length + f.spec.installs.length + f.spec.publishes.length = f.madeRules.length
  madeNew : ∀ ρ ∈ f.madeRules, ρ ∉ s.rules
  removed : f.removedRules.length = f.spec.removes.length
  removedNodup : f.removedRules.Nodup
  removedHeld : ∀ x ∈ f.spec.removes.zip f.removedRules, x.2 ∈ s.rules ∧ (s.held x.2).zone = x.1.1
  published : f.published.length = f.spec.publishes.length

/-- **The shapes**: a fresh opening, the shapes of the rows and those of the rule occurrences. -/
def Shapes (ambient : Set C) : Prop :=
  f.Fresh X ∧ f.RowShapes ∧ f.RuleShapes ambient

/-- **A rule query at a solution**: no held rule of the zone has a take pattern that an instantiation
of its code's unknowns, agreeing with its arguments, equates with the opened pattern. -/
def unmatchedHolds {b : Obj} (σ : Hom (E.target f.ext) b) (q : Z × Tm f.spec.locals) : Prop :=
  ∀ ρ ∈ s.rules, (s.held ρ).zone = q.1 → ∀ p ∈ (codes.unfold (s.held ρ).code).body.take,
    ∀ h : Hom (codes.unfold (s.held ρ).code).locals b,
      (∀ e ∈ (codes.unfold (s.held ρ).code).params.zip (s.held ρ).args,
        X.E (X.act h e.1) (X.act σ (X.act (E.weaken f.ext) e.2))) →
      ¬ X.E (X.act σ (X.act f.opening q.2)) (X.act h p)

/-- **The guard predicate at a solution**: that of the firing read in the present step, every rule
query, every opened install term denoting its installed code, every opened removal term denoting
the code of the occurrence removed for it, and every published code being the closed row of its
opened term under the firing's information. -/
def Holds {b : Obj} (σ : Hom (E.target f.ext) b) : Prop :=
  f.base.Holds X s.toState σ ∧ (∀ q ∈ f.spec.unmatched, f.unmatchedHolds X σ q) ∧
    (∀ x ∈ f.spec.installs.zip f.installed,
      codes.denotes b (X.act σ (X.act f.opening x.1.term)) x.2) ∧
    (∀ x ∈ f.spec.removes.zip f.removedRules,
      codes.denotes b (X.act σ (X.act f.opening x.1.2)) (s.held x.2).code) ∧
    ∀ x ∈ f.spec.publishes.zip f.published,
      codes.close (E.target f.ext) (f.information X) (X.act f.opening x.1.1) = some x.2

/-- The labels of the made, installed and published rule occurrences: the opened made rules, then
each installed code with its opened arguments, then each published code, without arguments. -/
def madeLabels : List (Held Tm C Z (E.target f.ext)) :=
  f.spec.makes.map (Held.act X f.opening) ++
    ((f.spec.installs.zip f.installed).map fun x =>
      ⟨x.2, x.1.args.map (X.act f.opening), x.1.mode, x.1.zone⟩) ++
    (f.spec.publishes.zip f.published).map fun x => ⟨x.2, [], x.1.2.1, x.1.2.2⟩

/-- The held rules the use leaves: all of them, less the used occurrence when it is linear. -/
def left [DecidableEq R] : Finset R :=
  match f.use with
  | .ambient _ => s.rules
  | .held ρ => if (s.held ρ).mode = Mode.linear then s.rules.erase ρ else s.rules

/-- **The held rules kept**: those the use leaves, less the removed ones. -/
def kept [DecidableEq R] : Finset R := f.left \ f.removedRules.toFinset

variable [DecidableEq O]

/-- **Admission, derived**: the shapes, the enabling of the row selection, solvable information, and
the guard predicate at every solution of the information. -/
def Admits (ambient : Set C) : Prop :=
  f.Shapes X ambient ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X) ∧ X.Entails (f.information X) (fun _ σ => f.Holds X σ)

variable [DecidableEq R]

/-- **The result**: the extended frame, the information as knowledge, the fired rows with the made rows
labelled by the opened made rows, and the held rules kept with the made and installed rule
occurrences labelled by their rules; every other held rule is carried along the extension. -/
def result : RState Tm O R C Z where
  frame := E.target f.ext
  knowledge := f.information X
  present := fire s.present (f.selection.commit (T := Unit))
  label := relabel (f.base.row X s.toState) f.selection.made (f.base.opened X).produce
  rules := f.kept ∪ f.madeRules.toFinset
  held := assign (fun ρ => (s.held ρ).act X (E.weaken f.ext)) f.madeRules (f.madeLabels X)

end RFiring

/-! ## The step -/

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (R : Type uR) [DecidableEq R]
  (E : Extensions.{uO, uH, uE} Hom) {C : Type uC} {Z : Type uZ} (codes : Codes Tm C Z)
  (ambient : Set C)

/-- **The step of the rules a state holds, beside an ambient program** (a candidate). Its admission
is `RFiring.Admits`, computed from the used rule, the opening and the selection. -/
def rstep : Interface.Step.Standard X O (RState Tm O R C Z) (fun s => RFiring O R E codes s) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := E.target f.ext
  extension f := E.weaken f.ext
  information f := f.information X
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨e, member, rfl⟩))))
  Shapes f := f.Shapes X ambient
  Holds f _ σ := f.Holds X σ
  Admits f := f.Admits X ambient
  admits_iff _ := Iff.rfl
  preparedResult f _ := f.result X
  present_preparedResult _ _ := rfl
  preparedSettle f _ := X.id (E.target f.ext)
  knowledge_preparedResult f _ := (Frames.applyStore_id (X := X) (f.information X)).symm

variable {X O R E codes ambient}

theorem rstep_admits_iff {s : RState Tm O R C Z} (f : RFiring O R E codes s) :
    (rstep X O R E codes ambient).Admits f ↔ f.Admits X ambient :=
  Iff.rfl

theorem rstep_result {s : RState Tm O R C Z} (f : RFiring O R E codes s)
    (admitted : (rstep X O R E codes ambient).Admits f) :
    (rstep X O R E codes ambient).result f admitted = f.result X :=
  rfl

/-! ## The held rules of a result -/

namespace RFiring

variable {s : RState Tm O R C Z} (f : RFiring O R E codes s)

/-- **What the result holds**: the held rules kept, and the made and installed ones. -/
theorem mem_result_rules {ρ : R} :
    ρ ∈ (f.result X).rules ↔ ρ ∈ f.kept ∨ ρ ∈ f.madeRules := by
  show ρ ∈ f.kept ∪ f.madeRules.toFinset ↔ _
  rw [Finset.mem_union, List.mem_toFinset]

omit [DecidableEq O] in
/-- A firing that removes no rule keeps what its use leaves. -/
theorem kept_of_none (none : f.removedRules = []) : f.kept = f.left := by
  unfold kept
  rw [none, List.toFinset_nil, Finset.sdiff_empty]

omit [DecidableEq O] in
/-- Firing a rule of the ambient program, and removing none, takes no held rule. -/
theorem kept_ambient {c : C} (ambientUse : f.use = Use.ambient c) (none : f.removedRules = []) :
    f.kept = s.rules := by
  rw [f.kept_of_none none]
  unfold left
  rw [ambientUse]

omit [DecidableEq O] in
/-- A persistent rule is kept when it fires and removes none. -/
theorem kept_persistent {ρ : R} (heldUse : f.use = Use.held ρ)
    (persistent : (s.held ρ).mode = Mode.persistent) (none : f.removedRules = []) :
    f.kept = s.rules := by
  rw [f.kept_of_none none]
  unfold left
  rw [heldUse]
  show (if (s.held ρ).mode = Mode.linear then s.rules.erase ρ else s.rules) = s.rules
  rw [persistent]
  exact if_neg (by decide)

omit [DecidableEq O] in
/-- A linear rule is taken when it fires. -/
theorem kept_linear {ρ : R} (heldUse : f.use = Use.held ρ)
    (linear : (s.held ρ).mode = Mode.linear) (none : f.removedRules = []) :
    f.kept = s.rules.erase ρ := by
  rw [f.kept_of_none none]
  unfold left
  rw [heldUse]
  exact if_pos linear

omit [DecidableEq O] in
/-- The use leaves only held rules. -/
theorem left_subset : f.left ⊆ s.rules := by
  unfold left
  cases f.use with
  | ambient c => exact Finset.Subset.refl _
  | held ρ =>
      show (if (s.held ρ).mode = Mode.linear then s.rules.erase ρ else s.rules) ⊆ s.rules
      split
      · exact Finset.erase_subset _ _
      · exact Finset.Subset.refl _

omit [DecidableEq O] in
/-- Every kept rule was held. -/
theorem kept_subset : f.kept ⊆ s.rules :=
  fun _ inside => f.left_subset (Finset.mem_sdiff.mp inside).1

omit [DecidableEq O] [DecidableEq R] in
/-- One label per made or installed identity. -/
theorem length_madeLabels (shapes : f.RuleShapes ambient) :
    (f.madeLabels X).length = f.madeRules.length := by
  unfold madeLabels
  rw [List.length_append, List.length_append, List.length_map, List.length_map, List.length_map,
    List.length_zip, List.length_zip, shapes.installed, shapes.published, Nat.min_self, Nat.min_self]
  exact shapes.madeLength

/-- **A made or installed rule occurrence holds its label.** -/
theorem result_held_made (shapes : f.RuleShapes ambient) {x : R × Held Tm C Z (E.target f.ext)}
    (inside : x ∈ f.madeRules.zip (f.madeLabels X)) :
    (f.result X).held x.1 = x.2 :=
  assign_zip _ f.madeRules _ shapes.madeNodup (f.length_madeLabels shapes).symm x inside

/-- **Every other held rule is carried along the extension.** -/
theorem result_held_other {ρ : R} (absent : ρ ∉ f.madeRules) :
    (f.result X).held ρ = (s.held ρ).act X (E.weaken f.ext) :=
  assign_of_not_mem _ f.madeRules _ absent

end RFiring

#print axioms rstep
#print axioms rstep_admits_iff
#print axioms Spec.terms_of_plain
#print axioms RState.mentions_of_closed
#print axioms RState.argsOf_of_closed
#print axioms assign_zip
#print axioms RFiring.mem_result_rules
#print axioms RFiring.kept_of_none
#print axioms RFiring.kept_ambient
#print axioms RFiring.kept_persistent
#print axioms RFiring.kept_linear
#print axioms RFiring.kept_subset
#print axioms RFiring.length_madeLabels
#print axioms RFiring.result_held_made
#print axioms RFiring.result_held_other

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
