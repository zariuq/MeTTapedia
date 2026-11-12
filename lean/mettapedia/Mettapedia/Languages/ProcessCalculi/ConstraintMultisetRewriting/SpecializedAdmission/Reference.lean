import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Language

/-!
# Rule schemas and the step's admission of their instances

A **rule** is a firing schema: its locals `0 .. nparams - 1` are its parameters (ground terms given
at each decision), its other locals are the firing's fresh variables, `fresh j` is the `j`-th name
it mints; its takes and reads select occurrences that each decision names (`Ctx.occs`: the takes'
identities, then the reads'); its makes ask for fresh identities.

The **instance** of a rule at a state, with parameters `p` and identities `o`, is decided by the
characterization of admission (`Interface.Step.Standard.admits_iff`), with the conjuncts grouped
as the reference implementation groups them:

* `Shapes`: every opened term is a term of the target frame (its names minted, its fresh names
  among the firing's own, its variables declared, its parameters' names minted), and the takes'
  identities are not `0` and pairwise distinct;
* `Fits`: every selected occurrence is present, and nothing is both taken and read
  (`OccurrenceCommits.Enabled`; made identities are fresh by construction);
* `Solvable`: the information has a solution `σ`: the parameters, each pattern equal to the label
  it selects, each tell;
* `Entails`: each guard holds at **every** solution (`Frames.Entails`).

`Verdict` names the first conjunct that fails (`RefVerdict`). `Result` is the state an admitted
firing leaves: the takes leave, the makes arrive with the next identities, at their values at a
solution (every solution, for a rule whose makes the information determines), and the names are
minted. Solutions are quantified, never computed: the statement names no unification algorithm.
States here are first-order states of the ground fragment: their labels are closed terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission

/-- Guards: an ask, an absence, a count, or a host predicate (whose meaning the host gives). -/
inductive Guard where
  | ask (a b : Tm)
  | absent (p : Tm)
  | count (p : Tm) (n : Nat)
  | host (name : String) (args : List Tm)

/-- A firing schema. -/
structure Rule where
  nparams : Nat
  fresh : Nat
  takes : List Tm
  reads : List Tm
  makes : List Tm
  tells : List (Tm × Tm)
  aparts : List (Tm × Tm)
  guards : List Guard

/-- The terms of a guard that the firing opens at its target frame; a host is handed its terms as
written. -/
def Guard.opened : Guard → List Tm
  | .ask a b => [a, b]
  | .absent p => [p]
  | .count p _ => [p]
  | .host _ _ => []

namespace Rule

/-- The patterns of the uses: the takes, then the reads. -/
def uses (R : Rule) : List Tm := R.takes ++ R.reads

/-- Every term the firing opens at its target frame. -/
def opened (R : Rule) : List Tm :=
  R.takes ++ R.reads ++ R.makes ++ R.tells.flatMap (fun e => [e.1, e.2]) ++
    R.aparts.flatMap (fun e => [e.1, e.2]) ++ R.guards.flatMap Guard.opened

end Rule

/-- Fresh names opened at a frame that has minted `b` names. -/
def openFresh (b : Nat) : Nat → Tm := fun j => .name (b + j)

section Reference

variable (R : Rule) (s : St) (p : List Tm) (o : List Nat)

/-- An atom of an opened term belongs to the target frame. -/
def AtomAtFrame (a : Tm) : Prop :=
  match a with
  | .name m => m < s.names
  | .fresh j => j < R.fresh
  | .var i => i < s.vars
  | .loc k => k < R.nparams → (p.getD k default).minted s.names = true
  | .code _ => True
  | .app _ _ => True

def Shapes : Prop :=
  (∀ t ∈ R.opened, ∀ a ∈ t.atoms, AtomAtFrame R s p a) ∧
  (∀ u < R.takes.length, o.getD u 0 ≠ 0) ∧
  (∀ u < R.takes.length, ∀ v < u, o.getD u 0 ≠ o.getD v 0)

def Fits : Prop :=
  (∀ u < R.uses.length, (labelOf s (o.getD u 0)).isSome = true) ∧
  (∀ u < R.uses.length, R.takes.length ≤ u → ∀ v < R.takes.length, o.getD u 0 ≠ o.getD v 0)

/-- `σ` solves the information: the parameters, every use, every tell. -/
def Sol (σ : Nat → Tm) : Prop :=
  (∀ k < R.nparams, σ k = p.getD k default) ∧
  (∀ u < R.uses.length,
    labelOf s (o.getD u 0) = some ((R.uses.getD u default).inst σ (openFresh s.names))) ∧
  (∀ e ∈ R.tells, e.1.inst σ (openFresh s.names) = e.2.inst σ (openFresh s.names))

def Solvable : Prop := ∃ σ, Sol R s p o σ

/-- A guard at one solution. -/
def Guard.Holds (host : String → List Tm → Prop) (s : St) (σ : Nat → Tm) : Guard → Prop
  | .ask a b => a.inst σ (openFresh s.names) = b.inst σ (openFresh s.names)
  | .absent q => ∀ row ∈ s.present, row.label ≠ q.inst σ (openFresh s.names)
  | .count q n =>
      (s.present.filter fun row => decide (row.label = q.inst σ (openFresh s.names))).length = n
  | .host h args => host h (args.map (Tm.inst σ (openFresh s.names)))

/-- A guard holds at every solution of the information. -/
def Entails (host : String → List Tm → Prop) (g : Guard) : Prop :=
  ∀ σ, Sol R s p o σ → g.Holds host s σ

def Admits (host : String → List Tm → Prop) : Prop :=
  Shapes R s p o ∧ Fits R s o ∧ Solvable R s p o ∧ ∀ g ∈ R.guards, Entails R s p o host g

/-- The verdict of the step: admitted, or the first conjunct that fails. -/
def RefVerdict (host : String → List Tm → Prop) : Verdict → Prop
  | .refused .shapes => ¬ Shapes R s p o
  | .refused .fits => Shapes R s p o ∧ ¬ Fits R s o
  | .refused .unsolvable => Shapes R s p o ∧ Fits R s o ∧ ¬ Solvable R s p o
  | .refused (.guard i) => Shapes R s p o ∧ Fits R s o ∧ Solvable R s p o ∧
      ∃ g, R.guards[i]? = some g ∧ ¬ Entails R s p o host g ∧
        ∀ j < i, ∀ g', R.guards[j]? = some g' → Entails R s p o host g'
  | .admitted => Admits R s p o host

/-- Rows labelled by `ts`, with identities from `start` on. -/
def madeRows : Nat → List Tm → List Row
  | _, [] => []
  | start, t :: ts => ⟨start, t⟩ :: madeRows (start + 1) ts

/-- The identities the takes select. -/
def takenIds : List Nat := (List.range R.takes.length).map fun u => o.getD u 0

/-- The state an admitted firing leaves, written at the solution `σ`. -/
def Result (σ : Nat → Tm) : St :=
  { s with
    names := s.names + R.fresh
    nextId := s.nextId + R.makes.length
    present := s.present.filter (fun row => (takenIds R o).all fun id => row.id != id) ++
      madeRows s.nextId (R.makes.map (Tm.inst σ (openFresh s.names))) }

end Reference

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission
