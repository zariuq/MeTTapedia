import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullRace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullIndependenceControls

/-!
# Firings at different spaces are independent, in the interface's sense

The interface's independence notion is `Transport.Independent`: both firings admitted, each residual
admitted after the other, and the composites in one state class. Where diamonds close
(`Transport.Closes`) it is the four admissions (`Transport.independent_iff_admits`). This module
proves, for the first-order and the dependent full step, that **two admitted firings at different
spaces, the first of which adds no information, are independent in that sense**.

## The first-order step with located occurrences (`located_independent`)

Its independence notion is `firstOrderTransport`, whose diamonds close (`firstOrder_closes`).
`Spaces.independent` is the residual law, with its exact `quiet` hypothesis: a firing at `a` that
adds no information leaves the admission of a firing at `b ≠ a` as it was. Applied in both orders,
it gives independence (`located_independent`, both firings quiet), and its one-sided form is the
residual law of the transport (`located_residual_iff`). For static firings it is the run layer's
static independence (`located_static_independent`).

**The bridge** (`quiet_of_exact`, `exact_independent`): a firing whose take and read patterns are its
rows' own labels and whose tells have equal sides is quiet, a syntactic condition a program checks.
The quiet read of `Spaces.Controls` is exact, and the binding read `p(X)` is not
(`Controls.quiet_read_exact`).

## The dependent full step (`dependent_independent`)

Its independence notion is `plainTransport` on firings without helpers (`DependentFullRace`), whose
diamonds close (`plain_closes`) and which R93's clauses imply (`independent_of_clauses`).
* **Spaces give the resource clauses**: firings that take, read and make only at their own spaces
  (`PlainAt`), at different spaces, take apart, take none of each other's reads, and make different
  occurrences.
* **The first firing's quietness gives the joint clause**: if its information has the solutions of
  the knowledge, the joint information has the solutions of the second firing's information, which
  is solvable.
* **Queries are not located at dependent frames.** A predicate query there is a region of labels,
  and dependent labels carry no space handle, so the two "unwritten" clauses stay hypotheses
  (`dependent_independent`); without queries they hold (`dependent_independent_of_no_queries`).

## Information crosses spaces (`Controls.dependent_shared_variable_crosses_spaces`)

The control `Spaces.Controls.shared_variable_crosses_spaces`, at dependent frames: telling `X ≐ Ground`
and telling `X ≐ Ground → Ground` are each admitted, at any two spaces, and the second is refused
after the first. The `quiet` hypothesis is needed there too.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpacesInterface

open Interface (Frames Transport)
open Spaces (At located label)

/-! ## The first-order step with located occurrences -/

section FirstOrder

universe uT uS uH uO

variable {T : Type uT} {S : Type uS} {H : Type uH} {O : Type uO} [DecidableEq O] [DecidableEq H]
  (A : SubstitutionAction T S) (space : O → H) (payload : O → T)

/-- The independence notion of the located first-order step. -/
abbrev transport :=
  AnnotatedRuns.firstOrderTransport (LocatedSubstitution.action (N := H) A) (label space payload)

/-- **The residual law of spaces** in the transport's terms: a residual of a firing at `b` after a quiet
firing at `a ≠ b` is admitted exactly when the firing is. It is `Spaces.independent`, with its exact
`quiet` hypothesis. -/
theorem located_residual_iff {C : Configuration (H × T) O} {f g : AnnotatedRuns.Firing (H × T) S O}
    {a b : H} (different : a ≠ b) (atF : At a f) (atG : At b g)
    (admittedF : (located A space payload).Admits (s := C) f)
    (quiet : (LocatedSubstitution.action (N := H) A).Equivalent
      (f.selection.problem (label space payload) f.rule C) C.equations)
    (distinct : ∀ o ∈ g.selection.made, o ∉ f.selection.made) :
    (located A space payload).Admits (s := (located A space payload).result f admittedF)
        ((transport A space payload).residual f admittedF g) ↔
      (located A space payload).Admits (s := C) g :=
  (Spaces.independent A space payload different atF atG admittedF quiet distinct).symm

/-- **Firings at different spaces that add no information are independent**, in the interface's
sense, at the located first-order step. -/
theorem located_independent {C : Configuration (H × T) O} {f g : AnnotatedRuns.Firing (H × T) S O}
    {a b : H} (different : a ≠ b) (atF : At a f) (atG : At b g)
    (admittedF : (located A space payload).Admits (s := C) f)
    (admittedG : (located A space payload).Admits (s := C) g)
    (quietF : (LocatedSubstitution.action (N := H) A).Equivalent
      (f.selection.problem (label space payload) f.rule C) C.equations)
    (quietG : (LocatedSubstitution.action (N := H) A).Equivalent
      (g.selection.problem (label space payload) g.rule C) C.equations)
    (distinct : ∀ o ∈ g.selection.made, o ∉ f.selection.made) :
    (transport A space payload).Independent C f g :=
  (AnnotatedRuns.firstOrder_independent_iff _ _).mpr ⟨admittedF, admittedG,
    (Spaces.independent A space payload different atF atG admittedF quietF distinct).mp admittedG,
    (Spaces.independent A space payload (Ne.symm different) atG atF admittedG quietG
      (fun o made other => distinct o other made)).mp admittedF⟩

/-- **And statically independent**, for static firings: the run layer's static independence. -/
theorem located_static_independent {C : Configuration (H × T) O} {f g : AnnotatedRuns.Firing (H × T) S O}
    {a b : H} (different : a ≠ b) (atF : At a f) (atG : At b g)
    (fStatic : f.Static) (gStatic : g.Static)
    (admittedF : (located A space payload).Admits (s := C) f)
    (admittedG : (located A space payload).Admits (s := C) g)
    (quietF : (LocatedSubstitution.action (N := H) A).Equivalent
      (f.selection.problem (label space payload) f.rule C) C.equations)
    (quietG : (LocatedSubstitution.action (N := H) A).Equivalent
      (g.selection.problem (label space payload) g.rule C) C.equations)
    (distinct : ∀ o ∈ g.selection.made, o ∉ f.selection.made) :
    AnnotatedRuns.StaticIndependent (label space payload) f g :=
  (AnnotatedRuns.firstOrder_independent_iff_static _ _ fStatic gStatic admittedF
    ((Spaces.independent A space payload different atF atG admittedF quietF distinct).mp admittedG)).mp
    (located_independent A space payload different atF atG admittedF admittedG quietF quietG distinct)

/-! ### The bridge: exact firings are quiet -/

omit [DecidableEq O] [DecidableEq H] in
/-- The equations of patterns that are their rows' own labels are reflexive. -/
theorem equations_exact {L' : Type uT} {U : Type uO} (lab : U → L') :
    ∀ (selected : List U), ∀ e ∈ Selection.equations lab (selected.map lab) selected, e.1 = e.2
  | [], _, member => absurd member List.not_mem_nil
  | o :: rest, e, member => by
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact equations_exact lab rest e later

omit [DecidableEq O] [DecidableEq H] in
/-- **An exact firing adds no information**: a firing whose take and read patterns are its rows' own
labels and whose tells have equal sides satisfies `quiet`. This is a syntactic condition a program
can check. -/
theorem quiet_of_exact {C : Configuration (H × T) O} {f : AnnotatedRuns.Firing (H × T) S O}
    (takes : f.rule.take = f.selection.taken.map (label space payload))
    (reads : f.rule.read = f.selection.read.map (label space payload))
    (tells : ∀ e ∈ f.rule.tell, e.1 = e.2) :
    (LocatedSubstitution.action (N := H) A).Equivalent
      (f.selection.problem (label space payload) f.rule C) C.equations := by
  intro σ
  have reflexive : ∀ e ∈ Selection.equations (label space payload) f.rule.take f.selection.taken ++
      Selection.equations (label space payload) f.rule.read f.selection.read ++ f.rule.tell, e.1 = e.2 := by
    intro e member
    rcases List.mem_append.mp member with front | told
    · rcases List.mem_append.mp front with taken | read
      · rw [takes] at taken
        exact equations_exact _ _ e taken
      · rw [reads] at read
        exact equations_exact _ _ e read
    · exact tells e told
  constructor
  · intro solved e member
    exact solved e (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))
  · intro solved e member
    simp only [Selection.problem, List.mem_append] at member
    rcases member with ((known | taken) | read) | told
    · exact solved e known
    · have same := reflexive e (List.mem_append_left _ (List.mem_append_left _ taken))
      show (LocatedSubstitution.action (N := H) A).E _ _
      rw [same]
      exact (LocatedSubstitution.action (N := H) A).equivalence.refl _
    · have same := reflexive e (List.mem_append_left _ (List.mem_append_right _ read))
      show (LocatedSubstitution.action (N := H) A).E _ _
      rw [same]
      exact (LocatedSubstitution.action (N := H) A).equivalence.refl _
    · have same := reflexive e (List.mem_append_right _ told)
      show (LocatedSubstitution.action (N := H) A).E _ _
      rw [same]
      exact (LocatedSubstitution.action (N := H) A).equivalence.refl _

/-- **Exact firings at different spaces are independent**: the bridge from the syntactic condition
to the interface's independence. -/
theorem exact_independent {C : Configuration (H × T) O} {f g : AnnotatedRuns.Firing (H × T) S O}
    {a b : H} (different : a ≠ b) (atF : At a f) (atG : At b g)
    (admittedF : (located A space payload).Admits (s := C) f)
    (admittedG : (located A space payload).Admits (s := C) g)
    (takesF : f.rule.take = f.selection.taken.map (label space payload))
    (readsF : f.rule.read = f.selection.read.map (label space payload))
    (tellsF : ∀ e ∈ f.rule.tell, e.1 = e.2)
    (takesG : g.rule.take = g.selection.taken.map (label space payload))
    (readsG : g.rule.read = g.selection.read.map (label space payload))
    (tellsG : ∀ e ∈ g.rule.tell, e.1 = e.2)
    (distinct : ∀ o ∈ g.selection.made, o ∉ f.selection.made) :
    (transport A space payload).Independent C f g :=
  located_independent A space payload different atF atG admittedF admittedG
    (quiet_of_exact A space payload takesF readsF tellsF) (quiet_of_exact A space payload takesG readsG tellsG)
    distinct

end FirstOrder

/-! ## The dependent full step -/

section Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type} [DecidableEq O] {H : Type} (space : O → H)

/-- **A firing without helpers at the space `h`**: it takes, reads and makes only there. -/
structure PlainAt (h : H) {Δ : Context rules} (f : Plain levels O Δ) : Prop where
  taken : ∀ o ∈ f.taken, space o = h
  read : ∀ o ∈ f.read, space o = h
  made : ∀ o ∈ f.made, space o = h

variable {space}

/-- **Firings at different spaces are independent at dependent frames**, when the first adds no
information and neither writes a region of the other's predicate queries. -/
theorem dependent_independent {s : State rules O} {f g : Natural levels O s.frame} {a b : H}
    (different : a ≠ b) (atF : PlainAt space a f.toPlain) (atG : PlainAt space b g.toPlain)
    (first : (plainStep levels O).Admits f) (second : (plainStep levels O).Admits g)
    (quiet : (frames levels).Equivalent (f.toPlain.information s.toLocal) s.knowledge)
    (leftUnwritten : ∀ q ∈ g.toPlain.queries, (frames levels).Entails (joint s.toLocal f.toPlain g.toPlain)
      (fun _ τ => ¬ f.toPlain.Writes s.label q τ))
    (rightUnwritten : ∀ q ∈ f.toPlain.queries, (frames levels).Entails (joint s.toLocal f.toPlain g.toPlain)
      (fun _ τ => ¬ g.toPlain.Writes s.label q τ)) :
    (plainTransport levels O).Independent s f g := by
  refine independent_of_clauses first second ⟨?_, ?_, ?_, ?_, ?_, leftUnwritten, rightUnwritten⟩
  · intro o inF inG
    exact different ((atF.taken o inF).symm.trans (atG.taken o inG))
  · intro o inF inG
    exact different ((atF.taken o inF).symm.trans (atG.read o inG))
  · intro o inG inF
    exact different ((atF.read o inF).symm.trans (atG.taken o inG))
  · intro o inF inG
    exact different ((atF.made o inF).symm.trans (atG.made o inG))
  · obtain ⟨Θ, τ, solved⟩ := second.2.2.1
    refine ⟨Θ, τ, ?_⟩
    have known : (frames levels).Models τ s.knowledge :=
      Frames.models_of_subset (fun e member => List.mem_append_left _ member) solved
    have own : (frames levels).Models τ (f.toPlain.own s.label) :=
      Frames.models_of_subset (fun e member => List.mem_append_right _ member) ((quiet Θ τ).mpr known)
    have gOwn : (frames levels).Models τ (g.toPlain.own s.label) :=
      Frames.models_of_subset (fun e member => List.mem_append_right _ member) solved
    show (frames levels).Models τ (s.knowledge ++ f.toPlain.own s.label ++ g.toPlain.own s.label)
    rw [Frames.models_append, Frames.models_append]
    exact ⟨⟨known, own⟩, gOwn⟩

/-- **Without predicate queries, firings at different spaces are independent at dependent frames**
when the first adds no information. -/
theorem dependent_independent_of_no_queries {s : State rules O} {f g : Natural levels O s.frame} {a b : H}
    (different : a ≠ b) (atF : PlainAt space a f.toPlain) (atG : PlainAt space b g.toPlain)
    (first : (plainStep levels O).Admits f) (second : (plainStep levels O).Admits g)
    (quiet : (frames levels).Equivalent (f.toPlain.information s.toLocal) s.knowledge)
    (noF : f.queries = []) (noG : g.queries = []) :
    (plainTransport levels O).Independent s f g := by
  refine dependent_independent different atF atG first second quiet ?_ ?_
  · intro q member
    have empty : g.toPlain.queries = [] := by
      show g.queries.map NaturalQuery.toQuery = []
      rw [noG]
      rfl
    rw [empty] at member
    exact absurd member List.not_mem_nil
  · intro q member
    have empty : f.toPlain.queries = [] := by
      show f.queries.map NaturalQuery.toQuery = []
      rw [noF]
      rfl
    rw [empty] at member
    exact absurd member List.not_mem_nil

end Dependent

/-! ## Controls: information crosses spaces at dependent frames -/

namespace Controls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull
open Interface.DependentFull.Controls
open Interface.DependentFull.IndependenceControls

/-- Every firing that takes, reads and makes nothing is at every space. -/
theorem tells_at (space : Nat → Nat) (h : Nat) {f : Plain setting.levels Nat triple}
    (taken : f.taken = []) (read : f.read = []) (makes : f.makes = []) : PlainAt space h f :=
  ⟨fun o member => absurd (taken ▸ member) List.not_mem_nil,
    fun o member => absurd (read ▸ member) List.not_mem_nil,
    fun o member => absurd (show o ∈ f.makes.map Prod.fst from member) (by rw [makes]; exact List.not_mem_nil)⟩

/-- **A shared variable crosses spaces at dependent frames**: telling `X ≐ Ground` at space `1` and
telling `X ≐ Ground → Ground` at space `2` are each admitted, and the second is refused after the
first. -/
theorem dependent_shared_variable_crosses_spaces (space : Nat → Nat) :
    PlainAt space 1 tellGround ∧ PlainAt space 2 tellArrow ∧
      (Plain.toFiring (s := stateAt [] {0}) tellGround).Admits ∧
      (Plain.toFiring (s := stateAt [] {0}) tellArrow).Admits ∧
      ∀ first : (Plain.toFiring (s := stateAt [] {0}) tellGround).Admits,
        ¬ (Plain.toFiring (Plain.residual (s := stateAt [] {0}) tellGround tellArrow first)).Admits :=
  ⟨tells_at space 1 rfl rfl rfl, tells_at space 2 rfl rfl rfl,
    (Plain.admits_toFiring (s := stateAt [] {0}) tellGround).mpr tellGround_admitted,
    (Plain.admits_toFiring (s := stateAt [] {0}) tellArrow).mpr tellArrow_admitted, tells_clash_refused⟩

/-- **The bridge on the first-order control**: the quiet read of `Spaces.Controls` is exact, so the
syntactic condition gives the `quiet` hypothesis that `quiet_read_independent` uses; the binding read
`p(X)` is not exact, and the shared variable crosses spaces. -/
theorem quiet_read_exact :
    Spaces.Controls.readOneQuiet.rule.read =
        Spaces.Controls.readOneQuiet.selection.read.map (label Spaces.Controls.space Spaces.Controls.payload) ∧
      (LocatedSubstitution.action (N := Nat) Spaces.Controls.B).Equivalent
        (Spaces.Controls.readOneQuiet.selection.problem (label Spaces.Controls.space Spaces.Controls.payload)
          Spaces.Controls.readOneQuiet.rule Spaces.Controls.start) Spaces.Controls.start.equations ∧
      Spaces.Controls.readOne.rule.read ≠
        Spaces.Controls.readOne.selection.read.map (label Spaces.Controls.space Spaces.Controls.payload) := by
  refine ⟨rfl, quiet_of_exact Spaces.Controls.B Spaces.Controls.space Spaces.Controls.payload rfl rfl
    (fun _ member => absurd member List.not_mem_nil), fun same => ?_⟩
  have heads := congrArg List.head? same
  simp [Spaces.Controls.readOne, label, Spaces.Controls.space, Spaces.Controls.payload,
    Disequality.Controls.X] at heads

end Controls

#print axioms located_static_independent
#print axioms quiet_of_exact
#print axioms exact_independent
#print axioms Controls.quiet_read_exact
#print axioms located_residual_iff
#print axioms located_independent
#print axioms dependent_independent
#print axioms dependent_independent_of_no_queries
#print axioms Controls.dependent_shared_variable_crosses_spaces

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpacesInterface
