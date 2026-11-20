import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces

/-!
# The first-order step restricted to a program is the step of the program at one frame

At the one-frame action of a substitution action (`Frames.ofSubstitution A`), with the identity as the
only extension, the step of a program (`step`) and the existing first-order step
(`AnnotatedRuns.firstOrder`) are compared through two maps.

* **States**: a configuration with the global labels is a state at the one frame (`embed`).
* **Firings**: a firing of the program goes to the first-order firing whose rule instance is the
  opened rule, whose region queries are the exact observations of the opened collect patterns with
  their seen sets (a row is in the region at a solution when the solution equates its label with the
  pattern), and whose selection is the same (`toFirstOrder`).

The first-order step labels identities once and for all (`label : O → T`) and asks that made
identities already carry the made rows; the step of a program labels made identities by its made
rows. The first-order discipline is the restriction of the step to firings whose made identities
already carry their made rows (`keeping`).

**The first-order step restricted to a program** (`firstOrderOn`) admits the first-order firings
that are the image of a firing of the program with a fresh opening.

* `admits_toFirstOrder_iff`: a firing of the program is admitted and keeps labels exactly when its
  first-order image is admitted by the first-order step, its opening is fresh, and it has one seen set
  per collect pattern.
* `result_toFirstOrder`: the result of a label-keeping firing is the embedded first-order result.
* `firstOrderOn_admits_iff`: the admitted firings of the restricted first-order step are exactly the
  images of the admitted label-keeping firings of the program.
* **`firstOrder_eq`**: through `embed`, the transition relation of the restricted first-order step is
  the transition relation of the label-keeping step of the program, and the latter never leaves the
  embedded configurations (`keeping_closed`).

The map on firings is onto the admitted firings of the restricted step, and not injective: two rules,
or two openings, may open to the same rule instance; the step of a program remembers which rule and
which opening fired. At one frame the first-order step moves along the identity
(`firstOrder_along_identity`), so its knowledge genuinely only refines.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire regionOf mem_regionOf)
open LogicOverTheStep.StepSpan (Succ)

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]

/-- Terms at the one frame. -/
abbrev Terms (T : Type uT) : PUnit.{1} → Type uT := fun _ => T

/-- The one-frame frame action. -/
abbrev frames : Frames (Terms T) (fun _ _ : PUnit.{1} => S) := Frames.ofSubstitution A

/-- The one-frame extensions: the identity. -/
abbrev ext : Extensions.{0, uS, 0} (fun _ _ : PUnit.{1} => S) := Extensions.identity (frames A)

variable (label : O → T) (P : Program (Terms T))

/-- **A configuration with its labels, as a state at the one frame.** -/
def embed (C : Configuration T O) : State (Terms T) O := ⟨PUnit.unit, C.equations, C.present, label⟩

omit [DecidableEq O] in
theorem embed_injective {C D : Configuration T O} (same : embed label C = embed label D) : C = D := by
  cases C
  cases D
  simp only [embed, State.mk.injEq, true_and] at same
  obtain ⟨equations, present, -⟩ := same
  subst equations
  subst present
  rfl

/-- A collect pattern as a predicate query of the first-order step: at a solution, a row is in the
region when the solution equates its label with the pattern. -/
noncomputable def collectQuery (pattern : T) (seen : Finset O) : PredicateQueryAdmission.Query T S O :=
  ⟨fun σ t => @decide (A.E (A.apply σ pattern) (A.apply σ t)) (Classical.propDecidable _), seen⟩

/-- **The first-order firing of a firing of a program**: the opened rule, the opened collect patterns as
exact region queries of their seen sets, and the same selection. -/
noncomputable def toFirstOrder (g : Firing O (ext A) P PUnit.unit) : AnnotatedRuns.Firing T S O :=
  ⟨g.opened (frames A),
    (((g.collectOpened (frames A)).zip g.seen).map fun q => collectQuery A q.1 q.2).map
      PredicateQueryAdmission.Query.toRegion,
    g.selection⟩

/-- The first-order firings that open a rule of the program freshly, with its collect patterns. -/
def OpensProgram (C : Configuration T O) (f : AnnotatedRuns.Firing T S O) : Prop :=
  ∃ g : Firing O (ext A) P PUnit.unit, g.Fresh (frames A) (embed label C) ∧
    g.rule.collect.length = g.seen.length ∧ toFirstOrder A P g = f

/-- **The first-order step restricted to a program**: its admitted firings that open a rule of the
program freshly. -/
def firstOrderOn : Interface.Step (frames A) O (Configuration T O) (fun _ => AnnotatedRuns.Firing T S O) :=
  Spaces.restrict (AnnotatedRuns.firstOrder A label).toStep (fun {C} f => OpensProgram A label P C f)

/-- **The label-keeping step of a program**: firings whose made identities already carry their made
rows. -/
def keeping :
    Interface.Step (frames A) O (State (Terms T) O) (fun s => Firing O (ext A) P s.frame) :=
  Spaces.restrict (step (frames A) O (ext A) P).toStep
    (fun {s} g => g.selection.made.map s.label = (g.opened (frames A)).produce)

/-! ## Rows, information and checks agree -/

section Agreement

variable {A label P}

omit [DecidableEq O] in
theorem row_eq (C : Configuration T O) (g : Firing O (ext A) P PUnit.unit) :
    g.row (frames A) (embed label C) = label := by
  funext o
  exact A.apply_identity (label o)

omit [DecidableEq O] in
/-- **The information is the first-order problem.** -/
theorem information_eq (C : Configuration T O) (g : Firing O (ext A) P PUnit.unit) :
    g.information (frames A) (embed label C) = g.selection.problem label (g.opened (frames A)) C := by
  unfold Firing.information Firing.matching Selection.problem Selection.equations
  rw [row_eq C g]
  have known : (frames A).applyStore ((ext A).weaken g.ext) (embed label C).knowledge = C.equations :=
    Frames.applyStore_id (X := frames A) C.equations
  rw [known]

omit [DecidableEq O] in
theorem matchesAt_eq {σ : S} (present : Finset O) (pattern : T) :
    matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ label present pattern =
      Check.«matches» A σ label present pattern := by
  classical
  ext o
  rw [mem_matchesAt]
  unfold Check.«matches»
  rw [Finset.mem_filter]
  exact Iff.rfl

omit [DecidableEq O] in
theorem checkHolds_iff {σ : S} (present : Finset O) (c : Check T) :
    checkHolds (frames A) (a := PUnit.unit) (b := PUnit.unit) σ label present c ↔
      c.Holds A σ label present := by
  cases c with
  | equal left right => exact Iff.rfl
  | predicate quantifier pattern => exact Iff.rfl
  | count pattern number =>
      show (matchesAt (frames A) σ label present pattern).card = number ↔ _
      rw [matchesAt_eq]
      exact Iff.rfl

omit [DecidableEq O] in
theorem collect_iff {σ : S} (present : Finset O) (pattern : T) (seen : Finset O) :
    matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ label present pattern = seen ↔
      ((collectQuery A pattern seen).atSolution σ).Holds label present := by
  have same : matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ label present pattern =
      regionOf label present ((collectQuery A pattern seen).atSolution σ).region := by
    ext o
    rw [mem_matchesAt, mem_regionOf]
    simp only [collectQuery, PredicateQueryAdmission.Query.atSolution, decide_eq_true_iff]
    exact Iff.rfl
  rw [same]
  exact Iff.rfl

/-- **The guard predicate is the first-order one.** -/
theorem holds_iff (C : Configuration T O) (g : Firing O (ext A) P PUnit.unit) (σ : S) :
    g.Holds (frames A) (embed label C) (b := PUnit.unit) σ ↔
      (AnnotatedRuns.firstOrder A label).Holds (s := C) (toFirstOrder A P g) PUnit.unit σ := by
  unfold Firing.Holds
  rw [row_eq C g]
  show _ ↔ (∀ check ∈ (g.opened (frames A)).checks, check.Holds A σ label C.present) ∧
    ∀ query ∈ (((g.collectOpened (frames A)).zip g.seen).map (fun q => collectQuery A q.1 q.2)).map
        PredicateQueryAdmission.Query.toRegion,
      query.Holds σ label C.present
  rw [List.forall_mem_map, List.forall_mem_map]
  apply and_congr
  · exact forall₂_congr fun c _ => checkHolds_iff C.present c
  · exact forall₂_congr fun q _ => collect_iff C.present q.1 q.2

end Agreement

/-! ## Admission and results agree -/

variable {A label P}

/-- **Admission agrees.** A firing of the program is admitted and keeps labels exactly when its
first-order image is admitted, its opening is fresh, and it has one seen set per collect pattern. -/
theorem admits_toFirstOrder_iff (C : Configuration T O) (g : Firing O (ext A) P PUnit.unit) :
    ((step (frames A) O (ext A) P).Admits (s := embed label C) g ∧
        g.selection.made.map label = (g.opened (frames A)).produce) ↔
      ((AnnotatedRuns.firstOrder A label).Admits (s := C) (toFirstOrder A P g) ∧
        g.Fresh (frames A) (embed label C) ∧ g.rule.collect.length = g.seen.length) := by
  have entails : (frames A).Entails (g.information (frames A) (embed label C))
        (fun b σ => g.Holds (frames A) (embed label C) (b := b) σ) ↔
      (frames A).Entails (g.selection.problem label (g.opened (frames A)) C)
        ((AnnotatedRuns.firstOrder A label).Holds (s := C) (toFirstOrder A P g)) := by
    rw [information_eq C g]
    exact forall₂_congr fun _ σ => imp_congr_right fun _ => holds_iff C g σ
  have solvable : (frames A).Solvable (g.information (frames A) (embed label C)) ↔
      (frames A).Solvable (g.selection.problem label (g.opened (frames A)) C) := by
    rw [information_eq C g]
  have takeLength : (g.opened (frames A)).take.length = g.rule.body.take.length := List.length_map _
  have readLength : (g.opened (frames A)).read.length = g.rule.body.read.length := List.length_map _
  have produceLength : (g.opened (frames A)).produce.length = g.rule.body.produce.length :=
    List.length_map _
  show (g.Admits (frames A) (embed label C) ∧ _) ↔ ((toFirstOrder A P g).Valid A label C ∧ _)
  rw [AnnotatedRuns.firstOrder_admits_iff A label C (toFirstOrder A P g)]
  unfold Firing.Admits Firing.Shapes
  rw [entails, solvable]
  constructor
  · rintro ⟨⟨⟨fresh, takenNodup, madeNodup, take, read, -, collect⟩, enabled, consistent, asks⟩, keeps⟩
    exact ⟨⟨⟨takenNodup, madeNodup, takeLength.trans take, readLength.trans read, keeps⟩, enabled,
      consistent, asks⟩, fresh, collect⟩
  · rintro ⟨⟨⟨takenNodup, madeNodup, take, read, keeps⟩, enabled, consistent, asks⟩, fresh, collect⟩
    have keeps' : g.selection.made.map label = (g.opened (frames A)).produce := keeps
    have produce : g.rule.body.produce.length = g.selection.made.length := by
      rw [← produceLength, ← keeps', List.length_map]
    exact ⟨⟨⟨fresh, takenNodup, madeNodup, takeLength.symm.trans take, readLength.symm.trans read,
      produce, collect⟩, enabled, consistent, asks⟩, keeps⟩

theorem relabel_map_self {a : PUnit.{1}} (old : O → Terms T a) :
    ∀ made : List O, relabel old made (made.map old) = old
  | [] => rfl
  | o' :: rest => by
      funext o
      simp only [List.map_cons, relabel]
      split_ifs with same
      · rw [same]
      · exact congrFun (relabel_map_self old rest) o

/-- **Results agree**: the result of a label-keeping firing is the embedded first-order result. -/
theorem result_toFirstOrder (C : Configuration T O) (g : Firing O (ext A) P PUnit.unit)
    (keeps : g.selection.made.map label = (g.opened (frames A)).produce) :
    g.result (frames A) (embed label C) =
      embed label ((toFirstOrder A P g).result label C) := by
  unfold Firing.result
  rw [information_eq C g, row_eq C g, ← keeps, relabel_map_self]
  rfl

/-- **The restricted first-order step admits exactly the images of the admitted label-keeping
firings of the program.** -/
theorem firstOrderOn_admits_iff (C : Configuration T O) (f : AnnotatedRuns.Firing T S O) :
    (firstOrderOn A label P).Admits (s := C) f ↔
      ∃ g : Firing O (ext A) P PUnit.unit, toFirstOrder A P g = f ∧
        (step (frames A) O (ext A) P).Admits (s := embed label C) g ∧
        g.selection.made.map label = (g.opened (frames A)).produce := by
  constructor
  · rintro ⟨admitted, g, fresh, collect, rfl⟩
    exact ⟨g, rfl, (admits_toFirstOrder_iff C g).mpr ⟨admitted, fresh, collect⟩⟩
  · rintro ⟨g, rfl, admitted, keeps⟩
    obtain ⟨firstAdmitted, fresh, collect⟩ := (admits_toFirstOrder_iff C g).mp ⟨admitted, keeps⟩
    exact ⟨firstAdmitted, g, fresh, collect, rfl⟩

/-- **The first-order step restricted to a program is the step of the program at one frame**: through
`embed`, the two transition relations are equal. -/
theorem firstOrder_eq (C C' : Configuration T O) :
    Succ (firstOrderOn A label P) C C' ↔ Succ (keeping A P) (embed label C) (embed label C') := by
  constructor
  · rintro ⟨f, admitted, reached⟩
    obtain ⟨g, rfl, stepAdmitted, keeps⟩ := (firstOrderOn_admits_iff C f).mp admitted
    refine ⟨g, ⟨stepAdmitted, keeps⟩, ?_⟩
    show g.result (frames A) (embed label C) = embed label C'
    rw [result_toFirstOrder C g keeps]
    exact congrArg (embed label) reached
  · rintro ⟨g, ⟨stepAdmitted, keeps⟩, reached⟩
    have firstAdmitted := (firstOrderOn_admits_iff C (toFirstOrder A P g)).mpr ⟨g, rfl, stepAdmitted, keeps⟩
    refine ⟨toFirstOrder A P g, firstAdmitted, ?_⟩
    apply embed_injective label
    have result := result_toFirstOrder C g keeps
    exact result.symm.trans reached

/-- **The label-keeping step never leaves the embedded configurations.** -/
theorem keeping_closed (C : Configuration T O) {s' : State (Terms T) O}
    (reached : Succ (keeping A P) (embed label C) s') :
    ∃ C', s' = embed label C' := by
  obtain ⟨g, ⟨-, keeps⟩, rfl⟩ := reached
  exact ⟨(toFirstOrder A P g).result label C, result_toFirstOrder C g keeps⟩

/-- **The first-order step moves along the identity**, so its knowledge genuinely only refines
(`refines_of_identity`). -/
theorem firstOrder_along_identity {C : Configuration T O} (f : AnnotatedRuns.Firing T S O)
    (admitted : (AnnotatedRuns.firstOrder A label).Admits (s := C) f) (t : T) :
    A.apply ((AnnotatedRuns.firstOrder A label).toStep.along f admitted) t = t := by
  show A.apply (A.compose A.identity A.identity) t = t
  rw [A.apply_compose, A.apply_identity, A.apply_identity]

#print axioms embed_injective
#print axioms information_eq
#print axioms holds_iff
#print axioms admits_toFirstOrder_iff
#print axioms result_toFirstOrder
#print axioms firstOrderOn_admits_iff
#print axioms firstOrder_eq
#print axioms keeping_closed
#print axioms firstOrder_along_identity

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame
