import Mettapedia.GSLT.Contexts.TermsAlone
import Mathlib.Data.Setoid.Basic

/-!
# A theory read along a map

Given a theory `target` (terms, static equivalence, reduction) and a map
`read : Source → target.Term`, the source terms carry a theory of their own:
a source term steps to another when their readings do, and two source terms
are statically equivalent when their readings are (`GSLT.readAlong`).  With a
finer static equivalence on the source, one that the reading still respects,
the same reduction gives `GSLT.readAlongWith`.

Presented through their contexts by `GSLT.termsAlone`, these are theories of
the category of `Mettapedia.GSLT.Contexts`, and the reading is a map in it.

* `ContextMap.betweenTerms` — a map on terms between two theories given by
  their terms alone, with `betweenTerms_hosting_iff` and
  `betweenTerms_exhausting_iff`: exhausting says that every term of the
  target is, up to the static equivalence, a reading.
* `GSLT.readAlongWith_hosting_iff` — the reading is hosting exactly when the
  static equivalence chosen on the source is the induced one and the readings
  are closed under reduction, up to the static equivalence.
* `GSLT.translate`, `GSLT.translate_hosting` — a map `convert` between the
  sources of two readings of one target, whose composite with the second
  reading is the first reading up to the static equivalence, is a hosting map
  between the two theories read along.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Mettapedia.GSLT

universe u

namespace ContextMap

variable {source target : GSLT.{u}}

/-- A map on terms that respects the static equivalence, as a map between two
theories given by their terms alone. -/
def betweenTerms (term : source.Term → target.Term)
    (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
      target.equations.r (term first) (term second)) :
    ContextMap source.termsAlone target.termsAlone :=
  ContextMap.ofTerms (target := target.termsAlone) PUnit.unit term term_resp

/-- Hosting, for a map between theories given by their terms alone: reflect
the static equivalence, send steps to steps, lift every step of an image. -/
theorem betweenTerms_hosting_iff (term : source.Term → target.Term)
    (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
      target.equations.r (term first) (term second)) :
    (betweenTerms term term_resp).Hosting ↔
      (∀ first second : source.Term, target.equations.r (term first) (term second) →
        source.equations.r first second) ∧
      (∀ first next : source.Term, source.rewrites first next →
        target.rewrites (term first) (term next)) ∧
      ∀ (first : source.Term) (next : target.Term), target.rewrites (term first) next →
        ∃ sourceNext, source.rewrites first sourceNext ∧
          target.equations.r next (term sourceNext) :=
  ContextMap.ofTerms_hosting_iff (target := target.termsAlone) PUnit.unit term term_resp

/-- **Exhausting, for a map between theories given by their terms alone**:
every term of the target is, up to the static equivalence, an image. -/
theorem betweenTerms_exhausting_iff (term : source.Term → target.Term)
    (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
      target.equations.r (term first) (term second)) :
    (betweenTerms term term_resp).Exhausting ↔
      ∀ value : target.Term, ∃ origin : source.Term, target.equations.r (term origin) value := by
  constructor
  · intro exhausting value
    obtain ⟨origin, related⟩ :=
      ContextMap.Exhausting.term_surjective (betweenTerms term term_resp) exhausting
        (origin := PUnit.unit) value
    exact ⟨origin, target.equations.iseqv.symm related⟩
  · intro reached arity holes result observer
    have filled : ∀ (context : TermsContext source.Term arity) (filling : arity → source.Term),
        target.termsAlone.fill (holes := fun _ : arity => PUnit.unit) (result := PUnit.unit)
            (ContextMap.termsImage (target := target.termsAlone) PUnit.unit term context)
            (fun index => term (filling index)) =
          term (context.fill filling) :=
      fun context filling =>
        ContextMap.fill_termsImage (target := target.termsAlone) PUnit.unit term context filling
    cases observer with
    | hole position only =>
        refine ⟨TermsContext.hole position only, fun filling => ?_⟩
        have same := filled (TermsContext.hole position only) filling
        exact ContextMap.equations_of_eq (target := target.termsAlone) same
    | constant value empty =>
        obtain ⟨origin, related⟩ := reached value
        refine ⟨TermsContext.constant origin empty, fun filling => ?_⟩
        have same := filled (TermsContext.constant origin empty) filling
        exact target.equations.iseqv.trans
          (ContextMap.equations_of_eq (target := target.termsAlone) same) related

end ContextMap

namespace GSLT

variable (target : GSLT.{u})

/-- **A theory read along a map, at a chosen static equivalence.**  The terms
are the source terms; one steps to another when their readings do; the static
equivalence is the chosen one, which the reading respects. -/
def readAlongWith {Source : Type u} (read : Source → target.Term) (static : Setoid Source)
    (respects : ∀ {first second : Source}, static.r first second →
      target.equations.r (read first) (read second)) : GSLT.{u} where
  Term := Source
  equations := static
  rewrites := fun term next => target.rewrites (read term) (read next)
  rewrites_resp_left := by
    intro term term' next equivalent step
    obtain ⟨next', step', related⟩ := target.rewrites_resp_left (respects equivalent) step
    exact ⟨next, target.rewrites_resp_right step' (target.equations.iseqv.symm related),
      static.iseqv.refl next⟩
  rewrites_resp_right := fun step equivalent =>
    target.rewrites_resp_right step (respects equivalent)

/-- **A theory read along a map**: two source terms are statically equivalent
when their readings are. -/
def readAlong {Source : Type u} (read : Source → target.Term) : GSLT.{u} :=
  target.readAlongWith read (Setoid.comap read target.equations) (fun equivalent => equivalent)

variable {target}

@[simp] theorem readAlong_equations {Source : Type u} (read : Source → target.Term)
    (first second : Source) :
    (target.readAlong read).equations.r first second ↔
      target.equations.r (read first) (read second) :=
  Iff.rfl

@[simp] theorem readAlongWith_rewrites {Source : Type u} (read : Source → target.Term)
    (static : Setoid Source)
    (respects : ∀ {first second : Source}, static.r first second →
      target.equations.r (read first) (read second)) (term next : Source) :
    (target.readAlongWith read static respects).rewrites term next ↔
      target.rewrites (read term) (read next) :=
  Iff.rfl

@[simp] theorem readAlong_rewrites {Source : Type u} (read : Source → target.Term)
    (term next : Source) :
    (target.readAlong read).rewrites term next ↔ target.rewrites (read term) (read next) :=
  Iff.rfl

/-- The readings are closed under reduction, up to the static equivalence:
every reduct of a reading is equivalent to a reading. -/
def ReadingClosed {Source : Type u} (read : Source → target.Term) : Prop :=
  ∀ (origin : Source) (value : target.Term), target.rewrites (read origin) value →
    ∃ next : Source, target.equations.r value (read next)

/-- The reading, as a map of theories. -/
def readingWith {Source : Type u} (read : Source → target.Term) (static : Setoid Source)
    (respects : ∀ {first second : Source}, static.r first second →
      target.equations.r (read first) (read second)) :
    ContextMap (target.readAlongWith read static respects).termsAlone target.termsAlone :=
  ContextMap.betweenTerms (source := target.readAlongWith read static respects) read respects

/-- The reading out of the theory read along it. -/
def reading {Source : Type u} (read : Source → target.Term) :
    ContextMap (target.readAlong read).termsAlone target.termsAlone :=
  readingWith read (Setoid.comap read target.equations) (fun equivalent => equivalent)

/-- The reading sends steps to steps, at every static equivalence. -/
theorem readingWith_preserves {Source : Type u} (read : Source → target.Term)
    (static : Setoid Source)
    (respects : ∀ {first second : Source}, static.r first second →
      target.equations.r (read first) (read second)) :
    (readingWith read static respects).PreservesTransitions := by
  apply (ContextMap.preservesTransitions_iff_rewrites _).mpr
  intro interface term next step
  exact step

/-- The reading lifts every step of an image when the readings are closed
under reduction. -/
theorem readingWith_reflects {Source : Type u} (read : Source → target.Term)
    (static : Setoid Source)
    (respects : ∀ {first second : Source}, static.r first second →
      target.equations.r (read first) (read second)) (closed : ReadingClosed read) :
    (readingWith read static respects).ReflectsTransitions := by
  apply (ContextMap.reflectsTransitions_iff_rewrites _).mpr
  intro interface term next step
  obtain ⟨sourceNext, related⟩ := closed term next step
  exact ⟨sourceNext, target.rewrites_resp_right step related, related⟩

/-- **The reading is hosting exactly when the chosen static equivalence is the
induced one and the readings are closed under reduction.** -/
theorem readingWith_hosting_iff {Source : Type u} (read : Source → target.Term)
    (static : Setoid Source)
    (respects : ∀ {first second : Source}, static.r first second →
      target.equations.r (read first) (read second)) :
    (readingWith read static respects).Hosting ↔
      (∀ first second : Source, target.equations.r (read first) (read second) →
        static.r first second) ∧ ReadingClosed read := by
  refine Iff.trans (ContextMap.betweenTerms_hosting_iff
    (source := target.readAlongWith read static respects) read respects) ?_
  constructor
  · rintro ⟨reflectsEquations, -, reflects⟩
    refine ⟨reflectsEquations, fun origin value step => ?_⟩
    obtain ⟨next, -, related⟩ := reflects origin value step
    exact ⟨next, related⟩
  · rintro ⟨reflectsEquations, closed⟩
    refine ⟨reflectsEquations, fun _ _ step => step, fun origin value step => ?_⟩
    obtain ⟨next, related⟩ := closed origin value step
    exact ⟨next, target.rewrites_resp_right step related, related⟩

/-- **The reading out of the theory read along it is hosting** when the
readings are closed under reduction. -/
theorem reading_hosting {Source : Type u} (read : Source → target.Term)
    (closed : ReadingClosed read) : (reading read).Hosting :=
  (readingWith_hosting_iff read _ _).mpr ⟨fun _ _ equivalent => equivalent, closed⟩

/-- **A finer static equivalence is not hosted by the reading**: two source
terms kept apart whose readings are equivalent. -/
theorem readingWith_not_hosting {Source : Type u} (read : Source → target.Term)
    (static : Setoid Source)
    (respects : ∀ {first second : Source}, static.r first second →
      target.equations.r (read first) (read second)) {first second : Source}
    (apart : ¬ static.r first second)
    (identified : target.equations.r (read first) (read second)) :
    ¬ (readingWith read static respects).Hosting :=
  fun hosting => apart (((readingWith_hosting_iff read static respects).mp hosting).1 _ _ identified)

/-- The reading is exhausting exactly when every term of the target is, up to
the static equivalence, a reading. -/
theorem readingWith_exhausting_iff {Source : Type u} (read : Source → target.Term)
    (static : Setoid Source)
    (respects : ∀ {first second : Source}, static.r first second →
      target.equations.r (read first) (read second)) :
    (readingWith read static respects).Exhausting ↔
      ∀ value : target.Term, ∃ origin : Source, target.equations.r (read origin) value :=
  ContextMap.betweenTerms_exhausting_iff (source := target.readAlongWith read static respects)
    read respects

/-- The reading out of the theory read along it is exhausting exactly when
every term of the target is, up to the static equivalence, a reading. -/
theorem reading_exhausting_iff {Source : Type u} (read : Source → target.Term) :
    (reading read).Exhausting ↔
      ∀ value : target.Term, ∃ origin : Source, target.equations.r (read origin) value :=
  readingWith_exhausting_iff read (Setoid.comap read target.equations)
    (fun equivalent => equivalent)

/-! ## Maps between two readings of one target -/

/-- A map between the sources that agrees with the readings respects the
static equivalences read along them. -/
theorem translate_resp {First Second : Type u} (firstRead : First → target.Term)
    (secondRead : Second → target.Term) (convert : First → Second)
    (agrees : ∀ origin : First,
      target.equations.r (secondRead (convert origin)) (firstRead origin))
    {first second : First}
    (equivalent : (target.readAlong firstRead).equations.r first second) :
    (target.readAlong secondRead).equations.r (convert first) (convert second) :=
  target.equations.iseqv.trans (agrees first)
    (target.equations.iseqv.trans equivalent (target.equations.iseqv.symm (agrees second)))

/-- A map between the sources of two readings, whose composite with the second
reading is the first reading up to the static equivalence of the target, as a
map between the two theories read along. -/
def translate {First Second : Type u} (firstRead : First → target.Term)
    (secondRead : Second → target.Term) (convert : First → Second)
    (agrees : ∀ origin : First,
      target.equations.r (secondRead (convert origin)) (firstRead origin)) :
    ContextMap (target.readAlong firstRead).termsAlone (target.readAlong secondRead).termsAlone :=
  ContextMap.betweenTerms (source := target.readAlong firstRead)
    (target := target.readAlong secondRead) convert
    (translate_resp firstRead secondRead convert agrees)

/-- **Such a map is hosting**, when the first readings are closed under
reduction. -/
theorem translate_hosting {First Second : Type u} (firstRead : First → target.Term)
    (secondRead : Second → target.Term) (convert : First → Second)
    (agrees : ∀ origin : First,
      target.equations.r (secondRead (convert origin)) (firstRead origin))
    (closed : ReadingClosed firstRead) :
    (translate firstRead secondRead convert agrees).Hosting := by
  refine (ContextMap.betweenTerms_hosting_iff (source := target.readAlong firstRead)
    (target := target.readAlong secondRead) convert
    (translate_resp firstRead secondRead convert agrees)).mpr ?_
  refine ⟨fun first second equivalent => ?_, fun first next step => ?_, fun first next step => ?_⟩
  · exact target.equations.iseqv.trans (target.equations.iseqv.symm (agrees first))
      (target.equations.iseqv.trans equivalent (agrees second))
  · obtain ⟨value, moved, related⟩ :=
      target.rewrites_resp_left (target.equations.iseqv.symm (agrees first)) step
    exact target.rewrites_resp_right moved
      (target.equations.iseqv.trans (target.equations.iseqv.symm related)
        (target.equations.iseqv.symm (agrees next)))
  · obtain ⟨value, moved, related⟩ := target.rewrites_resp_left (agrees first) step
    obtain ⟨sourceNext, reached⟩ := closed first value moved
    refine ⟨sourceNext, target.rewrites_resp_right moved reached, ?_⟩
    exact target.equations.iseqv.trans related
      (target.equations.iseqv.trans reached (target.equations.iseqv.symm (agrees sourceNext)))

/-- Such a map is exhausting exactly when every second reading is, up to the
static equivalence, a first reading. -/
theorem translate_exhausting_iff {First Second : Type u} (firstRead : First → target.Term)
    (secondRead : Second → target.Term) (convert : First → Second)
    (agrees : ∀ origin : First,
      target.equations.r (secondRead (convert origin)) (firstRead origin)) :
    (translate firstRead secondRead convert agrees).Exhausting ↔
      ∀ value : Second, ∃ origin : First,
        target.equations.r (firstRead origin) (secondRead value) := by
  refine Iff.trans (ContextMap.betweenTerms_exhausting_iff (source := target.readAlong firstRead)
    (target := target.readAlong secondRead) convert
    (translate_resp firstRead secondRead convert agrees)) ?_
  constructor
  · intro reached value
    obtain ⟨origin, related⟩ := reached value
    exact ⟨origin, target.equations.iseqv.trans (target.equations.iseqv.symm (agrees origin)) related⟩
  · intro reached value
    obtain ⟨origin, related⟩ := reached value
    exact ⟨origin, target.equations.iseqv.trans (agrees origin) related⟩

/-- **A map between the sources that does not send steps to steps is not
hosting**, whatever its action on contexts. -/
theorem not_hosting_of_step_lost {First Second : Type u} {firstRead : First → target.Term}
    {secondRead : Second → target.Term}
    (map : ContextMap (target.readAlong firstRead).termsAlone
      (target.readAlong secondRead).termsAlone)
    {origin next : First} (step : target.rewrites (firstRead origin) (firstRead next))
    (lost : ¬ target.rewrites (secondRead (map.term (origin := PUnit.unit) origin))
      (secondRead (map.term (origin := PUnit.unit) next))) : ¬ map.Hosting :=
  fun hosting =>
    lost (map.preservesRewrites_of_transitions hosting.preserves (interface := PUnit.unit) step)

end GSLT

#print axioms ContextMap.betweenTerms_exhausting_iff
#print axioms GSLT.readingWith_hosting_iff
#print axioms GSLT.reading_hosting
#print axioms GSLT.translate_hosting
#print axioms GSLT.translate_exhausting_iff
#print axioms GSLT.not_hosting_of_step_lost

end Mettapedia.GSLT
