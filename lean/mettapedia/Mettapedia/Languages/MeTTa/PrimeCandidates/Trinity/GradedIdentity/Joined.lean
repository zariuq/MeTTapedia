import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle
import Mettapedia.PLN.Bridges.Languages.NativeGradedEvidence
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity.Typed

/-!
# The shared graded identity: the three faces joined

The specimen stores `(coin)` three times: `2` with grade `3`, `2` with grade `3` again, and
`5` with grade `7`. It defines `(weigh-by-self $x) = $x` with grade `$x`, and
`(paired $x) = (Pair $x $x)`. The term `(paired (weigh-by-self (coin)))` runs to the bag
`(Pair 2 2)` with coefficient `6`, `(Pair 2 2)` with coefficient `6` again, and `(Pair 5 5)`
with coefficient `35`. Each stored row of the coin is one occurrence. The selected coin is
charged once, with its own grade and the identity's grade (the coin's value), and is used
twice inside `Pair`.

**What `weigh-by-self` is.** Under value erasure it is the identity: it returns its argument.
Under the weighted reading it is not an identity: it weighs its result by that result. The
nested identity `(id (id 7))` with grade `$x` (the form of `(weigh-by-self (weigh-by-self 7))` in the
identity program) returns `7` with coefficient `49`. The identity of the weighted reading is the
unit grade: `(id 7)` with grade `1` has coefficient `1`. With the literal grade `2`,
`(id (id 7))` has coefficient `4`; read as evidence, the literal grade `(evidence 2 1)` gives
`(evidence 4 1)`.

**Running.** The native weighted machine with nested coefficient continuations
(`NativeWeightedHandler.nestedSource`, or `nestedAdmittedSource` under a declared admission);
`Specimen.nativeBag` reads its completed values with their coefficients. Its runs are the ones
proved in `NativeWeightedControls` and `NativeGradedEvidence`, cited here: `shared_identity_values`,
`nested_grade_forcing_retains_inner_factor`, `graded_identity_constant_composes`,
`graded_identity_unit`, `grade_only_binding_survives`, `nested_grade_keeps_argument_factor`,
`graded_evidence_identity_shares_choice`. Two runs are stated here for the first time: the
same pair with one stored row of `2` (`singlePair_native`), and the literal evidence grade
(`literalEvidence_native`).

**Annotated occurrences.** A reading of the stored rows (`Specimen.occurrences`). A call
selects each stored row of its head, in order. A row with a grade is charged once at each
invocation, with the grade its annotation reads once its parameter is bound. An argument is
selected once and shared by every use of the parameter, and is selected only when the body or
the grade uses it. An annotated occurrence (`AnnotatedOccurrence`) is the value returned and
the rows charged, in the order in which they are charged; `Specimen.annotate` gives those of
the specimen's term. This reading does not run the machine. Every charge of an annotated
occurrence is a stored row of the program that its annotation grades, with a grade the
admission accepts (`Specimen.charges_stored`).

Alone, this face is not a typing. **The typed reading** (section at the end) supplies the
derivation behind it: the typed programs of `Typed.lean` (the weight carriers declared in a
package, the specimen typed by `ScopedComputation.Typing`) run to worlds whose recorded charges,
read, are exactly the annotated occurrences (`sharedPair_typed`, `nestedSelf_typed`,
`coinThroughId_typed`, and `evidenceShared_typed` over evidence counts). `typedTriangle` has
these typed occurrences as its middle face, each with its typing derivation
(`TypedSpecimen.typing`). Negative example: a fresh producer at each use of `paired` is typed
as well, but its nine occurrences include the mixed pair `(Pair 2 5)` and are not the annotated
ones (`fresh_producer_not_annotated`).

**A guard, compared apart.** The contextual handler has no abort, so a guard that produces no
world is realized by the direct worlds of the typed program only. Under a zero-rejecting
admission the identity over the coin drops the occurrence of the ungraded zero row, which
attachment keeps; the typed guarded worlds, the annotated occurrences and a new native run
agree (`guard_comparison`, `guardedCoin_native`). The native machine draws the same line on
another program (`zero_attachment_is_not_guard_admission`).

**Meaning.** The weighted bag (`weigh`): one entry for each annotated occurrence, with the
value it returns and the product of its grades.

**The triangles commute by proof.** `numberTriangle` (natural grades) and `evidenceTriangle`
(evidence counts) are built by `triangleOfThree` on three faces: running, annotated
occurrences and meaning. The direct map runs the machine; the agreement with the bag of the
annotated occurrences is a cited run on one side and a computation of the occurrences on the
other (`numberAgree`, `evidenceAgree`). Each evidence bag is the number bag with each
coefficient `n` read as `(evidence n 1)`, on the same annotated rows
(`evidence_annotated_is_count_image`, `evidence_bag_is_count_image`): `(evidence 6 1)` twice and
`(evidence 35 1)` for the shared pair, `(evidence 4 1)` for the literal identity.

**What each map forgets.**
* Value erasure (`erase`) gives the values of the ordinary run, which ignores the grades
  (`erase_is_ordinary_run`). It forgets the coefficients: `(id (id 7))` with grade `$x`, with grade
  `2`, and `(id 7)` with grade `1` all erase to `[7]`, with coefficients `49`, `4` and `1`
  (`erasedTriangle_loses`, `graded_identity_is_identity_of_values`). The one-level scoring of
  the nested term also returns `7`, with `7` against `49` (`one_level_scoring_erases_alike`).
* The set of values (`valueSet`) forgets multiplicity: three stored rows and two stored rows
  give one set `{(Pair 2 2), (Pair 5 5)}` (`valueSetTriangle_loses`), while the bag keeps the two
  rows of `(Pair 2 2)` as two occurrences (`pair_two_two_twice`). The commutation with the bag
  read one entry per value fails (`onePerValue_disagrees`).
* Charging once is part of the meaning (`charged_once`): the machine gives `6` and `35`.
  Duplicating only the identity factor gives `12` and `175` (`duplicate_identity_factor`);
  duplicating only the coin factor gives `18` and `245` (`duplicate_coin_factor`); duplicating
  the producer's whole ledger at the same selected value gives `36` and `1225`
  (`duplicate_producer_ledger`). Rerunning independent producers is a different program again:
  it can form mixed pairs, which the run never does (`no_mixed_pair`).
* The per-value sum and the linear total identify the two rows of `6` with one row of `12`
  (`linear_total_identifies_rows`); the bag does not.

**Controls outside the triangles.** The annotated occurrences also agree with the machine on a
zero grade under attachment and under a nonzero guard (`zero_controls_agree`), on opposite
evidence polarities under nonzero and positive admission (`polarity_controls_agree`), and on
the order of factors in a noncommutative algebra (`demand_order_controls_agree`).

Positive examples: the annotated rows of the shared pair are the coin rows `0`, `1`, `2`, each
with the identity row `3` (`sharedPair_annotated`); a zero coefficient stays an occurrence
(`coinThroughId_annotated`). Negative examples: no annotated or native occurrence is a mixed pair
(`no_mixed_pair`); the commutation with one entry per value is refused
(`onePerValue_disagrees`).

Not here: a typing of every term of the graded fragment (the typed reading covers the shared
pair, the nested identity and the identity over the coin), and a typed account of the
machine's intermediate states; a general theorem that the annotated occurrences and the machine
agree on every term of the fragment; and a general theorem
that erasing the coefficients of the nested machine gives the ordinary native answers
(`native_answers_erasure` states it for the settled source; here it is checked on each
specimen, `erase_is_ordinary_run`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationNeed (Program Outcome)
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateGrades (Row)
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeControls (integer call resultValues)
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedControls
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Core.InferenceControl (WorkOccurrence)
open Mettapedia.PLN.Evidence (BinEvNat)
open Mettapedia.PLN.Bridges.Languages.NativeGradedEvidence

/-! ## Terms, specimens and the native run -/

/-- **The source terms of the specimens**: an integer, a call of stored rows without
parameters, and a call of stored rows with one parameter. -/
inductive GradedTerm where
  | int (value : Int)
  | stored (head : String)
  | apply (head : String) (argument : GradedTerm)
  deriving DecidableEq, Repr

/-- The atom of a term. -/
def GradedTerm.toAtom : GradedTerm → Atom
  | .int value => integer value
  | .stored head => call head
  | .apply head argument => call head [argument.toAtom]

/-- **A graded specimen**: stored rows, the grade annotation of each row, how the algebra reads
a returned grade, an optional admission of grades, a term and a budget. -/
structure Specimen (V : Type) where
  program : Program
  annotation : Row → Option Atom
  read : Outcome → Option V
  admission : Option (V → Bool)
  term : GradedTerm
  fuel : Nat

variable {V : Type}

/-- The native machine of a specimen: nested coefficient continuations, under its admission
when it declares one. -/
def Specimen.source [Monoid V] (specimen : Specimen V) :
    WeightedBranchingResumption.Coalgebra NestedWork NestedResult V :=
  match specimen.admission with
  | none => nestedSource specimen.program specimen.annotation specimen.read
  | some test => nestedAdmittedSource specimen.program specimen.annotation specimen.read test

/-- **What runs**: the completed values of the native run, each with its coefficient, one
entry for each physical occurrence. -/
def Specimen.nativeBag [Monoid V] (specimen : Specimen V) :
    WeightedResumption.Contributions Atom V :=
  completedValues (WeightedBranchingResumption.contributions specimen.source specimen.fuel
    (.inl (WorkOccurrence.root (NativeEquationNeed.initial specimen.term.toAtom))))

/-! ## Annotated occurrences over the stored rows -/

/-- Replace a parameter by a value. -/
def bindParameter (name : String) (value : Atom) : Atom → Atom
  | .var other => if other = name then value else .var other
  | .expression items => .expression (bindParameterList name value items)
  | other => other
where
  /-- Replace a parameter by a value in a list of atoms. -/
  bindParameterList (name : String) (value : Atom) : List Atom → List Atom
    | [] => []
    | item :: rest => bindParameter name value item :: bindParameterList name value rest

/-- Whether an atom uses a parameter. -/
def mentions (name : String) : Atom → Bool
  | .var other => other == name
  | .expression items => mentionsList name items
  | _ => false
where
  /-- Whether a list of atoms uses a parameter. -/
  mentionsList (name : String) : List Atom → Bool
    | [] => false
    | item :: rest => mentions name item || mentionsList name rest

/-- **A charge**: a stored row selected by an occurrence, with the grade its annotation
contributes at that invocation. -/
structure Charge (V : Type) where
  row : Nat
  grade : V
  deriving DecidableEq, Repr

/-- **An annotated occurrence**: the value returned and the rows charged, in the order in which
they are charged. -/
structure AnnotatedOccurrence (V : Type) where
  value : Atom
  charges : List (Charge V)
  deriving DecidableEq, Repr

/-- Whether the specimen's admission accepts a grade. -/
def Specimen.accepts (specimen : Specimen V) (grade : V) : Bool :=
  match specimen.admission with
  | none => true
  | some test => test grade

/-- The charge of one invocation of a stored row: nothing when the row has no grade; the
grade its annotation reads, with the parameter bound, when the algebra reads it and the
admission accepts it. `none` when the invocation does not complete. -/
def Specimen.charge (specimen : Specimen V) (index : Nat) (body : Atom)
    (binding : Atom → Atom) : Option (List (Charge V)) :=
  match specimen.annotation ⟨index, body, []⟩ with
  | none => some []
  | some grade =>
      match specimen.read (.value (binding grade)) with
      | some value => if specimen.accepts value then some [⟨index, value⟩] else none
      | none => none

/-- **The annotated occurrences of a term**: each stored row of the called head, in order; the
argument is selected once, shared by every use of the parameter, and selected only when the
body or the grade uses it. The charges are in the order of demand: an argument that the grade
uses is charged before the row, otherwise after it. -/
def Specimen.occurrences (specimen : Specimen V) : GradedTerm → List (AnnotatedOccurrence V)
  | .int value => [⟨integer value, []⟩]
  | .stored head =>
      specimen.program.zipIdx.filterMap fun (equation, index) =>
        if equation.head = head ∧ equation.parameters = [] then
          (specimen.charge index equation.body id).map fun charges => ⟨equation.body, charges⟩
        else none
  | .apply head argument =>
      let inner := specimen.occurrences argument
      specimen.program.zipIdx.flatMap fun (equation, index) =>
        match equation.parameters with
        | [name] =>
            if equation.head = head then
              let graded := (specimen.annotation ⟨index, equation.body, []⟩).any (mentions name)
              if graded || mentions name equation.body then
                inner.filterMap fun selected =>
                  (specimen.charge index equation.body
                      (bindParameter name selected.value)).map fun own =>
                    ⟨bindParameter name selected.value equation.body,
                      if graded then selected.charges ++ own else own ++ selected.charges⟩
              else
                ((specimen.charge index equation.body id).map fun own =>
                  (⟨equation.body, own⟩ : AnnotatedOccurrence V)).toList
            else []
        | _ => []

/-- **The middle face**: the annotated occurrences of the specimen's term. This is not a
typing judgment. -/
def Specimen.annotate (specimen : Specimen V) : List (AnnotatedOccurrence V) :=
  specimen.occurrences specimen.term

/-- A charge of a completed invocation names the invocation's row, which has a grade, and the
admission accepts its grade. -/
theorem Specimen.charge_mem {specimen : Specimen V} {index : Nat} {body : Atom}
    {binding : Atom → Atom} {charges : List (Charge V)}
    (charged : specimen.charge index body binding = some charges) {charge : Charge V}
    (member : charge ∈ charges) :
    charge.row = index ∧ (specimen.annotation ⟨index, body, []⟩).isSome = true ∧
      specimen.accepts charge.grade = true := by
  unfold Specimen.charge at charged
  split at charged
  · cases charged
    simp at member
  · rename_i grade annotated
    split at charged
    · split at charged
      · rename_i admitted
        cases charged
        rw [List.mem_singleton] at member
        subst member
        exact ⟨rfl, by simp [annotated], admitted⟩
      · cases charged
    · cases charged

/-- **Every charge of an annotated occurrence is a stored row of the program**, which its
annotation grades, with a grade that the admission accepts. -/
theorem Specimen.charges_stored (specimen : Specimen V) : ∀ term : GradedTerm,
    ∀ selected ∈ specimen.occurrences term, ∀ charge ∈ selected.charges,
      ∃ equation, specimen.program[charge.row]? = some equation ∧
        (specimen.annotation ⟨charge.row, equation.body, []⟩).isSome = true ∧
        specimen.accepts charge.grade = true
  | .int _ => by
      intro selected member charge charged
      simp only [Specimen.occurrences, List.mem_singleton] at member
      subst member
      simp at charged
  | .stored head => by
      intro selected member charge charged
      simp only [Specimen.occurrences, List.mem_filterMap] at member
      obtain ⟨⟨equation, index⟩, entry, produced⟩ := member
      split at produced
      · obtain ⟨charges, chargedAt, rfl⟩ := Option.map_eq_some_iff.mp produced
        obtain ⟨rfl, annotated, admitted⟩ := Specimen.charge_mem chargedAt charged
        exact ⟨equation, List.mem_zipIdx_iff_getElem?.mp entry, annotated, admitted⟩
      · cases produced
  | .apply head argument => by
      have inner := specimen.charges_stored argument
      intro selected member charge charged
      simp only [Specimen.occurrences, List.mem_flatMap] at member
      obtain ⟨⟨equation, index⟩, entry, produced⟩ := member
      have stored := List.mem_zipIdx_iff_getElem?.mp entry
      split at produced
      · split at produced
        · split at produced
          · obtain ⟨previous, previousMember, own⟩ := List.mem_filterMap.mp produced
            obtain ⟨charges, chargedAt, rfl⟩ := Option.map_eq_some_iff.mp own
            have fromParts : charge ∈ previous.charges ∨ charge ∈ charges := by
              dsimp only at charged
              split at charged
              · exact List.mem_append.mp charged
              · exact (List.mem_append.mp charged).symm
            rcases fromParts with fromArgument | fromRow
            · exact inner previous previousMember charge fromArgument
            · obtain ⟨rfl, annotated, admitted⟩ := Specimen.charge_mem chargedAt fromRow
              exact ⟨equation, stored, annotated, admitted⟩
          · obtain ⟨charges, chargedAt, rfl⟩ :=
              Option.map_eq_some_iff.mp (Option.mem_toList.mp produced)
            obtain ⟨rfl, annotated, admitted⟩ := Specimen.charge_mem chargedAt charged
            exact ⟨equation, stored, annotated, admitted⟩
        · cases produced
      · cases produced

/-- **The meaning**: the weighted bag, one entry for each annotated occurrence, with its value
and the product of its grades. -/
def weigh [Monoid V] (occurrences : List (AnnotatedOccurrence V)) :
    WeightedResumption.Contributions Atom V :=
  occurrences.map fun selected => (selected.value, (selected.charges.map Charge.grade).prod)

/-- An annotated occurrence with each grade read in another algebra. -/
def AnnotatedOccurrence.regrade {W : Type} (change : V → W) (selected : AnnotatedOccurrence V) :
    AnnotatedOccurrence W :=
  ⟨selected.value, selected.charges.map fun charge => ⟨charge.row, change charge.grade⟩⟩

/-- **The meaning commutes with a change of algebra**: reading each grade through a monoid
homomorphism and then weighing is weighing and then reading each coefficient through it. -/
theorem weigh_regrade {W : Type} [Monoid V] [Monoid W] (change : V →* W)
    (occurrences : List (AnnotatedOccurrence V)) :
    weigh (occurrences.map (AnnotatedOccurrence.regrade change)) =
      WeightedResumption.mapCoefficients change (weigh occurrences) := by
  simp [weigh, AnnotatedOccurrence.regrade, WeightedResumption.mapCoefficients, map_list_prod,
    Function.comp_def]

/-- **The triangle of a family of specimens**: what runs is annotated by its occurrences, the
occurrences mean their weighted bag, and the direct map runs the machine. -/
def gradedTriangle [Monoid V] {Index : Type} (specimen : Index → Specimen V)
    (agree : ∀ index, weigh (specimen index).annotate = (specimen index).nativeBag) :
    Mettapedia.Computability.ComputationalTrinity.Comparison.{0, 0, 0} Closed :=
  triangleOfThree (fun index => (specimen index).annotate) weigh
    (fun index => (specimen index).nativeBag) agree

/-! ## The number specimens -/

/-- The returned pair of a value with itself. -/
def pairOf (value : Int) : Atom := call "Pair" [integer value, integer value]

/-- `(paired (weigh-by-self (coin)))`. -/
def pairTerm : GradedTerm := .apply "paired" (.apply "weigh-by-self" (.stored "coin"))

/-- `(id (id 7))`. -/
def nestedTerm : GradedTerm := .apply "id" (.apply "id" (.int 7))

/-- The shared pair with one stored row of `2`: the duplicate row of the specimen left out. -/
def singlePairProgram : Program :=
  [⟨"coin", [], integer 2⟩, ⟨"coin", [], integer 5⟩,
   ⟨"weigh-by-self", ["x"], .var "x"⟩, ⟨"paired", ["x"], call "Pair" [.var "x", .var "x"]⟩]

/-- The grades of `singlePairProgram`: `3` and `7` on the coin rows, `$x` on the identity. -/
def singlePairAnnotation (row : Row) : Option Atom :=
  if row.index = 0 then some (integer 3)
  else if row.index = 1 then some (integer 7)
  else if row.index = 2 then some (.var "x")
  else none

/-- The grade `$x` on the row `constant` of the identity program, and no other grade. -/
def gradeOnlyAnnotation (row : Row) : Option Atom :=
  if row.index = 3 then some (.var "x") else none

/-- **The number specimens**: the shared pair, the same pair with one stored row of `2`, the
nested identity with grade `$x`, with literal grade `2`, the single identity with unit grade,
a grade that alone uses the argument, and the identity applied to the coin. -/
inductive NumberSpecimen where
  | sharedPair
  | singlePair
  | nestedSelf
  | nestedLiteral
  | unitOnce
  | gradeOnly
  | coinThroughId
  deriving DecidableEq, Repr

/-- The specimen of each index, over natural grades. -/
def numberSpecimen : NumberSpecimen → Specimen Nat
  | .sharedPair => ⟨sharedIdentityProgram, sharedIdentityAnnotation, naturalCoefficient, none,
      pairTerm, 400⟩
  | .singlePair => ⟨singlePairProgram, singlePairAnnotation, naturalCoefficient, none,
      pairTerm, 400⟩
  | .nestedSelf => ⟨identityProgram, identityAnnotation (.var "x"), naturalCoefficient, none,
      nestedTerm, 300⟩
  | .nestedLiteral => ⟨identityProgram, identityAnnotation (integer 2), naturalCoefficient,
      none, nestedTerm, 300⟩
  | .unitOnce => ⟨identityProgram, identityAnnotation (integer 1), naturalCoefficient, none,
      .apply "id" (.int 7), 300⟩
  | .gradeOnly => ⟨identityProgram, gradeOnlyAnnotation, naturalCoefficient, none,
      .apply "constant" (.int 9), 300⟩
  | .coinThroughId => ⟨identityProgram, gradedCoinAnnotation, naturalCoefficient, none,
      .apply "id" (.stored "coin"), 300⟩

/-! ### Running: the cited runs, and one new run -/

theorem sharedPair_native : (numberSpecimen .sharedPair).nativeBag =
    [(pairOf 2, 6), (pairOf 2, 6), (pairOf 5, 35)] :=
  shared_identity_values

/-- **New run**: with one stored row of `2`, the pair `(Pair 2 2)` occurs once. -/
theorem singlePair_native : (numberSpecimen .singlePair).nativeBag =
    [(pairOf 2, 6), (pairOf 5, 35)] := by
  decide +kernel

theorem nestedSelf_native : (numberSpecimen .nestedSelf).nativeBag = [(integer 7, 49)] :=
  nested_grade_forcing_retains_inner_factor

theorem nestedLiteral_native : (numberSpecimen .nestedLiteral).nativeBag = [(integer 7, 4)] :=
  graded_identity_constant_composes

theorem unitOnce_native : (numberSpecimen .unitOnce).nativeBag = [(integer 7, 1)] :=
  graded_identity_unit

theorem gradeOnly_native : (numberSpecimen .gradeOnly).nativeBag = [(integer 7, 9)] :=
  grade_only_binding_survives

theorem coinThroughId_native :
    (numberSpecimen .coinThroughId).nativeBag = [(integer 0, 0), (integer 1, 3)] :=
  nested_grade_keeps_argument_factor

/-! ### Annotated occurrences -/

/-- Positive example: **the annotated rows of the shared pair** are the coin rows `0`, `1` and
`2`, each charged once with its grade, followed by the identity row `3`, charged once with the
coin's value. -/
theorem sharedPair_annotated : (numberSpecimen .sharedPair).annotate =
    [⟨pairOf 2, [⟨0, 3⟩, ⟨3, 2⟩]⟩, ⟨pairOf 2, [⟨1, 3⟩, ⟨3, 2⟩]⟩,
     ⟨pairOf 5, [⟨2, 7⟩, ⟨3, 5⟩]⟩] := by
  decide +kernel

/-- The nested identity with grade `$x` charges the identity row twice, once per invocation,
the inner one first. -/
theorem nestedSelf_annotated : (numberSpecimen .nestedSelf).annotate =
    [⟨integer 7, [⟨2, 7⟩, ⟨2, 7⟩]⟩] := by
  decide +kernel

/-- Positive example: the coin row `0` has no grade and the value `0`; the identity's grade
on it is `0`, and the occurrence stays. -/
theorem coinThroughId_annotated : (numberSpecimen .coinThroughId).annotate =
    [⟨integer 0, [⟨2, 0⟩]⟩, ⟨integer 1, [⟨1, 3⟩, ⟨2, 1⟩]⟩] := by
  decide +kernel

theorem sharedPair_weigh : weigh (numberSpecimen .sharedPair).annotate =
    [(pairOf 2, 6), (pairOf 2, 6), (pairOf 5, 35)] := by
  decide +kernel

theorem singlePair_weigh : weigh (numberSpecimen .singlePair).annotate =
    [(pairOf 2, 6), (pairOf 5, 35)] := by
  decide +kernel

theorem nestedSelf_weigh : weigh (numberSpecimen .nestedSelf).annotate = [(integer 7, 49)] := by
  decide +kernel

theorem nestedLiteral_weigh :
    weigh (numberSpecimen .nestedLiteral).annotate = [(integer 7, 4)] := by
  decide +kernel

theorem unitOnce_weigh : weigh (numberSpecimen .unitOnce).annotate = [(integer 7, 1)] := by
  decide +kernel

theorem gradeOnly_weigh : weigh (numberSpecimen .gradeOnly).annotate = [(integer 7, 9)] := by
  decide +kernel

theorem coinThroughId_weigh :
    weigh (numberSpecimen .coinThroughId).annotate = [(integer 0, 0), (integer 1, 3)] := by
  decide +kernel

/-! ### The number triangle -/

/-- **The two ways to the weighted bag agree** on every number specimen: the bag of the
annotated occurrences is the bag the machine runs to. -/
theorem numberAgree : ∀ index,
    weigh (numberSpecimen index).annotate = (numberSpecimen index).nativeBag
  | .sharedPair => sharedPair_weigh.trans sharedPair_native.symm
  | .singlePair => singlePair_weigh.trans singlePair_native.symm
  | .nestedSelf => nestedSelf_weigh.trans nestedSelf_native.symm
  | .nestedLiteral => nestedLiteral_weigh.trans nestedLiteral_native.symm
  | .unitOnce => unitOnce_weigh.trans unitOnce_native.symm
  | .gradeOnly => gradeOnly_weigh.trans gradeOnly_native.symm
  | .coinThroughId => coinThroughId_weigh.trans coinThroughId_native.symm

/-- **The triangle of the number specimens.** -/
def numberTriangle : Mettapedia.Computability.ComputationalTrinity.Comparison.{0, 0, 0} Closed :=
  gradedTriangle numberSpecimen numberAgree

/-- The direct map of the triangle is the native run. -/
theorem numberTriangle_direct (index : NumberSpecimen) :
    numberTriangle.programToSpace.app
        (Opposite.op (_root_.CategoryTheory.Discrete.mk PUnit.unit)) index =
      (numberSpecimen index).nativeBag :=
  rfl

/-! ## What each map forgets -/

/-- **Value erasure**: the values of a bag, in order, without their coefficients. -/
def erase (bag : WeightedResumption.Contributions Atom V) : List Atom := bag.map Prod.fst

/-- **The set of values** of a bag. -/
def valueSet (bag : WeightedResumption.Contributions Atom V) : Finset Atom :=
  (bag.map Prod.fst).toFinset

/-- The number triangle read through value erasure. -/
def erasedTriangle : Mettapedia.Computability.ComputationalTrinity.Comparison.{0, 0, 0} Closed :=
  triangleOfThree (fun index => (numberSpecimen index).annotate)
    (fun annotated => erase (weigh annotated))
    (fun index => erase (numberSpecimen index).nativeBag)
    fun index => congrArg erase (numberAgree index)

/-- The number triangle read as sets of values. -/
def valueSetTriangle :
    Mettapedia.Computability.ComputationalTrinity.Comparison.{0, 0, 0} Closed :=
  triangleOfThree (fun index => (numberSpecimen index).annotate)
    (fun annotated => valueSet (weigh annotated))
    (fun index => valueSet (numberSpecimen index).nativeBag)
    fun index => congrArg valueSet (numberAgree index)

/-- **`weigh-by-self` is an identity of values, not of the weighted reading.** The nested
identity with grade `$x`, with literal grade `2`, and the single identity with unit grade all
erase to `[7]`; their weighted bags are `49`, `4` and `1`, pairwise different. -/
theorem graded_identity_is_identity_of_values :
    erase (numberSpecimen .nestedSelf).nativeBag = [integer 7] ∧
    erase (numberSpecimen .nestedLiteral).nativeBag = [integer 7] ∧
    erase (numberSpecimen .unitOnce).nativeBag = [integer 7] ∧
    (numberSpecimen .nestedSelf).nativeBag ≠ (numberSpecimen .nestedLiteral).nativeBag ∧
    (numberSpecimen .nestedSelf).nativeBag ≠ (numberSpecimen .unitOnce).nativeBag ∧
    (numberSpecimen .nestedLiteral).nativeBag ≠ (numberSpecimen .unitOnce).nativeBag := by
  rw [nestedSelf_native, nestedLiteral_native, unitOnce_native]
  decide +kernel

/-- **Value erasure loses the coefficients**: two different specimens, one erased value
list. -/
theorem erasedTriangle_loses : erasedTriangle.LosesProgramInformation :=
  triangleOfThree_loses _ _ _ _ (left := .nestedSelf) (right := .nestedLiteral) (by decide)
    (graded_identity_is_identity_of_values.1.trans
      graded_identity_is_identity_of_values.2.1.symm)

/-- **Value erasure is the ordinary run.** Erasing the coefficients of each number specimen's
weighted run gives the values of the ordinary native run of the same stored rows, which
ignores every grade; there `weigh-by-self` returns its argument. -/
theorem erase_is_ordinary_run : ∀ index : NumberSpecimen,
    erase (numberSpecimen index).nativeBag =
      resultValues (Mettapedia.Machines.BranchLocalNeed.NeedReference.answers
        (NativeEquationNeed.specification (numberSpecimen index).program) 400
        (NativeEquationNeed.initial (numberSpecimen index).term.toAtom))
  | .sharedPair => by rw [sharedPair_native]; decide +kernel
  | .singlePair => by rw [singlePair_native]; decide +kernel
  | .nestedSelf => by rw [nestedSelf_native]; decide +kernel
  | .nestedLiteral => by rw [nestedLiteral_native]; decide +kernel
  | .unitOnce => by rw [unitOnce_native]; decide +kernel
  | .gradeOnly => by rw [gradeOnly_native]; decide +kernel
  | .coinThroughId => by rw [coinThroughId_native]; decide +kernel

/-- The bag of the one-level scoring of `(id (id 7))` with grade `$x`. -/
def oneLevelBag : WeightedResumption.Contributions Atom Nat :=
  pendingValues (WeightedBranchingResumption.contributions
    (pendingSource identityProgram (identityAnnotation (.var "x")) naturalCoefficient)
    300 (.inl (WorkOccurrence.root (NativeEquationNeed.initial nestedIdentityTerm))))

/-- **The nested gap**: the one-level scoring and the nested reading return the same value
`7`; their coefficients are `7` and `49`. -/
theorem one_level_scoring_erases_alike :
    erase oneLevelBag = erase (numberSpecimen .nestedSelf).nativeBag ∧
    oneLevelBag ≠ (numberSpecimen .nestedSelf).nativeBag := by
  rw [show oneLevelBag = [(integer 7, 7)] from ordinary_scoring_loses_nested_factor.1,
    nestedSelf_native]
  decide +kernel

/-- **Two rows of `(Pair 2 2)`**: the annotated occurrences keep the coin rows `0` and `1`,
which are two different occurrences; the bag keeps two entries `(Pair 2 2, 6)`; the set of
values has two elements for three occurrences. -/
theorem pair_two_two_twice :
    ((numberSpecimen .sharedPair).annotate.filter fun selected => selected.value = pairOf 2).map
        (fun selected => selected.charges.map Charge.row) = [[0, 3], [1, 3]] ∧
    (numberSpecimen .sharedPair).nativeBag.count (pairOf 2, 6) = 2 ∧
    (valueSet (numberSpecimen .sharedPair).nativeBag).card = 2 := by
  rw [sharedPair_annotated, sharedPair_native]
  decide +kernel

/-- **The set of values loses multiplicity**: three stored rows and two stored rows give one
set of values, while their bags differ. -/
theorem valueSetTriangle_loses : valueSetTriangle.LosesProgramInformation :=
  triangleOfThree_loses _ _ _ _ (left := .sharedPair) (right := .singlePair) (by decide)
    (by
      show valueSet (numberSpecimen .sharedPair).nativeBag =
        valueSet (numberSpecimen .singlePair).nativeBag
      rw [sharedPair_native, singlePair_native]
      decide +kernel)

/-- The bags of the three-row and the two-row pair differ. -/
theorem sharedPair_ne_singlePair :
    (numberSpecimen .sharedPair).nativeBag ≠ (numberSpecimen .singlePair).nativeBag := by
  rw [sharedPair_native, singlePair_native]
  decide +kernel

/-- **One entry for each value**: the bag with the other entries of the same value dropped. -/
def onePerValue (bag : WeightedResumption.Contributions Atom V) :
    WeightedResumption.Contributions Atom V :=
  bag.pwFilter fun left right => left.1 ≠ right.1

/-- Negative example: **read one entry per value, the run loses an occurrence, and the three
maps form no triangle.** The two rows of `(Pair 2 2)` become one; the annotated occurrences
keep both. -/
theorem onePerValue_disagrees :
    ¬ ∀ index, weigh (numberSpecimen index).annotate =
      onePerValue (numberSpecimen index).nativeBag := by
  intro agree
  have shared := agree .sharedPair
  rw [sharedPair_weigh, sharedPair_native] at shared
  exact absurd shared (by decide +kernel)

/-- **A duplicated factor**: the grade of every row that `duplicated` picks is charged twice,
every other grade once. -/
def weighDuplicating [Monoid V] (duplicated : Nat → Bool)
    (occurrences : List (AnnotatedOccurrence V)) : WeightedResumption.Contributions Atom V :=
  occurrences.map fun occurrence =>
    (occurrence.value, (occurrence.charges.map fun charge =>
      if duplicated charge.row then charge.grade * charge.grade else charge.grade).prod)

/-- Duplicating no factor is the meaning. -/
theorem weighDuplicating_none [Monoid V] (occurrences : List (AnnotatedOccurrence V)) :
    weighDuplicating (fun _ => false) occurrences = weigh occurrences := by
  simp [weighDuplicating, weigh]

/-- The identity row `3` of the shared pair's program: the identity factor. -/
def identityRow (row : Nat) : Bool := row == 3

/-- The coin rows `0`, `1` and `2` of the shared pair's program: the coin factor. -/
def coinRow (row : Nat) : Bool := decide (row < 3)

/-- The rows of the producer `(weigh-by-self (coin))`: its whole ledger, coin and identity. -/
def producerRow (row : Nat) : Bool := coinRow row || identityRow row

/-- **Charging once is part of the meaning**: the machine charges the coin factor and the
identity factor once each, `3 * 2 = 6` twice and `7 * 5 = 35`. -/
theorem charged_once : (numberSpecimen .sharedPair).nativeBag.map Prod.snd = [6, 6, 35] :=
  shared_identity_factors_charged_once

/-- **Duplicating only the identity factor** gives `3 * 2 * 2 = 12` and `7 * 5 * 5 = 175`, which
is not the run. -/
theorem duplicate_identity_factor :
    (weighDuplicating identityRow (numberSpecimen .sharedPair).annotate).map Prod.snd =
      [12, 12, 175] ∧
    weighDuplicating identityRow (numberSpecimen .sharedPair).annotate ≠
      (numberSpecimen .sharedPair).nativeBag := by
  rw [sharedPair_annotated, sharedPair_native]
  decide +kernel

/-- **Duplicating only the coin factor** gives `3 * 3 * 2 = 18` and `7 * 7 * 5 = 245`, which is
not the run. -/
theorem duplicate_coin_factor :
    (weighDuplicating coinRow (numberSpecimen .sharedPair).annotate).map Prod.snd =
      [18, 18, 245] ∧
    weighDuplicating coinRow (numberSpecimen .sharedPair).annotate ≠
      (numberSpecimen .sharedPair).nativeBag := by
  rw [sharedPair_annotated, sharedPair_native]
  decide +kernel

/-- **Duplicating the producer's whole ledger at the same selected value** gives
`(3 * 2) * (3 * 2) = 36` and `(7 * 5) * (7 * 5) = 1225`, which is not the run. Rerunning
independent producers is a different program again: each use may select a different coin and
form a mixed pair, which the run never does (`no_mixed_pair`). -/
theorem duplicate_producer_ledger :
    (weighDuplicating producerRow (numberSpecimen .sharedPair).annotate).map Prod.snd =
      [36, 36, 1225] ∧
    weighDuplicating producerRow (numberSpecimen .sharedPair).annotate ≠
      (numberSpecimen .sharedPair).nativeBag := by
  rw [sharedPair_annotated, sharedPair_native]
  decide +kernel

/-- **The per-value sum**: one entry for each value, with the sum of its coefficients. -/
def perValue [AddCommMonoid V] (bag : WeightedResumption.Contributions Atom V) :
    WeightedResumption.Contributions Atom V :=
  (bag.map Prod.fst).dedup.map fun value =>
    (value, WeightedResumption.total (bag.filter fun entry => entry.1 = value))

/-- **The per-value sum and the linear total identify the two rows of `6`** with one row of
`12`; the bag keeps them apart. -/
theorem linear_total_identifies_rows :
    perValue (numberSpecimen .sharedPair).nativeBag = [(pairOf 2, 12), (pairOf 5, 35)] ∧
    perValue (numberSpecimen .sharedPair).nativeBag =
      perValue [(pairOf 2, 12), (pairOf 5, 35)] ∧
    WeightedResumption.total (numberSpecimen .sharedPair).nativeBag = 47 ∧
    WeightedResumption.total [(pairOf 2, 12), (pairOf 5, 35)] = 47 ∧
    (numberSpecimen .sharedPair).nativeBag ≠ [(pairOf 2, 12), (pairOf 5, 35)] := by
  rw [sharedPair_native]
  decide +kernel

/-- Negative example: **no mixed pair**, among the annotated occurrences and in the run. -/
theorem no_mixed_pair :
    (∀ selected ∈ (numberSpecimen .sharedPair).annotate,
      selected.value ≠ call "Pair" [integer 2, integer 5] ∧
        selected.value ≠ call "Pair" [integer 5, integer 2]) ∧
    ∀ coefficient,
      (call "Pair" [integer 2, integer 5], coefficient) ∉
          (numberSpecimen .sharedPair).nativeBag ∧
        (call "Pair" [integer 5, integer 2], coefficient) ∉
          (numberSpecimen .sharedPair).nativeBag := by
  refine ⟨?_, shared_identity_excludes_mixed_pairs⟩
  rw [sharedPair_annotated]
  decide +kernel

/-! ## The evidence packet on the same rows -/

/-- **The evidence specimens**: the shared pair under positive admission, and the nested
literal identity with grade `(evidence 2 1)` under positive admission. -/
inductive EvidenceSpecimen where
  | sharedPair
  | nestedLiteral
  deriving DecidableEq, Repr

/-- The specimen of each index, over evidence counts. -/
def evidenceSpecimen : EvidenceSpecimen → Specimen BinEvNat
  | .sharedPair => ⟨sharedIdentityProgram, sharedCountAnnotation, countCoefficient,
      some countAdmission, pairTerm, 300⟩
  | .nestedLiteral => ⟨identityProgram, identityAnnotation (evidenceLiteral 2 1),
      countCoefficient, some countAdmission, nestedTerm, 300⟩

theorem evidenceShared_native : (evidenceSpecimen .sharedPair).nativeBag =
    [(pairOf 2, ⟨6, 1⟩), (pairOf 2, ⟨6, 1⟩), (pairOf 5, ⟨35, 1⟩)] :=
  graded_evidence_identity_shares_choice

/-- **New run**: the literal evidence grade `(evidence 2 1)`, invoked twice, gives
`(evidence 4 1)`; the value stays `7`. Beside it, the number law with grade `2` gives `4`
(`graded_identity_constant_composes`). -/
theorem literalEvidence_native :
    (evidenceSpecimen .nestedLiteral).nativeBag = [(integer 7, ⟨4, 1⟩)] := by
  decide +kernel

theorem evidenceShared_weigh : weigh (evidenceSpecimen .sharedPair).annotate =
    [(pairOf 2, ⟨6, 1⟩), (pairOf 2, ⟨6, 1⟩), (pairOf 5, ⟨35, 1⟩)] := by
  decide +kernel

theorem literalEvidence_weigh :
    weigh (evidenceSpecimen .nestedLiteral).annotate = [(integer 7, ⟨4, 1⟩)] := by
  decide +kernel

/-- **The two ways to the evidence bag agree** on both specimens. -/
theorem evidenceAgree : ∀ index,
    weigh (evidenceSpecimen index).annotate = (evidenceSpecimen index).nativeBag
  | .sharedPair => evidenceShared_weigh.trans evidenceShared_native.symm
  | .nestedLiteral => literalEvidence_weigh.trans literalEvidence_native.symm

/-- **The triangle of the evidence specimens.** -/
def evidenceTriangle :
    Mettapedia.Computability.ComputationalTrinity.Comparison.{0, 0, 0} Closed :=
  gradedTriangle evidenceSpecimen evidenceAgree

/-- A natural count `n` read as the evidence `(evidence n 1)`. -/
def countGrade : Nat →* BinEvNat where
  toFun count := ⟨count, 1⟩
  map_one' := rfl
  map_mul' _ _ := BinEvNat.ext rfl rfl

/-- The number specimen whose grades the evidence specimen reads as counts. -/
def EvidenceSpecimen.counted : EvidenceSpecimen → NumberSpecimen
  | .sharedPair => .sharedPair
  | .nestedLiteral => .nestedLiteral

/-- **The same annotated rows**: the evidence occurrences charge the same rows as the number
occurrences, each grade `n` read as `(evidence n 1)`. -/
theorem evidence_annotated_is_count_image : ∀ index : EvidenceSpecimen,
    (evidenceSpecimen index).annotate =
      (numberSpecimen index.counted).annotate.map (AnnotatedOccurrence.regrade countGrade)
  | .sharedPair => by decide +kernel
  | .nestedLiteral => by decide +kernel

/-- **The evidence bag is the number bag** with each coefficient `n` read as `(evidence n 1)`:
`(evidence 6 1)` twice and `(evidence 35 1)` beside `6`, `6` and `35`, and `(evidence 4 1)`
beside `4`. The proof goes through the two triangles and the annotated rows, not through a
run. -/
theorem evidence_bag_is_count_image (index : EvidenceSpecimen) :
    (evidenceSpecimen index).nativeBag =
      WeightedResumption.mapCoefficients countGrade (numberSpecimen index.counted).nativeBag := by
  rw [← evidenceAgree, ← numberAgree, evidence_annotated_is_count_image, weigh_regrade]

/-- The two rows of `(Pair 2 2)` stay two evidence entries. -/
theorem evidence_pair_two_two_twice :
    (evidenceSpecimen .sharedPair).nativeBag.count (pairOf 2, ⟨6, 1⟩) = 2 := by
  rw [evidenceShared_native]
  decide +kernel

/-! ## Controls outside the triangles -/

/-- The inner zero grade under the outer grade `$x`, attached and under a nonzero guard. -/
def zeroSpecimen (guarded : Bool) : Specimen Nat :=
  ⟨orderedIdentityProgram,
    fun row => if row.index = 2 then some (integer 0)
      else if row.index = 4 then some (.var "x") else none,
    naturalCoefficient, some fun value => !guarded || value != 0,
    .apply "outer" (.apply "id" (.int 7)), 300⟩

/-- **Zero**: attachment keeps the occurrence with coefficient `0`; a nonzero guard refuses it.
The annotated occurrences agree with the machine on both. The settled machine keeps zero captures as
occurrences as well (`zero_capture_retains_occurrences`). -/
theorem zero_controls_agree :
    weigh (zeroSpecimen false).annotate = (zeroSpecimen false).nativeBag ∧
    weigh (zeroSpecimen true).annotate = (zeroSpecimen true).nativeBag ∧
    (zeroSpecimen false).nativeBag = [(integer 7, 0)] ∧
    (zeroSpecimen true).nativeBag = [] := by
  have attached : (zeroSpecimen false).nativeBag = [(integer 7, 0)] :=
    nested_zero_attachment_and_guard_differ.1
  have guarded : (zeroSpecimen true).nativeBag = [] := by
    show completedValues (nestedZeroRun true) = []
    rw [nested_zero_attachment_and_guard_differ.2]
    rfl
  rw [attached, guarded]
  exact ⟨by decide +kernel, by decide +kernel, rfl, rfl⟩

/-- **Positive admission of a coefficient is admission of each of its grades**
(`count_admission_tensor`), so testing each charge, as the machine does, is testing the
product. Nonzero admission has no such law: two nonzero packets multiply to zero
(`polarity_controls_agree`). -/
theorem countAdmission_prod (grades : List BinEvNat) :
    countAdmission grades.prod = grades.all countAdmission := by
  induction grades with
  | nil => exact count_admission_zero_and_one.2
  | cons grade rest ih => rw [List.prod_cons, count_admission_tensor, ih, List.all_cons]

/-- Opposite evidence polarities on the inner and the outer identity. -/
def polaritySpecimen (admission : BinEvNat → Bool) : Specimen BinEvNat :=
  ⟨orderedIdentityProgram,
    fun row => if row.index = 2 then some (evidenceLiteral 1 0)
      else if row.index = 4 then some (evidenceLiteral 0 1) else none,
    countCoefficient, some admission, .apply "outer" (.apply "id" (.int 7)), 300⟩

/-- **Polarity**: nonzero admission accepts both polarities and returns a zero packet;
positive admission refuses the counter-only outer grade. The annotated occurrences agree with
the machine on both. -/
theorem polarity_controls_agree :
    weigh (polaritySpecimen fun value => value != 0).annotate =
        (polaritySpecimen fun value => value != 0).nativeBag ∧
    weigh (polaritySpecimen countAdmission).annotate =
      (polaritySpecimen countAdmission).nativeBag ∧
    (polaritySpecimen fun value => value != 0).nativeBag = [(integer 7, 0)] ∧
    (polaritySpecimen countAdmission).nativeBag = [] := by
  have nonzero : (polaritySpecimen fun value => value != 0).nativeBag = [(integer 7, 0)] :=
    nonzero_packet_admission_breaks_tensor_support.1
  have positive : (polaritySpecimen countAdmission).nativeBag = [] := by
    show completedValues (polarityRun countAdmission) = []
    rw [nonzero_packet_admission_breaks_tensor_support.2]
    rfl
  rw [nonzero, positive]
  exact ⟨by decide +kernel, by decide +kernel, rfl, rfl⟩

/-- Free words expose the order of factors. -/
local instance : DecidableEq (FreeMonoid String) :=
  inferInstanceAs (DecidableEq (List String))

/-- The inner grade `2` read as the word `inner`, the outer grade read as `outer`: `$x` when
the outer grade uses the argument, the literal `7` otherwise. -/
def orderSpecimen (forceArgument : Bool) : Specimen (FreeMonoid String) :=
  ⟨orderedIdentityProgram,
    fun row => if row.index = 2 then some (integer 2)
      else if row.index = 4 then some (if forceArgument then .var "x" else integer 7) else none,
    orderedCoefficient, none, .apply "outer" (.apply "id" (.int 7)), 300⟩

/-- **Demand order**: a grade that uses the argument completes the inner factor first; a
literal grade completes first. The annotated occurrences agree with the machine on both orders. -/
theorem demand_order_controls_agree :
    weigh (orderSpecimen true).annotate = (orderSpecimen true).nativeBag ∧
    weigh (orderSpecimen false).annotate = (orderSpecimen false).nativeBag ∧
    (orderSpecimen true).nativeBag ≠ (orderSpecimen false).nativeBag := by
  have forced : (orderSpecimen true).nativeBag =
      [(integer 7, FreeMonoid.of "inner" * FreeMonoid.of "outer")] :=
    graded_identity_keeps_factor_completion_order.1
  have literal : (orderSpecimen false).nativeBag =
      [(integer 7, FreeMonoid.of "outer" * FreeMonoid.of "inner")] :=
    graded_identity_keeps_factor_completion_order.2
  rw [forced, literal]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## The typed reading: the occurrences of a typing derivation -/

/-- **The atom a typed value denotes**: a numeral is an integer, and `Pair a b` of two
numerals is `(Pair a b)`. -/
def readValue : Typed.ClosedTerm → Option Atom
  | .app (.app (.const c) a) b =>
    if c = Typed.pairCtorN then
      (Typed.readNumber a).bind fun x => (Typed.readNumber b).map fun y =>
        call "Pair" [integer x, integer y]
    else none
  | t => (Typed.readNumber t).map fun k => integer k

/-- **The occurrence a world of a typed program produces**: the value it returns, and the rows
it charged in order, each with its grade read in the algebra. -/
def readWorld (readGrade : Typed.ClosedTerm → Option V) (world : Typed.ChargedWorld) :
    Option (AnnotatedOccurrence V) :=
  (readValue world.answer).bind fun value =>
    (world.intents.mapM fun charge =>
      (readGrade charge.2).map fun grade => (⟨charge.1, grade⟩ : Charge V)).map fun charges =>
        ⟨value, charges⟩

/-- The occurrences of a list of worlds, in order. -/
def readOccurrences (readGrade : Typed.ClosedTerm → Option V) (worlds : List Typed.ChargedWorld) :
    Option (List (AnnotatedOccurrence V)) :=
  worlds.mapM (readWorld readGrade)

/-- A grade term read as evidence counts. -/
def readEvidence (term : Typed.ClosedTerm) : Option BinEvNat :=
  (Typed.readCount term).map fun counts => ⟨counts.1, counts.2⟩

/-- **The annotated occurrences of the shared pair are the occurrences of its typing
derivation**: each world of the typed program `Typed.sharedPairCode`, read, is the annotated
occurrence at its place. -/
theorem sharedPair_typed :
    readOccurrences Typed.readNumber (Typed.worldsOf (Typed.sharedPairCode .number)) =
      some (numberSpecimen .sharedPair).annotate := by
  decide +kernel

/-- The nested identity: the two charges of the identity row, the inner one first. -/
theorem nestedSelf_typed :
    readOccurrences Typed.readNumber (Typed.worldsOf (Typed.nestedCode .number)) =
      some (numberSpecimen .nestedSelf).annotate := by
  decide +kernel

/-- The identity over a coin with an ungraded row: the zero weight stays an occurrence. -/
theorem coinThroughId_typed :
    readOccurrences Typed.readNumber (Typed.worldsOf Typed.coinThroughIdCode) =
      some (numberSpecimen .coinThroughId).annotate := by
  decide +kernel

/-- The shared pair over evidence counts: the same rows, each grade a packet. -/
theorem evidenceShared_typed :
    readOccurrences readEvidence (Typed.worldsOf (Typed.sharedPairCode .count)) =
      some (evidenceSpecimen .sharedPair).annotate := by
  decide +kernel

/-- **The number specimens with a typing derivation.** -/
inductive TypedSpecimen where
  | sharedPair
  | nestedSelf
  | coinThroughId
  deriving DecidableEq, Repr

/-- The number specimen of each typed specimen. -/
def TypedSpecimen.specimen : TypedSpecimen → NumberSpecimen
  | .sharedPair => .sharedPair
  | .nestedSelf => .nestedSelf
  | .coinThroughId => .coinThroughId

/-- The typed program of each specimen. -/
def TypedSpecimen.code : TypedSpecimen → Typed.ChargeCode
  | .sharedPair => Typed.sharedPairCode .number
  | .nestedSelf => Typed.nestedCode .number
  | .coinThroughId => Typed.coinThroughIdCode

/-- The type of its result. -/
def TypedSpecimen.type : TypedSpecimen → Typed.ClosedTerm
  | .sharedPair => Typed.rNumberPair
  | .nestedSelf => Typed.rNum
  | .coinThroughId => Typed.rNum

/-- **Each typed program has its typing derivation** in the weight package. -/
theorem TypedSpecimen.typing : ∀ specimen : TypedSpecimen,
    Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ScopedComputation.Typing
      Typed.weightRules (Typed.gradeSignature .number) .nil specimen.code specimen.type
  | .sharedPair => Typed.sharedPair_typing .number
  | .nestedSelf => Typed.nested_typing .number
  | .coinThroughId => Typed.coinThroughId_typing

/-- **The typed face**: the occurrences of the worlds of the typed program. -/
def TypedSpecimen.occurrences (specimen : TypedSpecimen) : List (AnnotatedOccurrence Nat) :=
  (readOccurrences Typed.readNumber (Typed.worldsOf specimen.code)).getD []

/-- **The typed face is the annotated face**, on every typed specimen. -/
theorem TypedSpecimen.occurrences_eq_annotate : ∀ specimen : TypedSpecimen,
    specimen.occurrences = (numberSpecimen specimen.specimen).annotate
  | .sharedPair => by
    show (readOccurrences Typed.readNumber
      (Typed.worldsOf (Typed.sharedPairCode .number))).getD [] = _
    rw [sharedPair_typed]
    rfl
  | .nestedSelf => by
    show (readOccurrences Typed.readNumber (Typed.worldsOf (Typed.nestedCode .number))).getD [] = _
    rw [nestedSelf_typed]
    rfl
  | .coinThroughId => by
    show (readOccurrences Typed.readNumber (Typed.worldsOf Typed.coinThroughIdCode)).getD [] = _
    rw [coinThroughId_typed]
    rfl

/-- **The triangle with the typed face**: what runs is read as the occurrences of a typing
derivation, the occurrences mean their weighted bag, and the direct map runs the machine. -/
def typedTriangle : Mettapedia.Computability.ComputationalTrinity.Comparison.{0, 0, 0} Closed :=
  triangleOfThree TypedSpecimen.occurrences weigh
    (fun specimen => (numberSpecimen specimen.specimen).nativeBag)
    fun specimen => by
      rw [specimen.occurrences_eq_annotate]
      exact numberAgree specimen.specimen

/-- The evidence bag of the typed shared pair is the native evidence run. -/
theorem evidenceShared_typed_agree :
    weigh ((readOccurrences readEvidence (Typed.worldsOf (Typed.sharedPairCode .count))).getD []) =
      (evidenceSpecimen .sharedPair).nativeBag := by
  rw [evidenceShared_typed]
  exact evidenceAgree .sharedPair

/-- Negative example: **a fresh producer at each use of `paired` gives other occurrences.**
The program `Typed.freshPairCode` has a typing derivation too, but its nine occurrences
include the mixed pair `(Pair 2 5)`, and the linking theorem fails for it. -/
theorem fresh_producer_not_annotated :
    readOccurrences Typed.readNumber (Typed.worldsOf (Typed.freshPairCode .number)) ≠
        some (numberSpecimen .sharedPair).annotate ∧
      ((readOccurrences Typed.readNumber (Typed.worldsOf (Typed.freshPairCode .number))).getD
        []).length = 9 ∧
      ((readOccurrences Typed.readNumber (Typed.worldsOf (Typed.freshPairCode .number))).getD
        []).any (fun occurrence => decide (occurrence.value = call "Pair" [integer 2, integer 5])) =
        true := by
  decide +kernel

/-! ## A guarded variant, compared apart -/

/-- The identity over the coin of the identity program, under a zero-rejecting admission. -/
def guardedCoinSpecimen : Specimen Nat :=
  ⟨identityProgram, gradedCoinAnnotation, naturalCoefficient, some fun value => value != 0,
    .apply "id" (.stored "coin"), 300⟩

/-- **New run**: the native machine under the admission refuses the identity's zero grade on
the coin row `0`, and keeps the row `1`. -/
theorem guardedCoin_native : guardedCoinSpecimen.nativeBag = [(integer 1, 3)] := by
  decide +kernel

theorem guardedCoin_annotated :
    guardedCoinSpecimen.annotate = [⟨integer 1, [⟨1, 3⟩, ⟨2, 1⟩]⟩] := by
  decide +kernel

/-- **The guarded comparison.** Under attachment the typed program keeps the occurrence of the
coin row `0` with the zero weight, as the native run does (`(0, 0)` beside `(1, 3)`); under the
zero-rejecting guard the direct worlds of the same typed program drop it, and their occurrences
are the annotated occurrences of the guarded specimen, whose bag is the native guarded run. The
guard is realized by the direct worlds only: no contextual handler produces no world
(`Typed.guarded_no_handler`), so result preservation under the guard is the direct theorem
(`Typed.coinThroughId_guarded_results`). -/
theorem guard_comparison :
    readOccurrences Typed.readNumber (Typed.worldsOf Typed.coinThroughIdCode) =
        some (numberSpecimen .coinThroughId).annotate ∧
      (numberSpecimen .coinThroughId).nativeBag = [(integer 0, 0), (integer 1, 3)] ∧
      readOccurrences Typed.readNumber (Typed.guardedWorldsOf Typed.coinThroughIdCode) =
        some guardedCoinSpecimen.annotate ∧
      weigh guardedCoinSpecimen.annotate = guardedCoinSpecimen.nativeBag ∧
      guardedCoinSpecimen.nativeBag = [(integer 1, 3)] := by
  refine ⟨coinThroughId_typed, coinThroughId_native, by decide +kernel, ?_, guardedCoin_native⟩
  rw [guardedCoin_annotated, guardedCoin_native]
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity
