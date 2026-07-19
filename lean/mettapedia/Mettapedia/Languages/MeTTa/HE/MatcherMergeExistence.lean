import Mettapedia.Languages.MeTTa.HE.MatchSolutionTheory
import Mettapedia.Languages.MeTTa.HE.UnificationCompleteness

/-!
# Satisfiable matcher-result merge-back exists (`HESatisfiedMatcherMergeRelExists`)

Target: discharge the open obligation
`HESatisfiedMatcherMergeRelExists` (`LeaTTaMatcherCongruence.lean:527`).

This file transports the Phase-1 Robinson-completeness machinery
(`UnificationCompleteness.lean`) to the HE mutual merge engine.

Layering: this module sits **below** `LeaTTaMatcherCongruence`, importing only
`MatchSolutionTheory` and `UnificationCompleteness` (both of which import just
`LeaTTaBindingTransport`).  That is deliberate — the conflict callbacks that
consume these lemmas live *inside* `LeaTTaMatcherCongruence`, so this module
must be importable from there without an import cycle.

## Building block 1 — value-conflict joint satisfiability
Under a common valuation, a stored class value and a proposed matched
assignment value are jointly satisfied, so their equation feeds the conflict
matcher.  (Committed analogues: `classValues_equationSatisfied`,
`valueConflict_equationSatisfied`; this is the direct-`assignments` phrasing.)
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- **BB1.**  A value already carried by `b`'s equality class for `v` and a
value assigned to `v` by a co-satisfied `matched` record have the same
solution image, i.e. their translated equation is satisfied.  This is the
semantic premise consumed by every `AddVarBindingRel.conflict` branch. -/
theorem valueConflict_jointly_satisfied
    {μ : String → Metta.Atom} {b matched : Bindings} {v : String}
    {val first : Atom} {rest : List Atom}
    (hb : HEBindingSatisfied μ b) (hmatched : HEBindingSatisfied μ matched)
    (hclass : b.classValues v = first :: rest)
    (hval : (v, val) ∈ matched.assignments) :
    MettaEquationSatisfied μ (toLeaTTaAtom first, toLeaTTaAtom val) := by
  have h1 : μ v = applyClassSolution μ (toLeaTTaAtom first) :=
    hb.eq_applyClassSolution_of_mem_classValues
      (by rw [hclass]; exact List.mem_cons_self ..)
  have h2 : μ v = applyClassSolution μ (toLeaTTaAtom val) := hmatched.1 v val hval
  simpa [MettaEquationSatisfied] using h1.symm.trans h2

/-! ## Building block 2 — the joint-system measure (Robinson variable count)

The recursion in `AddVarBindingRel.conflict` / `AddVarEqualityRel.pairConflict`
recurses `MergeRel b mB out` with `b` the *unchanged* accumulator and
`mB = match(first, val)`, so no structural/`sizeOf` measure on the arguments
decreases.  The well-founded index is the Robinson elimination of the joint
system of `seed` and `matched` (Phase 1, `UnificationCompleteness`).

Two facts split the descent:

* **measure adequacy (below).**  The joint HE equation system is host-float-free
  and satisfied by the common valuation, so Phase-1 Robinson unification
  succeeds at the structural fuel and returns a finite elimination trace.  Its
  length is bounded by the Robinson variable count
  `(eqVars _).card ≤ equationFuel _` (`card_eqVars_le_equationFuel`).
* **strict per-step descent (already committed).**  Each realized conflict
  merge strictly shrinks the count of *unrealized* trace obligations,
  `pendingEliminationTraceEntries_card_lt_of_mergeBindings`
  (`LeaTTaMatcherCongruence.lean:4559`).

Note the descent measure is the count of **unsolved** obligations, not the raw
`(eqVars _).card` of `(b, mB)`.  Raw `eqVars` does **not** decrease at a conflict
step: e.g. `seed = {x ↦ f y}`, `matched = {x ↦ f z}` gives
`mB = match(f y, f z) = {y = z}`, and both `HEEquations b ++ HEEquations m` and
`HEEquations b ++ HEEquations mB` have variable set `{x, y, z}`.  The raw count
is only the *fuel bound* (trace length), while the strict per-step index is the
unrealized-obligation count above. -/

/-- Translated first-order equation presentation of one HE binding record:
each assignment `$x <- val` becomes `$x = ⟦val⟧`, each equality `$x = $y`
becomes `$x = $y`, all in LeaTTa atoms.  This is the joint-system carrier over
which the Robinson variable count is taken. -/
def HEEquations (b : Bindings) : List (Metta.Atom × Metta.Atom) :=
  b.assignments.map (fun p => (Metta.Atom.var p.1, toLeaTTaAtom p.2)) ++
  b.equalities.map (fun p => (Metta.Atom.var p.1, Metta.Atom.var p.2))

/-- Constraint-list presentation of the same literal HE record.  Unlike the
Robinson elimination trace, this carrier deliberately retains every raw
runtime assignment and equality entry. -/
def HEConstraints (b : Bindings) : List (String × Metta.Atom) :=
  b.assignments.map (fun p => (p.1, toLeaTTaAtom p.2)) ++
    b.equalities.map (fun p => (p.1, Metta.Atom.var p.2))

/-- Every equation extracted from an HE record is host-float-free on both
sides: variables are float-free by definition, translated values by
`toLeaTTaAtom_noFloat`. -/
theorem HEEquations_noFloat (b : Bindings) :
    ∀ eq ∈ HEEquations b, MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2 := by
  intro eq hmem
  simp only [HEEquations, List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩
  · exact ⟨by simp [MettaAtomNoFloat], toLeaTTaAtom_noFloat p.2⟩
  · exact ⟨by simp [MettaAtomNoFloat], by simp [MettaAtomNoFloat]⟩

/-- A valuation satisfying an HE record satisfies its translated equation
system.  Assignments unfold through `applyClassSolution _ (var x) = μ x`;
equalities are the raw class edges. -/
theorem HEEquations_satisfied {μ : String → Metta.Atom} {b : Bindings}
    (hb : HEBindingSatisfied μ b) :
    MettaEquationsSatisfied μ (HEEquations b) := by
  intro eq hmem
  simp only [HEEquations, List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · show applyClassSolution μ (Metta.Atom.var p.1)
        = applyClassSolution μ (toLeaTTaAtom p.2)
    simpa [applyClassSolution] using hb.1 p.1 p.2 hp
  · show applyClassSolution μ (Metta.Atom.var p.1)
        = applyClassSolution μ (Metta.Atom.var p.2)
    simpa [applyClassSolution] using hb.2 p.1 p.2 hp

/-- The translated equation carrier is exact, not merely sound: it presents
the same valuation theory as the HE binding record from which it was
extracted. -/
theorem HEEquations_satisfied_iff
    (μ : String → Metta.Atom) (b : Bindings) :
    MettaEquationsSatisfied μ (HEEquations b) ↔
      HEBindingSatisfied μ b := by
  constructor
  · intro hequations
    constructor
    · intro key value hmem
      have hconstraint := hequations
        (Metta.Atom.var key, toLeaTTaAtom value)
        (by
          simp only [HEEquations, List.mem_append, List.mem_map]
          exact Or.inl ⟨(key, value), hmem, rfl⟩)
      simpa [MettaEquationSatisfied, applyClassSolution] using hconstraint
    · intro left right hmem
      have hconstraint := hequations
        (Metta.Atom.var left, Metta.Atom.var right)
        (by
          simp only [HEEquations, List.mem_append, List.mem_map]
          exact Or.inr ⟨(left, right), hmem, rfl⟩)
      simpa [MettaEquationSatisfied, applyClassSolution] using hconstraint
  · exact HEEquations_satisfied

/-- Left atoms of the literal pointwise presentation of a binding record.
Assignments are visited first and equalities second, exactly as `MergeRel`
folds them. -/
def HEEquationLeftAtoms (b : Bindings) : List Atom :=
  b.assignments.map (fun p => .var p.1) ++
    b.equalities.map (fun p => .var p.1)

/-- Right atoms of the literal pointwise presentation of a binding record. -/
def HEEquationRightAtoms (b : Bindings) : List Atom :=
  b.assignments.map Prod.snd ++
    b.equalities.map (fun p => .var p.2)

/-- The pointwise atom presentation is definitionally faithful to
`HEEquations`, including the runtime assignment-before-equality order. -/
theorem zip_translated_HEEquationAtoms (b : Bindings) :
    List.zip (toLeaTTaAtoms (HEEquationLeftAtoms b))
        (toLeaTTaAtoms (HEEquationRightAtoms b)) =
      HEEquations b := by
  have htranslate : ∀ atoms : List Atom,
      toLeaTTaAtoms atoms = atoms.map toLeaTTaAtom := by
    intro atoms
    induction atoms with
    | nil => rfl
    | cons atom rest ih => simp [toLeaTTaAtoms, ih]
  rw [htranslate, htranslate]
  simp only [HEEquationLeftAtoms, HEEquationRightAtoms,
    List.map_append]
  rw [List.zip_append (by simp)]
  have hassignments :
      List.zip
          (b.assignments.map (fun p => Metta.Atom.var p.1))
          (b.assignments.map (fun p => toLeaTTaAtom p.2)) =
        b.assignments.map
          (fun p => (Metta.Atom.var p.1, toLeaTTaAtom p.2)) := by
    induction b.assignments with
    | nil => rfl
    | cons assignment rest ih => simp [ih]
  have hequalities :
      List.zip
          (b.equalities.map (fun p => Metta.Atom.var p.1))
          (b.equalities.map (fun p => Metta.Atom.var p.2)) =
        b.equalities.map
          (fun p => (Metta.Atom.var p.1, Metta.Atom.var p.2)) := by
    induction b.equalities with
    | nil => rfl
    | cons equality rest ih => simp [ih]
  simp only [List.map_map]
  change
    List.zip
        (b.assignments.map (fun p => Metta.Atom.var p.1))
        (b.assignments.map (fun p => toLeaTTaAtom p.2)) ++
      List.zip
        (b.equalities.map (fun p => Metta.Atom.var p.1))
        (b.equalities.map (fun p => Metta.Atom.var p.2)) =
      HEEquations b
  rw [hassignments, hequalities]
  rfl

/-- The two pointwise presentations are aligned for every binding record. -/
theorem HEEquationAtoms_length_eq (b : Bindings) :
    (HEEquationLeftAtoms b).length =
      (HEEquationRightAtoms b).length := by
  simp [HEEquationLeftAtoms, HEEquationRightAtoms]

/-- Inversion of a declarative merge whose right record is exactly one value
assignment.  This exposes the literal `AddVarBindingRel` step hidden by the
two runtime folds. -/
theorem mergeRel_singleAssignment_inv
    {seed out : Bindings} {key : String} {value : Atom}
    (h : DeclMergeSpec.MergeRel seed
      (⟨[(key, value)], []⟩ : Bindings) out) :
    DeclMergeSpec.AddVarBindingRel seed key value out := by
  cases h with
  | mk hassignments hequalities =>
      cases hequalities with
      | nil =>
          cases hassignments with
          | cons hhead htail =>
              cases htail with
              | nil => exact hhead

/-- Equality companion to `mergeRel_singleAssignment_inv`. -/
theorem mergeRel_singleEquality_inv
    {seed out : Bindings} {left right : String}
    (h : DeclMergeSpec.MergeRel seed
      (⟨[], [(left, right)]⟩ : Bindings) out) :
    DeclMergeSpec.AddVarEqualityRel seed left right out := by
  cases h with
  | mk hassignments hequalities =>
      cases hassignments with
      | nil =>
          cases hequalities with
          | cons hhead htail =>
              cases htail with
              | nil => exact hhead

/-- A pointwise list match of the literal equations of a binding record is
an actual merge of that record into the same live seed.  This is an
operational reconstruction theorem: it retains the original per-entry
`MatchRel` and `MergeRel` premises and folds them into the exact runtime
`MergeRel`, rather than appealing to solution-set equality. -/
theorem matchListAccRel_HEEquationAtoms_to_mergeRel
    {right seed out : Bindings}
    (hnonvar : ∀ key value, (key, value) ∈ right.assignments →
      DeclMatchSpec.Atom.isVarB value = false)
    (h : DeclMatchSpec.MatchListAccRel
      (HEEquationLeftAtoms right) (HEEquationRightAtoms right) seed out) :
    DeclMergeSpec.MergeRel seed right out := by
  have equalitiesFold : ∀
      (equalities : List (String × String)) (before after : Bindings),
      DeclMatchSpec.MatchListAccRel
        (equalities.map (fun p => Atom.var p.1))
        (equalities.map (fun p => Atom.var p.2)) before after →
      DeclMergeSpec.MergeEqsRel before equalities after := by
    intro equalities
    induction equalities with
    | nil =>
        intro before after hlist
        cases hlist
        exact DeclMergeSpec.MergeEqsRel.nil
    | cons equality rest ih =>
        rcases equality with ⟨left, right⟩
        intro before after hlist
        simp only [List.map_cons] at hlist
        cases hlist with
        | @cons _ _ _ _ _ matched next _ fuel hmatch hmerge htail =>
            have hmatched : matched =
                (⟨[], [(left, right)]⟩ : Bindings) :=
              DeclMatchSpec.matchRel_varVar_inv hmatch
            subst matched
            have hadd : DeclMergeSpec.AddVarEqualityRel
                before left right next :=
              mergeRel_singleEquality_inv
                (DeclMergeSpec.mergeBindings_sound hmerge)
            exact DeclMergeSpec.MergeEqsRel.cons hadd (ih next after htail)
  have assignmentsFold : ∀
      (assignments : List (String × Atom))
      (equalities : List (String × String))
      (before after : Bindings),
      (∀ key value, (key, value) ∈ assignments →
        DeclMatchSpec.Atom.isVarB value = false) →
      DeclMatchSpec.MatchListAccRel
        (assignments.map (fun p => Atom.var p.1) ++
          equalities.map (fun p => Atom.var p.1))
        (assignments.map Prod.snd ++
          equalities.map (fun p => Atom.var p.2)) before after →
      ∃ middle,
        DeclMergeSpec.MergeAssignsRel before assignments middle ∧
          DeclMergeSpec.MergeEqsRel middle equalities after := by
    intro assignments
    induction assignments with
    | nil =>
        intro equalities before after _ hlist
        simp only [List.map_nil, List.nil_append] at hlist
        exact ⟨before, DeclMergeSpec.MergeAssignsRel.nil,
          equalitiesFold equalities before after hlist⟩
    | cons assignment rest ih =>
        rcases assignment with ⟨key, value⟩
        intro equalities before after hvalues hlist
        simp only [List.map_cons, List.cons_append] at hlist
        cases hlist with
        | @cons _ _ _ _ _ matched next _ fuel hmatch hmerge htail =>
            have hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false :=
              hvalues key value (by simp)
            have hmatched : matched =
                (⟨[(key, value)], []⟩ : Bindings) := by
              cases hmatch with
              | varVar => simp [DeclMatchSpec.Atom.isVarB] at hvalueNonvar
              | varNonVar => rfl
              | nonVarVar hleft =>
                  simp [DeclMatchSpec.Atom.isVarB] at hleft
            subst matched
            have hadd : DeclMergeSpec.AddVarBindingRel
                before key value next :=
              mergeRel_singleAssignment_inv
                (DeclMergeSpec.mergeBindings_sound hmerge)
            have hrestValues : ∀ restKey restValue,
                (restKey, restValue) ∈ rest →
                  DeclMatchSpec.Atom.isVarB restValue = false := by
              intro restKey restValue hmem
              exact hvalues restKey restValue (by simp [hmem])
            obtain ⟨middle, hrest, hequalities⟩ :=
              ih equalities next after hrestValues htail
            exact ⟨middle,
              DeclMergeSpec.MergeAssignsRel.cons hadd hrest,
              hequalities⟩
  obtain ⟨middle, hassignments, hequalities⟩ := assignmentsFold
    right.assignments right.equalities seed out hnonvar (by
      simpa [HEEquationLeftAtoms, HEEquationRightAtoms] using h)
  exact DeclMergeSpec.MergeRel.mk hassignments hequalities

/-- **BB2 (measure adequacy).**  Under a common valuation the joint HE equation
system of `seed` and `matched` is host-float-free and satisfied, so Phase-1
Robinson unification succeeds at the structural fuel — the finite descent
budget for the conflict recursion.  This is exactly Phase 1
(`exists_unifyRounds_equationFuel_of_satisfied`), transported to the HE mutual
merge problem; the fuel `equationFuel _` bounds the Robinson variable count
`(eqVars _).card` (`card_eqVars_le_equationFuel`). -/
theorem jointHESystem_robinson_succeeds
    {μ : String → Metta.Atom} {seed matched : Bindings}
    (hseed : HEBindingSatisfied μ seed)
    (hmatched : HEBindingSatisfied μ matched) :
    ∃ result,
      Metta.Unify.unifyRounds
        (Metta.Bindings.equationFuel (HEEquations seed ++ HEEquations matched))
        (HEEquations seed ++ HEEquations matched) [] = some result := by
  refine exists_unifyRounds_equationFuel_of_satisfied (valuation := μ)
    (HEEquations seed ++ HEEquations matched) ?_ ?_
  · intro eq hmem
    rcases List.mem_append.mp hmem with h | h
    · exact HEEquations_noFloat seed eq h
    · exact HEEquations_noFloat matched eq h
  · intro eq hmem
    rcases List.mem_append.mp hmem with h | h
    · exact HEEquations_satisfied hseed eq h
    · exact HEEquations_satisfied hmatched eq h

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
