/-
QueryOp observational anchor.

LeaTTa's `queryOp` turns bindings into observable behaviour in exactly one
place: a knowledge-base rule `(= lhs rhs)` is matched against the evaluated
atom (`matchAtoms lhs toEval`), the match output is merged with the incoming
bindings (`Bindings.merge`), loop-carrying merges are discarded, and the
surviving merged bindings are applied to the rule's right-hand side
(`instantiate merged rhs`).

This file anchors that observable pipeline to the executable-independent
spec specification:

* `queryOp_hit_observational_anchor` — every match+merge hit of the pipeline
  (with satisfiable merged output) has a spec `MatchRel` derivation for the
  match step and a spec `MergeRel` derivation for the merge step whose
  result presents the same complete binding solution theory as the
  executable merged bindings.  The satisfiability premise is the matcher
  soundness input; it is discharged by the matcher-output satisfiability
  theorem, so no ad-hoc quotient enters here.

* `resolveAtom_semantically_inert` / `instantiate_semantically_inert` — the
  observable application step is semantically inert: under every valuation
  satisfying the bindings, the instantiated atom is identified with the raw
  atom.  So the observable emitted by `queryOp` is determined by the binding
  solution theory, which is precisely the equivalence the conformance seal
  is stated in: nothing finer than solution theory is observable through
  `queryOp`, and the seal's equivalence is derived from that observation
  rather than chosen for convenience.
-/
import Mettapedia.Languages.MeTTa.HE.LeaTTaSpecSoundness
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.EquationQueryStep
import MettaHyperonFull.Proofs.CaptureAvoidingFreshening

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

/-! ## Valuation constancy on explicit equality classes -/

private theorem lookupVal_mem :
    ∀ {lb : Metta.Bindings} {x : String} {a : Metta.Atom},
      Metta.Bindings.lookupVal lb x = some a →
      Metta.BindingRel.val x a ∈ lb
  | [], _, _, h => by simp [Metta.Bindings.lookupVal] at h
  | .val y v :: rest, x, a, h => by
    simp only [Metta.Bindings.lookupVal] at h
    by_cases hxy : (x == y) = true
    · rw [if_pos hxy] at h
      cases h
      have : x = y := by simpa using hxy
      subst this
      exact List.mem_cons_self
    · rw [if_neg hxy] at h
      exact List.mem_cons_of_mem _ (lookupVal_mem h)
  | .eq _ _ :: rest, x, a, h => by
    simp only [Metta.Bindings.lookupVal] at h
    exact List.mem_cons_of_mem _ (lookupVal_mem h)

private theorem leaSatisfied_eq_of_reachable
    {lb : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsat : ∀ x y, Metta.BindingRel.eq x y ∈ lb →
      valuation x = valuation y)
    {left right : String}
    (hreach : (EqualityClosure.edgeGraph
      (leaEqualityEdges lb)).Reachable left right) :
    valuation left = valuation right := by
  apply hreach.elim
  intro walk
  induction walk with
  | nil => rfl
  | @cons start next finish hadj tail ih =>
    have hstep : valuation start = valuation next := by
      rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with
        hedge | hedge
      · exact hsat _ _ (mem_leaEqualityEdges_iff.mp hedge)
      · exact (hsat _ _ (mem_leaEqualityEdges_iff.mp hedge)).symm
    exact hstep.trans (ih tail.reachable)

private theorem leaSatisfied_eq_of_mem_eqClass
    {lb : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsat : LeaBindingSatisfied valuation lb) {x y : String}
    (hmem : y ∈ Metta.Bindings.eqClass lb x) :
    valuation x = valuation y :=
  leaSatisfied_eq_of_reachable hsat.2
    (mem_leaEqClass_iff_reachable.mp hmem)

private theorem mem_eqClassOrdered_cases
    {lb : Metta.Bindings} {x y : String}
    (h : y ∈ Metta.Bindings.eqClassOrdered lb x) :
    y = x ∨ y ∈ Metta.Bindings.eqClass lb x := by
  unfold Metta.Bindings.eqClassOrdered at h
  cases hfilter : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun z => (Metta.Bindings.eqClass lb x).contains z) with
  | nil =>
    rw [hfilter] at h
    simp only [List.mem_singleton] at h
    exact Or.inl h
  | cons head tail =>
    rw [hfilter] at h
    have hmem : y ∈ (Metta.Bindings.eqVarsInOrder lb).filter
        (fun z => (Metta.Bindings.eqClass lb x).contains z) := by
      rw [hfilter]; exact h
    have := (List.mem_filter.mp hmem).2
    exact Or.inr (by simpa using this)

private theorem leaSatisfied_eq_of_mem_eqClassOrdered
    {lb : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsat : LeaBindingSatisfied valuation lb) {x y : String}
    (hmem : y ∈ Metta.Bindings.eqClassOrdered lb x) :
    valuation x = valuation y := by
  rcases mem_eqClassOrdered_cases hmem with heq | hclass
  · subst heq; rfl
  · exact leaSatisfied_eq_of_mem_eqClass hsat hclass

private theorem leaSatisfied_eqRepresentative
    {lb : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsat : LeaBindingSatisfied valuation lb) (x : String) :
    valuation (Metta.Bindings.eqRepresentative lb x) = valuation x := by
  unfold Metta.Bindings.eqRepresentative
  cases hcls : Metta.Bindings.eqClassOrdered lb x with
  | nil => simp
  | cons head tail =>
    simp only [List.headD_cons]
    exact (leaSatisfied_eq_of_mem_eqClassOrdered hsat
      (by rw [hcls]; exact List.mem_cons_self)).symm

private theorem leaSatisfied_eq_of_mem_classValues
    {lb : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsat : LeaBindingSatisfied valuation lb) {x : String}
    {value : Metta.Atom}
    (hmem : value ∈ Metta.Bindings.classValues lb x) :
    valuation x = applyClassSolution valuation value := by
  unfold Metta.Bindings.classValues at hmem
  obtain ⟨y, hy, hlookup⟩ := List.mem_filterMap.mp hmem
  exact (leaSatisfied_eq_of_mem_eqClassOrdered hsat hy).trans
    (hsat.1 y value (lookupVal_mem hlookup))

/-! ## Semantic inertness of the resolver -/

private theorem mapM_resolveAtomAux_inert
    {lb : Metta.Bindings} {valuation : String → Metta.Atom} {fuel : Nat}
    (ih : ∀ (visited : List String) (a resolved : Metta.Atom),
      Metta.Bindings.resolveAtomAux lb fuel visited a = some resolved →
      applyClassSolution valuation resolved =
        applyClassSolution valuation a)
    (visited : List String) :
    ∀ (xs ys : List Metta.Atom),
      xs.mapM (Metta.Bindings.resolveAtomAux lb fuel visited) = some ys →
      ys.map (applyClassSolution valuation) =
        xs.map (applyClassSolution valuation)
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, ys, h => by
    cases hx : Metta.Bindings.resolveAtomAux lb fuel visited x with
    | none => simp [List.mapM_cons, hx] at h
    | some xr =>
      cases hxs : xs.mapM
          (Metta.Bindings.resolveAtomAux lb fuel visited) with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some xsr =>
        have hys : xr :: xsr = ys := by
          simpa [List.mapM_cons, hx, hxs] using h
        subst hys
        simp only [List.map_cons]
        rw [ih visited x xr hx,
          mapM_resolveAtomAux_inert ih visited xs xsr hxs]

/-- Every successful bounded resolution step is inert under every valuation
satisfying the bindings: variable hops move inside one equality class, and
value unfoldings follow value equations, both of which the valuation
identifies. -/
private theorem resolveAtomAux_semantically_inert
    {lb : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsat : LeaBindingSatisfied valuation lb) :
    ∀ (fuel : Nat) (visited : List String) (a resolved : Metta.Atom),
      Metta.Bindings.resolveAtomAux lb fuel visited a = some resolved →
      applyClassSolution valuation resolved =
        applyClassSolution valuation a := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited a resolved h
    simp [Metta.Bindings.resolveAtomAux] at h
  | succ fuel ih =>
    intro visited a resolved h
    cases a with
    | sym s =>
      simp only [Metta.Bindings.resolveAtomAux] at h
      cases h
      rfl
    | gnd g =>
      simp only [Metta.Bindings.resolveAtomAux] at h
      cases h
      rfl
    | expr xs =>
      simp only [Metta.Bindings.resolveAtomAux] at h
      cases hmap : xs.mapM
          (Metta.Bindings.resolveAtomAux lb fuel visited) with
      | none => rw [hmap] at h; cases h
      | some ys =>
        rw [hmap] at h
        cases h
        simp only [applyClassSolution, Metta.Atom.expr.injEq]
        exact mapM_resolveAtomAux_inert ih visited xs ys hmap
    | var x =>
      simp only [Metta.Bindings.resolveAtomAux] at h
      by_cases hvisited : ((Metta.Bindings.eqClassOrdered lb x).any
          visited.contains) = true
      · rw [if_pos hvisited] at h
        cases h
      · rw [if_neg hvisited] at h
        cases hvalues : Metta.Bindings.classValues lb x with
        | nil =>
          rw [hvalues] at h
          cases h
          simpa [applyClassSolution] using
            leaSatisfied_eqRepresentative hsat x
        | cons value rest =>
          rw [hvalues] at h
          have hvalue : value ∈ Metta.Bindings.classValues lb x := by
            rw [hvalues]; exact List.mem_cons_self
          have hxvalue : valuation x =
              applyClassSolution valuation value :=
            leaSatisfied_eq_of_mem_classValues hsat hvalue
          cases value with
          | var y =>
            by_cases hcontains : y ∈ Metta.Bindings.eqClassOrdered lb x
            · by_cases hlen :
                  (Metta.Bindings.eqClassOrdered lb x).length = 1
              · simp [hcontains, hlen] at h
              · have hsome : Metta.Atom.var
                    (Metta.Bindings.eqRepresentative lb x) = resolved := by
                  simpa [hcontains, hlen] using h
                subst hsome
                simpa [applyClassSolution] using
                  leaSatisfied_eqRepresentative hsat x
            · have hrec : Metta.Bindings.resolveAtomAux lb fuel
                  (Metta.Bindings.eqClassOrdered lb x ++ visited)
                  (Metta.Atom.var y) = some resolved := by
                simpa [hcontains] using h
              rw [ih _ _ _ hrec]
              simpa [applyClassSolution] using hxvalue.symm
          | sym s =>
            have := ih _ _ _ h
            rw [this]
            simpa [applyClassSolution] using hxvalue.symm
          | gnd g =>
            have := ih _ _ _ h
            rw [this]
            simpa [applyClassSolution] using hxvalue.symm
          | expr atoms =>
            have := ih _ _ _ h
            rw [this]
            simpa [applyClassSolution] using hxvalue.symm

private theorem inert_size_pos (a : Metta.Atom) : 0 < a.size := by
  cases a <;> simp only [Metta.Atom.size] <;> omega

private theorem inert_size_lt_of_mem {a : Metta.Atom} :
    ∀ {l : List Metta.Atom}, a ∈ l →
      a.size < (Metta.Atom.expr l).size
  | x :: xs, h => by
    cases List.mem_cons.mp h with
    | inl h1 =>
      subst h1
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons]
      omega
    | inr h2 =>
      have := inert_size_lt_of_mem h2
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- Full resolution (LeaTTa's `instantiate` substrate) is semantically inert
under every valuation satisfying the bindings.  Failure branches fall back
to the input atom, so no side condition is needed. -/
theorem resolveAtom_semantically_inert
    {lb : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsat : LeaBindingSatisfied valuation lb) :
    ∀ a : Metta.Atom,
      applyClassSolution valuation (Metta.Bindings.resolveAtom lb a) =
        applyClassSolution valuation a := by
  suffices key : ∀ (n : Nat) (a : Metta.Atom), a.size ≤ n →
      applyClassSolution valuation (Metta.Bindings.resolveAtom lb a) =
        applyClassSolution valuation a by
    exact fun a => key a.size a le_rfl
  intro n
  induction n with
  | zero =>
    intro a hsize
    exact absurd hsize (by have := inert_size_pos a; omega)
  | succ n ihn =>
    intro a hsize
    cases a with
    | sym s => simp [Metta.Bindings.resolveAtom]
    | gnd g => simp [Metta.Bindings.resolveAtom]
    | var x =>
      simp only [Metta.Bindings.resolveAtom]
      cases hres : Metta.Bindings.resolve lb x with
      | none => simp
      | some r =>
        simp only [Option.getD_some]
        have hres' : Metta.Bindings.resolveAtomAux lb
            (Metta.Bindings.resolutionFuel lb (Metta.Atom.var x)) []
            (Metta.Atom.var x) = some r := by
          by_cases hguard :
              ((Metta.Bindings.eqClassOrdered lb x == [x]) &&
                (Metta.Bindings.classValues lb x).isEmpty) = true
          · simp [Metta.Bindings.resolve, hguard] at hres
          · simpa [Metta.Bindings.resolve, hguard] using hres
        exact resolveAtomAux_semantically_inert hsat _ _ _ _ hres'
    | expr xs =>
      simp only [Metta.Bindings.resolveAtom, applyClassSolution,
        List.map_map, Metta.Atom.expr.injEq]
      refine List.map_congr_left ?_
      intro child hchild
      have hlt := inert_size_lt_of_mem hchild
      exact ihn child (by omega)

/-- LeaTTa's observable application step: `instantiate` is semantically
inert under every valuation satisfying the applied bindings. -/
theorem instantiate_semantically_inert
    {lb : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsat : LeaBindingSatisfied valuation lb) (a : Metta.Atom) :
    applyClassSolution valuation (Metta.instantiate lb a) =
      applyClassSolution valuation a :=
  resolveAtom_semantically_inert hsat a

/-! ## The queryOp hit anchor -/

/-- **QueryOp observational anchor.**  One `queryOp` pipeline hit — a
repaired-LeaTTa match of a translated rule pattern against a translated
query atom, merged with the incoming bindings — is anchored to the spec
specification: the match step has a spec `MatchRel` derivation, the merge
step has a spec `MergeRel` derivation from the incoming record and that
match derivation's output, and the spec merge result presents the same
complete binding solution theory as the executable merged bindings.

The satisfiability premise is the matcher/merge soundness input (discharged
by matcher-output satisfiability for loop-free outputs); everything else is
observational. -/
theorem queryOp_hit_observational_anchor
    {pattern query : OSLFCore.Atom} {specIncoming : Bindings}
    {incoming matched merged : Metta.Bindings}
    (hincomingEquiv : LeaBindingSolutionTheoryEquiv specIncoming incoming)
    (hincomingNonvariable : HEAssignmentsNonVariable specIncoming)
    (hincomingNoFloat : LeaBindingsNoFloat incoming)
    (hmatch : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hmerge : merged ∈ Metta.Bindings.merge incoming matched)
    (hsat : ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation merged) :
    ∃ specMatched specMerged,
      Spec.Match.Merge.MatchRel
          Spec.Match.Merge.equalityGroundedSemantic
          query pattern specMatched ∧
        Spec.Match.Merge.MergeRel
          Spec.Match.Merge.equalityGroundedSemantic
          specIncoming specMatched specMerged ∧
        LeaBindingSolutionTheoryEquiv specMerged merged ∧
        HEAssignmentsNonVariable specMerged := by
  obtain ⟨valuation, hmerged⟩ := hsat
  have hmatchedNoFloat : LeaBindingsNoFloat matched :=
    leaMatchAtoms_result_noFloat
      (toLeaTTaAtom_noFloat pattern) (toLeaTTaAtom_noFloat query) hmatch
  have hsplit := (leaMerge_solution_iff valuation
    hincomingNoFloat hmatchedNoFloat hmerge).mp hmerged
  have hincomingSat : LeaBindingSatisfied valuation incoming := hsplit.1
  have hmatchedSat : LeaBindingSatisfied valuation matched := hsplit.2
  have hmettaEquation : MettaEquationSatisfied valuation
      (toLeaTTaAtom pattern, toLeaTTaAtom query) :=
    (leaMatchAtoms_solution_iff valuation
      (toLeaTTaAtom_noFloat pattern)
      (toLeaTTaAtom_noFloat query) hmatch).mp hmatchedSat
  have hspecEquation : HEAtomEquationSatisfied valuation query pattern :=
    hmettaEquation.symm
  obtain ⟨specMatched, hspecMatch, hspecMatchedSat⟩ :=
    Spec.Match.Completeness.exists_specMatch_of_solution hspecEquation
  have hmatchedEquiv : LeaBindingSolutionTheoryEquiv specMatched matched :=
    Spec.Match.SolutionTheory.specMatch_leaMatch_solutionTheoryEquiv
      hspecMatch hmatch
  have hspecIncomingSat : HEBindingSatisfied valuation specIncoming :=
    (hincomingEquiv valuation).mpr hincomingSat
  have hspecMatchedNonvariable : HEAssignmentsNonVariable specMatched :=
    LeaTTaSpecConformance.specMatch_assignmentsNonVariable hspecMatch
  obtain ⟨specMerged, hspecMerge, _, hspecMergedNonvariable⟩ :=
    Spec.Match.Completeness.exists_specMerge_of_solution
      hspecIncomingSat hincomingNonvariable
      hspecMatchedSat hspecMatchedNonvariable
  refine ⟨specMatched, specMerged, hspecMatch, hspecMerge, ?_,
    hspecMergedNonvariable⟩
  intro observer
  rw [Spec.Match.SolutionTheory.mergeRel_solution_iff hspecMerge observer,
    leaMerge_solution_iff observer hincomingNoFloat hmatchedNoFloat hmerge,
    hincomingEquiv observer, hmatchedEquiv observer]

/-- **QueryOp hit existence (completeness twin).**  Every spec-specified
match+merge derivation with a satisfiable result is realized by the
executable pipeline: repaired LeaTTa produces a raw match output and a merge
with the incoming bindings that survives the `queryOp` loop filter and
presents the same complete binding solution theory as the spec merge
result.  The variable-disjointness premise is exactly what `queryOp`'s rule
freshening establishes before matching. -/
theorem queryOp_hit_exists_of_spec
    {pattern query : OSLFCore.Atom}
    {specIncoming specMatched specMerged : Bindings}
    {incoming : Metta.Bindings}
    (hincomingEquiv : LeaBindingSolutionTheoryEquiv specIncoming incoming)
    (hincomingNoFloat : LeaBindingsNoFloat incoming)
    (hincomingNonvariable : LeaAssignmentsNonVariable incoming)
    (hincomingIrreflexive : LeaEqualitiesIrreflexive incoming)
    (hdisjoint : VarsDisjoint query pattern)
    (hspecMatch : Spec.Match.Merge.MatchRel
      Spec.Match.Merge.equalityGroundedSemantic
      query pattern specMatched)
    (hspecMerge : Spec.Match.Merge.MergeRel
      Spec.Match.Merge.equalityGroundedSemantic
      specIncoming specMatched specMerged)
    (hsat : ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation specMerged) :
    ∃ matched merged,
      matched ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        merged ∈ Metta.Bindings.merge incoming matched ∧
        merged.hasLoop = false ∧
        LeaBindingSolutionTheoryEquiv specMerged merged := by
  obtain ⟨valuation, hmergedSatHE⟩ := hsat
  have hpair := (Spec.Match.SolutionTheory.mergeRel_solution_iff
    hspecMerge valuation).mp hmergedSatHE
  have hequation : MettaEquationSatisfied valuation
      (toLeaTTaAtom query, toLeaTTaAtom pattern) :=
    (Spec.Match.SolutionTheory.matchRel_solution_iff
      hspecMatch valuation).mp hpair.2
  obtain ⟨matched, hmatched, hmatchedEquiv⟩ :=
    LeaTTaSpecConformance.specMatch_observational_complete_of_satisfiable
      hspecMatch hdisjoint ⟨valuation, hequation⟩
  have hincomingSat : LeaBindingSatisfied valuation incoming :=
    (hincomingEquiv valuation).mp hpair.1
  have hmatchedSat : LeaBindingSatisfied valuation matched :=
    (hmatchedEquiv valuation).mp hpair.2
  have hmatchedNoFloat : LeaBindingsNoFloat matched :=
    leaMatchAtoms_result_noFloat
      (toLeaTTaAtom_noFloat pattern) (toLeaTTaAtom_noFloat query) hmatched
  obtain ⟨merged, hmerged, hmergedSat, _⟩ :=
    LeaTTaMergeExistence.merge_exists_of_satisfied
      hincomingNoFloat hmatchedNoFloat hincomingSat hmatchedSat
  refine ⟨matched, merged, hmatched, hmerged, ?_, ?_⟩
  · exact leaBindings_hasLoop_false_of_satisfied hmergedSat
      (leaMerge_result_assignmentsNonVariable hincomingNonvariable hmerged)
      (leaMerge_result_equalitiesIrreflexive hincomingIrreflexive hmerged)
  · intro observer
    rw [Spec.Match.SolutionTheory.mergeRel_solution_iff hspecMerge observer,
      leaMerge_solution_iff observer hincomingNoFloat hmatchedNoFloat
        hmerged,
      hincomingEquiv observer, hmatchedEquiv observer]

/-- The anchored observable: under the anchor's solution-theory equivalence,
every model of the spec merge result identifies the emitted `queryOp`
observable `instantiate merged rhs` with the raw rule right-hand side.  The
`queryOp` observation therefore factors through the binding solution theory,
which derives the seal's equivalence from the observation itself. -/
theorem anchored_observable_inert
    {specMerged : Bindings} {merged : Metta.Bindings}
    (hequiv : LeaBindingSolutionTheoryEquiv specMerged merged)
    {valuation : String → Metta.Atom}
    (hvaluation : HEBindingSatisfied valuation specMerged)
    (rhs : Metta.Atom) :
    applyClassSolution valuation (Metta.instantiate merged rhs) =
      applyClassSolution valuation rhs :=
  instantiate_semantically_inert ((hequiv valuation).mp hvaluation) rhs

/-- One satisfiable executable query hit has both a declarative spec
match-and-merge witness and an observable that factors through the witness's
complete solution theory.  This packages the two independent parts of the
query boundary into the premise shape used by the final soundness seal. -/
theorem queryOp_hit_observational_sound_of_satisfiable
    {pattern query : OSLFCore.Atom} {specIncoming : Bindings}
    {incoming matched merged : Metta.Bindings} {rhs : Metta.Atom}
    (hincomingEquiv : LeaBindingSolutionTheoryEquiv specIncoming incoming)
    (hincomingNonvariable : HEAssignmentsNonVariable specIncoming)
    (hincomingNoFloat : LeaBindingsNoFloat incoming)
    (hmatch : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hmerge : merged ∈ Metta.Bindings.merge incoming matched)
    (hsat : ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation merged) :
    ∃ specMatched specMerged,
      Spec.Match.Merge.MatchRel
          Spec.Match.Merge.equalityGroundedSemantic
          query pattern specMatched ∧
        Spec.Match.Merge.MergeRel
          Spec.Match.Merge.equalityGroundedSemantic
          specIncoming specMatched specMerged ∧
        LeaBindingSolutionTheoryEquiv specMerged merged ∧
        ∀ valuation : String → Metta.Atom,
          HEBindingSatisfied valuation specMerged →
            applyClassSolution valuation (Metta.instantiate merged rhs) =
              applyClassSolution valuation rhs := by
  obtain ⟨specMatched, specMerged, hspecMatch, hspecMerge, hequiv,
      _hspecMergedNonvariable⟩ :=
    queryOp_hit_observational_anchor
      hincomingEquiv hincomingNonvariable hincomingNoFloat
      hmatch hmerge hsat
  refine ⟨specMatched, specMerged, hspecMatch, hspecMerge, hequiv, ?_⟩
  intro valuation hvaluation
  exact anchored_observable_inert hequiv hvaluation rhs

/-! ## Reachable query binding states -/

/-- The paired invariant at the executable/declarative query boundary.  The
spec and Lea records present the same complete solution theory, the spec
record remains normalized for the next declarative merge, and the Lea record
carries the canonical runtime invariant preserved by every loop-filtered
matcher merge. -/
structure LeaQueryOpBindingInvariant
    (spec : Bindings) (lea : Metta.Bindings) : Prop where
  solutionTheory : LeaBindingSolutionTheoryEquiv spec lea
  specAssignmentsNonVariable : HEAssignmentsNonVariable spec
  runtime :
    LeaTTaSpecConformance.LeaRuntimeBindingInvariant lea

/-- Empty spec and executable bindings initialize the paired query-state
invariant. -/
theorem leaQueryOpBindingInvariant_empty :
    LeaQueryOpBindingInvariant Bindings.empty Metta.Bindings.empty := by
  refine ⟨?_, ?_,
    LeaTTaSpecConformance.leaRuntimeBindingInvariant_empty⟩
  · intro valuation
    simp [HEBindingSatisfied, LeaBindingSatisfied,
      Bindings.empty, Metta.Bindings.empty]
  · intro key target hmem
    simp [Bindings.empty] at hmem

/-- **Unconditional reachable-state query hit soundness.**  A repaired
`queryOp` match+merge hit starting from the paired runtime invariant produces
a new paired invariant, an executable-independent spec match and merge, and
an observable that factors through their shared solution theory.  The
canonical runtime model discharges satisfiability; no joint-model assumption
is exposed at the theorem boundary. -/
theorem queryOp_hit_observational_sound
    {pattern query : OSLFCore.Atom} {specIncoming : Bindings}
    {incoming matched merged : Metta.Bindings} {rhs : Metta.Atom}
    (hinvariant : LeaQueryOpBindingInvariant specIncoming incoming)
    (hmatch : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hmerge : merged ∈ Metta.Bindings.merge incoming matched)
    (hloop : merged.hasLoop = false) :
    ∃ specMatched specMerged,
      Spec.Match.Merge.MatchRel
          Spec.Match.Merge.equalityGroundedSemantic
          query pattern specMatched ∧
        Spec.Match.Merge.MergeRel
          Spec.Match.Merge.equalityGroundedSemantic
          specIncoming specMatched specMerged ∧
        LeaQueryOpBindingInvariant specMerged merged ∧
        ∀ valuation : String → Metta.Atom,
          HEBindingSatisfied valuation specMerged →
            applyClassSolution valuation (Metta.instantiate merged rhs) =
              applyClassSolution valuation rhs := by
  have hmergedInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant merged :=
    LeaTTaSpecConformance.LeaRuntimeBindingInvariant.merge_matchOutput
      hinvariant.runtime
      (toLeaTTaAtom_noFloat pattern)
      (toLeaTTaAtom_noFloat query)
      hmatch hmerge hloop
  obtain ⟨specMatched, specMerged, hspecMatch, hspecMerge,
      hequiv, hspecMergedNonvariable⟩ :=
    queryOp_hit_observational_anchor
      hinvariant.solutionTheory
      hinvariant.specAssignmentsNonVariable
      hinvariant.runtime.noFloat hmatch hmerge
      ⟨leaClassSolution merged, hmergedInvariant.canonical.1⟩
  refine ⟨specMatched, specMerged, hspecMatch, hspecMerge,
    ⟨hequiv, hspecMergedNonvariable, hmergedInvariant⟩, ?_⟩
  intro valuation hvaluation
  exact anchored_observable_inert hequiv hvaluation rhs

/-- **Executable-independent equation-query-step soundness.**  One reachable,
loop-filtered LeaTTa match-and-merge hit realizes a spec equation-query step
at exactly the work-item boundary.  The theorem neither assumes nor concludes
recursive evaluation of the emitted atom. -/
theorem queryOp_hit_specEquationQueryStep_sound
    {pattern query : OSLFCore.Atom} {specIncoming : Bindings}
    {incoming matched merged : Metta.Bindings} {freshRhs : Metta.Atom}
    (hinvariant : LeaQueryOpBindingInvariant specIncoming incoming)
    (hdisjoint : VarsDisjoint query pattern)
    (hmatch : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hmerge : merged ∈ Metta.Bindings.merge incoming matched)
    (hloop : merged.hasLoop = false) :
    ∃ specMerged,
      Spec.Eval.EquationQueryStep query pattern specIncoming specMerged
          freshRhs (Metta.instantiate merged freshRhs) ∧
        LeaQueryOpBindingInvariant specMerged merged := by
  obtain ⟨specMatched, specMerged, hspecMatch, hspecMerge,
      hnextInvariant, hobservable⟩ :=
    queryOp_hit_observational_sound
      (rhs := freshRhs) hinvariant hmatch hmerge hloop
  refine ⟨specMerged, ?_, hnextInvariant⟩
  refine ⟨specMatched, hdisjoint, hspecMatch, hspecMerge, ?_, hobservable⟩
  exact ⟨leaClassSolution merged,
    (hnextInvariant.solutionTheory (leaClassSolution merged)).mpr
      hnextInvariant.runtime.canonical.1⟩

/-- The same seal at the executable one-candidate worklist boundary.  Actual
membership in `queryOpItemsOfRule` is decomposed into its repaired freshening,
matcher, merge, loop-filter, and instantiation witnesses; a representation
equation for the freshened pattern then connects that concrete item to the
spec matcher without tracing any HE executable matcher. -/
theorem queryOpItemsOfRule_observational_sound
    {pattern query : OSLFCore.Atom} {specIncoming : Bindings}
    {incoming : Metta.Bindings} {prev : Metta.Minimal.Stack}
    {counter : Nat} {rawLhs rawRhs : Metta.Atom}
    {item : Metta.Minimal.Item}
    (hinvariant : LeaQueryOpBindingInvariant specIncoming incoming)
    (hfreshPattern :
      (Metta.Minimal.freshenRuleAvoiding counter
        (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom query) incoming)
        rawLhs rawRhs).1.1 = toLeaTTaAtom pattern)
    (hitem : item ∈ Metta.Minimal.queryOpItemsOfRule
      prev (toLeaTTaAtom query) incoming counter (rawLhs, rawRhs)) :
    ∃ merged specMatched specMerged,
      item = Metta.Minimal.evalResult prev
          (Metta.instantiate merged
            (Metta.Minimal.freshenRuleAvoiding counter
              (Metta.Minimal.queryOpAvoid prev
                (toLeaTTaAtom query) incoming)
              rawLhs rawRhs).1.2) merged ∧
        Spec.Match.Merge.MatchRel
          Spec.Match.Merge.equalityGroundedSemantic
          query pattern specMatched ∧
        Spec.Match.Merge.MergeRel
          Spec.Match.Merge.equalityGroundedSemantic
          specIncoming specMatched specMerged ∧
        LeaQueryOpBindingInvariant specMerged merged ∧
        ∀ valuation : String → Metta.Atom,
          HEBindingSatisfied valuation specMerged →
            applyClassSolution valuation
                (Metta.instantiate merged
                  (Metta.Minimal.freshenRuleAvoiding counter
                    (Metta.Minimal.queryOpAvoid prev
                      (toLeaTTaAtom query) incoming)
                    rawLhs rawRhs).1.2) =
              applyClassSolution valuation
                (Metta.Minimal.freshenRuleAvoiding counter
                  (Metta.Minimal.queryOpAvoid prev
                    (toLeaTTaAtom query) incoming)
                  rawLhs rawRhs).1.2 := by
  have hitem' : item ∈ queryOpItemsOfRule
      prev (toLeaTTaAtom query) incoming counter (rawLhs, rawRhs) := hitem
  rw [mem_queryOpItemsOfRule_iff] at hitem'
  obtain ⟨matched, hmatch, merged, hmerge, hloop, hitemEq⟩ := hitem'
  rw [hfreshPattern] at hmatch
  obtain ⟨specMatched, specMerged, hspecMatch, hspecMerge,
      hnextInvariant, hobservable⟩ :=
    queryOp_hit_observational_sound
      (rhs :=
        (Metta.Minimal.freshenRuleAvoiding counter
          (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom query) incoming)
          rawLhs rawRhs).1.2)
      hinvariant hmatch hmerge hloop
  exact ⟨merged, specMatched, specMerged, hitemEq,
    hspecMatch, hspecMerge, hnextInvariant, hobservable⟩

/-- Capture-avoiding freshening makes the selected rule pattern disjoint from
the query variables visible at this work-item step. -/
theorem varsDisjoint_of_freshenRuleAvoiding_pattern
    {pattern query : OSLFCore.Atom} {incoming : Metta.Bindings}
    {prev : Metta.Minimal.Stack} {counter : Nat}
    {rawLhs rawRhs : Metta.Atom}
    (hfreshPattern :
      (Metta.Minimal.freshenRuleAvoiding counter
        (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom query) incoming)
        rawLhs rawRhs).1.1 = toLeaTTaAtom pattern) :
    VarsDisjoint query pattern := by
  intro name hquery hpattern
  have hfresh := Metta.Minimal.freshenRuleAvoiding_vars_fresh
    counter
    (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom query) incoming)
    rawLhs rawRhs
  have hfreshName :
      name ∈
        (Metta.Minimal.freshenRuleAvoiding counter
          (Metta.Minimal.queryOpAvoid prev
            (toLeaTTaAtom query) incoming)
          rawLhs rawRhs).1.1.vars ++
        (Metta.Minimal.freshenRuleAvoiding counter
          (Metta.Minimal.queryOpAvoid prev
            (toLeaTTaAtom query) incoming)
          rawLhs rawRhs).1.2.vars := by
    apply List.mem_append_left
    rw [hfreshPattern]
    exact hpattern
  apply hfresh name hfreshName
  simp only [Metta.Minimal.queryOpAvoid, List.mem_append]
  exact Or.inl (Or.inr hquery)

/-- Public one-candidate equation-query seal.  Membership in the repaired
LeaTTa work-item generator supplies the hygienically freshened pattern and RHS,
the exact emitted `evalResult`, a spec equation-query-step derivation, and the
paired invariant required by the next reachable query step.

This theorem seals matcher, merge, and equation-query-step soundness only.  It
does not claim the separately scoped recursive evaluator/call layer. -/
theorem queryOpItemsOfRule_specEquationQueryStep_sound
    {pattern query : OSLFCore.Atom} {specIncoming : Bindings}
    {incoming : Metta.Bindings} {prev : Metta.Minimal.Stack}
    {counter : Nat} {rawLhs rawRhs : Metta.Atom}
    {item : Metta.Minimal.Item}
    (hinvariant : LeaQueryOpBindingInvariant specIncoming incoming)
    (hfreshPattern :
      (Metta.Minimal.freshenRuleAvoiding counter
        (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom query) incoming)
        rawLhs rawRhs).1.1 = toLeaTTaAtom pattern)
    (hitem : item ∈ Metta.Minimal.queryOpItemsOfRule
      prev (toLeaTTaAtom query) incoming counter (rawLhs, rawRhs)) :
    ∃ merged specMerged freshRhs,
      freshRhs =
          (Metta.Minimal.freshenRuleAvoiding counter
            (Metta.Minimal.queryOpAvoid prev
              (toLeaTTaAtom query) incoming)
            rawLhs rawRhs).1.2 ∧
        item = Metta.Minimal.evalResult prev
          (Metta.instantiate merged freshRhs) merged ∧
        Spec.Eval.EquationQueryStep query pattern specIncoming specMerged
          freshRhs (Metta.instantiate merged freshRhs) ∧
        LeaQueryOpBindingInvariant specMerged merged := by
  obtain ⟨merged, specMatched, specMerged, hitemEq,
      hspecMatch, hspecMerge, hnextInvariant, hobservable⟩ :=
    queryOpItemsOfRule_observational_sound
      hinvariant hfreshPattern hitem
  let freshRhs :=
    (Metta.Minimal.freshenRuleAvoiding counter
      (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom query) incoming)
      rawLhs rawRhs).1.2
  refine ⟨merged, specMerged, freshRhs, rfl, ?_, ?_, hnextInvariant⟩
  · exact hitemEq
  · refine ⟨specMatched,
      varsDisjoint_of_freshenRuleAvoiding_pattern hfreshPattern,
      hspecMatch, hspecMerge, ?_, hobservable⟩
    exact ⟨leaClassSolution merged,
      (hnextInvariant.solutionTheory (leaClassSolution merged)).mpr
        hnextInvariant.runtime.canonical.1⟩

/-- A query hit started from empty bindings is unconditionally anchored: the
direct matcher soundness theorem supplies a model of the match output, and
the exact merge solution theorem transports that model through the empty
incoming binding. -/
theorem queryOp_hit_observational_sound_empty_incoming
    {pattern query : OSLFCore.Atom}
    {matched merged : Metta.Bindings} {rhs : Metta.Atom}
    (hmatch : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hmerge : merged ∈
      Metta.Bindings.merge Metta.Bindings.empty matched) :
    ∃ specMatched specMerged,
      Spec.Match.Merge.MatchRel
          Spec.Match.Merge.equalityGroundedSemantic
          query pattern specMatched ∧
        Spec.Match.Merge.MergeRel
          Spec.Match.Merge.equalityGroundedSemantic
          Bindings.empty specMatched specMerged ∧
        LeaBindingSolutionTheoryEquiv specMerged merged ∧
        ∀ valuation : String → Metta.Atom,
          HEBindingSatisfied valuation specMerged →
            applyClassSolution valuation (Metta.instantiate merged rhs) =
              applyClassSolution valuation rhs := by
  obtain ⟨valuation, hmatchedSatisfied⟩ :=
    LeaTTaSpecConformance.leaMatchAtoms_output_satisfiable
      (toLeaTTaAtom_noFloat pattern)
      (toLeaTTaAtom_noFloat query) hmatch
  have hmatchedNoFloat : LeaBindingsNoFloat matched :=
    leaMatchAtoms_result_noFloat
      (toLeaTTaAtom_noFloat pattern)
      (toLeaTTaAtom_noFloat query) hmatch
  have hemptySatisfied :
      LeaBindingSatisfied valuation Metta.Bindings.empty := by
    simp [LeaBindingSatisfied, Metta.Bindings.empty]
  have hmergedSatisfied : LeaBindingSatisfied valuation merged :=
    (leaMerge_solution_iff valuation
      (by simp [LeaBindingsNoFloat, Metta.Bindings.empty])
      hmatchedNoFloat hmerge).mpr
        ⟨hemptySatisfied, hmatchedSatisfied⟩
  have hincomingEquiv : LeaBindingSolutionTheoryEquiv
      Bindings.empty Metta.Bindings.empty := by
    intro observer
    simp [HEBindingSatisfied, LeaBindingSatisfied,
      Bindings.empty, Metta.Bindings.empty]
  have hincomingNonvariable :
      HEAssignmentsNonVariable Bindings.empty := by
    intro key target hmem
    simp [Bindings.empty] at hmem
  exact queryOp_hit_observational_sound_of_satisfiable
    hincomingEquiv hincomingNonvariable
    (by simp [LeaBindingsNoFloat, Metta.Bindings.empty])
    hmatch hmerge ⟨valuation, hmergedSatisfied⟩

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
