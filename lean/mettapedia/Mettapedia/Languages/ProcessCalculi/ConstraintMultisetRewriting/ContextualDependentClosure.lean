import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensus

/-!
# The stratified fragment: a closure class beyond the dynamic pattern fragment

Decomposition produces **heterogeneous equations**: twins whose annotations are equal only once the
pieces before them are solved. `InFragmentStore` asks each equation's annotations to be equal types
outright, so the pieces leave it (R97). The class here keeps the fragment's conditions on the sides and
relaxes the condition on the annotations, in the order of the store, as Gundry and McBride's twins do:

* **fragment sides**: every normal form of each opened side has Miller occurrences and every
  metavariable at its arity (the side conditions of `InFragment`);
* **stratified annotations**: the two annotations of an equation are equal types under every solution
  of the equations before it.

The class is read from the store and its solutions alone, never from a solver. It contains the dynamic
pattern fragment (`stratified_of_fragment`). The first equation of a nonempty stratified store has equal
annotations (`Stratified.head_typeEq`) and fragment sides: it is an equation of the fragment up to the
normal form of its annotation, the equation on which firing is to be read. The class is kept when a
valid first equation is dropped (`Stratified.drop_valid`) and when the first equation is replaced by one
with the same solutions, fragment sides and equal annotations (`Stratified.replace_head`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)

/-- **Fragment sides**: the side conditions of the dynamic pattern fragment, at the opening depth of the
left side. -/
def FragmentSides {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : Prop :=
  (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.1.2.code) code → Normal rules code →
    InFragmentCode Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code) ∧
  (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.2.2.code) code → Normal rules code →
    InFragmentCode Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code)

/-- **Stratified annotations**: under every solution of the equations before it, the two annotations of
an equation are equal types. -/
def StratifiedAt {Θ : Context rules} (before : EquationStore (TotalTerm Θ)) (equation : Equation (TotalTerm Θ)) :
    Prop :=
  ∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Models σ before →
    TypeEq rules Δ.raw (subst σ.substitution equation.1.1.code) (subst σ.substitution equation.2.1.code)

/-- **The stratified fragment**: at every position of the store, the equation there has fragment sides
and annotations equal under every solution of the equations before it. -/
def Stratified {Θ : Context rules} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  ∀ (before after : EquationStore (TotalTerm Θ)) (equation : Equation (TotalTerm Θ)),
    problem = before ++ equation :: after → FragmentSides equation ∧ StratifiedAt levels before equation

variable {levels}

/-- **The stratified fragment contains the dynamic pattern fragment.** -/
theorem stratified_of_fragment {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (inside : InFragmentStore problem) : Stratified levels problem := by
  intro before after equation split
  have member : equation ∈ problem := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨same, _, _, leftSide, rightSide⟩ := inside equation member
  exact ⟨⟨leftSide, rightSide⟩, fun σ _ => reindex_typeEquality same σ⟩

/-- **The first equation of a stratified store has equal annotations.** -/
theorem Stratified.head_typeEq {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (stratified : Stratified levels (equation :: rest)) :
    TypeEq rules Θ.raw equation.1.1.code equation.2.1.code := by
  have atHead := (stratified [] rest equation rfl).2 (𝟙 Θ) (fun _ member => absurd member List.not_mem_nil)
  change TypeEq rules Θ.raw (subst ids equation.1.1.code) (subst ids equation.2.1.code) at atHead
  rwa [subst_ids, subst_ids] at atHead

/-- **The first equation of a stratified store has fragment sides.** -/
theorem Stratified.head_sides {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (stratified : Stratified levels (equation :: rest)) :
    FragmentSides equation :=
  (stratified [] rest equation rfl).1

/-- **The first equation of a stratified store, with a normal annotation that has a Π binder for every
abstraction of its left side, is an equation of the dynamic pattern fragment.** -/
theorem Stratified.head_inFragment {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (stratified : Stratified levels (equation :: rest))
    (normal : Normal rules equation.1.1.code)
    (depth : ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤ piCount equation.1.1.code) :
    InFragment equation :=
  ⟨stratified.head_typeEq, normal, depth, stratified.head_sides.1, stratified.head_sides.2⟩

/-- **Dropping a first equation that holds at every solution keeps the class.** -/
theorem Stratified.drop_valid {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (stratified : Stratified levels (equation :: rest))
    (valid : ∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Solves σ equation) :
    Stratified levels rest := by
  intro before after later split
  have whole := stratified (equation :: before) after later (by rw [split]; rfl)
  refine ⟨whole.1, fun σ solved => whole.2 σ ?_⟩
  intro e member
  rcases List.mem_cons.mp member with rfl | inside
  · exact valid σ
  · exact solved e inside

/-- **Replacing the first equation by one with the same solutions, fragment sides and equal annotations
keeps the class.** -/
theorem Stratified.replace_head {Θ : Context rules} {equation equation' : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (stratified : Stratified levels (equation :: rest))
    (same : ∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Solves σ equation' ↔ (frames levels).Solves σ equation)
    (sides : FragmentSides equation')
    (annotations : TypeEq rules Θ.raw equation'.1.1.code equation'.2.1.code) :
    Stratified levels (equation' :: rest) := by
  intro before after later split
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      exact ⟨sides, fun σ _ => reindex_typeEquality annotations σ⟩
  | cons first before =>
      simp only [List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      have whole := stratified (equation :: before) after later rfl
      refine ⟨whole.1, fun σ solved => whole.2 σ ?_⟩
      intro e member
      rcases List.mem_cons.mp member with rfl | inside
      · exact (same σ).mp (solved _ List.mem_cons_self)
      · exact solved e (List.mem_cons_of_mem _ inside)

/-! ## Closure under the kinds of progress -/

theorem models_append_iff {Θ Δ : Context rules} (σ : Δ ⟶ Θ) (first second : EquationStore (TotalTerm Θ)) :
    (frames levels).Models σ (first ++ second) ↔ (frames levels).Models σ first ∧ (frames levels).Models σ second :=
  Frames.models_append (X := frames levels) σ first second

/-- **Mapping every equation to one with the same solutions keeps the class**, when the map keeps fragment
sides and stratified annotations. -/
theorem Stratified.map {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (stratified : Stratified levels problem) (f : Equation (TotalTerm Θ) → Equation (TotalTerm Θ))
    (same : ∀ (equation : Equation (TotalTerm Θ)) {Δ : Context rules} (σ : Δ ⟶ Θ),
      (frames levels).Solves σ (f equation) ↔ (frames levels).Solves σ equation)
    (sides : ∀ equation ∈ problem, FragmentSides equation → FragmentSides (f equation))
    (annotations : ∀ equation ∈ problem, ∀ before : EquationStore (TotalTerm Θ),
      StratifiedAt levels before equation → StratifiedAt levels before (f equation)) :
    Stratified levels (problem.map f) := by
  intro before' after' later split
  obtain ⟨before, rest, rfl, rfl, mapped⟩ := List.map_eq_append_iff.mp split
  obtain ⟨equation, after, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
  have member : equation ∈ before ++ equation :: after := List.mem_append_right _ List.mem_cons_self
  obtain ⟨sides₀, at₀⟩ := stratified before after equation rfl
  refine ⟨sides equation member sides₀, fun σ solved => annotations equation member before at₀ σ ?_⟩
  intro e inside
  exact (same e σ).mp (solved (f e) (List.mem_map.mpr ⟨e, inside, rfl⟩))

/-- **Replacing one equation by pieces with exactly its solutions keeps the class**, when the pieces have
fragment sides and stratified annotations among themselves, after the equations before them. With no pieces
this is dropping an equation that holds at every solution. -/
theorem Stratified.splice {Θ : Context rules} {before after pieces : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (stratified : Stratified levels (before ++ equation :: after))
    (exact : ∀ {Δ : Context rules} (σ : Δ ⟶ Θ),
      (frames levels).Models σ pieces ↔ (frames levels).Solves σ equation)
    (sides : ∀ piece ∈ pieces, FragmentSides piece)
    (internal : ∀ (first last : EquationStore (TotalTerm Θ)) (piece : Equation (TotalTerm Θ)),
      pieces = first ++ piece :: last → StratifiedAt levels (before ++ first) piece) :
    Stratified levels (before ++ (pieces ++ after)) := by
  -- an equation after the pieces keeps its condition: the pieces stand for the replaced equation
  have afterPart : ∀ (middle rest : EquationStore (TotalTerm Θ)) (later : Equation (TotalTerm Θ)),
      after = middle ++ later :: rest →
      FragmentSides later ∧ StratifiedAt levels (before ++ (pieces ++ middle)) later := by
    intro middle rest later split
    have whole := stratified (before ++ equation :: middle) rest later (by rw [split]; simp)
    refine ⟨whole.1, fun σ solved => whole.2 σ ?_⟩
    rw [models_append_iff, models_append_iff] at solved
    rw [models_append_iff]
    refine ⟨solved.1, ?_⟩
    intro e member
    rcases List.mem_cons.mp member with rfl | inside
    · exact (exact σ).mp solved.2.1
    · exact solved.2.2 e inside
  intro before' after' later split
  rcases List.append_eq_append_iff.mp split with ⟨cs, rfl, rest⟩ | ⟨bs, sameBefore, rest⟩
  · rcases List.append_eq_append_iff.mp rest with ⟨ds, rfl, inAfter⟩ | ⟨ds, inPieces, tail⟩
    · have := afterPart ds after' later inAfter
      simpa [List.append_assoc] using this
    · rcases ds with _ | ⟨first, ds⟩
      · simp only [List.append_nil] at inPieces
        subst inPieces
        have := afterPart [] after' later (by simpa using tail.symm)
        simpa using this
      · simp only [List.cons_append, List.cons.injEq] at tail
        obtain ⟨rfl, rfl⟩ := tail
        exact ⟨sides _ (by rw [inPieces]; exact List.mem_append_right _ List.mem_cons_self),
          internal cs ds later inPieces⟩
  · rcases List.cons_eq_append_iff.mp rest with ⟨rfl, inRest⟩ | ⟨bs', rfl, tail⟩
    · simp only [List.append_nil] at sameBefore
      subst sameBefore
      rcases List.append_eq_cons_iff.mp inRest with ⟨rfl, inAfter⟩ | ⟨ps, inPieces, tail⟩
      · have := afterPart [] after' later inAfter.symm.symm
        simpa using this
      · refine ⟨sides _ (by rw [inPieces]; exact List.mem_cons_self), ?_⟩
        have atPiece : StratifiedAt levels (before ++ []) later := internal [] ps later inPieces
        rwa [List.append_nil] at atPiece
    · have whole := stratified before' (bs' ++ equation :: after) later (by rw [sameBefore]; simp)
      exact whole

/-! ## Stratification after a fixed prefix -/

/-- **Stratified after a prefix**: every equation of the store has fragment sides and annotations equal under
every solution of the prefix and of the equations before it. -/
def StratifiedFrom (levels : LevelModel rules L) {Θ : Context rules} (fixed problem : EquationStore (TotalTerm Θ)) :
    Prop :=
  ∀ (before after : EquationStore (TotalTerm Θ)) (equation : Equation (TotalTerm Θ)),
    problem = before ++ equation :: after → FragmentSides equation ∧ StratifiedAt levels (fixed ++ before) equation

theorem stratifiedFrom_nil {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)} :
    StratifiedFrom levels [] problem ↔ Stratified levels problem := by
  unfold StratifiedFrom Stratified
  simp only [List.nil_append]

theorem StratifiedFrom.nil {Θ : Context rules} (fixed : EquationStore (TotalTerm Θ)) :
    StratifiedFrom levels fixed [] := by
  intro before after equation split
  cases before <;> cases split

theorem StratifiedFrom.head {Θ : Context rules} {fixed rest : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (stratified : StratifiedFrom levels fixed (equation :: rest)) :
    FragmentSides equation ∧ StratifiedAt levels fixed equation := by
  have := stratified [] rest equation rfl
  simpa using this

theorem StratifiedFrom.tail {Θ : Context rules} {fixed rest : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (stratified : StratifiedFrom levels fixed (equation :: rest)) :
    StratifiedFrom levels (fixed ++ [equation]) rest := by
  intro before after later split
  have := stratified (equation :: before) after later (by rw [split]; rfl)
  simpa [List.append_assoc] using this

theorem StratifiedFrom.cons {Θ : Context rules} {fixed rest : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (sides : FragmentSides equation) (atFixed : StratifiedAt levels fixed equation)
    (later : StratifiedFrom levels (fixed ++ [equation]) rest) : StratifiedFrom levels fixed (equation :: rest) := by
  intro before after other split
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      refine ⟨sides, ?_⟩
      rw [List.append_nil]
      exact atFixed
  | cons first before =>
      simp only [List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      have := later before after other rfl
      simpa [List.append_assoc] using this

/-- **A stronger prefix keeps the class.** -/
theorem StratifiedFrom.strengthen {Θ : Context rules} {fixed fixed' problem : EquationStore (TotalTerm Θ)}
    (stratified : StratifiedFrom levels fixed problem)
    (stronger : ∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Models σ fixed' → (frames levels).Models σ fixed) :
    StratifiedFrom levels fixed' problem := by
  intro before after equation split
  obtain ⟨sides, atBefore⟩ := stratified before after equation split
  refine ⟨sides, fun σ solved => atBefore σ ?_⟩
  rw [models_append_iff] at solved ⊢
  exact ⟨stronger σ solved.1, solved.2⟩

/-- **Dropping equations that hold at every solution keeps the class.** The kept store is read through a
selection of the equations: `keep equation = false` only for equations that hold at every solution. -/
theorem StratifiedFrom.filter_valid {Θ : Context rules} (keep : Equation (TotalTerm Θ) → Bool)
    (valid : ∀ equation, keep equation = false → ∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Solves σ equation) :
    ∀ {fixed fixed' : EquationStore (TotalTerm Θ)} (problem : EquationStore (TotalTerm Θ)),
      (∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Models σ fixed' → (frames levels).Models σ fixed) →
      StratifiedFrom levels fixed problem → StratifiedFrom levels fixed' (problem.filter keep)
  | _, fixed', [], _, _ => StratifiedFrom.nil fixed'
  | fixed, fixed', equation :: rest, stronger, stratified => by
      obtain ⟨sides, atFixed⟩ := stratified.head
      by_cases kept : keep equation = true
      · rw [List.filter_cons_of_pos kept]
        refine StratifiedFrom.cons sides (fun σ solved => atFixed σ (stronger σ solved)) ?_
        refine StratifiedFrom.filter_valid keep valid rest (fixed := fixed ++ [equation]) (fun σ solved => ?_)
          stratified.tail
        rw [models_append_iff] at solved ⊢
        exact ⟨stronger σ solved.1, solved.2⟩
      · rw [List.filter_cons_of_neg kept]
        refine StratifiedFrom.filter_valid keep valid rest (fixed := fixed ++ [equation]) (fun σ solved => ?_)
          stratified.tail
        rw [models_append_iff]
        refine ⟨stronger σ solved, ?_⟩
        intro e member
        rw [List.mem_singleton.mp member]
        exact valid equation (by simpa using kept) σ

end ContextualDependentClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
