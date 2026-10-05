import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaNameSupply

/-!
# Variable scope of emitted computation bodies

The allocation bound describes the actual emitted syntax. It is used to keep
later control variables out of already emitted operands and continuations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)

def UsesBefore (bound : Nat) (atom : Atom) : Prop :=
  ∀ name, AtomOccurs atom name → ∃ index, index < bound ∧ name = freshName index

theorem UsesBefore.mono {first last : Nat} {atom : Atom}
    (bounded : UsesBefore first atom) (later : first ≤ last) : UsesBefore last atom := by
  intro name occurrence
  obtain ⟨index, before, same⟩ := bounded name occurrence
  exact ⟨index, before.trans_le later, same⟩

@[simp] theorem usesBefore_symbol (bound : Nat) (name : String) :
    UsesBefore bound (.symbol name) := by
  intro name occurrence
  cases occurrence

@[simp] theorem usesBefore_grounded (bound : Nat) (value) :
    UsesBefore bound (.grounded value) := by
  intro name occurrence
  cases occurrence

@[simp] theorem usesBefore_freshName (bound index : Nat) :
    UsesBefore bound (.var (freshName index)) ↔ index < bound := by
  constructor
  · intro bounded
    obtain ⟨other, before, same⟩ := bounded _ (.var _)
    rw [freshName_injective same]
    exact before
  · intro before name occurrence
    cases occurrence
    exact ⟨index, before, rfl⟩

@[simp] theorem usesBefore_call (bound : Nat) (head : String) (arguments : List Atom) :
    UsesBefore bound (call head arguments) ↔ ∀ atom ∈ arguments, UsesBefore bound atom := by
  constructor
  · intro bounded atom member name occurrence
    exact bounded name ((occurs_call_iff _ _ _).mpr ⟨atom, member, occurrence⟩)
  · intro bounded name occurrence
    obtain ⟨atom, member, occurrence⟩ := (occurs_call_iff _ _ _).mp occurrence
    exact bounded atom member name occurrence

theorem usesBefore_data (bound : Nat) (term : Term) :
    UsesBefore bound (MeTTaData.encode term) := by
  intro name occurrence
  exact False.elim (data_has_no_variables (MeTTaData.encode_data term) name occurrence)

theorem usesBefore_sequence (bound : Nat) (items : List Atom)
    (bounded : ∀ atom ∈ items, UsesBefore bound atom) :
    UsesBefore bound (sequenceAtom items) := by
  induction items with
  | nil => exact usesBefore_symbol _ _
  | cons head rest ih =>
      have first := bounded head (by simp)
      have tail := ih (fun atom member => bounded atom (by simp [member]))
      simpa [sequenceAtom] using And.intro first tail

theorem UsesBefore.excludes {bound : Nat} {atom : Atom}
    (bounded : UsesBefore bound atom) (index : Nat) (later : bound ≤ index) :
    ¬AtomOccurs atom (freshName index) := by
  intro occurrence
  obtain ⟨other, before, same⟩ := bounded _ occurrence
  have equalIndex := freshName_injective same
  omega

theorem usesBefore_selectBranches (bound : Nat) (target : Atom)
    (branches : List (Atom × Atom)) (otherwise : Atom)
    (targetBound : UsesBefore bound target)
    (branchBound : ∀ row ∈ branches,
      UsesBefore bound row.1 ∧ UsesBefore bound row.2)
    (otherwiseBound : UsesBefore bound otherwise) :
    UsesBefore bound (selectBranches target branches otherwise) := by
  induction branches with
  | nil => exact otherwiseBound
  | cons row rest ih =>
      have rowBound := branchBound row (by simp)
      have restBound := ih (fun pair member => branchBound pair (by simp [member]))
      simpa [selectBranches] using ⟨targetBound, rowBound.1, rowBound.2, restBound⟩

theorem bindResult_scope (source name continuation : Atom) (first : Nat)
    (sourceBound : UsesBefore first source) (nameBound : UsesBefore first name)
    (continuationBound : UsesBefore first continuation) :
    (bindResult source name continuation first).2 = first + 1 ∧
      UsesBefore (first + 1) (bindResult source name continuation first).1 := by
  have sourceLater := sourceBound.mono (Nat.le_succ first)
  have nameLater := nameBound.mono (Nat.le_succ first)
  have continuationLater := continuationBound.mono (Nat.le_succ first)
  change first + 1 = first + 1 ∧ UsesBefore (first + 1)
    (call "chain" [call "function" [source], .var (freshName first),
      selectBranches (.var (freshName first))
        [(value name, continuation),
         (.symbol "nik:Failure", returned (.symbol "nik:Failure")),
         (.symbol "nik:Exhausted", returned (.symbol "nik:Exhausted"))]
        (returned (.symbol "nik:Malformed"))])
  simp [selectBranches, returned, value, sourceLater, nameLater, continuationLater]

theorem invoke_scope (program : Program) (fuel : Atom) (head : String)
    (arguments : List Atom) (bound : Nat)
    (fuelBound : UsesBefore bound fuel)
    (argumentsBound : ∀ atom ∈ arguments, UsesBefore bound atom) :
    UsesBefore bound (invoke program fuel head arguments) := by
  have sequenceBound := usesBefore_sequence bound arguments argumentsBound
  have withHead := usesBefore_sequence bound (MeTTaData.encode (.sym head) :: arguments)
    (by simpa using And.intro (usesBefore_data bound (.sym head)) argumentsBound)
  unfold invoke
  split
  · simpa using And.intro fuelBound sequenceBound
  · split
    · simpa using sequenceBound
    · simpa [value] using withHead

theorem returnInvocation_scope (invocation : Atom) (first : Nat)
    (invocationBound : UsesBefore first invocation) :
    first ≤ (returnInvocation invocation first).2 ∧
      UsesBefore (returnInvocation invocation first).2
        (returnInvocation invocation first).1 := by
  unfold returnInvocation
  split
  · change first ≤ first ∧ UsesBefore first (returned _)
    simpa [returned] using invocationBound
  · have later := invocationBound.mono (show first ≤ first + 2 by omega)
    change first ≤ first + 2 ∧ UsesBefore (first + 2)
      (call "chain" [call "context-space" [], .var (freshName first),
        call "chain" [call "metta" [_, .symbol "%Undefined%", .var (freshName first)],
          .var (freshName (first + 1)), returned (.var (freshName (first + 1)))]])
    simp [returned, later]
  · have later := invocationBound.mono (Nat.le_succ first)
    change first ≤ first + 1 ∧ UsesBefore (first + 1)
      (call "chain" [call "eval" [invocation], .var (freshName first),
        returned (.var (freshName first))])
    simp [returned, later]

theorem withFuel_scope (fuel : Atom) (build : Atom → Emit Atom) (first : Nat)
    (fuelBound : UsesBefore first fuel)
    (bodyBound : first + 1 ≤ (build (.var (freshName first)) (first + 1)).2 ∧
      UsesBefore (build (.var (freshName first)) (first + 1)).2
        (build (.var (freshName first)) (first + 1)).1) :
    first < (withFuel fuel build first).2 ∧
      UsesBefore (withFuel fuel build first).2 (withFuel fuel build first).1 := by
  let emitted := build (.var (freshName first)) (first + 1)
  change first + 1 ≤ emitted.2 ∧ UsesBefore emitted.2 emitted.1 at bodyBound
  have remainingBefore : first < emitted.2 + 1 := by omega
  have fuelLater := fuelBound.mono (show first ≤ emitted.2 + 1 by omega)
  have bodyLater := bodyBound.2.mono (Nat.le_succ emitted.2)
  change first < emitted.2 + 1 ∧ UsesBefore (emitted.2 + 1)
    (call "chain" [call "eval" [call "==" [fuel, .grounded (.int 0)]],
      .var (freshName emitted.2),
      call "unify" [.var (freshName emitted.2), .grounded (.bool true),
        returned (.symbol "nik:Exhausted"),
        call "chain" [call "eval" [call "-" [fuel, .grounded (.int 1)]],
          .var (freshName first), emitted.1]]])
  simp [returned, fuelLater, bodyLater, remainingBefore]

mutual

theorem expression_scope (program : Program) (names : Names) (fuel : Atom)
    (source : Term) (first : Nat)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel) :
    first < (expression program names fuel source first).2 ∧
      UsesBefore (expression program names fuel source first).2
        (expression program names fuel source first).1 := by
  unfold expression
  apply withFuel_scope fuel _ first fuelBound
  have remainingBound : UsesBefore (first + 1) (.var (freshName first)) := by simp
  have namesNext : ∀ entry ∈ names, UsesBefore (first + 1) entry.2 :=
    fun entry member => (namesBound entry member).mono (Nat.le_succ first)
  split
  case h_1 =>
    rename_i name
    cases found : names.find? (fun entry => entry.1 == name) with
    | none =>
        change first + 1 ≤ first + 1 ∧ UsesBefore (first + 1) (returned _)
        simp [returned]
    | some entry =>
        have bounded := namesNext entry (List.mem_of_find?_eq_some found)
        change first + 1 ≤ first + 1 ∧ UsesBefore (first + 1) (returned _)
        simpa [found, returned, value] using bounded
  case h_2 | h_3 | h_4 | h_8 =>
    refine ⟨le_rfl, ?_⟩
    change UsesBefore (first + 1) (returned (value (MeTTaData.encode _)))
    simpa [returned, value] using usesBefore_data (first + 1) _
  case h_7 | h_9 =>
    refine ⟨le_rfl, ?_⟩
    change UsesBefore (first + 1) (returned (.symbol "nik:Failure"))
    simp [returned]
  case h_5 | h_11 =>
    apply expressions_scope program names (.var (freshName first)) _ _ (first + 1)
      namesNext remainingBound
    intro next _ arguments argumentsBound
    refine ⟨le_rfl, ?_⟩
    change UsesBefore next (returned (value (call _ [sequenceAtom arguments])))
    simpa [returned, value] using usesBefore_sequence next arguments argumentsBound
  case h_10 =>
    apply expressions_scope program names (.var (freshName first)) _ _ (first + 1)
      namesNext remainingBound
    intro next later arguments argumentsBound
    apply returnInvocation_scope
    exact invoke_scope program _ _ arguments next (remainingBound.mono later) argumentsBound
  case h_6 =>
    rename_i name bound body
    let assigned := expression program names (.var (freshName first)) bound (first + 2)
    have assignedBound := expression_scope program names (.var (freshName first)) bound
      (first + 2) (fun entry member => (namesBound entry member).mono (by omega))
      ((usesBefore_freshName (first + 2) first).mpr (by omega))
    change first + 2 < assigned.2 ∧ UsesBefore assigned.2 assigned.1 at assignedBound
    let target := Atom.var (freshName (first + 1))
    let bodyCode := expression program ((name, target) :: names)
      (.var (freshName first)) body assigned.2
    have bodyBound := expression_scope program ((name, target) :: names)
      (.var (freshName first)) body assigned.2 (by
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact (usesBefore_freshName assigned.2 (first + 1)).mpr (by omega)
        · exact (namesBound entry member).mono (by omega))
      ((usesBefore_freshName assigned.2 first).mpr (by omega))
    change assigned.2 < bodyCode.2 ∧ UsesBefore bodyCode.2 bodyCode.1 at bodyBound
    have resultBound := bindResult_scope assigned.1 target bodyCode.1 bodyCode.2
      (assignedBound.2.mono bodyBound.1.le)
      ((usesBefore_freshName bodyCode.2 (first + 1)).mpr (by omega)) bodyBound.2
    change first + 1 ≤ (bindResult assigned.1 target bodyCode.1 bodyCode.2).2 ∧
      UsesBefore (bindResult assigned.1 target bodyCode.1 bodyCode.2).2
        (bindResult assigned.1 target bodyCode.1 bodyCode.2).1
    rw [resultBound.1]
    exact ⟨by omega, resultBound.2⟩
termination_by sizeOf source

theorem expressions_scope (program : Program) (names : Names) (fuel : Atom)
    (sources : List Term) (continuation : List Atom → Emit Atom) (first : Nat)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel)
    (continuationBound : ∀ next, first ≤ next → ∀ arguments,
      (∀ atom ∈ arguments, UsesBefore next atom) →
      next ≤ (continuation arguments next).2 ∧
        UsesBefore (continuation arguments next).2 (continuation arguments next).1) :
    first ≤ (expressions program names fuel sources continuation first).2 ∧
      UsesBefore (expressions program names fuel sources continuation first).2
        (expressions program names fuel sources continuation first).1 := by
  cases sources with
  | nil => simpa only [expressions] using continuationBound first le_rfl [] (by simp)
  | cons head rest =>
      let headCode := expression program names fuel head (first + 1)
      have headBound := expression_scope program names fuel head (first + 1)
        (fun entry member => (namesBound entry member).mono (Nat.le_succ first))
        (fuelBound.mono (Nat.le_succ first))
      change first + 1 < headCode.2 ∧ UsesBefore headCode.2 headCode.1 at headBound
      let tailCode := expressions program names fuel rest
        (fun values => continuation (.var (freshName first) :: values)) headCode.2
      have tailBound := expressions_scope program names fuel rest
        (fun values => continuation (.var (freshName first) :: values)) headCode.2
        (fun entry member => (namesBound entry member).mono (by omega))
        (fuelBound.mono (by omega)) (by
          intro next later arguments argumentsBound
          apply continuationBound next (by omega)
          simpa using And.intro
            ((usesBefore_freshName next first).mpr (by omega)) argumentsBound)
      change headCode.2 ≤ tailCode.2 ∧ UsesBefore tailCode.2 tailCode.1 at tailBound
      have bound := bindResult_scope headCode.1 (.var (freshName first)) tailCode.1 tailCode.2
        (headBound.2.mono tailBound.1)
        ((usesBefore_freshName tailCode.2 first).mpr (by omega)) tailBound.2
      rw [expressions]
      change first ≤ (bindResult headCode.1 (.var (freshName first)) tailCode.1 tailCode.2).2 ∧
        UsesBefore (bindResult headCode.1 (.var (freshName first)) tailCode.1 tailCode.2).2
          (bindResult headCode.1 (.var (freshName first)) tailCode.1 tailCode.2).1
      rw [bound.1]
      exact ⟨by omega, bound.2⟩
termination_by sizeOf sources

end

/-- Matching supplies the name table used by the body, at its actual allocation bound. -/
theorem namesForMatch_scope (environment : Env) (first : Nat) :
    ∀ entry ∈ namesForMatch first environment,
      UsesBefore (first + environment.length) entry.2 := by
  induction environment generalizing first with
  | nil => simp
  | cons head rest ih =>
      intro entry member
      rw [namesForMatch_cons] at member
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (first + 1) entry member

theorem matched_body_scope (program : Program) (parameters arguments : List Term)
    (environment : Env) (matched : matchTerms parameters arguments = some environment)
    (body : Term) (fuel : Atom) (first : Nat) (fuelBound : UsesBefore first fuel) :
    let names := (patterns parameters first).1.2
    let start := (patterns parameters first).2
    start < (expression program names fuel body start).2 ∧
      UsesBefore (expression program names fuel body start).2
        (expression program names fuel body start).1 := by
  dsimp only
  apply expression_scope
  · rw [patterns_names_of_match parameters arguments environment matched,
      patterns_end_of_match parameters arguments environment matched]
    exact namesForMatch_scope environment first
  · exact fuelBound.mono (patterns_name_bounds parameters first).1

/-- A subsequent allocation cannot occur anywhere in an earlier complete body. -/
theorem expression_excludes_later_names (program : Program) (names : Names) (fuel : Atom)
    (source : Term) (first index : Nat)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel)
    (later : (expression program names fuel source first).2 ≤ index) :
    ¬AtomOccurs (expression program names fuel source first).1 (freshName index) :=
  (expression_scope program names fuel source first namesBound fuelBound).2.excludes index later

/-- Nested source shadowing still leaves the next target allocation private. -/
theorem nested_shadowing_scope (program : Program) (name : String) (first : Nat) :
    let source := Term.expr [.sym "let", .var name, .sym "outer",
      .expr [.sym "let", .var name, .var name, .var name]]
    let emitted := expression program [] (.grounded (.int 3)) source first
    ¬AtomOccurs emitted.1 (freshName emitted.2) := by
  dsimp only
  exact expression_excludes_later_names program [] _ _ first _ (by simp)
    (usesBefore_grounded _ _) le_rfl

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
