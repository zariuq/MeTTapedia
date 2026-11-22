import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocated
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNameTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientControls

/-!
# Controls of the located program

Each hypothesis of `ReflLocated` with the example that fails without it.

* **Heating needs the name frame.**
  * `root_heat_fires_on_input_at_quotient`: at `QX` the root heat takes `onAB @ Root`, a row that is no
    parallel composition (through the exact arrow, from `ReflQuotient.Controls.heat_admitted_at_quotient`);
    `root_heat_refused_at_name_frame`: at `QN` it is refused at every opening.
  * `no_check_guard_at_quotient`: at `QX`, for **every** list of checks added to the heat rule and every fresh
    opening, heating the parallel composition `A | B` of two atoms has two solutions of its result reading the
    first made row as `A` and as `B`. Checks only accept or refuse a firing; they do not constrain its
    solutions. So a guard by checks either refuses heat on a genuine parallel composition or reads it
    ambiguously. `name_heat_determinate`: at `QN` the same heating is admitted and reads `A` and `B`.
* **One location is needed** (`two_locations_no_counterpart`): the manuscript's COMM redex with the sender at
  the root and the receiver at a child: the COMM of the finite program is admitted at the state without
  locations, and its root firing is refused at every opening.
* **No opens** (`open_fires_at_one_location`, `openRoot_not_root`): `openRoot` is admitted at a state whose
  only row is a reflection at the root, and it is no root rule: without excluding it, reflection fails.
* **Locations are values** (`unknown_locations_merge`): with location unknowns, the step at a child takes a
  row at `l1` and a row at `l2`, and every solution of its result identifies `l1` and `l2`.
* **Close takes the token** (`close_as_designed_refused`): a close that takes the last row `C @ L` and asks
  that no row be at `L` is refused at every fresh opening, because the check sees the taken row. The close of
  the located program asks the same absence while taking the token: it is admitted once the child is cooled,
  reading `for(@0 <- @0) 0 @ Root` at every solution of its result (`close_root_fires`, close-empty), and
  refused while a row is left at the child (`close_root_waits`). These are hand-made states, not reached
  runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocated.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect demoChan)
open MeTTaOperationsComm (psubst PSubst pvars patternAction psubst_of_pvars_nil commSelection)
open MeTTaCalculus.Corrected (psubstList_eq_map)
open FiniteProgram (commRule heatRule program commRule_mem heatRule_mem leftPart rightPart firstPattern
  secondPattern channelUnknown firstBody secondBody IsPar not_par_pFor)
open FiniteProgram.Controls (rows rename)
open Comm (Tm X E renameBy ruleVars)
open Comm.Controls (zeroTerm y sender receiver start)
open OneFrame (embed)
open ReflQuotient (BagLaws bagAction QX QE quotientFiring fresh_quotient bagLaws_par_comm commAtQ)
open ReflQuotient.Controls (heatNames heatAt rowsInput startOne onAB heat_admitted_at_quotient example_comm_bag)
open ReflNames (NameLaws nameAction QN QNE nameLaws_of_eq fresh_name)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)

/-! ## Heating needs the name frame -/

/-- **At `QX` the root heat takes a row that is no parallel composition.** -/
theorem root_heat_fires_on_input_at_quotient :
    (RuleSyntax.step QX ℕ QE located).Admits (s := rootState rowsInput startOne)
      (rootFiring (quotientFiring (heatAt (renameBy heatNames)))) ∧ ¬ IsPar onAB :=
  ⟨((conservative_at_root_QX rowsInput startOne).1 _).1.mpr heat_admitted_at_quotient, not_par_pFor _ _ _⟩

/-- **At `QN` the same root heat is refused at every opening.** -/
theorem root_heat_refused_at_name_frame (ρ : PSubst) :
    ¬ (RuleSyntax.step QN ℕ QNE located).Admits (s := rootState rowsInput startOne) (rootFiring (heatN ρ 0 2 3)) := by
  rw [((conservative_at_root_QN rowsInput startOne).1 _).1]
  refine heat_refused rowsInput startOne 0 2 3 (fun σ _ pair => ?_) ρ
  have ground : psubst σ (rowsInput 0) = onAB := psubst_of_pvars_nil σ _ (by decide +kernel)
  rw [ground] at pair
  exact not_par_pFor _ _ _ pair

/-- Heating with a guard: the heat rule with any list of checks. -/
def guardedHeat (checks : List (Check Pattern)) : Rule Tm :=
  ⟨PUnit.unit, ⟨[par leftPart rightPart], [], [], checks, [leftPart, rightPart]⟩, []⟩

/-- Its program. -/
def guardedProgram (checks : List (Check Pattern)) : Program Tm := {guardedHeat checks}

/-- The guarded heating at the syntactic frame: take `0`, make `1` and `2`. -/
def guardedAt (checks : List (Check Pattern)) (ρ : PSubst) : Firing ℕ E (guardedProgram checks) PUnit.unit :=
  ⟨guardedHeat checks, rfl, PUnit.unit, ρ, ⟨[0], [], [1, 2]⟩, []⟩

/-- The parallel composition of two atoms at `0`. -/
def rowsPair : ℕ → Pattern
  | 0 => par atomA atomB
  | _ => pZero

/-- No knowledge; identity `0` present. -/
def startPair : Configuration Pattern ℕ := ⟨[], {0}⟩

/-- `A` read as the atom `A`, `B` as `B`. -/
def splitAB : PSubst := fun v => if v = "A" then some atomA else if v = "B" then some atomB else none

/-- The other order. -/
def splitBA : PSubst := fun v => if v = "A" then some atomB else if v = "B" then some atomA else none

theorem pair_facts : IsPar (rowsPair 0) ∧ ¬ BagLaws atomA atomB ∧ BagLaws (par atomB atomA) (par atomA atomB) :=
  ⟨⟨atomA, atomB, rfl⟩, by decide +kernel, bagLaws_par_comm _ _⟩

theorem split_facts :
    BagLaws (psubst splitAB (par leftPart rightPart)) (par atomA atomB) ∧
      BagLaws (psubst splitBA (par leftPart rightPart)) (par atomA atomB) ∧
      BagLaws (psubst splitAB leftPart) atomA ∧ BagLaws (psubst splitBA leftPart) atomB := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **A fresh opening of the guarded heating exists**, for every list of checks. -/
theorem guarded_fresh_exists (checks : List (Check Pattern)) :
    ∃ ρ : PSubst, (quotientFiring (guardedAt checks ρ)).Fresh QX (embed rowsPair startPair) := by
  obtain ⟨g, injective, avoids⟩ :=
    Comm.exists_apart_renaming (embed rowsPair startPair) (ruleVars (guardedHeat checks))
  exact ⟨renameBy g, fresh_quotient (Comm.fresh_of_renaming (embed rowsPair startPair)
    (guardedAt checks (renameBy g)) g rfl injective avoids)⟩

/-- **No guard by checks makes heating determinate at `QX`.** For every list of checks and every fresh
opening, the result of heating `A | B` has a solution reading the first made row as `A` and one reading it
as `B`. -/
theorem no_check_guard_at_quotient (checks : List (Check Pattern)) (ρ : PSubst)
    (fresh : (quotientFiring (guardedAt checks ρ)).Fresh QX (embed rowsPair startPair)) :
    ∃ σ₁ σ₂ : PSubst,
      bagAction.Models σ₁ ((quotientFiring (guardedAt checks ρ)).result QX (embed rowsPair startPair)).knowledge ∧
      bagAction.Models σ₂ ((quotientFiring (guardedAt checks ρ)).result QX (embed rowsPair startPair)).knowledge ∧
      BagLaws (psubst σ₁ (((quotientFiring (guardedAt checks ρ)).result QX (embed rowsPair startPair)).label 1))
        atomA ∧
      BagLaws (psubst σ₂ (((quotientFiring (guardedAt checks ρ)).result QX (embed rowsPair startPair)).label 1))
        atomB := by
  have info : ((quotientFiring (guardedAt checks ρ)).result QX (embed rowsPair startPair)).knowledge =
      ([(psubst ρ (par leftPart rightPart), par atomA atomB)] : EquationStore Pattern) := by
    show (quotientFiring (guardedAt checks ρ)).information QX (embed rowsPair startPair) = _
    rw [OneFrame.information_eq]
    rfl
  have label₁ : ((quotientFiring (guardedAt checks ρ)).result QX (embed rowsPair startPair)).label 1 =
      psubst ρ leftPart := rfl
  have takeTerm : par leftPart rightPart ∈ (guardedHeat checks).terms := by simp [Rule.terms, guardedHeat]
  have leftTerm : leftPart ∈ (guardedHeat checks).terms := by simp [Rule.terms, guardedHeat]
  obtain ⟨u₁, -, onRule₁⟩ := fresh PUnit.unit (fun _ => none) splitAB
  obtain ⟨u₂, -, onRule₂⟩ := fresh PUnit.unit (fun _ => none) splitBA
  obtain ⟨splitAB_pair, splitBA_pair, splitAB_left, splitBA_left⟩ := split_facts
  have pattern₁ : BagLaws (psubst u₁ (psubst ρ (par leftPart rightPart))) (par atomA atomB) :=
    (show BagLaws (psubst u₁ (psubst ρ (par leftPart rightPart))) (psubst splitAB (par leftPart rightPart)) from
      onRule₁ _ takeTerm).trans splitAB_pair
  have pattern₂ : BagLaws (psubst u₂ (psubst ρ (par leftPart rightPart))) (par atomA atomB) :=
    (show BagLaws (psubst u₂ (psubst ρ (par leftPart rightPart))) (psubst splitBA (par leftPart rightPart)) from
      onRule₂ _ takeTerm).trans splitBA_pair
  have solves : ∀ u : PSubst, BagLaws (psubst u (psubst ρ (par leftPart rightPart))) (par atomA atomB) →
      bagAction.Models u ((quotientFiring (guardedAt checks ρ)).result QX (embed rowsPair startPair)).knowledge := by
    intro u pattern
    rw [info]
    intro e member
    rw [List.mem_singleton] at member
    subst member
    show BagLaws (psubst u (psubst ρ (par leftPart rightPart))) (psubst u (par atomA atomB))
    rw [psubst_of_pvars_nil u (par atomA atomB) (by decide +kernel)]
    exact pattern
  refine ⟨u₁, u₂, solves u₁ pattern₁, solves u₂ pattern₂, ?_, ?_⟩
  · rw [label₁]
    exact (show BagLaws (psubst u₁ (psubst ρ leftPart)) (psubst splitAB leftPart) from
      onRule₁ _ leftTerm).trans splitAB_left
  · rw [label₁]
    exact (show BagLaws (psubst u₂ (psubst ρ leftPart)) (psubst splitBA leftPart) from
      onRule₂ _ leftTerm).trans splitBA_left

/-- The heating of the finite program at the syntactic frame: take `0`, make `1` and `2`. -/
def heatX (ρ : PSubst) : Firing ℕ E program PUnit.unit :=
  ⟨heatRule, heatRule_mem, PUnit.unit, ρ, ⟨[0], [], [1, 2]⟩, []⟩

/-- **At `QN` heating `A | B` is admitted and reads determinately**: at a fresh opening it is admitted, and
every solution of its result reads the made rows as `A` and `B`. -/
theorem name_heat_determinate :
    ∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE program).Admits (s := embed rowsPair startPair) (heatN ρ 0 1 2) ∧
      ∀ σ : PSubst, nameAction.Models σ ((heatN ρ 0 1 2).result QN (embed rowsPair startPair)).knowledge →
        NameLaws (psubst σ (((heatN ρ 0 1 2).result QN (embed rowsPair startPair)).label 1)) atomA ∧
          NameLaws (psubst σ (((heatN ρ 0 1 2).result QN (embed rowsPair startPair)).label 2)) atomB := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed rowsPair startPair) (ruleVars heatRule)
  have fresh : (heatN (renameBy g) 0 1 2).Fresh QN (embed rowsPair startPair) :=
    fresh_name (Comm.fresh_of_renaming (embed rowsPair startPair) (heatX (renameBy g)) g rfl injective avoids)
  refine ⟨renameBy g, heat_admitted rowsPair startPair 0 1 2 (by decide) (by decide) (by decide) (by decide)
    (σ₀ := fun _ => none) (fun _ member => absurd member List.not_mem_nil) (a := atomA) (b := atomB)
    (nameLaws_of_eq (psubst_of_pvars_nil _ _ (by decide +kernel))) fresh, fun σ solved => ?_⟩
  have reads : ∀ σ : PSubst, nameAction.Models σ startPair.equations →
      NameLaws (psubst σ (rowsPair 0)) (psubst σ (par atomA atomB)) := fun _ _ => ReflNames.NameLaws.refl _
  obtain ⟨left, right⟩ := heat_reads_determinately rowsPair startPair (renameBy g) 0 (by decide : (1 : ℕ) ≠ 2)
    atomA atomB reads solved
  rw [psubst_of_pvars_nil σ atomA (by decide +kernel)] at left
  rw [psubst_of_pvars_nil σ atomB (by decide +kernel)] at right
  exact ⟨left, right⟩

/-! ## One location is needed -/

/-- A child location without variables. -/
def childOne : Pattern := childLoc rootLoc demoChan pZero

theorem pvars_childOne : pvars childOne = [] := by decide +kernel

/-- The sender at the root, the receiver at the child. -/
def rowsTwo : ℕ → Pattern := fun o => if o = 0 then atLoc (rows 0) rootLoc else atLoc (rows o) childOne

/-- **Rows at two locations are never taken by the root COMM**, at any frame for locations and any opening. -/
theorem two_locations_refused {A : SubstitutionAction Pattern PSubst} (hA : LocatedFrame A) (ρ : PSubst) :
    ¬ (RuleSyntax.step (OneFrame.frames A) ℕ (OneFrame.ext A) located).Admits (s := embed rowsTwo start)
      (rootFiring (A := A) (a := PUnit.unit) ⟨commRule, commRule_mem, PUnit.unit, ρ, commSelection 0 1 2 3, []⟩) := by
  intro admitted
  obtain ⟨_, _, _, ⟨_, σ, solved⟩, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have zipped : (A.apply ρ (atLoc (pFor secondPattern channelUnknown secondBody) rootLoc), (1 : ℕ)) ∈
      ((rootFiring (A := A) (a := PUnit.unit)
          ⟨commRule, commRule_mem, PUnit.unit, ρ, commSelection 0 1 2 3, []⟩).opened (OneFrame.frames A)).take.zip
        [0, 1] := by
    show _ ∈ (([pFor firstPattern channelUnknown firstBody, pFor secondPattern channelUnknown secondBody].map
      fun t => atLoc t rootLoc).map (A.apply ρ)).zip [0, 1]
    simp
  have equal := Firing.take_solved _ solved zipped
  rw [OneFrame.row_eq] at equal
  change A.E (A.apply σ (A.apply ρ (atLoc (pFor secondPattern channelUnknown secondBody) rootLoc)))
    (A.apply σ (atLoc (rows 1) childOne)) at equal
  rw [act_atLoc hA ρ _ pvars_rootLoc, act_atLoc hA σ _ pvars_rootLoc, act_atLoc hA σ _ pvars_childOne] at equal
  have locations := ((hA.atLoc_iff _ _ _ _).mp equal).2
  exact absurd (hA.heads _ _ _ _ locations) (by decide)

/-- **One location is needed.** The manuscript's COMM redex: the COMM of the finite program is admitted at
the state without locations, and at the state with the sender at the root and the receiver at a child its
root firing is refused at every opening: the location map is no arrow there. -/
theorem two_locations_no_counterpart :
    (RuleSyntax.step QX ℕ QE program).Admits (s := embed rows start) (commAtQ (renameBy rename) 0 1 2 3) ∧
      ∀ ρ : PSubst, ¬ (RuleSyntax.step QX ℕ QE located).Admits (s := embed rowsTwo start)
        (rootFiring (commAtQ ρ 0 1 2 3)) :=
  ⟨example_comm_bag.1, fun ρ => two_locations_refused locatedFrame_bag ρ⟩

/-! ## No opens -/

/-- A reflection `@0?(0)` at the root, without locations. -/
def reflLabels : ℕ → Pattern
  | 0 => pReflect demoChan pZero
  | _ => pZero

/-- No knowledge; identity `0` present. -/
def startRefl : Configuration Pattern ℕ := ⟨[], {0}⟩

/-- `openRoot` at the syntactic frame: read `0`, make `1` and `2`. -/
def openAtX (ρ : PSubst) : Firing ℕ E located PUnit.unit :=
  ⟨openRoot, openRoot_mem, PUnit.unit, ρ, ⟨[], [0], [1, 2]⟩, []⟩

/-- `X` read as `@0`, `P` as `0`. -/
def reflectionParts : PSubst := fun v => if v = "X" then some demoChan else if v = "P" then some pZero else none

/-- The reflection row read by `openRoot`, through `reflectionParts`. -/
theorem open_agrees : ∀ q ∈ openRoot.body.read.zip [0],
    BagLaws (psubst reflectionParts q.1) (psubst (fun _ => none) (atLabel rootLoc reflLabels q.2)) := by
  decide +kernel

/-- **`openRoot` fires at a one-location state**: at every fresh opening it is admitted at `QX` where the only
row is the reflection `@0?(0) @ Root`. -/
theorem open_fires_at_one_location (ρ : PSubst)
    (fresh : (quotientFiring (openAtX ρ)).Fresh QX (rootState reflLabels startRefl)) :
    (RuleSyntax.step QX ℕ QE located).Admits (s := rootState reflLabels startRefl) (quotientFiring (openAtX ρ)) := by
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QX) (s := rootState reflLabels startRefl)
    (quotientFiring (openAtX ρ)) fresh (b := PUnit.unit) (fun _ => none) reflectionParts
    (fun _ member => absurd member List.not_mem_nil)
    (fun _ member => absurd member List.not_mem_nil)
    (fun _ member => absurd member List.not_mem_nil)
    (fun o member => by
      have zero : o = 0 := List.mem_singleton.mp member
      subst zero
      decide)
    (fun _ member => absurd member List.not_mem_nil)
    (fun q member => open_agrees q member)
  have notAt : ∀ (σ : PSubst) (c : String) (args : List Pattern), c ≠ "At" →
      ¬ BagLaws (psubst σ (.apply c args)) (psubst σ (atLoc (pReflect demoChan pZero) rootLoc)) := by
    intro σ c args other same
    simp only [atLoc, psubst_apply] at same
    exact other (locatedFrame_bag.heads _ _ _ _ same)
  refine (RuleSyntax.admits_iff _).mpr ⟨fresh,
    ⟨List.nodup_nil, (show ([1, 2] : List ℕ).Nodup by decide), rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, ?_, fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp [quotientFiring, openAtX, Selection.commit] at member
  · intro o member
    simp only [quotientFiring, openAtX, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    decide
  · simp [quotientFiring, openAtX, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [quotientFiring, openAtX, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> decide
  · intro c member b σ _
    simp only [Firing.opened, RuleInstance.map, quotientFiring, openAtX, openRoot, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    have onlyZero : ∀ o ∈ (rootState reflLabels startRefl).present, o = 0 := fun o present => by
      simpa [rootState, embed, atConf, startRefl] using present
    rcases member with rfl | rfl | rfl
    · intro o present same
      obtain rfl := onlyZero o present
      change BagLaws (psubst σ (psubst ρ (pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc)))
        (psubst σ (atLoc (pReflect demoChan pZero) rootLoc)) at same
      rw [show psubst ρ (pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc) =
        .apply "Pending" ([childLoc rootLoc channelUnknown reflP, rootLoc].map (psubst ρ)) from
          psubst_apply ρ _ _] at same
      exact notAt σ "Pending" _ (by decide) same
    · intro o present same
      obtain rfl := onlyZero o present
      change BagLaws (psubst σ (psubst ρ (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc anyZ)))
        (psubst σ (atLoc (pReflect demoChan pZero) rootLoc)) at same
      rw [show psubst ρ (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc anyZ) =
        .apply "Done" ([childLoc rootLoc channelUnknown reflP, rootLoc, anyZ].map (psubst ρ)) from
          psubst_apply ρ _ _] at same
      exact notAt σ "Done" _ (by decide) same
    · intro o present same
      obtain rfl := onlyZero o present
      change BagLaws (psubst σ (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP))))
        (psubst σ (atLoc (pReflect demoChan pZero) rootLoc)) at same
      simp only [atLoc, childLoc, psubst_apply, List.map_cons, List.map_nil] at same
      have parts := (locatedFrame_bag.atLoc_iff _ _ _ _).mp same
      exact absurd (locatedFrame_bag.heads _ _ _ _ parts.2) (by decide)

/-- A fresh opening of `openRoot` exists at that state. -/
theorem open_fresh_exists :
    ∃ ρ : PSubst, (quotientFiring (openAtX ρ)).Fresh QX (rootState reflLabels startRefl) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (rootState reflLabels startRefl) (ruleVars openRoot)
  exact ⟨renameBy g, fresh_quotient (Comm.fresh_of_renaming (rootState reflLabels startRefl) (openAtX (renameBy g))
    g rfl injective avoids)⟩

/-! ## Locations are values -/

/-- Two location unknowns. -/
def locU₁ : Pattern := .fvar "l1"
def locU₂ : Pattern := .fvar "l2"

/-- The sender at `l1`, the receiver at `l2`, and the token of `l1`. -/
def rowsMerge : ℕ → Pattern := fun o =>
  if o = 0 then atLoc sender locU₁ else if o = 1 then atLoc receiver locU₂ else pendingTok locU₁ rootLoc

/-- No knowledge; identities `0`, `1`, `2` present. -/
def startMerge : Configuration Pattern ℕ := ⟨[], {0, 1, 2}⟩

/-- The step at a child: take `0`, `1`, `2`; make `3`, `4`, `5`. -/
def commChildAt (ρ : PSubst) : Firing ℕ E located PUnit.unit :=
  ⟨commChild, commChild_mem, PUnit.unit, ρ, ⟨[0, 1, 2], [], [3, 4, 5]⟩, []⟩

/-- The state's solution that identifies `l2` with `l1`, and reads `y` as `(0)`. -/
def mergeState : PSubst := fun v => if v = "l2" then some locU₁ else if v = "y" then some zeroTerm else none

/-- The rule's instance at the merged location. -/
def mergeRule : PSubst := fun v =>
  if v = "L" then some locU₁ else if v = "M" then some rootLoc else if v = "T1" then some zeroTerm
  else if v = "T2" then some zeroTerm else if v = "X" then some demoChan else if v = "K1" then some pZero
  else if v = "K2" then some zeroTerm else none

theorem merge_agrees : ∀ q ∈ commChild.body.take.zip [0, 1, 2],
    psubst mergeRule q.1 = psubst mergeState (rowsMerge q.2) := by
  decide +kernel

theorem merge_told : ∀ e ∈ commChild.body.tell, psubst mergeRule e.1 = psubst mergeRule e.2 := by
  decide +kernel

/-- The location of a row read through a solution. -/
theorem loc_of_psubst_atLoc {σ : PSubst} {a b l l' : Pattern}
    (same : psubst σ (atLoc a l) = psubst σ (atLoc b l')) : psubst σ l = psubst σ l' := by
  simp only [atLoc, psubst_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq, true_and,
    and_true] at same
  exact same.2

/-- **Location unknowns merge.** With locations that are unknowns of the knowledge, the step at a child is
admitted on a row at `l1` and a row at `l2`, at every fresh opening, and every solution of its result
identifies the two locations. -/
theorem unknown_locations_merge (ρ : PSubst) (fresh : (commChildAt ρ).Fresh X (embed rowsMerge startMerge)) :
    (RuleSyntax.step X ℕ E located).Admits (s := embed rowsMerge startMerge) (commChildAt ρ) ∧
      locU₁ ≠ locU₂ ∧
      ∀ σ : PSubst, patternAction.Models σ ((commChildAt ρ).result X (embed rowsMerge startMerge)).knowledge →
        psubst σ locU₁ = psubst σ locU₂ := by
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := X) (s := embed rowsMerge startMerge)
    (commChildAt ρ) fresh (b := PUnit.unit) mergeState mergeRule
    (fun _ member => absurd member List.not_mem_nil)
    (fun e member => merge_told e member)
    (fun o member => by
      have inside : o ∈ ([0, 1, 2] : List ℕ) := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide)
    (fun _ member => absurd member List.not_mem_nil)
    (fun q member => merge_agrees q member)
    (fun _ member => absurd member List.not_mem_nil)
  refine ⟨(RuleSyntax.admits_iff _).mpr ⟨fresh,
    ⟨(show ([0, 1, 2] : List ℕ).Nodup by decide), (show ([3, 4, 5] : List ℕ).Nodup by decide), rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩, by decide, fun σ known => ?_⟩
  · intro o member
    simp only [commChildAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro o member
    simp [commChildAt, Selection.commit] at member
  · simp [commChildAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [commChildAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> decide
  · have info : ((commChildAt ρ).result X (embed rowsMerge startMerge)).knowledge =
        (commChildAt ρ).information X (embed rowsMerge startMerge) := rfl
    rw [info, OneFrame.information_eq] at known
    have first : psubst σ (psubst ρ (atLoc (pFor firstPattern channelUnknown firstBody) locL)) =
        psubst σ (atLoc sender locU₁) :=
      known (psubst ρ (atLoc (pFor firstPattern channelUnknown firstBody) locL), atLoc sender locU₁)
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)))
    have second : psubst σ (psubst ρ (atLoc (pFor secondPattern channelUnknown secondBody) locL)) =
        psubst σ (atLoc receiver locU₂) :=
      known (psubst ρ (atLoc (pFor secondPattern channelUnknown secondBody) locL), atLoc receiver locU₂)
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_of_mem _ List.mem_cons_self))))
    have openedFirst : psubst ρ (atLoc (pFor firstPattern channelUnknown firstBody) locL) =
        atLoc (psubst ρ (pFor firstPattern channelUnknown firstBody)) (psubst ρ locL) := by
      simp only [atLoc, psubst_apply, List.map_cons, List.map_nil]
    have openedSecond : psubst ρ (atLoc (pFor secondPattern channelUnknown secondBody) locL) =
        atLoc (psubst ρ (pFor secondPattern channelUnknown secondBody)) (psubst ρ locL) := by
      simp only [atLoc, psubst_apply, List.map_cons, List.map_nil]
    rw [openedFirst] at first
    rw [openedSecond] at second
    exact (loc_of_psubst_atLoc first).symm.trans (loc_of_psubst_atLoc second)

/-- A fresh opening of the merge control exists. -/
theorem merge_fresh_exists : ∃ ρ : PSubst, (commChildAt ρ).Fresh X (embed rowsMerge startMerge) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed rowsMerge startMerge) (ruleVars commChild)
  exact ⟨renameBy g, Comm.fresh_of_renaming (embed rowsMerge startMerge) (commChildAt (renameBy g)) g rfl
    injective avoids⟩

/-! ## Close takes the token -/

/-- The token of the design's stepped child. -/
def steppedTok (l m : Pattern) : Pattern := .apply "Stepped" [l, m]

/-- **The design's close**: take `x?(P) @ M`, `Stepped(L, M)` and `C @ L`; ask that no row be at `L`; make
`for(@C <- x) 0 @ M`. -/
def closeAsDesigned : Rule Tm :=
  ⟨PUnit.unit, ⟨[atLoc (pReflect channelUnknown reflP) locM, steppedTok locL locM, atLoc accC locL], [], [],
    [.predicate .none (atLoc anyY locL)], [atLoc (pFor (tProc accC) channelUnknown pZero) locM]⟩, []⟩

/-- Its program. -/
def designProgram : Program Tm := {closeAsDesigned}

/-- A reflection at the root, its stepped child, and the child's last row. -/
def rowsDesign : ℕ → Pattern := fun o =>
  if o = 0 then atLoc (pReflect demoChan pZero) rootLoc else if o = 1 then steppedTok childOne rootLoc
  else atLoc pZero childOne

/-- No knowledge; identities `0`, `1`, `2` present. -/
def startDesign : Configuration Pattern ℕ := ⟨[], {0, 1, 2}⟩

/-- The design's close: take `0`, `1`, `2`; make `3`. -/
def closeDesignAt (ρ : PSubst) : Firing ℕ E designProgram PUnit.unit :=
  ⟨closeAsDesigned, rfl, PUnit.unit, ρ, ⟨[0, 1, 2], [], [3]⟩, []⟩

/-- The instance that closes the child, with the check's unknown on the taken row. -/
def designInstance : PSubst := fun v =>
  if v = "M" then some rootLoc else if v = "X" then some demoChan else if v = "P" then some pZero
  else if v = "L" then some childOne else if v = "C" then some pZero else if v = "Y" then some pZero else none

theorem design_agrees : ∀ q ∈ closeAsDesigned.body.take.zip [0, 1, 2],
    psubst designInstance q.1 = psubst (fun _ => none) (rowsDesign q.2) := by
  decide +kernel

theorem design_check : psubst designInstance (atLoc anyY locL) = rowsDesign 2 := by
  decide +kernel

/-- **The design's close is refused at every fresh opening**: some solution of its information reads the
check's `Y @ L` as the taken row `0 @ L`, so the absence does not hold at every solution. -/
theorem close_as_designed_refused (ρ : PSubst) (fresh : (closeDesignAt ρ).Fresh X (embed rowsDesign startDesign)) :
    ¬ (RuleSyntax.step X ℕ E designProgram).Admits (s := embed rowsDesign startDesign) (closeDesignAt ρ) := by
  intro admitted
  obtain ⟨w, solved, -, onRule⟩ := Comm.information_amalgamates_matched (Y := X) (s := embed rowsDesign startDesign)
    (closeDesignAt ρ) fresh (b := PUnit.unit) (fun _ => none) designInstance
    (fun _ member => absurd member List.not_mem_nil)
    (fun _ member => absurd member List.not_mem_nil)
    (fun o member => by
      have inside : o ∈ ([0, 1, 2] : List ℕ) := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide)
    (fun _ member => absurd member List.not_mem_nil)
    (fun q member => design_agrees q member)
    (fun _ member => absurd member List.not_mem_nil)
  have checks := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.2.1
  have asked := checks (.predicate .none (psubst ρ (atLoc anyY locL))) List.mem_cons_self PUnit.unit w solved
  have term : atLoc anyY locL ∈ closeAsDesigned.terms := by simp [Rule.terms, closeAsDesigned, checkTerms]
  have reads : psubst w (psubst ρ (atLoc anyY locL)) = rowsDesign 2 :=
    (show psubst w (psubst ρ (atLoc anyY locL)) = psubst designInstance (atLoc anyY locL) from
      onRule _ term).trans design_check
  apply asked 2 (by decide)
  rw [OneFrame.row_eq]
  show psubst w (psubst ρ (atLoc anyY locL)) = psubst w (rowsDesign 2)
  rw [reads, psubst_of_pvars_nil w _ (by decide +kernel)]

/-! ## The close of the located program: guarded by absence, through the token -/

/-- A reflection at the root, the token of its stepped child with the cooled bag `0`, and a row at the child
(present only in `leftConf`). -/
def rowsClose : ℕ → Pattern := fun o =>
  if o = 0 then atLoc (pReflect demoChan pZero) rootLoc else if o = 1 then doneTok childOne rootLoc pZero
  else atLoc pZero childOne

/-- The child cooled: identities `0` and `1` present. -/
def cooledConf : Configuration Pattern ℕ := ⟨[], {0, 1}⟩

/-- A row left at the child: identities `0`, `1` and `2` present. -/
def leftConf : Configuration Pattern ℕ := ⟨[], {0, 1, 2}⟩

/-- The close at the root: take `0` and `1`, make `3`. -/
def closeRootAt (ρ : PSubst) : Firing ℕ E located PUnit.unit :=
  ⟨closeRoot, closeRoot_mem, PUnit.unit, ρ, ⟨[0, 1], [], [3]⟩, []⟩

/-- The instance of the close, with the check's unknown on the leftover row. -/
def closeInstance : PSubst := fun v =>
  if v = "X" then some demoChan else if v = "P" then some pZero else if v = "C" then some pZero
  else if v = "Y" then some pZero else none

theorem close_agrees : ∀ q ∈ closeRoot.body.take.zip [0, 1],
    psubst closeInstance q.1 = psubst (fun _ => none) (rowsClose q.2) := by
  decide +kernel

theorem close_check_leftover :
    psubst closeInstance (atLoc anyY (childLoc rootLoc channelUnknown reflP)) = rowsClose 2 := by
  decide +kernel

/-- **The close fires once the child is cooled** (close-empty: the cooled bag is `0`): at every fresh opening it
is admitted, and every solution of its result reads the made row as `for(@0 <- @0) 0 @ Root`. -/
theorem close_root_fires (ρ : PSubst) (fresh : (closeRootAt ρ).Fresh X (embed rowsClose cooledConf)) :
    (RuleSyntax.step X ℕ E located).Admits (s := embed rowsClose cooledConf) (closeRootAt ρ) ∧
      ∀ σ : PSubst, patternAction.Models σ ((closeRootAt ρ).result X (embed rowsClose cooledConf)).knowledge →
        psubst σ (((closeRootAt ρ).result X (embed rowsClose cooledConf)).label 3) =
          atLoc (pFor (tProc pZero) demoChan pZero) rootLoc := by
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := X) (s := embed rowsClose cooledConf)
    (closeRootAt ρ) fresh (b := PUnit.unit) (fun _ => none) closeInstance
    (fun _ member => absurd member List.not_mem_nil)
    (fun _ member => absurd member List.not_mem_nil)
    (fun o member => by
      have inside : o ∈ ([0, 1] : List ℕ) := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> decide)
    (fun _ member => absurd member List.not_mem_nil)
    (fun q member => close_agrees q member)
    (fun _ member => absurd member List.not_mem_nil)
  refine ⟨(RuleSyntax.admits_iff _).mpr ⟨fresh,
    ⟨(show ([0, 1] : List ℕ).Nodup by decide), (show ([3] : List ℕ).Nodup by decide), rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, ?_, fun _ member => (List.not_mem_nil member).elim⟩, fun σ known => ?_⟩
  · intro o member
    simp only [closeRootAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> decide
  · intro o member
    simp [closeRootAt, Selection.commit] at member
  · simp [closeRootAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [closeRootAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    decide
  · intro c member b σ _
    simp only [Firing.opened, RuleInstance.map, closeRootAt, closeRoot, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    intro o present same
    have zeroOrOne : o = 0 ∨ o = 1 := by simpa [embed, cooledConf] using present
    rw [OneFrame.row_eq] at same
    change psubst σ (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP))) = psubst σ (rowsClose o) at same
    rcases zeroOrOne with rfl | rfl
    · simp [rowsClose, atLoc, childLoc, rootLoc, psubst_apply] at same
    · simp [rowsClose, atLoc, doneTok, psubst_apply] at same
  · have info : ((closeRootAt ρ).result X (embed rowsClose cooledConf)).knowledge =
        (closeRootAt ρ).information X (embed rowsClose cooledConf) := rfl
    rw [info, OneFrame.information_eq] at known
    have token : psubst σ (psubst ρ (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC)) =
        psubst σ (rowsClose 1) :=
      known (psubst ρ (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC), rowsClose 1)
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_of_mem _ List.mem_cons_self))))
    have made : ((closeRootAt ρ).result X (embed rowsClose cooledConf)).label 3 =
        psubst ρ (atLoc (pFor (tProc accC) channelUnknown pZero) rootLoc) := rfl
    have groundAll : ∀ u : PSubst, psubst u rootLoc = rootLoc ∧ psubst u pZero = pZero :=
      fun u => ⟨psubst_of_pvars_nil u _ rfl, psubst_of_pvars_nil u _ rfl⟩
    have tokenShape : psubst σ (psubst ρ (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC)) =
        doneTok (childLoc rootLoc (psubst σ (psubst ρ channelUnknown)) (psubst σ (psubst ρ reflP))) rootLoc
          (psubst σ (psubst ρ accC)) := by
      simp only [doneTok, childLoc, psubst_apply, List.map_cons, List.map_nil, (groundAll ρ).1, (groundAll σ).1]
    have rowOne : psubst σ (rowsClose 1) = doneTok childOne rootLoc pZero :=
      psubst_of_pvars_nil σ _ (by decide +kernel)
    rw [tokenShape, rowOne] at token
    have args := (Pattern.apply.inj token).2
    have childEq := (List.cons.inj args).1
    have accEq := (List.cons.inj (List.cons.inj (List.cons.inj args).2).2).1
    have chanEq := (List.cons.inj (List.cons.inj (Pattern.apply.inj childEq).2).2).1
    have lhs : psubst σ (psubst ρ (atLoc (pFor (tProc accC) channelUnknown pZero) rootLoc)) =
        atLoc (pFor (tProc (psubst σ (psubst ρ accC))) (psubst σ (psubst ρ channelUnknown)) pZero) rootLoc := by
      simp only [atLoc, pFor, tProc, psubst_apply, List.map_cons, List.map_nil, (groundAll ρ).1, (groundAll σ).1,
        (groundAll ρ).2, (groundAll σ).2]
    rw [made, lhs, accEq, chanEq]

/-- **The close waits for cooling**: with a row left at the child it is refused at every fresh opening; some
solution reads the check's `Y @ Child(Root, x, P)` as that row. -/
theorem close_root_waits (ρ : PSubst) (fresh : (closeRootAt ρ).Fresh X (embed rowsClose leftConf)) :
    ¬ (RuleSyntax.step X ℕ E located).Admits (s := embed rowsClose leftConf) (closeRootAt ρ) := by
  intro admitted
  obtain ⟨w, solved, -, onRule⟩ := Comm.information_amalgamates_matched (Y := X) (s := embed rowsClose leftConf)
    (closeRootAt ρ) fresh (b := PUnit.unit) (fun _ => none) closeInstance
    (fun _ member => absurd member List.not_mem_nil)
    (fun _ member => absurd member List.not_mem_nil)
    (fun o member => by
      have inside : o ∈ ([0, 1] : List ℕ) := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> decide)
    (fun _ member => absurd member List.not_mem_nil)
    (fun q member => close_agrees q member)
    (fun _ member => absurd member List.not_mem_nil)
  have checks := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.2.1
  have asked := checks (.predicate .none (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP)))) List.mem_cons_self
    PUnit.unit w solved
  have term : atLoc anyY (childLoc rootLoc channelUnknown reflP) ∈ closeRoot.terms := by
    simp [Rule.terms, closeRoot, checkTerms]
  have reads : psubst w (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP))) = rowsClose 2 :=
    (show psubst w (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP))) =
        psubst closeInstance (atLoc anyY (childLoc rootLoc channelUnknown reflP)) from onRule _ term).trans
      close_check_leftover
  apply asked 2 (by decide)
  rw [OneFrame.row_eq]
  show psubst w (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP))) = psubst w (rowsClose 2)
  rw [reads, psubst_of_pvars_nil w _ (by decide +kernel)]

/-- Fresh openings of the close exist at both states. -/
theorem close_fresh_exists :
    (∃ ρ : PSubst, (closeRootAt ρ).Fresh X (embed rowsClose cooledConf)) ∧
      ∃ ρ : PSubst, (closeRootAt ρ).Fresh X (embed rowsClose leftConf) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed rowsClose cooledConf) (ruleVars closeRoot)
  obtain ⟨g', injective', avoids'⟩ := Comm.exists_apart_renaming (embed rowsClose leftConf) (ruleVars closeRoot)
  exact ⟨⟨renameBy g, Comm.fresh_of_renaming _ (closeRootAt (renameBy g)) g rfl injective avoids⟩,
    ⟨renameBy g', Comm.fresh_of_renaming _ (closeRootAt (renameBy g')) g' rfl injective' avoids'⟩⟩

/-- A fresh opening of the design's close exists at that state. -/
theorem close_design_fresh_exists : ∃ ρ : PSubst, (closeDesignAt ρ).Fresh X (embed rowsDesign startDesign) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed rowsDesign startDesign) (ruleVars closeAsDesigned)
  exact ⟨renameBy g, Comm.fresh_of_renaming (embed rowsDesign startDesign) (closeDesignAt (renameBy g)) g rfl
    injective avoids⟩

#print axioms root_heat_fires_on_input_at_quotient
#print axioms root_heat_refused_at_name_frame
#print axioms pair_facts
#print axioms split_facts
#print axioms guarded_fresh_exists
#print axioms no_check_guard_at_quotient
#print axioms name_heat_determinate
#print axioms two_locations_refused
#print axioms two_locations_no_counterpart
#print axioms open_agrees
#print axioms open_fires_at_one_location
#print axioms openRoot_not_root
#print axioms open_fresh_exists
#print axioms merge_agrees
#print axioms unknown_locations_merge
#print axioms merge_fresh_exists
#print axioms design_agrees
#print axioms close_as_designed_refused
#print axioms close_design_fresh_exists
#print axioms close_agrees
#print axioms close_root_fires
#print axioms close_root_waits
#print axioms close_fresh_exists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocated.Controls
