import Mettapedia.GSLT.Distinction.Constructive.Scale
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mathlib.Tactic.Abel

/-!
# Depth-indexed graded observations over a constructive value scale

A **presented system** (`PresentedSystem`) is a labelled system over a GSLT
(`HennessyMilner.System`) together with readings into a value scale and an
**authored successor enumeration**: for each label and term a list of actual
successors that covers every successor up to the equations.  No finiteness
predicate is turned into a list by choice; the list is data.

* **Formula values** (`val`) of the real-valued Hennessy–Milner logic of
  `BehaviouralMetric` (truth, atoms, `one − f`, `min`, clamped shift, discounted
  diamond), computed from the enumeration.  They respect the equations
  (`val_resp`) and do not depend on which covering enumeration is used
  (`val_dia_eq_of_cover`).
* **The depth bound** (`depthBound`) needs, in addition, finite lists of the
  observation names and labels (`Vocabulary`).  It is computed by the
  Hausdorff recursion of van Breugel and Worrell, truncated at depth `n`.
  - Adequacy at depth `n` (`abs_val_sub_le_depthBound`): every formula of modal
    depth at most `n` changes by at most the bound.
  - Expressivity at depth `n` (`exists_formula_eq_depthBound`): an explicit
    formula of depth at most `n` attains the bound exactly.
  - Hence the bound is a pseudometric (`depthBound_self`, `depthBound_symm`,
    `depthBound_triangle`), monotone in the depth (`depthBound_mono`),
    respects the equations, and is independent of the chosen vocabulary lists
    (`depthBound_vocabulary`).
* **Zero at depth `n`** is agreement on depth-`n` formulas
  (`depthBound_eq_zero_iff`), and with a positive discount the `n`-step
  bisimulation approximant (`depthBound_eq_zero_iff_approx`).
* **Three separate notions.**
  - agreement at every finite depth: `∀ n, depthBound n s t = 0`;
  - a coherent infinite witness: `GradedBisimilar`, which implies the former
    (`depthBound_eq_zero_of_gradedBisimilar`);
  - a limit: the bounds increase, and successive bounds differ by at most the
    iterated discount (`depthBound_add_le`), a convergence modulus exactly when
    the iterated discounts are summable.
  A **stabilization certificate** (`Stabilizes`) closes the gap between the
  first two constructively (`gradedBisimilar_iff_of_stabilizes`).  Without one
  the step is a logical principle; see `Controls` for the LLPO lower bound.

Nothing here uses `Classical.choice`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Constructive

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner

universe uS uAtom uLabel uObs uV

/-! ## Formulas -/

/-- Graded Hennessy–Milner formulas with thresholds in a value scale. -/
inductive ScaledFormula (Obs : Type uObs) (Label : Type uLabel) (V : Type uV) :
    Type (max uObs uLabel uV) where
  | top : ScaledFormula Obs Label V
  | atom (observation : Obs) : ScaledFormula Obs Label V
  | neg (inner : ScaledFormula Obs Label V) : ScaledFormula Obs Label V
  | conj (left right : ScaledFormula Obs Label V) : ScaledFormula Obs Label V
  | shift (threshold : V) (inner : ScaledFormula Obs Label V) : ScaledFormula Obs Label V
  | dia (label : Label) (inner : ScaledFormula Obs Label V) : ScaledFormula Obs Label V

namespace ScaledFormula

variable {Obs : Type uObs} {Label : Type uLabel} {V : Type uV}

/-- Modal depth: the nesting of diamonds. -/
def depth : ScaledFormula Obs Label V → ℕ
  | top => 0
  | atom _ => 0
  | neg inner => depth inner
  | conj left right => max (depth left) (depth right)
  | shift _ inner => depth inner
  | dia _ inner => depth inner + 1

end ScaledFormula

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-! ## Presented systems -/

set_option linter.checkUnivs false in
/-- A **presented system**: labelled dynamics over a GSLT, readings in a value
scale that respect the equations, and an authored successor enumeration whose
entries are actual successors and which covers every successor up to the
equations. -/
structure PresentedSystem (S : GSLT.{uS}) (K : Scale V) where
  /-- The labelled steps. -/
  dynamics : System.{uAtom, uLabel} S
  /-- The observation names. -/
  Obs : Type uObs
  /-- The reading of a term. -/
  value : Obs → S.Term → V
  value_nonneg : ∀ observation term, 0 ≤ value observation term
  value_le_one : ∀ observation term, value observation term ≤ K.one
  value_resp : ∀ observation {left right : S.Term}, S.Equiv left right →
    value observation left = value observation right
  /-- The authored successor enumeration. -/
  successors : dynamics.Label → S.Term → List S.Term
  successors_act : ∀ {label : dynamics.Label} {term target : S.Term},
    target ∈ successors label term → dynamics.act label term target
  successors_cover : ∀ {label : dynamics.Label} {term target : S.Term},
    dynamics.act label term target →
      ∃ representative ∈ successors label term, S.Equiv target representative

/-- Finite lists of every observation name and every label. -/
structure PresentedSystem.Vocabulary {S : GSLT.{uS}} {K : Scale V}
    (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K) where
  observations : List Q.Obs
  observations_complete : ∀ observation, observation ∈ observations
  labels : List Q.dynamics.Label
  labels_complete : ∀ label, label ∈ labels

namespace PresentedSystem

variable {S : GSLT.{uS}} {K : Scale V} (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)

/-- The formulas of a presented system. -/
abbrev Formula : Type (max uObs uLabel uV) := ScaledFormula Q.Obs Q.dynamics.Label V

/-! ## Formula values -/

/-- The value of a formula at a term, computed from the enumeration. -/
def val : Q.Formula → S.Term → V
  | .top, _ => K.one
  | .atom observation, term => Q.value observation term
  | .neg inner, term => K.one - val inner term
  | .conj left right, term => min (val left term) (val right term)
  | .shift threshold inner, term => K.clamp (val inner term - threshold)
  | .dia label inner, term => K.discount (listSup (val inner) (Q.successors label term))

@[simp] theorem val_top (term : S.Term) : Q.val .top term = K.one := rfl

@[simp] theorem val_atom (observation : Q.Obs) (term : S.Term) :
    Q.val (.atom observation) term = Q.value observation term := rfl

@[simp] theorem val_neg (inner : Q.Formula) (term : S.Term) :
    Q.val (.neg inner) term = K.one - Q.val inner term := rfl

@[simp] theorem val_conj (left right : Q.Formula) (term : S.Term) :
    Q.val (.conj left right) term = min (Q.val left term) (Q.val right term) := rfl

@[simp] theorem val_shift (threshold : V) (inner : Q.Formula) (term : S.Term) :
    Q.val (.shift threshold inner) term = K.clamp (Q.val inner term - threshold) := rfl

@[simp] theorem val_dia (label : Q.dynamics.Label) (inner : Q.Formula) (term : S.Term) :
    Q.val (.dia label inner) term =
      K.discount (listSup (Q.val inner) (Q.successors label term)) := rfl

/-- Every formula takes values in `[0, one]`. -/
theorem val_mem : ∀ (formula : Q.Formula) (term : S.Term),
    0 ≤ Q.val formula term ∧ Q.val formula term ≤ K.one
  | .top, _ => ⟨K.zero_le_one, le_rfl⟩
  | .atom observation, term => ⟨Q.value_nonneg observation term, Q.value_le_one observation term⟩
  | .neg inner, term =>
      ⟨sub_nonneg.mpr (val_mem inner term).2, sub_le_self _ (val_mem inner term).1⟩
  | .conj left right, term =>
      ⟨le_min (val_mem left term).1 (val_mem right term).1,
        (min_le_left _ _).trans (val_mem left term).2⟩
  | .shift _ _, _ => ⟨K.clamp_nonneg _, K.clamp_le_one _⟩
  | .dia _ inner, _ =>
      ⟨K.discount_nonneg (listSup_nonneg _ _),
        (K.discount_le (listSup_nonneg _ _)).trans
          (listSup_le _ K.zero_le_one fun target _ => (val_mem inner target).2)⟩

theorem val_nonneg (formula : Q.Formula) (term : S.Term) : 0 ≤ Q.val formula term :=
  (Q.val_mem formula term).1

theorem val_le_one (formula : Q.Formula) (term : S.Term) : Q.val formula term ≤ K.one :=
  (Q.val_mem formula term).2

/-- A list of actual successors of one term has supremum at most that of a
list covering the successors of an equated term, for any function that respects
the equations. -/
theorem listSup_le_of_cover (label : Q.dynamics.Label) {left right : S.Term}
    (first second : List S.Term) (sound : ∀ target ∈ first, Q.dynamics.act label left target)
    (equivalent : S.Equiv left right)
    (cover : ∀ target, Q.dynamics.act label right target →
      ∃ representative ∈ second, S.Equiv target representative)
    (f : S.Term → V) (respects : ∀ {one two : S.Term}, S.Equiv one two → f one = f two) :
    listSup f first ≤ listSup f second := by
  refine listSup_le_listSup f f fun target member => ?_
  obtain ⟨target', step', close⟩ := Q.dynamics.act_resp_left equivalent (sound target member)
  obtain ⟨representative, representativeMember, close'⟩ := cover target' step'
  exact ⟨representative, representativeMember, le_of_eq ((respects close).trans (respects close'))⟩

/-- **Formulas are functions of equation classes.** -/
theorem val_resp : ∀ (formula : Q.Formula) {left right : S.Term},
    S.Equiv left right → Q.val formula left = Q.val formula right
  | .top, _, _, _ => rfl
  | .atom observation, _, _, equivalent => Q.value_resp observation equivalent
  | .neg inner, _, _, equivalent => by
      rw [val_neg, val_neg, val_resp inner equivalent]
  | .conj first second, _, _, equivalent => by
      rw [val_conj, val_conj, val_resp first equivalent, val_resp second equivalent]
  | .shift threshold inner, _, _, equivalent => by
      rw [val_shift, val_shift, val_resp inner equivalent]
  | .dia label inner, left, right, equivalent => by
      rw [val_dia, val_dia]
      congr 1
      exact le_antisymm
        (Q.listSup_le_of_cover label (Q.successors label left) (Q.successors label right)
          (fun _ member => Q.successors_act member) equivalent
          (fun _ step => Q.successors_cover step) (Q.val inner) (fun close => val_resp inner close))
        (Q.listSup_le_of_cover label (Q.successors label right) (Q.successors label left)
          (fun _ member => Q.successors_act member) (S.equations.iseqv.symm equivalent)
          (fun _ step => Q.successors_cover step) (Q.val inner) (fun close => val_resp inner close))

/-- **Values do not depend on the enumeration.** Any list of actual successors
covering every successor up to the equations gives the same diamond value. -/
theorem val_dia_eq_of_cover (label : Q.dynamics.Label) (inner : Q.Formula) (term : S.Term)
    (list : List S.Term) (sound : ∀ target ∈ list, Q.dynamics.act label term target)
    (cover : ∀ target, Q.dynamics.act label term target →
      ∃ representative ∈ list, S.Equiv target representative) :
    Q.val (.dia label inner) term = K.discount (listSup (Q.val inner) list) := by
  rw [val_dia]
  congr 1
  exact le_antisymm
    (Q.listSup_le_of_cover label (Q.successors label term) list
      (fun _ member => Q.successors_act member) (S.equations.iseqv.refl term) cover (Q.val inner)
      (fun close => Q.val_resp inner close))
    (Q.listSup_le_of_cover label list (Q.successors label term) sound
      (S.equations.iseqv.refl term) (fun _ step => Q.successors_cover step) (Q.val inner)
      (fun close => Q.val_resp inner close))

/-! ## The depth bound -/

variable (W : Q.Vocabulary)

/-- The largest difference of a reading. -/
def observationGap (left right : S.Term) : V :=
  listSup (fun observation => |Q.value observation left - Q.value observation right|)
    W.observations

/-- One step of the Hausdorff recursion. -/
def boundStep (distance : S.Term → S.Term → V) (left right : S.Term) : V :=
  max (Q.observationGap W left right)
    (K.discount (listSup (fun label =>
      hausdorff K.one distance (Q.successors label left) (Q.successors label right)) W.labels))

/-- **The depth bound**: the Hausdorff recursion truncated at depth `n`. -/
def depthBound : ℕ → S.Term → S.Term → V
  | 0 => Q.observationGap W
  | depth + 1 => Q.boundStep W (depthBound depth)

theorem depthBound_zero (left right : S.Term) :
    Q.depthBound W 0 left right = Q.observationGap W left right := rfl

theorem depthBound_succ (depth : ℕ) (left right : S.Term) :
    Q.depthBound W (depth + 1) left right =
      max (Q.observationGap W left right)
        (K.discount (listSup (fun label => hausdorff K.one (Q.depthBound W depth)
          (Q.successors label left) (Q.successors label right)) W.labels)) := rfl

theorem abs_value_sub_le_one (observation : Q.Obs) (left right : S.Term) :
    |Q.value observation left - Q.value observation right| ≤ K.one := by
  rw [abs_sub_le_iff]
  exact ⟨(sub_le_self _ (Q.value_nonneg observation right)).trans (Q.value_le_one observation left),
    (sub_le_self _ (Q.value_nonneg observation left)).trans (Q.value_le_one observation right)⟩

theorem observationGap_nonneg (left right : S.Term) : 0 ≤ Q.observationGap W left right :=
  listSup_nonneg _ _

theorem observationGap_le_one (left right : S.Term) : Q.observationGap W left right ≤ K.one :=
  listSup_le _ K.zero_le_one fun observation _ => Q.abs_value_sub_le_one observation left right

theorem abs_value_sub_le_observationGap (observation : Q.Obs) (left right : S.Term) :
    |Q.value observation left - Q.value observation right| ≤ Q.observationGap W left right :=
  le_listSup (fun observation => |Q.value observation left - Q.value observation right|)
    (W.observations_complete observation)

theorem observationGap_le_depthBound :
    ∀ (depth : ℕ) (left right : S.Term), Q.observationGap W left right ≤ Q.depthBound W depth left right
  | 0, _, _ => le_rfl
  | _ + 1, _, _ => le_max_left _ _

theorem depthBound_nonneg (depth : ℕ) (left right : S.Term) : 0 ≤ Q.depthBound W depth left right :=
  (Q.observationGap_nonneg W left right).trans (Q.observationGap_le_depthBound W depth left right)

theorem depthBound_le_one : ∀ (depth : ℕ) (left right : S.Term), Q.depthBound W depth left right ≤ K.one
  | 0, left, right => Q.observationGap_le_one W left right
  | depth + 1, left, right => by
      rw [depthBound_succ]
      refine max_le (Q.observationGap_le_one W left right) ?_
      refine (K.discount_le (listSup_nonneg _ _)).trans ?_
      exact listSup_le _ K.zero_le_one fun _ _ => hausdorff_le_top K.zero_le_one _ _ _

/-! ## Adequacy at depth `n` -/

/-- **Adequacy at depth `n`.** A formula of modal depth at most `n` changes by
at most the depth-`n` bound. -/
theorem abs_val_sub_le_depthBound : ∀ (formula : Q.Formula) (depth : ℕ) (left right : S.Term),
    formula.depth ≤ depth → |Q.val formula left - Q.val formula right| ≤ Q.depthBound W depth left right
  | .top, depth, left, right, _ => by
      rw [val_top, val_top, sub_self, abs_zero]
      exact Q.depthBound_nonneg W depth left right
  | .atom observation, depth, left, right, _ =>
      (Q.abs_value_sub_le_observationGap W observation left right).trans
        (Q.observationGap_le_depthBound W depth left right)
  | .neg inner, depth, left, right, bounded => by
      rw [val_neg, val_neg, show K.one - Q.val inner left - (K.one - Q.val inner right) =
        Q.val inner right - Q.val inner left by abel, abs_sub_comm]
      exact abs_val_sub_le_depthBound inner depth left right bounded
  | .conj first second, depth, left, right, bounded => by
      rw [val_conj, val_conj]
      exact (abs_min_sub_min_le _ _ _ _).trans
        (max_le (abs_val_sub_le_depthBound first depth left right ((le_max_left _ _).trans bounded))
          (abs_val_sub_le_depthBound second depth left right ((le_max_right _ _).trans bounded)))
  | .shift threshold inner, depth, left, right, bounded => by
      rw [val_shift, val_shift]
      refine (K.abs_clamp_sub_clamp_le _ _).trans ?_
      rw [sub_sub_sub_cancel_right]
      exact abs_val_sub_le_depthBound inner depth left right bounded
  | .dia _ _, 0, _, _, bounded => absurd bounded (Nat.not_succ_le_zero _)
  | .dia label inner, depth + 1, left, right, bounded => by
      have innerBound : inner.depth ≤ depth := Nat.le_of_succ_le_succ bounded
      have close : ∀ first second : S.Term,
          |Q.val inner first - Q.val inner second| ≤ Q.depthBound W depth first second :=
        fun first second => abs_val_sub_le_depthBound inner depth first second innerBound
      rw [val_dia, val_dia, ← K.discount_sub, K.abs_discount]
      refine (K.discount_mono (abs_listSup_sub_listSup_le_hausdorff (top := K.one)
        (distance := Q.depthBound W depth) (fun target _ => Q.val_le_one inner target)
        (fun target _ => Q.val_le_one inner target)
        (fun first _ second _ => sub_le_iff_le_add'.mp ((abs_sub_le_iff.mp (close first second)).1))
        (fun first _ second _ => sub_le_iff_le_add'.mp ((abs_sub_le_iff.mp (close first second)).2)))).trans ?_
      rw [depthBound_succ]
      exact (K.discount_mono (le_listSup (fun label => hausdorff K.one (Q.depthBound W depth)
        (Q.successors label left) (Q.successors label right)) (W.labels_complete label))).trans
        (le_max_right _ _)

/-! ## Expressivity at depth `n` -/

/-- An atom, or its negation, attains the reading gap on any list of names. -/
theorem exists_formula_ge_listSup_gap (left right : S.Term) :
    ∀ list : List Q.Obs, ∃ formula : Q.Formula, formula.depth = 0 ∧
      listSup (fun observation => |Q.value observation left - Q.value observation right|) list ≤
        Q.val formula left - Q.val formula right
  | [] => ⟨.top, rfl, by rw [listSup_nil, val_top, val_top, sub_self]⟩
  | head :: rest => by
      obtain ⟨observation, _, attained⟩ :=
        exists_eq_listSup (fun observation => |Q.value observation left - Q.value observation right|)
          (List.cons_ne_nil head rest) (fun _ _ => abs_nonneg _)
      rw [attained]
      rcases le_total (Q.value observation right) (Q.value observation left) with le | le
      · exact ⟨.atom observation, rfl, by
          rw [val_atom, val_atom, abs_of_nonneg (sub_nonneg.mpr le)]⟩
      · refine ⟨.neg (.atom observation), rfl, ?_⟩
        rw [val_neg, val_neg, val_atom, val_atom, abs_of_nonpos (sub_nonpos.mpr le)]
        exact le_of_eq (by abel)

/-- **Peaks.** From separating formulas of depth at most `n`, one formula of
depth at most `n` is `one` at a center and at most `one − distance` at each
listed term. -/
theorem exists_peak (depth : ℕ) (center : S.Term) (distance : S.Term → V)
    (distanceNonneg : ∀ term, 0 ≤ distance term) (distanceLe : ∀ term, distance term ≤ K.one) :
    ∀ list : List S.Term, (∀ term ∈ list, ∃ formula : Q.Formula, formula.depth ≤ depth ∧
        distance term ≤ Q.val formula center - Q.val formula term) →
      ∃ peak : Q.Formula, peak.depth ≤ depth ∧ Q.val peak center = K.one ∧
        ∀ term ∈ list, Q.val peak term ≤ K.one - distance term
  | [], _ => ⟨.top, Nat.zero_le _, rfl, fun _ member => absurd member List.not_mem_nil⟩
  | head :: rest, separated => by
      obtain ⟨formula, formulaDepth, separation⟩ := separated head List.mem_cons_self
      obtain ⟨peak, peakDepth, peakCenter, peakRest⟩ :=
        exists_peak depth center distance distanceNonneg distanceLe rest
          fun term member => separated term (List.mem_cons_of_mem _ member)
      have bumpCenter : Q.val (.shift (Q.val formula center - K.one) formula) center = K.one := by
        rw [val_shift, sub_sub_cancel]
        exact K.clamp_of_mem K.zero_le_one le_rfl
      have bumpHead : Q.val (.shift (Q.val formula center - K.one) formula) head ≤
          K.one - distance head := by
        rw [val_shift]
        have below : Q.val formula head - (Q.val formula center - K.one) ≤ K.one - distance head :=
          calc Q.val formula head - (Q.val formula center - K.one)
              = K.one - (Q.val formula center - Q.val formula head) := by abel
            _ ≤ K.one - distance head := sub_le_sub_left separation _
        exact (K.clamp_mono below).trans_eq
          (K.clamp_of_mem (sub_nonneg.mpr (distanceLe head)) (sub_le_self _ (distanceNonneg head)))
      refine ⟨.conj (.shift (Q.val formula center - K.one) formula) peak,
        max_le formulaDepth peakDepth, ?_, ?_⟩
      · rw [val_conj, bumpCenter, peakCenter, min_self]
      · intro term member
        rcases List.mem_cons.mp member with rfl | member
        · exact (min_le_left _ _).trans bumpHead
        · exact (min_le_right _ _).trans (peakRest term member)

/-- **The diamond witness.** From separating formulas at depth `n`, a formula of
depth at most `n + 1` separates two terms by at least the discounted Hausdorff
value of the depth-`n` bound on their successors under a label. -/
theorem exists_dia_witness (depth : ℕ) (label : Q.dynamics.Label) (left right : S.Term)
    (separating : ∀ first second : S.Term, ∃ formula : Q.Formula, formula.depth ≤ depth ∧
      Q.depthBound W depth first second ≤ Q.val formula first - Q.val formula second) :
    ∃ formula : Q.Formula, formula.depth ≤ depth + 1 ∧
      K.discount (hausdorff K.one (Q.depthBound W depth) (Q.successors label left)
        (Q.successors label right)) ≤ Q.val formula left - Q.val formula right := by
  have nonneg := Q.depthBound_nonneg W depth
  have le_one := Q.depthBound_le_one W depth
  cases hLeft : Q.successors label left with
  | nil =>
      cases hRight : Q.successors label right with
      | nil =>
          refine ⟨.top, Nat.zero_le _, ?_⟩
          rw [hausdorff_nil_nil, K.discount_zero, val_top, val_top, sub_self]
      | cons other rest =>
          refine ⟨.neg (.dia label .top), Nat.succ_le_succ (Nat.zero_le _), ?_⟩
          rw [val_neg, val_neg, val_dia, val_dia, hLeft, hRight, listSup_nil, K.discount_zero,
            sub_zero, sub_sub_cancel]
          exact (K.discount_mono (hausdorff_le_top K.zero_le_one _ _ _)).trans
            (K.discount_mono (le_listSup (Q.val .top) (List.mem_cons_self (a := other) (l := rest))))
  | cons element first =>
      cases hRight : Q.successors label right with
      | nil =>
          refine ⟨.dia label .top, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
          rw [val_dia, val_dia, hLeft, hRight, listSup_nil, K.discount_zero, sub_zero]
          exact (K.discount_mono (hausdorff_le_top K.zero_le_one _ _ _)).trans
            (K.discount_mono (le_listSup (Q.val .top)
              (List.mem_cons_self (a := element) (l := first))))
      | cons other second =>
          unfold hausdorff
          rcases max_choice
              (listSup (fun element' => listInf K.one (Q.depthBound W depth element')
                (other :: second)) (element :: first))
              (listSup (fun other' => listInf K.one (fun element' => Q.depthBound W depth element' other')
                (element :: first)) (other :: second)) with same | same <;> rw [same]
          · obtain ⟨center, centerMember, attained⟩ :=
              exists_eq_listSup (fun element' => listInf K.one (Q.depthBound W depth element')
                (other :: second)) (List.cons_ne_nil element first)
                (fun element' _ => le_listInf _ _ K.zero_le_one fun other' _ => nonneg element' other')
            rw [attained]
            obtain ⟨peak, peakDepth, peakCenter, peakRest⟩ :=
              Q.exists_peak depth center (Q.depthBound W depth center) (nonneg center) (le_one center)
                (other :: second) fun term _ => separating center term
            refine ⟨.dia label peak, Nat.succ_le_succ peakDepth, ?_⟩
            rw [val_dia, val_dia, hLeft, hRight]
            have upper : K.one ≤ listSup (Q.val peak) (element :: first) :=
              peakCenter ▸ le_listSup (Q.val peak) centerMember
            have lower : listSup (Q.val peak) (other :: second) ≤
                K.one - listInf K.one (Q.depthBound W depth center) (other :: second) :=
              listSup_le _ (sub_nonneg.mpr (listInf_le_top _ _ _)) fun term member =>
                (peakRest term member).trans
                  (sub_le_sub_left (listInf_le K.one (Q.depthBound W depth center) member) _)
            calc K.discount (listInf K.one (Q.depthBound W depth center) (other :: second))
                = K.discount K.one - K.discount
                    (K.one - listInf K.one (Q.depthBound W depth center) (other :: second)) := by
                  rw [← K.discount_sub, sub_sub_cancel]
              _ ≤ _ := sub_le_sub (K.discount_mono upper) (K.discount_mono lower)
          · obtain ⟨center, centerMember, attained⟩ :=
              exists_eq_listSup (fun other' => listInf K.one
                (fun element' => Q.depthBound W depth element' other') (element :: first))
                (List.cons_ne_nil other second)
                (fun other' _ => le_listInf _ _ K.zero_le_one fun element' _ => nonneg element' other')
            rw [attained]
            obtain ⟨peak, peakDepth, peakCenter, peakRest⟩ :=
              Q.exists_peak depth center (fun term => Q.depthBound W depth term center)
                (fun term => nonneg term center) (fun term => le_one term center)
                (element :: first) fun term _ => by
                  obtain ⟨formula, formulaDepth, separation⟩ := separating term center
                  refine ⟨.neg formula, formulaDepth, ?_⟩
                  rw [val_neg, val_neg]
                  exact separation.trans_eq (by abel)
            refine ⟨.neg (.dia label peak), Nat.succ_le_succ peakDepth, ?_⟩
            rw [val_neg, val_neg, val_dia, val_dia, hLeft, hRight]
            have upper : K.one ≤ listSup (Q.val peak) (other :: second) :=
              peakCenter ▸ le_listSup (Q.val peak) centerMember
            have lower : listSup (Q.val peak) (element :: first) ≤
                K.one - listInf K.one (fun term => Q.depthBound W depth term center)
                  (element :: first) :=
              listSup_le _ (sub_nonneg.mpr (listInf_le_top _ _ _)) fun term member =>
                (peakRest term member).trans
                  (sub_le_sub_left (listInf_le K.one (fun term => Q.depthBound W depth term center)
                    member) _)
            calc K.discount (listInf K.one (fun term => Q.depthBound W depth term center)
                  (element :: first))
                = K.discount K.one - K.discount (K.one - listInf K.one
                    (fun term => Q.depthBound W depth term center) (element :: first)) := by
                  rw [← K.discount_sub, sub_sub_cancel]
              _ ≤ K.discount (listSup (Q.val peak) (other :: second)) -
                    K.discount (listSup (Q.val peak) (element :: first)) :=
                  sub_le_sub (K.discount_mono upper) (K.discount_mono lower)
              _ = _ := by abel

/-- **Expressivity at depth `n`, lower form.** An explicit formula of depth at
most `n` separates two terms by at least the depth-`n` bound. -/
theorem exists_formula_le_val_sub : ∀ (depth : ℕ) (left right : S.Term),
    ∃ formula : Q.Formula, formula.depth ≤ depth ∧
      Q.depthBound W depth left right ≤ Q.val formula left - Q.val formula right
  | 0, left, right => by
      obtain ⟨formula, formulaDepth, le⟩ := Q.exists_formula_ge_listSup_gap left right W.observations
      exact ⟨formula, formulaDepth.le, le⟩
  | depth + 1, left, right => by
      rw [depthBound_succ]
      rcases max_choice (Q.observationGap W left right)
          (K.discount (listSup (fun label => hausdorff K.one (Q.depthBound W depth)
            (Q.successors label left) (Q.successors label right)) W.labels)) with same | same <;>
        rw [same]
      · obtain ⟨formula, formulaDepth, le⟩ :=
          Q.exists_formula_ge_listSup_gap left right W.observations
        exact ⟨formula, formulaDepth ▸ Nat.zero_le _, le⟩
      · cases hLabels : W.labels with
        | nil =>
            refine ⟨.top, Nat.zero_le _, ?_⟩
            rw [listSup_nil, K.discount_zero, val_top, val_top, sub_self]
        | cons head rest =>
            obtain ⟨label, _, attained⟩ :=
              exists_eq_listSup (fun label => hausdorff K.one (Q.depthBound W depth)
                (Q.successors label left) (Q.successors label right)) (List.cons_ne_nil head rest)
                (fun _ _ => hausdorff_nonneg _ _ _ _)
            rw [attained]
            exact Q.exists_dia_witness W depth label left right (exists_formula_le_val_sub depth)

/-- **Expressivity at depth `n`.** An explicit formula of depth at most `n`
attains the depth-`n` bound exactly. -/
theorem exists_formula_eq_depthBound (depth : ℕ) (left right : S.Term) :
    ∃ formula : Q.Formula, formula.depth ≤ depth ∧
      Q.val formula left - Q.val formula right = Q.depthBound W depth left right := by
  obtain ⟨formula, formulaDepth, le⟩ := Q.exists_formula_le_val_sub W depth left right
  exact ⟨formula, formulaDepth, le_antisymm
    ((le_abs_self _).trans (Q.abs_val_sub_le_depthBound W formula depth left right formulaDepth)) le⟩

/-! ## The depth bound as a pseudometric characterized by formulas -/

/-- The depth-`n` bound is the least bound on depth-`n` formula differences. -/
theorem depthBound_le_iff (depth : ℕ) (left right : S.Term) (bound : V) :
    Q.depthBound W depth left right ≤ bound ↔
      ∀ formula : Q.Formula, formula.depth ≤ depth →
        |Q.val formula left - Q.val formula right| ≤ bound := by
  constructor
  · intro le formula formulaDepth
    exact (Q.abs_val_sub_le_depthBound W formula depth left right formulaDepth).trans le
  · intro each
    obtain ⟨formula, formulaDepth, attained⟩ := Q.exists_formula_eq_depthBound W depth left right
    rw [← attained]
    exact (le_abs_self _).trans (each formula formulaDepth)

/-- **Zero at depth `n` is agreement on every formula of depth at most `n`.** -/
theorem depthBound_eq_zero_iff (depth : ℕ) (left right : S.Term) :
    Q.depthBound W depth left right = 0 ↔
      ∀ formula : Q.Formula, formula.depth ≤ depth → Q.val formula left = Q.val formula right := by
  constructor
  · intro zero formula formulaDepth
    exact eq_of_abs_sub_nonpos
      ((Q.abs_val_sub_le_depthBound W formula depth left right formulaDepth).trans_eq zero)
  · intro agree
    refine le_antisymm ((Q.depthBound_le_iff W depth left right 0).mpr fun formula formulaDepth => ?_)
      (Q.depthBound_nonneg W depth left right)
    rw [agree formula formulaDepth, sub_self, abs_zero]

theorem depthBound_self (depth : ℕ) (term : S.Term) : Q.depthBound W depth term term = 0 :=
  (Q.depthBound_eq_zero_iff W depth term term).mpr fun _ _ => rfl

theorem depthBound_symm (depth : ℕ) (left right : S.Term) :
    Q.depthBound W depth left right = Q.depthBound W depth right left := by
  have oneWay : ∀ first second : S.Term,
      Q.depthBound W depth first second ≤ Q.depthBound W depth second first := by
    intro first second
    refine (Q.depthBound_le_iff W depth first second _).mpr fun formula formulaDepth => ?_
    rw [abs_sub_comm]
    exact Q.abs_val_sub_le_depthBound W formula depth second first formulaDepth
  exact le_antisymm (oneWay left right) (oneWay right left)

theorem depthBound_triangle (depth : ℕ) (first second third : S.Term) :
    Q.depthBound W depth first third ≤
      Q.depthBound W depth first second + Q.depthBound W depth second third := by
  obtain ⟨formula, formulaDepth, attained⟩ := Q.exists_formula_eq_depthBound W depth first third
  rw [← attained, show Q.val formula first - Q.val formula third =
    (Q.val formula first - Q.val formula second) + (Q.val formula second - Q.val formula third) by
      abel]
  exact add_le_add
    ((le_abs_self _).trans (Q.abs_val_sub_le_depthBound W formula depth first second formulaDepth))
    ((le_abs_self _).trans (Q.abs_val_sub_le_depthBound W formula depth second third formulaDepth))

/-- **The depth bounds increase with the depth.** -/
theorem depthBound_mono {depth depth' : ℕ} (le : depth ≤ depth') (left right : S.Term) :
    Q.depthBound W depth left right ≤ Q.depthBound W depth' left right := by
  obtain ⟨formula, formulaDepth, attained⟩ := Q.exists_formula_eq_depthBound W depth left right
  rw [← attained]
  exact (le_abs_self _).trans
    (Q.abs_val_sub_le_depthBound W formula depth' left right (formulaDepth.trans le))

theorem depthBound_resp_left (depth : ℕ) {left left' : S.Term} (equivalent : S.Equiv left left')
    (right : S.Term) : Q.depthBound W depth left right = Q.depthBound W depth left' right := by
  have oneWay : ∀ {first first' : S.Term}, S.Equiv first first' →
      Q.depthBound W depth first right ≤ Q.depthBound W depth first' right := by
    intro first first' close
    refine (Q.depthBound_le_iff W depth first right _).mpr fun formula formulaDepth => ?_
    rw [Q.val_resp formula close]
    exact Q.abs_val_sub_le_depthBound W formula depth first' right formulaDepth
  exact le_antisymm (oneWay equivalent) (oneWay (S.equations.iseqv.symm equivalent))

theorem depthBound_resp_right (depth : ℕ) (left : S.Term) {right right' : S.Term}
    (equivalent : S.Equiv right right') :
    Q.depthBound W depth left right = Q.depthBound W depth left right' := by
  rw [Q.depthBound_symm W depth left right, Q.depthBound_resp_left W depth equivalent left,
    Q.depthBound_symm W depth right' left]

/-- **The bound is a property of the system, not of the vocabulary lists.** -/
theorem depthBound_vocabulary (W' : Q.Vocabulary) (depth : ℕ) (left right : S.Term) :
    Q.depthBound W depth left right = Q.depthBound W' depth left right := by
  have oneWay : ∀ first second : Q.Vocabulary,
      Q.depthBound first depth left right ≤ Q.depthBound second depth left right := by
    intro first second
    refine (Q.depthBound_le_iff first depth left right _).mpr fun formula formulaDepth => ?_
    exact Q.abs_val_sub_le_depthBound second formula depth left right formulaDepth
  exact le_antisymm (oneWay W W') (oneWay W' W)

/-! ## Bisimulation approximants -/

/-- **The `n`-step bisimulation approximant**: equal readings, and at positive
depth every labelled step is matched by a step to an approximant of one depth
less. -/
def Approx : ℕ → S.Term → S.Term → Prop
  | 0, left, right => ∀ observation, Q.value observation left = Q.value observation right
  | depth + 1, left, right =>
      (∀ observation, Q.value observation left = Q.value observation right) ∧
        (∀ (label : Q.dynamics.Label) (left' : S.Term), Q.dynamics.act label left left' →
          ∃ right', Q.dynamics.act label right right' ∧ Approx depth left' right') ∧
        (∀ (label : Q.dynamics.Label) (right' : S.Term), Q.dynamics.act label right right' →
          ∃ left', Q.dynamics.act label left left' ∧ Approx depth left' right')

theorem approx_values : ∀ {depth : ℕ} {left right : S.Term}, Q.Approx depth left right →
    ∀ observation, Q.value observation left = Q.value observation right
  | 0, _, _, approx => approx
  | _ + 1, _, _, approx => approx.1

theorem approx_refl : ∀ (depth : ℕ) (term : S.Term), Q.Approx depth term term
  | 0, _ => fun _ => rfl
  | depth + 1, _ => ⟨fun _ => rfl, fun _ left' step => ⟨left', step, approx_refl depth left'⟩,
      fun _ right' step => ⟨right', step, approx_refl depth right'⟩⟩

/-- Approximants agree on every formula of at most their depth.  No positivity
of the discount is needed. -/
theorem val_eq_of_approx : ∀ (formula : Q.Formula) {depth : ℕ} {left right : S.Term},
    formula.depth ≤ depth → Q.Approx depth left right → Q.val formula left = Q.val formula right
  | .top, _, _, _, _, _ => rfl
  | .atom observation, _, _, _, _, approx => Q.approx_values approx observation
  | .neg inner, _, _, _, bounded, approx => by
      rw [val_neg, val_neg, val_eq_of_approx inner bounded approx]
  | .conj first second, _, _, _, bounded, approx => by
      rw [val_conj, val_conj, val_eq_of_approx first ((le_max_left _ _).trans bounded) approx,
        val_eq_of_approx second ((le_max_right _ _).trans bounded) approx]
  | .shift threshold inner, _, _, _, bounded, approx => by
      rw [val_shift, val_shift, val_eq_of_approx inner bounded approx]
  | .dia _ _, 0, _, _, bounded, _ => absurd bounded (Nat.not_succ_le_zero _)
  | .dia label inner, depth + 1, left, right, bounded, approx => by
      have innerBound : inner.depth ≤ depth := Nat.le_of_succ_le_succ bounded
      rw [val_dia, val_dia]
      congr 1
      refine le_antisymm (listSup_le_listSup _ _ fun target member => ?_)
        (listSup_le_listSup _ _ fun target member => ?_)
      · obtain ⟨right', step, approx'⟩ :=
          approx.2.1 label target (Q.successors_act member)
        obtain ⟨representative, representativeMember, close⟩ := Q.successors_cover step
        exact ⟨representative, representativeMember, le_of_eq
          ((val_eq_of_approx inner innerBound approx').trans (Q.val_resp inner close))⟩
      · obtain ⟨left', step, approx'⟩ :=
          approx.2.2 label target (Q.successors_act member)
        obtain ⟨representative, representativeMember, close⟩ := Q.successors_cover step
        exact ⟨representative, representativeMember, le_of_eq
          ((val_eq_of_approx inner innerBound approx').symm.trans (Q.val_resp inner close))⟩

theorem depthBound_eq_zero_of_approx {depth : ℕ} {left right : S.Term}
    (approx : Q.Approx depth left right) : Q.depthBound W depth left right = 0 :=
  (Q.depthBound_eq_zero_iff W depth left right).mpr fun formula formulaDepth =>
    Q.val_eq_of_approx formula formulaDepth approx

theorem values_eq_of_observationGap_le_zero {left right : S.Term}
    (zero : Q.observationGap W left right ≤ 0) (observation : Q.Obs) :
    Q.value observation left = Q.value observation right :=
  eq_of_abs_sub_nonpos ((Q.abs_value_sub_le_observationGap W observation left right).trans zero)

/-- With a positive discount, a zero depth-`n` bound gives the `n`-step
approximant. -/
theorem approx_of_depthBound_eq_zero (positive : K.Positive) :
    ∀ {depth : ℕ} {left right : S.Term}, Q.depthBound W depth left right = 0 →
      Q.Approx depth left right
  | 0, _, _, zero => Q.values_eq_of_observationGap_le_zero W zero.le
  | depth + 1, left, right, zero => by
      have gapZero : Q.observationGap W left right ≤ 0 := (le_max_left _ _).trans zero.le
      have sumZero := Scale.eq_zero_of_discount_le_zero positive (listSup_nonneg _ _)
        ((le_max_right _ _).trans zero.le)
      have labelZero : ∀ label : Q.dynamics.Label,
          hausdorff K.one (Q.depthBound W depth) (Q.successors label left)
            (Q.successors label right) ≤ 0 := fun label =>
        (le_listSup (fun label => hausdorff K.one (Q.depthBound W depth)
          (Q.successors label left) (Q.successors label right)) (W.labels_complete label)).trans
          sumZero.le
      refine ⟨Q.values_eq_of_observationGap_le_zero W gapZero, ?_, ?_⟩
      · intro label left' step
        obtain ⟨representative, representativeMember, close⟩ := Q.successors_cover step
        obtain ⟨right', rightMember, matched⟩ :=
          exists_zero_of_hausdorff_le_zero K.one_pos
            (fun first _ second _ => Q.depthBound_nonneg W depth first second)
            (fun first _ second _ => Q.depthBound_le_one W depth first second)
            (labelZero label) representativeMember
        refine ⟨right', Q.successors_act rightMember, approx_of_depthBound_eq_zero positive ?_⟩
        rw [Q.depthBound_resp_left W depth close right']
        exact matched
      · intro label right' step
        obtain ⟨representative, representativeMember, close⟩ := Q.successors_cover step
        obtain ⟨left', leftMember, matched⟩ :=
          exists_zero_of_hausdorff_le_zero' K.one_pos
            (fun first _ second _ => Q.depthBound_nonneg W depth first second)
            (fun first _ second _ => Q.depthBound_le_one W depth first second)
            (labelZero label) representativeMember
        refine ⟨left', Q.successors_act leftMember, approx_of_depthBound_eq_zero positive ?_⟩
        rw [Q.depthBound_resp_right W depth left' close]
        exact matched

/-- **Zero at depth `n` is the `n`-step approximant**, for a positive discount. -/
theorem depthBound_eq_zero_iff_approx (positive : K.Positive) (depth : ℕ) (left right : S.Term) :
    Q.depthBound W depth left right = 0 ↔ Q.Approx depth left right :=
  ⟨Q.approx_of_depthBound_eq_zero W positive, Q.depthBound_eq_zero_of_approx W⟩

/-! ## Infinite witnesses -/

/-- A bisimulation of the labelled steps that preserves every reading exactly. -/
def IsGradedBisimulation (relation : S.Term → S.Term → Prop) : Prop :=
  (∀ ⦃left right⦄, relation left right → ∀ (label : Q.dynamics.Label) ⦃left'⦄,
      Q.dynamics.act label left left' →
        ∃ right', Q.dynamics.act label right right' ∧ relation left' right') ∧
    (∀ ⦃left right⦄, relation left right → ∀ (label : Q.dynamics.Label) ⦃right'⦄,
      Q.dynamics.act label right right' →
        ∃ left', Q.dynamics.act label left left' ∧ relation left' right') ∧
    (∀ ⦃left right⦄, relation left right → ∀ observation,
      Q.value observation left = Q.value observation right)

/-- **A coherent infinite witness**: some graded bisimulation relates the terms. -/
def GradedBisimilar (left right : S.Term) : Prop :=
  ∃ relation, Q.IsGradedBisimulation relation ∧ relation left right

theorem approx_of_isGradedBisimulation {relation : S.Term → S.Term → Prop}
    (bisimulation : Q.IsGradedBisimulation relation) :
    ∀ (depth : ℕ) {left right : S.Term}, relation left right → Q.Approx depth left right
  | 0, _, _, related => bisimulation.2.2 related
  | depth + 1, _, _, related =>
      ⟨bisimulation.2.2 related,
        fun label _ step => by
          obtain ⟨right', step', related'⟩ := bisimulation.1 related label step
          exact ⟨right', step', approx_of_isGradedBisimulation bisimulation depth related'⟩,
        fun label _ step => by
          obtain ⟨left', step', related'⟩ := bisimulation.2.1 related label step
          exact ⟨left', step', approx_of_isGradedBisimulation bisimulation depth related'⟩⟩

/-- **An infinite witness gives agreement at every finite depth.** -/
theorem depthBound_eq_zero_of_gradedBisimilar {left right : S.Term}
    (bisimilar : Q.GradedBisimilar left right) (depth : ℕ) :
    Q.depthBound W depth left right = 0 := by
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  exact Q.depthBound_eq_zero_of_approx W (Q.approx_of_isGradedBisimulation bisimulation depth related)

theorem val_eq_of_gradedBisimilar {left right : S.Term} (bisimilar : Q.GradedBisimilar left right)
    (formula : Q.Formula) : Q.val formula left = Q.val formula right := by
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  exact Q.val_eq_of_approx formula le_rfl
    (Q.approx_of_isGradedBisimulation bisimulation formula.depth related)

/-- The equations are a graded bisimulation. -/
theorem isGradedBisimulation_equiv : Q.IsGradedBisimulation S.Equiv := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right equivalent label left' step
    exact Q.dynamics.act_resp_left equivalent step
  · intro left right equivalent label right' step
    obtain ⟨left', step', equivalent'⟩ :=
      Q.dynamics.act_resp_left (S.equations.iseqv.symm equivalent) step
    exact ⟨left', step', S.equations.iseqv.symm equivalent'⟩
  · intro left right equivalent observation
    exact Q.value_resp observation equivalent

/-! ## Convergence: successive bounds and the geometric tail -/

/-- **Successive bounds differ by at most the iterated discount of `one`.** -/
theorem depthBound_succ_le : ∀ (depth : ℕ) (left right : S.Term),
    Q.depthBound W (depth + 1) left right ≤
      Q.depthBound W depth left right + K.discount^[depth] K.one
  | 0, left, right =>
      (Q.depthBound_le_one W 1 left right).trans
        (le_add_of_nonneg_left (Q.depthBound_nonneg W 0 left right))
  | depth + 1, left, right => by
      have slackNonneg := K.iterate_discount_nonneg depth K.zero_le_one
      rw [Q.depthBound_succ W (depth + 1), Q.depthBound_succ W depth]
      refine max_le_max_add (K.iterate_discount_nonneg (depth + 1) K.zero_le_one) ?_
      rw [Function.iterate_succ_apply', ← K.discount_add]
      refine K.discount_mono (listSup_le_listSup_add_of_le slackNonneg fun label _ => ?_)
      exact hausdorff_le_hausdorff_add slackNonneg fun first _ second _ =>
        depthBound_succ_le depth first second

/-- **The tail bound**: bounds `j` steps deeper exceed the depth-`n` bound by at
most the geometric tail.  With a discount whose iterates are summable this is
a convergence modulus; at discount one it is no information. -/
theorem depthBound_add_le (depth : ℕ) : ∀ (extra : ℕ) (left right : S.Term),
    Q.depthBound W (depth + extra) left right ≤ Q.depthBound W depth left right + K.tail depth extra
  | 0, left, right => by rw [Nat.add_zero, Scale.tail, add_zero]
  | extra + 1, left, right => by
      rw [Scale.tail, ← add_assoc (Q.depthBound W depth left right)]
      exact (Q.depthBound_succ_le W (depth + extra) left right).trans
        (add_le_add (depthBound_add_le depth extra left right) le_rfl)

/-! ## Stabilization: a certificate that closes the gap constructively -/

/-- **A stabilization certificate at depth `N`**: one more step changes no bound. -/
def Stabilizes (stage : ℕ) : Prop :=
  ∀ left right : S.Term, Q.depthBound W (stage + 1) left right = Q.depthBound W stage left right

/-- After a stabilization stage the bounds are constant. -/
theorem depthBound_add_of_stabilizes {stage : ℕ} (stable : Q.Stabilizes W stage) :
    ∀ (extra : ℕ) (left right : S.Term),
      Q.depthBound W (stage + extra) left right = Q.depthBound W stage left right
  | 0, _, _ => rfl
  | extra + 1, left, right => by
      have same : Q.depthBound W (stage + extra) = Q.depthBound W stage :=
        funext fun first => funext fun second => depthBound_add_of_stabilizes stable extra first second
      show Q.boundStep W (Q.depthBound W (stage + extra)) left right = _
      rw [same]
      exact stable left right

/-- **Reflection from a certificate.** With a positive discount and a
stabilization stage, zero at that stage is a graded bisimulation. -/
theorem isGradedBisimulation_of_stabilizes (positive : K.Positive) {stage : ℕ}
    (stable : Q.Stabilizes W stage) :
    Q.IsGradedBisimulation fun left right => Q.depthBound W stage left right = 0 := by
  have next : ∀ {left right : S.Term}, Q.depthBound W stage left right = 0 →
      Q.Approx (stage + 1) left right := fun zero =>
    Q.approx_of_depthBound_eq_zero W positive ((stable _ _).trans zero)
  refine ⟨?_, ?_, ?_⟩
  · intro left right zero label left' step
    obtain ⟨right', step', approx⟩ := (next zero).2.1 label left' step
    exact ⟨right', step', Q.depthBound_eq_zero_of_approx W approx⟩
  · intro left right zero label right' step
    obtain ⟨left', step', approx⟩ := (next zero).2.2 label right' step
    exact ⟨left', step', Q.depthBound_eq_zero_of_approx W approx⟩
  · intro left right zero observation
    exact Q.approx_values (next zero) observation

/-- **Under a certificate the three notions coincide**: an infinite witness,
agreement at every finite depth, and agreement at the stabilization stage. -/
theorem gradedBisimilar_iff_of_stabilizes (positive : K.Positive) {stage : ℕ}
    (stable : Q.Stabilizes W stage) (left right : S.Term) :
    (Q.GradedBisimilar left right ↔ ∀ depth, Q.depthBound W depth left right = 0) ∧
      (Q.GradedBisimilar left right ↔ Q.depthBound W stage left right = 0) := by
  have toWitness : Q.depthBound W stage left right = 0 → Q.GradedBisimilar left right :=
    fun zero => ⟨_, Q.isGradedBisimulation_of_stabilizes W positive stable, zero⟩
  exact ⟨⟨fun bisimilar depth => Q.depthBound_eq_zero_of_gradedBisimilar W bisimilar depth,
      fun zero => toWitness (zero stage)⟩,
    ⟨fun bisimilar => Q.depthBound_eq_zero_of_gradedBisimilar W bisimilar stage, toWitness⟩⟩

end PresentedSystem

end Mettapedia.GSLT.Distinction.Constructive
