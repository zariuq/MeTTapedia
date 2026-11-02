import Mettapedia.ProbabilityTheory.ImpreciseProbability.FiniteConditionalConstraints
import Mettapedia.Logic.Arithmetic.FourierMotzkin

/-!
# Certified exact bounds for finite conditional constraints

All distribution variables range over the reals. Rational constraints compile
to the existing Fourier–Motzkin engine. To query `A | C`, scale the whole table
so its mass on `C` is one, then project onto the mass of `A ∩ C`. Projection of
these non-strict inequalities is again closed. This establishes attainment
without assuming a positive lower bound on conditioning mass across models.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.ConditionalConstraintBounds

open scoped BigOperators
open FiniteConditionalConstraints FiniteEventMass
open Mettapedia.Logic.Arithmetic

def coefficients {n : Nat} (f : Fin n → ℚ) : FourierMotzkin.Coeff n :=
  Nat.recOn (motive := fun n => (Fin n → ℚ) → FourierMotzkin.Coeff n) n
    (fun _ => .nil) (fun n rest f => .cons (f 0) (rest (fun i : Fin n => f i.succ))) f

@[simp] theorem coefficients_succ {n : Nat} (f : Fin (n+1) → ℚ) :
    coefficients f = .cons (f 0) (coefficients (fun i : Fin n => f i.succ)) := rfl

theorem coefficients_dot {n : Nat} (f : Fin n → ℚ) (env : Fin n → ℝ) :
    (coefficients f).dot env = ∑ i, (f i : ℝ) * env i := by
  induction n with
  | zero => simp [coefficients, FourierMotzkin.Coeff.dot]
  | succ n ih => simp only [coefficients_succ, FourierMotzkin.Coeff.dot, ih, Fin.sum_univ_succ]

def linear {n : Nat} (f : Fin n → ℚ) (constant : ℚ) : FourierMotzkin.LinTerm n := ⟨coefficients f, constant⟩

theorem linear_eval {n : Nat} (f : Fin n → ℚ) (constant : ℚ) (env : Fin n → ℝ) :
    (linear f constant).eval env = (∑ i, (f i : ℝ) * env i) + constant := by
  simp [linear, FourierMotzkin.LinTerm.eval, coefficients_dot]

def varTerm {n : Nat} (i : Fin n) : FourierMotzkin.LinTerm n := linear (fun j => if j = i then 1 else 0) 0

@[simp] theorem variable_eval {n : Nat} (i : Fin n) (env : Fin n → ℝ) : (varTerm i).eval env = env i := by
  simp only [varTerm, linear_eval]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ different
    simp [different]
  · simp

def constant {n : Nat} (value : ℚ) : FourierMotzkin.LinTerm n := linear (fun _ => 0) value

@[simp] theorem constant_eval {n : Nat} (value : ℚ) (env : Fin n → ℝ) :
    (constant value).eval env = (value : ℝ) := by simp [constant, linear_eval]

/-- Distribution coordinates come first; the final coordinate is the query value. -/
def eventTerm {n : Nat} (event : Fin n → Bool) : FourierMotzkin.LinTerm (n+1) :=
  linear (Fin.lastCases 0 (fun i => if event i then 1 else 0)) 0

theorem eventTerm_eval {n : Nat} (event : Fin n → Bool) (env : Fin (n+1) → ℝ) :
    (eventTerm event).eval env = mass (fun i => env i.castSucc) event := by
  simp only [eventTerm, linear_eval, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
    Fin.lastCases_last, Rat.cast_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  cases event i <;> simp

def equalAtoms {n : Nat} (first second : FourierMotzkin.LinTerm n) : List (FourierMotzkin.Atom n) :=
  [⟨first.sub second, .le⟩, ⟨second.sub first, .le⟩]

theorem equalAtoms_sat {n : Nat} (first second : FourierMotzkin.LinTerm n) (env : Fin n → ℝ) :
    FourierMotzkin.allSat (equalAtoms first second) env ↔ first.eval env = second.eval env := by
  simp only [FourierMotzkin.allSat, equalAtoms, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, FourierMotzkin.Atom.sat, FourierMotzkin.holds, FourierMotzkin.eval_sub]
  constructor
  · rintro ⟨first, second⟩
    linarith
  · intro h
    constructor <;> linarith

def constraintAtoms {n : Nat} (c : Constraint (Fin n)) : List (FourierMotzkin.Atom (n+1)) :=
  [⟨(eventTerm c.condition).scale c.lower |>.sub (eventTerm (fun w => c.event w && c.condition w)), .le⟩,
   ⟨(eventTerm (fun w => c.event w && c.condition w)).sub ((eventTerm c.condition).scale c.upper), .le⟩]

theorem constraintAtoms_sat {n : Nat} (c : Constraint (Fin n)) (env : Fin (n+1) → ℝ) :
    FourierMotzkin.allSat (constraintAtoms c) env ↔ c.Holds (fun i => env i.castSucc) := by
  simp [FourierMotzkin.allSat, constraintAtoms, FourierMotzkin.Atom.sat, FourierMotzkin.holds, FourierMotzkin.eval_sub, FourierMotzkin.eval_scale,
    eventTerm_eval, Constraint.Holds]

def baseAtoms {n : Nat} (base : KnowledgeBase (Fin n)) : List (FourierMotzkin.Atom (n+1)) :=
  (List.finRange n).map (fun i => ⟨(varTerm i.castSucc).scale (-1), .le⟩) ++
    base.flatMap constraintAtoms

theorem baseAtoms_sat {n : Nat} (base : KnowledgeBase (Fin n)) (env : Fin (n+1) → ℝ) :
    FourierMotzkin.allSat (baseAtoms base) env ↔
      (∀ i : Fin n, 0 ≤ env i.castSucc) ∧ Satisfies base (fun i => env i.castSucc) := by
  rw [baseAtoms, FourierMotzkin.allSat_append]
  simp only [FourierMotzkin.allSat, List.forall_mem_map, List.mem_finRange, forall_const,
    List.forall_mem_flatMap]
  change (∀ i : Fin n, ((varTerm i.castSucc).scale (-1)).eval env ≤ 0) ∧
      (∀ c ∈ base, FourierMotzkin.allSat (constraintAtoms c) env) ↔ _
  simp only [FourierMotzkin.eval_scale, variable_eval, Rat.cast_neg, Rat.cast_one, neg_one_mul, neg_nonpos,
    constraintAtoms_sat, Satisfies]

def scaledAtoms {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    List (FourierMotzkin.Atom (n+1)) :=
  baseAtoms base ++ equalAtoms (eventTerm condition) (constant 1) ++
    equalAtoms (varTerm (Fin.last n)) (eventTerm (fun w => event w && condition w))

theorem scaledAtoms_sat {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (env : Fin (n+1) → ℝ) :
    FourierMotzkin.allSat (scaledAtoms base event condition) env ↔
      ScaledFeasible base condition (fun i => env i.castSucc) ∧
        env (Fin.last n) = mass (fun i => env i.castSucc) (fun w => event w && condition w) := by
  simp only [scaledAtoms, FourierMotzkin.allSat_append, baseAtoms_sat, equalAtoms_sat, eventTerm_eval,
    constant_eval, variable_eval, Rat.cast_one, ScaledFeasible]
  tauto

/-! ## Projection retains closed halfspaces -/

def NonStrict {n : Nat} (atoms : List (FourierMotzkin.Atom n)) : Prop := ∀ a ∈ atoms, a.rel = .le

private theorem classify_nonStrict {n : Nat} (a : FourierMotzkin.Atom (n+1)) (closed : a.rel = .le) :
    match FourierMotzkin.classify a with
    | .keep r => r.rel = .le
    | .lower b => b.strict = false
    | .upper b => b.strict = false := by
  obtain ⟨⟨coeff, constant⟩, rel⟩ := a
  cases coeff with
  | cons head tail =>
    change rel = .le at closed
    subst rel
    simp only [FourierMotzkin.classify]
    split_ifs <;> rfl

private theorem lower_closed {n : Nat} (atoms : List (FourierMotzkin.Atom (n+1))) (closed : NonStrict atoms)
    (bound : FourierMotzkin.Bound n) (member : bound ∈ FourierMotzkin.lowers atoms) : bound.strict = false := by
  obtain ⟨a, member, same⟩ := FourierMotzkin.mem_lowers.mp member
  have result := classify_nonStrict a (closed a member)
  simpa only [same] using result

private theorem upper_closed {n : Nat} (atoms : List (FourierMotzkin.Atom (n+1))) (closed : NonStrict atoms)
    (bound : FourierMotzkin.Bound n) (member : bound ∈ FourierMotzkin.uppers atoms) : bound.strict = false := by
  obtain ⟨a, member, same⟩ := FourierMotzkin.mem_uppers.mp member
  have result := classify_nonStrict a (closed a member)
  simpa only [same] using result

theorem project_nonStrict {n : Nat} (atoms : List (FourierMotzkin.Atom (n+1))) (closed : NonStrict atoms) :
    NonStrict (FourierMotzkin.project atoms) := by
  induction atoms with
  | nil => simp [FourierMotzkin.project, NonStrict]
  | cons a rest ih =>
    have tail : NonStrict rest := fun b hb => closed b (List.mem_cons_of_mem _ hb)
    have head := classify_nonStrict a (closed a (List.mem_cons_self ..))
    intro b hb
    cases same : FourierMotzkin.classify a with
    | keep r =>
      rw [FourierMotzkin.project_keep same] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa only [same] using head
      · exact ih tail b hb
    | lower bound =>
      rw [FourierMotzkin.project_lower same] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih tail b hb
      · obtain ⟨hi, member, rfl⟩ := List.mem_map.mp hb
        have strict : bound.strict = false := by simpa only [same] using head
        simp [FourierMotzkin.cross, strict, upper_closed rest tail hi member]
    | upper bound =>
      rw [FourierMotzkin.project_upper same] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih tail b hb
      · obtain ⟨lo, member, rfl⟩ := List.mem_map.mp hb
        have strict : bound.strict = false := by simpa only [same] using head
        simp [FourierMotzkin.cross, strict, lower_closed rest tail lo member]

def projectToOne (n : Nat) (atoms : List (FourierMotzkin.Atom (n+1))) : List (FourierMotzkin.Atom 1) :=
  Nat.recOn (motive := fun n => List (FourierMotzkin.Atom (n+1)) → List (FourierMotzkin.Atom 1)) n
    (fun atoms => atoms) (fun _ rest atoms => rest (FourierMotzkin.project atoms)) atoms

@[simp] theorem projectToOne_succ (n : Nat) (atoms : List (FourierMotzkin.Atom (n+1+1))) :
    projectToOne (n+1) atoms = projectToOne n (FourierMotzkin.project atoms) := rfl

theorem projectToOne_closed (n : Nat) (atoms : List (FourierMotzkin.Atom (n+1))) (closed : NonStrict atoms) :
    NonStrict (projectToOne n atoms) := by
  induction n with
  | zero => exact closed
  | succ n ih => exact ih _ (project_nonStrict atoms closed)

theorem projectToOne_sat (n : Nat) (atoms : List (FourierMotzkin.Atom (n+1))) (value : ℝ) :
    FourierMotzkin.allSat (projectToOne n atoms) (fun _ => value) ↔
      ∃ env : Fin (n+1) → ℝ, FourierMotzkin.allSat atoms env ∧ env (Fin.last n) = value := by
  induction n with
  | zero =>
    constructor
    · intro held
      exact ⟨fun _ => value, held, rfl⟩
    · rintro ⟨env, held, equal⟩
      have same : env = fun _ => value := by
        funext i
        have index : i = Fin.last 0 := by apply Fin.ext; omega
        simpa [index] using equal
      simpa [projectToOne, same] using held
  | succ n ih =>
    rw [projectToOne_succ, ih]
    constructor
    · rintro ⟨tail, held, equal⟩
      obtain ⟨head, whole⟩ := (FourierMotzkin.project_iff atoms tail).mpr held
      exact ⟨FourierMotzkin.envCons head tail, whole, by
        change tail (Fin.last n) = value
        exact equal⟩
    · rintro ⟨env, held, equal⟩
      refine ⟨FourierMotzkin.envTail env, (FourierMotzkin.project_iff atoms (FourierMotzkin.envTail env)).mp ⟨env 0, ?_⟩, ?_⟩
      · simpa only [← FourierMotzkin.env_eq_cons] using held
      · simpa [FourierMotzkin.envTail] using equal

theorem scaledAtoms_closed {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    NonStrict (scaledAtoms base event condition) := by
  intro a member
  simp only [scaledAtoms, baseAtoms, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with ((⟨i, _, rfl⟩ | ⟨c, _, member⟩) | member) | member
  · rfl
  · simp only [constraintAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  all_goals
    simp only [equalAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

def projected {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) : List (FourierMotzkin.Atom 1) :=
  projectToOne n (scaledAtoms base event condition)

theorem projected_values {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) (value : ℝ) :
    FourierMotzkin.allSat (projected base event condition) (fun _ => value) ↔ value ∈ queryValues base event condition := by
  rw [projected, projectToOne_sat, queryValues_scaled]
  constructor
  · rintro ⟨env, held, equal⟩
    obtain ⟨feasible, observed⟩ := (scaledAtoms_sat base event condition env).mp held
    exact ⟨_, feasible, observed.symm.trans equal⟩
  · rintro ⟨weight, feasible, observed⟩
    refine ⟨Fin.lastCases value weight, (scaledAtoms_sat base event condition _).mpr ?_, by simp⟩
    simpa using And.intro feasible observed.symm

theorem coefficients_continuous {n : Nat} (c : FourierMotzkin.Coeff n) :
    Continuous (fun env : Fin n → ℝ => c.dot env) := by
  induction c with
  | nil => exact continuous_const
  | @cons n head tail ih =>
    change Continuous (fun env : Fin (n+1) → ℝ => (head : ℝ) * env 0 + tail.dot (fun i => env i.succ))
    exact (continuous_const.mul (continuous_apply 0)).add
      (ih.comp (continuous_pi (fun i => continuous_apply i.succ)))

/-- Closedness is obtained from the projected non-strict inequalities, not
from a claim that arbitrary continuous images of closed sets are closed. -/
theorem projected_values_closed {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    IsClosed (queryValues base event condition) := by
  have same : queryValues base event condition =
      {value | FourierMotzkin.allSat (projected base event condition) (fun _ => value)} := by
    ext value
    exact (projected_values base event condition value).symm
  rw [same]
  simp only [FourierMotzkin.allSat, Set.ofPred_forall]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro member
  have closed := projectToOne_closed n _ (scaledAtoms_closed base event condition) a member
  simp only [FourierMotzkin.Atom.sat, closed, FourierMotzkin.holds, FourierMotzkin.LinTerm.eval]
  exact isClosed_le
    (((coefficients_continuous a.term.coeff).comp (continuous_pi (fun _ => continuous_id))).add continuous_const)
    continuous_const

theorem queryValues_compact {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    IsCompact (queryValues base event condition) :=
  isCompact_Icc.of_isClosed_subset (projected_values_closed base event condition)
    (queryValues_subset_unit base event condition)

/-! ## Exact rational endpoints of the one-dimensional projection -/

def lowerValues (atoms : List (FourierMotzkin.Atom 1)) : List (Bool × ℚ) :=
  (false, 0) :: (FourierMotzkin.lowers atoms).map (fun b => (false, b.term.const))

def upperValues (atoms : List (FourierMotzkin.Atom 1)) : List (Bool × ℚ) :=
  (false, 1) :: (FourierMotzkin.uppers atoms).map (fun b => (false, b.term.const))

def lowerEndpoint (atoms : List (FourierMotzkin.Atom 1)) : ℚ :=
  ((FourierMotzkin.tightLower (lowerValues atoms)).getD (false, 0)).2

def upperEndpoint (atoms : List (FourierMotzkin.Atom 1)) : ℚ :=
  ((FourierMotzkin.tightUpper (upperValues atoms)).getD (false, 1)).2

private theorem lowerEndpoint_spec (atoms : List (FourierMotzkin.Atom 1)) :
    (false, lowerEndpoint atoms) ∈ lowerValues atoms ∧
      ∀ q, (false, q) ∈ lowerValues atoms → q ≤ lowerEndpoint atoms := by
  have existsValue : ∃ bound, FourierMotzkin.tightLower (lowerValues atoms) = some bound := by
    cases result : FourierMotzkin.tightLower (lowerValues atoms) with
    | none => have impossible := (FourierMotzkin.tightLower_eq_none _).mp result; simp [lowerValues] at impossible
    | some bound => exact ⟨bound, rfl⟩
  obtain ⟨bound, result⟩ := existsValue
  obtain ⟨member, greatest, _⟩ := FourierMotzkin.tightLower_spec _ _ result
  have flag : bound.1 = false := by
    rcases List.mem_cons.mp member with same | member
    · exact congrArg Prod.fst same
    · obtain ⟨b, _, same⟩ := List.mem_map.mp member
      exact (congrArg Prod.fst same).symm
  simp only [lowerEndpoint, result, Option.getD_some]
  exact ⟨by simpa [flag] using member, fun q hq => greatest false q hq⟩

private theorem upperEndpoint_spec (atoms : List (FourierMotzkin.Atom 1)) :
    (false, upperEndpoint atoms) ∈ upperValues atoms ∧
      ∀ q, (false, q) ∈ upperValues atoms → upperEndpoint atoms ≤ q := by
  have existsValue : ∃ bound, FourierMotzkin.tightUpper (upperValues atoms) = some bound := by
    unfold FourierMotzkin.tightUpper
    cases result : FourierMotzkin.tightLower ((upperValues atoms).map fun p => (p.1, -p.2)) with
    | none =>
      have impossible := (FourierMotzkin.tightLower_eq_none _).mp result
      simp [upperValues] at impossible
    | some bound => exact ⟨_, rfl⟩
  obtain ⟨bound, result⟩ := existsValue
  obtain ⟨member, least, _⟩ := FourierMotzkin.tightUpper_spec _ _ result
  have flag : bound.1 = false := by
    rcases List.mem_cons.mp member with same | member
    · exact congrArg Prod.fst same
    · obtain ⟨b, _, same⟩ := List.mem_map.mp member
      exact (congrArg Prod.fst same).symm
  simp only [upperEndpoint, result, Option.getD_some]
  exact ⟨by simpa [flag] using member, fun q hq => least false q hq⟩

private theorem zeroTerm_eval (term : FourierMotzkin.LinTerm 0) :
    term.eval (Fin.elim0 : Fin 0 → ℝ) = (term.const : ℝ) := by
  obtain ⟨coeff, constant⟩ := term
  cases coeff
  simp [FourierMotzkin.LinTerm.eval, FourierMotzkin.Coeff.dot]

theorem oneDimensional_sat (atoms : List (FourierMotzkin.Atom 1)) (closed : NonStrict atoms) (value : ℝ) :
    FourierMotzkin.allSat atoms (fun _ => value) ↔
      FourierMotzkin.allSat (FourierMotzkin.residuals atoms) (Fin.elim0 : Fin 0 → ℝ) ∧
      (∀ b ∈ FourierMotzkin.lowers atoms, (b.term.const : ℝ) ≤ value) ∧
      (∀ b ∈ FourierMotzkin.uppers atoms, value ≤ (b.term.const : ℝ)) := by
  have env : (fun _ : Fin 1 => value) = FourierMotzkin.envCons value (Fin.elim0 : Fin 0 → ℝ) := by
    funext i
    have index : i = 0 := by apply Fin.ext; omega
    subst i
    rfl
  rw [env]
  constructor
  · intro held
    refine ⟨?_, ?_, ?_⟩
    · intro a member
      obtain ⟨original, member, same⟩ := FourierMotzkin.mem_residuals.mp member
      exact (FourierMotzkin.sat_keep same).mp (held original member)
    · intro b member
      obtain ⟨a, ha, same⟩ := FourierMotzkin.mem_lowers.mp member
      have bound := (FourierMotzkin.sat_lower same).mp (held a ha)
      simpa only [FourierMotzkin.Bound.below, lower_closed atoms closed b member,
        Bool.false_eq_true, if_false, zeroTerm_eval] using bound
    · intro b member
      obtain ⟨a, ha, same⟩ := FourierMotzkin.mem_uppers.mp member
      have bound := (FourierMotzkin.sat_upper same).mp (held a ha)
      simpa only [FourierMotzkin.Bound.above, upper_closed atoms closed b member,
        Bool.false_eq_true, if_false, zeroTerm_eval] using bound
  · rintro ⟨residuals, lower, upper⟩ a member
    cases same : FourierMotzkin.classify a with
    | keep r => exact (FourierMotzkin.sat_keep same).mpr (residuals r (FourierMotzkin.mem_residuals.mpr ⟨a, member, same⟩))
    | lower b =>
      have hb := FourierMotzkin.mem_lowers.mpr ⟨a, member, same⟩
      apply (FourierMotzkin.sat_lower same).mpr
      simpa only [FourierMotzkin.Bound.below, lower_closed atoms closed b hb,
        Bool.false_eq_true, if_false, zeroTerm_eval] using lower b hb
    | upper b =>
      have hb := FourierMotzkin.mem_uppers.mpr ⟨a, member, same⟩
      apply (FourierMotzkin.sat_upper same).mpr
      simpa only [FourierMotzkin.Bound.above, upper_closed atoms closed b hb,
        Bool.false_eq_true, if_false, zeroTerm_eval] using upper b hb

private theorem lowerEndpoint_le (atoms : List (FourierMotzkin.Atom 1)) (value : ℝ)
    (nonnegative : 0 ≤ value) (lower : ∀ b ∈ FourierMotzkin.lowers atoms, (b.term.const : ℝ) ≤ value) :
    (lowerEndpoint atoms : ℝ) ≤ value := by
  rcases List.mem_cons.mp (lowerEndpoint_spec atoms).1 with same | member
  · have equal : lowerEndpoint atoms = 0 := congrArg Prod.snd same
    rw [equal, Rat.cast_zero]
    exact nonnegative
  · obtain ⟨b, member, equal⟩ := List.mem_map.mp member
    have number : b.term.const = lowerEndpoint atoms := congrArg Prod.snd equal
    rw [← number]
    exact lower b member

private theorem le_upperEndpoint (atoms : List (FourierMotzkin.Atom 1)) (value : ℝ)
    (bounded : value ≤ 1) (upper : ∀ b ∈ FourierMotzkin.uppers atoms, value ≤ (b.term.const : ℝ)) :
    value ≤ (upperEndpoint atoms : ℝ) := by
  rcases List.mem_cons.mp (upperEndpoint_spec atoms).1 with same | member
  · have equal : upperEndpoint atoms = 1 := congrArg Prod.snd same
    rw [equal, Rat.cast_one]
    exact bounded
  · obtain ⟨b, member, equal⟩ := List.mem_map.mp member
    have number : b.term.const = upperEndpoint atoms := congrArg Prod.snd equal
    rw [← number]
    exact upper b member

theorem projected_interval {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (possible : (queryValues base event condition).Nonempty) :
    queryValues base event condition = Set.Icc
      (lowerEndpoint (projected base event condition) : ℝ) (upperEndpoint (projected base event condition) : ℝ) := by
  let atoms := projected base event condition
  have closed : NonStrict atoms := projectToOne_closed n _ (scaledAtoms_closed base event condition)
  obtain ⟨witness, witnessMember⟩ := possible
  have feasible := (oneDimensional_sat atoms closed witness).mp ((projected_values base event condition witness).mpr witnessMember)
  ext value
  constructor
  · intro member
    have numerical := (oneDimensional_sat atoms closed value).mp ((projected_values base event condition value).mpr member)
    have unit := queryValues_subset_unit base event condition member
    exact ⟨lowerEndpoint_le atoms value unit.1 numerical.2.1, le_upperEndpoint atoms value unit.2 numerical.2.2⟩
  · rintro ⟨lower, upper⟩
    apply (projected_values base event condition value).mp
    apply (oneDimensional_sat atoms closed value).mpr
    refine ⟨feasible.1, ?_, ?_⟩
    · intro b member
      have bound := (lowerEndpoint_spec atoms).2 b.term.const (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, member, rfl⟩))
      exact (Rat.cast_le.mpr bound).trans lower
    · intro b member
      have bound := (upperEndpoint_spec atoms).2 b.term.const (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, member, rfl⟩))
      exact upper.trans (Rat.cast_le.mpr bound)

/-- A successful query returns exact rational endpoints. Failure means that
no model supports the conditioning event, not a vacuous numerical interval. -/
def queryBoundsRat {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) : Option (ℚ × ℚ) :=
  let atoms := projected base event condition
  if FourierMotzkin.decideSat atoms then some (lowerEndpoint atoms, upperEndpoint atoms) else none

theorem projected_decide_iff {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    FourierMotzkin.decideSat (projected base event condition) = true ↔ (queryValues base event condition).Nonempty := by
  rw [FourierMotzkin.decideSat_iff (R := ℝ)]
  constructor
  · rintro ⟨env, held⟩
    refine ⟨env 0, (projected_values base event condition (env 0)).mp ?_⟩
    have same : env = fun _ => env 0 := by funext i; congr 1; apply Fin.ext; omega
    exact same ▸ held
  · rintro ⟨value, member⟩
    exact ⟨fun _ => value, (projected_values base event condition value).mpr member⟩

theorem queryBoundsRat_none_iff {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    queryBoundsRat base event condition = none ↔
      ¬ ∃ p ∈ models base, 0 < mass p.weight condition := by
  simp only [queryBoundsRat, ite_eq_right_iff, reduceCtorEq, imp_false, projected_decide_iff]
  constructor
  · intro absent ⟨p, member, positive⟩
    exact absent ⟨conditionalValue p event condition, p, member, positive, rfl⟩
  · intro absent ⟨value, p, member, positive, _⟩
    exact absent ⟨p, member, positive⟩

theorem queryBoundsRat_some_iff {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (lower upper : ℚ) :
    queryBoundsRat base event condition = some (lower, upper) ↔
      (queryValues base event condition).Nonempty ∧
      lower = lowerEndpoint (projected base event condition) ∧ upper = upperEndpoint (projected base event condition) := by
  by_cases possible : (queryValues base event condition).Nonempty
  · have decision := (projected_decide_iff base event condition).mpr possible
    simp only [queryBoundsRat, decision, if_true, Option.some.injEq, Prod.mk.injEq]
    exact ⟨fun h => ⟨possible, h.1.symm, h.2.symm⟩, fun h => ⟨h.2.1.symm, h.2.2.symm⟩⟩
  · have decision : FourierMotzkin.decideSat (projected base event condition) = false :=
      Bool.eq_false_iff.mpr (fun h => possible ((projected_decide_iff base event condition).mp h))
    simp only [queryBoundsRat, decision, Bool.false_eq_true, if_false, reduceCtorEq, possible, false_and]

theorem bounds_attained {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    {lower upper : ℚ} (returned : queryBoundsRat base event condition = some (lower, upper)) :
    (0 ≤ lower ∧ lower ≤ upper ∧ upper ≤ 1) ∧
      (∃ p ∈ models base, 0 < mass p.weight condition ∧ conditionalValue p event condition = lower) ∧
      (∃ p ∈ models base, 0 < mass p.weight condition ∧ conditionalValue p event condition = upper) := by
  obtain ⟨possible, rfl, rfl⟩ := (queryBoundsRat_some_iff base event condition lower upper).mp returned
  have interval := projected_interval base event condition possible
  obtain ⟨value, member⟩ := possible
  have ordered : (lowerEndpoint (projected base event condition) : ℝ) ≤ upperEndpoint (projected base event condition) := by
    rw [interval] at member
    exact member.1.trans member.2
  have loMem : (lowerEndpoint (projected base event condition) : ℝ) ∈ queryValues base event condition := by
    rw [interval]
    exact ⟨le_rfl, ordered⟩
  have hiMem : (upperEndpoint (projected base event condition) : ℝ) ∈ queryValues base event condition := by
    rw [interval]
    exact ⟨ordered, le_rfl⟩
  have loUnit := queryValues_subset_unit base event condition loMem
  have hiUnit := queryValues_subset_unit base event condition hiMem
  exact ⟨⟨by exact_mod_cast loUnit.1, by exact_mod_cast ordered, by exact_mod_cast hiUnit.2⟩, loMem, hiMem⟩

/-- Consistency is a query with the certain condition; it distinguishes an
inconsistent base from an unsupported conditional in a consistent base. -/
def isConsistent {n : Nat} (base : KnowledgeBase (Fin n)) : Bool :=
  FourierMotzkin.decideSat (projected base (fun _ => false) (fun _ => true))

theorem isConsistent_correct {n : Nat} (base : KnowledgeBase (Fin n)) :
    isConsistent base = true ↔ Consistent base := by
  rw [isConsistent, projected_decide_iff]
  constructor
  · rintro ⟨_, p, member, _, _⟩
    exact ⟨p, member⟩
  · rintro ⟨p, member⟩
    refine ⟨conditionalValue p (fun _ => false) (fun _ => true), p, member, ?_, rfl⟩
    simp [mass, p.total]

theorem no_bounds_of_inconsistent {n : Nat} (base : KnowledgeBase (Fin n))
    (inconsistent : ¬ Consistent base) (event condition : Event (Fin n)) :
    queryBoundsRat base event condition = none := by
  apply (queryBoundsRat_none_iff base event condition).mpr
  rintro ⟨p, member, _⟩
  exact inconsistent ⟨p, member⟩

theorem bounds_exact_range {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    {lower upper : ℚ} (returned : queryBoundsRat base event condition = some (lower, upper)) :
    queryValues base event condition = Set.Icc (lower : ℝ) (upper : ℝ) := by
  obtain ⟨possible, rfl, rfl⟩ := (queryBoundsRat_some_iff base event condition lower upper).mp returned
  exact projected_interval base event condition possible

/-- Reuse the existing interval carrier after certifying the computed endpoints. -/
noncomputable def queryBounds {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    Option CredalSets.Interval :=
  match returned : queryBoundsRat base event condition with
  | none => none
  | some (lower, upper) => some ⟨lower, upper, Rat.cast_le.mpr (bounds_attained base event condition returned).1.2.1⟩

theorem queryBounds_none_iff {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    queryBounds base event condition = none ↔ ¬ ∃ p ∈ models base, 0 < mass p.weight condition := by
  rw [← queryBoundsRat_none_iff base event condition]
  unfold queryBounds
  split <;> simp_all

/-- The rational ATP answer is the existing lower/upper credal envelope of
posterior observations, with original-model endpoint witnesses supplied above. -/
theorem bounds_eq_credal_envelopes {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    {lower upper : ℚ} (returned : queryBoundsRat base event condition = some (lower, upper)) :
    ProjectiveCredal.lowerEnvelope (posteriorCredalModels base condition) (eventGamble event) = lower ∧
      ProjectiveCredal.upperEnvelope (posteriorCredalModels base condition) (eventGamble event) = upper := by
  have ordered : (lower : ℝ) ≤ upper := Rat.cast_le.mpr (bounds_attained base event condition returned).1.2.1
  simp only [ProjectiveCredal.lowerEnvelope, ProjectiveCredal.upperEnvelope, posterior_values,
    bounds_exact_range base event condition returned]
  exact ⟨csInf_Icc ordered, csSup_Icc ordered⟩

/-- Semantic certificates determine the executable answer, without reducing
the potentially large elimination trace inside each application proof. -/
theorem queryBoundsRat_eq_of_witnesses {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n))
    (lower upper : ℚ) (lowerWitness : (lower : ℝ) ∈ queryValues base event condition)
    (upperWitness : (upper : ℝ) ∈ queryValues base event condition)
    (bounded : queryValues base event condition ⊆ Set.Icc (lower : ℝ) (upper : ℝ)) :
    queryBoundsRat base event condition = some (lower, upper) := by
  let lo := lowerEndpoint (projected base event condition)
  let hi := upperEndpoint (projected base event condition)
  have possible : (queryValues base event condition).Nonempty := ⟨lower, lowerWitness⟩
  have returned : queryBoundsRat base event condition = some (lo, hi) :=
    (queryBoundsRat_some_iff base event condition lo hi).mpr ⟨possible, rfl, rfl⟩
  obtain ⟨_, loAttained, hiAttained⟩ := bounds_attained base event condition returned
  have rangeEq := bounds_exact_range base event condition returned
  have loBound := bounded loAttained
  have hiBound := bounded hiAttained
  rw [rangeEq] at lowerWitness upperWitness
  have loEq : lo = lower := by exact_mod_cast le_antisymm lowerWitness.1 loBound.1
  have hiEq : hi = upper := by exact_mod_cast le_antisymm hiBound.2 upperWitness.2
  simpa only [loEq, hiEq] using returned

end Mettapedia.ProbabilityTheory.ImpreciseProbability.ConditionalConstraintBounds
