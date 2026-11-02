import Mettapedia.Logic.BDD.Operations
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Existential projection of a trailing BDD variable block

Source variables precede auxiliary variables. Source nodes are retained with
the existing reduced-node constructor; auxiliary nodes are combined with the
existing Boolean OR operation. Correctness requires the ordered BDD invariant:
an arbitrary tree may test the same eliminated variable inconsistently along
one path. The result has only the source-variable carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.Projection

def projectAux {n k : Nat} : BDD (n+k) → BDD n
  | .zero => .zero
  | .one => .one
  | .node v lo hi =>
      if source : v.val < n then
        mk ⟨v.val, source⟩ (projectAux lo) (projectAux hi)
      else apply (· || ·) (projectAux lo) (projectAux hi)

private theorem tail_terminal {n k : Nat} (f : BDD (n+k)) {bound : Fin (n+k)}
    (ordered : f.Ordered (some bound)) (beyond : n ≤ bound.val) :
    projectAux f = .zero ∨ projectAux f = .one := by
  induction f generalizing bound with
  | zero => exact Or.inl rfl
  | one => exact Or.inr rfl
  | node v lo hi ihlo ihhi =>
    cases ordered with
    | node greater hlo hhi _ =>
      have greaterBound := greater bound rfl
      have beyondVariable : n ≤ v.val := by omega
      have notSource : ¬ v.val < n := by omega
      simp only [projectAux, dif_neg notSource]
      rcases ihlo hlo beyondVariable with hl | hl <;>
        rcases ihhi hhi beyondVariable with hh | hh <;> simp [hl, hh, apply]

theorem projectAux_ordered {n k : Nat} (f : BDD (n+k)) (bound : Option (Fin n))
    (ordered : f.Ordered (bound.map (Fin.castAdd k))) : (projectAux f).Ordered bound := by
  induction f generalizing bound with
  | zero => exact .zero
  | one => exact .one
  | node v lo hi ihlo ihhi =>
    cases ordered with
    | node greater hlo hhi _ =>
      by_cases source : v.val < n
      · let retained : Fin n := ⟨v.val, source⟩
        have same : Fin.castAdd k retained = v := Fin.ext rfl
        rw [projectAux, dif_pos source]
        apply mk_ordered
        · intro b hb
          have order := greater (Fin.castAdd k b) (by simp [hb])
          exact order
        · exact ihlo (some retained) (by simpa only [Option.map_some, same] using hlo)
        · exact ihhi (some retained) (by simpa only [Option.map_some, same] using hhi)
      · rw [projectAux, dif_neg source]
        rcases tail_terminal lo hlo (by omega) with hl | hl <;>
          rcases tail_terminal hi hhi (by omega) with hh | hh <;>
          simp only [hl, hh, apply, Bool.or_false, Bool.or_true, if_true]
        all_goals first | exact .zero | exact .one

private theorem update_auxiliary {n k : Nat} (input : Fin n → Bool) (auxiliary : Fin k → Bool)
    (index : Fin k) (value : Bool) :
    (Fin.addCases input (Function.update auxiliary index value) : Fin (n+k) → Bool) =
      Function.update (Fin.addCases input auxiliary : Fin (n+k) → Bool) (Fin.natAdd n index) value := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have different : Fin.castAdd k j ≠ Fin.natAdd n index := by
      intro same
      have values := congrArg Fin.val same
      simp only [Fin.val_castAdd, Fin.val_natAdd] at values
      omega
    simp [different]
  · intro j
    by_cases same : j = index
    · subst j
      simp
    · have different : Fin.natAdd n j ≠ Fin.natAdd n index := by
        intro equal
        apply same
        exact Fin.ext (by have h := congrArg Fin.val equal; simp only [Fin.val_natAdd] at h; omega)
      simp [same, different]

/-- Ordered auxiliary tests can be forgotten existentially, with one shared
assignment witnessing all retained occurrences. -/
theorem projectAux_eval {n k : Nat} (f : BDD (n+k)) {bound : Option (Fin (n+k))}
    (ordered : f.Ordered bound) (input : Fin n → Bool) :
    (projectAux f).eval input = true ↔ ∃ auxiliary : Fin k → Bool, f.eval (Fin.addCases input auxiliary) = true := by
  induction f generalizing bound with
  | zero => simp [projectAux]
  | one => simp [projectAux]
  | node v lo hi ihlo ihhi =>
    cases ordered with
    | node greater hlo hhi _ =>
      by_cases source : v.val < n
      · let retained : Fin n := ⟨v.val, source⟩
        have same : v = Fin.castAdd k retained := Fin.ext rfl
        rw [projectAux, dif_pos source, mk_eval]
        have evaluate (auxiliary : Fin k → Bool) :
            (Fin.addCases input auxiliary : Fin (n+k) → Bool) v = input retained := by
          rw [same]
          simp
        simp only [BDD.eval, evaluate]
        cases value : input retained <;> simp only [Bool.false_eq_true, if_false, if_true]
        · exact ihlo hlo
        · exact ihhi hhi
      · let index : Fin k := ⟨v.val - n, by omega⟩
        have same : v = Fin.natAdd n index := Fin.ext (by dsimp [index]; omega)
        rw [projectAux, dif_neg source, apply_eval, Bool.or_eq_true, ihlo hlo, ihhi hhi]
        constructor
        · rintro (⟨auxiliary, held⟩ | ⟨auxiliary, held⟩)
          · refine ⟨Function.update auxiliary index false, ?_⟩
            rw [update_auxiliary, ← same, BDD.eval, Function.update_self]
            simp only [Bool.false_eq_true, if_false]
            rw [BDD.eval_independent lo hlo (Fin.addCases input auxiliary) v le_rfl false]
            exact held
          · refine ⟨Function.update auxiliary index true, ?_⟩
            rw [update_auxiliary, ← same, BDD.eval, Function.update_self]
            simp only [if_true]
            rw [BDD.eval_independent hi hhi (Fin.addCases input auxiliary) v le_rfl true]
            exact held
        · rintro ⟨auxiliary, held⟩
          simp only [BDD.eval] at held
          split at held
          · exact Or.inr ⟨auxiliary, held⟩
          · exact Or.inl ⟨auxiliary, held⟩

namespace Controls

def repeatedAuxiliary : BDD 1 := .node 0 (.node 0 .zero .one) .zero

theorem repeated_auxiliary_unsatisfiable : ∀ world, repeatedAuxiliary.eval world = false := by
  intro world
  cases h : world 0 <;> simp [repeatedAuxiliary, BDD.eval, h]

/-- Without ordering, the two OR branches can demand contradictory values of one variable. -/
theorem unordered_projection_is_wrong :
    (projectAux (n := 0) (k := 1) repeatedAuxiliary).eval Fin.elim0 = true ∧
      ¬ repeatedAuxiliary.Ordered none := by
  constructor
  · simp [projectAux, repeatedAuxiliary, apply]
  · intro ordered
    obtain ⟨auxiliary, held⟩ :=
      (projectAux_eval (n := 0) (k := 1) repeatedAuxiliary ordered Fin.elim0).mp (by simp [projectAux, repeatedAuxiliary, apply])
    rw [repeated_auxiliary_unsatisfiable] at held
    exact Bool.noConfusion held

end Controls

end Mettapedia.Logic.BDDCore.Projection
