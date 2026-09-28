import Mettapedia.Logic.Unification.ListSpliceTerms
import Mettapedia.Logic.Unification.ListPrefixMeeting
import Mathlib.Data.List.OfFn

/-!
# List splices and first-order cons terms

This first-order encoding uses distinct nil, cons and expression constructors. Raw splice
syntax is intentionally not injective: `[a | [b]]` and `[a b]` denote the same
list. This encoding is injective exactly modulo the independently generated
splice congruence, and is injective outright on normalized terms. Substitution
commutes with encoding, so list constraints have the same solutions as their
first-order translations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Unification.ListSplice

namespace Encoding


variable {Leaf Var : Type}

def encode : Term Leaf Var → ListPrefixMeeting.Tm Leaf Var
  | .atom a => .const (.atom a)
  | .var v => .var v
  | .expr xs => ListPrefixMeeting.expr (xs.map encode)
  | .list xs => ListPrefixMeeting.spine (xs.map encode) none
  | .rest xs tail => ListPrefixMeeting.spine (xs.map encode) (some (encode tail))

def decode : ListPrefixMeeting.Tm Leaf Var → Term Leaf Var
  | .var v => .var v
  | .const (.atom a) => .atom a
  | .const .nil => .list []
  | .app .cons children => splice [decode (children 0)] (decode (children 1))
  | .app (.expr _) children => .expr (List.ofFn fun i => decode (children i))

@[simp] theorem decode_nil : decode (ListPrefixMeeting.nil : ListPrefixMeeting.Tm Leaf Var) = .list [] := rfl

@[simp] theorem decode_cons (head tail : ListPrefixMeeting.Tm Leaf Var) :
    decode (ListPrefixMeeting.cons head tail) = splice [decode head] (decode tail) := by
  simp [ListPrefixMeeting.cons, decode]

@[simp] theorem decode_expr (xs : List (ListPrefixMeeting.Tm Leaf Var)) :
    decode (ListPrefixMeeting.expr xs) = .expr (xs.map decode) := by
  simp [ListPrefixMeeting.expr, decode]

theorem decode_spine (xs : List (ListPrefixMeeting.Tm Leaf Var)) (rest : Option (ListPrefixMeeting.Tm Leaf Var)) :
    decode (ListPrefixMeeting.spine xs rest) = splice (xs.map decode) (decode (ListPrefixMeeting.close rest)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [ListPrefixMeeting.spine_cons, decode_cons, List.map_cons, ih]
    exact (splice_append [decode x] (xs.map decode) _).symm

/-- Decoding recovers the normal form of the authored term, not a reconstructed target. -/
theorem decode_encode (t : Term Leaf Var) : decode (encode t) = normalize t := by
  match t with
  | .atom _ => simp [encode, decode, normalize]
  | .var _ => simp [encode, decode, normalize]
  | .expr xs =>
    simp only [encode, decode_expr, normalize, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => decode_encode x
  | .list xs =>
    simp only [encode, decode_spine, ListPrefixMeeting.close_none, decode_nil, splice_list,
      List.append_nil, normalize, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => decode_encode x
  | .rest xs tail =>
    simp only [encode, decode_spine, ListPrefixMeeting.close_some, normalize, List.map_map,
      decode_encode tail]
    congr 1
    exact List.map_congr_left fun x _ => decode_encode x
termination_by sizeOf t

theorem spine_append (xs ys : List (ListPrefixMeeting.Tm Leaf Var)) (rest : Option (ListPrefixMeeting.Tm Leaf Var)) :
    ListPrefixMeeting.spine (xs ++ ys) rest = ListPrefixMeeting.spine xs (some (ListPrefixMeeting.spine ys rest)) := by
  simp [ListPrefixMeeting.spine, List.foldr_append]

theorem encode_splice (xs : List (Term Leaf Var)) (tail : Term Leaf Var) :
    encode (splice xs tail) = ListPrefixMeeting.spine (xs.map encode) (some (encode tail)) := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases tail with
    | list ys => simp only [splice_list, encode, List.map_append, spine_append]
    | rest ys tail => simp only [splice_rest, encode, List.map_append, spine_append]
    | atom a => simp [splice, encode]
    | var v => simp [splice, encode]
    | expr ys => simp [splice, encode]

/-- The cons representation identifies just the stipulated splice equations. -/
theorem encode_normalize (t : Term Leaf Var) : encode (normalize t) = encode t := by
  match t with
  | .atom _ => simp [normalize]
  | .var _ => simp [normalize]
  | .expr xs =>
    simp only [normalize, encode, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => encode_normalize x
  | .list xs =>
    simp only [normalize, encode, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => encode_normalize x
  | .rest xs tail =>
    simp only [normalize, encode_splice, encode, List.map_map, encode_normalize tail]
    congr 1
    exact List.map_congr_left fun x _ => encode_normalize x
termination_by sizeOf t

theorem encode_eq_iff (s t : Term Leaf Var) : encode s = encode t ↔ Equivalent s t := by
  rw [equivalent_iff_normalize_eq]
  constructor
  · intro h
    simpa only [decode_encode] using congrArg decode h
  · intro h
    rw [← encode_normalize s, ← encode_normalize t, h]

theorem encode_injective_on_normal_forms {s t : Term Leaf Var}
    (hs : normalize s = s) (ht : normalize t = t) (h : encode s = encode t) : s = t :=
  normal_forms_unique hs ht ((encode_eq_iff s t).mp h)

/-- All first-order terms in the list signature decode, including improper tails. -/
theorem encode_decode (t : ListPrefixMeeting.Tm Leaf Var) : encode (decode t) = t := by
  induction t with
  | var v => simp [decode, encode]
  | const c => cases c <;> simp [decode, encode, ListPrefixMeeting.nil]
  | app f children ih =>
    cases f with
    | cons =>
      simp only [decode, encode_splice, List.map_cons, List.map_nil,
        ListPrefixMeeting.spine_cons, ListPrefixMeeting.spine_nil,
        ListPrefixMeeting.close_some, ih]
      unfold ListPrefixMeeting.cons
      congr 1
      funext i
      by_cases zero : i = 0
      · simp [zero]
      · have one : i = 1 := Fin.ext (by omega)
        simp [one]
    | expr n =>
      have mapped : (List.ofFn fun i => decode (children i)).map encode =
          List.ofFn children := by
        rw [List.map_ofFn]
        congr 1
        funext i
        exact ih i
      simp only [decode, encode, mapped]
      exact congrArg
        (fun p : Σ n, Fin n → ListPrefixMeeting.Tm Leaf Var =>
          @Mettapedia.Logic.LP.Term.app (ListPrefixMeeting.signature Leaf Var)
            (.expr p.1) p.2)
        (List.equivSigmaTuple.apply_symm_apply ⟨n, children⟩)

theorem decode_normal (t : ListPrefixMeeting.Tm Leaf Var) :
    normalize (decode t) = decode t := by
  rw [← decode_encode, encode_decode]

def encodeSubst (σ : Var → Term Leaf Var) : ListPrefixMeeting.Substitution Leaf Var :=
  fun v => encode (σ v)

def decodeSubst (θ : ListPrefixMeeting.Substitution Leaf Var) : Var → Term Leaf Var :=
  fun v => decode (θ v)

theorem encodeSubst_decodeSubst (θ : ListPrefixMeeting.Substitution Leaf Var) :
    encodeSubst (decodeSubst θ) = θ := by
  funext v
  exact encode_decode (θ v)

/-- Raw substitution followed by translation is first-order substitution. -/
theorem encode_subst (σ : Var → Term Leaf Var) (t : Term Leaf Var) :
    encode (subst σ t) = (encodeSubst σ).applyTerm (encode t) := by
  match t with
  | .atom _ => simp [subst, encode]
  | .var _ => simp [subst, encode, encodeSubst]
  | .expr xs =>
    simp only [subst, encode, ListPrefixMeeting.apply_expr, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => encode_subst σ x
  | .list xs =>
    simp only [subst, encode, ListPrefixMeeting.apply_spine, Option.map_none, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => encode_subst σ x
  | .rest xs tail =>
    simp only [subst, encode, ListPrefixMeeting.apply_spine, Option.map_some, List.map_map,
      encode_subst σ tail]
    congr 1
    exact List.map_congr_left fun x _ => encode_subst σ x
termination_by sizeOf t

/-- Solutions, including repeated variables and open tails, are preserved and reflected. -/
theorem solution_iff (σ : Var → Term Leaf Var) (s t : Term Leaf Var) :
    Equivalent (subst σ s) (subst σ t) ↔
      (encodeSubst σ).applyTerm (encode s) = (encodeSubst σ).applyTerm (encode t) := by
  rw [← encode_eq_iff, encode_subst, encode_subst]

/-- Instantiation order for source substitutions is modulo the declared splice laws. -/
def MoreGeneral (σ τ : Var → Term Leaf Var) : Prop :=
  ∃ δ : Var → Term Leaf Var, ∀ v, Equivalent (τ v) (subst δ (σ v))

/-- The translation preserves and reflects factorization, not a particular MGU name. -/
theorem moreGeneral_iff (σ τ : Var → Term Leaf Var) :
    MoreGeneral σ τ ↔ (encodeSubst σ).moreGeneral (encodeSubst τ) := by
  constructor
  · rintro ⟨δ, h⟩
    refine ⟨encodeSubst δ, ?_⟩
    intro v
    simpa only [encodeSubst, encode_subst] using
      (encode_eq_iff _ _).mpr (h v)
  · rintro ⟨θ, h⟩
    refine ⟨decodeSubst θ, fun v => ?_⟩
    apply (encode_eq_iff _ _).mp
    rw [encode_subst, encodeSubst_decodeSubst]
    exact h v

section Solver

variable [DecidableEq Leaf] [DecidableEq Var]

/-- Solve a source equation via the existing total first-order unifier. This
is a reference solver, not a claim about a native contextual binding store. -/
def solve (s t : Term Leaf Var) : Option (Var → Term Leaf Var) :=
  (Mettapedia.Logic.LP.unifyTotal [(encode s, encode t)]).map decodeSubst

theorem solve_sound (s t : Term Leaf Var) (σ : Var → Term Leaf Var)
    (accepted : solve s t = some σ) : Equivalent (subst σ s) (subst σ t) := by
  unfold solve at accepted
  obtain ⟨θ, raw, rfl⟩ := Option.map_eq_some_iff.mp accepted
  apply (solution_iff _ _ _).mpr
  rw [encodeSubst_decodeSubst]
  exact Mettapedia.Logic.LP.unifyTotal_sound [(encode s, encode t)] θ raw
    (encode s, encode t) (by simp)

/-- Every solution factors through the translated MGU modulo splice equations. -/
theorem solve_mgu (s t : Term Leaf Var) (σ : Var → Term Leaf Var)
    (accepted : solve s t = some σ) (candidate : Var → Term Leaf Var)
    (solved : Equivalent (subst candidate s) (subst candidate t)) :
    MoreGeneral σ candidate := by
  unfold solve at accepted
  obtain ⟨θ, raw, rfl⟩ := Option.map_eq_some_iff.mp accepted
  apply (moreGeneral_iff _ _).mpr
  rw [encodeSubst_decodeSubst]
  apply Mettapedia.Logic.LP.unifyTotal_mgu _ θ raw (encodeSubst candidate)
  simpa [Mettapedia.Logic.LP.Unifies] using (solution_iff _ _ _).mp solved

theorem solve_complete (s t : Term Leaf Var)
    (solvable : ∃ σ : Var → Term Leaf Var, Equivalent (subst σ s) (subst σ t)) :
    ∃ σ, solve s t = some σ := by
  obtain ⟨candidate, solved⟩ := solvable
  have encoded : Mettapedia.Logic.LP.Unifies (encodeSubst candidate)
      [(encode s, encode t)] := by
    simpa [Mettapedia.Logic.LP.Unifies] using (solution_iff _ _ _).mp solved
  obtain ⟨θ, accepted⟩ := Mettapedia.Logic.LP.unifyTotal_complete ⟨_, encoded⟩
  exact ⟨decodeSubst θ, by simp [solve, accepted]⟩

theorem solve_none_iff (s t : Term Leaf Var) : solve s t = none ↔
    ¬∃ σ : Var → Term Leaf Var, Equivalent (subst σ s) (subst σ t) := by
  constructor
  · intro rejected solvable
    obtain ⟨σ, accepted⟩ := solve_complete s t solvable
    rw [rejected] at accepted
    cases accepted
  · intro impossible
    cases result : solve s t with
    | none => rfl
    | some σ => exact (impossible ⟨σ, solve_sound s t σ result⟩).elim

end Solver

example : encode (Term.rest [.atom 1] (.list [.atom 2]) : Term Nat Nat) =
    encode (.list [.atom 1, .atom 2]) := by simp [encode, ListPrefixMeeting.spine]

example : encode (Term.list [] : Term Nat Nat) ≠ encode (.expr []) := by
  simpa only [encode, List.map_nil, ListPrefixMeeting.spine_nil,
    ListPrefixMeeting.close_none] using
    (ListPrefixMeeting.nil_ne_expr ([] : List (ListPrefixMeeting.Tm Nat Nat)))

example : normalize (Term.rest [.atom 1] (.atom 2) : Term Nat Nat) =
    .rest [.atom 1] (.atom 2) := by simp [normalize, splice]

example : normalize (Term.rest [] (.atom 2) : Term Nat Nat) = .atom 2 := by
  simp [normalize]

example : solve (Term.var 0 : Term Nat Nat) (.rest [.atom 1] (.var 0)) = none := by
  rw [solve_none_iff]
  rintro ⟨σ, h⟩
  apply ListPrefixMeeting.occurs_rest_unsatisfiable
    (Leaf := Nat) (Var := Nat) 0 (.const (.atom 1))
  refine ⟨encodeSubst σ, ?_⟩
  simpa only [encode, List.map_cons, List.map_nil] using (solution_iff _ _ _).mp h

example : solve (Term.rest [.var 0, .var 0] (.var 1) : Term Nat Nat)
    (.list [.atom 1, .atom 2, .atom 3]) = none := by
  rw [solve_none_iff]
  rintro ⟨σ, h⟩
  apply ListPrefixMeeting.repeated_head_unsatisfiable
    (Leaf := Nat) (Var := Nat) 0 (.var 1) 1 2 (by decide) [.const (.atom 3)]
  refine ⟨encodeSubst σ, ?_⟩
  simpa only [encode, List.map_cons, List.map_nil] using (solution_iff _ _ _).mp h

example : Equivalent
    (subst (fun v : Nat => if v = 0 then Term.atom 1 else Term.list [.atom 2])
      (.rest [.var 0] (.var 1)))
    (.list [.atom 1, .atom 2] : Term Nat Nat) := by
  apply (equivalent_iff_normalize_eq _ _).mpr
  simp [subst, normalize]

#print axioms encode_eq_iff
#print axioms encode_decode
#print axioms moreGeneral_iff
#print axioms solve_sound
#print axioms solve_mgu
#print axioms solve_complete
#print axioms solve_none_iff

end Encoding
end Mettapedia.Logic.Unification.ListSplice
