import Mettapedia.OSLF.Syntax.BindingTelescope

/-!
# Raw substitution geometry for telescopes

The raw arrow operations are the binding signature's substitutions. Pairing
extends an arbitrary arrow by its newest component; projection and newest
variable recover both components. Their laws and precomposition naturality
are syntactic equalities, before any formation or typing admission.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Telescope

variable {S : Signature} {b k : S.Srt}

def identity (b : S.Srt) (n : Nat) : RawSub S b n n := fun _ var => .var var

/-- First apply the left substitution, then substitute by the right one. -/
def comp {n m p : Nat} (first : RawSub S b n m) (second : RawSub S b m p) : RawSub S b n p :=
  fun s var => bind second (first s var)

@[simp] theorem comp_identity_left {n m : Nat} (substitution : RawSub S b n m) :
    comp (identity b n) substitution = substitution := rfl

@[simp] theorem comp_identity_right {n m : Nat} (substitution : RawSub S b n m) :
    comp substitution (identity b m) = substitution := by
  funext s var
  exact bind_id (substitution s var)

theorem comp_assoc {n m p q : Nat} (first : RawSub S b n m)
    (second : RawSub S b m p) (third : RawSub S b p q) :
    comp (comp first second) third = comp first (comp second third) := by
  funext s var
  exact bind_comp second third (first s var)

@[simp] theorem bind_identity {n : Nat} {s : S.Srt} (term : Term S (scope b n) s) :
    bind (identity b n) term = term := bind_id term

theorem bind_compose {n m p : Nat} (first : RawSub S b n m) (second : RawSub S b m p)
    {s : S.Srt} (term : Term S (scope b n) s) :
    bind second (bind first term) = bind (comp first second) term :=
  bind_comp first second term

/-- The raw projection forgets the newest declaration. -/
def projection (b : S.Srt) (n : Nat) : RawSub S b n (n + 1) := fun _ var => .var (.succ var)

def newest (b : S.Srt) (n : Nat) : RawTm S b (n + 1) := .var .zero

/-- Pair an arbitrary substitution with a term for the new variable. -/
def pair {n m : Nat} (substitution : RawSub S b n m) (term : RawTm S b m) :
    RawSub S b (n + 1) m
  | _, .zero => term
  | s, .succ var => substitution s var

@[simp] theorem pair_newest {n m : Nat} (substitution : RawSub S b n m) (term : RawTm S b m) :
    bind (pair substitution term) (newest b n) = term := rfl

@[simp] theorem pair_older {n m : Nat} (substitution : RawSub S b n m) (term : RawTm S b m)
    {s : S.Srt} (var : Var (scope b n) s) :
    pair substitution term s (.succ var) = substitution s var := rfl

@[simp] theorem projection_pair {n m : Nat} (substitution : RawSub S b n m)
    (term : RawTm S b m) : comp (projection b n) (pair substitution term) = substitution := rfl

/-- All substitutions into an extended source recover from these two components. -/
theorem pair_projection_newest {n m : Nat} (substitution : RawSub S b (n + 1) m) :
    pair (comp (projection b n) substitution) (bind substitution (newest b n)) = substitution := by
  funext s var
  cases var <;> rfl

@[simp] theorem pair_projection_identity (b : S.Srt) (n : Nat) :
    pair (projection b n) (newest b n) = identity b (n + 1) := by
  funext s var
  cases var <;> rfl

/-- Projection acts on syntax by the existing capture-avoiding weakening. -/
theorem bind_projection {n : Nat} {s : S.Srt} (term : Term S (scope b n) s) :
    bind (projection b n) term = weaken term :=
  bind_var_eq_rename (fun _ var => .succ var) term

/-- Weakening a code removes the newest component from its substitution. -/
theorem bind_pair_weaken {n m : Nat} (substitution : RawSub S b n m)
    (term : RawTm S b m) {s : S.Srt} (body : Term S (scope b n) s) :
    bind (pair substitution term) (weaken body) = bind substitution body :=
  bind_rename (fun _ var => .succ var) (pair substitution term) body

/-- Pairing commutes with precomposition, retaining the substituted newest term. -/
theorem pair_precompose {n m p : Nat} (first : RawSub S b n m) (term : RawTm S b m)
    (second : RawSub S b m p) :
    comp (pair first term) second = pair (comp first second) (bind second term) := by
  funext s var
  cases var <;> rfl

/-- The raw decomposition is a product; typed admission later refines its second factor. -/
def split {n m : Nat} (substitution : RawSub S b (n + 1) m) : RawSub S b n m × RawTm S b m :=
  (comp (projection b n) substitution, bind substitution (newest b n))

@[simp] theorem split_pair {n m : Nat} (substitution : RawSub S b n m) (term : RawTm S b m) :
    split (pair substitution term) = (substitution, term) := rfl

@[simp] theorem pair_split {n m : Nat} (substitution : RawSub S b (n + 1) m) :
    pair (split substitution).1 (split substitution).2 = substitution :=
  pair_projection_newest substitution

/-- Both directions retain every ordinary-variable assignment. -/
def pairingEquiv (S : Signature) (b : S.Srt) (n m : Nat) :
    RawSub S b (n + 1) m ≃ RawSub S b n m × RawTm S b m where
  toFun := split
  invFun := fun components => pair components.1 components.2
  left_inv := pair_split
  right_inv := fun _ => rfl

theorem pairing_precompose {n m p : Nat} (first : RawSub S b (n + 1) m)
    (second : RawSub S b m p) :
    pairingEquiv S b n p (comp first second) =
      (comp (pairingEquiv S b n m first).1 second,
        bind second (pairingEquiv S b n m first).2) :=
  Prod.ext (comp_assoc (projection b n) first second).symm
    (bind_comp first second (newest b n)).symm

theorem pairing_symm_precompose {n m p : Nat} (substitution : RawSub S b n m)
    (term : RawTm S b m) (next : RawSub S b m p) :
    comp ((pairingEquiv S b n m).symm (substitution, term)) next =
      (pairingEquiv S b n p).symm (comp substitution next, bind next term) :=
  pair_precompose substitution term next

/-- The binder extension is the existing signature lift. -/
def lift {n m : Nat} (substitution : RawSub S b n m) : RawSub S b (n + 1) (m + 1) :=
  liftSub substitution [b]

@[simp] theorem lift_newest {n m : Nat} (substitution : RawSub S b n m) :
    bind (lift substitution) (newest b n) = newest b m := rfl

@[simp] theorem lift_older {n m : Nat} (substitution : RawSub S b n m)
    {s : S.Srt} (var : Var (scope b n) s) :
    lift substitution s (.succ var) = weaken (substitution s var) := rfl

@[simp] theorem lift_identity (b : S.Srt) (n : Nat) :
    lift (identity b n) = identity b (n + 1) := liftSub_var [b]

theorem lift_comp {n m p : Nat} (first : RawSub S b n m) (second : RawSub S b m p) :
    comp (lift first) (lift second) = lift (comp first second) := liftSub_comp first second [b]

theorem bind_lift_weaken {n m : Nat} (substitution : RawSub S b n m)
    {s : S.Srt} (term : Term S (scope b n) s) :
    bind (lift substitution) (weaken term) = weaken (bind substitution term) :=
  (bind_rename (fun _ var => .succ var) (lift substitution) term).trans
    (rename_bind substitution (fun _ var => .succ var) term).symm

theorem lift_pair {n m : Nat} (substitution : RawSub S b n m) :
    lift substitution = pair (comp substitution (projection b m)) (newest b m) := by
  funext s var
  cases var with
  | zero => rfl
  | succ old => exact (bind_projection (substitution s old)).symm

theorem projection_lift {n m : Nat} (substitution : RawSub S b n m) :
    comp (projection b n) (lift substitution) = comp substitution (projection b m) := by
  funext s var
  exact (bind_projection (substitution s var)).symm

/-- Instantiation is the special case pairing the identity with one term. -/
theorem pair_identity_eq_extend {n : Nat} (term : RawTm S b n) :
    pair (identity b n) term = extend term := by
  funext s var
  cases var <;> rfl

theorem bind_pair_identity {n : Nat} (term : RawTm S b n)
    {s : S.Srt} (body : Term S (scope b (n + 1)) s) :
    bind (pair (identity b n) term) body = inst body term := by
  rw [pair_identity_eq_extend]
  rfl

/-- The newest declaration's stored code is reindexed by the older components. -/
theorem lookup_pair_newest {n m : Nat} (context : RawContext S b k n) (code : RawTy S b k n)
    (substitution : RawSub S b n m) (term : RawTm S b m) :
    bind (pair substitution term) (lookup (.snoc context code) .zero) = bind substitution code :=
  bind_pair_weaken substitution term code

theorem lookup_pair_older {n m : Nat} (context : RawContext S b k n) (code : RawTy S b k n)
    (var : Var (scope b n) b) (substitution : RawSub S b n m) (term : RawTm S b m) :
    bind (pair substitution term) (lookup (.snoc context code) (.succ var)) =
      bind substitution (lookup context var) := bind_pair_weaken substitution term (lookup context var)

theorem lookup_projection {n : Nat} (context : RawContext S b k n) (code : RawTy S b k n)
    (var : Var (scope b n) b) :
    lookup (.snoc context code) (.succ var) = bind (projection b n) (lookup context var) :=
  (bind_projection (lookup context var)).symm

theorem lookup_lift_newest {n m : Nat} (context : RawContext S b k n) (code : RawTy S b k n)
    (substitution : RawSub S b n m) :
    bind (lift substitution) (lookup (.snoc context code) .zero) = weaken (bind substitution code) :=
  bind_lift_weaken substitution code

theorem lookup_lift_older {n m : Nat} (context : RawContext S b k n) (code : RawTy S b k n)
    (var : Var (scope b n) b) (substitution : RawSub S b n m) :
    bind (lift substitution) (lookup (.snoc context code) (.succ var)) =
      weaken (bind substitution (lookup context var)) := bind_lift_weaken substitution (lookup context var)

#print axioms pairingEquiv
#print axioms pairing_precompose
#print axioms lift_comp
#print axioms bind_lift_weaken
#print axioms lookup_pair_newest
#print axioms lookup_lift_older

end Mettapedia.OSLF.Binding.Telescope
