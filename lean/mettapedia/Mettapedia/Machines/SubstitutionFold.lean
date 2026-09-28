/-!
# Applying a substitution on an explicit stack

Applying a substitution to a term is a fold over the term.  A variable is
replaced by the image of the value it is bound to, or read as it stands when it
is unbound.  An expression is replaced by the expression of its children's
images.  The runtime memoises variables' images and cuts a binding cycle at a
variable met again on its own binding path.  Here both are carried by an
abstract state `S` and an abstract path `P`, which the variable step reads and
extends.  A term that cannot change (the runtime's has-variables flag) is its
own image.

`Fold` is the recursive specification, as a recursive function computes it.
The runtime runs it on an explicit stack instead (`Step`).  The stack holds
pending variables, whose images are stored once found, and pending expressions,
whose remaining children wait.

* `fold_runs`: from any stack, the machine reaches the image `Fold` gives,
  with that stack unchanged.
* `run_unique`: the machine is deterministic (`step_deterministic`), so from
  the empty stack its only final configuration is that image.

A term nested to any depth, or a binding chain of any length, is therefore
applied with its pending work on the heap: the C stack stays constant.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SubstitutionFold

universe u

/-- Terms: variables, leaves, and expressions of terms. -/
inductive Term (V L : Type u) : Type u where
  | var : V → Term V L
  | leaf : L → Term V L
  | expr : List (Term V L) → Term V L

/-- What the variable step makes of a variable read in scope `c` on path `p`
from state `s`.  Either its image and the state after it (a memoised image, a
variable met again on its own path, an unbound variable's reading).  Or the
value it is bound to, with the key its image is stored under and the scope,
path and state that value is read in.  Or a failure, which the runtime
reports for the whole application. -/
inductive Outcome (V L K C P S : Type u) : Type u where
  | image (r : Term V L) (s : S)
  | bound (k : K) (t : Term V L) (c : C) (p : P) (s : S)
  | failed

/-- A substitution as the fold sees it: the variable step, the memo's store,
and which terms may change (any predicate; the runtime uses its has-variables
flag). -/
structure Subst (V L K C P S : Type u) where
  step : C → P → S → V → Outcome V L K C P S
  store : S → K → Term V L → S
  hasVars : Term V L → Bool

variable {V L K C P S : Type u} (σ : Subst V L K C P S)

mutual
/-- The recursive fold: term `t`, read in scope `c` on path `p` from state `s`,
has image `r` and leaves state `s'`. -/
inductive Fold : C → P → S → Term V L → Term V L → S → Prop
  | fixed {c p s t} : σ.hasVars t = false → Fold c p s t t s
  | leaf {c p s l} : σ.hasVars (.leaf l) = true → Fold c p s (.leaf l) (.leaf l) s
  | image {c p s v r s'} :
      σ.hasVars (.var v) = true → σ.step c p s v = .image r s' →
      Fold c p s (.var v) r s'
  | bound {c p s v k t c' p' s₁ r s₂} :
      σ.hasVars (.var v) = true → σ.step c p s v = .bound k t c' p' s₁ →
      Fold c' p' s₁ t r s₂ → Fold c p s (.var v) r (σ.store s₂ k r)
  | expr {c p s ts rs s'} :
      σ.hasVars (.expr ts) = true → Folds c p s ts rs s' →
      Fold c p s (.expr ts) (.expr rs) s'

/-- The children of an expression, left to right, each read in the
expression's scope and path, the state threaded through. -/
inductive Folds : C → P → S → List (Term V L) → List (Term V L) → S → Prop
  | nil {c p s} : Folds c p s [] [] s
  | cons {c p s t ts r rs s₁ s₂} :
      Fold c p s t r s₁ → Folds c p s₁ ts rs s₂ → Folds c p s (t :: ts) (r :: rs) s₂
end

/-- Pending work: a variable whose image is stored under a key once found, or
an expression with the images of its children so far (latest first) and the
children still to read. -/
inductive Frame (V L K C P : Type u) : Type u where
  | var (k : K)
  | expr (c : C) (p : P) (done : List (Term V L)) (rest : List (Term V L))

/-- The machine: descending into a term, or ascending with an image. -/
inductive Config (V L K C P S : Type u) : Type u where
  | descend (c : C) (p : P) (t : Term V L) (stack : List (Frame V L K C P)) (s : S)
  | ascend (r : Term V L) (stack : List (Frame V L K C P)) (s : S)

/-- One step of the machine. -/
inductive Step : Config V L K C P S → Config V L K C P S → Prop
  | fixed {c p t stack s} :
      σ.hasVars t = false → Step (.descend c p t stack s) (.ascend t stack s)
  | leaf {c p l stack s} :
      σ.hasVars (.leaf l) = true →
      Step (.descend c p (.leaf l) stack s) (.ascend (.leaf l) stack s)
  | image {c p v stack s r s'} :
      σ.hasVars (.var v) = true → σ.step c p s v = .image r s' →
      Step (.descend c p (.var v) stack s) (.ascend r stack s')
  | bound {c p v stack s k t c' p' s₁} :
      σ.hasVars (.var v) = true → σ.step c p s v = .bound k t c' p' s₁ →
      Step (.descend c p (.var v) stack s) (.descend c' p' t (.var k :: stack) s₁)
  | empty {c p stack s} :
      σ.hasVars (.expr []) = true →
      Step (.descend c p (.expr []) stack s) (.ascend (.expr []) stack s)
  | enter {c p u us stack s} :
      σ.hasVars (.expr (u :: us)) = true →
      Step (.descend c p (.expr (u :: us)) stack s)
        (.descend c p u (.expr c p [] us :: stack) s)
  | store {r k stack s} :
      Step (.ascend r (.var k :: stack) s) (.ascend r stack (σ.store s k r))
  | next {r c p done u us stack s} :
      Step (.ascend r (.expr c p done (u :: us) :: stack) s)
        (.descend c p u (.expr c p (r :: done) us :: stack) s)
  | close {r c p done stack s} :
      Step (.ascend r (.expr c p done [] :: stack) s)
        (.ascend (.expr (r :: done).reverse) stack s)

/-- Runs of the machine. -/
inductive Steps : Config V L K C P S → Config V L K C P S → Prop
  | refl {x} : Steps x x
  | head {x y z} : Step σ x y → Steps y z → Steps x z

variable {σ}

theorem Steps.single {x y : Config V L K C P S} (h : Step σ x y) : Steps σ x y :=
  .head h .refl

theorem Steps.trans {x y z : Config V L K C P S} :
    Steps σ x y → Steps σ y z → Steps σ x z := by
  intro hxy hyz
  induction hxy with
  | refl => exact hyz
  | head h _ ih => exact .head h (ih hyz)

/-- Where the machine stands inside a pending expression with images `done`
(latest first) and children `ts` still to read: descending into the next
child, or closing the expression. -/
def resume (c : C) (p : P) (done : List (Term V L)) :
    List (Term V L) → List (Frame V L K C P) → S → Config V L K C P S
  | u :: us, stack, s => .descend c p u (.expr c p done us :: stack) s
  | [], stack, s => .ascend (.expr done.reverse) stack s

/-- Entering an expression resumes it with no image yet. -/
theorem enter_resume {c : C} {p : P} {ts : List (Term V L)}
    {stack : List (Frame V L K C P)} {s : S} (hv : σ.hasVars (.expr ts) = true) :
    Step σ (.descend c p (.expr ts) stack s) (resume c p [] ts stack s) := by
  cases ts with
  | nil => exact .empty hv
  | cons u us => exact .enter hv

/-- A child's image resumes its expression with that image. -/
theorem ascend_resume {r : Term V L} {c : C} {p : P} {done ts : List (Term V L)}
    {stack : List (Frame V L K C P)} {s : S} :
    Step σ (.ascend r (.expr c p done ts :: stack) s) (resume c p (r :: done) ts stack s) := by
  cases ts with
  | nil => exact .close
  | cons u us => exact .next

/-- The machine reaches, from any stack, the image the recursive fold gives.
Inside a pending expression it reads the remaining children and closes the
expression with every image in order. -/
theorem fold_runs {c : C} {p : P} {s s' : S} {t r : Term V L}
    (h : Fold σ c p s t r s') (stack : List (Frame V L K C P)) :
    Steps σ (.descend c p t stack s) (.ascend r stack s') := by
  refine Fold.rec
    (motive_1 := fun c p s t r s' _ => ∀ stack : List (Frame V L K C P),
      Steps σ (.descend c p t stack s) (.ascend r stack s'))
    (motive_2 := fun c p s ts rs s' _ =>
      ∀ (stack : List (Frame V L K C P)) (done : List (Term V L)),
        Steps σ (resume c p done ts stack s)
          (.ascend (.expr (done.reverse ++ rs)) stack s'))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h stack
  · intro c p s t hv stack
    exact .single (.fixed hv)
  · intro c p s l hv stack
    exact .single (.leaf hv)
  · intro c p s v r s' hv hs stack
    exact .single (.image hv hs)
  · intro c p s v k t c' p' s₁ r s₂ hv hs _ ih stack
    exact .head (.bound hv hs) ((ih _).trans (.single .store))
  · intro c p s ts rs s' hv _ ih stack
    have hrun := ih stack []
    simp only [List.reverse_nil, List.nil_append] at hrun
    exact .head (enter_resume hv) hrun
  · intro c p s stack done
    simp only [List.append_nil]
    exact .refl
  · intro c p s t ts r rs s₁ s₂ _ _ ih₁ ih₂ stack done
    have hrest := ih₂ stack (r :: done)
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hrest
    exact (ih₁ _).trans (.head ascend_resume hrest)

/-- The machine has at most one step from any configuration. -/
theorem step_deterministic {x y z : Config V L K C P S}
    (hy : Step σ x y) (hz : Step σ x z) : y = z := by
  cases hy <;> cases hz <;> simp_all

/-- An image with no pending work is final. -/
theorem ascend_nil_final (r : Term V L) (s : S) (y : Config V L K C P S) :
    ¬ Step σ (.ascend r [] s) y := by
  intro h
  cases h

/-- Two final configurations reached from one configuration are equal. -/
theorem steps_final_unique {x a : Config V L K C P S} (ha : Steps σ x a) :
    ∀ {b}, (∀ y, ¬ Step σ a y) → Steps σ x b → (∀ y, ¬ Step σ b y) → a = b := by
  induction ha with
  | refl =>
      intro b ha_final hb _
      cases hb with
      | refl => rfl
      | head h _ => exact absurd h (ha_final _)
  | head hxy _ ih =>
      intro b ha_final hb hb_final
      cases hb with
      | refl => exact absurd hxy (hb_final _)
      | head hxy' hb' =>
          rw [← step_deterministic hxy hxy'] at hb'
          exact ih ha_final hb' hb_final

/-- From the empty stack, the machine's only final configuration is the
recursive fold's image, with the state the fold leaves. -/
theorem run_unique {c : C} {p : P} {s s' : S} {t r : Term V L}
    (h : Fold σ c p s t r s') {z : Config V L K C P S}
    (hz : Steps σ (.descend c p t [] s) z) (hz_final : ∀ y, ¬ Step σ z y) :
    z = .ascend r [] s' :=
  (steps_final_unique (fold_runs h []) (ascend_nil_final r s') hz hz_final).symm

namespace Controls

/-- Variables and leaves of the controls. -/
inductive Name | x | y | z
  deriving DecidableEq

inductive Leaf | cons | one | two | nil
  deriving DecidableEq

/-- A two-cell list bound cell by cell: `x ↦ (cons 1 y)`, `y ↦ (cons 2 nil)`;
`z` is unbound. -/
def chain : Subst Name Leaf Name Unit Unit Unit where
  step _ _ _ v :=
    match v with
    | .x => .bound .x (.expr [.leaf .cons, .leaf .one, .var .y]) () () ()
    | .y => .bound .y (.expr [.leaf .cons, .leaf .two, .leaf .nil]) () () ()
    | .z => .image (.var .z) ()
  store s _ _ := s
  hasVars t :=
    match t with
    | .var _ => true
    | .leaf _ => false
    | .expr [_, _, .var _] => true
    | .expr _ => false

/-- The image of `x` is the whole list: the fold follows the chain through `y`. -/
theorem chain_image :
    Fold chain () () () (.var .x)
      (.expr [.leaf .cons, .leaf .one,
        .expr [.leaf .cons, .leaf .two, .leaf .nil]]) () :=
  .bound (k := .x) (t := .expr [.leaf .cons, .leaf .one, .var .y])
    (c' := ()) (p' := ()) (s₁ := ()) rfl rfl
    (.expr rfl (.cons (.fixed rfl) (.cons (.fixed rfl)
      (.cons (.bound (k := .y) (t := .expr [.leaf .cons, .leaf .two, .leaf .nil])
        (c' := ()) (p' := ()) (s₁ := ()) rfl rfl (.fixed rfl)) .nil))))

/-- An unbound variable's image is the step's own reading of it. -/
theorem unbound_image : Fold chain () () () (.var .z) (.var .z) () :=
  .image rfl rfl

/-- The machine does not stop at the bound value `(cons 1 y)`: its only final
configuration from `x` is the whole list. -/
theorem chain_not_shallow
    (hz : Steps chain (.descend () () (.var .x) [] ())
      (.ascend (.expr [.leaf .cons, .leaf .one, .var .y]) [] ())) : False := by
  have := run_unique chain_image hz (ascend_nil_final _ _)
  simp at this

end Controls

end Mettapedia.Machines.SubstitutionFold
