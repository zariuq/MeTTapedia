import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-!
# Realized property atoms and consumer alphabets

An atom is a realized vector of membership observations in an explicit
domain. It can have several disconnected interval components. Boolean
expressions lower to sets of these atoms; their independent pointwise meaning
is preserved and reflected by equality of the lowered sets. Literal predicates
can refine an existing partition. These laws do not certify a native event
sweep, hash table or pointer representation.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.PropertyAtoms

universe u
variable {α : Type u} {n : Nat}

noncomputable def profile (labels : Fin n → Set α) (point : α) : Fin n → Bool := by
  classical
  exact fun label => decide (point ∈ labels label)

inductive Expr (n : Nat) where
  | empty
  | full
  | label (index : Fin n)
  | union (left right : Expr n)
  | intersection (left right : Expr n)
  | difference (left right : Expr n)
  | complement (expression : Expr n)
  deriving Repr, DecidableEq

def evaluate : Expr n → (Fin n → Bool) → Bool
  | .empty, _ => false
  | .full, _ => true
  | .label index, bits => bits index
  | .union left right, bits => evaluate left bits || evaluate right bits
  | .intersection left right, bits => evaluate left bits && evaluate right bits
  | .difference left right, bits => evaluate left bits && !evaluate right bits
  | .complement expression, bits => !evaluate expression bits

/-- Independent pointwise meaning, with every operation scoped to its domain. -/
def Denote (domain : Set α) (labels : Fin n → Set α) : Expr n → α → Prop
  | .empty, _ => False
  | .full, point => point ∈ domain
  | .label index, point => point ∈ domain ∧ point ∈ labels index
  | .union left right, point => Denote domain labels left point ∨ Denote domain labels right point
  | .intersection left right, point => Denote domain labels left point ∧ Denote domain labels right point
  | .difference left right, point => Denote domain labels left point ∧ ¬Denote domain labels right point
  | .complement expression, point => point ∈ domain ∧ ¬Denote domain labels expression point

theorem denote_evaluate (domain : Set α) (labels : Fin n → Set α)
    (expression : Expr n) (point : α) :
    Denote domain labels expression point ↔
      point ∈ domain ∧ evaluate expression (profile labels point) = true := by
  classical
  induction expression with
  | empty => simp [Denote, evaluate]
  | full => simp [Denote, evaluate]
  | label index => simp [Denote, evaluate, profile]
  | union left right ihl ihr =>
    simp only [Denote, evaluate, Bool.or_eq_true, ihl, ihr]
    tauto
  | intersection left right ihl ihr =>
    simp only [Denote, evaluate, Bool.and_eq_true, ihl, ihr]
    tauto
  | difference left right ihl ihr =>
    cases hl : evaluate left (profile labels point) <;>
      cases hr : evaluate right (profile labels point) <;>
      simp_all [Denote, evaluate]
  | complement expression ih =>
    cases he : evaluate expression (profile labels point) <;>
      simp_all [Denote, evaluate]

def Atom (domain : Set α) (labels : Fin n → Set α) :=
  {bits : Fin n → Bool // ∃ point ∈ domain, profile labels point = bits}

def fiber (domain : Set α) (labels : Fin n → Set α)
    (atom : Atom domain labels) : Set α :=
  {point | point ∈ domain ∧ profile labels point = atom.val}

theorem fibers_cover (domain : Set α) (labels : Fin n → Set α)
    (point : α) (present : point ∈ domain) :
    ∃ atom : Atom domain labels, point ∈ fiber domain labels atom := by
  exact ⟨⟨profile labels point, point, present, rfl⟩, present, rfl⟩

theorem fiber_nonempty (domain : Set α) (labels : Fin n → Set α)
    (atom : Atom domain labels) : (fiber domain labels atom).Nonempty := by
  obtain ⟨point, present, observed⟩ := atom.property
  exact ⟨point, present, observed⟩

theorem fibers_disjoint (domain : Set α) (labels : Fin n → Set α)
    (left right : Atom domain labels) (different : left ≠ right) :
    Disjoint (fiber domain labels left) (fiber domain labels right) := by
  apply Set.disjoint_left.mpr
  rintro point ⟨_, hl⟩ ⟨_, hr⟩
  exact different (Subtype.ext (hl.symm.trans hr))

def lower (domain : Set α) (labels : Fin n → Set α)
    (expression : Expr n) : Set (Atom domain labels) :=
  {atom | evaluate expression atom.val = true}

theorem lower_membership (domain : Set α) (labels : Fin n → Set α)
    (expression : Expr n) (atom : Atom domain labels)
    (point : α) (member : point ∈ fiber domain labels atom) :
    atom ∈ lower domain labels expression ↔ Denote domain labels expression point := by
  rw [denote_evaluate]
  change evaluate expression atom.val = true ↔
    point ∈ domain ∧ evaluate expression (profile labels point) = true
  rw [member.2]
  simp [member.1]

/-- Equality of atom normal forms is exactly equality of observable sets, not
equality on impossible membership combinations. -/
theorem normal_forms_equal_iff (domain : Set α) (labels : Fin n → Set α)
    (left right : Expr n) :
    lower domain labels left = lower domain labels right ↔
      ∀ point, Denote domain labels left point ↔ Denote domain labels right point := by
  constructor
  · intro equal point
    by_cases present : point ∈ domain
    · obtain ⟨atom, member⟩ := fibers_cover domain labels point present
      rw [←lower_membership domain labels left atom point member,
        ←lower_membership domain labels right atom point member, equal]
    · simp [denote_evaluate, present]
  · intro equal
    apply Set.ext
    intro atom
    obtain ⟨point, present, observed⟩ := atom.property
    have member : point ∈ fiber domain labels atom := ⟨present, observed⟩
    rw [lower_membership domain labels left atom point member,
      lower_membership domain labels right atom point member]
    exact equal point

theorem same_atom_same_expression (domain : Set α) (labels : Fin n → Set α)
    (expression : Expr n) (left right : α)
    (hl : left ∈ domain) (hr : right ∈ domain)
    (same : profile labels left = profile labels right) :
    Denote domain labels expression left ↔ Denote domain labels expression right := by
  simp only [denote_evaluate, hl, hr, true_and, same]

theorem consumer_projection {m : Nat} (labels : Fin n → Set α)
    (select : Fin m → Fin n) (point : α) :
    profile (fun index => labels (select index)) point =
      fun index => profile labels point (select index) := by
  classical
  rfl

theorem projection_preserves_equivalence {m : Nat} (labels : Fin n → Set α)
    (select : Fin m → Fin n) (left right : α)
    (same : profile labels left = profile labels right) :
    profile (fun index => labels (select index)) left =
      profile (fun index => labels (select index)) right := by
  simp only [consumer_projection, same]

theorem complement_involution (domain : Set α) (labels : Fin n → Set α)
    (expression : Expr n) :
    lower domain labels (.complement (.complement expression)) =
      lower domain labels expression := by
  apply (normal_forms_equal_iff domain labels _ _).mpr
  intro point
  rw [denote_evaluate, denote_evaluate]
  simp [evaluate]

theorem intersection_distributes (domain : Set α) (labels : Fin n → Set α)
    (first second third : Expr n) :
    lower domain labels (.intersection first (.union second third)) =
      lower domain labels (.union (.intersection first second) (.intersection first third)) := by
  apply (normal_forms_equal_iff domain labels _ _).mpr
  intro point
  simp only [Denote]
  tauto

/-! Positive and negative examples. A literal can split a property atom;
comparing all bit vectors instead of realized ones rejects a valid equality. -/

example : profile (fun _ : Fin 1 => (Set.univ : Set Nat)) 0 =
    profile (fun _ : Fin 1 => (Set.univ : Set Nat)) 1 := by
  classical
  funext index
  simp [profile]

example : profile (fun i : Fin 2 => if i = 0 then Set.univ else ({0} : Set Nat)) 0 ≠
    profile (fun i : Fin 2 => if i = 0 then Set.univ else ({0} : Set Nat)) 1 := by
  classical
  intro equal
  have observed := congrFun equal 1
  simp [profile] at observed

example : lower (Set.univ : Set Nat) (fun _ : Fin 1 => ∅) (.label 0) =
    lower Set.univ (fun _ : Fin 1 => ∅) .empty := by
  apply (normal_forms_equal_iff _ _ _ _).mpr
  intro point
  simp [Denote]

example : evaluate (Expr.label (0 : Fin 1)) (fun _ => true) ≠
    evaluate (Expr.empty : Expr 1) (fun _ => true) := by decide +kernel

#print axioms denote_evaluate
#print axioms fibers_cover
#print axioms fiber_nonempty
#print axioms fibers_disjoint
#print axioms lower_membership
#print axioms normal_forms_equal_iff
#print axioms same_atom_same_expression
#print axioms consumer_projection
#print axioms projection_preserves_equivalence
#print axioms complement_involution
#print axioms intersection_distributes

end Mettapedia.Computability.RegularLanguages.PropertyAtoms
