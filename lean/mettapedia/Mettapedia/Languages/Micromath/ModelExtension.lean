import Mettapedia.Languages.Micromath.Kernel

/-!
# Fresh definition and the allocated interpretation frontier

Projection rules may mention symbols not yet allocated by the source kernel.
Consequently sound stored claims must hold uniformly over interpretations of
those future symbols. A fresh definition restricts this family of models; it
does not require every earlier claim to avoid the fresh symbol syntactically.

These laws specify semantic extension and conservativity on the old vocabulary.
They do not verify UInt64 arithmetic, mutable C storage or binary loading.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Micromath.ModelExtension
universe u
variable {D : Type u}
abbrev BinaryOperation (D : Type u) := D → D → D

def superpose (f g h : BinaryOperation D) : BinaryOperation D := fun a b => f (g a b) (h a b)
def first : BinaryOperation D := fun a _ => a
def second : BinaryOperation D := fun _ b => b

theorem superpose_superpose (f g h a b : BinaryOperation D) :
    superpose (superpose f g h) a b = superpose f (superpose g a b) (superpose h a b) := rfl
theorem superpose_first (g h : BinaryOperation D) : superpose first g h = g := rfl
theorem superpose_second (g h : BinaryOperation D) : superpose second g h = h := rfl
theorem superpose_projections (f : BinaryOperation D) : superpose f first second = f := rfl

def AgreesThrough (frontier : Nat) (base candidate : Assignment D) : Prop :=
  ∀ symbol, symbol ≤ frontier → candidate symbol = base symbol

def Forces (frontier : Nat) (base : Assignment D) (claim : Claim) : Prop :=
  ∀ candidate, AgreesThrough frontier base candidate → Holds candidate claim

def UniformlyValid (frontier : Nat) (base : Assignment D) (claims : Set Claim) : Prop :=
  ∀ claim ∈ claims, Forces frontier base claim

def update (frontier : Nat) (base : Assignment D) (operation : BinaryOperation D) : Assignment D :=
  fun symbol => if symbol = frontier + 1 then operation else base symbol

theorem update_fresh (frontier : Nat) (base : Assignment D) (operation : BinaryOperation D) :
    update frontier base operation (frontier + 1) = operation := if_pos rfl

theorem update_old (frontier : Nat) (base : Assignment D) (operation : BinaryOperation D)
    (symbol : Symbol) (old : symbol ≤ frontier) : update frontier base operation symbol = base symbol := by
  exact if_neg (Nat.ne_of_lt (Nat.lt_succ_of_le old))

theorem agrees_old (frontier : Nat) (base candidate : Assignment D) (operation : BinaryOperation D)
    (agrees : AgreesThrough (frontier + 1) (update frontier base operation) candidate) :
    AgreesThrough frontier base candidate := by
  intro symbol old
  exact (agrees symbol (Nat.le_trans old (Nat.le_succ frontier))).trans (update_old frontier base operation symbol old)

/-- Opaque allocation may choose any binary operation for the next symbol. -/
theorem allocate_preserves (frontier : Nat) (base : Assignment D) (operation : BinaryOperation D)
    (claims : Set Claim) (valid : UniformlyValid frontier base claims) :
    UniformlyValid (frontier + 1) (update frontier base operation) claims := by
  intro claim member candidate agrees
  exact valid claim member candidate (agrees_old frontier base candidate operation agrees)

def define (frontier : Nat) (base : Assignment D) (f x y : Symbol) : Assignment D :=
  update frontier base (superpose (base f) (base x) (base y))

def definition (frontier : Nat) (f x y : Symbol) : Claim := ⟨frontier + 1,f,x,y⟩

theorem definition_forced (frontier : Nat) (base : Assignment D) (f x y : Symbol)
    (fOld : f ≤ frontier) (xOld : x ≤ frontier) (yOld : y ≤ frontier) :
    Forces (frontier + 1) (define frontier base f x y) (definition frontier f x y) := by
  intro candidate agrees a b
  have previous := agrees_old frontier base candidate (superpose (base f) (base x) (base y)) agrees
  change candidate (frontier + 1) a b = candidate f (candidate x a b) (candidate y a b)
  rw [agrees (frontier + 1) (Nat.le_refl _)]
  change update frontier base (superpose (base f) (base x) (base y)) (frontier + 1) a b = _
  rw [update_fresh,
    previous f fOld, previous x xOld, previous y yOld]
  rfl

theorem define_preserves (frontier : Nat) (base : Assignment D) (claims : Set Claim)
    (valid : UniformlyValid frontier base claims) (f x y : Symbol)
    (fOld : f ≤ frontier) (xOld : x ≤ frontier) (yOld : y ≤ frontier) :
    UniformlyValid (frontier + 1) (define frontier base f x y) (insert (definition frontier f x y) claims) := by
  intro claim member
  rcases member with rfl | member
  · exact definition_forced frontier base f x y fOld xOld yOld
  · exact allocate_preserves frontier base _ claims valid claim member

theorem projects_of_agrees (frontier : Nat) (base candidate : Assignment D)
    (projections : Projects base) (bothAllocated : 1 ≤ frontier)
    (agrees : AgreesThrough frontier base candidate) : Projects candidate := by
  constructor
  · intro a b
    rw [agrees 0 (Nat.zero_le frontier)]
    exact projections.first a b
  · intro a b
    rw [agrees 1 bothAllocated]
    exact projections.second a b

/-- Future symbol addresses in a projection require no allocation premise. -/
theorem projection_forced (frontier : Nat) (base : Assignment D)
    (projections : Projects base) (bothAllocated : 1 ≤ frontier) (a b : Symbol) :
    Forces frontier base (projectionFirst a b) := by
  intro candidate agrees
  exact projectionFirst_holds candidate (projects_of_agrees frontier base candidate projections bothAllocated agrees) a b

theorem derivation_forced (frontier : Nat) (base : Assignment D)
    (projections : Projects base) (bothAllocated : 1 ≤ frontier)
    (axioms : Set Claim) (valid : UniformlyValid frontier base axioms)
    (claim : Claim) (derived : Derives axioms claim) : Forces frontier base claim := by
  intro candidate agrees
  exact derives_sound candidate (projects_of_agrees frontier base candidate projections bothAllocated agrees)
    (fun premise member => valid premise member candidate agrees) derived

def Bounded (frontier : Nat) (claim : Claim) : Prop :=
  claim.out ≤ frontier ∧ claim.f ≤ frontier ∧ claim.x ≤ frontier ∧ claim.y ≤ frontier

theorem holds_update_iff (frontier : Nat) (base : Assignment D) (operation : BinaryOperation D)
    (claim : Claim) (bounded : Bounded frontier claim) :
    Holds (update frontier base operation) claim ↔ Holds base claim := by
  rcases bounded with ⟨outOld,fOld,xOld,yOld⟩
  constructor
  · intro held a b
    simpa only [update_old frontier base operation claim.out outOld,
      update_old frontier base operation claim.f fOld,update_old frontier base operation claim.x xOld,
      update_old frontier base operation claim.y yOld] using held a b
  · intro held a b
    rw [update_old frontier base operation claim.out outOld,update_old frontier base operation claim.f fOld,
      update_old frontier base operation claim.x xOld,update_old frontier base operation claim.y yOld]
    exact held a b

theorem extend_agrees (frontier : Nat) (base candidate : Assignment D) (operation : BinaryOperation D)
    (agrees : AgreesThrough frontier base candidate) :
    AgreesThrough (frontier + 1) (update frontier base operation) (update frontier candidate operation) := by
  intro symbol bound
  by_cases fresh : symbol = frontier + 1
  · subst symbol
    rw [update_fresh,update_fresh]
  · have old : symbol ≤ frontier := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne bound fresh)
    rw [update_old frontier candidate operation symbol old,update_old frontier base operation symbol old]
    exact agrees symbol old

/-- The fresh operation can be eliminated from claims in the old vocabulary. -/
theorem definition_conservative (frontier : Nat) (base : Assignment D) (f x y : Symbol)
    (claim : Claim) (bounded : Bounded frontier claim)
    (valid : Forces (frontier + 1) (define frontier base f x y) claim) : Forces frontier base claim := by
  intro candidate agrees
  let operation := superpose (base f) (base x) (base y)
  have extension := extend_agrees frontier base candidate operation agrees
  exact (holds_update_iff frontier candidate operation claim bounded).mp (valid _ extension)

namespace Controls
def boolBase : Assignment Bool := fun symbol => if symbol = 1 then second else first
def futureFixed : Claim := ⟨2,0,0,1⟩
theorem boolBase_projects : Projects boolBase := by constructor <;> intros <;> rfl
theorem pointwise_future_claim : Holds boolBase futureFixed := by intro a b; rfl
theorem defined_future_claim_refused : ¬ Holds (define 1 boolBase 1 0 1) futureFixed := by
  intro holds
  have impossible : true = false := holds false true
  exact Bool.noConfusion impossible
theorem pointwise_is_not_uniform : ¬ Forces 1 boolBase futureFixed := by
  intro forced
  apply defined_future_claim_refused
  apply forced
  intro symbol bound
  exact update_old 1 boolBase _ symbol bound
theorem future_projection_preserved : Forces 2 (define 1 boolBase 1 0 1) (projectionFirst 99 100) :=
  allocate_preserves 1 boolBase _ {projectionFirst 99 100}
    (by intro claim member; change claim = projectionFirst 99 100 at member; cases member
        exact projection_forced 1 boolBase boolBase_projects (by decide) 99 100)
    _ rfl
theorem new_definition_valid : Forces 2 (define 1 boolBase 1 0 1) (definition 1 1 0 1) :=
  definition_forced 1 boolBase 1 0 1 (by decide) (by decide) (by decide)
end Controls

#print axioms define_preserves
#print axioms definition_conservative
#print axioms Controls.pointwise_is_not_uniform
end Mettapedia.Languages.Micromath.ModelExtension
