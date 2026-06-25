/- ============================================================================
   Lean ladder 01 — Basics: data, functions, evaluation
   (MeTTaKernel curriculum, DTT ladder, Lean 4 — vanilla, no Mathlib)
   Style after "Functional Programming in Lean".  Check: `lean 01_basics.lean` (exit 0).
   ========================================================================== -/
namespace ICL01

def negb : Bool → Bool
  | true  => false
  | false => true

def andb : Bool → Bool → Bool
  | true,  b => b
  | false, _ => false

def double : Nat → Nat
  | 0     => 0
  | n + 1 => double n + 2

#eval negb true          -- false
#eval andb true false    -- false
#eval double 3           -- 6

theorem negb_negb (b : Bool) : negb (negb b) = b := by
  cases b <;> rfl

theorem double_two : double 2 = 4 := rfl

end ICL01
