import Mettapedia.OSLF.PiCalculus.Syntax

/-!
# Structural Congruence for π-Calculus

Defines α-equivalence and structural congruence (≡).

## References
- Lybech (2022), Section 3, page 98
-/

namespace Mettapedia.OSLF.PiCalculus

/-- Structural congruence relation (Type-valued for extraction) -/
inductive StructuralCongruence : Process → Process → Type where
  -- Reflexivity, symmetry, transitivity
  | refl (P : Process) :
      StructuralCongruence P P
  | symm (P Q : Process) :
      StructuralCongruence P Q →
      StructuralCongruence Q P
  | trans (P Q R : Process) :
      StructuralCongruence P Q →
      StructuralCongruence Q R →
      StructuralCongruence P R

  -- Congruence rules
  | par_cong (P P' Q Q' : Process) :
      StructuralCongruence P P' →
      StructuralCongruence Q Q' →
      StructuralCongruence (P ||| Q) (P' ||| Q')
  | input_cong (x y : Name) (P P' : Process) :
      StructuralCongruence P P' →
      StructuralCongruence (Process.input x y P) (Process.input x y P')
  | nu_cong (x : Name) (P P' : Process) :
      StructuralCongruence P P' →
      StructuralCongruence (Process.nu x P) (Process.nu x P')
  | replicate_cong (x y : Name) (P P' : Process) :
      StructuralCongruence P P' →
      StructuralCongruence (Process.replicate x y P) (Process.replicate x y P')

  -- Parallel composition laws
  | par_comm (P Q : Process) :
      StructuralCongruence (P ||| Q) (Q ||| P)
  | par_assoc (P Q R : Process) :
      StructuralCongruence ((P ||| Q) ||| R) (P ||| (Q ||| R))
  | par_nil_left (P : Process) :
      StructuralCongruence (Process.nil ||| P) P
  | par_nil_right (P : Process) :
      StructuralCongruence (P ||| Process.nil) P

  -- Restriction laws
  | nu_nil (x : Name) :
      StructuralCongruence (Process.nu x Process.nil) Process.nil
  | nu_par (x : Name) (P Q : Process) :
      x ∉ Q.freeNames →
      StructuralCongruence (Process.nu x (P ||| Q)) ((Process.nu x P) ||| Q)
  | nu_swap (x y : Name) (P : Process) :
      StructuralCongruence (Process.nu x (Process.nu y P)) (Process.nu y (Process.nu x P))

  -- α-conversion
  | alpha_input (x y z : Name) (P : Process) :
      z ∉ P.freeNames →
      z ≠ y →
      StructuralCongruence
        (Process.input x y P)
        (Process.input x z (P.substitute y z))
  | alpha_nu (x y : Name) (P : Process) :
      y ∉ P.freeNames →
      StructuralCongruence
        (Process.nu x P)
        (Process.nu y (P.substitute x y))
  | alpha_replicate (x y z : Name) (P : Process) :
      z ∉ P.freeNames →
      z ≠ y →
      StructuralCongruence
        (Process.replicate x y P)
        (Process.replicate x z (P.substitute y z))

  -- Replication unfolding
  | replicate_unfold (x y : Name) (P : Process) :
      StructuralCongruence
        (Process.replicate x y P)
        (Process.input x y (P ||| Process.replicate x y P))

notation:50 P " ≡ " Q => StructuralCongruence P Q

namespace StructuralCongruence

/-- Structural congruence is an equivalence relation (prop version) -/
theorem equivalence : Equivalence (fun P Q => Nonempty (P ≡ Q)) where
  refl P := ⟨refl P⟩
  symm := fun ⟨h⟩ => ⟨symm _ _ h⟩
  trans := fun ⟨h1⟩ ⟨h2⟩ => ⟨trans _ _ _ h1 h2⟩

end StructuralCongruence

end Mettapedia.OSLF.PiCalculus
