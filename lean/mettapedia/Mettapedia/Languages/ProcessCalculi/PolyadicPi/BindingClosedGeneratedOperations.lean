import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedPresentation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations

/-!
# Ordinary pi primitives from complete binding operator domains

Unbound arguments are actual functions out of the terminal binder context.
They are packed by currying their supplied values. Receivers keep the full
ordered name-tuple function, while unary and binary continuation primitives
use the canonical unit and associativity isomorphisms on that tuple.

The construction applies to any closed binding algebra of the all-arity
signature, in particular the independently generated equation guest's own
algebra. It does not require a runtime model or a compiler comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedPrimitiveOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open Bridges.NamePassingContinuationOperations
open Bridges.NamePassingBindingClosedOperations (emptyValue empty_curry)

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations AllArity.sig C)

def plain (result : AllArity.sig.Srt) : binding.sort result ⟶ (𝟙_ C ⟶[C] binding.sort result) :=
  MonoidalClosed.curry (snd (𝟙_ C) (binding.sort result))

theorem plain_recovers (result : AllArity.sig.Srt) :
    plain binding result ≫ emptyValue (binding.sort result) = 𝟙 (binding.sort result) := by
  simpa only [plain, Category.comp_id] using empty_curry (𝟙 (binding.sort result))

def names : C := binding.sort Srt.nm
def processes : C := binding.sort Srt.pr
def tuple (arity : Nat) : C := binding.context (AllArity.names arity)

def vector : (arity : Nat) → tuple binding arity ⟶ binding.family (AllArity.nameArguments arity)
  | 0 => 𝟙 (𝟙_ C)
  | arity + 1 => lift (fst _ _ ≫ plain binding Srt.nm) (snd _ _ ≫ vector arity)

def output (arity : Nat) : names binding ⊗ tuple binding arity ⟶ processes binding :=
  lift (fst _ _ ≫ plain binding Srt.nm) (snd _ _ ≫ vector binding arity) ≫
    binding.operation (AllArity.Op.out arity)

def input (arity : Nat) :
    names binding ⊗ (tuple binding arity ⟶[C] processes binding) ⟶ processes binding :=
  lift (fst _ _ ≫ plain binding Srt.nm) (lift (snd _ _) (toUnit _)) ≫
    binding.operation (AllArity.Op.inp arity)

def binaryTuple : tuple binding 2 ≅ names binding ⊗ names binding :=
  (α_ (names binding) (names binding) (𝟙_ C)).symm ≪≫ ρ_ (names binding ⊗ names binding)

def unaryBody : (names binding ⟶[C] processes binding) ⟶
    (tuple binding 1 ⟶[C] processes binding) :=
  (MonoidalClosed.pre (ρ_ (names binding)).hom).app (processes binding)

def binaryBody : ((names binding ⊗ names binding) ⟶[C] processes binding) ⟶
    (tuple binding 2 ⟶[C] processes binding) :=
  (MonoidalClosed.pre (binaryTuple binding).hom).app (processes binding)

def continuation : Operations C where
  names := names binding
  processes := processes binding
  empty := binding.operation AllArity.Op.nil
  parallel := lift (fst _ _ ≫ plain binding Srt.pr)
    (lift (snd _ _ ≫ plain binding Srt.pr) (toUnit _)) ≫ binding.operation AllArity.Op.par
  output := lift (fst _ _) (lift (snd _ _) (toUnit _)) ≫ output binding 1
  send := lift (fst _ _) (snd _ _ ≫ (binaryTuple binding).inv) ≫ output binding 2
  input := lift (fst _ _) (snd _ _ ≫ unaryBody binding) ≫ input binding 1
  receive := lift (fst _ _) (snd _ _ ≫ binaryBody binding) ≫ input binding 2
  fresh := lift (unaryBody binding) (toUnit _) ≫ binding.operation AllArity.Op.nu
  replication := lift (plain binding Srt.pr) (toUnit _) ≫ binding.operation AllArity.Op.rep

theorem unary_body_evaluation :
    (tuple binding 1 ◁ unaryBody binding) ≫ (ihom.ev (tuple binding 1)).app (processes binding) =
      ((ρ_ (names binding)).hom ▷ (names binding ⟶[C] processes binding)) ≫
        (ihom.ev (names binding)).app (processes binding) :=
  MonoidalClosed.id_tensor_pre_app_comp_ev _ _

theorem binary_body_evaluation :
    (tuple binding 2 ◁ binaryBody binding) ≫ (ihom.ev (tuple binding 2)).app (processes binding) =
      ((binaryTuple binding).hom ▷ ((names binding ⊗ names binding) ⟶[C] processes binding)) ≫
        (ihom.ev (names binding ⊗ names binding)).app (processes binding) :=
  MonoidalClosed.id_tensor_pre_app_comp_ev _ _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedPrimitiveOperations
