import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafPrograms

/-!
# Polyadic primitive arrows in the actual binding-clone presheaf category

Every primitive is assembled from the independently supplied clone operator
and the actual chosen products and exponentials. Plain arguments are curried
as functions of the empty binder context. Unary bodies use the entire name
function object; binary bodies use an earned comparison with the ordered
two-name context representable. No operation or equation is supplied by an
asserted compiler interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperations

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf

universe u

variable (A : BindingCloneAlgebra.Algebra.{u} sig)

abbrev Ambient := IntrinsicScopedOperationalPresheafPrograms.target A
abbrev names : Ambient A := programs A Srt.nm
abbrev processes : Ambient A := programs A Srt.pr
abbrev unaryBodies : Ambient A := (ihom (names A)).obj (processes A)
abbrev binaryBodies : Ambient A := (ihom (names A ⊗ names A)).obj (processes A)

/-- A supplied value gives its genuine future-sensitive function of no
bound arguments. Its future stage still reindexes the supplied value. -/
def plainArgument (sort : Srt) :
    programs A sort ⟶ IntrinsicScopedOperationalPresheafPrograms.power A [] sort :=
  MonoidalClosed.curry (snd (binders A []) (programs A sort))

/-- The two ordered names are the actual two-name context representable. -/
def binaryContextIso : names A ⊗ names A ≅ binders A [Srt.nm, Srt.nm] :=
  (MonoidalCategory.tensorIso (Iso.refl (names A)) (ρ_ (names A)).symm) ≪≫
    IntrinsicScopedOperationalPresheafPrograms.contextIso A [Srt.nm, Srt.nm]

/-- Precomposition is an actual exponential isomorphism, retaining the
entire binary function section and both distinct binder positions. -/
def binaryBodyIso : binaryBodies A ≅
    IntrinsicScopedOperationalPresheafPrograms.power A [Srt.nm, Srt.nm] Srt.pr :=
  (MonoidalClosed.internalHom.mapIso (binaryContextIso A).symm.op).app (processes A)

def empty : 𝟙_ (Ambient A) ⟶ processes A :=
  IntrinsicScopedOperationalPresheafPrograms.op A Op.nil

def parallel : processes A ⊗ processes A ⟶ processes A :=
  lift (fst _ _ ≫ plainArgument A Srt.pr)
    (lift (snd _ _ ≫ plainArgument A Srt.pr) (toUnit _)) ≫
      IntrinsicScopedOperationalPresheafPrograms.op A Op.par

def output : names A ⊗ names A ⟶ processes A :=
  lift (fst _ _ ≫ plainArgument A Srt.nm)
    (lift (snd _ _ ≫ plainArgument A Srt.nm) (toUnit _)) ≫
      IntrinsicScopedOperationalPresheafPrograms.op A Op.out1

def send : names A ⊗ (names A ⊗ names A) ⟶ processes A :=
  lift (fst _ _ ≫ plainArgument A Srt.nm)
    (lift (snd _ _ ≫ fst _ _ ≫ plainArgument A Srt.nm)
      (lift (snd _ _ ≫ snd _ _ ≫ plainArgument A Srt.nm) (toUnit _))) ≫
        IntrinsicScopedOperationalPresheafPrograms.op A Op.out2

def input : names A ⊗ unaryBodies A ⟶ processes A :=
  lift (fst _ _ ≫ plainArgument A Srt.nm)
    (lift (snd _ _) (toUnit _)) ≫
      IntrinsicScopedOperationalPresheafPrograms.op A Op.inp1

def receive : names A ⊗ binaryBodies A ⟶ processes A :=
  lift (fst _ _ ≫ plainArgument A Srt.nm)
    (lift (snd _ _ ≫ (binaryBodyIso A).hom) (toUnit _)) ≫
      IntrinsicScopedOperationalPresheafPrograms.op A Op.inp2

def fresh : unaryBodies A ⟶ processes A :=
  lift (𝟙 _) (toUnit _) ≫ IntrinsicScopedOperationalPresheafPrograms.op A Op.nu

def replication : processes A ⟶ processes A :=
  lift (plainArgument A Srt.pr) (toUnit _) ≫
    IntrinsicScopedOperationalPresheafPrograms.op A Op.rep

/-- The actual independently authored pi equation quotient is one instance
of these same whole-function primitive arrows. -/
abbrev equationAlgebra := AuthoredClassified.algebra

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperations
