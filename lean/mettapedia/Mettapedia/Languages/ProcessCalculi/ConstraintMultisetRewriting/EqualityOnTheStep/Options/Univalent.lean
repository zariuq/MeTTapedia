import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.Observability
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The univalent option, in a model: equivalent types are identified

Cubical type theory makes equality of types univalent: a path between two types is an equivalence,
and transport along it applies the equivalence. No syntax is built here. The model is the universe
of small types as a groupoid, whose paths are equivalences (`Path`), and sets over it are functions
into it, whose paths are pointwise (`SetPath`).

**What holds in the model.**

* *The decoding family transports along paths, coherently* (`transport_refl`, `transport_trans`,
  `transport_symm_cancel`): along the identity path transport is the identity, along a composite it
  composes, and along the inverse it cancels; the groupoid laws hold (`trans_assoc`, `refl_trans`,
  `trans_refl`, `trans_symm`).
* *The two sets of `SetExtensionality` are identified* (`swapPath`): `S X = X × G` and
  `T X = G × X` are joined by the swap at every `X`; transport along it computes the swapped pair
  (`transport_swap`), as `Computation.coercion_computes` computes it in the knowledge, and the round
  trip is the identity (`swap_round_trip`), as `Computation.swap_round_trip` is in the knowledge.
* *The identity family transports*: the **path family** `R ↦ SetPath R S₀`, the univalent
  replacement of the intensional identity family, transports by composition
  (`pathFamily_transport`), coherently (`pathFamily_transport_refl`, `pathFamily_transport_trans`).
  In the tree's intensional syntax its counterpart has no respect term
  (`Controls.idFamily_no_respect`): univalence changes that result.
* *Counting is invariant along paths* (`count_respected`): equivalent types have the same number of
  elements. Evidence that is only a pair of maps does not give this (`Observational`).

**The control: an equality with unique proofs is not univalent** (`uip_not_univalent`). In the
set-family model the identity of types is Lean's equality, a proposition, so the map from
`Bool = Bool` to `Bool ≃ Bool` takes only the value `Equiv.refl` and misses negation. Univalence
needs proof-relevant identity of types; the intensional identity with unique proofs cannot be made
univalent by adding equations.

**What a step would need for this option** (no theorem here claims it): an interval with endpoint
equations in the knowledge, Kan operations (transport and composition) with computation rules by
type structure, glue types to turn equivalences into paths, and unification modulo the face lattice
(constraints of the form `i = 0 ∨ j = 1`). Paths would be terms, as evidence rows are: the knowledge
would still separate `S` and `T` judgmentally, so by `Observability.conservative_iff` absence and
counting of rows of `S` and of `T` would keep their separate answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Options.Univalent

universe u

/-! ## The universe as a groupoid -/

/-- **A path between two small types**: an equivalence. -/
abbrev Path (A B : Type u) : Type u := A ≃ B

/-- The identity path. -/
def Path.rfl (A : Type u) : Path A A := Equiv.refl A

/-- The composite path. -/
def Path.trans {A B C : Type u} (p : Path A B) (q : Path B C) : Path A C := Equiv.trans p q

/-- The inverse path. -/
def Path.symm {A B : Type u} (p : Path A B) : Path B A := Equiv.symm p

/-- **Transport in the decoding family** along a path. -/
def transport {A B : Type u} (p : Path A B) : A → B := p

theorem transport_refl (A : Type u) (a : A) : transport (Path.rfl A) a = a := rfl

theorem transport_trans {A B C : Type u} (p : Path A B) (q : Path B C) (a : A) :
    transport (p.trans q) a = transport q (transport p a) := rfl

theorem transport_symm_cancel {A B : Type u} (p : Path A B) (a : A) :
    transport p.symm (transport p a) = a :=
  Equiv.symm_apply_apply p a

theorem trans_assoc {A B C D : Type u} (p : Path A B) (q : Path B C) (r : Path C D) :
    (p.trans q).trans r = p.trans (q.trans r) := Equiv.trans_assoc p q r

theorem refl_trans {A B : Type u} (p : Path A B) : (Path.rfl A).trans p = p := Equiv.refl_trans p

theorem trans_refl {A B : Type u} (p : Path A B) : p.trans (Path.rfl B) = p := Equiv.trans_refl p

theorem trans_symm {A B : Type u} (p : Path A B) : p.trans p.symm = Path.rfl A := Equiv.self_trans_symm p

/-! ## Sets over the universe, and their paths -/

/-- **A path between two sets**: a path at every small type. -/
def SetPath (S T : Type u → Type u) : Type (u + 1) := ∀ X : Type u, Path (S X) (T X)

def SetPath.rfl (S : Type u → Type u) : SetPath S S := fun X => Path.rfl (S X)

def SetPath.trans {S T U : Type u → Type u} (p : SetPath S T) (q : SetPath T U) : SetPath S U :=
  fun X => (p X).trans (q X)

def SetPath.symm {S T : Type u → Type u} (p : SetPath S T) : SetPath T S := fun X => (p X).symm

/-- The set `S = {X | Σ (_ : X). Ground}`, in the model. -/
def sFam (G : Type u) : Type u → Type u := fun X => X × G

/-- The set `T = {X | Σ (_ : Ground). X}`, in the model. -/
def tFam (G : Type u) : Type u → Type u := fun X => G × X

/-- **The two sets are identified**: the swap is a path at every `X`. -/
def swapPath (G : Type u) : SetPath (sFam G) (tFam G) := fun X => Equiv.prodComm X G

/-- **Transport along the swap computes the swapped pair.** -/
theorem transport_swap (G X : Type u) (x : X) (g : G) : transport (swapPath G X) (x, g) = (g, x) := rfl

/-- **The round trip is the identity.** -/
theorem swap_round_trip (G X : Type u) (p : sFam G X) :
    transport (swapPath G X).symm (transport (swapPath G X) p) = p :=
  transport_symm_cancel (swapPath G X) p

/-! ## Families transport along paths: the path family -/

/-- **The path family of a set `S₀`**: `R ↦ SetPath R S₀`, the univalent identity family. -/
abbrev PathFamily (S₀ : Type u → Type u) (R : Type u → Type u) : Type (u + 1) := SetPath R S₀

/-- **The path family transports along every path between sets**, by composition with the inverse. -/
def pathFamily_transport {S₀ R R' : Type u → Type u} (e : SetPath R R') :
    PathFamily S₀ R → PathFamily S₀ R' :=
  fun p => e.symm.trans p

/-- Along the identity path, transport in the path family is the identity. -/
theorem pathFamily_transport_refl {S₀ R : Type u → Type u} (p : PathFamily S₀ R) :
    pathFamily_transport (SetPath.rfl R) p = p := by
  funext X
  exact Equiv.ext fun _ => rfl

/-- Along a composite path, transport in the path family composes. -/
theorem pathFamily_transport_trans {S₀ R R' R'' : Type u → Type u} (e : SetPath R R') (e' : SetPath R' R'')
    (p : PathFamily S₀ R) :
    pathFamily_transport (e.trans e') p = pathFamily_transport e' (pathFamily_transport e p) := by
  funext X
  exact Equiv.ext fun _ => rfl

/-- The swap path is a member of the path family of `T`, at `S`: the identity family is inhabited
at the second set. -/
def swap_in_pathFamily (G : Type u) : PathFamily (tFam G) (sFam G) := swapPath G

/-! ## Counting is invariant along paths -/

/-- **Equivalent types have the same number of elements.** -/
theorem count_respected {A B : Type u} (p : Path A B) : Nat.card A = Nat.card B := Nat.card_congr p

/-! ## The control: unique proofs of equality are not univalent -/

/-- Negation, an equivalence of `Bool` with itself. -/
def negation : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- **The identity of types with unique proofs is not univalent**: every proof of `Bool = Bool` is
sent to the identity equivalence, so negation is missed. -/
theorem uip_not_univalent : ¬ Function.Surjective (fun h : Bool = Bool => Equiv.cast h) := by
  intro onto
  obtain ⟨h, same⟩ := onto negation
  have atTrue : (Equiv.cast h) true = negation true := congrArg (fun e : Bool ≃ Bool => e true) same
  have castTrue : (Equiv.cast h) true = true := by
    cases h
    rfl
  rw [castTrue] at atTrue
  exact absurd atTrue (by decide)

/-- **The univalent model does have a non-identity path from `Bool` to itself.** -/
theorem negation_is_a_path : negation ≠ Path.rfl Bool := by
  intro same
  have atTrue := congrArg (fun e : Bool ≃ Bool => e true) same
  exact absurd atTrue (by decide)

end EqualityOnTheStep.Options.Univalent

#print axioms EqualityOnTheStep.Options.Univalent.transport_trans
#print axioms EqualityOnTheStep.Options.Univalent.trans_symm
#print axioms EqualityOnTheStep.Options.Univalent.transport_swap
#print axioms EqualityOnTheStep.Options.Univalent.swap_round_trip
#print axioms EqualityOnTheStep.Options.Univalent.pathFamily_transport_refl
#print axioms EqualityOnTheStep.Options.Univalent.pathFamily_transport_trans
#print axioms EqualityOnTheStep.Options.Univalent.count_respected
#print axioms EqualityOnTheStep.Options.Univalent.uip_not_univalent
#print axioms EqualityOnTheStep.Options.Univalent.negation_is_a_path

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
