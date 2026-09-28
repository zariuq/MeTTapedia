import Mettapedia.Logic.HOL.ImpredicativeProofCore
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeRepresentation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompiler
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerConversion

/-!
# Total compilation on the retained core proof fragment

The optional compiler becomes total on its exact syntactic fragment when its
eight equality operations are total. The operation algebra still carries its
typing laws; totality does not grant a new axiom or proof rule. The compiler
for proofs modulo definitional conversion, which uses no equality operation,
is total on its core fragment outright.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler

open Presentation FormationSensitiveHOLInterface Mettapedia.Logic
open HOL.ImpredicativeConnectives

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- All equality capabilities are computationally available. This supplements,
and never replaces, the laws of `Operations`. -/
structure RawOperations.Total (raw : RawOperations Base) : Prop where
  reflexivity : ∀ n, (raw.reflexivity (n := n)).isSome
  symmetry : ∀ {n} t (a b : Tower.Tm n), (raw.symmetry t a b).isSome
  transitivity : ∀ {n} t (a b c : Tower.Tm n), (raw.transitivity t a b c).isSome
  propositionExtensionality : ∀ {n} (a b c d : Tower.Tm n),
    (raw.propositionExtensionality a b c d).isSome
  propositionForward : ∀ {n} (a : Tower.Tm n), (raw.propositionForward a).isSome
  functionCongruence : ∀ {n} t (a b c : Tower.Tm n), (raw.functionCongruence t a b c).isSome
  argumentCongruence : ∀ {n} t (a b c : Tower.Tm n), (raw.argumentCongruence t a b c).isSome
  functionExtensionality : ∀ {n} (a b c d e : Tower.Tm n),
    (raw.functionExtensionality a b c d e).isSome

private theorem bind_total {α β : Type} {input : Option α} {next : α → Option β}
    (available : input.isSome) (continued : ∀ value, (next value).isSome) :
    (input.bind next).isSome := by
  cases input with
  | none => contradiction
  | some value => exact continued value

theorem compile_core_isSome (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    (total : operations.raw.Total)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ) (core : IsCoreProof source)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin Δ.length → Tower.Tm n) :
    (compile signature proofName operations source objects hypotheses).isSome := by
  have representTotal : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base}
      (term : HOL.Term Const Γ τ), IsCore term → (represent signature term).isSome := by
    intro Γ τ term supported
    obtain ⟨out, success⟩ := HOLImpredicativeRepresentation.represent_core signature term supported
    simp [success]
  induction source generalizing n <;>
    simp only [IsCoreProof] at core <;>
    simp only [compile] <;>
    repeat' first
        | exact core.elim
        | apply bind_total
        | intro value
        | assumption
        | exact Bool.true_eq_true
        | apply representTotal
        | apply total.reflexivity
        | apply total.symmetry
        | apply total.transitivity
        | apply total.propositionExtensionality
        | apply total.propositionForward
        | apply total.functionCongruence
        | apply total.argumentCongruence
        | apply total.functionExtensionality
        | (rcases core with ⟨coreLeft, core⟩)
        | solve_by_elim

/-- Every core proof modulo definitional conversion compiles. -/
theorem compileModulo_core_isSome (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)}
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntaxModulo equations Δ φ) (core : IsCoreProofModulo source)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin Δ.length → Tower.Tm n) :
    (Modulo.compileModulo signature source objects hypotheses).isSome := by
  have representTotal : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base}
      (term : HOL.Term Const Γ τ), IsCore term → (represent signature term).isSome := by
    intro Γ τ term supported
    obtain ⟨out, success⟩ := HOLImpredicativeRepresentation.represent_core signature term supported
    simp [success]
  induction source generalizing n with
  | hyp occurrence => simp [Modulo.compileModulo]
  | impI body ih =>
      obtain ⟨premise, coreBody⟩ := core
      simp only [Modulo.compileModulo]
      exact bind_total (representTotal _ premise) fun _ =>
        bind_total (ih coreBody _ _) fun _ => rfl
  | impE function argument ihFunction ihArgument =>
      obtain ⟨coreFunction, coreArgument⟩ := core
      simp only [Modulo.compileModulo]
      exact bind_total (ihFunction coreFunction _ _) fun _ =>
        bind_total (ihArgument coreArgument _ _) fun _ => rfl
  | allI body ih =>
      simp only [Modulo.compileModulo]
      exact bind_total (ih core _ _) fun _ => rfl
  | allE term function ih =>
      obtain ⟨coreTerm, coreFunction⟩ := core
      simp only [Modulo.compileModulo]
      exact bind_total (representTotal _ coreTerm) fun _ =>
        bind_total (ih coreFunction _ _) fun _ => rfl
  | convert _ proof ih =>
      simp only [Modulo.compileModulo]
      exact ih core _ _

#print axioms compile_core_isSome

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
