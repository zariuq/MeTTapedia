import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompiler

/-!
# Substitution naturality of the one generic HOL proof compiler

Typing an optional operation does not force its availability or output to
commute with substitution. The local laws below characterize exactly that
extra requirement on the computational algebra. They do not extend the
language core or introduce another compiler. The recursive theorem covers
every retained source constructor, including rejection and nested binders.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler

open Presentation Mettapedia.Logic FormationSensitiveHOLInterface

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Local substitution laws, including preservation of optional availability. -/
structure RawOperations.Natural (raw : RawOperations Base) : Prop where
  reflexivity : ∀ {n m : Nat} (sigma : Sub Tower.Head n m),
    (raw.reflexivity : Option (Tower.Tm m)) = raw.reflexivity.map (subst sigma)
  symmetry : ∀ {n m : Nat} (sigma : Sub Tower.Head n m) (type : HOL.Ty Base)
      (left comparison : Tower.Tm n),
    raw.symmetry type (subst sigma left) (subst sigma comparison) =
      (raw.symmetry type left comparison).map (subst sigma)
  transitivity : ∀ {n m : Nat} (sigma : Sub Tower.Head n m) (type : HOL.Ty Base)
      (left first second : Tower.Tm n),
    raw.transitivity type (subst sigma left) (subst sigma first) (subst sigma second) =
      (raw.transitivity type left first second).map (subst sigma)
  propositionExtensionality : ∀ {n m : Nat} (sigma : Sub Tower.Head n m)
      (left right forward backward : Tower.Tm n),
    raw.propositionExtensionality (subst sigma left) (subst sigma right)
        (subst sigma forward) (subst sigma backward) =
      (raw.propositionExtensionality left right forward backward).map (subst sigma)
  propositionForward : ∀ {n m : Nat} (sigma : Sub Tower.Head n m) (comparison : Tower.Tm n),
    raw.propositionForward (subst sigma comparison) =
      (raw.propositionForward comparison).map (subst sigma)
  functionCongruence : ∀ {n m : Nat} (sigma : Sub Tower.Head n m) (result : HOL.Ty Base)
      (function argument comparison : Tower.Tm n),
    raw.functionCongruence result (subst sigma function) (subst sigma argument)
        (subst sigma comparison) =
      (raw.functionCongruence result function argument comparison).map (subst sigma)
  argumentCongruence : ∀ {n m : Nat} (sigma : Sub Tower.Head n m) (result : HOL.Ty Base)
      (function argument comparison : Tower.Tm n),
    raw.argumentCongruence result (subst sigma function) (subst sigma argument)
        (subst sigma comparison) =
      (raw.argumentCongruence result function argument comparison).map (subst sigma)
  functionExtensionality : ∀ {n m : Nat} (sigma : Sub Tower.Head n m)
      (domain codomain function other pointwise : Tower.Tm n),
    raw.functionExtensionality (subst sigma domain) (subst sigma codomain)
        (subst sigma function) (subst sigma other) (subst sigma pointwise) =
      (raw.functionExtensionality domain codomain function other pointwise).map (subst sigma)

theorem RawOperations.logicalOnly_natural :
    (RawOperations.logicalOnly : RawOperations Base).Natural := by
  constructor <;> intros <;> rfl

/-- Compile after moving the native environment, or move the actual compiler
result: both routes agree, including unsupported operations and source nodes. -/
theorem compile_substitute (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (natural : operations.raw.Natural)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {phi : HOL.Formula Const gamma} (source : HOL.ProofSyntax Const delta phi)
    {n m : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) (sigma : Sub Tower.Head n m) :
    compile signature proofName operations source (fun i => subst sigma (objects i))
        (fun i => subst sigma (hypotheses i)) =
      (compile signature proofName operations source objects hypotheses).map (subst sigma) := by
  induction source generalizing n m with
  | hyp occurrence => rfl
  | @impI gamma delta p q body ih =>
      have obj : (fun i => rename wk (subst sigma (objects i))) =
          (fun i => subst (liftSub sigma) (rename wk (objects i))) := by
        funext i
        simp only [subst_liftSub_wk]
      have hyp : Fin.cases (.var 0) (fun i => rename wk (subst sigma (hypotheses i))) =
          (fun i => subst (liftSub sigma)
            (Fin.cases (.var 0) (fun j => rename wk (hypotheses j)) i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      simp only [compile, obj, hyp]
      erw [ih (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) (liftSub sigma)]
      cases represent signature p <;>
        cases compile signature proofName operations body (fun i => rename wk (objects i))
          (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) <;> rfl
  | impE function argument ihf iha =>
      simp only [compile, ihf, iha]
      cases compile signature proofName operations function objects hypotheses <;>
        cases compile signature proofName operations argument objects hypotheses <;> rfl
  | @allI gamma delta type phi body ih =>
      have obj : liftSub (fun i => subst sigma (objects i)) =
          (fun i => subst (liftSub sigma) (liftSub objects i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      have hyp : (fun i : Fin (HOL.weakenHyps (σ := type) delta).length =>
          rename wk (subst sigma (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) =
          (fun i => subst (liftSub sigma)
            (rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) := by
        funext i
        simp only [subst_liftSub_wk]
      simp only [compile, obj, hyp]
      erw [ih (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) (liftSub sigma)]
      cases compile signature proofName operations body (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) <;> rfl
  | allE term function ih =>
      simp only [compile, ih]
      cases represent signature term with
      | none => rfl
      | some code =>
          cases compile signature proofName operations function objects hypotheses with
          | none => rfl
          | some native => simp [subst, subst_comp]
  | eqRefl term =>
      simp only [compile]
      cases represent signature term <;> first | rfl | exact natural.reflexivity sigma
  | @eqSymm gamma delta type x y comparison ih =>
      simp only [compile, ih]
      cases represent signature x <;> cases represent signature y <;>
        cases compile signature proofName operations comparison objects hypotheses <;>
          first | rfl | (rename_i l r h; simpa using natural.symmetry sigma type (subst objects l) h)
  | @eqTrans gamma delta type x y z first second ihh ihk =>
      simp only [compile, ihh, ihk]
      cases represent signature x <;> cases represent signature y <;> cases represent signature z <;>
        cases compile signature proofName operations first objects hypotheses <;>
        cases compile signature proofName operations second objects hypotheses <;>
          first | rfl | (rename_i l mid r h k; simpa using natural.transitivity sigma type (subst objects l) h k)
  | @eqPropI gamma delta p q forward backward ihf ihb =>
      simp only [compile, ihf, ihb]
      cases represent signature p <;> cases represent signature q <;>
        cases compile signature proofName operations forward objects hypotheses <;>
        cases compile signature proofName operations backward objects hypotheses <;>
          first | rfl | (rename_i l r h k; simpa using
            (natural.propositionExtensionality sigma (subst objects l) (subst objects r) h k))
  | @eqPropEL gamma delta p q comparison ih =>
      simp only [compile, ih]
      cases represent signature p <;> cases represent signature q <;>
        cases compile signature proofName operations comparison objects hypotheses <;>
          first | rfl | (rename_i l r h; simpa using natural.propositionForward sigma h)
  | @eqPropER gamma delta p q comparison ih =>
      simp only [compile, ih]
      cases represent signature p <;> cases represent signature q <;>
        cases compile signature proofName operations comparison objects hypotheses <;>
          try rfl
      rename_i l r h
      change (operations.raw.symmetry HOL.Ty.prop
        (subst (fun i => subst sigma (objects i)) l) (subst sigma h)).bind _ = _
      rw [← subst_comp, natural.symmetry sigma]
      cases reversed : operations.raw.symmetry HOL.Ty.prop (subst objects l) h with
      | none => simp [reversed]
      | some result => simpa [reversed] using natural.propositionForward sigma result
  | @eqApp gamma delta a b f g x comparison ih =>
      simp only [compile, ih]
      cases represent signature f <;> cases represent signature g <;> cases represent signature x <;>
        cases compile signature proofName operations comparison objects hypotheses <;>
          first | rfl | (rename_i funCode other arg h; simpa using
            (natural.functionCongruence sigma b (subst objects funCode) (subst objects arg) h))
  | @eqAppArg gamma delta a b f x y comparison ih =>
      simp only [compile, ih]
      cases represent signature f <;> cases represent signature x <;> cases represent signature y <;>
        cases compile signature proofName operations comparison objects hypotheses <;>
          first | rfl | (rename_i funCode arg other h; simpa using
            (natural.argumentCongruence sigma b (subst objects funCode) (subst objects arg) h))
  | @eqLam gamma delta domain codomain left right comparison ih =>
      have obj : liftSub (fun i => subst sigma (objects i)) =
          (fun i => subst (liftSub sigma) (liftSub objects i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      have hyp : (fun i : Fin (HOL.weakenHyps (σ := domain) delta).length =>
          rename wk (subst sigma (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) =
          (fun i => subst (liftSub sigma)
            (rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) := by
        funext i
        simp only [subst_liftSub_wk]
      simp only [compile, obj, hyp]
      erw [ih (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) (liftSub sigma)]
      cases represent signature left <;> cases represent signature right <;>
        cases compile signature proofName operations comparison (liftSub objects)
          (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) <;>
          try rfl
      rename_i l r h
      simpa [subst]
        using natural.functionExtensionality sigma
          (typeAt signature.types n domain) (typeAt signature.types n codomain)
          (.lam (subst (liftSub objects) l)) (.lam (subst (liftSub objects) r)) (.lam h)
  | @funExt gamma delta domain codomain function other pointwise ih =>
      simp only [compile, ih]
      cases represent signature function <;> cases represent signature other <;>
        cases compile signature proofName operations pointwise objects hypotheses <;>
          first | rfl | (rename_i f g h; simpa using
            (natural.functionExtensionality sigma (typeAt signature.types n domain)
              (typeAt signature.types n codomain) (subst objects f) (subst objects g) h))
  | beta term body =>
      simp only [compile]
      cases represent signature term <;> cases represent signature body <;>
        first | rfl | exact natural.reflexivity sigma
  | @eta gamma delta domain codomain function =>
      simp only [compile]
      cases represent signature function <;> try rfl
      rename_i f
      change (operations.raw.reflexivity : Option (Tower.Tm (m + 1))).bind _ = _
      rw [natural.reflexivity (liftSub sigma)]
      cases (operations.raw.reflexivity : Option (Tower.Tm (n + 1))) <;>
        first | rfl | (rename_i h; simpa [subst, liftSub] using
          (natural.functionExtensionality sigma (typeAt signature.types n domain)
            (typeAt signature.types n codomain)
            (.lam (.app (rename wk (subst objects f)) (.var 0))) (subst objects f) (.lam h)))
  | _ => rfl

#print axioms compile_substitute

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
