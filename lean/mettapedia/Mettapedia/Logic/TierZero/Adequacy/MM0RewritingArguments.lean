import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingJudgments

/-!
# Decoding and admitting the argument columns of a native MM0 step

Only a finite argument tuple is decoded. The check validates the object
representation, sorting and support constraints; it never evaluates proof
objects or asks whether a statement is derivable.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

def readArgument (context : Context) (assignment : Subst Nat Tm) (index : Nat) : Option Preterm :=
  (assignment index).bind (decodeExact context)

theorem readArgument_iff (context : Context) (assignment : Subst Nat Tm) (index : Nat) (expression : Preterm) :
    readArgument context assignment index = some expression ↔
      assignment index = some (encode context expression) := by
  cases assigned : assignment index with
  | none => simp [readArgument, assigned]
  | some term => simp [readArgument, assigned, decodeExact_iff]

def readArguments (context : Context) (arity : Nat) (assignment : Subst Nat Tm) : Option (List Preterm) :=
  (List.range arity).mapM (readArgument context assignment)

private theorem collect_iff {A B : Type} (f : A → Option B) (xs : List A) (ys : List B) :
    xs.mapM f = some ys ↔ List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil =>
          cases head : f x <;> cases tail : xs.mapM f <;> simp [List.mapM_cons, head, tail]
      | cons y ys =>
          cases head : f x <;> cases tail : xs.mapM f <;>
            simp [List.mapM_cons, head, tail, ← ih]

theorem readArguments_iff (context : Context) (arity : Nat) (assignment : Subst Nat Tm) (arguments : List Preterm) :
    readArguments context arity assignment = some arguments ↔
      arguments.length = arity ∧
        ∀ index < arity, assignment index = expressionAssignment context arguments index := by
  rw [readArguments, collect_iff, List.forall₂_iff_get]
  simp only [List.length_range]
  constructor
  · rintro ⟨lengths, columns⟩
    refine ⟨lengths.symm, ?_⟩
    intro index inside
    have argumentInside : index < arguments.length := lengths ▸ inside
    have column := columns index inside argumentInside
    simp only [List.get_eq_getElem, List.getElem_range] at column
    have assigned := (readArgument_iff context assignment index _).mp column
    simpa [expressionAssignment, List.getElem?_eq_getElem argumentInside] using assigned
  · rintro ⟨lengths, columns⟩
    refine ⟨lengths.symm, ?_⟩
    intro index inside argumentInside
    simp only [List.get_eq_getElem, List.getElem_range]
    apply (readArgument_iff context assignment index _).mpr
    simpa [expressionAssignment, List.getElem?_eq_getElem argumentInside] using columns index inside

theorem readArguments_encoded (context : Context) (arguments : List Preterm) :
    readArguments context arguments.length (expressionAssignment context arguments) = some arguments :=
  (readArguments_iff _ _ _ _).mpr ⟨rfl, fun _ _ => rfl⟩

def admitArguments (signature : TermSignature) (formal target : Context)
    (assignment : Subst Nat Tm) : Option (List Preterm) := do
  let arguments ← readArguments target formal.length assignment
  if checkAdmissibleNative [] signature formal target arguments then some arguments else none

theorem admitArguments_iff (signature : TermSignature) (formal target : Context)
    (assignment : Subst Nat Tm) (arguments : List Preterm) :
    admitArguments signature formal target assignment = some arguments ↔
      Substitution.Admissible signature formal target arguments ∧
        ∀ index < formal.length, assignment index = expressionAssignment target arguments index := by
  unfold admitArguments
  cases read : readArguments target formal.length assignment with
  | none =>
      simp only [Option.bind_eq_bind, Option.bind_none, reduceCtorEq, false_iff, not_and]
      intro admitted columns
      have success := (readArguments_iff _ _ _ _).mpr ⟨admitted.length_eq, columns⟩
      rw [read] at success
      cases success
  | some values =>
      have facts := (readArguments_iff _ _ _ _).mp read
      simp only [Option.bind_eq_bind, Option.bind_some]
      change (if checkAdmissibleNative [] signature formal target values = true then some values else none) =
        some arguments ↔ _
      constructor
      · intro checked
        split at checked
        · cases checked
          exact ⟨(checkAdmissibleNative_iff canonical_nil _ _ _ _).mp
            ‹checkAdmissibleNative [] signature formal target arguments = true›, facts.2⟩
        · cases checked
      · rintro ⟨admitted, columns⟩
        have success := (readArguments_iff _ _ _ _).mpr ⟨admitted.length_eq, columns⟩
        have same : values = arguments := Option.some.inj (read.symm.trans success)
        subst values
        exact if_pos ((checkAdmissibleNative_iff canonical_nil _ _ _ _).mpr admitted)

theorem admitted_arguments_supported {sorts : SortSignature} {signature : TermSignature}
    {formal target : Context} {arguments : List Preterm}
    (formed : Context.WellFormed sorts target)
    (admitted : Substitution.Admissible signature formal target arguments) :
    ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true := by
  have typed := admitted.typed
  clear admitted
  induction typed with
  | nil => simp
  | @cons argument binder arguments binders head tail ih =>
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨support, supported⟩ := head.support_exists
        exact encode_supported formed supported
      · exact ih value member

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
