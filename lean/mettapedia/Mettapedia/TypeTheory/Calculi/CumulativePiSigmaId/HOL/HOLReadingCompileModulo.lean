import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingCompile

/-!
# The generic proof compiler in the selected typed judgment

The generic compiler `Modulo.compileModulo` reads a declared logical signature
only through its symbols: implication, the quantifier and the equality at each
type, and the constants. A reading of the signature in a code package
*agrees* with it when it names the same symbols (`HOLReading.Agrees`). Then

* every term the reading reads is the signature's representation of it
  (`Agrees.term_represent`), and every proof the reading compiles is compiled
  by `compileModulo` to the same term (`Agrees.compile_compileModulo`);
* **licensing** (`Laws.compileModulo_typedO`): such a term is typed in the
  selected judgment of the reading's package, at the decoding of the code of
  its conclusion. So the output of `compileModulo`, whose typing theorem
  `Modulo.compileModulo_typed` is stated for the formation-sensitive judgment
  of an operation algebra's target, is also a term of the package on which the
  metatheory is proved;
* for a reading that interprets every constant, the two compilers are equal
  (`Agrees.compileModulo_eq`), and every successful run of `compileModulo` is
  typed (`Laws.compileModulo_typedO_of_total`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace HOLReading

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FormationSensitiveHOLInterface (LogicalSignature represent variableIndex represent_app
  represent_lam represent_eq represent_imp represent_all)
open HOLNativeGenericProofCompiler (Modulo.compileModulo)
open Mettapedia.Logic

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- A reading agrees with a declared logical signature when it reads the
signature's own symbols. -/
structure Agrees (ρ : HOLReading Tower.Head Base Const) (sig : LogicalSignature Base Const) :
    Prop where
  implication : sig.implication = .const ρ.codes.imp
  universal : ∀ τ, sig.universal τ = .const (ρ.allName τ)
  equality : ∀ τ, sig.equality τ = .const (ρ.eqName τ)
  constant : ∀ {τ : HOL.Ty Base} (c : Const τ) {t : Tower.Tm 0}, ρ.constant c = some t →
    sig.constant c = t

theorem varIndex_eq_variableIndex :
    ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (i : HOL.Var Γ τ), varIndex i = variableIndex i
  | _, _, .vz => rfl
  | _, _, .vs i => congrArg Fin.succ (varIndex_eq_variableIndex i)

namespace Agrees

variable {ρ : HOLReading Tower.Head Base Const} {sig : LogicalSignature Base Const}
  (A : ρ.Agrees sig)
include A

/-- A read term is the signature's representation of it. -/
theorem term_represent : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {t : HOL.Term Const Γ τ}
    {out : Tower.Tm Γ.length}, ρ.term t = some out → represent sig t = some out
  | _, _, .var i, _, h => by
      cases h
      simp only [represent, varIndex_eq_variableIndex]
  | _, _, .const c, _, h => by
      obtain ⟨t0, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [represent, A.constant c ht]
  | _, _, .app f a, _, h => by
      obtain ⟨f', a', hf, ha, rfl⟩ := term_app h
      exact represent_app sig f a (term_represent hf) (term_represent ha)
  | _, _, .lam b, _, h => by
      obtain ⟨b', hb, rfl⟩ := term_lam h
      exact represent_lam sig b (term_represent hb)
  | _, _, .imp p q, _, h => by
      obtain ⟨p', q', hp, hq, rfl⟩ := term_imp h
      rw [represent_imp, term_represent hp, term_represent hq, A.implication]
      rfl
  | _, _, .all b, _, h => by
      obtain ⟨b', hb, rfl⟩ := term_all h
      rw [represent_all, term_represent hb, A.universal]
      rfl
  | _, _, .eq l r, _, h => by
      obtain ⟨l', r', hl, hr, rfl⟩ := term_eq h
      rw [represent_eq sig l r (term_represent hl) (term_represent hr), A.equality]
      rfl
  | _, _, .top, _, h | _, _, .bot, _, h | _, _, .and _ _, _, h | _, _, .or _ _, _, h
  | _, _, .not _, _, h | _, _, .ex _, _, h => by cases h

/-- A proof the reading compiles is compiled by `compileModulo` to the same
term. -/
theorem compile_compileModulo {eqs : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo eqs Δ φ) :
    ∀ {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n)
      {out : Tower.Tm n}, ρ.compile d objects hyps = some out →
        Modulo.compileModulo sig d objects hyps = some out := by
  induction d with
  | hyp i =>
      intro n objects hyps out h
      exact h
  | @impI Γ Δ p q body ih =>
      intro n objects hyps out h
      cases hp : ρ.term p with
      | none => simp [compile, hp] at h
      | some pc =>
          cases hb : ρ.compile body (fun i => Presentation.rename wk (objects i))
              (Fin.cases (.var 0) (fun i => Presentation.rename wk (hyps i))) with
          | none => simp [compile, hp, hb] at h
          | some b =>
              simp [compile, hp, hb] at h
              subst h
              simp [Modulo.compileModulo, A.term_represent hp, ih _ _ hb]
  | impE function argument ihf iha =>
      intro n objects hyps out h
      cases hf : ρ.compile function objects hyps with
      | none => simp [compile, hf] at h
      | some f =>
          cases ha : ρ.compile argument objects hyps with
          | none => simp [compile, hf, ha] at h
          | some a =>
              simp [compile, hf, ha] at h
              subst h
              simp [Modulo.compileModulo, ihf _ _ hf, iha _ _ ha]
  | allI body ih =>
      intro n objects hyps out h
      cases hb : ρ.compile body (liftSub objects)
          (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) with
      | none => simp [compile, hb] at h
      | some b =>
          simp [compile, hb] at h
          subst h
          simp [Modulo.compileModulo, ih _ _ hb]
  | allE t function ih =>
      intro n objects hyps out h
      cases ht : ρ.term t with
      | none => simp [compile, ht] at h
      | some tc =>
          cases hf : ρ.compile function objects hyps with
          | none => simp [compile, ht, hf] at h
          | some f =>
              simp [compile, ht, hf] at h
              subst h
              simp [Modulo.compileModulo, A.term_represent ht, ih _ _ hf]
  | convert _ inner ih =>
      intro n objects hyps out h
      exact ih objects hyps h

/-- Under a total reading, reading is representation. -/
theorem term_eq_represent (T : ρ.Total) :
    ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ),
      ρ.term t = represent sig t
  | _, _, .var i => by simp only [term, represent, varIndex_eq_variableIndex]
  | _, _, .const c => by
      obtain ⟨t0, ht⟩ := Option.isSome_iff_exists.mp (T c)
      simp only [term, represent, ht, A.constant c ht, Option.map_some]
  | _, _, .app f a => by
      simp only [term, represent, ← term_eq_represent T f, ← term_eq_represent T a]
      cases ρ.term f <;> cases ρ.term a <;> rfl
  | _, _, .lam b => by
      simp only [term, represent, ← term_eq_represent T b]
  | _, _, .imp p q => by
      rw [term, represent_imp, ← term_eq_represent T p, ← term_eq_represent T q, A.implication]
      cases ρ.term p <;> cases ρ.term q <;> rfl
  | _, _, .all b => by
      rw [term, represent_all, ← term_eq_represent T b, A.universal]
      cases ρ.term b <;> rfl
  | _, _, .eq l r => by
      simp only [term, represent, ← term_eq_represent T l, ← term_eq_represent T r, A.equality]
      cases ρ.term l <;> cases ρ.term r <;> rfl
  | _, _, .top | _, _, .bot | _, _, .and _ _ | _, _, .or _ _ | _, _, .not _
  | _, _, .ex _ => rfl

/-- Under a total reading, the reading's compiler is `compileModulo`. -/
theorem compileModulo_eq (T : ρ.Total) {eqs : List (HOL.DefiningEquation Const)}
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo eqs Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hyps : Fin Δ.length → Tower.Tm n) :
    Modulo.compileModulo sig d objects hyps = ρ.compile d objects hyps := by
  induction d generalizing n with
  | hyp i => rfl
  | impI body ih =>
      simp only [Modulo.compileModulo, compile, ih, A.term_eq_represent T]
  | impE function argument ihf iha =>
      simp only [Modulo.compileModulo, compile, ihf, iha]
  | allI body ih =>
      simp only [Modulo.compileModulo, compile, ih]
  | allE t function ih =>
      simp only [Modulo.compileModulo, compile, ih, A.term_eq_represent T]
  | convert _ inner ih => exact ih objects hyps

end Agrees

namespace Laws

variable {ρ : HOLReading Tower.Head Base Const} {sig : LogicalSignature Base Const}
  {eqs : List (HOL.DefiningEquation Const)}

/-- **Licensing.** A proof whose articles stay inside the read terms, compiled
by the reading, is compiled by `compileModulo` to the same term, and that term
is typed in the selected judgment of the reading's package at the decoding of
the code of the conclusion, which is also the signature's representation of
it. -/
theorem compileModulo_typedO (L : ρ.Laws) (R : ρ.Realizes eqs) (A : ρ.Agrees sig)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    {d : HOL.ProofSyntaxModulo eqs Δ φ} (articles : ρ.ArticlesRead eqs d) {n : Nat}
    {target : Tower.Ctx n} {objects : Sub Tower.Head Γ.length n}
    {hyps : Fin Δ.length → Tower.Tm n}
    (objectsTyped : SubstMor ρ.rules (ρ.objCtx Γ) target objects)
    (hypsTyped : ∀ i, ∃ c, ρ.term (Δ.get i) = some c ∧
      Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c)))
    {out : Tower.Tm n} (success : ρ.compile d objects hyps = some out) :
    Modulo.compileModulo sig d objects hyps = some out ∧
      ∃ code, represent sig φ = some code ∧ ρ.term φ = some code ∧
        Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) := by
  obtain ⟨code, hcode, typed⟩ := L.compile_typed R articles objectsTyped hypsTyped success
  exact ⟨A.compile_compileModulo d objects hyps success, code, A.term_represent hcode, hcode,
    typed⟩

/-- **Licensing under a total reading**: every successful run of
`compileModulo` is typed in the selected judgment. -/
theorem compileModulo_typedO_of_total (L : ρ.Laws) (R : ρ.Realizes eqs) (A : ρ.Agrees sig)
    (T : ρ.Total) {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo eqs Δ φ) {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head Γ.length n} {hyps : Fin Δ.length → Tower.Tm n}
    (objectsTyped : SubstMor ρ.rules (ρ.objCtx Γ) target objects)
    (hypsTyped : ∀ i, ∃ c, represent sig (Δ.get i) = some c ∧
      Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c)))
    {out : Tower.Tm n} (success : Modulo.compileModulo sig d objects hyps = some out) :
    ∃ code, represent sig φ = some code ∧
      Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) := by
  rw [A.compileModulo_eq T] at success
  obtain ⟨code, hcode, typed⟩ := L.compile_typed_of_total R T d objectsTyped
    (fun i => by simpa only [A.term_eq_represent T] using hypsTyped i) success
  exact ⟨code, A.term_represent hcode, typed⟩

end Laws

end HOLReading

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
