import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingCompile
import Mettapedia.Logic.HOL.ImpredicativeProofModulo

/-!
# The derived connectives through a reading

A reading declines the connectives `⊤ ⊥ ∧ ∨ ¬ ∃`. Elaborated by their
impredicative definitions (`HOL.ImpredicativeConnectives.expandInline`), they
are read as codes built from `imp` and the quantifier `all@prop` over codes:

* `⊤` as `∀c. c ⇒ c` and `⊥` as `∀c. c` (`topCode`, `botCode`);
* `p ∧ q` as `∀c. (p ⇒ q ⇒ c) ⇒ c` and `p ∨ q` as `∀c. (p ⇒ c) ⇒ (q ⇒ c) ⇒ c`
  (`andCode`, `orCode`);
* `¬p` as `p ⇒ ⊥` and `∃x : A. b` as `∀c. (∀x : A. b ⇒ c) ⇒ c` (`exCode`).

No constant is added to the package and no decoding step is added: the
connectives are definitions, and their codes are codes of the package
(`term_expandInline_and`, …, `term_typed`). A reading that interprets every
constant reads every elaborated term (`term_expandInline_isSome`).

**Proofs.** The elaboration `expandProofModulo?` of a retained proof lands in
the proofs with core premises and reflexive retyping steps (`Elaborated`). For
those:

* every retyping step stays inside the read terms, for every reading
  (`ArticlesRead.of_elaborated`), so the typing theorem of the compiler applies
  with no side condition on the equations (`Laws.compile_typed_of_elaborated`);
* under a reading that interprets every constant, compilation succeeds
  (`compile_isSome_of_isCore`; exactly on the core proofs,
  `compile_isSome_iff_isCore`).

Together (`Laws.expandProofModulo?_compiles_typed`): every retained proof of
the connective fragment compiles, under a total constant reading, to a term of
the selected judgment at the decoding of the code of its expanded conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace HOLReading

open Normalization
open Mettapedia.Logic
open Mettapedia.Logic.HOL.ImpredicativeConnectives

universe u v

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-! ## The codes of the connectives -/

section Codes

variable (ρ : HOLReading Head Base Const) {n : Nat}

/-- `⊤` as the code `∀c. c ⇒ c`. -/
def topCode : Tm Head n := ρ.allOf .prop (.lam (ρ.impOf (.var 0) (.var 0)))

/-- `⊥` as the code `∀c. c`. -/
def botCode : Tm Head n := ρ.allOf .prop (.lam (.var 0))

/-- `p ∧ q` as the code `∀c. (p ⇒ q ⇒ c) ⇒ c`. -/
def andCode (p q : Tm Head n) : Tm Head n :=
  ρ.allOf .prop (.lam (ρ.impOf (ρ.impOf (Presentation.rename wk p)
    (ρ.impOf (Presentation.rename wk q) (.var 0))) (.var 0)))

/-- `p ∨ q` as the code `∀c. (p ⇒ c) ⇒ (q ⇒ c) ⇒ c`. -/
def orCode (p q : Tm Head n) : Tm Head n :=
  ρ.allOf .prop (.lam (ρ.impOf (ρ.impOf (Presentation.rename wk p) (.var 0))
    (ρ.impOf (ρ.impOf (Presentation.rename wk q) (.var 0)) (.var 0))))

/-- `∃x : τ. b` as the code `∀c. (∀x : τ. b ⇒ c) ⇒ c`. -/
def exCode (τ : HOL.Ty Base) (b : Tm Head (n + 1)) : Tm Head n :=
  ρ.allOf .prop (.lam (ρ.impOf (ρ.allOf τ (.lam (ρ.impOf (Presentation.rename (liftRen wk) b)
    (.var 1)))) (.var 0)))

end Codes

/-! ## The reading of elaborated terms -/

section Terms

variable (ρ : HOLReading Head Base Const) {Γ : HOL.Ctx Base}

theorem term_truth : ρ.term (truth : HOL.Formula Const Γ) = some ρ.topCode := rfl

theorem term_falsity : ρ.term (falsity : HOL.Formula Const Γ) = some ρ.botCode := rfl

theorem term_conjunctionFormula {p q : HOL.Formula Const Γ} {p' q' : Tm Head Γ.length}
    (hp : ρ.term p = some p') (hq : ρ.term q = some q') :
    ρ.term (conjunctionFormula p q) = some (ρ.andCode p' q') := by
  unfold conjunctionFormula
  simp only [term, ρ.term_weaken, hp, hq, Option.map_some]
  rfl

theorem term_disjunctionFormula {p q : HOL.Formula Const Γ} {p' q' : Tm Head Γ.length}
    (hp : ρ.term p = some p') (hq : ρ.term q = some q') :
    ρ.term (disjunctionFormula p q) = some (ρ.orCode p' q') := by
  unfold disjunctionFormula
  simp only [term, ρ.term_weaken, hp, hq, Option.map_some]
  rfl

theorem term_existentialInline {σ : HOL.Ty Base} {b : HOL.Formula Const (σ :: Γ)}
    {b' : Tm Head (Γ.length + 1)} (hb : ρ.term b = some b') :
    ρ.term (existentialInline b) = some (ρ.exCode σ b') := by
  have renamed : ρ.term (HOL.rename (HOL.Rename.lift (HOL.Rename.weaken (σ := .prop))) b) =
      some (Presentation.rename (liftRen wk) b') := by
    rw [ρ.term_rename (HOL.Rename.lift HOL.Rename.weaken) (liftRen wk)
      (fun i => by cases i <;> rfl), hb]
    rfl
  unfold existentialInline
  simp only [term, renamed]
  rfl

theorem term_expandInline_top :
    ρ.term (expandInline (.top : HOL.Formula Const Γ)) = some ρ.topCode :=
  rfl

theorem term_expandInline_bot :
    ρ.term (expandInline (.bot : HOL.Formula Const Γ)) = some ρ.botCode :=
  rfl

theorem term_expandInline_and (p q : HOL.Formula Const Γ) :
    ρ.term (expandInline (.and p q)) =
      both ρ.andCode (ρ.term (expandInline p)) (ρ.term (expandInline q)) := by
  cases hp : ρ.term (expandInline p) with
  | none =>
      simp only [expandInline, conjunctionFormula, term, ρ.term_weaken, hp, Option.map_none]
      rfl
  | some p' =>
      cases hq : ρ.term (expandInline q) with
      | none =>
          simp only [expandInline, conjunctionFormula, term, ρ.term_weaken, hq, Option.map_none]
          cases ρ.term (expandInline p) <;> rfl
      | some q' => exact ρ.term_conjunctionFormula hp hq

theorem term_expandInline_or (p q : HOL.Formula Const Γ) :
    ρ.term (expandInline (.or p q)) =
      both ρ.orCode (ρ.term (expandInline p)) (ρ.term (expandInline q)) := by
  cases hp : ρ.term (expandInline p) with
  | none =>
      simp only [expandInline, disjunctionFormula, term, ρ.term_weaken, hp, Option.map_none]
      rfl
  | some p' =>
      cases hq : ρ.term (expandInline q) with
      | none =>
          simp only [expandInline, disjunctionFormula, term, ρ.term_weaken, hq, Option.map_none]
          cases ρ.term (expandInline p) <;> rfl
      | some q' => exact ρ.term_disjunctionFormula hp hq

theorem term_expandInline_not (p : HOL.Formula Const Γ) :
    ρ.term (expandInline (.not p)) = (ρ.term (expandInline p)).map (ρ.impOf · ρ.botCode) := by
  cases hp : ρ.term (expandInline p) <;> simp only [expandInline, term, hp] <;> rfl

theorem term_expandInline_ex {σ : HOL.Ty Base} (b : HOL.Formula Const (σ :: Γ)) :
    ρ.term (expandInline (.ex b)) = (ρ.term (expandInline b)).map (ρ.exCode σ) := by
  cases hb : ρ.term (expandInline b) with
  | none =>
      have renamed : ρ.term (HOL.rename (HOL.Rename.lift (HOL.Rename.weaken (σ := .prop)))
          (expandInline b)) = none := by
        rw [ρ.term_rename (HOL.Rename.lift HOL.Rename.weaken) (liftRen wk)
          (fun i => by cases i <;> rfl),
          hb]
        rfl
      simp only [expandInline, existentialInline, term, renamed, Option.map_none]
      rfl
  | some b' => exact ρ.term_existentialInline hb

/-- **Totality on elaborated terms.** A reading that interprets every constant
reads every elaborated term. -/
theorem term_expandInline_isSome {ρ : HOLReading Head Base Const} (T : ρ.Total) {τ : HOL.Ty Base}
    (t : HOL.Term Const Γ τ) : (ρ.term (expandInline t)).isSome :=
  term_isSome_of_isCore T _ (expandInline_isCore t)

end Terms

/-! ## Compilation of core proofs -/

section Compile

variable {ρ : HOLReading Head Base Const} {eqs : List (HOL.DefiningEquation Const)}

private theorem bind_isSome {α β : Type} {input : Option α} {next : α → Option β}
    (available : input.isSome) (continued : ∀ value, (next value).isSome) :
    (input.bind next).isSome := by
  cases input with
  | none => contradiction
  | some value => exact continued value

private theorem isSome_of_bind_isSome {α β : Type} {input : Option α} {next : α → Option β}
    (h : (input.bind next).isSome) : input.isSome := by
  cases input with
  | none => contradiction
  | some _ => rfl

private theorem next_isSome_of_bind {α β : Type} {input : Option α} {next : α → Option β}
    {value : α} (h : (input.bind next).isSome) (hv : input = some value) :
    (next value).isSome := by
  subst hv
  exact h

/-- Under a reading that interprets every constant, every core proof modulo
conversion compiles. -/
theorem compile_isSome_of_isCore (T : ρ.Total) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo eqs Δ φ)
    (core : IsCoreProofModulo d) {n : Nat} (objects : Sub Head Γ.length n)
    (hyps : Fin Δ.length → Tm Head n) : (ρ.compile d objects hyps).isSome := by
  have read : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ), IsCore t →
      (ρ.term t).isSome := fun t h => term_isSome_of_isCore T t ((isCore_eq_true_iff t).mpr h)
  induction d generalizing n with
  | hyp => rfl
  | impI body ih =>
      obtain ⟨premise, coreBody⟩ := core
      exact bind_isSome (read _ premise) fun _ => bind_isSome (ih coreBody _ _) fun _ => rfl
  | impE function argument ihf iha =>
      obtain ⟨coreFunction, coreArgument⟩ := core
      exact bind_isSome (ihf coreFunction _ _) fun _ =>
        bind_isSome (iha coreArgument _ _) fun _ => rfl
  | allI body ih => exact bind_isSome (ih core _ _) fun _ => rfl
  | allE t function ih =>
      obtain ⟨coreTerm, coreFunction⟩ := core
      exact bind_isSome (read _ coreTerm) fun _ => bind_isSome (ih coreFunction _ _) fun _ => rfl
  | convert _ inner ih => exact ih core objects hyps

/-- **Exact domain** of compilation under a reading that interprets every
constant: a proof modulo conversion compiles exactly when it is core. -/
theorem compile_isSome_iff_isCore (T : ρ.Total) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo eqs Δ φ)
    {n : Nat} (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n) :
    (ρ.compile d objects hyps).isSome ↔ IsCoreProofModulo d := by
  refine ⟨fun success => ?_, fun core => compile_isSome_of_isCore T d core objects hyps⟩
  have core : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {t : HOL.Term Const Γ τ},
      (ρ.term t).isSome → IsCore t := fun {_ _ t} h => by
    obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp h
    exact (isCore_eq_true_iff t).mp (isCore_of_term ht)
  induction d generalizing n with
  | hyp => trivial
  | @impI Γ Δ premise ψ body ih =>
      have first := isSome_of_bind_isSome success
      obtain ⟨p', hp⟩ := Option.isSome_iff_exists.mp first
      have rest := next_isSome_of_bind success hp
      exact ⟨core first, ih _ _ (isSome_of_bind_isSome rest)⟩
  | impE function argument ihf iha =>
      have first := isSome_of_bind_isSome success
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp first
      have rest := next_isSome_of_bind success hf
      exact ⟨ihf _ _ first, iha _ _ (isSome_of_bind_isSome rest)⟩
  | allI body ih => exact ih _ _ (isSome_of_bind_isSome success)
  | allE t function ih =>
      have first := isSome_of_bind_isSome success
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp first
      have rest := next_isSome_of_bind success ht
      exact ⟨core first, ih _ _ (isSome_of_bind_isSome rest)⟩
  | convert _ inner ih => exact ih objects hyps success

end Compile

/-! ## Elaborated proofs -/

section Elaborated

variable {ρ : HOLReading Head Base Const} {eqs : List (HOL.DefiningEquation Const)}

/-- The retyping steps of an elaborated proof stay inside the read terms, for
every reading. -/
theorem ArticlesRead.of_elaborated {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} {d : HOL.ProofSyntaxModulo eqs Δ φ} (e : Elaborated d) :
    ρ.ArticlesRead eqs d := by
  induction e with
  | hyp i => exact .hyp i
  | impI _ _ ih => exact .impI ih
  | impE _ _ ihf iha => exact .impE ihf iha
  | allI _ ih => exact .allI ih
  | allE _ _ ih => exact .allE _ ih
  | convert same _ ih =>
      subst same
      exact .convert (.refl _) ih

/-- An elaborated proof over one list of equations has a twin over any other
list, elaborated and compiled to the same terms. -/
theorem compile_retarget_of_elaborated {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} {d : HOL.ProofSyntaxModulo eqs Δ φ} (e : Elaborated d)
    (eqs' : List (HOL.DefiningEquation Const)) :
    ∃ d' : HOL.ProofSyntaxModulo eqs' Δ φ, Elaborated d' ∧
      ∀ {n : Nat} (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n),
        ρ.compile d' objects hyps = ρ.compile d objects hyps := by
  induction e with
  | hyp i => exact ⟨.hyp i, .hyp i, fun _ _ => rfl⟩
  | impI premise _ ih =>
      obtain ⟨b, eb, same⟩ := ih
      refine ⟨.impI b, .impI premise eb, fun objects hyps => ?_⟩
      simp only [compile, same]
  | impE _ _ ihf iha =>
      obtain ⟨f, ef, sameF⟩ := ihf
      obtain ⟨a, ea, sameA⟩ := iha
      refine ⟨.impE f a, .impE ef ea, fun objects hyps => ?_⟩
      simp only [compile, sameF, sameA]
  | allI _ ih =>
      obtain ⟨b, eb, same⟩ := ih
      refine ⟨.allI b, .allI eb, fun objects hyps => ?_⟩
      simp only [compile, same]
  | allE core _ ih =>
      obtain ⟨f, ef, same⟩ := ih
      refine ⟨.allE _ f, .allE core ef, fun objects hyps => ?_⟩
      simp only [compile, same]
  | convert same _ ih =>
      subst same
      obtain ⟨d', e', compiled⟩ := ih
      exact ⟨.convert (.refl _) d', .convert rfl e', fun objects hyps => compiled objects hyps⟩

end Elaborated

/-! ## Typing -/

theorem realizes_nil (ρ : HOLReading Head Base Const) : ρ.Realizes [] :=
  fun _ listed => absurd listed List.not_mem_nil

namespace Laws

variable {ρ : HOLReading Head Base Const} (L : ρ.Laws)
include L

/-- **Typing of elaborated proofs**, with no condition on the equations: a
successful compilation of an elaborated proof is typed, in the selected
judgment, at the decoding of the code of its conclusion. -/
theorem compile_typed_of_elaborated {eqs : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    {d : HOL.ProofSyntaxModulo eqs Δ φ} (e : Elaborated d) {n : Nat} {target : Ctx Head n}
    {objects : Sub Head Γ.length n} {hyps : Fin Δ.length → Tm Head n}
    (objectsTyped : SubstMor ρ.rules (ρ.objCtx Γ) target objects)
    (hypsTyped : ∀ i, ∃ c, ρ.term (Δ.get i) = some c ∧
      Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c)))
    {out : Tm Head n} (success : ρ.compile d objects hyps = some out) :
    ∃ code, ρ.term φ = some code ∧
      Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) := by
  obtain ⟨d', e', same⟩ := compile_retarget_of_elaborated (ρ := ρ) e []
  rw [← same] at success
  exact L.compile_typed ρ.realizes_nil (ArticlesRead.of_elaborated e') objectsTyped hypsTyped
    success

/-- **Typing on the expanded image.** A successful compilation of an
elaborated retained proof is typed at the decoding of the code of the expanded
conclusion. This holds for every reading, total or not. -/
theorem expandProofModulo?_typed {eqs : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    {proof : HOL.ProofSyntax Const Δ φ}
    {d : HOL.ProofSyntaxModulo eqs (Δ.map expandInline) (expandInline φ)}
    (expanded : expandProofModulo? proof = some d) {n : Nat} {target : Ctx Head n}
    {objects : Sub Head Γ.length n} {hyps : Fin (Δ.map expandInline).length → Tm Head n}
    (objectsTyped : SubstMor ρ.rules (ρ.objCtx Γ) target objects)
    (hypsTyped : ∀ i, ∃ c, ρ.term ((Δ.map expandInline).get i) = some c ∧
      Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c)))
    {out : Tm Head n} (success : ρ.compile d objects hyps = some out) :
    ∃ code, ρ.term (expandInline φ) = some code ∧
      Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) :=
  L.compile_typed_of_elaborated (expandProofModulo?_elaborated proof expanded) objectsTyped
    hypsTyped success

/-- **Compile totality and typing on the expanded image.** Under a reading that
interprets every constant, every retained proof of the connective fragment,
once elaborated, compiles, and its compilation is typed at the decoding of the
code of the expanded conclusion. -/
theorem expandProofModulo?_compiles_typed (T : ρ.Total) {eqs : List (HOL.DefiningEquation Const)}
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    {proof : HOL.ProofSyntax Const Δ φ}
    {d : HOL.ProofSyntaxModulo eqs (Δ.map expandInline) (expandInline φ)}
    (expanded : expandProofModulo? proof = some d) {n : Nat} {target : Ctx Head n}
    {objects : Sub Head Γ.length n} {hyps : Fin (Δ.map expandInline).length → Tm Head n}
    (objectsTyped : SubstMor ρ.rules (ρ.objCtx Γ) target objects)
    (hypsTyped : ∀ i, ∃ c, ρ.term ((Δ.map expandInline).get i) = some c ∧
      Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c))) :
    ∃ out, ρ.compile d objects hyps = some out ∧
      ∃ code, ρ.term (expandInline φ) = some code ∧
      Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) := by
  obtain ⟨out, success⟩ := Option.isSome_iff_exists.mp
    (compile_isSome_of_isCore T d (expandProofModulo?_isCore expanded) objects hyps)
  exact ⟨out, success, L.expandProofModulo?_typed expanded objectsTyped hypsTyped success⟩

end Laws

end HOLReading

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
