import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLReadingCompileModulo
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingIdentity

/-!
# The pointed compiler and the legacy formation-sensitive compiler

The legacy capability record `HOLNativeGenericProofCompiler.RawOperations`
embeds into the typed record `EqualityRaw` by ignoring the endpoints it
withholds (`EqualityRaw.ofLegacy`); function extensionality receives the
carriers of the signature's type interpretation, as the legacy compiler passes
them.

**Where the domains overlap.** For a reading that agrees with the signature
(`HOLReading.Agrees`), the constant-reflexivity embedding of a legacy algebra
compiles every proof without an η node as the legacy compiler does
(`compileP_embed`; one direction for a partial reading,
`compileP_embed_of_success`). At an η node the two differ by design: the
legacy compiler emits function extensionality of pointwise reflexivity, because
untyped conversion does not see η, while the pointed compiler realizes η by
reflexivity. Proofs without reflexivity nodes compile identically under any
typed algebra whose forgetful image is such an embedding
(`compileP_legacy`).

**Licensing** (`Laws.compile_typedO`): when the embedded legacy record is
lawful in the selected judgment, every result of the legacy compiler on a proof
without η nodes is a term of the reading's package at the decoding of the
signature's representation of the conclusion.

**The obstruction** (`identityRaw_not_ofLegacy`): the identity algebra is not
the embedding of any legacy record, because its symmetry depends on the right
endpoint, which the legacy record never receives.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FormationSensitiveHOLInterface (LogicalSignature TypeInterpretation represent typeAt)
open HOLNativeGenericProofCompiler (RawOperations Operations)
open Mettapedia.Logic

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The legacy record as a typed record: the endpoints the legacy record
withholds are ignored, and function extensionality receives the carriers of
the type interpretation. -/
def EqualityRaw.ofLegacy (types : TypeInterpretation Base) (raw : RawOperations Base) :
    EqualityRaw Tower.Head Base where
  reflexivity := raw.reflexivity
  symmetry := fun τ l _ e => raw.symmetry τ l e
  transitivity := fun τ l _ _ e₁ e₂ => raw.transitivity τ l e₁ e₂
  propositionExtensionality := raw.propositionExtensionality
  propositionForward := fun _ _ e => raw.propositionForward e
  functionCongruence := fun _ τ f _ a e => raw.functionCongruence τ f a e
  argumentCongruence := fun _ τ f l _ e => raw.argumentCongruence τ f l e
  functionExtensionality := fun {n} σ τ f g pw =>
    raw.functionExtensionality (typeAt types n σ) (typeAt types n τ) f g pw

theorem EqualityRaw.ofLegacy_logicalOnly (types : TypeInterpretation Base) :
    EqualityRaw.ofLegacy types RawOperations.logicalOnly = EqualityRaw.logicalOnly :=
  rfl

/-- An η node requests reflexivity at a point. -/
theorem exists_pointed_of_eta {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ)
    (m : HOL.ProofSyntax.RuleTag.eta ∈ HOL.ProofSyntax.rules d) :
    ∃ τ, Request.pointed τ ∈ requests d := by
  induction d with
  | eta => exact ⟨_, List.mem_singleton_self _⟩
  | hyp | topI | eqRefl | beta => simp [HOL.ProofSyntax.rules] at m
  | botE p ih | andEL p ih | andER p ih | orIL p ih | orIR p ih | impI p ih | notI p ih
  | allI p ih | allE _ p ih | exI _ p ih =>
      simp only [HOL.ProofSyntax.rules, List.mem_cons, reduceCtorEq, false_or] at m
      exact ih m
  | eqSymm p ih | eqPropEL p ih | eqApp _ p ih | eqAppArg _ p ih | eqLam p ih | funExt p ih =>
      simp only [HOL.ProofSyntax.rules, List.mem_cons, reduceCtorEq, false_or] at m
      obtain ⟨τ, h⟩ := ih m
      exact ⟨τ, List.mem_cons_of_mem _ h⟩
  | eqPropER p ih =>
      simp only [HOL.ProofSyntax.rules, List.mem_cons, reduceCtorEq, false_or] at m
      obtain ⟨τ, h⟩ := ih m
      exact ⟨τ, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)⟩
  | andI p q ihp ihq | impE p q ihp ihq | notE p q ihp ihq | exE p q ihp ihq =>
      simp only [HOL.ProofSyntax.rules, List.mem_cons, List.mem_append, reduceCtorEq,
        false_or] at m
      rcases m with m | m
      · obtain ⟨τ, h⟩ := ihp m
        exact ⟨τ, List.mem_append_left _ h⟩
      · obtain ⟨τ, h⟩ := ihq m
        exact ⟨τ, List.mem_append_right _ h⟩
  | eqTrans p q ihp ihq | eqPropI p q ihp ihq =>
      simp only [HOL.ProofSyntax.rules, List.mem_cons, List.mem_append, reduceCtorEq,
        false_or] at m
      rcases m with m | m
      · obtain ⟨τ, h⟩ := ihp m
        exact ⟨τ, List.mem_cons_of_mem _ (List.mem_append_left _ h)⟩
      · obtain ⟨τ, h⟩ := ihq m
        exact ⟨τ, List.mem_cons_of_mem _ (List.mem_append_right _ h)⟩
  | orE p q r ihp ihq ihr =>
      simp only [HOL.ProofSyntax.rules, List.mem_cons, List.mem_append, reduceCtorEq,
        false_or] at m
      rcases m with (m | m) | m
      · obtain ⟨τ, h⟩ := ihp m
        exact ⟨τ, List.mem_append_left _ (List.mem_append_left _ h)⟩
      · obtain ⟨τ, h⟩ := ihq m
        exact ⟨τ, List.mem_append_left _ (List.mem_append_right _ h)⟩
      · obtain ⟨τ, h⟩ := ihr m
        exact ⟨τ, List.mem_append_right _ h⟩

namespace HOLReading

variable {ρ : HOLReading Tower.Head Base Const} {sig : LogicalSignature Base Const}

/-- **The embedding compiles as before**, for a reading that interprets every
constant: on proofs without an η node, the constant-reflexivity embedding of a
legacy algebra and the legacy compiler give the same result. -/
theorem Agrees.compileP_embed (A : ρ.Agrees sig) (T : ρ.Total) {proofName : DeclName}
    (ops : Operations sig proofName) {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ)
    (noEta : HOL.ProofSyntax.RuleTag.eta ∉ HOL.ProofSyntax.rules d) {n : Nat}
    (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    ρ.compileP (EqualityRaw.ofLegacy sig.types ops.raw).pointedByConstant d objects hyps =
      HOLNativeGenericProofCompiler.compile sig proofName ops d objects hyps := by
  have read : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ),
      ρ.term t = represent sig t := fun t => A.term_eq_represent T t
  induction d generalizing n with
  | hyp => rfl
  | impI body ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
  | impE function argument ihf iha =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile,
        ihf (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_left _ m))),
        iha (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_right _ m)))]
  | allI body ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
  | allE t function ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
  | eqRefl t =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read]
      rfl
  | eqSymm proof ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
      rfl
  | eqTrans first second ihFirst ihSecond =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read,
        ihFirst (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_left _ m))),
        ihSecond (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_right _ m)))]
      rfl
  | eqPropI forward backward ihForward ihBackward =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read,
        ihForward (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_left _ m))),
        ihBackward (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_right _ m)))]
      rfl
  | eqPropEL proof ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
      rfl
  | eqPropER proof ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
      rfl
  | eqApp argument proof ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
      rfl
  | eqAppArg function proof ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
      rfl
  | eqLam proof ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
      rfl
  | funExt proof ih =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read, ih (fun m => noEta (List.mem_cons_of_mem _ m))]
      rfl
  | beta t body =>
      simp only [compileP, HOLNativeGenericProofCompiler.compile, read]
      rfl
  | eta function => exact absurd (List.mem_singleton_self _) noEta
  | _ => rfl

/-- **Forgetful image of a legacy algebra.** A proof with no reflexivity node
compiles under any typed algebra whose forgetful image is the embedding of a
legacy algebra as the legacy compiler compiles it. -/
theorem Agrees.compileP_legacy (A : ρ.Agrees sig) (T : ρ.Total) {proofName : DeclName}
    (legacy : Operations sig proofName) (ops : PointedRaw Tower.Head Base)
    (twin : ops.forget = EqualityRaw.ofLegacy sig.types legacy.raw) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ)
    (noPointed : ∀ τ, Request.pointed τ ∉ requests d) {n : Nat}
    (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    ρ.compileP ops d objects hyps = HOLNativeGenericProofCompiler.compile sig proofName legacy d objects hyps := by
  have noEta : HOL.ProofSyntax.RuleTag.eta ∉ HOL.ProofSyntax.rules d := fun m => by
    obtain ⟨τ, pointed⟩ := exists_pointed_of_eta d m
    exact noPointed τ pointed
  rw [compileP_congr (ops' := (EqualityRaw.ofLegacy sig.types legacy.raw).pointedByConstant)
    twin d noPointed objects hyps]
  exact A.compileP_embed T legacy d noEta objects hyps

/-- **The embedding compiles as before**, for a reading that may leave constants
unread: a proof without an η node that the embedding compiles is compiled by the
legacy compiler to the same term. -/
theorem Agrees.compileP_embed_of_success (A : ρ.Agrees sig) {proofName : DeclName}
    (ops : Operations sig proofName) {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ)
    (noEta : HOL.ProofSyntax.RuleTag.eta ∉ HOL.ProofSyntax.rules d) {n : Nat}
    {objects : Sub Tower.Head Γ.length n} {hyps : Fin Δ.length → Tower.Tm n} {out : Tower.Tm n}
    (success : ρ.compileP (EqualityRaw.ofLegacy sig.types ops.raw).pointedByConstant d objects hyps =
      some out) :
    HOLNativeGenericProofCompiler.compile sig proofName ops d objects hyps = some out := by
  induction d generalizing n out with
  | hyp => exact success
  | impI body ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at success
      obtain ⟨p, hp, b, hb, rfl⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, A.term_represent hp, Option.bind_eq_bind, Option.bind_some,
        ih (fun m => noEta (List.mem_cons_of_mem _ m)) hb]
      rfl
  | impE function argument ihf iha =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at success
      obtain ⟨f, hf, a, ha, rfl⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind,
        ihf (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_left _ m))) hf,
        iha (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_right _ m))) ha,
        Option.bind_some]
      rfl
  | allI body ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at success
      obtain ⟨b, hb, rfl⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, ih (fun m => noEta (List.mem_cons_of_mem _ m)) hb,
        Option.bind_some]
      rfl
  | allE t function ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at success
      obtain ⟨t', ht, f, hf, rfl⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent ht,
        ih (fun m => noEta (List.mem_cons_of_mem _ m)) hf, Option.bind_some]
      rfl
  | eqRefl t =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨t', ht, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent ht, Option.bind_some]
      exact hs
  | eqSymm proof ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨l, hl, r, hr, e, he, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hl, A.term_represent hr,
        ih (fun m => noEta (List.mem_cons_of_mem _ m)) he, Option.bind_some]
      exact hs
  | eqTrans first second ihFirst ihSecond =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨l, hl, m', hm, r, hr, e₁, he₁, e₂, he₂, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hl, A.term_represent hm,
        A.term_represent hr,
        ihFirst (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_left _ m))) he₁,
        ihSecond (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_right _ m))) he₂,
        Option.bind_some]
      exact hs
  | eqPropI forward backward ihForward ihBackward =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨p, hp, q, hq, f, hf, b, hb, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hp, A.term_represent hq,
        ihForward (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_left _ m))) hf,
        ihBackward (fun m => noEta (List.mem_cons_of_mem _ (List.mem_append_right _ m))) hb,
        Option.bind_some]
      exact hs
  | eqPropEL proof ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨p, hp, q, hq, e, he, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hp, A.term_represent hq,
        ih (fun m => noEta (List.mem_cons_of_mem _ m)) he, Option.bind_some]
      exact hs
  | eqPropER proof ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨p, hp, q, hq, e, he, reversed, hr, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hp, A.term_represent hq,
        ih (fun m => noEta (List.mem_cons_of_mem _ m)) he, Option.bind_some]
      rw [show ops.raw.symmetry .prop (Presentation.subst objects p) e = some reversed from hr]
      exact hs
  | eqApp argument proof ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨f, hf, g, hg, a, ha, e, he, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hf, A.term_represent hg,
        A.term_represent ha, ih (fun m => noEta (List.mem_cons_of_mem _ m)) he, Option.bind_some]
      exact hs
  | eqAppArg function proof ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨f, hf, l, hl, r, hr, e, he, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hf, A.term_represent hl,
        A.term_represent hr, ih (fun m => noEta (List.mem_cons_of_mem _ m)) he, Option.bind_some]
      exact hs
  | eqLam proof ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨l, hl, r, hr, e, he, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hl, A.term_represent hr,
        ih (fun m => noEta (List.mem_cons_of_mem _ m)) he, Option.bind_some]
      exact hs
  | funExt proof ih =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨f, hf, g, hg, e, he, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent hf, A.term_represent hg,
        ih (fun m => noEta (List.mem_cons_of_mem _ m)) he, Option.bind_some]
      exact hs
  | beta t body =>
      simp only [compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨a, ha, b, hb, hs⟩ := success
      simp only [HOLNativeGenericProofCompiler.compile, Option.bind_eq_bind, A.term_represent ha, A.term_represent hb,
        Option.bind_some]
      exact hs
  | eta function => exact absurd (List.mem_singleton_self _) noEta
  | _ => simp [compileP] at success

/-- **Licensing of the legacy compiler.** When the embedded legacy record is
lawful in the selected judgment, every result of the legacy compiler on a
proof without η nodes is a term of the reading's package at the decoding of the
signature's representation of the conclusion. -/
theorem Laws.compile_typedO (L : ρ.Laws) (A : ρ.Agrees sig) (T : ρ.Total)
    {proofName : DeclName} (legacy : Operations sig proofName)
    (lawful : (EqualityRaw.ofLegacy sig.types legacy.raw).Lawful ρ) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ)
    (noEta : HOL.ProofSyntax.RuleTag.eta ∉ HOL.ProofSyntax.rules d) {n : Nat}
    {target : Tower.Ctx n} {objects : Sub Tower.Head Γ.length n}
    {hyps : Fin Δ.length → Tower.Tm n}
    (objectsTyped : SubstMor ρ.rules (ρ.objCtx Γ) target objects)
    (hypsTyped : ∀ i, ∃ c, represent sig (Δ.get i) = some c ∧
      Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c)))
    {out : Tower.Tm n} (success : HOLNativeGenericProofCompiler.compile sig proofName legacy d objects hyps = some out) :
    ∃ code, represent sig φ = some code ∧
      Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) := by
  rw [← A.compileP_embed T legacy d noEta objects hyps] at success
  obtain ⟨code, hcode, typed⟩ := L.compileP_typedO lawful.pointedByConstant d objectsTyped
    (fun i => by simpa only [A.term_eq_represent T] using hypsTyped i) success
  exact ⟨code, A.term_represent hcode, typed⟩

end HOLReading

/-! ## The obstruction -/

/-- **The identity algebra is not a legacy algebra.** Under the identity
reading, symmetry depends on the right endpoint, which the legacy record never
receives; so no legacy record embeds as the identity algebra's forgetful
image. -/
theorem HOLReading.identityRaw_not_ofLegacy {ρ : HOLReading Tower.Head Base Const}
    (identity : ρ.codes.identity = true) (J : DeclName)
    (funext : HOL.Ty Base → HOL.Ty Base → Option DeclName) (propext : Option DeclName)
    (types : TypeInterpretation Base) (τ : HOL.Ty Base) :
    ¬ ∃ raw : RawOperations Base,
      (ρ.identityRaw J funext propext).forget = EqualityRaw.ofLegacy types raw := by
  rintro ⟨raw, same⟩
  have first := congrArg (fun ops : EqualityRaw Tower.Head Base =>
    ops.symmetry (n := 0) τ (.const .anonymous) (.const `left) (.const .anonymous)) same
  have second := congrArg (fun ops : EqualityRaw Tower.Head Base =>
    ops.symmetry (n := 0) τ (.const .anonymous) (.const `right) (.const .anonymous)) same
  simp only [PointedRaw.forget, identityRaw, identity, if_true, EqualityRaw.ofLegacy] at first second
  rw [← second] at first
  simp only [Option.some.injEq, transport, Tm.app.injEq, Tm.const.injEq, and_true, true_and]
    at first
  exact absurd first (by decide)

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
