import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReading

/-!
# Compiling HOL proofs modulo conversion into the selected typed judgment

A reading compiles a proof of `HOL.ProofSyntaxModulo` as the generic compiler
does (`HOLNativeGenericProofCompiler.Modulo.compileModulo`): a hypothesis is its
proof term, implication introduction is an abstraction over a proof of the
premise, universal introduction is an abstraction over the carrier,
elimination is application, and a retyping step along a conversion article
emits no term.

**Typing.** When the defining equations of the source are root steps of the
base package (`Realizes`), every compiled proof is typed, in the selected
judgment of the reading's package, at the decoding of the code of its
conclusion (`Laws.compile_typed`). A definitional step of the source between
read terms is typed equality (`Laws.sourceStep_equal`, `Laws.conversion_equal`).

**Articles.** A reading may interpret only part of the signature. The typing
theorem then needs each conversion article of the proof to stay inside the
read terms (`ArticlesRead`): a zig-zag through a term with an uninterpreted
constant can relate two read terms that the package does not equate, because
the source may have terms of a sort that the package's fragment lacks. For a
reading that interprets every constant, every article stays inside the read
terms (`ArticlesRead.of_total`), and the typing theorem needs no side
condition (`Laws.compile_typed_of_total`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace HOLReading

open Normalization
open Mettapedia.Logic

universe u v

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-! ## Realized equations and conversion inside the read terms -/

section Definitions

variable (ρ : HOLReading Head Base Const) (eqs : List (HOL.DefiningEquation Const))

/-- Every listed equation is read on both sides, and every instance of the read
equation is a root step of the base package. -/
def Realizes : Prop :=
  ∀ equation ∈ eqs, ∃ l r,
    ρ.term equation.left = some l ∧ ρ.term equation.right = some r ∧
    ∀ {n : Nat} (σ : Sub Head equation.context.length n),
      ρ.base.computation.step (Presentation.subst σ l) (Presentation.subst σ r)

/-- A definitional step of the source between two read terms. -/
def RepStep {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (s t : HOL.Term Const Γ τ) : Prop :=
  (ρ.term s).isSome ∧ (ρ.term t).isSome ∧ HOL.SourceStep eqs s t

/-- A conversion article that stays inside the read terms. -/
abbrev RepConversion {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (s t : HOL.Term Const Γ τ) : Prop :=
  Relation.EqvGen (ρ.RepStep eqs) s t

/-- A reading that interprets every constant of the signature. -/
def Total : Prop := ∀ {τ : HOL.Ty Base} (c : Const τ), (ρ.constant c).isSome

end Definitions

variable {ρ : HOLReading Head Base Const} {eqs : List (HOL.DefiningEquation Const)}

/-- A relation included in another generates an included equivalence. -/
theorem eqvGen_mono {α : Type*} {r r' : α → α → Prop} (sub : ∀ a b, r a b → r' a b)
    {a b : α}
    (related : Relation.EqvGen r a b) : Relation.EqvGen r' a b := by
  induction related with
  | rel a b step => exact .rel a b (sub a b step)
  | refl a => exact .refl a
  | symm a b _ ih => exact .symm a b ih
  | trans a b c _ _ first second => exact .trans a b c first second

/-- Related terms are equal, or both read. -/
theorem RepConversion.eq_or_read {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ}
    (conversion : ρ.RepConversion eqs s t) :
    s = t ∨ ((ρ.term s).isSome ∧ (ρ.term t).isSome) := by
  induction conversion with
  | rel _ _ step => exact .inr ⟨step.1, step.2.1⟩
  | refl => exact .inl rfl
  | symm _ _ _ ih =>
      rcases ih with same | ⟨first, second⟩
      · exact .inl same.symm
      · exact .inr ⟨second, first⟩
  | trans _ _ _ _ _ first second =>
      rcases first with same | ⟨firstRead, _⟩
      · rcases second with same' | ⟨middleRead, lastRead⟩
        · exact .inl (same.trans same')
        · subst same
          exact .inr ⟨middleRead, lastRead⟩
      · rcases second with same' | ⟨_, lastRead⟩
        · subst same'
          exact .inr ⟨firstRead, by assumption⟩
        · exact .inr ⟨firstRead, lastRead⟩

/-- A conversion inside the read terms is a conversion article. -/
theorem RepConversion.core {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ}
    (conversion : ρ.RepConversion eqs s t) : HOL.CoreConversion eqs s t := by
  refine eqvGen_mono (fun a b step => ?_) conversion
  obtain ⟨ha, hb, source⟩ := step
  obtain ⟨_, ha'⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp hb
  exact ⟨isCore_of_term ha', isCore_of_term hb', source⟩

/-- A total reading reads every core term. -/
theorem term_isSome_of_isCore (T : ρ.Total) :
    ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ), t.isCore = true →
      (ρ.term t).isSome
  | _, _, .var _, _ => rfl
  | _, _, .const c, _ => by
      obtain ⟨t0, ht⟩ := Option.isSome_iff_exists.mp (T c)
      simp [term, ht]
  | _, _, .app f a, core => by
      simp only [HOL.Term.isCore, Bool.and_eq_true] at core
      obtain ⟨f', hf⟩ := Option.isSome_iff_exists.mp (term_isSome_of_isCore T f core.1)
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp (term_isSome_of_isCore T a core.2)
      simp [term, hf, ha, both]
  | _, _, .lam b, core => by
      simp only [HOL.Term.isCore] at core
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp (term_isSome_of_isCore T b core)
      simp [term, hb]
  | _, _, .imp p q, core => by
      simp only [HOL.Term.isCore, Bool.and_eq_true] at core
      obtain ⟨p', hp⟩ := Option.isSome_iff_exists.mp (term_isSome_of_isCore T p core.1)
      obtain ⟨q', hq⟩ := Option.isSome_iff_exists.mp (term_isSome_of_isCore T q core.2)
      simp [term, hp, hq, both]
  | _, _, .all b, core => by
      simp only [HOL.Term.isCore] at core
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp (term_isSome_of_isCore T b core)
      simp [term, hb]
  | _, _, .eq l r, core => by
      simp only [HOL.Term.isCore, Bool.and_eq_true] at core
      obtain ⟨l', hl⟩ := Option.isSome_iff_exists.mp (term_isSome_of_isCore T l core.1)
      obtain ⟨r', hr⟩ := Option.isSome_iff_exists.mp (term_isSome_of_isCore T r core.2)
      simp [term, hl, hr, both]
  | _, _, .top, core | _, _, .bot, core | _, _, .and _ _, core | _, _, .or _ _, core
  | _, _, .not _, core | _, _, .ex _, core => by simp [HOL.Term.isCore] at core

/-- Under a total reading every conversion article stays inside the read
terms. -/
theorem RepConversion.of_core (T : ρ.Total) {Γ : HOL.Ctx Base} {τ : HOL.Ty Base}
    {s t : HOL.Term Const Γ τ} (conversion : HOL.CoreConversion eqs s t) :
    ρ.RepConversion eqs s t :=
  eqvGen_mono (fun a b step =>
    ⟨term_isSome_of_isCore T a step.1, term_isSome_of_isCore T b step.2.1, step.2.2⟩) conversion

/-! ## Conversion is typed equality -/

namespace Laws

variable (L : ρ.Laws)
include L

theorem equal_impOf {n : Nat} {Γ : Ctx Head n} {p p' q q' : Tm Head n}
    (hp : Equal ρ.rules Γ p p' ρ.codes.propT) (hq : Equal ρ.rules Γ q q' ρ.codes.propT) :
    Equal ρ.rules Γ (ρ.impOf p q) (ρ.impOf p' q') ρ.codes.propT :=
  .appCong (.appCong (.refl L.imp_typed) hp) hq

theorem equal_eqOf {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {x x' y y' : Tm Head n}
    (hx : Equal ρ.rules Γ x x' (ρ.carrierAt n τ))
    (hy : Equal ρ.rules Γ y y' (ρ.carrierAt n τ)) :
    Equal ρ.rules Γ (ρ.eqOf τ x y) (ρ.eqOf τ x' y') ρ.codes.propT := by
  have first := Derivable.appCong (.refl (L.eq_typed τ)) hx
  rw [inst0, Presentation.subst, subst_carrierAt] at first
  exact .appCong first hy

theorem equal_allOf_lam {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {b b' : Tm Head (n + 1)}
    (h : Equal ρ.rules (.snoc Γ (ρ.carrierAt n τ)) b b' ρ.codes.propT) :
    Equal ρ.rules Γ (ρ.allOf τ (.lam b)) (ρ.allOf τ (.lam b')) ρ.codes.propT :=
  .appCong (.refl (L.all_typed τ))
    (.lamCong (L.pi_typed (L.carrierAt_typed τ) L.prop_typed) L.proofs_universe h)

/-- **A definitional step is typed equality.** A step of the source between
read terms, by β or by an instance of a realized equation, closed under the
term formers, relates the reads in the selected judgment at their carrier. -/
theorem sourceStep_equal (R : ρ.Realizes eqs) {Γ : HOL.Ctx Base} {τ : HOL.Ty Base}
    {s t : HOL.Term Const Γ τ} (step : HOL.SourceStep eqs s t) :
    ∀ {s' t' : Tm Head Γ.length}, ρ.term s = some s' → ρ.term t = some t' →
      Equal ρ.rules (ρ.objCtx Γ) s' t' (ρ.carrierAt Γ.length τ) := by
  induction step with
  | beta body argument =>
      intro s' t' hs ht
      obtain ⟨f', a', hf, ha, rfl⟩ := term_app hs
      obtain ⟨b', hb, rfl⟩ := term_lam hf
      rw [ρ.term_instantiate ha, hb] at ht
      cases ht
      have e := Derivable.betaPi (L.carrierAt_typed (.arr _ _)) L.proofs_universe
        (L.term_typed hb) (L.term_typed ha)
      rwa [ρ.inst0_carrierAt] at e
  | delta equation listed substitution _ =>
      intro s' t' hs ht
      obtain ⟨l, r, hl, hr, roots⟩ := R equation listed
      obtain ⟨l0, hl0, hs'⟩ := ρ.term_subst_inv substitution (ρ.nativeSub substitution)
        (fun {_} i {_} h => ρ.nativeSub_varIndex substitution i h) equation.left hs
      obtain ⟨r0, hr0, ht'⟩ := ρ.term_subst_inv substitution (ρ.nativeSub substitution)
        (fun {_} i {_} h => ρ.nativeSub_varIndex substitution i h) equation.right ht
      rw [hl] at hl0
      rw [hr] at hr0
      cases hl0
      cases hr0
      subst hs' ht'
      exact .root (ρ.codes.extend_base_step ρ.base (roots _)) (L.term_typed hs) (L.term_typed ht)
  | appFun argument _ ih =>
      intro s' t' hs ht
      obtain ⟨f', a', hf, ha, rfl⟩ := term_app hs
      obtain ⟨g', a'', hg, ha', rfl⟩ := term_app ht
      rw [ha] at ha'
      cases ha'
      have e := Derivable.appCong (ih hf hg) (.refl (L.term_typed ha))
      rwa [ρ.inst0_carrierAt] at e
  | appArg function _ ih =>
      intro s' t' hs ht
      obtain ⟨f', a', hf, ha, rfl⟩ := term_app hs
      obtain ⟨f'', b', hf', hb, rfl⟩ := term_app ht
      rw [hf] at hf'
      cases hf'
      have e := Derivable.appCong (.refl (L.term_typed hf)) (ih ha hb)
      rwa [ρ.inst0_carrierAt] at e
  | lam _ ih =>
      intro s' t' hs ht
      obtain ⟨b', hb, rfl⟩ := term_lam hs
      obtain ⟨c', hc, rfl⟩ := term_lam ht
      exact .lamCong (L.carrierAt_typed (.arr _ _)) L.proofs_universe (ih hb hc)
  | impLeft right _ ih =>
      intro s' t' hs ht
      obtain ⟨p', q', hp, hq, rfl⟩ := term_imp hs
      obtain ⟨p'', q'', hp', hq', rfl⟩ := term_imp ht
      rw [hq] at hq'
      cases hq'
      exact L.equal_impOf (ih hp hp') (.refl (L.term_typed hq))
  | impRight left _ ih =>
      intro s' t' hs ht
      obtain ⟨p', q', hp, hq, rfl⟩ := term_imp hs
      obtain ⟨p'', q'', hp', hq', rfl⟩ := term_imp ht
      rw [hp] at hp'
      cases hp'
      exact L.equal_impOf (.refl (L.term_typed hp)) (ih hq hq')
  | eqLeft right _ ih =>
      intro s' t' hs ht
      obtain ⟨l', r', hl, hr, rfl⟩ := term_eq hs
      obtain ⟨l'', r'', hl', hr', rfl⟩ := term_eq ht
      rw [hr] at hr'
      cases hr'
      exact L.equal_eqOf (ih hl hl') (.refl (L.term_typed hr))
  | eqRight left _ ih =>
      intro s' t' hs ht
      obtain ⟨l', r', hl, hr, rfl⟩ := term_eq hs
      obtain ⟨l'', r'', hl', hr', rfl⟩ := term_eq ht
      rw [hl] at hl'
      cases hl'
      exact L.equal_eqOf (.refl (L.term_typed hl)) (ih hr hr')
  | all _ ih =>
      intro s' t' hs ht
      obtain ⟨b', hb, rfl⟩ := term_all hs
      obtain ⟨c', hc, rfl⟩ := term_all ht
      exact L.equal_allOf_lam (ih hb hc)

/-- **Conversion is typed equality.** A conversion article inside the read
terms relates the reads of its ends in the selected judgment. -/
theorem conversion_equal (R : ρ.Realizes eqs) {Γ : HOL.Ctx Base} {τ : HOL.Ty Base}
    {s t : HOL.Term Const Γ τ} (conversion : ρ.RepConversion eqs s t) :
    ∀ {s' t' : Tm Head Γ.length}, ρ.term s = some s' → ρ.term t = some t' →
      Equal ρ.rules (ρ.objCtx Γ) s' t' (ρ.carrierAt Γ.length τ) := by
  induction conversion with
  | rel _ _ step => exact L.sourceStep_equal R step.2.2
  | refl =>
      intro s' t' hs ht
      rw [hs] at ht
      cases ht
      exact .refl (L.term_typed hs)
  | symm _ _ _ ih =>
      intro s' t' hs ht
      exact .symm (ih ht hs)
  | trans _ _ _ first _ ihFirst ihSecond =>
      intro s' t' hs ht
      rcases RepConversion.eq_or_read first with same | ⟨_, middleRead⟩
      · subst same
        exact ihSecond hs ht
      · obtain ⟨m', hm⟩ := Option.isSome_iff_exists.mp middleRead
        exact .trans (ihFirst hs hm) (ihSecond hm ht)

/-- Under a total reading, every conversion article between read terms is
typed equality. -/
theorem conversion_equal_of_total (R : ρ.Realizes eqs) (T : ρ.Total) {Γ : HOL.Ctx Base}
    {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ} (conversion : HOL.CoreConversion eqs s t)
    {s' t' : Tm Head Γ.length} (hs : ρ.term s = some s') (ht : ρ.term t = some t') :
    Equal ρ.rules (ρ.objCtx Γ) s' t' (ρ.carrierAt Γ.length τ) :=
  L.conversion_equal R (RepConversion.of_core T conversion) hs ht

end Laws

/-! ## The compiler -/

section Compile

variable (ρ)

/-- The proof compiler of the reading: the cases of `compileModulo`, with the
reading in place of the signature's representation. -/
def compile {eqs : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo eqs Δ φ) {n : Nat} (objects : Sub Head Γ.length n)
    (hyps : Fin Δ.length → Tm Head n) : Option (Tm Head n) :=
  match d with
  | .hyp i => some (hyps i)
  | @HOL.ProofSyntaxModulo.impI _ _ _ _ _ premise _ body => do
      let _ ← ρ.term premise
      let b ← compile body (fun i => Presentation.rename wk (objects i))
        (Fin.cases (.var 0) (fun i => Presentation.rename wk (hyps i)))
      pure (.lam b)
  | .impE function argument => do
      let f ← compile function objects hyps
      let a ← compile argument objects hyps
      pure (.app f a)
  | .allI body => do
      let b ← compile body (liftSub objects)
        (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))
      pure (.lam b)
  | .allE t function => do
      let t' ← ρ.term t
      let f ← compile function objects hyps
      pure (.app f (Presentation.subst objects t'))
  | .convert _ inner => compile inner objects hyps

/-- Every conversion article of a proof stays inside the read terms. -/
inductive ArticlesRead (eqs : List (HOL.DefiningEquation Const)) :
    {Γ : HOL.Ctx Base} → {Δ : List (HOL.Formula Const Γ)} → {φ : HOL.Formula Const Γ} →
    HOL.ProofSyntaxModulo eqs Δ φ → Prop
  | hyp {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} (i : Fin Δ.length) :
      ArticlesRead eqs (.hyp (equations := eqs) (Δ := Δ) i)
  | impI {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ ψ : HOL.Formula Const Γ}
      {body : HOL.ProofSyntaxModulo eqs (φ :: Δ) ψ} :
      ArticlesRead eqs body → ArticlesRead eqs (.impI body)
  | impE {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ ψ : HOL.Formula Const Γ}
      {function : HOL.ProofSyntaxModulo eqs Δ (.imp φ ψ)}
      {argument : HOL.ProofSyntaxModulo eqs Δ φ} :
      ArticlesRead eqs function → ArticlesRead eqs argument →
      ArticlesRead eqs (.impE function argument)
  | allI {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {σ : HOL.Ty Base}
      {φ : HOL.Formula Const (σ :: Γ)}
      {body : HOL.ProofSyntaxModulo eqs (HOL.weakenHyps (σ := σ) Δ) φ} :
      ArticlesRead eqs body → ArticlesRead eqs (.allI body)
  | allE {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {σ : HOL.Ty Base}
      {φ : HOL.Formula Const (σ :: Γ)} (t : HOL.Term Const Γ σ)
      {function : HOL.ProofSyntaxModulo eqs Δ (.all φ)} :
      ArticlesRead eqs function → ArticlesRead eqs (.allE t function)
  | convert {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ ψ : HOL.Formula Const Γ}
      {article : HOL.CoreConversion eqs φ ψ} {inner : HOL.ProofSyntaxModulo eqs Δ φ} :
      ρ.RepConversion eqs φ ψ → ArticlesRead eqs inner →
      ArticlesRead eqs (.convert article inner)

end Compile

/-- Under a total reading every proof's articles stay inside the read terms. -/
theorem ArticlesRead.of_total (T : ρ.Total) {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntaxModulo eqs Δ φ) : ρ.ArticlesRead eqs d := by
  induction d with
  | hyp i => exact .hyp i
  | impI _ ih => exact .impI ih
  | impE _ _ ihf iha => exact .impE ihf iha
  | allI _ ih => exact .allI ih
  | allE t _ ih => exact .allE t ih
  | convert article _ ih => exact .convert (RepConversion.of_core T article) ih

namespace Laws

variable (L : ρ.Laws)
include L

/-- **Typing of compiled proofs** (the typed twin of
`HOLNativeGenericProofCompiler.Modulo.compileModulo_typed`). If the objects
are typed at their carriers, and each hypothesis is read and has a proof of the
decoding of its code, a successful compilation of a proof whose articles stay
inside the read terms is typed, in the selected judgment, at the decoding of
the code of its conclusion. -/
theorem compile_typed (R : ρ.Realizes eqs) {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} {d : HOL.ProofSyntaxModulo eqs Δ φ}
    (articles : ρ.ArticlesRead eqs d) :
    ∀ {n : Nat} {target : Ctx Head n} {objects : Sub Head Γ.length n}
      {hyps : Fin Δ.length → Tm Head n},
      SubstMor ρ.rules (ρ.objCtx Γ) target objects →
      (∀ i, ∃ c, ρ.term (Δ.get i) = some c ∧
        Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c))) →
      ∀ {out : Tm Head n}, ρ.compile d objects hyps = some out →
        ∃ code, ρ.term φ = some code ∧
          Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) := by
  induction articles with
  | hyp i =>
      intro n target objects hyps _ hypsTyped out success
      simp only [compile, Option.some.injEq] at success
      subst success
      exact hypsTyped i
  | @impI Γ Δ p q body _ ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      cases hp : ρ.term p with
      | none => simp [compile, hp] at success
      | some pc =>
          cases hb : ρ.compile body (fun i => Presentation.rename wk (objects i))
              (Fin.cases (.var 0) (fun i => Presentation.rename wk (hyps i))) with
          | none => simp [compile, hp, hb] at success
          | some b =>
              simp [compile, hp, hb] at success
              subst success
              have objectsTyped' : SubstMor ρ.rules (ρ.objCtx Γ)
                  (.snoc target (ρ.holdsOf (Presentation.subst objects pc)))
                  (fun i => Presentation.rename wk (objects i)) := fun i => by
                simpa only [rename_subst] using (objectsTyped i).weaken
                  (extension := ρ.holdsOf (Presentation.subst objects pc))
              have hypsTyped' : ∀ i : Fin (p :: Δ).length, ∃ c,
                  ρ.term ((p :: Δ).get i) = some c ∧
                  Typed ρ.rules (.snoc target (ρ.holdsOf (Presentation.subst objects pc)))
                    (Fin.cases (.var 0) (fun i => Presentation.rename wk (hyps i)) i)
                    (ρ.holdsOf (Presentation.subst
                      (fun i => Presentation.rename wk (objects i)) c)) := by
                intro i
                refine Fin.cases ?_ (fun j => ?_) i
                · refine ⟨pc, hp, ?_⟩
                  simpa only [Fin.cases_zero, Ctx.lookup_snoc_zero, rename_subst,
                    Presentation.rename] using
                    (Derivable.var (R := ρ.rules)
                      (Γ := .snoc target (ρ.holdsOf (Presentation.subst objects pc))) 0)
                · obtain ⟨c, hc, typed⟩ := hypsTyped j
                  refine ⟨c, hc, ?_⟩
                  simpa only [Fin.cases_succ, rename_subst, Presentation.rename] using
                    typed.weaken (extension := ρ.holdsOf (Presentation.subst objects pc))
              obtain ⟨qc, hq, bodyTyped⟩ := ih objectsTyped' hypsTyped' hb
              refine ⟨ρ.impOf pc qc, by simp only [term, hp, hq]; rfl, ?_⟩
              exact L.impIntro ((L.term_typed hp).substitute objectsTyped)
                ((L.term_typed hq).substitute objectsTyped)
                (by simpa only [rename_subst] using bodyTyped)
  | impE _ _ ihFunction ihArgument =>
      intro n target objects hyps objectsTyped hypsTyped out success
      rename_i function argument _ _
      cases hf : ρ.compile function objects hyps with
      | none => simp [compile, hf] at success
      | some f =>
          cases ha : ρ.compile argument objects hyps with
          | none => simp [compile, hf, ha] at success
          | some a =>
              simp [compile, hf, ha] at success
              subst success
              obtain ⟨fc, hfc, functionTyped⟩ := ihFunction objectsTyped hypsTyped hf
              obtain ⟨pc, hpc, argumentTyped⟩ := ihArgument objectsTyped hypsTyped ha
              obtain ⟨p', q', hp', hq', rfl⟩ := term_imp hfc
              rw [hpc] at hp'
              cases hp'
              exact ⟨q', hq', L.impElim ((L.term_typed hpc).substitute objectsTyped)
                ((L.term_typed hq').substitute objectsTyped) functionTyped argumentTyped⟩
  | @allI Γ Δ σ φ body _ ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      cases hb : ρ.compile body (liftSub objects)
          (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) with
      | none => simp [compile, hb] at success
      | some b =>
          simp [compile, hb] at success
          subst success
          have objectsTyped' : SubstMor ρ.rules (ρ.objCtx (σ :: Γ))
              (.snoc target (ρ.carrierAt n σ)) (liftSub objects) := by
            have lifted := SubstMor.lift objectsTyped (ρ.carrierAt Γ.length σ)
            rw [subst_carrierAt] at lifted
            exact lifted
          have hypsTyped' : ∀ i : Fin (HOL.weakenHyps (σ := σ) Δ).length, ∃ c,
              ρ.term ((HOL.weakenHyps (σ := σ) Δ).get i) = some c ∧
                Typed ρ.rules (.snoc target (ρ.carrierAt n σ))
                  (Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))
                  (ρ.holdsOf (Presentation.subst (liftSub objects) c)) := by
            intro i
            obtain ⟨c, hc, typed⟩ := hypsTyped (i.cast (by simp [HOL.weakenHyps]))
            refine ⟨Presentation.rename wk c, ?_, ?_⟩
            · have entry : (HOL.weakenHyps (σ := σ) Δ).get i =
                  HOL.weaken (Δ.get (i.cast (by simp [HOL.weakenHyps]))) := by
                have indexValid : i.val < Δ.length := by simpa [HOL.weakenHyps] using i.isLt
                change (Δ.map (HOL.weaken (σ := σ)))[i.val] = HOL.weaken Δ[i.val]
                simp only [List.getElem_map]
              rw [entry, ρ.term_weaken, hc]
              rfl
            · simpa only [subst_liftSub_wk, Presentation.rename] using
                typed.weaken (extension := ρ.carrierAt n σ)
          obtain ⟨bc, hbc, bodyTyped⟩ := ih objectsTyped' hypsTyped' hb
          refine ⟨ρ.allOf σ (.lam bc), by simp only [term, hbc]; rfl, ?_⟩
          exact L.allIntro ((L.term_typed hbc).substitute objectsTyped') bodyTyped
  | @allE Γ Δ σ φ t function _ ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      cases ht : ρ.term t with
      | none => simp [compile, ht] at success
      | some tc =>
          cases hf : ρ.compile function objects hyps with
          | none => simp [compile, ht, hf] at success
          | some f =>
              simp [compile, ht, hf] at success
              subst success
              obtain ⟨fc, hfc, functionTyped⟩ := ih objectsTyped hypsTyped hf
              obtain ⟨φc, hφc, rfl⟩ := term_all hfc
              refine ⟨inst0 tc φc, by rw [ρ.term_instantiate ht, hφc]; rfl, ?_⟩
              have objectsTyped' : SubstMor ρ.rules (ρ.objCtx (σ :: Γ))
                  (.snoc target (ρ.carrierAt n σ)) (liftSub objects) := by
                have lifted := SubstMor.lift objectsTyped (ρ.carrierAt Γ.length σ)
                rw [subst_carrierAt] at lifted
                exact lifted
              have argument : Typed ρ.rules target (Presentation.subst objects tc)
                  (ρ.carrierAt n σ) := by
                simpa only [subst_carrierAt] using (L.term_typed ht).substitute objectsTyped
              have eliminated := L.allElim ((L.term_typed hφc).substitute objectsTyped')
                functionTyped argument
              simpa only [subst_inst0] using eliminated
  | @convert Γ Δ φ ψ article inner represented _ ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [compile] at success
      obtain ⟨φc, hφc, typed⟩ := ih objectsTyped hypsTyped success
      rcases RepConversion.eq_or_read represented with same | ⟨_, ψRead⟩
      · subst same
        exact ⟨φc, hφc, typed⟩
      · obtain ⟨ψc, hψc⟩ := Option.isSome_iff_exists.mp ψRead
        refine ⟨ψc, hψc, ?_⟩
        have equal := (L.conversion_equal R represented hφc hψc).substitute objectsTyped
        exact .conv typed (L.equal_holdsOf equal) L.proofs_universe

/-- **Typing of compiled proofs under a total reading.** -/
theorem compile_typed_of_total (R : ρ.Realizes eqs) (T : ρ.Total) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo eqs Δ φ) {n : Nat} {target : Ctx Head n}
    {objects : Sub Head Γ.length n} {hyps : Fin Δ.length → Tm Head n}
    (objectsTyped : SubstMor ρ.rules (ρ.objCtx Γ) target objects)
    (hypsTyped : ∀ i, ∃ c, ρ.term (Δ.get i) = some c ∧
      Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c)))
    {out : Tm Head n} (success : ρ.compile d objects hyps = some out) :
    ∃ code, ρ.term φ = some code ∧
      Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) :=
  L.compile_typed R (ArticlesRead.of_total T d) objectsTyped hypsTyped success

end Laws

end HOLReading

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
