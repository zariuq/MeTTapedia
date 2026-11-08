import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationFrames
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion

/-!
# Second-order frames inside dependent frames: reflection, and the identity off the image

**Reflection** (`translation_reflects`). Over a rule package with no declared root computation and
a symmetric head equality, conversion is Church–Rosser (`EmptyRootConversion.churchRosser`). The
translation of a term is a normal form (`encode_normal`), the translation of a type is a normal form
(`type_normal`), and both are injective when the sort and constructor names are
(`encode_injective`, `bindingType_injective`). Hence two observations translate to convertible
judged terms exactly when they are equal, and the map reflects models and asks of equation
guards (`translation_models_iff`, `translation_entails_reflect`).

**The identity off the image** (`translation_id_off_image`). The code of the identity assignment
sends a metavariable with parameters to its eta expansion `λx̄. m x̄`. The candidate's conversion has
no eta for products, so this is not convertible to the variable `m`; the translated identity acts as
the identity on translated terms (`translation_id_image`) but not on every judged term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation

open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type}

/-! ## Index values -/

theorem inner_val {k : Nat} : ∀ {p : Nat} (j : Fin p), (inner (k := k) j).val = j.val
  | 0, j => j.elim0
  | _ + 1, j => by
      refine Fin.cases rfl (fun j => ?_) j
      exact congrArg Nat.succ (inner_val j)

theorem outer_val {k : Nat} : ∀ {p : Nat} (i : Fin k), (outer (p := p) i).val = p + i.val
  | 0, i => (Nat.zero_add _).symm
  | p + 1, i => by
      show (outer (p := p) i).val + 1 = p + 1 + i.val
      rw [outer_val i]
      omega

theorem vIdx_injective {Srt : Type} : ∀ {Γ : List Srt} {s : Srt} (a b : Binding.Var Γ s),
    vIdx a = vIdx b → a = b
  | _, _, .zero, .zero, _ => rfl
  | _, _, .zero, .succ _, same => absurd (congrArg Fin.val same).symm (Nat.succ_ne_zero _)
  | _, _, .succ _, .zero, same => absurd (congrArg Fin.val same) (Nat.succ_ne_zero _)
  | _, _, .succ a, .succ b, same =>
      congrArg Binding.Var.succ (vIdx_injective a b (Fin.succ_injective _ same))

theorem inner_injective {k p : Nat} : Function.Injective (inner (k := k) (p := p)) := by
  intro a b same
  have values := congrArg Fin.val same
  rw [inner_val, inner_val] at values
  exact Fin.ext values

theorem outer_injective {k p : Nat} : Function.Injective (outer (k := k) (p := p)) := by
  intro a b same
  have values := congrArg Fin.val same
  rw [outer_val, outer_val] at values
  exact Fin.ext (by omega)

theorem inner_ne_outer {k p : Nat} (j : Fin p) (i : Fin k) : inner (k := k) j ≠ outer i := by
  intro same
  have values := congrArg Fin.val same
  rw [inner_val, outer_val] at values
  have bound := j.isLt
  omega

/-! ## Normal forms -/

section Normal

variable (root : RootComputation Head) (headEq : Head → Head → Prop)

/-- A term with no computation step. -/
def Normal {n : Nat} (t : Tm Head n) : Prop := ∀ t', ¬ StepCore root headEq t t'

variable {root headEq}

theorem var_normal (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {n : Nat}
    (x : Fin n) : Normal root headEq (.var x : Tm Head n) := by
  intro t step
  cases step with
  | root h => exact noRoot _ _ h

theorem const_normal (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {n : Nat}
    (c : DeclName) : Normal root headEq (.const c : Tm Head n) := by
  intro t step
  cases step with
  | root h => exact noRoot _ _ h

theorem app_normal (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {n : Nat}
    {f a : Tm Head n} (normalF : Normal root headEq f) (normalA : Normal root headEq a)
    (notLam : ∀ body, f ≠ .lam body) : Normal root headEq (.app f a) := by
  intro t step
  cases step with
  | betaPi body _ => exact notLam body rfl
  | root h => exact noRoot _ _ h
  | congAppFun inner => exact normalF _ inner
  | congAppArg inner => exact normalA _ inner

theorem lam_normal (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {n : Nat}
    {body : Tm Head (n + 1)} (normal : Normal root headEq body) :
    Normal root headEq (.lam body) := by
  intro t step
  cases step with
  | root h => exact noRoot _ _ h
  | congLam inner => exact normal _ inner

theorem pi_normal (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {n : Nat}
    {A : Tm Head n} {B : Tm Head (n + 1)} (normalA : Normal root headEq A)
    (normalB : Normal root headEq B) : Normal root headEq (.pi A B) := by
  intro t step
  cases step with
  | root h => exact noRoot _ _ h
  | congPiDom inner => exact normalA _ inner
  | congPiCod inner => exact normalB _ inner

theorem applyVec_normal (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {n : Nat} :
    ∀ {p : Nat} {f : Tm Head n} {w : Sub Head p n}, Normal root headEq f →
      (∀ body, f ≠ .lam body) → (∀ j, Normal root headEq (w j)) →
      Normal root headEq (applyVec f w)
  | 0, _, _, normal, _, _ => normal
  | _ + 1, f, w, normal, notLam, arguments =>
      applyVec_normal noRoot (f := .app f (w 0)) (w := fun j => w j.succ)
        (app_normal noRoot normal (arguments 0) notLam) (fun _ same => by cases same)
        (fun j => arguments j.succ)

theorem spine_normal (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {n : Nat}
    {f : Tm Head n} (normal : Normal root headEq f) (notLam : ∀ body, f ≠ .lam body) :
    ∀ {p : Nat} {w : Sub Head p n}, (∀ j, Normal root headEq (w j)) →
      Normal root headEq (spine f w) ∧ ∀ body, spine f w ≠ .lam body
  | 0, _, _ => ⟨normal, notLam⟩
  | _ + 1, w, arguments =>
      have earlier := spine_normal noRoot normal notLam (w := fun j => w j.succ)
        (fun j => arguments j.succ)
      ⟨app_normal noRoot earlier.1 (arguments 0) earlier.2, fun _ same => by cases same⟩

theorem abstractB_normal {S : Binding.Signature}
    (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {k : Nat} {Γ : Binding.Ctx S} :
    ∀ (bound : List S.Srt) {body : Tm Head (k + (bound ++ Γ).length)},
      Normal root headEq body → Normal root headEq (abstractB (Γ := Γ) bound body)
  | [], _, normal => normal
  | _ :: bound, _, normal => abstractB_normal noRoot bound (lam_normal noRoot normal)

theorem abstractN_normal (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) {k : Nat} :
    ∀ (p : Nat) {body : Tm Head (k + p)}, Normal root headEq body →
      Normal root headEq (abstractN p body)
  | 0, _, normal => normal
  | p + 1, _, normal => abstractN_normal noRoot p (lam_normal noRoot normal)

/-- A normal form has only itself as a reduct. -/
theorem eq_of_steps_normal {n : Nat} {a c : Tm Head n} (normal : Normal root headEq a)
    (steps : Relation.ReflTransGen (StepCore root headEq) a c) : a = c := by
  rcases Relation.ReflTransGen.cases_head steps with same | ⟨b, step, _⟩
  · exact same
  · exact (normal b step).elim

end Normal

/-- **Convertible normal forms are equal**, under Church–Rosser. -/
theorem eq_of_conv_normal {rules : Rules Head} (cr : ConversionCoherence.ChurchRosser rules)
    {n : Nat} {a b : Tm Head n} (conv : Conv rules.headEq a b rules.computation)
    (normalA : Normal rules.computation rules.headEq a)
    (normalB : Normal rules.computation rules.headEq b) : a = b := by
  obtain ⟨c, toCommonA, toCommonB⟩ := cr conv
  rw [eq_of_steps_normal normalA toCommonA, eq_of_steps_normal normalB toCommonB]

variable {S : Binding.Signature} (names : BindingSignatureEmbedding.Names S)

section NormalTranslation

variable {root : RootComputation Head} {headEq : Head → Head → Prop}
  (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) (M : List (Binding.MetaArity S))

include noRoot

mutual

/-- **The translation of a term is a normal form.** -/
theorem encode_normal : ∀ {Γ : Binding.Ctx S} {s : S.Srt} (t : Binding.Term (Sig S M) Γ s),
    Normal root headEq (encode (Head := Head) names M t)
  | _, _, .var _ => var_normal noRoot _
  | _, _, .op (.inl _) args =>
      applyVec_normal noRoot (const_normal noRoot _) (fun _ same => by cases same)
        (encodeArgs_normal args)
  | _, _, .op (.inr (.mk _)) args =>
      (spine_normal noRoot (var_normal noRoot _) (fun _ same => by cases same)
        (fun j => encodeArgs_normal args _)).1

theorem encodeArgs_normal : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Binding.Ctx S}
    (args : Binding.Args (Sig S M) as Γ) (j : Fin as.length),
    Normal root headEq (encodeArgs (Head := Head) names M args j)
  | _, _, .nil, j => j.elim0
  | _, _, .cons (bs := bound) body rest, j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · exact abstractB_normal noRoot bound (encode_normal body)
      · exact encodeArgs_normal rest j

end

end NormalTranslation

/-! ## Types: products of sort constants -/

/-- The closed product `Π a₀. … Π aₘ₋₁. s`, outermost first. -/
def piChain (s : S.Srt) : List S.Srt → Tm Head 0
  | [] => BindingSignatureEmbedding.sortType names s
  | a :: L => BindingSignatureEmbedding.closedArrow (BindingSignatureEmbedding.sortType names a)
      (piChain s L)

theorem telescopeType_piChain (s : S.Srt) : ∀ (Γ L : List S.Srt),
    BindingSignatureEmbedding.telescopeType names Γ (piChain (Head := Head) names s L) =
      piChain names s (Γ.reverse ++ L)
  | [], _ => rfl
  | g :: Γ, L => by
      rw [show (g :: Γ).reverse ++ L = Γ.reverse ++ g :: L by simp]
      exact telescopeType_piChain s Γ (g :: L)

/-- The constant names read along a chain of products of constants. -/
def typeNames : {n : Nat} → Tm Head n → List DeclName
  | _, .const c => [c]
  | _, .pi (.const a) B => a :: typeNames B
  | _, _ => []

theorem typeNames_piChain (s : S.Srt) : ∀ (L : List S.Srt) {n : Nat},
    typeNames (liftClosed (piChain (Head := Head) names s L) : Tm Head n) =
      L.map names.sort ++ [names.sort s]
  | [], _ => rfl
  | a :: L, n => by
      have unfold : (liftClosed (piChain (Head := Head) names s (a :: L)) : Tm Head n) =
          .pi (.const (names.sort a)) (liftClosed (piChain names s L)) :=
        BindingSignatureEmbedding.liftClosed_closedArrow _ _
      rw [unfold]
      show names.sort a ::
        typeNames (liftClosed (piChain (Head := Head) names s L) : Tm Head (n + 1)) = _
      rw [typeNames_piChain s L]
      rfl

theorem bindingType_eq_piChain (Γ : List S.Srt) (s : S.Srt) :
    (BindingSignatureEmbedding.bindingType names Γ s : Tm Head 0) = piChain names s Γ.reverse := by
  have law := telescopeType_piChain (Head := Head) names s Γ []
  rw [List.append_nil] at law
  exact law

/-- **The type `Π Γ. s` determines `Γ` and `s`** when sort names are injective. -/
theorem bindingType_injective (sortInjective : Function.Injective names.sort) {n : Nat}
    {Γ Γ' : List S.Srt} {s s' : S.Srt}
    (same : (liftClosed (BindingSignatureEmbedding.bindingType names Γ s) : Tm Head n) =
      liftClosed (BindingSignatureEmbedding.bindingType names Γ' s')) : Γ = Γ' ∧ s = s' := by
  have read := congrArg typeNames same
  rw [bindingType_eq_piChain, bindingType_eq_piChain, typeNames_piChain, typeNames_piChain] at read
  obtain ⟨prefixes, lasts⟩ := List.append_inj' read rfl
  have sorts : s = s' := sortInjective (List.cons.inj lasts).1
  have reversed := (List.map_injective_iff.mpr sortInjective) prefixes
  exact ⟨List.reverse_injective reversed, sorts⟩

theorem piChain_normal {root : RootComputation Head} {headEq : Head → Head → Prop}
    (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ root.step a b) (s : S.Srt) :
    ∀ (L : List S.Srt) {n : Nat},
      Normal root headEq (liftClosed (piChain (Head := Head) names s L) : Tm Head n)
  | [], _ => const_normal noRoot _
  | a :: L, n => by
      have unfold : (liftClosed (piChain (Head := Head) names s (a :: L)) : Tm Head n) =
          .pi (.const (names.sort a)) (liftClosed (piChain names s L)) :=
        BindingSignatureEmbedding.liftClosed_closedArrow _ _
      rw [unfold]
      exact pi_normal noRoot (const_normal noRoot _) (piChain_normal noRoot s L)

/-! ## Injectivity of the translation of terms -/

/-- The head of an application spine. -/
def headOf : {n : Nat} → Tm Head n → Option (DeclName ⊕ Fin n)
  | _, .var x => some (.inr x)
  | _, .const c => some (.inl c)
  | _, .app f _ => headOf f
  | _, _ => none

theorem headOf_applyVec {n : Nat} : ∀ {p : Nat} (f : Tm Head n) (w : Sub Head p n),
    headOf (applyVec f w) = headOf f
  | 0, _, _ => rfl
  | _ + 1, f, w => headOf_applyVec (.app f (w 0)) (fun j => w j.succ)

theorem headOf_spine {n : Nat} (f : Tm Head n) : ∀ {p : Nat} (w : Sub Head p n),
    headOf (spine f w) = headOf f
  | 0, _ => rfl
  | _ + 1, w => headOf_spine f (fun j => w j.succ)

theorem applyVec_injective {n : Nat} : ∀ {p : Nat} {f f' : Tm Head n} {w w' : Sub Head p n},
    applyVec f w = applyVec f' w' → f = f' ∧ w = w'
  | 0, _, _, _, _, same => ⟨same, funext fun j => j.elim0⟩
  | _ + 1, f, f', w, w', same => by
      obtain ⟨heads, tails⟩ := applyVec_injective (f := .app f (w 0)) (f' := .app f' (w' 0))
        (w := fun j => w j.succ) (w' := fun j => w' j.succ) same
      obtain ⟨functions, firsts⟩ := Tm.app.inj heads
      refine ⟨functions, funext fun j => ?_⟩
      refine Fin.cases firsts (fun j => ?_) j
      exact congrFun tails j

theorem spine_injective {n : Nat} : ∀ {p : Nat} {f f' : Tm Head n} {w w' : Sub Head p n},
    spine f w = spine f' w' → f = f' ∧ w = w'
  | 0, _, _, _, _, same => ⟨same, funext fun j => j.elim0⟩
  | _ + 1, f, f', w, w', same => by
      obtain ⟨heads, firsts⟩ := Tm.app.inj same
      obtain ⟨functions, tails⟩ := spine_injective (f := f) (f' := f')
        (w := fun j => w j.succ) (w' := fun j => w' j.succ) heads
      refine ⟨functions, funext fun j => ?_⟩
      refine Fin.cases firsts (fun j => ?_) j
      exact congrFun tails j

theorem abstractB_injective {k : Nat} {Γ : Binding.Ctx S} :
    ∀ (bound : List S.Srt) {body body' : Tm Head (k + (bound ++ Γ).length)},
      abstractB (Γ := Γ) bound body = abstractB bound body' → body = body'
  | [], _, _, same => same
  | _ :: bound, _, _, same => Tm.lam.inj (abstractB_injective bound same)

theorem abstractN_injective {k : Nat} : ∀ (p : Nat) {body body' : Tm Head (k + p)},
    abstractN p body = abstractN p body' → body = body'
  | 0, _, _, same => same
  | p + 1, _, _, same => Tm.lam.inj (abstractN_injective p same)

section Injective

variable (M : List (Binding.MetaArity S))

theorem headOf_encode_var {Γ : Binding.Ctx S} {s : S.Srt} (v : Binding.Var Γ s) :
    headOf (encode (Head := Head) names M (.var v : Binding.Term (Sig S M) Γ s)) =
      some (.inr (inner (vIdx v))) := rfl

theorem headOf_encode_inl {Γ : Binding.Ctx S} {s : S.Srt} (o : S.Op s)
    (args : Binding.Args (Sig S M) (S.arity o) Γ) :
    headOf (encode (Head := Head) names M (.op (.inl o) args : Binding.Term (Sig S M) Γ s)) =
      some (.inl (names.operator o)) :=
  headOf_applyVec _ _

theorem headOf_encode_inr {Γ : Binding.Ctx S} (i : Fin M.length)
    (args : Binding.Args (Sig S M) ((M.get i).1.map (fun sort => (([] : List S.Srt), sort))) Γ) :
    headOf (encode (Head := Head) names M
        (.op (.inr (.mk i)) args : Binding.Term (Sig S M) Γ (M.get i).2)) =
      some (.inr (outer i)) :=
  headOf_spine _ _

mutual

/-- **The translation of terms is injective** when constructor names are. -/
theorem encode_injective
    (operatorInjective : ∀ {s : S.Srt}, Function.Injective (names.operator (sort := s))) :
    ∀ {Γ : Binding.Ctx S} {s s' : S.Srt}
    (t : Binding.Term (Sig S M) Γ s) (t' : Binding.Term (Sig S M) Γ s'), s = s' →
      encode (Head := Head) names M t = encode names M t' → HEq t t'
  | _, _, _, .var v, .var v', sorts, same => by
      subst sorts
      have positions := inner_injective (Tm.var.inj same)
      exact heq_of_eq (congrArg Binding.Term.var (vIdx_injective v v' positions))
  | _, _, _, .var v, .op (.inl o) args, _, same => by
      have read := congrArg headOf same
      rw [headOf_encode_var, headOf_encode_inl] at read
      cases read
  | _, _, _, .var v, .op (.inr (.mk i)) args, _, same => by
      have read := congrArg headOf same
      rw [headOf_encode_var, headOf_encode_inr] at read
      exact absurd (Sum.inr.inj (Option.some.inj read)) (inner_ne_outer _ _)
  | _, _, _, .op (.inl o) args, .var v', _, same => by
      have read := congrArg headOf same
      rw [headOf_encode_inl, headOf_encode_var] at read
      cases read
  | _, _, _, .op (.inl o) args, .op (.inl o') args', sorts, same => by
      subst sorts
      have read := congrArg headOf same
      rw [headOf_encode_inl, headOf_encode_inl] at read
      have operators : o = o' := operatorInjective (Sum.inl.inj (Option.some.inj read))
      subst operators
      have unfolded : applyVec (.const (names.operator o)) (encodeArgs (Head := Head) names M args) =
          applyVec (.const (names.operator o)) (encodeArgs names M args') := same
      obtain ⟨_, tails⟩ := applyVec_injective unfolded
      exact heq_of_eq (congrArg (Binding.Term.op _)
        (encodeArgs_injective @operatorInjective args args' (fun j => congrFun tails j)))
  | _, _, _, .op (.inl o) args, .op (.inr (.mk i)) args', _, same => by
      have read := congrArg headOf same
      rw [headOf_encode_inl, headOf_encode_inr] at read
      cases read
  | _, _, _, .op (.inr (.mk i)) args, .var v', _, same => by
      have read := congrArg headOf same
      rw [headOf_encode_inr, headOf_encode_var] at read
      exact absurd (Sum.inr.inj (Option.some.inj read)).symm (inner_ne_outer _ _)
  | _, _, _, .op (.inr (.mk i)) args, .op (.inl o') args', _, same => by
      have read := congrArg headOf same
      rw [headOf_encode_inr, headOf_encode_inl] at read
      cases read
  | _, _, _, .op (.inr (.mk i)) args, .op (.inr (.mk i')) args', _, same => by
      have read := congrArg headOf same
      rw [headOf_encode_inr, headOf_encode_inr] at read
      have identities : i = i' := outer_injective (Sum.inr.inj (Option.some.inj read))
      subst identities
      have castLength : (M.get i).1.length =
          ((M.get i).1.map (fun sort => (([] : List S.Srt), sort))).length := by simp
      have unfolded : spine (.var (outer i))
            (fun j => encodeArgs (Head := Head) names M args (Fin.cast castLength j)) =
          spine (.var (outer i)) (fun j => encodeArgs names M args' (Fin.cast castLength j)) :=
        same
      obtain ⟨_, tails⟩ := spine_injective unfolded
      refine heq_of_eq (congrArg (Binding.Term.op _)
        (encodeArgs_injective @operatorInjective args args' fun j => ?_))
      have component := congrFun tails (Fin.cast castLength.symm j)
      simpa only [Fin.cast_cast, Fin.cast_eq_self] using component

theorem encodeArgs_injective
    (operatorInjective : ∀ {s : S.Srt}, Function.Injective (names.operator (sort := s))) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Binding.Ctx S}
    (args args' : Binding.Args (Sig S M) as Γ),
    (∀ j, encodeArgs (Head := Head) names M args j = encodeArgs names M args' j) → args = args'
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons (bs := bound) body rest, .cons body' rest', same => by
      have bodies := eq_of_heq (encode_injective @operatorInjective body body' rfl
        (abstractB_injective bound (same 0)))
      have rests := encodeArgs_injective @operatorInjective rest rest' (fun j => same j.succ)
      rw [bodies, rests]

end

end Injective


/-! ## Reflection -/

section Reflection

variable {rules : Rules Head} (realization : BindingSignatureEmbedding.Realization names rules)

/-- **The translation reflects the equivalence**: two observations translate to convertible
judged terms only when they are equal. -/
theorem translation_reflects (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) (sortInjective : Function.Injective names.sort)
    (operatorInjective : ∀ {s : S.Srt}, Function.Injective (names.operator (sort := s))) :
    (translation names realization).Reflects := by
  intro M o o' same
  have cr : ConversionCoherence.ChurchRosser rules :=
    EmptyRootConversion.churchRosser rules empty symmetric
  have noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ rules.computation.step a b := by
    intro n a b step
    rw [empty] at step
    exact step
  obtain ⟨Γ, s, t⟩ := o
  obtain ⟨Γ', s', t'⟩ := o'
  have typeCodes : (liftClosed (BindingSignatureEmbedding.bindingType names Γ s) : Tm Head M.length) =
      liftClosed (BindingSignatureEmbedding.bindingType names Γ' s') := by
    refine eq_of_conv_normal cr same.1 ?_ ?_
    · rw [bindingType_eq_piChain]
      exact piChain_normal names noRoot s _
    · rw [bindingType_eq_piChain]
      exact piChain_normal names noRoot s' _
  obtain ⟨contexts, sorts⟩ := bindingType_injective names sortInjective typeCodes
  subst contexts
  subst sorts
  have termCodes : abstractN Γ.length (encode (Head := Head) names M t) =
      abstractN Γ.length (encode names M t') :=
    eq_of_conv_normal cr same.2
      (abstractN_normal noRoot _ (encode_normal names noRoot M t))
      (abstractN_normal noRoot _ (encode_normal names noRoot M t'))
  have terms := eq_of_heq (encode_injective names M @operatorInjective t t' rfl
    (abstractN_injective _ termCodes))
  subst terms
  rfl

/-- **Models are preserved and reflected.** -/
theorem translation_models_iff (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) (sortInjective : Function.Injective names.sort)
    (operatorInjective : ∀ {s : S.Srt}, Function.Injective (names.operator (sort := s)))
    {M N : List (Binding.MetaArity S)} (σa : Binding.ContextualFamily.Assignment (S := S) M.get N.get)
    (K : EquationStore (Binding.ContextualFamily.Observation S M.get)) :
    (Dependent.frames rules).Models ((translation names realization).hom σa)
        ((translation names realization).store K) ↔
      (listFrames S).Models (a := M) (b := N) σa K :=
  (translation names realization).models_iff
    (translation_reflects names realization empty symmetric sortInjective @operatorInjective) σa K

/-- **Asks of equation guards are reflected**: an ask over every dependent solution of the
translated knowledge is an ask over every second-order solution. -/
theorem translation_entails_reflect (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) (sortInjective : Function.Injective names.sort)
    (operatorInjective : ∀ {s : S.Srt}, Function.Injective (names.operator (sort := s)))
    {M : List (Binding.MetaArity S)} {K G : EquationStore (Binding.ContextualFamily.Observation S M.get)}
    (asked : (Dependent.frames rules).Entails ((translation names realization).store K)
      (fun _ g => (Dependent.frames rules).Models g ((translation names realization).store G))) :
    (listFrames S).Entails (a := M) K (fun _ f => (listFrames S).Models f G) :=
  (translation names realization).entails_reflect
    (translation_reflects names realization empty symmetric sortInjective @operatorInjective) asked

/-! ## The identity off the image -/

theorem abstractN_succ_lam {k : Nat} : ∀ (p : Nat) (body : Tm Head (k + p + 1)),
    ∃ inner, abstractN p (.lam body) = .lam inner
  | 0, body => ⟨body, rfl⟩
  | p + 1, body => abstractN_succ_lam (k := k) p (.lam body)

theorem abstractN_lam_of_ne_nil {Srt : Type} {k : Nat} :
    ∀ (P : List Srt) (body : Tm Head (k + P.length)), P ≠ [] →
      ∃ inner, abstractN P.length body = .lam inner
  | [], _, nonempty => absurd rfl nonempty
  | _ :: rest, body, _ => abstractN_succ_lam rest.length body

/-- The code of the identity at a metavariable with parameters is not convertible to the
variable: it is the eta expansion `λx̄. m x̄`, and conversion has no eta for products. -/
theorem identity_code_not_variable (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) {M : List (Binding.MetaArity S)} (i : Fin M.length)
    (parameters : (M.get i).1 ≠ []) :
    ¬ Conv rules.headEq (homCode (Head := Head) names M M (Binding.ContextualFamily.generator M.get) i)
      (.var i) rules.computation := by
  intro conv
  have cr : ConversionCoherence.ChurchRosser rules :=
    EmptyRootConversion.churchRosser rules empty symmetric
  have noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ rules.computation.step a b := by
    intro n a b step
    rw [empty] at step
    exact step
  have same := eq_of_conv_normal cr conv
    (abstractN_normal noRoot _ (encode_normal names noRoot M _)) (var_normal noRoot i)
  obtain ⟨inner, isLam⟩ := abstractN_lam_of_ne_nil (M.get i).1
    (encode (Head := Head) names M (Binding.ContextualFamily.generator M.get i)) parameters
  have clash : (Tm.lam inner : Tm Head M.length) = .var i := isLam.symm.trans same
  cases clash

/-- **The translated identity is not the identity off the image.** For a list frame with a
metavariable that has parameters, some judged term of its telescope is moved, up to conversion,
by the translation of the identity assignment. -/
theorem translation_id_off_image (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) {M : List (Binding.MetaArity S)} (i : Fin M.length)
    (parameters : (M.get i).1 ≠ []) :
    ¬ ∀ t : Dependent.Entry (ctxOf names realization M),
      (Dependent.frames rules).E
        ((Dependent.frames rules).act ((translation names realization).hom ((listFrames S).id M)) t)
        ((Dependent.frames rules).act ((Dependent.frames rules).id _) t) := by
  intro alike
  have pointwise := (Dependent.pointwise_iff _ _).mp alike i
  exact identity_code_not_variable names empty symmetric i parameters pointwise

end Reflection

end Translation

#print axioms Translation.eq_of_conv_normal
#print axioms Translation.encode_normal
#print axioms Translation.bindingType_injective
#print axioms Translation.encode_injective
#print axioms Translation.translation_reflects
#print axioms Translation.translation_models_iff
#print axioms Translation.translation_entails_reflect
#print axioms Translation.identity_code_not_variable
#print axioms Translation.translation_id_off_image

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
