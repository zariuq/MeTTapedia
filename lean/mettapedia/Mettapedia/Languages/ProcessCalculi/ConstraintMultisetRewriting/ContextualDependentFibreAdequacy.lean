import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreSpines
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.RigidHeads

/-!
# Adequacy: η-long terms over translated telescopes are translations

Over a rule package whose declared constants are exactly the realized sorts and operators
(`ClosedRealization`), every η-long term at a sort over a translated telescope is the translation
of a second-order term (`adequate_sort`), and every η-long judged term at `Π Γ. s` is the
translation of an observation (`adequate_entry`).

The proof reads the term back along its η-long derivation:

* at a sort, the term is a neutral spine (`spine_view`), whose remaining arrow must be that sort,
  so the head is fully applied;
* an object variable has a sort and no argument;
* a metavariable of arity `(P, s)` is applied to normal arguments at the sorts of `P`;
* an operator is applied to normal arguments at its binding types, each an abstraction over its
  binders of a normal term at its sort (`binding_view`);
* a sort constant is a type, never a term of a sort.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFibre

open CategoryTheory Interface Interface.Translation
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Sizes and lists -/

/-- The size of a raw term. -/
def size : {n : Nat} → Tm Head n → Nat
  | _, .var _ | _, .const _ | _, .head _ => 1
  | _, .pi A B | _, .sigma A B => size A + size B + 1
  | _, .id A x y => size A + size x + size y + 1
  | _, .lam b => size b + 1
  | _, .app f a | _, .pair f a => size f + size a + 1
  | _, .fst p | _, .snd p | _, .refl p => size p + 1

theorem size_pos {n : Nat} (t : Tm Head n) : 0 < size t := by
  cases t <;> simp [size]

theorem size_appSpine {n : Nat} : ∀ (args : List (Tm Head n)) (h : Tm Head n),
    (∀ a ∈ args, size a < size (appSpine h args)) ∧ size h ≤ size (appSpine h args)
  | [], h => ⟨fun _ member => (by simp at member), le_refl _⟩
  | x :: xs, h => by
      obtain ⟨inner, outer⟩ := size_appSpine xs (.app h x)
      have hx : size x < size (Tm.app h x) := by simp only [size]; omega
      have hh : size h < size (Tm.app h x) := by simp only [size]; omega
      refine ⟨fun a member => ?_, by simp only [appSpine_cons]; omega⟩
      rcases List.mem_cons.mp member with rfl | later
      · simp only [appSpine_cons]; omega
      · simpa only [appSpine_cons] using inner a later

theorem size_abstractB {Srt : Type} {k : Nat} {Γ : List Srt} : ∀ (bound : List Srt)
    (body : Tm Head (k + (bound ++ Γ).length)), size body ≤ size (abstractB (Γ := Γ) bound body)
  | [], _ => le_refl _
  | _ :: bound, body => by
      have := size_abstractB bound (.lam body)
      simp only [size] at this
      exact le_trans (Nat.le_succ _) this

theorem forall₂_imp_mem {α β : Type} {R R' : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      (∀ a ∈ xs, ∀ b, R a b → R' a b) → List.Forall₂ R' xs ys
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, imp =>
      .cons (imp _ (List.mem_cons_self ..) _ head)
        (forall₂_imp_mem tail fun a member b r => imp a (List.mem_cons_of_mem _ member) b r)

theorem forall₂_split_last {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} {y : β}, List.Forall₂ R xs (ys ++ [y]) →
      ∃ init x, xs = init ++ [x] ∧ List.Forall₂ R init ys ∧ R x y
  | [], ys, _, related => by cases ys <;> cases related
  | [x], [], _, .cons related .nil => ⟨[], x, rfl, .nil, related⟩
  | x :: xs, _ :: ys, y, .cons related rest => by
      obtain ⟨init, last, rfl, front, tail⟩ := forall₂_split_last (ys := ys) (y := y) rest
      exact ⟨x :: init, last, rfl, .cons related front, tail⟩
  | _ :: _ :: _, [], _, .cons _ rest => by cases rest

/-! ## Scopes and closed arrows of the translation -/

section Translation

variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)

/-- Every position of an extended scope is an object position or a metavariable position. -/
theorem inner_or_outer {k : Nat} : ∀ {p : Nat} (j : Fin (k + p)),
    (∃ l, j = inner (k := k) l) ∨ ∃ i, j = outer (p := p) i
  | 0, j => .inr ⟨j, rfl⟩
  | p + 1, j => by
      refine Fin.cases ?_ (fun j' => ?_) j
      · exact .inl ⟨0, rfl⟩
      · rcases inner_or_outer (p := p) j' with ⟨l, rfl⟩ | ⟨i, rfl⟩
        · exact .inl ⟨l.succ, rfl⟩
        · exact .inr ⟨i, rfl⟩

/-- The variable at a position of a context of sorts. -/
def varAt : ∀ (Γ : List sig.Srt) (l : Fin Γ.length), Binding.Var Γ (Γ.get l)
  | _ :: _, ⟨0, _⟩ => .zero
  | _ :: Γ, ⟨l + 1, bound⟩ => .succ (varAt Γ ⟨l, Nat.lt_of_succ_lt_succ bound⟩)

theorem vIdx_varAt : ∀ (Γ : List sig.Srt) (l : Fin Γ.length), vIdx (varAt Γ l) = l
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: Γ, ⟨l + 1, bound⟩ => by
      show (vIdx (varAt Γ ⟨l, Nat.lt_of_succ_lt_succ bound⟩)).succ = _
      rw [vIdx_varAt Γ]
      rfl

theorem lookup_inner {k : Nat} (c : Ctx Head k) (Γ : List sig.Srt) (l : Fin Γ.length) :
    Ctx.lookup (extendCtx names c Γ) (inner l) = BindingSignatureEmbedding.sortType names (Γ.get l) := by
  have law := extendCtx_inner names c (varAt Γ l)
  rwa [vIdx_varAt] at law

theorem arrows_eq_sorts {xs ys : List (Tm Head 0)} {s s' : sig.Srt}
    (same : arrows xs (BindingSignatureEmbedding.sortType names s) =
      arrows ys (BindingSignatureEmbedding.sortType names s')) :
    xs = ys ∧ names.sort s = names.sort s' := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact ⟨rfl, Tm.const.inj same⟩
      | cons y ys => cases same
  | cons x xs ih =>
      cases ys with
      | nil => cases same
      | cons y ys =>
          have parts := Tm.pi.inj same
          have tails := ih (liftClosed_injective parts.2)
          exact ⟨by rw [parts.1, tails.1], tails.2⟩

/-- The declared constants of the package are exactly the realized sorts and operators. -/
def ClosedRealization : Prop :=
  ∀ {c : DeclName} {T : Tm Head 0}, S.R.constantType c = some T →
    (∃ s, c = names.sort s) ∨ ∃ (s : sig.Srt) (o : sig.Op s), c = names.operator o

variable (realization : BindingSignatureEmbedding.Realization names S.R)

include realization in
theorem arrowConstants (closed : ClosedRealization (S := S) names) :
    ArrowConstants (S := S) names := by
  intro c T declared
  rcases closed declared with ⟨s, rfl⟩ | ⟨s, o, rfl⟩
  · rw [realization.sortLookup s] at declared
    obtain rfl := Option.some.inj declared
    exact ⟨[], .head realization.typeUniverse, .inl ⟨_, realization.universeIs, rfl⟩, rfl⟩
  · rw [realization.operatorLookup o] at declared
    obtain rfl := Option.some.inj declared
    exact ⟨_, _, .inr ⟨s, rfl⟩, argumentsType_arrows names (sig.arity o) _⟩

/-- Translated telescopes have closed arrow types. -/
theorem arrowContext (M : List (Binding.MetaArity sig)) (Γ : Binding.Ctx sig) :
    ArrowContext (S := S) names (extendCtx names (metaCtx (Head := Head) names M) Γ) := by
  intro j
  rcases inner_or_outer j with ⟨l, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨[], _, .inr ⟨Γ.get l, rfl⟩, lookup_inner names _ Γ l⟩
  · refine ⟨((M.get i).1.reverse.map fun p => BindingSignatureEmbedding.sortType names p), _,
      .inr ⟨(M.get i).2, rfl⟩, ?_⟩
    rw [extendCtx_outer names (metaCtx names M) (metaCtx_lookup names M i) Γ]
    unfold BindingSignatureEmbedding.bindingType
    rw [telescopeType_arrows]

/-! ## Reading back -/

variable (facts : FormFacts S.R S.roles) (complete : AlgorithmicComplete S.R S.roles)
  (rigid : ∀ name, S.roles name = .rigid) (sortInjective : Function.Injective names.sort)

include facts realization in
/-- A normal term of a closed arrow type is an abstraction over its binders. -/
theorem binding_view {k : Nat} {c : Ctx Head k} (formedC : CtxFormed S.R c) :
    ∀ (bound : List sig.Srt) {Γ : Binding.Ctx sig} {r : Tm Head 0}
      {v : Tm Head (k + Γ.length)},
      Long S.R S.roles (.term (extendCtx names c Γ) v
        (liftClosed (BindingSignatureEmbedding.telescopeType names bound r))) →
      ∃ body, v = abstractB (Γ := Γ) bound body ∧
        Long S.R S.roles (.term (extendCtx names c (bound ++ Γ)) body (liftClosed r))
  | [], _, _, v, long => ⟨v, rfl, long⟩
  | s :: bound, Γ, r, _, long => by
      obtain ⟨body', rfl, long'⟩ := binding_view formedC bound (r := BindingSignatureEmbedding.closedArrow
        (BindingSignatureEmbedding.sortType names s) r) long
      have formed := extendCtx_formed names realization formedC (bound ++ Γ)
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at long'
      obtain ⟨b, A₁, B₁, rfl, e, _, lb⟩ := long'.lam_of_pi facts formed
      obtain ⟨eA, eB⟩ := TypeEq.pi_injective facts e formed
      obtain ⟨there, back⟩ := ctxEq_last formed eA
      exact ⟨b, rfl, ((lb.stable S.levels) back there).convType S.levels eB.symm⟩

include facts realization in
/-- A normal judged term of `Π Γ. r` is an abstraction over `Γ`. -/
theorem abstractN_view {k : Nat} {c : Ctx Head k} (formedC : CtxFormed S.R c) :
    ∀ (Γ : Binding.Ctx sig) {r : Tm Head 0} {v : Tm Head k},
      Long S.R S.roles (.term c v
        (liftClosed (BindingSignatureEmbedding.telescopeType names Γ r))) →
      ∃ body, v = abstractN Γ.length body ∧
        Long S.R S.roles (.term (extendCtx names c Γ) body (liftClosed r))
  | [], _, v, long => ⟨v, rfl, long⟩
  | s :: Γ, r, _, long => by
      obtain ⟨body', rfl, long'⟩ := abstractN_view formedC Γ (r := BindingSignatureEmbedding.closedArrow
        (BindingSignatureEmbedding.sortType names s) r) long
      have formed := extendCtx_formed names realization formedC Γ
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at long'
      obtain ⟨b, A₁, B₁, rfl, e, _, lb⟩ := long'.lam_of_pi facts formed
      obtain ⟨eA, eB⟩ := TypeEq.pi_injective facts e formed
      obtain ⟨there, back⟩ := ctxEq_last formed eA
      exact ⟨b, rfl, ((lb.stable S.levels) back there).convType S.levels eB.symm⟩

include facts complete rigid sortInjective in
/-- At a sort, the remaining arrow of a neutral spine is that sort. -/
theorem sort_result {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ) {U : Tm Head n}
    {ds : List (Tm Head 0)} {r : Tm Head 0} (base : BaseResult (S := S) names r) {s : sig.Srt}
    (eU : TypeEq S.R Δ U (liftClosed (arrows ds r)))
    (below : Below S.R Δ U (BindingSignatureEmbedding.sortType names s)) :
    ds = [] ∧ r = BindingSignatureEmbedding.sortType names s := by
  have le : Below S.R Δ (liftClosed (arrows ds r)) (BindingSignatureEmbedding.sortType names s) :=
    .subTrans eU.symm.below below
  have sortBase := sort_base facts rigid names formed s
  have sortNeutral : Neutral S.roles (BindingSignatureEmbedding.sortType names s : Tm Head n) :=
    Neutral.rigid (c := names.sort s) [] (rigid _)
  cases ds with
  | cons d rest =>
      have lifted : (liftClosed (arrows (d :: rest) r) : Tm Head n) =
          .pi (liftClosed d) (liftClosed (arrows rest r)) :=
        BindingSignatureEmbedding.liftClosed_closedArrow d (arrows rest r)
      rw [lifted] at le
      obtain ⟨_, _, eT, _⟩ := Below.pi_source facts le formed
        (IsType.refl (Below.isTypes le formed).1)
      exact absurd eT (sortBase.1 _ _)
  | nil =>
      refine ⟨rfl, ?_⟩
      rcases base with ⟨u, hu, rfl⟩ | ⟨s', rfl⟩
      · obtain ⟨v, _, eT, _⟩ := Below.universe_source facts le formed hu
          (IsType.refl (Below.isTypes le formed).1)
        exact absurd rfl ((TypeEq.neutral_form facts eT formed sortNeutral (.inl ⟨_, rfl⟩)).not_former.1 v)
      · have source := sort_base facts rigid names formed s'
        have neutral' : Neutral S.roles (BindingSignatureEmbedding.sortType names s' : Tm Head n) :=
          Neutral.rigid (c := names.sort s') [] (rigid _)
        have equal := Below.rigid le formed
          (fun u _ e => (TypeEq.neutral_form facts e formed neutral' (.inl ⟨_, rfl⟩)).not_former.1 u rfl)
          source.1 source.2
        by_cases same : names.sort s' = names.sort s
        · rw [sortInjective same]
        · obtain ⟨w, _, e⟩ := equal
          exact absurd e (not_equal_of_distinct_rigid complete formed same (rigid _) (rigid _))

/-! ## Building second-order arguments -/

/-- Metavariable arguments, read back. -/
theorem metaArgs_build (M : List (Binding.MetaArity sig)) {Γ : Binding.Ctx sig}
    {n : Nat} (f : Tm Head (M.length + Γ.length)) :
    ∀ (P : List sig.Srt) (args : List (Tm Head (M.length + Γ.length))),
      List.Forall₂ (fun a p => ∃ t : Binding.Term (Sig sig M) Γ p, encode names M t = a) args P.reverse →
      ∃ theArgs : Binding.Args (Sig sig M) (P.map fun p => (([] : List sig.Srt), p)) Γ,
        spine f (fun j : Fin P.length => encodeArgs names M theArgs (Fin.cast (by simp) j)) =
          appSpine f args
  | [], args, related => by
      cases related
      exact ⟨.nil, rfl⟩
  | p :: P, args, related => by
      rw [List.reverse_cons] at related
      obtain ⟨init, a, rfl, front, ⟨t, rfl⟩⟩ := forall₂_split_last related
      obtain ⟨rest, equation⟩ := metaArgs_build M (n := n) f P init front
      refine ⟨.cons (bs := []) t rest, ?_⟩
      rw [appSpine_append]
      show Tm.app (spine f _) _ = Tm.app (appSpine f init) (encode names M t)
      rw [← equation]
      rfl

/-- Operator arguments, read back. -/
theorem opArgs_build (M : List (Binding.MetaArity sig)) {Γ : Binding.Ctx sig} :
    ∀ (as : List (List sig.Srt × sig.Srt)) (f : Tm Head (M.length + Γ.length))
      (args : List (Tm Head (M.length + Γ.length))),
      List.Forall₂ (fun a b => ∃ t : Binding.Term (Sig sig M) (b.1 ++ Γ) b.2,
        abstractB (Γ := Γ) b.1 (encode names M t) = a) args as →
      ∃ theArgs : Binding.Args (Sig sig M) as Γ, applyVec f (encodeArgs names M theArgs) = appSpine f args
  | [], _, _, .nil => ⟨.nil, rfl⟩
  | (bound, sort) :: as, f, _ :: args, .cons ⟨t, rfl⟩ rest => by
      obtain ⟨tail, equation⟩ := opArgs_build M as (.app f (abstractB bound (encode names M t))) args rest
      exact ⟨.cons t tail, equation⟩

/-! ## Adequacy -/

variable (closed : ClosedRealization (S := S) names)

include realization facts complete rigid sortInjective closed in
/-- **Adequacy at sorts**: an η-long term at a sort over a translated telescope is the
translation of a second-order term. -/
theorem adequate_sort (M : List (Binding.MetaArity sig)) :
    ∀ (bound : Nat) {Γ : Binding.Ctx sig} {s : sig.Srt} {v : Tm Head (M.length + Γ.length)},
      size v ≤ bound →
      Long S.R S.roles (.term (extendCtx names (metaCtx names M) Γ) v
        (BindingSignatureEmbedding.sortType names s)) →
      ∃ t : Binding.Term (Sig sig M) Γ s, encode names M t = v
  | 0, _, _, v, small, _ => absurd small (by have := size_pos v; omega)
  | bound + 1, Γ, s, v, small, long => by
      have formedM : CtxFormed S.R (metaCtx (Head := Head) names M) :=
        metaCtx_formed names realization M
      have formed := extendCtx_formed names realization formedM Γ
      have sortNeutral : Neutral S.roles
          (BindingSignatureEmbedding.sortType names s : Tm Head (M.length + Γ.length)) :=
        Neutral.rigid (c := names.sort s) [] (rigid _)
      have sortBase := sort_base facts rigid names formed s
      -- At a sort, a normal term is neutral.
      obtain ⟨U, ls, le⟩ : ∃ U, Long S.R S.roles (.spine (extendCtx names (metaCtx names M) Γ) v U) ∧
          Below S.R _ U (BindingSignatureEmbedding.sortType names s) := by
        cases long with
        | univ _ e _ _ =>
            exact absurd rfl ((TypeEq.neutral_form facts e formed sortNeutral
              (.inl ⟨_, rfl⟩)).not_former.1 _)
        | lam e _ _ _ => exact absurd e (sortBase.1 _ _)
        | pair e _ _ _ => exact absurd e (sortBase.2 _ _)
        | refl e _ _ =>
            exact absurd rfl ((TypeEq.neutral_form facts e formed sortNeutral
              (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))).not_former.2.2.2 _ _ _)
        | neutral ls le _ _ => exact ⟨_, ls, le⟩
      obtain ⟨h, args, ds₁, ds₂, r, rfl, head, related, eU⟩ :=
        spine_view names facts rigid (arrowConstants names realization closed) ls formed
          (arrowContext names M Γ)
      obtain ⟨rfl, rfl⟩ := sort_result names facts complete rigid sortInjective formed head.1 eU le
      rw [List.append_nil] at head
      have smaller : ∀ a ∈ args, size a ≤ bound := fun a member => by
        have := (size_appSpine args h).1 a member
        omega
      rcases head.2 with ⟨j, rfl, lookup⟩ | ⟨c, rfl, declared⟩
      · rcases inner_or_outer j with ⟨l, rfl⟩ | ⟨i, rfl⟩
        · -- an object variable
          rw [lookup_inner names _ Γ l] at lookup
          cases ds₁ with
          | cons d rest =>
              rw [show (liftClosed (arrows (d :: rest) (BindingSignatureEmbedding.sortType names s)) :
                  Tm Head (M.length + Γ.length)) = .pi (liftClosed d) (liftClosed (arrows rest _)) from
                BindingSignatureEmbedding.liftClosed_closedArrow d _] at lookup
              cases lookup
          | nil =>
              cases related
              have sorts := sortInjective (Tm.const.inj lookup)
              subst sorts
              exact ⟨.var (varAt Γ l), by
                show Tm.var (inner (vIdx (varAt Γ l))) = _
                rw [vIdx_varAt]
                rfl⟩
        · -- a metavariable
          rw [extendCtx_outer names (metaCtx names M) (metaCtx_lookup names M i) Γ] at lookup
          unfold BindingSignatureEmbedding.bindingType at lookup
          rw [telescopeType_arrows] at lookup
          obtain ⟨rfl, sorts⟩ := arrows_eq_sorts names (liftClosed_injective lookup)
          have sorts' := sortInjective sorts
          subst sorts'
          have preimages : List.Forall₂ (fun a p => ∃ t : Binding.Term (Sig sig M) Γ p,
              encode names M t = a) args (M.get i).1.reverse := by
            rw [List.forall₂_map_right_iff] at related
            exact forall₂_imp_mem related fun a member p la =>
              adequate_sort M bound (smaller a member) la
          obtain ⟨theArgs, equation⟩ := metaArgs_build names M (n := 0) (.var (outer i)) _ args preimages
          exact ⟨.op (.inr (.mk i)) theArgs, equation⟩
      · -- a constant
        rcases closed declared with ⟨s', rfl⟩ | ⟨s', o, rfl⟩
        · rw [realization.sortLookup s'] at declared
          have same := Option.some.inj declared
          cases ds₁ with
          | nil => cases same
          | cons d rest => cases same
        · rw [realization.operatorLookup o] at declared
          have same := Option.some.inj declared
          unfold BindingSignatureEmbedding.operatorType at same
          rw [argumentsType_arrows] at same
          obtain ⟨rfl, sorts⟩ := arrows_eq_sorts names same
          have sorts' := sortInjective sorts
          subst sorts'
          have preimages : List.Forall₂ (fun a b => ∃ t : Binding.Term (Sig sig M) (b.1 ++ Γ) b.2,
              abstractB (Γ := Γ) b.1 (encode names M t) = a) args (sig.arity o) := by
            rw [List.forall₂_map_right_iff] at related
            refine forall₂_imp_mem related fun a member b la => ?_
            obtain ⟨body, rfl, lb⟩ := binding_view names realization facts formedM b.1
              (r := BindingSignatureEmbedding.sortType names b.2) la
            obtain ⟨t, rfl⟩ := adequate_sort M bound
              (le_trans (size_abstractB b.1 body) (smaller _ member)) lb
            exact ⟨t, rfl⟩
          obtain ⟨theArgs, equation⟩ := opArgs_build names M (sig.arity o) _ args preimages
          exact ⟨.op (.inl o) theArgs, equation⟩

include realization facts complete rigid sortInjective closed in
/-- **Adequacy for observations**: an η-long judged term at `Π Γ. s` over a translated
telescope is the translation of an observation. -/
theorem adequate_entry (M : List (Binding.MetaArity sig)) {Γ : Binding.Ctx sig} {s : sig.Srt}
    {v : Tm Head M.length}
    (long : Long S.R S.roles (.term (metaCtx names M) v
      (liftClosed (BindingSignatureEmbedding.bindingType names Γ s)))) :
    ∃ t : Binding.Term (Sig sig M) Γ s, abstractN Γ.length (encode names M t) = v := by
  obtain ⟨body, rfl, lb⟩ := abstractN_view names realization facts
    (metaCtx_formed names realization M) Γ long
  obtain ⟨t, rfl⟩ := adequate_sort names realization facts complete rigid sortInjective closed M
    (size body) (le_refl _) lb
  exact ⟨t, rfl⟩

end Translation

end ContextualDependentFibre
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
