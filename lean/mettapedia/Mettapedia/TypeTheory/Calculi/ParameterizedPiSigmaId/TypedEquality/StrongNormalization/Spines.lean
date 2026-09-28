import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Realizers

/-!
# Spines of computing constants

A computing constant applied to exactly as many arguments as it computes with
is inert: it is neither an introduction nor a partial application. Its reducts
are its root reducts and the spines obtained by reducing one argument.

So such a spine lies in a Kripke candidate when its arguments are strongly
normalizing and every root reduct lies in the candidate, along every sequence
of reductions of the arguments. The proof is by induction on the strong
normalization of the arguments: a list of strongly normalizing terms admits no
infinite sequence of steps of single arguments.

The identity eliminator is an instance: it computes only at reflexivity, to its
method. A realizer of an identity proof reduces to reflexivity only when the
endpoints are related, so the eliminator applied to realizers lies in every
candidate that contains the method whenever the endpoints are related.

A constant defined by one equation is another: it computes only to its
right-hand side, so its full application lies in every candidate containing
the right-hand side's instance, which then contains the instances at reduced
arguments.

The recursor on the numbers is another: it computes only at `zero` and at
`suc m`, and a realizer of a number of a given shape reduces to a numeral only
of that shape. So by induction on the shape, the recursor applied to a
realizer of a number lies in a family of candidates indexed by shapes whenever
the base case lies in the family at zero and the step sends realizers of a
shape and of the family there into the family at the successor.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace StrongNormalization

open Normalization

variable {Head : Type} {R : Rules Head} {roles : Roles Head}

/-! ## Steps of one argument -/

variable (R) in
/-- One argument of a list takes a step. -/
def ArgsStep {n : Nat} (args args' : List (Tm Head n)) : Prop :=
  ∃ pre a a' post, args = pre ++ a :: post ∧ Reduces R a a' ∧ args' = pre ++ a' :: post

theorem ArgsStep.length {n : Nat} {args args' : List (Tm Head n)} (step : ArgsStep R args args') :
    args'.length = args.length := by
  obtain ⟨pre, a, a', post, rfl, _, rfl⟩ := step
  simp

theorem ArgsStep.cons_inv {n : Nat} {a : Tm Head n} {rest args' : List (Tm Head n)}
    (step : ArgsStep R (a :: rest) args') :
    (∃ a', Reduces R a a' ∧ args' = a' :: rest) ∨
      ∃ rest', ArgsStep R rest rest' ∧ args' = a :: rest' := by
  obtain ⟨pre, x, x', post, e, s, rfl⟩ := step
  rcases pre with _ | ⟨y, pre⟩
  · simp only [List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact .inl ⟨x', s, rfl⟩
  · simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact .inr ⟨pre ++ x' :: post, ⟨pre, x, x', post, rfl, s, rfl⟩, rfl⟩

/-- Lists of strongly normalizing terms admit no infinite sequence of steps of
single arguments. -/
theorem ArgsStep.acc {n : Nat} :
    ∀ {args : List (Tm Head n)}, (∀ a ∈ args, SN R a) →
      Acc (fun v u => ArgsStep R u v) args
  | [], _ => Acc.intro _ fun _ step => by
      obtain ⟨pre, _, _, _, e, _, _⟩ := step
      simp at e
  | a :: rest, sns => by
      have key : ∀ a : Tm Head n, SN R a → ∀ rest : List (Tm Head n),
          Acc (fun v u => ArgsStep R u v) rest → Acc (fun v u => ArgsStep R u v) (a :: rest) := by
        intro a sa
        induction sa with
        | intro a _ iha =>
            intro rest hrest
            induction hrest with
            | intro rest hrest' ihrest =>
                refine Acc.intro _ fun args' step => ?_
                rcases step.cons_inv with ⟨a', s, rfl⟩ | ⟨rest', s, rfl⟩
                · exact iha a' s rest (Acc.intro rest hrest')
                · exact ihrest rest' s
      exact key a (sns a (List.mem_cons_self ..)) rest
        (ArgsStep.acc fun b hb => sns b (List.mem_cons_of_mem a hb))

/-- Along steps of single arguments, each argument reduces to the argument in
its place. -/
theorem ArgsStep.forall₂ {n : Nat} :
    ∀ {args args' : List (Tm Head n)}, ArgsStep R args args' →
      List.Forall₂ (ReducesStar R) args args'
  | [], _, step => by
      obtain ⟨pre, _, _, _, e, _, _⟩ := step
      simp at e
  | a :: rest, _, step => by
      rcases step.cons_inv with ⟨a', s, rfl⟩ | ⟨rest', s, rfl⟩
      · exact .cons (.single s) (List.forall₂_refl rest)
      · exact .cons .refl (ArgsStep.forall₂ s)

theorem forall₂_reducesStar_trans {n : Nat} :
    ∀ {l₁ l₂ l₃ : List (Tm Head n)}, List.Forall₂ (ReducesStar R) l₁ l₂ →
      List.Forall₂ (ReducesStar R) l₂ l₃ → List.Forall₂ (ReducesStar R) l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' => .cons (h.trans h') (forall₂_reducesStar_trans hs hs')

/-- Along sequences of steps of single arguments, each argument reduces to the
argument in its place. -/
theorem ArgsStep.star_forall₂ {n : Nat} {args args' : List (Tm Head n)}
    (steps : Relation.ReflTransGen (ArgsStep R) args args') :
    List.Forall₂ (ReducesStar R) args args' := by
  induction steps with
  | refl => exact List.forall₂_refl args
  | tail _ step ih => exact forall₂_reducesStar_trans ih step.forall₂

/-! ## Exact-arity spines -/

/-- A computing constant applied to exactly its number of arguments is inert. -/
theorem computingSpine_inert {c : DeclName} {arity : Nat} {scrutinee : InspectTree}
    (role : roles c = .computes arity scrutinee) {n : Nat} {args : List (Tm Head n)}
    (length : args.length = arity) : Inert roles (appSpine (.const c) args) := by
  refine ⟨fun b e => appSpine_const_ne_lam' e, fun a b e => appSpine_const_ne_pair e,
    fun a e => appSpine_const_ne_refl e, fun k arity' args' role' e => ?_,
    fun c' arity' scrutinee' args' role' short e => ?_⟩
  · obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
    rw [role] at role'
    cases role'
  · obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
    rw [role] at role'
    injection role' with same _
    rw [← same, length] at short
    exact Nat.lt_irrefl _ short

variable (shape : RootShape R roles)
include shape

/-- The reducts of a computing constant applied to exactly its number of
arguments: its root reducts, and the spines with one argument reduced. -/
theorem computingSpine_reduct {c : DeclName} {arity : Nat} {scrutinee : InspectTree}
    (role : roles c = .computes arity scrutinee) {n : Nat} {args : List (Tm Head n)}
    (length : args.length = arity) {v : Tm Head n} (step : Reduces R (appSpine (.const c) args) v) :
    R.computation.step (appSpine (.const c) args) v ∨
      ∃ args', ArgsStep R args args' ∧ v = appSpine (.const c) args' := by
  induction args using List.reverseRecOn with
  | nil =>
      cases step with
      | root r => exact .inl r
  | append_singleton init last _ =>
      rw [appSpine_concat] at step ⊢
      generalize hf : appSpine (.const c) init = f at step
      cases step with
      | betaPi body a => exact absurd hf appSpine_const_ne_lam'
      | root r => exact .inl r
      | congAppFun s =>
          subst hf
          have stuck : ∀ arity' scrutinee', roles c = .computes arity' scrutinee' →
              init.length < arity' := by
            intro arity' scrutinee' role'
            rw [role] at role'
            injection role' with same _
            rw [← same, ← length, List.length_append, List.length_singleton]
            exact Nat.lt_succ_self _
          obtain ⟨pre, a, a', post, rfl, s', rfl⟩ := constSpine_reduct shape stuck s
          refine .inr ⟨pre ++ a' :: (post ++ [last]),
            ⟨pre, a, a', post ++ [last], by simp, s', rfl⟩, ?_⟩
          rw [← appSpine_concat]
          simp
      | congAppArg s =>
          subst hf
          exact .inr ⟨init ++ [_], ⟨init, last, _, [], rfl, s, rfl⟩,
            (appSpine_concat _ _ _).symm⟩

/-- A computing constant applied to exactly its number of strongly normalizing
arguments lies in a Kripke candidate when every root reduct does, along every
sequence of reductions of single arguments. -/
theorem KCand.computingSpine_mem (X : KCand R roles) {c : DeclName} {arity : Nat}
    {scrutinee : InspectTree} (role : roles c = .computes arity scrutinee) {n : Nat}
    {args : List (Tm Head n)} (length : args.length = arity) (sns : ∀ a ∈ args, SN R a)
    (root : ∀ args', Relation.ReflTransGen (ArgsStep R) args args' →
      ∀ r, R.computation.step (appSpine (.const c) args') r → X.mem r) :
    X.mem (appSpine (.const c) args) := by
  induction ArgsStep.acc sns with
  | intro args _ ih =>
      refine X.inert (computingSpine_inert role length) fun v step => ?_
      rcases computingSpine_reduct shape role length step with r | ⟨args', s, rfl⟩
      · exact root args .refl v r
      · have length' : args'.length = arity := s.length.trans length
        refine ih args' s length' ?_ fun args'' steps r step' => root args'' (.head s steps) r step'
        intro a ha
        obtain ⟨pre, x, x', post, rfl, sx, rfl⟩ := s
        simp only [List.mem_append, List.mem_cons] at ha
        rcases ha with ha | rfl | ha
        · exact sns a (List.mem_append_left _ ha)
        · exact (sns x (by simp)).reduct sx
        · exact sns a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))


/-! ## The identity eliminator -/

/-- The identity eliminator applied to strongly normalizing arguments whose
proof argument realizes an identity proof of `Q` lies in every Kripke candidate
that contains the method whenever `Q` holds: it computes only at reflexivity,
to its method. -/
theorem KCand.eliminator_mem (reflects : RootReflectsRename R.computation) (X : KCand R roles)
    {J : DeclName} (role : roles J = .computes 6 (.split 5 .constructor fun _ => .leaf))
    (jRoot : ∀ {n : Nat} {a₀ a₁ a₂ a₃ a₄ a₅ r : Tm Head n},
      R.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅]) r →
        ∃ u, a₅ = .refl u ∧ r = a₃)
    {Q : Prop} {n : Nat} {A x P d y e : Tm Head n} (sA : SN R A) (sx : SN R x) (sP : SN R P)
    (sd : SN R d) (sy : SN R y) (he : (IdCand (roles := roles) reflects Q).mem e)
    (hd : Q → X.mem d) : X.mem (appSpine (.const J) [A, x, P, d, y, e]) := by
  refine KCand.computingSpine_mem shape X role rfl ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sA
    · exact sx
    · exact sP
    · exact sd
    · exact sy
    · exact he.1
  · intro args' steps r step
    have pointwise := ArgsStep.star_forall₂ steps
    obtain ⟨A', x', P', d', y', e', rfl, -, -, -, hd', -, he'⟩ :
        ∃ A' x' P' d' y' e', args' = [A', x', P', d', y', e'] ∧ ReducesStar R A A' ∧
          ReducesStar R x x' ∧ ReducesStar R P P' ∧ ReducesStar R d d' ∧
            ReducesStar R y y' ∧ ReducesStar R e e' := by
      rcases pointwise with _ | ⟨hA, pointwise⟩
      rcases pointwise with _ | ⟨hx, pointwise⟩
      rcases pointwise with _ | ⟨hP, pointwise⟩
      rcases pointwise with _ | ⟨hd, pointwise⟩
      rcases pointwise with _ | ⟨hy, pointwise⟩
      rcases pointwise with _ | ⟨he, pointwise⟩
      cases pointwise
      exact ⟨_, _, _, _, _, _, rfl, hA, hx, hP, hd, hy, he⟩
    obtain ⟨u, rfl, rfl⟩ := jRoot step
    exact X.reducts (hd (he.2 u he')) hd'


/-! ## The recursor on the numbers -/

section Recursor

variable {zero suc : DeclName} (reflects : RootReflectsRename R.computation)
  (numerals : NumeralRoles roles zero suc)

omit shape in
/-- A realizer of a number that reduces to `zero` has shape zero. -/
theorem NumReal.shape_of_zero {sh : NumShape} {n : Nat} {a : Tm Head n}
    (ha : (NumReal reflects numerals sh).mem a) (steps : ReducesStar R a (.const zero)) :
    sh = .zero := by
  cases sh with
  | zero => rfl
  | suc _ => exact absurd steps ha.2.1
  | star => exact absurd steps ha.2.1

omit shape in
/-- A realizer of a number that reduces to `suc m` has a successor shape, and
`m` realizes the predecessor shape. -/
theorem NumReal.shape_of_suc {sh : NumShape} {n : Nat} {a m : Tm Head n}
    (ha : (NumReal reflects numerals sh).mem a) (steps : ReducesStar R a (.app (.const suc) m)) :
    ∃ sh', sh = .suc sh' ∧ (NumReal reflects numerals sh').mem m := by
  cases sh with
  | zero => exact absurd steps (ha.2 m)
  | suc sh' => exact ⟨sh', rfl, ha.2.2 m steps⟩
  | star => exact absurd steps (ha.2.2 m)

variable (X : NumShape → KCand R roles)

/-- A step of a recursion on the numbers is realized when, after any renaming,
it sends realizers of each shape and of the family there to the family at the
successor shape. -/
def StepRealizes {n : Nat} (s : Tm Head n) : Prop :=
  ∀ (sh : NumShape) {m : Nat} (ρ : Ren n m) (b r : Tm Head m),
    (NumReal reflects numerals sh).mem b → (X sh).mem r →
      (X (.suc sh)).mem (.app (.app (Presentation.rename ρ s) b) r)

omit shape in
theorem StepRealizes.reducts {n : Nat} {s s' : Tm Head n}
    (hs : StepRealizes reflects numerals X s) (steps : ReducesStar R s s') :
    StepRealizes reflects numerals X s' := by
  intro sh m ρ b r hb hr
  exact (X (.suc sh)).reducts (hs sh ρ b r hb hr)
    (ReducesStar.app (ReducesStar.app (steps.rename ρ) .refl) .refl)

omit shape in
theorem ArgsStep.star_four {n : Nat} {p z s a : Tm Head n} {args' : List (Tm Head n)}
    (steps : Relation.ReflTransGen (ArgsStep R) [p, z, s, a] args') :
    ∃ p' z' s' a', args' = [p', z', s', a'] ∧ ReducesStar R p p' ∧ ReducesStar R z z' ∧
      ReducesStar R s s' ∧ ReducesStar R a a' := by
  have pointwise := ArgsStep.star_forall₂ steps
  rcases pointwise with _ | ⟨hp, pointwise⟩
  rcases pointwise with _ | ⟨hz, pointwise⟩
  rcases pointwise with _ | ⟨hs, pointwise⟩
  rcases pointwise with _ | ⟨ha, pointwise⟩
  cases pointwise
  exact ⟨_, _, _, _, rfl, hp, hz, hs, ha⟩

omit shape in
theorem ArgsStep.star_two {n : Nat} {x y : Tm Head n} {args' : List (Tm Head n)}
    (steps : Relation.ReflTransGen (ArgsStep R) [x, y] args') :
    ∃ x' y', args' = [x', y'] ∧ ReducesStar R x x' ∧ ReducesStar R y y' := by
  have pointwise := ArgsStep.star_forall₂ steps
  rcases pointwise with _ | ⟨hx, pointwise⟩
  rcases pointwise with _ | ⟨hy, pointwise⟩
  cases pointwise
  exact ⟨_, _, rfl, hx, hy⟩

omit shape in
theorem ArgsStep.star_six {n : Nat} {a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head n}
    {args' : List (Tm Head n)}
    (steps : Relation.ReflTransGen (ArgsStep R) [a₀, a₁, a₂, a₃, a₄, a₅] args') :
    ∃ b₀ b₁ b₂ b₃ b₄ b₅, args' = [b₀, b₁, b₂, b₃, b₄, b₅] ∧
      ReducesStar R a₀ b₀ ∧ ReducesStar R a₁ b₁ ∧ ReducesStar R a₂ b₂ ∧
      ReducesStar R a₃ b₃ ∧ ReducesStar R a₄ b₄ ∧ ReducesStar R a₅ b₅ := by
  have pointwise := ArgsStep.star_forall₂ steps
  rcases pointwise with _ | ⟨h₀, pointwise⟩
  rcases pointwise with _ | ⟨h₁, pointwise⟩
  rcases pointwise with _ | ⟨h₂, pointwise⟩
  rcases pointwise with _ | ⟨h₃, pointwise⟩
  rcases pointwise with _ | ⟨h₄, pointwise⟩
  rcases pointwise with _ | ⟨h₅, pointwise⟩
  cases pointwise
  exact ⟨_, _, _, _, _, _, rfl, h₀, h₁, h₂, h₃, h₄, h₅⟩

/-- The recursor on the numbers applied to realizers lies in a family of
candidates indexed by shapes, at the shape of the number, when its motive and
step are strongly normalizing, its base case lies in the family at zero, and
its step is realized. -/
theorem KCand.recursor_mem {rec : DeclName} (role : roles rec = .computes 4 (.split 3 .constructor fun _ => .leaf))
    (recRoot : ∀ {n : Nat} {p z s a r : Tm Head n},
      R.computation.step (appSpine (.const rec) [p, z, s, a]) r →
        (a = .const zero ∧ r = z) ∨
          ∃ m, a = .app (.const suc) m ∧
            r = .app (.app s m) (appSpine (.const rec) [p, z, s, m])) :
    ∀ (sh : NumShape) {n : Nat} {p z s a : Tm Head n}, SN R p → (X .zero).mem z → SN R s →
      StepRealizes reflects numerals X s → (NumReal reflects numerals sh).mem a →
        (X sh).mem (appSpine (.const rec) [p, z, s, a]) := by
  intro sh
  induction sh with
  | zero =>
      intro n p z s a sp hz ss hs ha
      refine KCand.computingSpine_mem shape (X .zero) role rfl ?_ ?_
      · intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl
        · exact sp
        · exact (X .zero).sn hz
        · exact ss
        · exact (NumReal reflects numerals _).sn ha
      · intro args' steps r step
        obtain ⟨p', z', s', a', rfl, _, hz', _, ha'⟩ := ArgsStep.star_four steps
        rcases recRoot step with ⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩
        · exact (X .zero).reducts hz hz'
        · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc reflects numerals ha ha'
          cases same
  | star =>
      intro n p z s a sp hz ss hs ha
      refine KCand.computingSpine_mem shape (X .star) role rfl ?_ ?_
      · intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl
        · exact sp
        · exact (X .zero).sn hz
        · exact ss
        · exact (NumReal reflects numerals _).sn ha
      · intro args' steps r step
        obtain ⟨p', z', s', a', rfl, _, _, _, ha'⟩ := ArgsStep.star_four steps
        rcases recRoot step with ⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩
        · cases NumReal.shape_of_zero reflects numerals ha ha'
        · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc reflects numerals ha ha'
          cases same
  | suc sh ih =>
      intro n p z s a sp hz ss hs ha
      refine KCand.computingSpine_mem shape (X (.suc sh)) role rfl ?_ ?_
      · intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl
        · exact sp
        · exact (X .zero).sn hz
        · exact ss
        · exact (NumReal reflects numerals _).sn ha
      · intro args' steps r step
        obtain ⟨p', z', s', a', rfl, hp', hz', hs', ha'⟩ := ArgsStep.star_four steps
        rcases recRoot step with ⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩
        · cases NumReal.shape_of_zero reflects numerals ha ha'
        · obtain ⟨sh', same, hm⟩ := NumReal.shape_of_suc reflects numerals ha ha'
          cases same
          have steps' := hs.reducts reflects numerals X hs'
          have call := ih (sp.reducts hp') ((X .zero).reducts hz hz') (ss.reducts hs') steps' hm
          have result := steps' sh idRen m _ hm call
          rwa [rename_id] at result

end Recursor


/-! ## Definitions by one equation -/

section Definitions

omit shape in
theorem forall₂_append_inv {α β : Type} {r : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, List.Forall₂ r (l₁ ++ l₂) (m₁ ++ m₂) →
      l₁.length = m₁.length → List.Forall₂ r l₁ m₁ ∧ List.Forall₂ r l₂ m₂
  | [], _, [], _, h, _ => ⟨.nil, h⟩
  | [], _, _ :: _, _, _, e => absurd e.symm (Nat.succ_ne_zero _)
  | _ :: _, _, [], _, _, e => absurd e (Nat.succ_ne_zero _)
  | _ :: _, _, _ :: _, _, .cons h hs, e => by
      obtain ⟨first, rest⟩ := forall₂_append_inv hs (Nat.succ.inj e)
      exact ⟨.cons h first, rest⟩

omit shape in
/-- Arguments of applications to one telescope that reduce pointwise come from
substitutions that reduce pointwise. -/
theorem telescopeArgs_forall₂ {m : Nat} :
    ∀ {k : Nat} (Θ : Ctx Head k) {σ σ' : Sub Head k m},
      List.Forall₂ (ReducesStar R) (telescopeArgs Θ σ) (telescopeArgs Θ σ') →
        ∀ i, ReducesStar R (σ i) (σ' i)
  | _, .nil, _, _, _, i => nomatch i
  | _, .snoc Θ _, σ, σ', h, i => by
      obtain ⟨tail, last⟩ := forall₂_append_inv h
        (by rw [telescopeArgs_length, telescopeArgs_length])
      refine Fin.cases ?_ (fun j => ?_) i
      · cases last with
        | cons h0 _ => exact h0
      · exact telescopeArgs_forall₂ Θ tail j

omit shape in
/-- Every list of arguments of the telescope's length is the list of arguments
of an instance of the telescope. -/
theorem telescopeArgs_surjective {m : Nat} :
    ∀ {k : Nat} (Θ : Ctx Head k) (args : List (Tm Head m)), args.length = k →
      ∃ σ : Sub Head k m, args = telescopeArgs Θ σ
  | _, .nil, [], _ => ⟨(fun i => Fin.elim0 i), rfl⟩
  | _, .nil, _ :: _, e => absurd e (Nat.succ_ne_zero _)
  | _, .snoc Θ _, args, e => by
      obtain ⟨init, last, rfl⟩ := (List.eq_nil_or_concat args).resolve_left (by
        intro h
        rw [h] at e
        exact absurd e.symm (Nat.succ_ne_zero _))
      rw [List.length_concat] at e
      obtain ⟨σ, rfl⟩ := telescopeArgs_surjective Θ init (Nat.succ.inj e)
      have tail : tailSub (consSub last σ) = σ := funext fun _ => rfl
      refine ⟨consSub last σ, ?_⟩
      rw [List.concat_eq_append]
      change _ = telescopeArgs Θ (tailSub (consSub last σ)) ++ [last]
      rw [tail]

omit shape in
/-- Every argument of an instance of a telescope is one of the instance's
terms. -/
theorem mem_telescopeArgs {m : Nat} :
    ∀ {k : Nat} (Θ : Ctx Head k) {σ : Sub Head k m} {a : Tm Head m},
      a ∈ telescopeArgs Θ σ → ∃ i, a = σ i
  | _, .nil, _, _, h => by simp [telescopeArgs] at h
  | _, .snoc Θ _, σ, _, h => by
      simp only [telescopeArgs, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · obtain ⟨i, rfl⟩ := mem_telescopeArgs Θ h
        exact ⟨i.succ, rfl⟩
      · exact ⟨0, rfl⟩

/-- A constant defined by one equation, applied to a strongly normalizing
instance of its telescope, lies in every Kripke candidate that contains the
instance of its right-hand side: it computes only to that instance, and to the
instances at reduced arguments, which the candidate then contains. -/
theorem KCand.definition_mem (X : KCand R roles) {f : DeclName} {k : Nat} {Θ : Ctx Head k}
    {rhs : Tm Head k} (role : roles f = .computes k .leaf)
    (defRoot : ∀ {n : Nat} {σ : Sub Head k n} {r : Tm Head n},
      R.computation.step (appSpine (.const f) (telescopeArgs Θ σ)) r →
        r = Presentation.subst σ rhs)
    {n : Nat} {σ : Sub Head k n} (sns : ∀ i, SN R (σ i))
    (unfold : X.mem (Presentation.subst σ rhs)) :
    X.mem (TelescopeAbstraction.applyClosed Θ σ (.const f)) := by
  rw [applyClosed_eq_appSpine]
  refine KCand.computingSpine_mem shape X role (telescopeArgs_length Θ σ) ?_ ?_
  · intro a ha
    obtain ⟨i, rfl⟩ := mem_telescopeArgs Θ ha
    exact sns i
  · intro args' steps r step
    have pointwise := ArgsStep.star_forall₂ steps
    have length : args'.length = k := pointwise.length_eq ▸ telescopeArgs_length Θ σ
    obtain ⟨σ', rfl⟩ : ∃ σ' : Sub Head k n, args' = telescopeArgs Θ σ' :=
      telescopeArgs_surjective Θ args' length
    rw [defRoot step]
    exact X.reducts unfold (reducesStar_subst_args rhs (telescopeArgs_forall₂ Θ pointwise))

end Definitions

end StrongNormalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
