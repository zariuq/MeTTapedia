import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Preservation

/-!
# Soundness of the conversion algorithm

The type-directed conversion algorithm relates only typed-equal terms: two
terms of a type that the algorithm compares are equal at that type; two
neutral terms it compares are equal at the type it assigns, which is their
least type; and two types of a universe that it compares are equal in that
universe.

Comparing two types of a universe by their parts, without the universe,
needs the universes of the parts to lie below it. This is a property of the
universe presentation: cumulativity is a preorder compatible with head
equality, and joins are least upper bounds. The explicit tower of levels has
it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-- The order structure of cumulativity. -/
structure CumulativeAlgebra (R : Rules Head) : Prop where
  trans : ∀ {u v w : Head}, R.cumulative u v → R.cumulative v w → R.cumulative u w
  same_left : ∀ {u u' v : Head}, HeadSame R u u' → R.cumulative u' v → R.cumulative u v
  same_right : ∀ {u v v' : Head}, R.cumulative u v → HeadSame R v v' → R.cumulative u v'
  join_least : ∀ {u v w x : Head}, R.join u v w → R.cumulative u x → R.cumulative v x →
    R.cumulative w x

variable {S : Setting Head L}

section Soundness

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include facts

/-- A universe is usable only at universes cumulatively above it. -/
theorem Below.universe_cumulative (algebra : CumulativeAlgebra S.R) {n : Nat} {Γ : Ctx Head n}
    {X T : Tm Head n} (le : Below S.R Γ X T) (formed : CtxFormed S.R Γ) {w : Head}
    (hw : S.R.isUniverse w) (eX : TypeEq S.R Γ X (.head w)) :
    ∃ v, S.R.isUniverse v ∧ TypeEq S.R Γ T (.head v) ∧ S.R.cumulative w v := by
  refine Below.induction (motive := fun n Γ X T => CtxFormed S.R Γ → ∀ {w : Head},
      S.R.isUniverse w → TypeEq S.R Γ X (.head w) →
        ∃ v, S.R.isUniverse v ∧ TypeEq S.R Γ T (.head v) ∧ S.R.cumulative w v)
    ?equal ?univ ?pi ?sigma ?trans le formed hw eX
  case equal =>
    intro n Γ X T u e hu formed w hw eX
    exact ⟨w, hw, TypeEq.trans S.levels (TypeEq.symm ⟨u, hu, e⟩) eX, S.levels.cumulative_refl hw⟩
  case univ =>
    intro n Γ u₀ v₀ c formed w hw eX
    have same := TypeEq.head_injective facts eX formed
    obtain ⟨_, hv₀, _⟩ := S.levels.cumulative_universe c
    exact ⟨v₀, hv₀, IsType.refl (IsType.head_of_universe hv₀),
      algebra.same_left (HeadSame.symm S.levels same) c⟩
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ formed w hw eX
    exact absurd eX (TypeEq.pi_ne_head facts formed)
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ formed w hw eX
    exact absurd eX (TypeEq.sigma_ne_head facts formed)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed w hw eX
    obtain ⟨v₁, hv₁, eY, c₁⟩ := ih₁ formed hw eX
    obtain ⟨v, hv, eT, c₂⟩ := ih₂ formed hv₁ eY
    exact ⟨v, hv, eT, algebra.trans c₁ c₂⟩

/-- A chain of conversions and universe raises between heads, from a type equal
to a universe, is cumulativity. -/
theorem TypeLe.cumulative_of_heads (algebra : CumulativeAlgebra S.R) {n : Nat} {Γ : Ctx Head n}
    (formed : CtxFormed S.R Γ) {X Y : Tm Head n} (le : TypeLe S.R Γ X Y) :
    ∀ {w u : Head}, S.R.isUniverse w → TypeEq S.R Γ X (.head w) → Y = .head u →
      S.R.cumulative w u := by
  induction le with
  | refl =>
      intro w u hw equal e
      subst e
      have same := TypeEq.head_injective facts equal formed
      exact algebra.same_right (S.levels.cumulative_refl hw) (HeadSame.symm S.levels same)
  | @conv A B C s e hs _ ih =>
      intro w u hw equal eC
      exact ih hw (TypeEq.trans S.levels (TypeEq.symm ⟨s, hs, e⟩) equal) eC
  | @cumul a b C c _ ih =>
      intro w u hw equal eC
      have same := TypeEq.head_injective facts equal formed
      have hb := (S.levels.cumulative_universe c).2.1
      obtain ⟨b', hb', typing, _⟩ := S.levels.successor hb
      have below := ih hb (IsType.refl ⟨b', hb', .headType typing⟩) eC
      exact algebra.same_left (HeadSame.symm S.levels same) (algebra.trans c below)
  | sub le _ ih =>
      intro w u hw equal eC
      obtain ⟨v, hv, eB, c⟩ := Below.universe_cumulative facts algebra le formed hw equal
      exact algebra.trans c (ih hv eB eC)

/-- The parts of a dependent function type in a universe lie in that universe. -/
theorem Typed.pi_universe (algebra : CumulativeAlgebra S.R) {n : Nat} {Γ : Ctx Head n}
    (formed : CtxFormed S.R Γ) {A : Tm Head n} {B : Tm Head (n + 1)} {u : Head}
    (typing : Typed S.R Γ (.pi A B) (.head u)) :
    Typed S.R Γ A (.head u) ∧ Typed S.R (.snoc Γ A) B (.head u) := by
  obtain ⟨u₁, v₁, w₁, tA, hu₁, tB, hv₁, join, le⟩ := Typed.generation typing
  have hw₁ := (S.levels.join_level join).1
  obtain ⟨s, hs, typing', _⟩ := S.levels.successor hw₁
  have below := TypeLe.cumulative_of_heads facts algebra formed le hw₁
    (IsType.refl ⟨s, hs, .headType typing'⟩) rfl
  obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
  exact ⟨.cumul tA (algebra.trans c₁ below), .cumul tB (algebra.trans c₂ below)⟩

/-- The parts of a dependent pair type in a universe lie in that universe. -/
theorem Typed.sigma_universe (algebra : CumulativeAlgebra S.R) {n : Nat} {Γ : Ctx Head n}
    (formed : CtxFormed S.R Γ) {A : Tm Head n} {B : Tm Head (n + 1)} {u : Head}
    (typing : Typed S.R Γ (.sigma A B) (.head u)) :
    Typed S.R Γ A (.head u) ∧ Typed S.R (.snoc Γ A) B (.head u) := by
  obtain ⟨u₁, v₁, w₁, tA, hu₁, tB, hv₁, join, le⟩ := Typed.generation typing
  have hw₁ := (S.levels.join_level join).1
  obtain ⟨s, hs, typing', _⟩ := S.levels.successor hw₁
  have below := TypeLe.cumulative_of_heads facts algebra formed le hw₁
    (IsType.refl ⟨s, hs, .headType typing'⟩) rfl
  obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
  exact ⟨.cumul tA (algebra.trans c₁ below), .cumul tB (algebra.trans c₂ below)⟩

/-- The carrier of an identity type in a universe lies in that universe. -/
theorem Typed.id_universe (algebra : CumulativeAlgebra S.R) {n : Nat} {Γ : Ctx Head n}
    (formed : CtxFormed S.R Γ) {C x y : Tm Head n} {u : Head}
    (typing : Typed S.R Γ (.id C x y) (.head u)) :
    Typed S.R Γ C (.head u) ∧ Typed S.R Γ x C ∧ Typed S.R Γ y C := by
  obtain ⟨u₁, tC, hu₁, tx, ty, le⟩ := Typed.generation typing
  obtain ⟨s, hs, typing', _⟩ := S.levels.successor hu₁
  have below := TypeLe.cumulative_of_heads facts algebra formed le hu₁
    (IsType.refl ⟨s, hs, .headType typing'⟩) rfl
  exact ⟨.cumul tC below, tx, ty⟩

/-- A type equal to a dependent function type that is below another dependent
function type has an equal domain and a codomain usable at the other's. -/
theorem TypeLe.pi_parts_of_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {U A A₁ : Tm Head n} {B B₁ : Tm Head (n + 1)} {s : Head} (hs : S.R.isUniverse s)
    (equal : Equal S.R Γ U (.pi A B) (.head s)) (le : TypeLe S.R Γ U (.pi A₁ B₁))
    (type₁ : IsType S.R Γ (.pi A₁ B₁)) :
    TypeEq S.R Γ A A₁ ∧ Below S.R (.snoc Γ A) B B₁ :=
  TypeLe.pi_parts facts (.conv (.symm equal) hs le) type₁ formed

/-- A type equal to a dependent pair type that is below another dependent pair
type has a domain and a codomain usable at the other's. -/
theorem TypeLe.sigma_parts_of_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {U A A₁ : Tm Head n} {B B₁ : Tm Head (n + 1)} {s : Head} (hs : S.R.isUniverse s)
    (equal : Equal S.R Γ U (.sigma A B) (.head s)) (le : TypeLe S.R Γ U (.sigma A₁ B₁))
    (type₁ : IsType S.R Γ (.sigma A₁ B₁)) :
    Below S.R Γ A A₁ ∧ Below S.R (.snoc Γ A) B B₁ :=
  TypeLe.sigma_parts facts (.conv (.symm equal) hs le) type₁ formed

omit facts in
/-- What an algorithm derivation guarantees about typed terms. -/
def AlgorithmSound (S : Setting Head L) : AlgorithmStatement Head → Prop
  | .compare Γ a b T => CtxFormed S.R Γ → Typed S.R Γ a T → Typed S.R Γ b T →
      Equal S.R Γ a b T
  | .neutral Γ a b U => CtxFormed S.R Γ → ∀ {X Y}, Typed S.R Γ a X → Typed S.R Γ b Y →
      Typed S.R Γ a U ∧ Typed S.R Γ b U ∧ Equal S.R Γ a b U ∧
        (∀ {X'}, Typed S.R Γ a X' → TypeLe S.R Γ U X') ∧
        (∀ {Y'}, Typed S.R Γ b Y' → TypeLe S.R Γ U Y')
  | .types Γ A B => CtxFormed S.R Γ → ∀ {u : Head}, S.R.isUniverse u →
      Typed S.R Γ A (.head u) → Typed S.R Γ B (.head u) → Equal S.R Γ A B (.head u)

include roots heads algebra

/-- Soundness of the conversion algorithm. -/
theorem Algorithm.sound {st : AlgorithmStatement Head} (derivation : Algorithm S.R st) :
    AlgorithmSound S st := by
  induction derivation with
  | @pi n Γ a b T A B red _ ih =>
      intro formed ta tb
      obtain ⟨s, hs, tT⟩ := Typed.isType ta formed
      obtain ⟨tPi, eT⟩ := Reduces.preserve facts roots heads formed red tT
      have change : TypeEq S.R Γ T (.pi A B) := ⟨s, hs, eT⟩
      have ta' := Typed.convType ta change
      have tb' := Typed.convType tb change
      obtain ⟨⟨u₁, hu₁, tA⟩, _⟩ := IsType.pi_parts ⟨s, hs, tPi⟩
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed ⟨u₁, hu₁, tA⟩
      have apply : ∀ {f : Tm Head n}, Typed S.R Γ f (.pi A B) →
          Typed S.R (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0)) B := by
        intro f tf
        have tw : Typed S.R (.snoc Γ A) (Presentation.rename wk f)
            (.pi (Presentation.rename wk A) (Presentation.rename (liftRen wk) B)) :=
          Typed.weaken tf
        have tapp := Derivable.appElim tw (.var 0 : Typed S.R (.snoc Γ A) (.var 0) _)
        rwa [inst0_var_rename_liftRen_wk] at tapp
      exact Equal.convType (.etaPi ta' tb' (ih formedA (apply ta') (apply tb')))
        (TypeEq.symm change)
  | @sigma n Γ a b T A B red _ _ ihFst ihSnd =>
      intro formed ta tb
      obtain ⟨s, hs, tT⟩ := Typed.isType ta formed
      obtain ⟨tSigma, eT⟩ := Reduces.preserve facts roots heads formed red tT
      have change : TypeEq S.R Γ T (.sigma A B) := ⟨s, hs, eT⟩
      have ta' := Typed.convType ta change
      have tb' := Typed.convType tb change
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
      have eFst := ihFst formed (.fstElim ta') (.fstElim tb')
      have sndChange := TypeEq.symm (TypeEq.of_instantiateEq family hv (.fstElim ta') eFst)
      have eSnd := ihSnd formed (.sndElim ta') (Typed.convType (.sndElim tb') sndChange)
      exact Equal.convType (.etaSigma ta' tb' eFst eSnd) (TypeEq.symm change)
  | @sort n Γ a b T u red hu _ ih =>
      intro formed ta tb
      obtain ⟨s, hs, tT⟩ := Typed.isType ta formed
      obtain ⟨_, eT⟩ := Reduces.preserve facts roots heads formed red tT
      have change : TypeEq S.R Γ T (.head u) := ⟨s, hs, eT⟩
      exact Equal.convType (ih formed hu (Typed.convType ta change) (Typed.convType tb change))
        (TypeEq.symm change)
  | @reflexivity n Γ a b T A x y a' b' redT redA redB _ ih =>
      intro formed ta tb
      obtain ⟨s, hs, tT⟩ := Typed.isType ta formed
      obtain ⟨tId, eT⟩ := Reduces.preserve facts roots heads formed redT tT
      have change : TypeEq S.R Γ T (.id A x y) := ⟨s, hs, eT⟩
      obtain ⟨tRefl, ea⟩ := Reduces.preserve facts roots heads formed redA
        (Typed.convType ta change)
      obtain ⟨tRefl', eb⟩ := Reduces.preserve facts roots heads formed redB
        (Typed.convType tb change)
      /- The subject of a reflexivity proof of `Id A x y` is a term of `A` equal to
      both endpoints. -/
      have subject : ∀ {c : Tm Head n}, Typed S.R Γ (.refl c) (.id A x y) →
          Typed S.R Γ c A ∧ Equal S.R Γ c x A ∧ Equal S.R Γ c y A := by
        intro c tc
        obtain ⟨A₁, tc₁, le⟩ := Typed.generation tc
        obtain ⟨u₁, hu₁, tA₁⟩ := Typed.isType tc₁ formed
        have equal := TypeLe.id_eq facts le (Typed.isType tc formed) formed
        obtain ⟨eA, ecx, ecy⟩ := TypeEq.id_injective facts equal formed
        exact ⟨Typed.convType tc₁ eA, Equal.convType ecx eA, Equal.convType ecy eA⟩
      obtain ⟨ta'', eax, eay⟩ := subject tRefl
      obtain ⟨tb'', _, _⟩ := subject tRefl'
      obtain ⟨u, hu, tA⟩ := Typed.isType ta'' formed
      have toId : TypeEq S.R Γ (.id A a' a') (.id A x y) := ⟨u, hu, .idCong (.refl tA) hu eax eay⟩
      have middle := Equal.convType (Derivable.reflCong (ih formed ta'' tb'')) toId
      exact Equal.convType (.trans ea (.trans middle (.symm eb))) (TypeEq.symm change)
  | @neutralAt n Γ a b T a' b' U redA redB _ ih =>
      intro formed ta tb
      obtain ⟨ta', ea⟩ := Reduces.preserve facts roots heads formed redA ta
      obtain ⟨tb', eb⟩ := Reduces.preserve facts roots heads formed redB tb
      obtain ⟨_, _, e, principal, _⟩ := ih formed ta' tb'
      exact .trans ea (.trans (Equal.subsume e (principal ta')) (.symm eb))
  | var i =>
      intro formed X Y _ _
      exact ⟨.var i, .var i, .refl (.var i), fun h => Typed.generation h,
        fun h => Typed.generation h⟩
  | @const n Γ name type declared =>
      intro formed X Y tc _
      obtain ⟨type', u, declared', tType, hu, _⟩ := Typed.generation tc
      rw [declared] at declared'
      obtain rfl := Option.some.inj declared'
      have typing : Typed S.R Γ (.const name) (liftClosed type) := .const declared tType hu
      have principal : ∀ {X'}, Typed S.R Γ (.const name) X' → TypeLe S.R Γ (liftClosed type) X' := by
        intro X' h
        obtain ⟨type'', u', declared'', _, _, le⟩ := Typed.generation h
        rw [declared] at declared''
        obtain rfl := Option.some.inj declared''
        exact le
      exact ⟨typing, typing, .refl typing, principal, principal⟩
  | @app n Γ f g a b U A B _ red _ ihF ihA =>
      intro formed X Y tfa tgb
      obtain ⟨A₁, B₁, tf, ta₁, _⟩ := Typed.generation tfa
      obtain ⟨A₂, B₂, tg, tb₂, _⟩ := Typed.generation tgb
      obtain ⟨tfU, tgU, efg, pf, pg⟩ := ihF formed tf tg
      obtain ⟨s, hs, tU⟩ := Typed.isType tfU formed
      obtain ⟨tPi, eU⟩ := Reduces.preserve facts roots heads formed red tU
      have change : TypeEq S.R Γ U (.pi A B) := ⟨s, hs, eU⟩
      obtain ⟨eA₁, _⟩ := TypeLe.pi_parts_of_equal facts formed hs eU (pf tf)
        (Typed.isType tf formed)
      obtain ⟨eA₂, _⟩ := TypeLe.pi_parts_of_equal facts formed hs eU (pg tg)
        (Typed.isType tg formed)
      have ta := Typed.convType ta₁ (TypeEq.symm eA₁)
      have tb := Typed.convType tb₂ (TypeEq.symm eA₂)
      have eab := ihA formed ta tb
      obtain ⟨_, v, hv, family⟩ := IsType.pi_parts ⟨s, hs, tPi⟩
      have tf' := Typed.convType tfU change
      have tg' := Typed.convType tgU change
      have argChange := TypeEq.of_instantiateEq family hv ta eab
      refine ⟨.appElim tf' ta, Typed.convType (.appElim tg' tb) (TypeEq.symm argChange),
        .appCong (Equal.convType efg change) eab, ?_, ?_⟩
      · intro X' h
        obtain ⟨A₃, B₃, tf₃, ta₃, le₃⟩ := Typed.generation h
        obtain ⟨_, leB₃⟩ := TypeLe.pi_parts_of_equal facts formed hs eU (pf tf₃)
          (Typed.isType tf₃ formed)
        exact .sub (Derivable.substitutes leB₃ (SubstMor.single ta)) le₃
      · intro Y' h
        obtain ⟨A₄, B₄, tg₄, tb₄, le₄⟩ := Typed.generation h
        obtain ⟨_, leB₄⟩ := TypeLe.pi_parts_of_equal facts formed hs eU (pg tg₄)
          (Typed.isType tg₄ formed)
        obtain ⟨w₁, hw₁, e₁⟩ := argChange
        exact .conv e₁ hw₁ (.sub (Derivable.substitutes leB₄ (SubstMor.single tb)) le₄)
  | @fst n Γ p q U A B _ red ih =>
      intro formed X Y tfp tfq
      obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tfp
      obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tfq
      obtain ⟨tpU, tqU, epq, pp, pq⟩ := ih formed tp tq
      obtain ⟨s, hs, tU⟩ := Typed.isType tpU formed
      obtain ⟨tSigma, eU⟩ := Reduces.preserve facts roots heads formed red tU
      have change : TypeEq S.R Γ U (.sigma A B) := ⟨s, hs, eU⟩
      have tp' := Typed.convType tpU change
      have tq' := Typed.convType tqU change
      refine ⟨.fstElim tp', .fstElim tq', .fstCong (Equal.convType epq change), ?_, ?_⟩
      · intro X' h
        obtain ⟨A₃, B₃, tp₃, le₃⟩ := Typed.generation h
        obtain ⟨leA₃, _⟩ := TypeLe.sigma_parts_of_equal facts formed hs eU (pp tp₃)
          (Typed.isType tp₃ formed)
        exact .sub leA₃ le₃
      · intro Y' h
        obtain ⟨A₄, B₄, tq₄, le₄⟩ := Typed.generation h
        obtain ⟨leA₄, _⟩ := TypeLe.sigma_parts_of_equal facts formed hs eU (pq tq₄)
          (Typed.isType tq₄ formed)
        exact .sub leA₄ le₄
  | @snd n Γ p q U A B _ red ih =>
      intro formed X Y tsp tsq
      obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tsp
      obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tsq
      obtain ⟨tpU, tqU, epq, pp, pq⟩ := ih formed tp tq
      obtain ⟨s, hs, tU⟩ := Typed.isType tpU formed
      obtain ⟨tSigma, eU⟩ := Reduces.preserve facts roots heads formed red tU
      have change : TypeEq S.R Γ U (.sigma A B) := ⟨s, hs, eU⟩
      have tp' := Typed.convType tpU change
      have tq' := Typed.convType tqU change
      have epq' := Equal.convType epq change
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
      have fstChange := TypeEq.of_instantiateEq family hv (.fstElim tp') (.fstCong epq')
      refine ⟨.sndElim tp', Typed.convType (.sndElim tq') (TypeEq.symm fstChange),
        .sndCong epq', ?_, ?_⟩
      · intro X' h
        obtain ⟨A₃, B₃, tp₃, le₃⟩ := Typed.generation h
        obtain ⟨_, leB₃⟩ := TypeLe.sigma_parts_of_equal facts formed hs eU (pp tp₃)
          (Typed.isType tp₃ formed)
        exact .sub (Derivable.substitutes leB₃ (SubstMor.single (.fstElim tp'))) le₃
      · intro Y' h
        obtain ⟨A₄, B₄, tq₄, le₄⟩ := Typed.generation h
        obtain ⟨_, leB₄⟩ := TypeLe.sigma_parts_of_equal facts formed hs eU (pq tq₄)
          (Typed.isType tq₄ formed)
        obtain ⟨w₁, hw₁, e₁⟩ := fstChange
        exact .conv e₁ hw₁ (.sub (Derivable.substitutes leB₄ (SubstMor.single (.fstElim tq'))) le₄)
  | @heads n Γ A B h h' redA redB same =>
      intro formed u hu tA tB
      obtain ⟨tH, eA⟩ := Reduces.preserve facts roots heads formed redA tA
      obtain ⟨tH', eB⟩ := Reduces.preserve facts roots heads formed redB tB
      exact .trans eA (.trans (headEquality same tH tH') (.symm eB))
  | @piTypes n Γ A B A₁ A₂ B₁ B₂ redA redB _ _ ihDom ihCod =>
      intro formed u hu tA tB
      obtain ⟨tPi₁, eA⟩ := Reduces.preserve facts roots heads formed redA tA
      obtain ⟨tPi₂, eB⟩ := Reduces.preserve facts roots heads formed redB tB
      obtain ⟨tA₁, tB₁⟩ := Typed.pi_universe facts algebra formed tPi₁
      obtain ⟨tA₂, tB₂⟩ := Typed.pi_universe facts algebra formed tPi₂
      have eDom := ihDom formed hu tA₁ tA₂
      have tB₂' := Typed.ctxConv tB₂ (TypeEq.symm ⟨u, hu, eDom⟩)
      have eCod := ihCod (.snoc formed ⟨u, hu, tA₁⟩) hu tB₁ tB₂'
      obtain ⟨w, join⟩ := S.levels.join_exists hu hu
      have c := algebra.join_least join (S.levels.cumulative_refl hu) (S.levels.cumulative_refl hu)
      exact .trans eA (.trans (.cumulEq (.piCong eDom hu eCod hu join) c) (.symm eB))
  | @sigmaTypes n Γ A B A₁ A₂ B₁ B₂ redA redB _ _ ihDom ihCod =>
      intro formed u hu tA tB
      obtain ⟨tSigma₁, eA⟩ := Reduces.preserve facts roots heads formed redA tA
      obtain ⟨tSigma₂, eB⟩ := Reduces.preserve facts roots heads formed redB tB
      obtain ⟨tA₁, tB₁⟩ := Typed.sigma_universe facts algebra formed tSigma₁
      obtain ⟨tA₂, tB₂⟩ := Typed.sigma_universe facts algebra formed tSigma₂
      have eDom := ihDom formed hu tA₁ tA₂
      have tB₂' := Typed.ctxConv tB₂ (TypeEq.symm ⟨u, hu, eDom⟩)
      have eCod := ihCod (.snoc formed ⟨u, hu, tA₁⟩) hu tB₁ tB₂'
      obtain ⟨w, join⟩ := S.levels.join_exists hu hu
      have c := algebra.join_least join (S.levels.cumulative_refl hu) (S.levels.cumulative_refl hu)
      exact .trans eA (.trans (.cumulEq (.sigmaCong eDom hu eCod hu join) c) (.symm eB))
  | @idTypes n Γ A B C C' x x' y y' redA redB _ _ _ ihTy ihX ihY =>
      intro formed u hu tA tB
      obtain ⟨tId, eA⟩ := Reduces.preserve facts roots heads formed redA tA
      obtain ⟨tId', eB⟩ := Reduces.preserve facts roots heads formed redB tB
      obtain ⟨tC, tx, ty⟩ := Typed.id_universe facts algebra formed tId
      obtain ⟨tC', tx', ty'⟩ := Typed.id_universe facts algebra formed tId'
      have eC := ihTy formed hu tC tC'
      have back : TypeEq S.R Γ C' C := TypeEq.symm ⟨u, hu, eC⟩
      have ex := ihX formed tx (Typed.convType tx' back)
      have ey := ihY formed ty (Typed.convType ty' back)
      exact .trans eA (.trans (.idCong eC hu ex ey) (.symm eB))
  | @neutralTypes n Γ A B A' B' U redA redB _ ih =>
      intro formed u hu tA tB
      obtain ⟨tA', eA⟩ := Reduces.preserve facts roots heads formed redA tA
      obtain ⟨tB', eB⟩ := Reduces.preserve facts roots heads formed redB tB
      obtain ⟨_, _, e, principal, _⟩ := ih formed tA' tB'
      exact .trans eA (.trans (Equal.subsume e (principal tA')) (.symm eB))

end Soundness

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
