import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursiveCallAbstraction

/-!
# Declared computations along call substitutions

The root computations of declared constants rewrite applications of those
constants whose arguments match their patterns. When `f` is none of the
rewritten constants and none of the constructors a pattern names, an
application of the image of a term without `f` is the image of an application
of the term: a call of `f` is never a pattern's constructor form. So the
recursor's computation rules reflect along call substitutions for `f`, and
they rewrite applications of constants other than `f`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type}

section Spines

variable {f : DeclName} {k : Nat} {n m : Nat} {τ : Sub Head n m}

/-- An application of a constant other than `f` that is the image of a term
without `f` is the image of an application of that constant. -/
theorem subst_eq_constSpine (call : CallSub f k τ) {c : DeclName} (hc : c ≠ f)
    {t : Tm Head n} (free : ConstFree f t) :
    ∀ {as : List (Tm Head m)}, Presentation.subst τ t = appSpine (.const c) as →
      ∃ as', t = appSpine (.const c) as' ∧ as'.map (Presentation.subst τ) = as ∧
        ∀ a ∈ as', ConstFree f a := by
  induction t with
  | var i =>
      intro as h
      exfalso
      rcases call.shape i with ⟨j, hj⟩ | ⟨xs, _, hx⟩
      · simp only [Presentation.subst, hj] at h
        exact appSpine_const_ne_var h.symm
      · simp only [Presentation.subst, hx] at h
        exact hc (appSpine_const_injective h).1.symm
  | const c' =>
      intro as h
      simp only [Presentation.subst] at h
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective (show appSpine (.const c') [] = _ from h)
      exact ⟨[], rfl, rfl, by simp⟩
  | app g a ihg _ =>
      intro as h
      simp only [Presentation.subst] at h
      obtain ⟨init, rfl, hg⟩ := appSpine_const_eq_app h.symm
      obtain ⟨init', rfl, hmap, hfree⟩ := ihg call free.1 hg
      refine ⟨init' ++ [a], (appSpine_concat _ _ _).symm, by simp [hmap], ?_⟩
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hfree b hb
      · rw [List.mem_singleton.mp hb]; exact free.2
  | head c' =>
      intro as h
      exact absurd h.symm (appSpine_const_ne_former (.inl ⟨_, rfl⟩))
  | pi A B _ _ =>
      intro as h
      exact absurd h.symm (appSpine_const_ne_former (.inr (.inl ⟨_, _, rfl⟩)))
  | sigma A B _ _ =>
      intro as h
      exact absurd h.symm (appSpine_const_ne_former (.inr (.inr (.inl ⟨_, _, rfl⟩))))
  | id A a b _ _ _ =>
      intro as h
      exact absurd h.symm (appSpine_const_ne_former (.inr (.inr (.inr ⟨_, _, _, rfl⟩))))
  | lam b _ =>
      intro as h
      exact absurd h.symm appSpine_const_ne_lam'
  | pair a b _ _ =>
      intro as h
      exact absurd h.symm appSpine_const_ne_pair
  | fst p _ =>
      intro as h
      exact absurd h.symm appSpine_const_ne_fst
  | snd p _ =>
      intro as h
      exact absurd h.symm appSpine_const_ne_snd
  | refl a _ =>
      intro as h
      exact absurd h.symm appSpine_const_ne_refl

end Spines

section Iota

variable {f rec : DeclName} {ctors : List (DeclName × List (Field Head))}

theorem recArgs_subset {n : Nat} :
    ∀ (fields : List (Field Head)) (as : List (Tm Head n)), ∀ a ∈ recArgs fields as, a ∈ as
  | .recursive :: fs, a :: as => by
      intro b hb
      change b ∈ a :: recArgs fs as at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (recArgs_subset fs as b hb)
  | .closed _ :: fs, a :: as => by
      intro b hb
      change b ∈ recArgs fs as at hb
      exact List.mem_cons_of_mem _ (recArgs_subset fs as b hb)
  | [], _ => by intro b hb; exact absurd hb (by simp [recArgs])
  | .recursive :: _, [] => by intro b hb; exact absurd hb (by simp [recArgs])
  | .closed _ :: _, [] => by intro b hb; exact absurd hb (by simp [recArgs])

/-- The recursor's computation rules rewrite applications of the recursor. -/
theorem iotaComputation_spine {n : Nat} {l r : Tm Head n} (step : IotaStep rec ctors l r) :
    ∃ args, l = appSpine (.const rec) args := by
  obtain ⟨p, ms, _, _, _, args, _, _, _, _, _, rfl, _⟩ := step
  exact ⟨_, rfl⟩

/-- The recursor's computation rules reflect along call substitutions for a
constant that is neither the recursor nor a constructor. -/
theorem iotaComputation_reflects {k : Nat} (hrec : rec ≠ f)
    (hctors : ∀ {c : DeclName} {fields : List (Field Head)}, (c, fields) ∈ ctors → c ≠ f) :
    ∀ {n m : Nat} {τ : Sub Head n m}, CallSub f k τ → ∀ {t : Tm Head n} {w : Tm Head m},
      ConstFree f t → IotaStep rec ctors (Presentation.subst τ t) w →
        ∃ w', IotaStep rec ctors t w' ∧ w = Presentation.subst τ w' ∧ ConstFree f w' := by
  intro n m τ call t w free step
  obtain ⟨p, ms, i, c, fields, args, mt, hms, hi, has, hm, hl, rfl⟩ := step
  have hc : c ≠ f := hctors (List.mem_of_getElem? hi)
  obtain ⟨as', rfl, hmap, hfree⟩ := subst_eq_constSpine call hrec free hl
  obtain ⟨p', rest', rfl, hp, hrest⟩ := List.map_eq_cons_iff.mp hmap
  obtain ⟨ms', xs', rfl, hms', hx⟩ := List.map_eq_append_iff.mp hrest
  obtain ⟨x', rfl, hx'⟩ := List.map_eq_singleton_iff.mp hx
  have freeX : ConstFree f x' := hfree x' (by simp)
  obtain ⟨args', rfl, hargs, hfreeArgs⟩ := subst_eq_constSpine call hc freeX hx'
  have hmi : (ms'.map (Presentation.subst τ))[i]? = some mt := by rw [hms']; exact hm
  rw [List.getElem?_map] at hmi
  obtain ⟨mt', hmt', rfl⟩ := Option.map_eq_some_iff.mp hmi
  have freeP : ConstFree f p' := hfree p' (by simp)
  have freeMs : ∀ a ∈ ms', ConstFree f a := fun a ha => hfree a (by simp [ha])
  have freeM : ConstFree f mt' := freeMs mt' (List.mem_of_getElem? hmt')
  refine ⟨appSpine mt' (args' ++ (recArgs fields args').map (recApp rec (p' :: ms'))),
    ⟨p', ms', i, c, fields, args', mt', by rw [← hms, ← hms', List.length_map], hi,
      by rw [← has, ← hargs, List.length_map], hmt', rfl, rfl⟩, ?_, ?_⟩
  · rw [subst_appSpine, List.map_append, ← hargs, List.map_map, ← map_recArgs, List.map_map]
    congr 2
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply, subst_recApp, List.map_cons, hp, hms']
  · refine ConstFree.appSpine freeM ?_
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfreeArgs a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      refine ConstFree.appSpine (constFree_const.mpr hrec) ?_
      intro d hd
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff,
        or_false] at hd
      rcases hd with rfl | hd | rfl
      · exact freeP
      · exact freeMs d hd
      · exact hfreeArgs d (recArgs_subset fields args' d hb)

end Iota


/-! ## Deciding that a closed term does not mention a constant -/

/-- Whether the constant `f` occurs in `t`. -/
def mentionsConst (f : DeclName) : {n : Nat} → Tm Head n → Bool
  | _, .var _ => false
  | _, .const c => c == f
  | _, .head _ => false
  | _, .pi A B => mentionsConst f A || mentionsConst f B
  | _, .sigma A B => mentionsConst f A || mentionsConst f B
  | _, .id A a b => mentionsConst f A || mentionsConst f a || mentionsConst f b
  | _, .lam b => mentionsConst f b
  | _, .app g a => mentionsConst f g || mentionsConst f a
  | _, .pair a b => mentionsConst f a || mentionsConst f b
  | _, .fst p => mentionsConst f p
  | _, .snd p => mentionsConst f p
  | _, .refl a => mentionsConst f a

theorem ConstFree.of_mentions {f : DeclName} {n : Nat} {t : Tm Head n}
    (h : mentionsConst f t = false) : ConstFree f t := by
  induction t with
  | var => trivial
  | const c =>
      simp only [mentionsConst, beq_eq_false_iff_ne] at h
      exact h
  | head => trivial
  | pi A B ihA ihB =>
      simp only [mentionsConst, Bool.or_eq_false_iff] at h
      exact ⟨ihA h.1, ihB h.2⟩
  | sigma A B ihA ihB =>
      simp only [mentionsConst, Bool.or_eq_false_iff] at h
      exact ⟨ihA h.1, ihB h.2⟩
  | id A a b ihA iha ihb =>
      simp only [mentionsConst, Bool.or_eq_false_iff] at h
      exact ⟨ihA h.1.1, iha h.1.2, ihb h.2⟩
  | lam b ih => exact ih h
  | app g a ihg iha =>
      simp only [mentionsConst, Bool.or_eq_false_iff] at h
      exact ⟨ihg h.1, iha h.2⟩
  | pair a b iha ihb =>
      simp only [mentionsConst, Bool.or_eq_false_iff] at h
      exact ⟨iha h.1, ihb h.2⟩
  | fst p ih => exact ih h
  | snd p ih => exact ih h
  | refl a ih => exact ih h

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
