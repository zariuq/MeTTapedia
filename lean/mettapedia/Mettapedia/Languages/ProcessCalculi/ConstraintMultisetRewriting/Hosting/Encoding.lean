import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Nodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.WellFormed

/-!
# Alternatives as rows: the encoding of a branch

An alternative of the source (a branch) is written as one row of the step,
`alt(focus, stack)`:
* the focus is `eval(c)` for a computation being run, or `value(t)` for a datum returned;
* a computation is `ret(t)`, `apply(t)`, `bind(p, c, k)` for `let_ s p c k`, `choice(c, d)`, `fail`,
  `query(space, pattern, body)`, or `outside` for the remaining constructs;
* the stack is `empty`, or `push(p, k, rest)` for a pending `let` frame `bindTo s p k`.

The encoding takes a map on data (`encComp N f`), so that instantiating the encoding is encoding the
instantiated data (`instantiate_encComp`), and an encoding depends only on its data
(`encComp_congr`). The inversion lemmas (`eval_eq_encFocus`, `ret_eq_encComp`, ...) read a node
back: a node with a given former equals an encoding only when the encoded construct has that former.

The binder site of a `let_` is not written: the names a `let` binds are opened when the equation that
contains it is used (see `Hosting.Rules`), not at the bind.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {Ty : Type}

/-! ## Vectors of one to three data -/

section Vectors

variable {α β : Type} (g : α → β)

theorem map_vec0 : (fun i : Fin 0 => g ((![] : Fin 0 → α) i)) = ![] :=
  funext fun i => i.elim0

theorem map_vec1 (a : α) : (fun i : Fin 1 => g (![a] i)) = ![g a] := by
  funext i; fin_cases i; rfl

theorem map_vec2 (a b : α) : (fun i : Fin 2 => g (![a, b] i)) = ![g a, g b] := by
  funext i; fin_cases i <;> rfl

theorem map_vec3 (a b c : α) : (fun i : Fin 3 => g (![a, b, c] i)) = ![g a, g b, g c] := by
  funext i; fin_cases i <;> rfl

theorem vec1_inj {a a' : α} (same : (![a] : Fin 1 → α) = ![a']) : a = a' := congrFun same 0

theorem vec2_inj {a b a' b' : α} (same : (![a, b] : Fin 2 → α) = ![a', b']) : a = a' ∧ b = b' :=
  ⟨congrFun same 0, congrFun same 1⟩

theorem vec3_inj {a b c a' b' c' : α} (same : (![a, b, c] : Fin 3 → α) = ![a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' :=
  ⟨congrFun same 0, congrFun same 1, congrFun same 2⟩

end Vectors

/-! ## The encoding -/

section Encoding

variable {V : Type} {D : V → MetaArity S}

/-- **A computation as a datum**, with a map on its data. -/
def encComp (f : Data κ Γ star → Term (signature S D) Γ star) : Comp κ Γ star Ty → Term (signature S D) Γ star
  | .ret t => N.node .ret ![f t]
  | .apply t => N.node .apply ![f t]
  | .let_ _ p c k => N.node .bind ![f p, encComp f c, encComp f k]
  | .choice c d => N.node .choice ![encComp f c, encComp f d]
  | .fail => N.node .fail ![]
  | .run _ => N.node .outside ![]
  | .query sp p k => N.node .query ![f sp, f p, encComp f k]
  | .add _ _ _ => N.node .outside ![]
  | .remove _ _ _ => N.node .outside ![]
  | .new _ _ _ => N.node .outside ![]
  | .check _ _ => N.node .outside ![]
  | .delay _ _ _ _ => N.node .outside ![]
  | .force _ => N.node .outside ![]

/-- **What an alternative is doing, as a datum.** -/
def encFocus (f : Data κ Γ star → Term (signature S D) Γ star) : Focus κ Γ star Ty → Term (signature S D) Γ star
  | .eval c => N.node .eval ![encComp N f c]
  | .value t => N.node .value ![f t]
  | .refused _ _ => N.node .outside ![]

/-- **What waits for the value, as a datum.** Only `let` frames are in the fragment. -/
def encStack (f : Data κ Γ star → Term (signature S D) Γ star) : List (Frame κ Γ star Ty) → Term (signature S D) Γ star
  | [] => N.node .empty ![]
  | .bindTo _ p k :: fs => N.node .push ![f p, encComp N f k, encStack f fs]
  | .checkAt _ :: _ => N.node .outside ![]
  | .memo _ :: _ => N.node .outside ![]

/-- **An alternative as a row**: `alt(focus, stack)`. -/
def encAlt (f : Data κ Γ star → Term (signature S D) Γ star) (focus : Focus κ Γ star Ty)
    (frames : List (Frame κ Γ star Ty)) : Term (signature S D) Γ star :=
  N.node .alt ![encFocus N f focus, encStack N f frames]

/-- A branch as a row. -/
abbrev encBranch (f : Data κ Γ star → Term (signature S D) Γ star) (b : Branch κ Γ star Ty) :
    Term (signature S D) Γ star :=
  encAlt N f b.focus b.frames

end Encoding

/-! ## Instantiation acts on the data -/

section Naturality

variable {V W : Type} {D : V → MetaArity S} {E : W → MetaArity S} (σ : Assignment D E)

theorem instantiate_outside :
    instantiate σ (N.node (D := D) .outside ![]) = N.node .outside ![] := by
  rw [N.instantiate_node]
  exact congrArg _ (map_vec0 _)

theorem instantiate_encComp (f : Data κ Γ star → Term (signature S D) Γ star) :
    ∀ c : Comp κ Γ star Ty, instantiate σ (encComp N f c) = encComp N (fun t => instantiate σ (f t)) c
  | .ret t => by
      rw [encComp, encComp, N.instantiate_node]
      exact congrArg _ (map_vec1 _ _)
  | .apply t => by
      rw [encComp, encComp, N.instantiate_node]
      exact congrArg _ (map_vec1 _ _)
  | .let_ _ p c k => by
      rw [encComp, encComp, N.instantiate_node]
      exact congrArg _ ((map_vec3 _ _ _ _).trans (by rw [instantiate_encComp f c, instantiate_encComp f k]))
  | .choice c d => by
      rw [encComp, encComp, N.instantiate_node]
      exact congrArg _ ((map_vec2 _ _ _).trans (by rw [instantiate_encComp f c, instantiate_encComp f d]))
  | .fail => by
      rw [encComp, encComp, N.instantiate_node]
      exact congrArg _ (map_vec0 _)
  | .run _ => instantiate_outside N σ
  | .query sp p k => by
      rw [encComp, encComp, N.instantiate_node]
      exact congrArg _ ((map_vec3 _ _ _ _).trans (by rw [instantiate_encComp f k]))
  | .add _ _ _ => instantiate_outside N σ
  | .remove _ _ _ => instantiate_outside N σ
  | .new _ _ _ => instantiate_outside N σ
  | .check _ _ => instantiate_outside N σ
  | .delay _ _ _ _ => instantiate_outside N σ
  | .force _ => instantiate_outside N σ

theorem instantiate_encFocus (f : Data κ Γ star → Term (signature S D) Γ star) :
    ∀ focus : Focus κ Γ star Ty,
      instantiate σ (encFocus N f focus) = encFocus N (fun t => instantiate σ (f t)) focus
  | .eval c => by
      rw [encFocus, encFocus, N.instantiate_node]
      exact congrArg _ ((map_vec1 _ _).trans (by rw [instantiate_encComp]))
  | .value t => by
      rw [encFocus, encFocus, N.instantiate_node]
      exact congrArg _ (map_vec1 _ _)
  | .refused _ _ => instantiate_outside N σ

theorem instantiate_encStack (f : Data κ Γ star → Term (signature S D) Γ star) :
    ∀ frames : List (Frame κ Γ star Ty),
      instantiate σ (encStack N f frames) = encStack N (fun t => instantiate σ (f t)) frames
  | [] => by
      rw [encStack, encStack, N.instantiate_node]
      exact congrArg _ (map_vec0 _)
  | .bindTo _ p k :: fs => by
      rw [encStack, encStack, N.instantiate_node]
      exact congrArg _ ((map_vec3 _ _ _ _).trans
        (by rw [instantiate_encComp, instantiate_encStack f fs]))
  | .checkAt _ :: _ => instantiate_outside N σ
  | .memo _ :: _ => instantiate_outside N σ

theorem instantiate_encAlt (f : Data κ Γ star → Term (signature S D) Γ star)
    (focus : Focus κ Γ star Ty) (frames : List (Frame κ Γ star Ty)) :
    instantiate σ (encAlt N f focus frames) = encAlt N (fun t => instantiate σ (f t)) focus frames := by
  rw [encAlt, encAlt, N.instantiate_node]
  exact congrArg _ ((map_vec2 _ _ _).trans (by rw [instantiate_encFocus, instantiate_encStack]))

end Naturality

/-! ## An encoding depends only on its data -/

section Congruence

variable {V : Type} {D : V → MetaArity S}

/-- The data of a focus. -/
def focusData : Focus κ Γ star Ty → List (Data κ Γ star)
  | .eval c => c.data
  | .value t => [t]
  | .refused t _ => [t]

/-- The data of a frame. -/
def frameData : Frame κ Γ star Ty → List (Data κ Γ star)
  | .bindTo _ p k => p :: k.data
  | .checkAt _ => []
  | .memo x => [x]

theorem encComp_congr {f g : Data κ Γ star → Term (signature S D) Γ star} :
    ∀ c : Comp κ Γ star Ty, (∀ t ∈ c.data, f t = g t) → encComp N f c = encComp N g c
  | .ret t, agree => by simp only [encComp, agree t (by simp [Comp.data])]
  | .apply t, agree => by simp only [encComp, agree t (by simp [Comp.data])]
  | .let_ _ p c k, agree => by
      have hp := agree p (by simp [Comp.data])
      have hc := encComp_congr c (fun t member => agree t (by simp [Comp.data, member]))
      have hk := encComp_congr k (fun t member => agree t (by simp [Comp.data, member]))
      simp only [encComp, hp, hc, hk]
  | .choice c d, agree => by
      have hc := encComp_congr c (fun t member => agree t (by simp [Comp.data, member]))
      have hd := encComp_congr d (fun t member => agree t (by simp [Comp.data, member]))
      simp only [encComp, hc, hd]
  | .fail, _ => rfl
  | .run _, _ => rfl
  | .query sp p k, agree => by
      have hs := agree sp (by simp [Comp.data])
      have hp := agree p (by simp [Comp.data])
      have hk := encComp_congr k (fun t member => agree t (by simp [Comp.data, member]))
      simp only [encComp, hs, hp, hk]
  | .add _ _ _, _ => rfl
  | .remove _ _ _, _ => rfl
  | .new _ _ _, _ => rfl
  | .check _ _, _ => rfl
  | .delay _ _ _ _, _ => rfl
  | .force _, _ => rfl

theorem encFocus_congr {f g : Data κ Γ star → Term (signature S D) Γ star} :
    ∀ focus : Focus κ Γ star Ty, (∀ t ∈ focusData focus, f t = g t) → encFocus N f focus = encFocus N g focus
  | .eval c, agree => by simp only [encFocus, encComp_congr N c agree]
  | .value t, agree => by simp only [encFocus, agree t (by simp [focusData])]
  | .refused _ _, _ => rfl

theorem encStack_congr {f g : Data κ Γ star → Term (signature S D) Γ star} :
    ∀ frames : List (Frame κ Γ star Ty), (∀ fr ∈ frames, ∀ t ∈ frameData fr, f t = g t) →
      encStack N f frames = encStack N g frames
  | [], _ => rfl
  | .bindTo _ p k :: fs, agree => by
      have hp := agree _ (List.mem_cons_self) p (by simp [frameData])
      have hk := encComp_congr N k (fun t member => agree _ List.mem_cons_self t (by simp [frameData, member]))
      have hs := encStack_congr fs (fun fr member t inside => agree fr (List.mem_cons_of_mem _ member) t inside)
      simp only [encStack, hp, hk, hs]
  | .checkAt _ :: _, _ => rfl
  | .memo _ :: _, _ => rfl

theorem encAlt_congr {f g : Data κ Γ star → Term (signature S D) Γ star} (focus : Focus κ Γ star Ty)
    (frames : List (Frame κ Γ star Ty)) (onFocus : ∀ t ∈ focusData focus, f t = g t)
    (onFrames : ∀ fr ∈ frames, ∀ t ∈ frameData fr, f t = g t) :
    encAlt N f focus frames = encAlt N g focus frames := by
  simp only [encAlt, encFocus_congr N focus onFocus, encStack_congr N frames onFrames]

theorem encComp_mapData (f : Data κ Γ star → Term (signature S D) Γ star)
    (g : Data κ Γ star → Data κ Γ star) :
    ∀ c : Comp κ Γ star Ty, encComp N f (c.mapData g) = encComp N (fun t => f (g t)) c
  | .ret _ => rfl
  | .apply _ => rfl
  | .let_ _ p c k => by simp only [Comp.mapData, encComp, encComp_mapData f g c, encComp_mapData f g k]
  | .choice c d => by simp only [Comp.mapData, encComp, encComp_mapData f g c, encComp_mapData f g d]
  | .fail => rfl
  | .run _ => rfl
  | .query _ _ k => by simp only [Comp.mapData, encComp, encComp_mapData f g k]
  | .add _ _ _ => rfl
  | .remove _ _ _ => rfl
  | .new _ _ _ => rfl
  | .check _ _ => rfl
  | .delay _ _ _ _ => rfl
  | .force _ => rfl

end Congruence

/-! ## Reading nodes back -/

section Inversion

variable {V : Type} {D : V → MetaArity S} (f : Data κ Γ star → Term (signature S D) Γ star)

theorem alt_eq_encAlt {x y : Term (signature S D) Γ star} {focus : Focus κ Γ star Ty}
    {frames : List (Frame κ Γ star Ty)} (same : N.node .alt ![x, y] = encAlt N f focus frames) :
    x = encFocus N f focus ∧ y = encStack N f frames :=
  vec2_inj (N.args_eq same)

theorem eval_eq_encFocus {x : Term (signature S D) Γ star} {focus : Focus κ Γ star Ty}
    (same : N.node .eval ![x] = encFocus N f focus) : ∃ c, focus = .eval c ∧ x = encComp N f c := by
  cases focus with
  | eval c => exact ⟨c, rfl, vec1_inj (N.args_eq same)⟩
  | value _ => exact absurd (N.tag_eq same) (by decide)
  | refused _ _ => exact absurd (N.tag_eq same) (by decide)

theorem value_eq_encFocus {x : Term (signature S D) Γ star} {focus : Focus κ Γ star Ty}
    (same : N.node .value ![x] = encFocus N f focus) : ∃ t, focus = .value t ∧ x = f t := by
  cases focus with
  | eval _ => exact absurd (N.tag_eq same) (by decide)
  | value t => exact ⟨t, rfl, vec1_inj (N.args_eq same)⟩
  | refused _ _ => exact absurd (N.tag_eq same) (by decide)

theorem ret_eq_encComp {x : Term (signature S D) Γ star} {c : Comp κ Γ star Ty}
    (same : N.node .ret ![x] = encComp N f c) : ∃ t, c = .ret t ∧ x = f t := by
  cases c with
  | ret t => exact ⟨t, rfl, vec1_inj (N.args_eq same)⟩
  | _ => exact absurd (N.tag_eq same) (by decide)

theorem apply_eq_encComp {x : Term (signature S D) Γ star} {c : Comp κ Γ star Ty}
    (same : N.node .apply ![x] = encComp N f c) : ∃ t, c = .apply t ∧ x = f t := by
  cases c with
  | apply t => exact ⟨t, rfl, vec1_inj (N.args_eq same)⟩
  | _ => exact absurd (N.tag_eq same) (by decide)

theorem choice_eq_encComp {x y : Term (signature S D) Γ star} {c : Comp κ Γ star Ty}
    (same : N.node .choice ![x, y] = encComp N f c) :
    ∃ c₁ c₂, c = .choice c₁ c₂ ∧ x = encComp N f c₁ ∧ y = encComp N f c₂ := by
  cases c with
  | choice c₁ c₂ => exact ⟨c₁, c₂, rfl, vec2_inj (N.args_eq same)⟩
  | _ => exact absurd (N.tag_eq same) (by decide)

theorem bind_eq_encComp {x y z : Term (signature S D) Γ star} {c : Comp κ Γ star Ty}
    (same : N.node .bind ![x, y, z] = encComp N f c) :
    ∃ s p c₁ k, c = .let_ s p c₁ k ∧ x = f p ∧ y = encComp N f c₁ ∧ z = encComp N f k := by
  cases c with
  | let_ s p c₁ k => exact ⟨s, p, c₁, k, rfl, vec3_inj (N.args_eq same)⟩
  | _ => exact absurd (N.tag_eq same) (by decide)

theorem query_eq_encComp {x y z : Term (signature S D) Γ star} {c : Comp κ Γ star Ty}
    (same : N.node .query ![x, y, z] = encComp N f c) :
    ∃ sp p k, c = .query sp p k ∧ x = f sp ∧ y = f p ∧ z = encComp N f k := by
  cases c with
  | query sp p k => exact ⟨sp, p, k, rfl, vec3_inj (N.args_eq same)⟩
  | _ => exact absurd (N.tag_eq same) (by decide)

theorem empty_eq_encStack {frames : List (Frame κ Γ star Ty)}
    (same : N.node .empty ![] = encStack N f frames) : frames = [] := by
  cases frames with
  | nil => rfl
  | cons fr fs =>
      cases fr with
      | bindTo _ _ _ => exact absurd (N.tag_eq same) (by decide)
      | checkAt _ => exact absurd (N.tag_eq same) (by decide)
      | memo _ => exact absurd (N.tag_eq same) (by decide)

theorem push_eq_encStack {x y z : Term (signature S D) Γ star} {frames : List (Frame κ Γ star Ty)}
    (same : N.node .push ![x, y, z] = encStack N f frames) :
    ∃ s p k fs, frames = .bindTo s p k :: fs ∧ x = f p ∧ y = encComp N f k ∧ z = encStack N f fs := by
  cases frames with
  | nil => exact absurd (N.tag_eq same) (by decide)
  | cons fr fs =>
      cases fr with
      | bindTo s p k => exact ⟨s, p, k, fs, rfl, vec3_inj (N.args_eq same)⟩
      | checkAt _ => exact absurd (N.tag_eq same) (by decide)
      | memo _ => exact absurd (N.tag_eq same) (by decide)

end Inversion

#print axioms instantiate_encAlt
#print axioms encAlt_congr
#print axioms encComp_mapData
#print axioms eval_eq_encFocus
#print axioms push_eq_encStack

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
