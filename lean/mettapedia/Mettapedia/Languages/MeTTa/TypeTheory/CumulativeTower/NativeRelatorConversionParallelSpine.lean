import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionParallel

/-!
# Rigid spines for the combined native parallel relation

All three eliminator heads retain their distinct arities. Below those arities,
and for the constructor heads, a parallel development is necessarily structural.
The recovered fields retain authored argument order and every metadata slot.
These are inversion laws for proof-side parallel development, not runtime rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorConversionParallel

open Presentation NativeIndexedFamilies

variable {n : Nat}

/-- Arguments are outermost first. -/
def spine (name : DeclName) : List (Tower.Tm n) → Tower.Tm n
  | [] => .const name
  | argument :: rest => .app (spine name rest) argument

def spineHead : Tower.Tm n → Option DeclName
  | .const name => some name
  | .app function _ => spineHead function
  | _ => none

def spineDepth : Tower.Tm n → Nat
  | .app function _ => spineDepth function + 1
  | _ => 0

theorem spine_injective (name : DeclName) : Function.Injective (spine (n := n) name) := by
  intro first
  induction first with
  | nil =>
      intro second equality
      cases second with
      | nil => rfl
      | cons _ _ => cases equality
  | cons argument rest ih =>
      intro second equality
      cases second with
      | nil => cases equality
      | cons argument' rest' =>
          obtain ⟨tail, head⟩ := Tm.app.inj equality
          exact congrArg₂ List.cons head (ih tail)

@[simp] theorem spineHead_spine (name : DeclName) (arguments : List (Tower.Tm n)) :
    spineHead (spine name arguments) = some name := by
  induction arguments with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem spineDepth_spine (name : DeclName) (arguments : List (Tower.Tm n)) :
    spineDepth (spine name arguments) = arguments.length := by
  induction arguments with
  | nil => rfl
  | cons _ _ ih => exact congrArg (fun count => count + 1) ih

/-- None of the three eliminator roots can contract this spine. -/
def Rigidity (name : DeclName) (arity : Nat) : Prop :=
  (name ≠ Intrinsic.eliminateName ∨ arity < 5) ∧
  (name ≠ Intrinsic.identityEliminateName ∨ arity < 6) ∧
  (name ≠ IntrinsicRelator.eliminateName ∨ arity < 9)

private theorem Rigidity.shorten {name : DeclName} {arity : Nat}
    (rigid : Rigidity name (arity + 1)) : Rigidity name arity := by
  rcases rigid with ⟨first, second, third⟩
  constructor
  · rcases first with different | short
    · exact .inl different
    · exact .inr (by omega)
  constructor
  · rcases second with different | short
    · exact .inl different
    · exact .inr (by omega)
  · rcases third with different | short
    · exact .inl different
    · exact .inr (by omega)

private theorem spine_inversion_aux {source target : Tower.Tm n} (parallel : Par source target) :
    ∀ name arguments, source = spine name arguments →
      Rigidity name arguments.length →
      ∃ arguments', target = spine name arguments' ∧ List.Forall₂ Par arguments arguments' := by
  induction parallel with
  | const original =>
      intro name arguments equality _
      cases arguments with
      | nil => cases equality; exact ⟨[], rfl, .nil⟩
      | cons argument rest => cases equality
  | @app n function function' argument argument' functionStep argumentStep ihFunction _ =>
      intro name arguments equality rigid
      cases arguments with
      | nil => cases equality
      | cons first rest =>
          cases equality
          obtain ⟨rest', shape, arguments⟩ := ihFunction name rest rfl rigid.shorten
          exact ⟨argument' :: rest', by simp only [spine, shape], .cons argumentStep arguments⟩
  | listNil =>
      intro name arguments equality rigid
      have names : Intrinsic.eliminateName = name := by
        simpa only [Intrinsic.eliminateApp, spineHead, spineHead_spine, Option.some.injEq] using
          congrArg spineHead equality
      have counts : 5 = arguments.length := by
        simpa only [Intrinsic.eliminateApp, spineDepth, spineDepth_spine] using congrArg spineDepth equality
      rcases rigid.1 with different | short
      · exact False.elim (different names.symm)
      · omega
  | listCons =>
      intro name arguments equality rigid
      have names : Intrinsic.eliminateName = name := by
        simpa only [Intrinsic.eliminateApp, spineHead, spineHead_spine, Option.some.injEq] using
          congrArg spineHead equality
      have counts : 5 = arguments.length := by
        simpa only [Intrinsic.eliminateApp, spineDepth, spineDepth_spine] using congrArg spineDepth equality
      rcases rigid.1 with different | short
      · exact False.elim (different names.symm)
      · omega
  | identity =>
      intro name arguments equality rigid
      have names : Intrinsic.identityEliminateName = name := by
        simpa only [Intrinsic.identityEliminateApp, spineHead, spineHead_spine, Option.some.injEq] using
          congrArg spineHead equality
      have counts : 6 = arguments.length := by
        simpa only [Intrinsic.identityEliminateApp, spineDepth, spineDepth_spine] using congrArg spineDepth equality
      rcases rigid.2.1 with different | short
      · exact False.elim (different names.symm)
      · omega
  | relNil =>
      intro name arguments equality rigid
      have names : IntrinsicRelator.eliminateName = name := by
        simpa only [IntrinsicRelator.eliminateApp, spineHead, spineHead_spine, Option.some.injEq] using
          congrArg spineHead equality
      have counts : 9 = arguments.length := by
        simpa only [IntrinsicRelator.eliminateApp, spineDepth, spineDepth_spine] using congrArg spineDepth equality
      rcases rigid.2.2 with different | short
      · exact False.elim (different names.symm)
      · omega
  | relCons =>
      intro name arguments equality rigid
      have names : IntrinsicRelator.eliminateName = name := by
        simpa only [IntrinsicRelator.eliminateApp, spineHead, spineHead_spine, Option.some.injEq] using
          congrArg spineHead equality
      have counts : 9 = arguments.length := by
        simpa only [IntrinsicRelator.eliminateApp, spineDepth, spineDepth_spine] using congrArg spineDepth equality
      rcases rigid.2.2 with different | short
      · exact False.elim (different names.symm)
      · omega
  | _ =>
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, spineHead_spine] at impossible
      cases impossible

theorem spine_inversion (name : DeclName) (arguments : List (Tower.Tm n))
    (rigid : Rigidity name arguments.length)
    {target : Tower.Tm n} (parallel : Par (spine name arguments) target) :
    ∃ arguments', target = spine name arguments' ∧ List.Forall₂ Par arguments arguments' :=
  spine_inversion_aux parallel name arguments rfl rigid

def listPrefix (a p z s : Tower.Tm n) : Tower.Tm n :=
  spine Intrinsic.eliminateName [s, z, p, a]

theorem par_listPrefix
    {a p z s a' p' z' s' : Tower.Tm n}
    (ha : Par a a')
    (hp : Par p p')
    (hz : Par z z')
    (hs : Par s s') :
    Par (listPrefix a p z s) (listPrefix a' p' z' s') :=
  .app (.app (.app (.app (.const _) ha) hp) hz) hs

theorem listPrefix_inversion
    {a p z s result : Tower.Tm n}
    (parallel : Par (listPrefix a p z s) result) :
    ∃ a' p' z' s', result = listPrefix a' p' z' s' ∧
      Par a a' ∧ Par p p' ∧ Par z z' ∧ Par s s' := by
  obtain ⟨arguments, shape, argumentSteps⟩ := spine_inversion Intrinsic.eliminateName
    [s, z, p, a] (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases argumentSteps with | cons hs rest =>
    cases rest with | cons hz rest =>
      cases rest with | cons hp rest =>
        cases rest with | cons ha rest =>
          cases rest
          exact ⟨_, _, _, _, shape, ha, hp, hz, hs⟩

theorem listPrefix_to_fixed
    {a p z s a' p' z' s' : Tower.Tm n}
    (parallel : Par (listPrefix a p z s) (listPrefix a' p' z' s')) :
    Par a a' ∧ Par p p' ∧ Par z z' ∧ Par s s' := by
  obtain ⟨a'', p'', z'', s'', shape, ha, hp, hz, hs⟩ := listPrefix_inversion parallel
  have fields := @spine_injective n Intrinsic.eliminateName
    [s', z', p', a'] [s'', z'', p'', a''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨ha, hp, hz, hs⟩

def identityPrefix (a x p d y : Tower.Tm n) : Tower.Tm n :=
  spine Intrinsic.identityEliminateName [y, d, p, x, a]

theorem par_identityPrefix
    {a x p d y a' x' p' d' y' : Tower.Tm n}
    (ha : Par a a')
    (hx : Par x x')
    (hp : Par p p')
    (hd : Par d d')
    (hy : Par y y') :
    Par (identityPrefix a x p d y) (identityPrefix a' x' p' d' y') :=
  .app (.app (.app (.app (.app (.const _) ha) hx) hp) hd) hy

theorem identityPrefix_inversion
    {a x p d y result : Tower.Tm n}
    (parallel : Par (identityPrefix a x p d y) result) :
    ∃ a' x' p' d' y', result = identityPrefix a' x' p' d' y' ∧
      Par a a' ∧ Par x x' ∧ Par p p' ∧ Par d d' ∧ Par y y' := by
  obtain ⟨arguments, shape, argumentSteps⟩ := spine_inversion Intrinsic.identityEliminateName
    [y, d, p, x, a] (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases argumentSteps with | cons hy rest =>
    cases rest with | cons hd rest =>
      cases rest with | cons hp rest =>
        cases rest with | cons hx rest =>
          cases rest with | cons ha rest =>
            cases rest
            exact ⟨_, _, _, _, _, shape, ha, hx, hp, hd, hy⟩

theorem identityPrefix_to_fixed
    {a x p d y a' x' p' d' y' : Tower.Tm n}
    (parallel : Par (identityPrefix a x p d y) (identityPrefix a' x' p' d' y')) :
    Par a a' ∧ Par x x' ∧ Par p p' ∧ Par d d' ∧ Par y y' := by
  obtain ⟨a'', x'', p'', d'', y'', shape, ha, hx, hp, hd, hy⟩ := identityPrefix_inversion parallel
  have fields := @spine_injective n Intrinsic.identityEliminateName
    [y', d', p', x', a'] [y'', d'', p'', x'', a''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨ha, hx, hp, hd, hy⟩

def relPrefix (a b r p z s xs ys : Tower.Tm n) : Tower.Tm n :=
  spine IntrinsicRelator.eliminateName [ys, xs, s, z, p, r, b, a]

theorem par_relPrefix
    {a b r p z s xs ys a' b' r' p' z' s' xs' ys' : Tower.Tm n}
    (ha : Par a a')
    (hb : Par b b')
    (hr : Par r r')
    (hp : Par p p')
    (hz : Par z z')
    (hs : Par s s')
    (hxs : Par xs xs')
    (hys : Par ys ys') :
    Par (relPrefix a b r p z s xs ys) (relPrefix a' b' r' p' z' s' xs' ys') :=
  .app (.app (.app (.app (.app (.app (.app (.app (.const _) ha) hb) hr) hp) hz) hs) hxs) hys

theorem relPrefix_inversion
    {a b r p z s xs ys result : Tower.Tm n}
    (parallel : Par (relPrefix a b r p z s xs ys) result) :
    ∃ a' b' r' p' z' s' xs' ys', result = relPrefix a' b' r' p' z' s' xs' ys' ∧
      Par a a' ∧ Par b b' ∧ Par r r' ∧ Par p p' ∧ Par z z' ∧ Par s s' ∧ Par xs xs' ∧ Par ys ys' := by
  obtain ⟨arguments, shape, argumentSteps⟩ := spine_inversion IntrinsicRelator.eliminateName
    [ys, xs, s, z, p, r, b, a] (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases argumentSteps with | cons hys rest =>
    cases rest with | cons hxs rest =>
      cases rest with | cons hs rest =>
        cases rest with | cons hz rest =>
          cases rest with | cons hp rest =>
            cases rest with | cons hr rest =>
              cases rest with | cons hb rest =>
                cases rest with | cons ha rest =>
                  cases rest
                  exact ⟨_, _, _, _, _, _, _, _, shape, ha, hb, hr, hp, hz, hs, hxs, hys⟩

theorem relPrefix_to_fixed
    {a b r p z s xs ys a' b' r' p' z' s' xs' ys' : Tower.Tm n}
    (parallel : Par (relPrefix a b r p z s xs ys) (relPrefix a' b' r' p' z' s' xs' ys')) :
    Par a a' ∧ Par b b' ∧ Par r r' ∧ Par p p' ∧ Par z z' ∧ Par s s' ∧ Par xs xs' ∧ Par ys ys' := by
  obtain ⟨a'', b'', r'', p'', z'', s'', xs'', ys'', shape, ha, hb, hr, hp, hz, hs, hxs, hys⟩ := relPrefix_inversion parallel
  have fields := @spine_injective n IntrinsicRelator.eliminateName
    [ys', xs', s', z', p', r', b', a'] [ys'', xs'', s'', z'', p'', r'', b'', a''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨ha, hb, hr, hp, hz, hs, hxs, hys⟩

theorem par_nilApp
    {a a' : Tower.Tm n}
    (ha : Par a a') :
    Par (Intrinsic.nilApp a) (Intrinsic.nilApp a') :=
  .app (.const _) ha

theorem nilApp_inversion
    {a result : Tower.Tm n}
    (parallel : Par (Intrinsic.nilApp a) result) :
    ∃ a', result = Intrinsic.nilApp a' ∧
      Par a a' := by
  obtain ⟨arguments, shape, argumentSteps⟩ := spine_inversion Intrinsic.nilName
    [a] (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases argumentSteps with | cons ha rest =>
    cases rest
    exact ⟨_, shape, ha⟩

theorem nilApp_to_fixed
    {a a' : Tower.Tm n}
    (parallel : Par (Intrinsic.nilApp a) (Intrinsic.nilApp a')) :
    Par a a' := by
  obtain ⟨a'', shape, ha⟩ := nilApp_inversion parallel
  have fields := @spine_injective n Intrinsic.nilName
    [a'] [a''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl⟩
  exact ha

theorem par_consApp
    {a h t a' h' t' : Tower.Tm n}
    (ha : Par a a')
    (hh : Par h h')
    (ht : Par t t') :
    Par (Intrinsic.consApp a h t) (Intrinsic.consApp a' h' t') :=
  .app (.app (.app (.const _) ha) hh) ht

theorem consApp_inversion
    {a h t result : Tower.Tm n}
    (parallel : Par (Intrinsic.consApp a h t) result) :
    ∃ a' h' t', result = Intrinsic.consApp a' h' t' ∧
      Par a a' ∧ Par h h' ∧ Par t t' := by
  obtain ⟨arguments, shape, argumentSteps⟩ := spine_inversion Intrinsic.consName
    [t, h, a] (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases argumentSteps with | cons ht rest =>
    cases rest with | cons hh rest =>
      cases rest with | cons ha rest =>
        cases rest
        exact ⟨_, _, _, shape, ha, hh, ht⟩

theorem consApp_to_fixed
    {a h t a' h' t' : Tower.Tm n}
    (parallel : Par (Intrinsic.consApp a h t) (Intrinsic.consApp a' h' t')) :
    Par a a' ∧ Par h h' ∧ Par t t' := by
  obtain ⟨a'', h'', t'', shape, ha, hh, ht⟩ := consApp_inversion parallel
  have fields := @spine_injective n Intrinsic.consName
    [t', h', a'] [t'', h'', a''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl⟩
  exact ⟨ha, hh, ht⟩

theorem par_nilRelApp
    {a b r a' b' r' : Tower.Tm n}
    (ha : Par a a')
    (hb : Par b b')
    (hr : Par r r') :
    Par (IntrinsicRelator.nilRelApp a b r) (IntrinsicRelator.nilRelApp a' b' r') :=
  .app (.app (.app (.const _) ha) hb) hr

theorem nilRelApp_inversion
    {a b r result : Tower.Tm n}
    (parallel : Par (IntrinsicRelator.nilRelApp a b r) result) :
    ∃ a' b' r', result = IntrinsicRelator.nilRelApp a' b' r' ∧
      Par a a' ∧ Par b b' ∧ Par r r' := by
  obtain ⟨arguments, shape, argumentSteps⟩ := spine_inversion IntrinsicRelator.nilRelName
    [r, b, a] (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases argumentSteps with | cons hr rest =>
    cases rest with | cons hb rest =>
      cases rest with | cons ha rest =>
        cases rest
        exact ⟨_, _, _, shape, ha, hb, hr⟩

theorem nilRelApp_to_fixed
    {a b r a' b' r' : Tower.Tm n}
    (parallel : Par (IntrinsicRelator.nilRelApp a b r) (IntrinsicRelator.nilRelApp a' b' r')) :
    Par a a' ∧ Par b b' ∧ Par r r' := by
  obtain ⟨a'', b'', r'', shape, ha, hb, hr⟩ := nilRelApp_inversion parallel
  have fields := @spine_injective n IntrinsicRelator.nilRelName
    [r', b', a'] [r'', b'', a''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl⟩
  exact ⟨ha, hb, hr⟩

theorem par_consRelApp
    {a b r h k t u he te a' b' r' h' k' t' u' he' te' : Tower.Tm n}
    (ha : Par a a')
    (hb : Par b b')
    (hr : Par r r')
    (hh : Par h h')
    (hk : Par k k')
    (ht : Par t t')
    (hu : Par u u')
    (hhe : Par he he')
    (hte : Par te te') :
    Par (IntrinsicRelator.consRelApp a b r h k t u he te) (IntrinsicRelator.consRelApp a' b' r' h' k' t' u' he' te') :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.const _) ha) hb) hr) hh) hk) ht) hu) hhe) hte

theorem consRelApp_inversion
    {a b r h k t u he te result : Tower.Tm n}
    (parallel : Par (IntrinsicRelator.consRelApp a b r h k t u he te) result) :
    ∃ a' b' r' h' k' t' u' he' te', result = IntrinsicRelator.consRelApp a' b' r' h' k' t' u' he' te' ∧
      Par a a' ∧ Par b b' ∧ Par r r' ∧ Par h h' ∧ Par k k' ∧ Par t t' ∧ Par u u' ∧ Par he he' ∧ Par te te' := by
  obtain ⟨arguments, shape, argumentSteps⟩ := spine_inversion IntrinsicRelator.consRelName
    [te, he, u, t, k, h, r, b, a] (by simp only [List.length_cons, List.length_nil, Rigidity]; decide) parallel
  cases argumentSteps with | cons hte rest =>
    cases rest with | cons hhe rest =>
      cases rest with | cons hu rest =>
        cases rest with | cons ht rest =>
          cases rest with | cons hk rest =>
            cases rest with | cons hh rest =>
              cases rest with | cons hr rest =>
                cases rest with | cons hb rest =>
                  cases rest with | cons ha rest =>
                    cases rest
                    exact ⟨_, _, _, _, _, _, _, _, _, shape, ha, hb, hr, hh, hk, ht, hu, hhe, hte⟩

theorem consRelApp_to_fixed
    {a b r h k t u he te a' b' r' h' k' t' u' he' te' : Tower.Tm n}
    (parallel : Par (IntrinsicRelator.consRelApp a b r h k t u he te) (IntrinsicRelator.consRelApp a' b' r' h' k' t' u' he' te')) :
    Par a a' ∧ Par b b' ∧ Par r r' ∧ Par h h' ∧ Par k k' ∧ Par t t' ∧ Par u u' ∧ Par he he' ∧ Par te te' := by
  obtain ⟨a'', b'', r'', h'', k'', t'', u'', he'', te'', shape, ha, hb, hr, hh, hk, ht, hu, hhe, hte⟩ := consRelApp_inversion parallel
  have fields := @spine_injective n IntrinsicRelator.consRelName
    [te', he', u', t', k', h', r', b', a'] [te'', he'', u'', t'', k'', h'', r'', b'', a''] shape
  simp only [List.cons.injEq, and_true] at fields
  rcases fields with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨ha, hb, hr, hh, hk, ht, hu, hhe, hte⟩

theorem lam_inversion {body : Tower.Tm (n + 1)} {target : Tower.Tm n}
    (parallel : Par (.lam body) target) :
    ∃ body', target = .lam body' ∧ Par body body' := by
  cases parallel with | lam inner => exact ⟨_, rfl, inner⟩

theorem pair_inversion {first second target : Tower.Tm n}
    (parallel : Par (.pair first second) target) :
    ∃ first' second', target = .pair first' second' ∧ Par first first' ∧ Par second second' := by
  cases parallel with | pair firstStep secondStep => exact ⟨_, _, rfl, firstStep, secondStep⟩

theorem refl_inversion {term target : Tower.Tm n}
    (parallel : Par (.refl term) target) :
    ∃ term', target = .refl term' ∧ Par term term' := by
  cases parallel with | refl inner => exact ⟨_, rfl, inner⟩

theorem refl_to_fixed {term term' : Tower.Tm n}
    (parallel : Par (.refl term) (.refl term')) : Par term term' := by
  cases parallel with | refl inner => exact inner

#print axioms spine_injective
#print axioms spine_inversion
#print axioms par_listPrefix
#print axioms listPrefix_inversion
#print axioms listPrefix_to_fixed
#print axioms par_identityPrefix
#print axioms identityPrefix_inversion
#print axioms identityPrefix_to_fixed
#print axioms par_relPrefix
#print axioms relPrefix_inversion
#print axioms relPrefix_to_fixed
#print axioms par_nilApp
#print axioms nilApp_inversion
#print axioms nilApp_to_fixed
#print axioms par_consApp
#print axioms consApp_inversion
#print axioms consApp_to_fixed
#print axioms par_nilRelApp
#print axioms nilRelApp_inversion
#print axioms nilRelApp_to_fixed
#print axioms par_consRelApp
#print axioms consRelApp_inversion
#print axioms consRelApp_to_fixed
#print axioms lam_inversion
#print axioms pair_inversion
#print axioms refl_inversion
#print axioms refl_to_fixed

end NativeRelatorConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
