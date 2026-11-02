import Mettapedia.Machines.PolyCursor

/-!
# Polynomial derivatives and compositional one-hole contexts

The derivative is defined by deleting a chosen position from a container, not
by recursion on a polynomial expression. Its interpretation is equivalent to
the existing `PolyCursor.Hole`. Product and composition laws therefore concern
independently constructed containers and contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PolynomialContexts

open PolyCursor

variable (P Q : PFunctor.{0, 0}) (X Y : Type)

/-- Choose one direction and retain precisely the other directions. -/
def derivative : PFunctor.{0, 0} where
  A := Sigma P.B
  B := fun p => {e : P.B p.1 // e ≠ p.2}

/-- The container derivative is the existing one-hole context. -/
def derivativeHoleEquiv : derivative P X ≃ Hole P.B X where
  toFun := fun ⟨⟨a, d⟩, f⟩ => ⟨a, d, fun e he => f ⟨e, he⟩⟩
  invFun := fun h => ⟨⟨h.a, h.d⟩, fun e => h.rest e.1 e.2⟩
  left_inv := by rintro ⟨⟨a, d⟩, f⟩; rfl
  right_inv := by rintro ⟨a, d, f⟩; rfl

/-- A product container: positions from either factor. -/
def product : PFunctor.{0, 0} where
  A := P.A × Q.A
  B := fun p => P.B p.1 ⊕ Q.B p.2

def productEquiv : product P Q X ≃ P X × Q X where
  toFun := fun ⟨⟨a, b⟩, f⟩ => (⟨a, fun d => f (.inl d)⟩, ⟨b, fun d => f (.inr d)⟩)
  invFun := fun ⟨⟨a, f⟩, ⟨b, g⟩⟩ => ⟨(a, b), Sum.elim f g⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, f⟩
    change (⟨(a, b), Sum.elim (fun d => f (.inl d)) (fun d => f (.inr d))⟩ :
      product P Q X) = ⟨(a, b), f⟩
    congr 1
    funext d
    cases d <;> rfl
  right_inv := by rintro ⟨⟨a, f⟩, ⟨b, g⟩⟩; rfl

def productSplit : Hole (product P Q).B X → (Hole P.B X × Q X) ⊕ (P X × Hole Q.B X)
  | ⟨(a, b), .inl d, rest⟩ =>
    .inl (⟨a, d, fun e he => rest (.inl e) (fun h => he (Sum.inl.inj h))⟩,
      ⟨b, fun e => rest (.inr e) (by intro h; cases h)⟩)
  | ⟨(a, b), .inr d, rest⟩ =>
    .inr (⟨a, fun e => rest (.inl e) (by intro h; cases h)⟩,
      ⟨b, d, fun e he => rest (.inr e) (fun h => he (Sum.inr.inj h))⟩)

def productJoin : (Hole P.B X × Q X) ⊕ (P X × Hole Q.B X) → Hole (product P Q).B X
  | .inl (h, ⟨b, f⟩) =>
    ⟨(h.a, b), .inl h.d, fun e he => match e with
      | .inl d => h.rest d (fun hd => he (congrArg Sum.inl hd))
      | .inr d => f d⟩
  | .inr (⟨a, f⟩, h) =>
    ⟨(a, h.a), .inr h.d, fun e he => match e with
      | .inl d => f d
      | .inr d => h.rest d (fun hd => he (congrArg Sum.inr hd))⟩

theorem productJoin_split (h : Hole (product P Q).B X) :
    productJoin P Q X (productSplit P Q X h) = h := by
  rcases h with ⟨⟨a, b⟩, d, rest⟩
  cases d <;> simp only [productSplit, productJoin]
  all_goals
    congr 1
    funext e he
    cases e <;> rfl

theorem productSplit_join (h : (Hole P.B X × Q X) ⊕ (P X × Hole Q.B X)) :
    productSplit P Q X (productJoin P Q X h) = h := by
  rcases h with ⟨⟨a, d, rest⟩, ⟨b, f⟩⟩ | ⟨⟨a, f⟩, ⟨b, d, rest⟩⟩ <;> rfl

/-- Leibniz's rule, as an equivalence with both constructive directions. -/
def productRule : Hole (product P Q).B X ≃ (Hole P.B X × Q X) ⊕ (P X × Hole Q.B X) where
  toFun := productSplit P Q X
  invFun := productJoin P Q X
  left_inv := productJoin_split P Q X
  right_inv := productSplit_join P Q X

/-- Fill a context to obtain a polynomial value, not a recursive tree. -/
noncomputable def plug (h : Hole P.B X) (x : X) : P X := by
  classical
  exact ⟨h.a, h.plug x⟩

theorem productRule_plug (h : Hole (product P Q).B X) (x : X) :
    productEquiv P Q X (plug (product P Q) X h x) =
      match productSplit P Q X h with
      | .inl (left, right) => (plug P X left x, right)
      | .inr (left, right) => (left, plug Q X right x) := by
  classical
  rcases h with ⟨⟨a, b⟩, d, rest⟩
  cases d <;> simp only [productSplit, productEquiv, plug, Hole.plug, Equiv.coe_fn_mk]
  all_goals
    congr 2 <;> funext e <;> simp [Hole.plug]
  all_goals grind

/-- Unfolded Mathlib object interface, for dependent context calculations. -/
abbrev Value (P : PFunctor.{0, 0}) (X : Type) := Σ a : P.A, P.B a → X

/-- Mathlib composition with its shape/direction interface exposed. -/
abbrev CompositeHole (P Q : PFunctor.{0, 0}) (X : Type) :=
  Hole (fun p : (Σ a : P.A, P.B a → Q.A) => Σ e : P.B p.1, Q.B (p.2 e)) X

/-- Splitting a composite context selects its outer and inner holes. -/
abbrev chainSplit (h : CompositeHole P Q X) : Hole P.B (Value Q X) × Hole Q.B X :=
  (⟨h.a.1, h.d.1, fun e he =>
      ⟨h.a.2 e, fun j => h.rest ⟨e, j⟩ (fun eq => he (congrArg Sigma.fst eq))⟩⟩,
   ⟨h.a.2 h.d.1, h.d.2, fun j hj => h.rest ⟨h.d.1, j⟩ (by
      intro eq
      have eq' : j = h.d.2 := sigma_mk_injective
        (β := fun e : P.B h.a.1 => Q.B (h.a.2 e))
        (eq.trans (Sigma.eta h.d).symm)
      exact hj eq')⟩)

/-- Reconstruct the family of inner shapes from the two component contexts. -/
noncomputable abbrev chainShapes (outer : Hole P.B (Value Q X)) (inner : Hole Q.B X) :
    P.B outer.a → Q.A := by
  classical
  exact fun e => if he : e = outer.d then inner.a else (outer.rest e he).1

@[simp] theorem chainShapes_selected (outer : Hole P.B (Value Q X)) (inner : Hole Q.B X) :
    chainShapes P Q X outer inner outer.d = inner.a := by
  simp [chainShapes]

@[simp] theorem chainShapes_other (outer : Hole P.B (Value Q X)) (inner : Hole Q.B X)
    (e : P.B outer.a) (he : e ≠ outer.d) :
    chainShapes P Q X outer inner e = (outer.rest e he).1 := by
  simp [chainShapes, he]

/-- Assemble a composite context. Dependent casts retain the chosen inner shape. -/
noncomputable def chainJoin (h : Hole P.B (Value Q X) × Hole Q.B X) : CompositeHole P Q X := by
  classical
  rcases h with ⟨outer, inner⟩
  let g := chainShapes P Q X outer inner
  have hd : g outer.d = inner.a := chainShapes_selected P Q X outer inner
  refine ⟨⟨outer.a, g⟩, ⟨outer.d, cast (congrArg Q.B hd.symm) inner.d⟩, ?_⟩
  rintro ⟨e, j⟩ hj
  by_cases he : e = outer.d
  · subst e
    refine inner.rest (cast (congrArg Q.B hd) j) ?_
    intro eq
    apply hj
    have hj' : j = cast (congrArg Q.B hd.symm) inner.d := eq_of_heq
      ((cast_heq (congrArg Q.B hd) j).symm.trans (heq_of_eq eq) |>.trans
        (cast_heq (congrArg Q.B hd.symm) inner.d).symm)
    exact congrArg (fun v : Q.B (g outer.d) =>
      (⟨outer.d, v⟩ : Σ e : P.B outer.a, Q.B (g e))) hj'
  · have hg : g e = (outer.rest e he).1 := chainShapes_other P Q X outer inner e he
    exact (outer.rest e he).2 (cast (congrArg Q.B hg) j)

theorem chainShapes_split (h : CompositeHole P Q X) :
    chainShapes P Q X (chainSplit P Q X h).1 (chainSplit P Q X h).2 = h.a.2 := by
  rcases h with ⟨⟨a, g⟩, ⟨d, j⟩, rest⟩
  funext e
  dsimp only [chainShapes, chainSplit]
  split_ifs with he
  · subst e; rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
theorem chainJoin_split (h : CompositeHole P Q X) :
    chainJoin P Q X (chainSplit P Q X h) = h := by
  classical
  rcases h with ⟨⟨a, g⟩, ⟨d, j⟩, rest⟩
  have hg := chainShapes_split P Q X (⟨⟨a, g⟩, ⟨d, j⟩, rest⟩ : CompositeHole P Q X)
  dsimp only [chainSplit] at hg
  simp only [chainJoin]
  generalize_proofs at *
  generalize hs : chainShapes P Q X
    (chainSplit P Q X (⟨⟨a, g⟩, ⟨d, j⟩, rest⟩ : CompositeHole P Q X)).1
    (chainSplit P Q X (⟨⟨a, g⟩, ⟨d, j⟩, rest⟩ : CompositeHole P Q X)).2 = g' at *
  cases hg
  simp only [cast_eq]
  congr 1
  funext e he
  rcases e with ⟨b, k⟩
  by_cases hb : b = d
  · subst b; simp
  · simp [hb]

private theorem value_cast (v : Value Q X) (a : Q.A) (ha : a = v.1)
    (h : ∀ _j : Q.B a, Q.B a = Q.B v.1) :
    (⟨a, fun j => v.2 (cast (h j) j)⟩ : Value Q X) = v := by
  rcases v with ⟨b, f⟩
  dsimp only at ha
  cases ha
  rfl

private theorem castRest_heq {A B X : Type} (e : B = A) (back : A = B)
    (d : A) (f : ∀ a : A, a ≠ d → X)
    (n : ∀ b : B, b ≠ cast back d → cast e b ≠ d) :
    HEq (fun b hb => f (cast e b) (n b hb)) f := by
  cases e
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem chainSplit_join (h : Hole P.B (Value Q X) × Hole Q.B X) :
    chainSplit P Q X (chainJoin P Q X h) = h := by
  classical
  rcases h with ⟨⟨a, d, rest⟩, ⟨b, j, rest'⟩⟩
  simp only [chainSplit, chainJoin, chainShapes]
  apply Prod.ext
  · dsimp only
    congr 1
    funext e he
    generalize_proofs at *
    simp only [dif_neg he]
    apply value_cast Q X (rest e he)
    exact dif_neg he
  · dsimp only
    generalize_proofs at *
    simp
    exact castRest_heq _ _ _ _ _

/-- The chain rule: a composite hole is an outer hole and one inner hole. -/
noncomputable def chainRule : Hole (P.comp Q).B X ≃ Hole P.B (Q X) × Hole Q.B X where
  toFun := chainSplit P Q X
  invFun := chainJoin P Q X
  left_inv := chainJoin_split P Q X
  right_inv := chainSplit_join P Q X

/-- The chain-rule decomposition commutes with filling the selected hole. -/
theorem chainRule_plug (h : CompositeHole P Q X) (x : X) :
    PFunctor.comp.get P Q (plug (P.comp Q) X h x) =
      plug P (Q X) (chainSplit P Q X h).1 (plug Q X (chainSplit P Q X h).2 x) := by
  classical
  change (⟨h.a.1, fun e => ⟨h.a.2 e, fun j =>
    @Hole.plug _ _ (fun _ => Classical.typeDecidableEq _) _ h x ⟨e, j⟩⟩⟩ : Value P (Value Q X)) =
    plug P (Value Q X) (chainSplit P Q X h).1 (plug Q X (chainSplit P Q X h).2 x)
  rcases h with ⟨⟨a, g⟩, ⟨d, j⟩, rest⟩
  dsimp only [plug, chainSplit, Hole.plug]
  congr 1
  funext e
  by_cases he : e = d
  · subst e
    simp only [Hole.plug]
    congr 1
    funext k
    by_cases hk : k = j
    · subst k; simp [Hole.plug]
    · have hp : (⟨d, k⟩ : Σ e : P.B a, Q.B (g e)) ≠ ⟨d, j⟩ :=
        fun h => hk (sigma_mk_injective (β := fun e => Q.B (g e)) h)
      simp [Hole.plug, hp, hk]
  · simp only [Hole.plug, dif_neg he]
    congr 1
    funext k
    have hp : (⟨e, k⟩ : Σ e : P.B a, Q.B (g e)) ≠ ⟨d, j⟩ :=
      fun h => he (congrArg Sigma.fst h)
    simp [hp]

/-- Recursive contexts compose by concatenating their inside-out hole stacks. -/
theorem plugAll_append {A : Type} {B : A → Type} [∀ a, DecidableEq (B a)]
    (inner outer : List (Hole B (WType B))) (t : WType B) :
    plugAll (inner ++ outer) t = plugAll outer (plugAll inner t) := by
  induction inner generalizing t with
  | nil => rfl
  | cons h hs ih => simpa only [List.cons_append, plugAll] using ih (WType.mk h.a (h.plug t))

#print axioms derivativeHoleEquiv
#print axioms productRule
#print axioms productRule_plug
#print axioms chainRule
#print axioms chainRule_plug
#print axioms plugAll_append

end Mettapedia.Machines.PolynomialContexts
