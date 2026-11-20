import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedStore
import Mettapedia.Algebra.SupportTensor

/-!
# Einsum on the graded store: a contraction rule sums over bindings, and compiles to the matrix kernels

A tensor is a graded store whose rows are index tuples of named tensors, annotated in a semiring. A **contraction**
(einsum) rule reads one row per operand and makes one row, each given by an index map from the bindings of the
index variables (`Contraction`); for instance the matrix product `(read (A $i $j) (B $j $k)) (make (C $i $k))`
binds index triples. Fired at the every-match grain on the graded store (`GradedStore.KeepRule.fire`):

* **Einsum** (`Contraction.fire_apply`, `Contraction.fireOn_apply`): each row keeps its annotation and gains the sum,
  over the matches whose output index tuple is that row, of the product of the operands' annotations in written
  order. The matches with a given output row are the bindings of the eliminated variables; non-matches add zero.

## Instances, through the tree's matrix kernels

* **Matrix product** (`gemm_productOf`, `matmul_productOf`): the rule accumulates `C + A * B` into the product rows,
  and `A * B` from a store without product rows: Mathlib's `Matrix.mul`.
  * the dense row-major contraction loop of `FiniteCoordinateBuffer` computes the same buffer (`matmul_dense`);
  * the occurrence-preserving sparse rows of `SupportTensor`, composed by `SparseLinearMap.compose`, have the same
    matrix (`matmul_sparse`).
* **Transpose** (`transpose_transposeOf`): `(read (A $i $j)) (make (T $j $i))` eliminates nothing.
* **Matrix–vector product** (`matvec_vectorOf`, `matvec_sparse`): `(read (A $i $j) (v $j)) (make (w $i))` reduces
  over `j`; it is `Matrix.mulVec`, and the sparse row traversal `SupportTensor.matvec` of support-aware operands.

## Licences

* **In place**: the product's made rows are not among its read rows, so its bindings may fire one at a time in
  place, in any order (`matmul_inPlace`); `GradedStore.Controls.inPlace_order_matters` is the control.
* **Contraction order** (`chained_contractions_reassociate`): contracting `A` with `B` and then with `C`, or `B` with
  `C` and then `A` with it, both give the three-way contraction `(read (A $i $j) (B $j $k) (C $k $l)) (make (Y $i
  $l))` (`chain_eq_mul_mul`, `chain_eq_mul_mul'`), by distributivity alone. A runtime may choose the order.
* **Change of annotation**: `GradedStore.KeepRule.mapK_fireOn` applies to every contraction.

## Controls

* **Factor order** (`operand_order_matters`): over two-by-two matrices as annotations, writing the operands in the
  other order changes the contraction.
* **A nonlinear per-row map blocks reassociation** (`square_blocks_reassociation`): squaring the intermediate
  product gives `4` when the sum over the eliminated index precedes the square and `2` when it follows; squaring
  does not distribute over the sum (`square_not_additive`). Doubling, which does, reassociates
  (`double_reassociates`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedEinsum

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra (Space)
open GradedStore (KeepRule)
open Mettapedia.Algebra (SparseLinearMap)
open Mettapedia.Algebra.FiniteCoordinateBuffer (Dense)
open Mettapedia.Algebra.SupportTensor (Value fill matrixFill toSparseRows sparseRows_toMatrix matvec
  matvec_eq_mulVec)
open scoped Matrix

universe uB uG uK

/-- **A contraction (einsum) rule**: one read per operand and one made row. Each is an index map: from a binding
of the index variables to the row (a tensor's name with an index tuple) that it reads or makes. -/
structure Contraction (B : Type uB) (G : Type uG) where
  /-- The operands' index maps, in written order. -/
  operands : List (B → G)
  /-- The output's index map. -/
  output : B → G

namespace Contraction

variable {B : Type uB} {G : Type uG} (c : Contraction B G)

/-- The keep-only rule of a contraction. -/
def toRule : KeepRule B G :=
  ⟨fun b => c.operands.map fun f => f b, fun b => [c.output b]⟩

variable {K : Type uK} [Semiring K] [DecidableEq G]

/-- **Einsum over a catalogue**: each row keeps its annotation and gains the sum, over the catalogued bindings
whose output index tuple is that row, of the operands' annotations multiplied in written order. -/
theorem fireOn_apply (cat : Finset B) (S : Space K G) (g : G) :
    c.toRule.fireOn cat S g =
      S g + ∑ b ∈ cat with c.output b = g, ((c.operands.map fun f => f b).map S).prod := by
  rw [KeepRule.fireOn_apply, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  simp only [toRule, KeepRule.value, List.count_singleton, beq_iff_eq]
  split_ifs <;> simp

/-- **Einsum at the every-match grain**: the sum runs over the matches whose output index tuple is the row, that
is, over the bindings of the eliminated variables at which every operand is present. -/
theorem fire_apply (S : Space K G) (finite : (c.toRule.matchSet S).Finite) (g : G) :
    c.toRule.fire S finite g =
      S g + ∑ b ∈ finite.toFinset with c.output b = g, ((c.operands.map fun f => f b).map S).prod :=
  c.fireOn_apply finite.toFinset S g

end Contraction

/-! ## Sums over the eliminated variables -/

/-- With the first index `i` and the last index `l` fixed, the bindings `(i, j, l)` are indexed by `j`. -/
theorem sum_filter_fiber {I J L G M : Type*} [Fintype I] [Fintype J] [Fintype L] [DecidableEq G]
    [AddCommMonoid M] (out : I × J × L → G) (g : G) (f : I × J × L → M) (i : I) (l : L)
    (fiber : ∀ b, out b = g ↔ b.1 = i ∧ b.2.2 = l) :
    ∑ b ∈ Finset.univ with out b = g, f b = ∑ j, f (i, j, l) := by
  symm
  apply Finset.sum_nbij' (fun j => (i, j, l)) (fun b => b.2.1)
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fiber _).mpr ⟨rfl, rfl⟩⟩
  · intro b _
    exact Finset.mem_univ _
  · intro j _
    rfl
  · rintro ⟨a, j, c⟩ member
    obtain ⟨rfl, rfl⟩ := (fiber _).mp (Finset.mem_filter.mp member).2
    rfl
  · intro j _
    rfl

/-- With the first index `i` fixed, the bindings `(i, j)` are indexed by `j`. -/
theorem sum_filter_fiber₂ {I J G M : Type*} [Fintype I] [Fintype J] [DecidableEq G] [AddCommMonoid M]
    (out : I × J → G) (g : G) (f : I × J → M) (i : I) (fiber : ∀ b, out b = g ↔ b.1 = i) :
    ∑ b ∈ Finset.univ with out b = g, f b = ∑ j, f (i, j) := by
  symm
  apply Finset.sum_nbij' (fun j => (i, j)) (fun b => b.2)
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fiber _).mpr rfl⟩
  · intro b _
    exact Finset.mem_univ _
  · intro j _
    rfl
  · rintro ⟨a, j⟩ member
    obtain rfl := (fiber _).mp (Finset.mem_filter.mp member).2
    rfl
  · intro j _
    rfl

/-- With the first index `i` and the last index `l` fixed, the bindings `(i, j, k, l)` are indexed by `(j, k)`. -/
theorem sum_filter_fiber₄ {I J L P G M : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype P]
    [DecidableEq G] [AddCommMonoid M] (out : I × J × L × P → G) (g : G) (f : I × J × L × P → M) (i : I)
    (l : P) (fiber : ∀ b, out b = g ↔ b.1 = i ∧ b.2.2.2 = l) :
    ∑ b ∈ Finset.univ with out b = g, f b = ∑ jk : J × L, f (i, jk.1, jk.2, l) := by
  symm
  apply Finset.sum_nbij' (fun jk => (i, jk.1, jk.2, l)) (fun b => (b.2.1, b.2.2.1))
  · intro jk _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fiber _).mpr ⟨rfl, rfl⟩⟩
  · intro b _
    exact Finset.mem_univ _
  · intro jk _
    rfl
  · rintro ⟨a, j, k, c⟩ member
    obtain ⟨rfl, rfl⟩ := (fiber _).mp (Finset.mem_filter.mp member).2
    rfl
  · intro jk _
    rfl

/-! ## The matrix product -/

section Product

variable {K : Type uK} [Semiring K] {m n p q : ℕ}

/-- Rows of a matrix product: the entries of `A` (`m × n`), of `B` (`n × p`) and of the product (`m × p`). -/
abbrev MulRow (m n p : ℕ) := (Fin m × Fin n) ⊕ (Fin n × Fin p) ⊕ (Fin m × Fin p)

/-- **The matrix product rule** `(read (A $i $j) (B $j $k)) (make (C $i $k))`; its bindings are index triples. -/
def matmul (m n p : ℕ) : Contraction (Fin m × Fin n × Fin p) (MulRow m n p) :=
  ⟨[fun b => Sum.inl (b.1, b.2.1), fun b => Sum.inr (Sum.inl (b.2.1, b.2.2))],
    fun b => Sum.inr (Sum.inr (b.1, b.2.2))⟩

/-- The store holding `A`, `B`, and `C₀` in the product rows. -/
noncomputable def gemmStore (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (C₀ : Matrix (Fin m) (Fin p) K) : Space K (MulRow m n p) :=
  Finsupp.equivFunOnFinite.symm
    (Sum.elim (fun x => A x.1 x.2) (Sum.elim (fun y => B y.1 y.2) fun z => C₀ z.1 z.2))

/-- The store holding `A` and `B`, with no product row present. -/
noncomputable def mulStore (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K) :
    Space K (MulRow m n p) :=
  gemmStore A B 0

/-- The product rows of a store, read as a matrix. -/
def productOf (S : Space K (MulRow m n p)) : Matrix (Fin m) (Fin p) K :=
  fun i k => S (Sum.inr (Sum.inr (i, k)))

/-- **The matrix product rule accumulates `A * B` into the product rows**: `C += A·B`. -/
theorem gemm_productOf (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (C₀ : Matrix (Fin m) (Fin p) K) :
    productOf ((matmul m n p).toRule.fire (gemmStore A B C₀) (Set.toFinite _)) = C₀ + A * B := by
  ext i k
  dsimp only [productOf]
  rw [KeepRule.fire_eq_fireOn_univ, Contraction.fireOn_apply, sum_filter_fiber (i := i) (l := k),
    Matrix.add_apply, Matrix.mul_apply]
  · simp [matmul, gemmStore]
  · intro b
    simp [matmul]

/-- **From a store without product rows, the matrix product rule makes `A * B`**: Mathlib's `Matrix.mul`. -/
theorem matmul_productOf (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K) :
    productOf ((matmul m n p).toRule.fire (mulStore A B) (Set.toFinite _)) = A * B := by
  rw [mulStore, gemm_productOf, zero_add]

/-- **The dense kernel computes the firing**: the row-major contraction loop of two flat buffers gives the buffer
of the product rows. -/
theorem matmul_dense (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K) :
    Dense.multiply? (Dense.encode A) (Dense.encode B) =
      some (Dense.encode (productOf ((matmul m n p).toRule.fire (mulStore A B) (Set.toFinite _)))) := by
  rw [matmul_productOf]
  exact Dense.multiply_encode A B

/-- **The sparse kernel computes the firing**: the occurrence-preserving sparse rows of two support-aware
operands, composed in data-flow order, have the product rows' matrix. -/
theorem matmul_sparse (A : Value (Fin m × Fin n) K) (B : Value (Fin n × Fin p) K) :
    productOf ((matmul m n p).toRule.fire (mulStore (matrixFill A) (matrixFill B)) (Set.toFinite _)) =
      ((toSparseRows B).compose (toSparseRows A)).toMatrix := by
  rw [matmul_productOf, SparseLinearMap.toMatrix_compose, sparseRows_toMatrix, sparseRows_toMatrix]

/-- **`C += A·B` may fire in place**: its made rows (the product rows) are disjoint from its read rows (those of
`A` and `B`), so firing its bindings one at a time in place, in any order listing each once, is the
every-grain firing. -/
theorem matmul_inPlace (S : Space K (MulRow m n p)) {l : List (Fin m × Fin n × Fin p)} (nodup : l.Nodup)
    (enumerates : l.toFinset = Finset.univ) :
    l.foldl (fun T b => (matmul m n p).toRule.fireInPlace b T) S =
      (matmul m n p).toRule.fire S (Set.toFinite _) := by
  rw [KeepRule.fire_eq_fireOn_univ]
  refine (matmul m n p).toRule.inPlace_every_order Finset.univ S
    (Sum.elim (fun _ => true) (Sum.elim (fun _ => true) fun _ => false))
    (Sum.elim (fun _ => false) (Sum.elim (fun _ => false) fun _ => true)) ?_ ?_ ?_ nodup enumerates
  · intro b _ g member
    simp [Contraction.toRule, matmul] at member
    rcases member with rfl | rfl <;> rfl
  · intro b _ g member
    simp [Contraction.toRule, matmul] at member
    subst member
    rfl
  · rintro (x | x | x) <;> simp

/-! ### The contraction order -/

/-- Rows of a chain of two products: the entries of `A` (`m × n`), `B` (`n × p`), `C` (`p × q`) and the result
(`m × q`). -/
abbrev ChainRow (m n p q : ℕ) := (Fin m × Fin n) ⊕ (Fin n × Fin p) ⊕ (Fin p × Fin q) ⊕ (Fin m × Fin q)

/-- **The three-way contraction** `(read (A $i $j) (B $j $k) (C $k $l)) (make (Y $i $l))`. -/
def chain (m n p q : ℕ) : Contraction (Fin m × Fin n × Fin p × Fin q) (ChainRow m n p q) :=
  ⟨[fun b => Sum.inl (b.1, b.2.1), fun b => Sum.inr (Sum.inl (b.2.1, b.2.2.1)),
      fun b => Sum.inr (Sum.inr (Sum.inl (b.2.2.1, b.2.2.2)))],
    fun b => Sum.inr (Sum.inr (Sum.inr (b.1, b.2.2.2)))⟩

/-- The store holding `A`, `B` and `C`, with no result row present. -/
noncomputable def chainStore (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (C : Matrix (Fin p) (Fin q) K) : Space K (ChainRow m n p q) :=
  Finsupp.equivFunOnFinite.symm
    (Sum.elim (fun x => A x.1 x.2) (Sum.elim (fun y => B y.1 y.2) (Sum.elim (fun z => C z.1 z.2) 0)))

/-- The result rows of a store, read as a matrix. -/
def chainOf (S : Space K (ChainRow m n p q)) : Matrix (Fin m) (Fin q) K :=
  fun i l => S (Sum.inr (Sum.inr (Sum.inr (i, l))))

/-- **The three-way contraction sums over both eliminated indices.** -/
theorem chain_apply (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (C : Matrix (Fin p) (Fin q) K) (i : Fin m) (l : Fin q) :
    chainOf ((chain m n p q).toRule.fire (chainStore A B C) (Set.toFinite _)) i l =
      ∑ j, ∑ k, A i j * (B j k * C k l) := by
  dsimp only [chainOf]
  rw [KeepRule.fire_eq_fireOn_univ, Contraction.fireOn_apply, sum_filter_fiber₄ (i := i) (l := l)]
  · simp [chain, chainStore, Fintype.sum_prod_type]
  · intro b
    simp [chain]

/-- The three-way contraction is `(A * B) * C`: distributivity moves the sum over `j` inside. -/
theorem chain_eq_mul_mul (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (C : Matrix (Fin p) (Fin q) K) :
    chainOf ((chain m n p q).toRule.fire (chainStore A B C) (Set.toFinite _)) = A * B * C := by
  ext i l
  rw [chain_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- The three-way contraction is `A * (B * C)`: distributivity moves the sum over `k` inside. -/
theorem chain_eq_mul_mul' (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (C : Matrix (Fin p) (Fin q) K) :
    chainOf ((chain m n p q).toRule.fire (chainStore A B C) (Set.toFinite _)) = A * (B * C) := by
  ext i l
  rw [chain_apply]
  simp only [Matrix.mul_apply, Finset.mul_sum]

/-- **Two chained contractions reassociate**: contracting `A` with `B` and the result with `C`, and contracting
`B` with `C` and `A` with the result, both give the three-way contraction. The order of contraction is free. -/
theorem chained_contractions_reassociate (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (C : Matrix (Fin p) (Fin q) K) :
    productOf ((matmul m p q).toRule.fire
        (mulStore (productOf ((matmul m n p).toRule.fire (mulStore A B) (Set.toFinite _))) C)
        (Set.toFinite _)) =
      chainOf ((chain m n p q).toRule.fire (chainStore A B C) (Set.toFinite _)) ∧
    productOf ((matmul m n q).toRule.fire
        (mulStore A (productOf ((matmul n p q).toRule.fire (mulStore B C) (Set.toFinite _))))
        (Set.toFinite _)) =
      chainOf ((chain m n p q).toRule.fire (chainStore A B C) (Set.toFinite _)) := by
  refine ⟨?_, ?_⟩
  · rw [matmul_productOf, matmul_productOf, chain_eq_mul_mul]
  · rw [matmul_productOf, matmul_productOf, chain_eq_mul_mul']

/-- **An additive per-row map reassociates**: doubling the intermediate product commutes with the order of
contraction. -/
theorem double_reassociates (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (C : Matrix (Fin p) (Fin q) K) :
    productOf ((matmul m p q).toRule.fire
        (mulStore ((2 : ℕ) • productOf ((matmul m n p).toRule.fire (mulStore A B) (Set.toFinite _))) C)
        (Set.toFinite _)) =
      productOf ((matmul m n q).toRule.fire
        (mulStore A ((2 : ℕ) • productOf ((matmul n p q).toRule.fire (mulStore B C) (Set.toFinite _))))
        (Set.toFinite _)) := by
  rw [matmul_productOf, matmul_productOf, matmul_productOf, matmul_productOf, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc]

end Product

/-! ## Transpose and the matrix–vector product -/

section Instances

variable {K : Type uK} [Semiring K] {m n : ℕ}

/-- Rows of a transpose: the entries of `A` (`m × n`) and of its transpose (`n × m`). -/
abbrev TransposeRow (m n : ℕ) := (Fin m × Fin n) ⊕ (Fin n × Fin m)

/-- **The transpose rule** `(read (A $i $j)) (make (T $j $i))`: it eliminates no variable. -/
def transpose (m n : ℕ) : Contraction (Fin m × Fin n) (TransposeRow m n) :=
  ⟨[fun b => Sum.inl b], fun b => Sum.inr b.swap⟩

/-- The store holding `A`, with no transposed row present. -/
noncomputable def transposeStore (A : Matrix (Fin m) (Fin n) K) : Space K (TransposeRow m n) :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun x => A x.1 x.2) 0)

/-- The transposed rows of a store, read as a matrix. -/
def transposeOf (S : Space K (TransposeRow m n)) : Matrix (Fin n) (Fin m) K :=
  fun j i => S (Sum.inr (j, i))

/-- **The transpose rule makes `Aᵀ`.** -/
theorem transpose_transposeOf (A : Matrix (Fin m) (Fin n) K) :
    transposeOf ((transpose m n).toRule.fire (transposeStore A) (Set.toFinite _)) = Aᵀ := by
  ext j i
  dsimp only [transposeOf]
  rw [KeepRule.fire_eq_fireOn_univ, Contraction.fireOn_apply, Finset.sum_filter,
    Fintype.sum_eq_single (i, j)]
  · simp [transpose, transposeStore]
  · intro b different
    rw [if_neg]
    intro same
    apply different
    simp only [transpose, Sum.inr.injEq] at same
    have swapped := congrArg Prod.swap same
    rw [Prod.swap_swap] at swapped
    exact swapped

/-- Rows of a matrix–vector product: the entries of `A` (`m × n`), of `v` (`n`) and of the result (`m`). -/
abbrev MatVecRow (m n : ℕ) := (Fin m × Fin n) ⊕ Fin n ⊕ Fin m

/-- **The matrix–vector rule** `(read (A $i $j) (v $j)) (make (w $i))`: it sums over the eliminated `j`. -/
def matvecRule (m n : ℕ) : Contraction (Fin m × Fin n) (MatVecRow m n) :=
  ⟨[fun b => Sum.inl b, fun b => Sum.inr (Sum.inl b.2)], fun b => Sum.inr (Sum.inr b.1)⟩

/-- The store holding `A` and `v`, with no result row present. -/
noncomputable def matvecStore (A : Matrix (Fin m) (Fin n) K) (v : Fin n → K) : Space K (MatVecRow m n) :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun x => A x.1 x.2) (Sum.elim v 0))

/-- The result rows of a store, read as a vector. -/
def vectorOf (S : Space K (MatVecRow m n)) : Fin m → K :=
  fun i => S (Sum.inr (Sum.inr i))

/-- **The matrix–vector rule makes `A *ᵥ v`.** -/
theorem matvec_vectorOf (A : Matrix (Fin m) (Fin n) K) (v : Fin n → K) :
    vectorOf ((matvecRule m n).toRule.fire (matvecStore A v) (Set.toFinite _)) = A *ᵥ v := by
  funext i
  dsimp only [vectorOf]
  rw [KeepRule.fire_eq_fireOn_univ, Contraction.fireOn_apply, sum_filter_fiber₂ (i := i)]
  · simp [matvecRule, matvecStore, Matrix.mulVec, dotProduct]
  · intro b
    simp [matvecRule]

/-- **The sparse row traversal computes the firing**: on support-aware operands, read with zero for none queries. -/
theorem matvec_sparse (A : Value (Fin m × Fin n) K) (v : Value (Fin n) K) :
    vectorOf ((matvecRule m n).toRule.fire (matvecStore (matrixFill A) (fill 0 v)) (Set.toFinite _)) =
      matvec A v := by
  rw [matvec_vectorOf, matvec_eq_mulVec]

end Instances

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra.Controls (upper lower upper_mul_lower_ne)

/-- The matrix product rule with its operands written in the other order:
`(read (B $j $k) (A $i $j)) (make (C $i $k))`. -/
def matmulSwapped (m n p : ℕ) : Contraction (Fin m × Fin n × Fin p) (MulRow m n p) :=
  ⟨[fun b => Sum.inr (Sum.inl (b.2.1, b.2.2)), fun b => Sum.inl (b.1, b.2.1)],
    fun b => Sum.inr (Sum.inr (b.1, b.2.2))⟩

theorem matmulSwapped_productOf {K : Type uK} [Semiring K] {m n p : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin p) K) :
    productOf ((matmulSwapped m n p).toRule.fire (mulStore A B) (Set.toFinite _)) =
      fun i k => ∑ j, B j k * A i j := by
  ext i k
  dsimp only [productOf]
  rw [KeepRule.fire_eq_fireOn_univ, Contraction.fireOn_apply, sum_filter_fiber (i := i) (l := k)]
  · simp [matmulSwapped, mulStore, gemmStore]
  · intro b
    simp [matmulSwapped]

/-- **The factor order is the written order**: over two-by-two matrices as annotations, writing the operands in
the other order changes the contraction. -/
theorem operand_order_matters :
    productOf ((matmul 1 1 1).toRule.fire (mulStore !![upper] !![lower]) (Set.toFinite _)) ≠
      productOf ((matmulSwapped 1 1 1).toRule.fire (mulStore !![upper] !![lower]) (Set.toFinite _)) := by
  intro same
  rw [matmul_productOf, matmulSwapped_productOf] at same
  have atCorner := congrFun (congrFun same 0) 0
  simp [Matrix.mul_apply] at atCorner
  exact upper_mul_lower_ne atCorner

/-- Square every entry: a per-row map that does not distribute over sums. -/
def squareEntries {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℕ) : Matrix (Fin a) (Fin b) ℕ :=
  fun i j => X i j ^ 2

/-- Squaring does not distribute over a sum. -/
theorem square_not_additive : ((1 : ℕ) + 1) ^ 2 ≠ 1 ^ 2 + 1 ^ 2 := by
  decide

/-- A row of two ones. -/
def onesRow : Matrix (Fin 1) (Fin 2) ℕ := fun _ _ => 1

/-- A column of two ones. -/
def onesColumn : Matrix (Fin 2) (Fin 1) ℕ := fun _ _ => 1

/-- The one-by-one matrix one. -/
def oneByOne : Matrix (Fin 1) (Fin 1) ℕ := fun _ _ => 1

/-- **A nonlinear per-row map blocks reassociation**: squaring the intermediate product gives `4` when the sum
over the eliminated index comes before the square, and `2` when it comes after. -/
theorem square_blocks_reassociation :
    productOf ((matmul 1 1 1).toRule.fire
        (mulStore (squareEntries (productOf ((matmul 1 2 1).toRule.fire (mulStore onesRow onesColumn)
          (Set.toFinite _)))) oneByOne) (Set.toFinite _)) 0 0 = 4 ∧
      productOf ((matmul 1 2 1).toRule.fire
        (mulStore onesRow (squareEntries (productOf ((matmul 2 1 1).toRule.fire
          (mulStore onesColumn oneByOne) (Set.toFinite _))))) (Set.toFinite _)) 0 0 = 2 := by
  rw [matmul_productOf, matmul_productOf, matmul_productOf, matmul_productOf]
  decide +kernel

end Controls

#print axioms Contraction.fireOn_apply
#print axioms Contraction.fire_apply
#print axioms gemm_productOf
#print axioms matmul_productOf
#print axioms matmul_dense
#print axioms matmul_sparse
#print axioms matmul_inPlace
#print axioms chain_apply
#print axioms chain_eq_mul_mul
#print axioms chain_eq_mul_mul'
#print axioms chained_contractions_reassociate
#print axioms double_reassociates
#print axioms transpose_transposeOf
#print axioms matvec_vectorOf
#print axioms matvec_sparse
#print axioms Controls.operand_order_matters
#print axioms Controls.square_not_additive
#print axioms Controls.square_blocks_reassociation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedEinsum
