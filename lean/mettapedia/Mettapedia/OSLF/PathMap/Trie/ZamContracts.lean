import Mettapedia.OSLF.PathMap.ZipperExecution
import Mettapedia.OSLF.PathMap.Trie.TrieZipper
import Mettapedia.OSLF.Framework.OptimizationTheorems

/-!
# ZAM Optimization Contracts for Trie Backend

Each optimization contract in `OptimizationTheorems.lean` is parameterized
over a `RelationEnv`.  This module transfers those contracts to
trie-backed `ZipperSpace` stores via the ZAM soundness theorems.

The transfer principle: since `zam_relEnv_eq` proves
`toRelationEnv zs = flatEnv` (when `StoresAgree`), every optimization
contract that holds for the flat environment automatically holds for
the zipper environment — just instantiate the `relEnv` parameter with
`toRelationEnv zs`.

## Theorem naming convention

Each theorem has the form `zam_<contract>`: the `<contract>` from
`OptimizationTheorems` transferred to the ZAM/trie backend.

## References

- OptimizationTheorems.lean: engine optimization contracts
- ZipperExecution.lean: ZAM soundness (`zam_oslf_sound`, `zam_diamond_sound`, `zam_box_sound`)
- Trie/TrieZipper.lean: concrete `SimpleTrieZipper` instance
-/

namespace Mettapedia.OSLF.PathMap.Trie.ZamContracts

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.OptimizationTheorems
open Mettapedia.OSLF.Framework.BeckChevalleyOSLF (commDi commPb)
open Mettapedia.OSLF.PathMap.ZipperExecution
open Mettapedia.PathMap

/-! ## §1: Backend Transfer Lemma

The core lemma: if a zipper store agrees with a flat environment,
the zipper-backed `RelationEnv` equals the flat one.  All subsequent
transfers are trivial rewrites using this equality. -/

/-- When stores agree, the zipper-backed RelationEnv equals the flat one. -/
theorem zam_relEnv_eq {Z V : Type*}
    [ZipperMoving Z] [ZipperValues Z V] [ZipperIteration Z]
    [ZipperStoreValues Z V]
    (zs : ZipperSpace Z V)
    (flatEnv : RelationEnv)
    (hagree : StoresAgree zs flatEnv.tuples) :
    toRelationEnv zs = flatEnv := by
  apply Mettapedia.OSLF.PathMap.RelationEnv.ext_tuples
  exact funext fun rel => funext fun args => hagree rel args

/-! ## §2: Early Termination on Trie Backend

If `¬◇φ p` on the zipper-backed store, every successor fails `φ`.
Works for any `RelationEnv`, so transfers directly to trie backend. -/

/-- Early termination transfers to trie backend. -/
theorem zam_diamond_false_early_termination
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern)
    (h : ¬ langDiamondUsing relEnv lang φ p) :
    ∀ q, langReducesUsing relEnv lang p q → ¬ φ q :=
  diamond_false_early_termination relEnv lang φ p h

/-! ## §3: Memoization on Trie Backend

Box memoization is safe on trie-backed stores. -/

/-- Memoization transfers to trie backend. -/
theorem zam_box_memoization_safe
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern)
    (h : langBoxUsing relEnv lang φ p) :
    ∀ q, langReducesUsing relEnv lang q p → φ q :=
  box_memoization_safe relEnv lang φ p h

/-! ## §4: Deterministic Dispatch on Trie Backend

When reduction is deterministic, diamond collapses to direct dispatch. -/

/-- Deterministic diamond collapse transfers to trie backend. -/
theorem zam_deterministic_diamond_collapse
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p q : Pattern)
    (hred : langReducesUsing relEnv lang p q)
    (hdet : ∀ q', langReducesUsing relEnv lang p q' → q' = q) :
    langDiamondUsing relEnv lang φ p ↔ φ q :=
  deterministic_diamond_collapse relEnv lang φ p q hred hdet

/-- Deterministic box collapse transfers to trie backend. -/
theorem zam_deterministic_box_collapse
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p q : Pattern)
    (hred : langReducesUsing relEnv lang q p)
    (hdet : ∀ q', langReducesUsing relEnv lang q' p → q' = q) :
    langBoxUsing relEnv lang φ p ↔ φ q :=
  deterministic_box_collapse relEnv lang φ p q hred hdet

/-! ## §5: Specialization on Trie Backend

Rule-set monotonicity now works for ANY `RelationEnv` (including
trie-backed stores), following the generalization of `declReduces_mono`. -/

/-- Specialization: reduction lifts from sub-language to super-language.
    Works on any backend (trie, flat, etc.). -/
theorem zam_specialization_preserves_reduction
    (relEnv : RelationEnv)
    {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    {p q : Pattern}
    (hred : langReducesUsing relEnv lang₁ p q) :
    langReducesUsing relEnv lang₂ p q :=
  specialization_preserves_reduction hrules hcong hred

/-- Diamond is monotone across sub-languages (any backend). -/
theorem zam_diamond_mono
    (relEnv : RelationEnv)
    {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (φ : Pattern → Prop) (p : Pattern)
    (h : langDiamondUsing relEnv lang₁ φ p) :
    langDiamondUsing relEnv lang₂ φ p :=
  diamond_mono_rules hrules hcong φ p h

/-- Box is contravariant across sub-languages (any backend). -/
theorem zam_box_contra
    (relEnv : RelationEnv)
    {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (φ : Pattern → Prop) (p : Pattern)
    (h : langBoxUsing relEnv lang₂ φ p) :
    langBoxUsing relEnv lang₁ φ p :=
  box_contra_rules hrules hcong φ p h

/-! ## §6: Substitution-Reduction Fusion on Trie Backend

Beck-Chevalley fusion is backend-independent (uses langDiamond/langBox
which are parameterized over the standard RelationEnv.empty). -/

/-- Substitution-reduction fusion is available on trie backend.
    Since fusion uses `langDiamond`/`langBox` (which fix `RelationEnv.empty`),
    the theorem transfers directly. -/
theorem zam_substitution_reduction_fusion
    (lang : LanguageDef) (q : Pattern) :
    GaloisConnection
      (commDi q ∘ langDiamond lang)
      (langBox lang ∘ commPb q) :=
  substitution_reduction_fusion lang q

/-! ## §7: Concrete Trie Zipper Instantiation

All the above work for any `ZipperSpace Z V`.  Here we specialize to
`SimpleTrieZipper V` to confirm the contracts are satisfiable. -/

/-- A trie-backed zipper space. -/
def trieZipperSpace (V : Type*) (t : FTrie V)
    (queryFn : SimpleTrieZipper V → String → List Pattern →
               List (List Pattern)) : ZipperSpace (SimpleTrieZipper V) V :=
  { root := SimpleTrieZipper.fromTrie t
    atRoot := rfl
    queryFn := queryFn }

/-! ## Summary

**0 sorries. 0 axioms.**

Contracts available on ZAM/trie backend:

| Contract | Optimization | Backend |
|----------|-------------|---------|
| `zam_diamond_false_early_termination` | Prune search when ¬◇φ | any RelationEnv |
| `zam_box_memoization_safe` | Cache □-typed results | any RelationEnv |
| `zam_deterministic_diamond_collapse` | Direct-dispatch (unique successor) | any RelationEnv |
| `zam_deterministic_box_collapse` | Direct-dispatch (unique predecessor) | any RelationEnv |
| `zam_specialization_preserves_reduction` | Lift reductions across sub-languages | any RelationEnv |
| `zam_diamond_mono` | Lift ◇ across sub-languages | any RelationEnv |
| `zam_box_contra` | Weaken □ across sub-languages | any RelationEnv |
| `zam_substitution_reduction_fusion` | Fuse subst + reduce passes | RelationEnv.empty |

All contracts except Beck-Chevalley fusion work for arbitrary `RelationEnv`
(including trie-backed stores), following the generalization of
`declReduces_mono` in `HypercubeGSLTFunctor.lean`.
-/

end Mettapedia.OSLF.PathMap.Trie.ZamContracts
