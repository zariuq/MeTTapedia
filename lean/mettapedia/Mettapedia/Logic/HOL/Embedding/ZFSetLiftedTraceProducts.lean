import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift
import Mettapedia.SetTheory.ZFSet.OrderedPair

/-!
# The model operations commute with the universe lift

Truth values, pair projections, graphs, traces, dependent sums and dependent
products of the lower universe are the same operations applied after `lift`.
A package modelled in one universe is then read in the next by lifting its
values. The tower does not have to be rebuilt upstairs.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetLiftedTraceProducts

open ZFSetHenkinInterpretation
open ZFSetUniverseLift
open ZFSetDependentProducts
open ZFSetTraceProducts
open ZFSetTraceProofDecoding
open Mettapedia.SetTheory.ZFSetOrderedPair

universe u

noncomputable section

/-! ## Bounds used by the pair operations -/

theorem lift_union (a b : ZFSet.{u}) : lift (a ∪ b) = lift a ∪ lift b := by
  rw [← ZFSet.sUnion_pair, ← ZFSet.sUnion_pair, lift_sUnion, lift_unorderedPair]

theorem left_mem_sUnion_pair (a b : ZFSet.{u}) : a ∈ ZFSet.sUnion (ZFSet.pair a b) := by
  refine ZFSet.mem_sUnion.mpr ⟨{a}, ?_, ZFSet.mem_singleton.mpr rfl⟩
  rw [ZFSet.pair]
  exact ZFSet.mem_pair.mpr (Or.inl rfl)

theorem right_mem_sUnion_pair (a b : ZFSet.{u}) : b ∈ ZFSet.sUnion (ZFSet.pair a b) := by
  refine ZFSet.mem_sUnion.mpr ⟨{a, b}, ?_, ZFSet.mem_pair.mpr (Or.inr rfl)⟩
  rw [ZFSet.pair]
  exact ZFSet.mem_pair.mpr (Or.inr rfl)

/-- Equivalent predicates separate the same pairs. -/
theorem truthCode_iff {P Q : Prop} (h : P ↔ Q) : truthCode.{u} P = truthCode.{u} Q := by
  apply ZFSet.ext
  intro z
  rw [mem_truthCode, mem_truthCode]
  exact and_congr_right (fun _ => h)

theorem lift_pairSep (x y : ZFSet.{u}) (p : ZFSet.{u} → ZFSet.{u} → Prop)
    (P : ZFSet.{u + 1} → ZFSet.{u + 1} → Prop)
    (agree : ∀ a ∈ x, ∀ b ∈ y, p a b ↔ P (lift a) (lift b)) :
    lift (ZFSet.pairSep p x y) = ZFSet.pairSep P (lift x) (lift y) := by
  unfold ZFSet.pairSep
  have bound :
      lift (ZFSet.powerset (ZFSet.powerset (x ∪ y))) =
        ZFSet.powerset (ZFSet.powerset (lift x ∪ lift y)) := by
    rw [lift_powerset, lift_powerset, lift_union]
  rw [lift_separation (ZFSet.powerset (ZFSet.powerset (x ∪ y)))
      (fun z => ∃ a ∈ x, ∃ b ∈ y, z = ZFSet.pair a b ∧ p a b)
      (fun z => ∃ a ∈ lift x, ∃ b ∈ lift y, z = ZFSet.pair a b ∧ P a b)
      (by
        intro z _
        constructor
        · rintro ⟨a, ha, b, hb, rfl, hp⟩
          exact ⟨lift a, lift_mem_lift.mpr ha, lift b, lift_mem_lift.mpr hb, lift_pair a b,
            (agree a ha b hb).mp hp⟩
        · rintro ⟨A, hA, B, hB, hZ, hP⟩
          obtain ⟨a, ha, rfl⟩ := mem_lift.mp hA
          obtain ⟨b, hb, rfl⟩ := mem_lift.mp hB
          refine ⟨a, ha, b, hb, lift_injective (hZ.trans (lift_pair a b).symm),
            (agree a ha b hb).mpr hP⟩),
    bound]

/-! ## Truth values and projections -/

theorem lift_truthCode (P : Prop) : lift (truthCode.{u} P) = truthCode.{u + 1} P := by
  rw [truthCode, truthCode,
    lift_separation ({∅} : ZFSet.{u}) (fun _ => P) (fun _ => P) (fun _ _ => Iff.rfl),
    lift_singleton, lift_empty]

theorem lift_first (p : ZFSet.{u}) : lift (first p) = first (lift p) := by
  rw [first, first, lift_sUnion,
    lift_separation (ZFSet.sUnion p) (fun x => ∃ y, p = ZFSet.pair x y)
      (fun x => ∃ y, lift p = ZFSet.pair x y)
      (by
        intro x _
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨lift y, lift_pair x y⟩
        · rintro ⟨Y, h⟩
          have hY : Y ∈ lift (ZFSet.sUnion p) := by
            rw [lift_sUnion, h]
            exact right_mem_sUnion_pair (lift x) Y
          obtain ⟨y, _, hy⟩ := mem_lift.mp hY
          refine ⟨y, lift_injective ?_⟩
          rw [h, ← hy, lift_pair]),
    lift_sUnion]

theorem lift_second (p : ZFSet.{u}) : lift (second p) = second (lift p) := by
  rw [second, second, lift_sUnion,
    lift_separation (ZFSet.sUnion p) (fun y => ∃ x, p = ZFSet.pair x y)
      (fun y => ∃ x, lift p = ZFSet.pair x y)
      (by
        intro y _
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨lift x, lift_pair x y⟩
        · rintro ⟨X, h⟩
          have hX : X ∈ lift (ZFSet.sUnion p) := by
            rw [lift_sUnion, h]
            exact left_mem_sUnion_pair X (lift y)
          obtain ⟨x, _, hx⟩ := mem_lift.mp hX
          refine ⟨x, lift_injective ?_⟩
          rw [h, ← hx, lift_pair]),
    lift_sUnion]

/-! ## Graphs, traces, sums and products -/

theorem lift_graph (a : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u})
    (F : ZFSet.{u + 1} → ZFSet.{u + 1}) (agree : ∀ x ∈ a, F (lift x) = lift (f x)) :
    lift (graph a f) = graph (lift a) F := by
  unfold graph
  rw [lift_replacement a (fun x => ZFSet.pair x (f x)) (fun y => ZFSet.pair y (F y))
    (fun x hx => by rw [agree x hx, lift_pair])]

theorem lift_coordinates (r : ZFSet.{u}) : lift (coordinates r) = coordinates (lift r) := by
  rw [coordinates, coordinates, lift_sUnion, lift_sUnion]

theorem lift_traceApp (r x : ZFSet.{u}) :
    lift (traceApp r x) = traceApp (lift r) (lift x) := by
  rw [traceApp, traceApp,
    lift_separation (coordinates r) (fun z => ZFSet.pair x z ∈ r)
      (fun z => ZFSet.pair (lift x) z ∈ lift r)
      (by
        intro z _
        constructor
        · intro hz
          rw [← lift_pair]
          exact lift_mem_lift.mpr hz
        · intro hz
          apply lift_mem_lift.mp
          rw [lift_pair]
          exact hz),
    lift_coordinates]

theorem lift_traceLam (r : ZFSet.{u}) : lift (traceLam r) = traceLam (lift r) := by
  unfold traceLam
  rw [lift_pairSep (coordinates r) (ZFSet.sUnion (coordinates r))
      (fun x z => ∃ y, ZFSet.pair x y ∈ r ∧ z ∈ y)
      (fun x z => ∃ y, ZFSet.pair x y ∈ lift r ∧ z ∈ y)
      (by
        intro x _ z _
        constructor
        · rintro ⟨y, hxy, hzy⟩
          refine ⟨lift y, ?_, lift_mem_lift.mpr hzy⟩
          rw [← lift_pair]
          exact lift_mem_lift.mpr hxy
        · rintro ⟨Y, hXY, hZY⟩
          obtain ⟨p, hp, hpEq⟩ := mem_lift.mp hXY
          have hInner : ({lift x, Y} : ZFSet.{u + 1}) ∈ lift p := by
            rw [hpEq, ZFSet.pair]
            exact ZFSet.mem_pair.mpr (Or.inr rfl)
          obtain ⟨s, _, hsEq⟩ := mem_lift.mp hInner
          have hY : Y ∈ lift s := by
            rw [hsEq]
            exact ZFSet.mem_pair.mpr (Or.inr rfl)
          obtain ⟨y, _, hy⟩ := mem_lift.mp hY
          have hxy : ZFSet.pair x y ∈ r := by
            apply lift_mem_lift.mp
            rw [lift_pair, hy, ← hpEq]
            exact lift_mem_lift.mpr hp
          refine ⟨y, hxy, ?_⟩
          apply lift_mem_lift.mp
          rw [hy]
          exact hZY),
    lift_coordinates, lift_sUnion, lift_coordinates]

theorem lift_familyUnion (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u})
    (B : ZFSet.{u + 1} → ZFSet.{u + 1}) (agree : ∀ x ∈ a, B (lift x) = lift (b x)) :
    lift (familyUnion a b) = familyUnion (lift a) B := by
  rw [familyUnion, familyUnion, lift_sUnion, lift_replacement a b B agree]

theorem lift_sigmaSet (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u})
    (B : ZFSet.{u + 1} → ZFSet.{u + 1}) (agree : ∀ x ∈ a, B (lift x) = lift (b x)) :
    lift (sigmaSet a b) = sigmaSet (lift a) B := by
  unfold sigmaSet
  rw [lift_pairSep a (familyUnion a b) (fun x y => y ∈ b x) (fun X Y => Y ∈ B X)
      (by
        intro x hx y _
        rw [agree x hx]
        exact lift_mem_lift.symm),
    lift_familyUnion a b B agree]

theorem lift_prod (x y : ZFSet.{u}) : lift (ZFSet.prod x y) = ZFSet.prod (lift x) (lift y) := by
  rw [ZFSet.prod, ZFSet.prod]
  exact lift_pairSep x y (fun _ _ => True) (fun _ _ => True) (fun _ _ _ _ => Iff.rfl)

theorem lift_isFunc {x y f : ZFSet.{u}} (hf : ZFSet.IsFunc x y f) :
    ZFSet.IsFunc (lift x) (lift y) (lift f) := by
  refine ⟨?_, ?_⟩
  · rw [← lift_prod]
    exact lift_subset_lift.mpr hf.1
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := mem_lift.mp hz
    obtain ⟨w, hw, huniq⟩ := hf.2 a ha
    have hmem : ZFSet.pair (lift a) (lift w) ∈ lift f := by
      rw [← lift_pair]
      exact lift_mem_lift.mpr hw
    refine ⟨lift w, hmem, ?_⟩
    · intro W hW
      obtain ⟨p, hp, hpEq⟩ := mem_lift.mp hW
      obtain ⟨a', _, b, _, hpPair⟩ := ZFSet.mem_prod.mp (hf.1 hp)
      have hpLift : lift (ZFSet.pair a' b) = ZFSet.pair (lift a) W := by
        rw [← hpPair]
        exact hpEq
      rw [lift_pair] at hpLift
      obtain ⟨haEq, hbEq⟩ := ZFSet.pair_inj.mp hpLift
      have ha'' : a' = a := lift_injective haEq
      have hbmem : ZFSet.pair a b ∈ f := by
        rw [← ha'', ← hpPair]
        exact hp
      rw [← hbEq, huniq b hbmem]

theorem lift_funs (x y : ZFSet.{u}) : lift (ZFSet.funs x y) = ZFSet.funs (lift x) (lift y) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨f, hf, rfl⟩ := mem_lift.mp hz
    exact ZFSet.mem_funs.mpr (lift_isFunc (ZFSet.mem_funs.mp hf))
  · intro hz
    have hF : ZFSet.IsFunc (lift x) (lift y) z := ZFSet.mem_funs.mp hz
    have subset : z ⊆ lift (ZFSet.prod x y) := by
      rw [lift_prod]
      exact hF.1
    obtain ⟨f, hfSub, rfl⟩ := subset_lift_classification.mp subset
    refine mem_lift.mpr ⟨f, ZFSet.mem_funs.mpr ⟨hfSub, ?_⟩, rfl⟩
    intro a ha
    obtain ⟨W, hW, hWuniq⟩ := hF.2 (lift a) (lift_mem_lift.mpr ha)
    obtain ⟨p, hp, hpEq⟩ := mem_lift.mp hW
    obtain ⟨a', _, b, _, hpPair⟩ := ZFSet.mem_prod.mp (hfSub hp)
    have hpLift : lift (ZFSet.pair a' b) = ZFSet.pair (lift a) W := by
      rw [← hpPair]
      exact hpEq
    rw [lift_pair] at hpLift
    obtain ⟨haEq, hbEq⟩ := ZFSet.pair_inj.mp hpLift
    have ha'' : a' = a := lift_injective haEq
    have hbmem : ZFSet.pair a b ∈ f := by
      rw [← ha'', ← hpPair]
      exact hp
    refine ⟨b, hbmem, ?_⟩
    intro b' hb'
    have hlift : ZFSet.pair (lift a) (lift b') ∈ lift f := by
      rw [← lift_pair]
      exact lift_mem_lift.mpr hb'
    exact lift_injective ((hWuniq (lift b') hlift).trans hbEq.symm)

theorem lift_piSet (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u})
    (B : ZFSet.{u + 1} → ZFSet.{u + 1}) (agree : ∀ x ∈ a, B (lift x) = lift (b x)) :
    lift (piSet a b) = piSet (lift a) B := by
  unfold piSet
  rw [lift_separation (ZFSet.funs a (familyUnion a b))
      (fun graph => ∀ x ∈ a, ∀ y, ZFSet.pair x y ∈ graph → y ∈ b x)
      (fun graph => ∀ x ∈ lift a, ∀ y, ZFSet.pair x y ∈ graph → y ∈ B x)
      (by
        intro graph _
        constructor
        · intro lower X hX Y hY
          obtain ⟨x, hx, rfl⟩ := mem_lift.mp hX
          obtain ⟨p, hp, hpEq⟩ := mem_lift.mp hY
          have hYmem : Y ∈ lift (ZFSet.sUnion p) := by
            rw [lift_sUnion, hpEq]
            exact right_mem_sUnion_pair (lift x) Y
          obtain ⟨y, _, hy⟩ := mem_lift.mp hYmem
          have hpPair : p = ZFSet.pair x y := by
            apply lift_injective
            rw [hpEq, ← hy, lift_pair]
          have hyb : y ∈ b x := lower x hx y (hpPair.symm ▸ hp)
          rw [← hy, agree x hx]
          exact lift_mem_lift.mpr hyb
        · intro upper x hx y hxy
          have hpair : ZFSet.pair (lift x) (lift y) ∈ lift graph := by
            rw [← lift_pair]
            exact lift_mem_lift.mpr hxy
          have hymem : lift y ∈ B (lift x) :=
            upper (lift x) (lift_mem_lift.mpr hx) (lift y) hpair
          rw [agree x hx] at hymem
          exact lift_mem_lift.mp hymem),
    lift_funs, lift_familyUnion a b B agree]

theorem lift_tracePiSet (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u})
    (B : ZFSet.{u + 1} → ZFSet.{u + 1}) (agree : ∀ x ∈ a, B (lift x) = lift (b x)) :
    lift (tracePiSet a b) = tracePiSet (lift a) B := by
  unfold tracePiSet
  rw [lift_replacement (piSet a b) traceLam traceLam (fun f _ => (lift_traceLam f).symm),
    lift_piSet a b B agree]

end

end Mettapedia.Logic.HOL.Embedding.ZFSetLiftedTraceProducts
