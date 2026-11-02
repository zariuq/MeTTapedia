import Mettapedia.Languages.VibeITP.Presentation.SimultaneousMeaning
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousRuleShapes

/-! Specification meanings of preparation and first-match environment lookup.
All replacement rows are formed before a theorem rule uses the environment.
Strict-order witnesses justify skipping an entry; equality never skips it. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Spec Spec.SimultaneousInstantiation SimultaneousFormation

theorem entry_parts (sig : Sig) (entry : Entry) (symbol arity value : Pattern)
    (encoded : entryPattern symbol arity value = encEntry sig entry) :
    symbol = encSym sig entry.symbol ∧ arity = encNat entry.arity ∧ value = encTerm sig entry.value := by
  simpa [entryPattern, encEntry, cCons, cNil] using encoded

theorem nlt_distinct {left right : Pattern} (less : NLtM left right) :
    ∀ a b, decNat left = some a → decNat right = some b → a ≠ b := by
  intro a b readA readB same
  obtain ⟨actual, read, smaller⟩ := less b readB
  rw [readA] at read
  cases read
  exact (Nat.ne_of_lt smaller) same

theorem ms_rManyPrepareNil (T : Theory) : MeaningV2 T (jManyPrepare cNil cNil) := by
  refine ⟨[], [], rfl, rfl, ?_, rfl⟩
  intro replacement member
  cases member

theorem ms_rManyPrepareCons (T : Theory) (fid fbs v n d reps entries : Pattern)
    (declared : MeaningV2 T (jSymDecl (cSym fid cKFvar fbs)))
    (length : MeaningV2 T (jLen fbs n)) (formed : MeaningV2 T (jWf v))
    (depth : MeaningV2 T (jDepth v d)) (bounded : MeaningV2 T (jNLe d n))
    (tail : MeaningV2 T (jManyPrepare reps entries)) :
    MeaningV2 T (jManyPrepare (cCons (pairPattern (cSym fid cKFvar fbs) v) reps)
      (cCons (entryPattern (cSym fid cKFvar fbs) n v) entries)) := by
  change SymDeclM T.sig (cSym fid cKFvar fbs) at declared
  change LenM fbs n at length
  change WfM T.sig v at formed
  change DepthM T.sig v d at depth
  change NLeM d n at bounded
  change PrepareM T.sig reps entries at tail
  change PrepareM T.sig _ _
  obtain ⟨symbol, known, rfl, kind, rfl⟩ := symDecl_inv declared
  have free : kindOf T.sig symbol = .fvar := encKind_inj kind.symm
  obtain ⟨value, rfl, valueFormed⟩ := formed
  obtain ⟨source, prepared, rfl, rfl, restFormed, restPrepared⟩ := tail
  have arityRead := length _ (decList_encNatList _)
  rw [List.length_map] at arityRead
  have depthCode := depth value rfl
  obtain ⟨actualDepth, depthRead, fits⟩ := bounded _ arityRead
  rw [depthCode, decNat_encNat] at depthRead
  cases depthRead
  obtain ⟨info, allocated⟩ := Option.isSome_iff_exists.mp known
  have infoFree : info.kind = .fvar := by simpa [kindOf, allocated] using free
  have infoArity : (bindersOf T.sig symbol).length = info.arity := by
    simp [bindersOf, allocated, SymInfo.arity]
  have arityCode : n = encNat info.arity := decNat_unique n _ (infoArity ▸ arityRead)
  have symbolCode : cSym (encNat (symNumber symbol)) cKFvar (encNatList (bindersOf T.sig symbol)) =
      encSym T.sig symbol := by rw [encSym_eq, free]; rfl
  refine ⟨(symbol, value) :: source, ⟨symbol, info.arity, value⟩ :: prepared, ?_, ?_, ?_, ?_⟩
  · simp only [encReplacements_cons, encReplacement, symbolCode]
  · simp only [encEntries_cons, encEntry, symbolCode, arityCode]
  · intro replacement member
    rcases List.mem_cons.mp member with newest | previous
    · subst replacement; exact valueFormed
    · exact restFormed replacement previous
  · simp only [prepare, allocated]
    rw [if_pos ⟨infoFree, infoArity ▸ fits⟩, restPrepared]
    rfl

theorem ms_rManyHitFirst (T : Theory) (fid fbs n v rest : Pattern) :
    MeaningV2 T (jManyHit (cCons (entryPattern (cSym fid cKFvar fbs) n v) rest)
      (cSym fid cKFvar fbs) n v) := by
  intro prepared target _ encoded targetCode
  obtain ⟨first, tail, rfl, firstCode, _⟩ := encEntries_eq_cons T.sig prepared _ _ encoded.symm
  obtain ⟨symbolCode, arityCode, valueCode⟩ := entry_parts T.sig first _ _ _ firstCode
  have same : target = first.symbol := encSym_inj T.sig (targetCode.symm.trans symbolCode)
  subst target
  exact ⟨first, by simp [lookup], arityCode, valueCode⟩

private theorem hit_skip (sig : Sig) (idv bs k w rest fid fbs n v : Pattern)
    (distinct : ∀ a b, decNat idv = some a → decNat fid = some b → a ≠ b)
    (tail : HitM sig rest (cSym fid cKFvar fbs) n v) :
    HitM sig (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v := by
  intro prepared target valid encoded targetCode
  obtain ⟨first, following, rfl, firstCode, restCode⟩ := encEntries_eq_cons sig prepared _ _ encoded.symm
  have symbolCode := (entry_parts sig first _ _ _ firstCode).1
  have firstNumber := (encSym_parts sig first.symbol symbolCode).1
  have targetNumber := (encSym_parts sig target targetCode).1
  have different : target ≠ first.symbol := by
    intro same
    apply distinct _ _ (decNat_of_eq firstNumber) (decNat_of_eq targetNumber)
    rw [same]
  have restValid : EntriesShape sig following := fun entry member => valid entry (List.mem_cons_of_mem _ member)
  obtain ⟨entry, found, arityCode, valueCode⟩ := tail following target restValid restCode targetCode
  exact ⟨entry, by simpa only [lookup, different, if_false] using found, arityCode, valueCode⟩

theorem ms_rManyHitLt (T : Theory) (idv bs k w rest fid fbs n v : Pattern)
    (less : MeaningV2 T (jNLt idv fid)) (tail : MeaningV2 T (jManyHit rest (cSym fid cKFvar fbs) n v)) :
    MeaningV2 T (jManyHit (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v) :=
  hit_skip T.sig idv bs k w rest fid fbs n v (nlt_distinct less) tail

theorem ms_rManyHitGt (T : Theory) (idv bs k w rest fid fbs n v : Pattern)
    (less : MeaningV2 T (jNLt fid idv)) (tail : MeaningV2 T (jManyHit rest (cSym fid cKFvar fbs) n v)) :
    MeaningV2 T (jManyHit (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) n v) :=
  hit_skip T.sig idv bs k w rest fid fbs n v
    (fun a b readA readB same => nlt_distinct less b a readB readA same.symm) tail

theorem ms_rManyMissNil (T : Theory) (fid fbs : Pattern) :
    MeaningV2 T (jManyMiss cNil (cSym fid cKFvar fbs)) := by
  intro prepared target _ encoded _
  have empty : [] = prepared := encEntries_injective T.sig encoded
  subst prepared
  rfl

private theorem miss_skip (sig : Sig) (idv bs k w rest fid fbs : Pattern)
    (distinct : ∀ a b, decNat idv = some a → decNat fid = some b → a ≠ b)
    (tail : MissM sig rest (cSym fid cKFvar fbs)) :
    MissM sig (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs) := by
  intro prepared target valid encoded targetCode
  obtain ⟨first, following, rfl, firstCode, restCode⟩ := encEntries_eq_cons sig prepared _ _ encoded.symm
  have symbolCode := (entry_parts sig first _ _ _ firstCode).1
  have firstNumber := (encSym_parts sig first.symbol symbolCode).1
  have targetNumber := (encSym_parts sig target targetCode).1
  have different : target ≠ first.symbol := by
    intro same
    apply distinct _ _ (decNat_of_eq firstNumber) (decNat_of_eq targetNumber)
    rw [same]
  have restValid : EntriesShape sig following := fun entry member => valid entry (List.mem_cons_of_mem _ member)
  simpa only [lookup, different, if_false] using tail following target restValid restCode targetCode

theorem ms_rManyMissLt (T : Theory) (idv bs k w rest fid fbs : Pattern)
    (less : MeaningV2 T (jNLt idv fid)) (tail : MeaningV2 T (jManyMiss rest (cSym fid cKFvar fbs))) :
    MeaningV2 T (jManyMiss (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs)) :=
  miss_skip T.sig idv bs k w rest fid fbs (nlt_distinct less) tail

theorem ms_rManyMissGt (T : Theory) (idv bs k w rest fid fbs : Pattern)
    (less : MeaningV2 T (jNLt fid idv)) (tail : MeaningV2 T (jManyMiss rest (cSym fid cKFvar fbs))) :
    MeaningV2 T (jManyMiss (cCons (entryPattern (cSym idv cKFvar bs) k w) rest) (cSym fid cKFvar fbs)) :=
  miss_skip T.sig idv bs k w rest fid fbs
    (fun a b readA readB same => nlt_distinct less b a readB readA same.symm) tail

#print axioms ms_rManyPrepareCons
#print axioms ms_rManyHitFirst
#print axioms ms_rManyMissGt

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
