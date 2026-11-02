import Mettapedia.GSLT.Parsing.PackedForestCatalogueExecution

/-! Exhaustive selected catalogues of the existing class-aware forest.
Physical production indices remain inside each family; identical shared
family data is represented once by the packed store. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareForestCatalogue

open ClassAwarePackedForest ClassAwarePackedForestKBest
open ClassAwareParserPackCertificate ClassAwareParserPackCorrespondence
open PackedForestCatalogue

abbrev Tree := PackedForestSelection.Derivation Family
abbrev Store := Cache NodeKey Family

def keys (forest : Forest) : List NodeKey := (forest.roots ++ forest.families.map Family.parent).eraseDups

theorem inventory (forest : Forest) (key : NodeKey) : familiesAt forest key ≠ [] → key ∈ keys forest := by
  intro nonempty
  obtain ⟨family, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨present, same⟩ := (family_at_iff _ _ _).mp member
  simp only [keys, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact Or.inr ⟨family, present, same⟩

def catalogue? (forest : Forest) (allow : Family → Bool) (rounds : Nat) : Option Store :=
  PackedForestCatalogue.catalogue? (familiesAt forest) (fun family => nodeChildren family.children)
    allow (keys forest) rounds

theorem catalogue?_exact (forest : Forest) (allow : Family → Bool) (rounds : Nat) (store : Store)
    (finished : catalogue? forest allow rounds = some store) (key : NodeKey) (tree : Tree) :
    tree ∈ lookup store key ↔ Unfolds (familiesAt forest) (fun family => nodeChildren family.children) allow key tree :=
  PackedForestCatalogue.catalogue?_exact _ _ _ _ _ _ (inventory forest) finished key tree

mutual
  def ofCertificate (sort : String) : Certificate → Tree
    | certificate@(.lexical _ _ _ _) => .node (certificateFamily sort certificate) []
    | certificate@(.structural _ _ _ body) => .node (certificateFamily sort certificate) (ofItems body)

  def ofItems : ItemsCertificate → List Tree
    | .nil _ => []
    | .terminal _ _ _ rest => ofItems rest
    | .nonterminal sort _ _ head rest => ofCertificate sort head :: ofItems rest
end

def treeKey : Tree → NodeKey
  | .node family _ => family.parent

theorem certificate_key (sort : String) (certificate : Certificate) :
    treeKey (ofCertificate sort certificate) = certificateKey sort certificate := by
  cases certificate <;> rfl

def restoreItems : Nat → List ChildRef → List Certificate → Option ItemsCertificate
  | cursor, [], [] => some (.nil cursor)
  | _, .terminal matcher start stop :: rest, nested =>
      (.terminal matcher start stop ·) <$> restoreItems stop rest nested
  | _, .node key :: rest, head :: nested =>
      (.nonterminal key.resultSort key.start key.stop head ·) <$> restoreItems key.stop rest nested
  | _, _, _ => none

mutual
  def restore : Tree → Option Certificate
    | .node family children => do
      let nested ← restoreList children
      match family.production with
      | .lexical position =>
        match family.children, nested with
        | [.terminal matcher start stop], [] => some (.lexical position matcher start stop)
        | _, _ => none
      | .structural position =>
        let body ← restoreItems family.parent.start family.children nested
        some (.structural position family.parent.start family.parent.stop body)

  def restoreList : List Tree → Option (List Certificate)
    | [] => some []
    | head :: rest => do pure ((← restore head) :: (← restoreList rest))
end

mutual
  theorem restore_replayed {profile : ParserProfileSemantics.ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {sort : String} {start stop : Nat} {tree : PresentationExprSemantics.CST}
      {certificate : Certificate} (replayed : Replays profile plan input certificate sort start stop tree) :
      restore (ofCertificate sort certificate) = some certificate :=
    match replayed with
    | .lexical _ _ _ _ _ _ => rfl
    | .structural position valid sortExact labelExact body => by
      simp only [ofCertificate, restore, certificateFamily]
      have inverse := restore_items body
      cases expanded : restoreList (ofItems _) with
      | none => simp [expanded] at inverse
      | some nested =>
        simp only [expanded, Option.bind_some] at inverse
        dsimp only [Bind.bind, Option.bind]
        rw [inverse]
    termination_by structural replayed

  theorem restore_items {profile : ParserProfileSemantics.ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {items : List PackItem} {start stop : Nat} {values : List PresentationExprSemantics.CST}
      {body : ItemsCertificate} (replayed : ItemsReplays profile plan input body items start stop values) :
      (restoreList (ofItems body)).bind (restoreItems start (itemsChildRefs body)) = some body :=
    match replayed with
    | .nil => rfl
    | .terminal matched rest => by
      have inverse := restore_items rest
      simp only [ofItems, itemsChildRefs]
      cases expanded : restoreList (ofItems _) with
      | none => simp [expanded] at inverse
      | some nested =>
        dsimp only [Bind.bind, Option.bind, Pure.pure, restoreItems]
        simp only [expanded, Option.bind_some] at inverse
        rw [inverse]
        rfl
    | .nonterminal head rest => by
      have inverse := restore_items rest
      simp only [ofItems, restoreList, restore_replayed head, itemsChildRefs]
      dsimp only [Bind.bind, Option.bind]
      cases expanded : restoreList (ofItems _) with
      | none => simp [expanded] at inverse
      | some nested =>
        dsimp only [Bind.bind, Option.bind, Pure.pure, restoreItems]
        simp only [expanded, Option.bind_some] at inverse
        rw [inverse]
        rfl
    termination_by structural replayed
end

end Mettapedia.GSLT.Parsing.ClassAwareForestCatalogue
