import Mettapedia.Languages.SUMO.Native.Semantics

/-!
# Semantic naturality of native SUMO renaming and substitution

This file proves the environment equations needed by quantified proof rules.
In particular, ordinary and row instantiation are interpreted by extending the
corresponding semantic environment, including beneath nested binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native

universe uSymbol uLiteral uModel

namespace Model

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}
variable {model : Model Symbol Literal}
variable {ordinary ordinary' rows rows' : Nat}

/-- Pull a semantic ordinary-variable environment back along a renaming. -/
def renameObjects
    (objects : model.ObjectEnvironment ordinary')
    (mapping : OrdinaryRenaming ordinary ordinary') :
    model.ObjectEnvironment ordinary :=
  fun index => objects (mapping index)

/-- Pull a semantic row environment back along a row renaming. -/
def renameRows
    (rowValues : model.RowEnvironment rows')
    (mapping : RowRenaming rows rows') :
    model.RowEnvironment rows :=
  fun index => rowValues (mapping index)

@[simp] theorem renameObjects_underObject
    (objects : model.ObjectEnvironment ordinary')
    (mapping : OrdinaryRenaming ordinary ordinary')
    (value : model.Carrier) :
    renameObjects (Fin.cases value objects) (Renaming.underObject mapping) =
      Fin.cases value (renameObjects objects mapping) := by
  funext index
  refine Fin.cases ?_ (fun previous => ?_) index <;> rfl

@[simp] theorem renameRows_underRow
    (rowValues : model.RowEnvironment rows')
    (mapping : RowRenaming rows rows')
    (values : List model.Carrier) :
    renameRows (Fin.cases values rowValues) (Renaming.underRow mapping) =
      Fin.cases values (renameRows rowValues mapping) := by
  funext index
  refine Fin.cases ?_ (fun previous => ?_) index <;> rfl

mutual
  /-- Term denotation commutes with simultaneous ordinary/row renaming. -/
  theorem denote_rename_term
      {ordinary ordinary' rows rows' : Nat}
      (model : Model Symbol Literal)
      (ordinaryMap : OrdinaryRenaming ordinary ordinary')
      (rowMap : RowRenaming rows rows')
      (objects : model.ObjectEnvironment ordinary')
      (rowValues : model.RowEnvironment rows') :
      (value : Term Symbol Literal ordinary rows) ->
      model.denoteTermLifted objects rowValues
          (Renaming.term ordinaryMap rowMap value) =
        model.denoteTermLifted (renameObjects objects ordinaryMap)
          (renameRows rowValues rowMap) value
    | .var _ => rfl
    | .constant _ => rfl
    | .literal _ => rfl
    | .application operator arguments => by
        change model.applyFunction _ _ = model.applyFunction _ _
        rw [denote_rename_term model ordinaryMap rowMap objects rowValues operator,
          denote_rename_spine model ordinaryMap rowMap objects rowValues arguments]
    | .quote body => by
        change model.quote _ = model.quote _
        rw [denote_rename_formula model ordinaryMap rowMap objects rowValues body]
    | .kappa body => by
        change model.kappa _ = model.kappa _
        apply congrArg model.kappa
        funext value
        rw [denote_rename_formula model (Renaming.underObject ordinaryMap)
          rowMap (Fin.cases value objects) rowValues body]
        rw [renameObjects_underObject]

  /-- Exact spine expansion commutes with simultaneous renaming. -/
  theorem denote_rename_spine
      {ordinary ordinary' rows rows' : Nat}
      (model : Model Symbol Literal)
      (ordinaryMap : OrdinaryRenaming ordinary ordinary')
      (rowMap : RowRenaming rows rows')
      (objects : model.ObjectEnvironment ordinary')
      (rowValues : model.RowEnvironment rows') :
      (arguments : Spine Symbol Literal ordinary rows) ->
      model.denoteSpineLifted objects rowValues
          (Renaming.spine ordinaryMap rowMap arguments) =
        model.denoteSpineLifted (renameObjects objects ordinaryMap)
          (renameRows rowValues rowMap) arguments
    | .nil => rfl
    | .term value rest => by
        change _ :: _ = _ :: _
        rw [denote_rename_term model ordinaryMap rowMap objects rowValues value,
          denote_rename_spine model ordinaryMap rowMap objects rowValues rest]
    | .row _ rest => by
        change _ ++ _ = _ ++ _
        rw [denote_rename_spine model ordinaryMap rowMap objects rowValues rest]
        rfl

  /-- World intension commutes with simultaneous ordinary/row renaming. -/
  theorem denote_rename_formula
      {ordinary ordinary' rows rows' : Nat}
      (model : Model Symbol Literal)
      (ordinaryMap : OrdinaryRenaming ordinary ordinary')
      (rowMap : RowRenaming rows rows')
      (objects : model.ObjectEnvironment ordinary')
      (rowValues : model.RowEnvironment rows') :
      (body : Formula Symbol Literal ordinary rows) ->
      model.denoteFormulaLifted objects rowValues
          (Renaming.formula ordinaryMap rowMap body) =
        model.denoteFormulaLifted (renameObjects objects ordinaryMap)
          (renameRows rowValues rowMap) body
    | .top => rfl
    | .bottom => rfl
    | .atom operator arguments => by
        funext world
        apply propext
        change model.applyRelation _ _ world <-> model.applyRelation _ _ world
        rw [denote_rename_term model ordinaryMap rowMap objects rowValues operator,
          denote_rename_spine model ordinaryMap rowMap objects rowValues arguments]
    | .asserted value => by
        funext world
        apply propext
        change model.holds _ world <-> model.holds _ world
        rw [denote_rename_term model ordinaryMap rowMap objects rowValues value]
    | .equal left right => by
        funext world
        apply propext
        change (_ = _) <-> (_ = _)
        rw [denote_rename_term model ordinaryMap rowMap objects rowValues left,
          denote_rename_term model ordinaryMap rowMap objects rowValues right]
    | .inOperatorDomain operator position argument => by
        funext world
        apply propext
        change model.inOperatorDomainAt _ position _ world <->
          model.inOperatorDomainAt _ position _ world
        rw [denote_rename_term model ordinaryMap rowMap objects rowValues operator,
          denote_rename_term model ordinaryMap rowMap objects rowValues argument]
    | .tailInOperatorDomain operator firstPosition arguments => by
        funext world
        apply propext
        change model.tailInOperatorDomainFrom _ firstPosition _ world <->
          model.tailInOperatorDomainFrom _ firstPosition _ world
        rw [denote_rename_term model ordinaryMap rowMap objects rowValues operator,
          denote_rename_spine model ordinaryMap rowMap objects rowValues arguments]
    | .not body => by
        funext world
        apply propext
        change
          (Not (model.denoteFormulaLifted objects rowValues
            (Renaming.formula ordinaryMap rowMap body) world)) <->
          Not (model.denoteFormulaLifted (renameObjects objects ordinaryMap)
            (renameRows rowValues rowMap) body world)
        rw [denote_rename_formula model ordinaryMap rowMap objects rowValues body]
    | .and left right => by
        funext world
        apply propext
        change
          (model.denoteFormulaLifted objects rowValues
              (Renaming.formula ordinaryMap rowMap left) world /\
            model.denoteFormulaLifted objects rowValues
              (Renaming.formula ordinaryMap rowMap right) world) <->
          (model.denoteFormulaLifted (renameObjects objects ordinaryMap)
              (renameRows rowValues rowMap) left world /\
            model.denoteFormulaLifted (renameObjects objects ordinaryMap)
              (renameRows rowValues rowMap) right world)
        rw [denote_rename_formula model ordinaryMap rowMap objects rowValues left,
          denote_rename_formula model ordinaryMap rowMap objects rowValues right]
    | .or left right => by
        funext world
        apply propext
        change
          (model.denoteFormulaLifted objects rowValues
              (Renaming.formula ordinaryMap rowMap left) world \/
            model.denoteFormulaLifted objects rowValues
              (Renaming.formula ordinaryMap rowMap right) world) <->
          (model.denoteFormulaLifted (renameObjects objects ordinaryMap)
              (renameRows rowValues rowMap) left world \/
            model.denoteFormulaLifted (renameObjects objects ordinaryMap)
              (renameRows rowValues rowMap) right world)
        rw [denote_rename_formula model ordinaryMap rowMap objects rowValues left,
          denote_rename_formula model ordinaryMap rowMap objects rowValues right]
    | .implies left right => by
        funext world
        apply propext
        change
          (model.denoteFormulaLifted objects rowValues
              (Renaming.formula ordinaryMap rowMap left) world ->
            model.denoteFormulaLifted objects rowValues
              (Renaming.formula ordinaryMap rowMap right) world) <->
          (model.denoteFormulaLifted (renameObjects objects ordinaryMap)
              (renameRows rowValues rowMap) left world ->
            model.denoteFormulaLifted (renameObjects objects ordinaryMap)
              (renameRows rowValues rowMap) right world)
        rw [denote_rename_formula model ordinaryMap rowMap objects rowValues left,
          denote_rename_formula model ordinaryMap rowMap objects rowValues right]
    | .iff left right => by
        funext world
        apply propext
        change
          (model.denoteFormulaLifted objects rowValues
              (Renaming.formula ordinaryMap rowMap left) world <->
            model.denoteFormulaLifted objects rowValues
              (Renaming.formula ordinaryMap rowMap right) world) <->
          (model.denoteFormulaLifted (renameObjects objects ordinaryMap)
              (renameRows rowValues rowMap) left world <->
            model.denoteFormulaLifted (renameObjects objects ordinaryMap)
              (renameRows rowValues rowMap) right world)
        rw [denote_rename_formula model ordinaryMap rowMap objects rowValues left,
          denote_rename_formula model ordinaryMap rowMap objects rowValues right]
    | .allInSpine arguments body => by
        funext world
        apply propext
        change
          (forall value,
            value ∈ model.denoteSpineLifted objects rowValues
                (Renaming.spine ordinaryMap rowMap arguments) ->
              model.denoteFormulaLifted (Fin.cases value objects) rowValues
                (Renaming.formula (Renaming.underObject ordinaryMap) rowMap body)
                world) <->
          (forall value,
            value ∈ model.denoteSpineLifted
                (renameObjects objects ordinaryMap)
                (renameRows rowValues rowMap) arguments ->
              model.denoteFormulaLifted
                (Fin.cases value (renameObjects objects ordinaryMap))
                (renameRows rowValues rowMap) body world)
        rw [denote_rename_spine model ordinaryMap rowMap objects rowValues arguments]
        constructor
        · intro premise value membership
          have consequence := premise value membership
          rw [denote_rename_formula model (Renaming.underObject ordinaryMap)
            rowMap (Fin.cases value objects) rowValues body] at consequence
          simpa only [renameObjects_underObject] using consequence
        · intro premise value membership
          have consequence := premise value membership
          rw [denote_rename_formula model (Renaming.underObject ordinaryMap)
            rowMap (Fin.cases value objects) rowValues body]
          simpa only [renameObjects_underObject] using consequence
    | .allObject body => by
        funext world
        apply propext
        constructor
        · intro premise value
          have consequence := premise value
          rw [denote_rename_formula model (Renaming.underObject ordinaryMap)
            rowMap (Fin.cases value objects) rowValues body] at consequence
          simpa only [renameObjects_underObject] using consequence
        · intro premise value
          have consequence := premise value
          rw [denote_rename_formula model (Renaming.underObject ordinaryMap)
            rowMap (Fin.cases value objects) rowValues body]
          simpa only [renameObjects_underObject] using consequence
    | .someObject body => by
        funext world
        apply propext
        constructor
        · rintro ⟨value, witness⟩
          refine ⟨value, ?_⟩
          rw [denote_rename_formula model (Renaming.underObject ordinaryMap)
            rowMap (Fin.cases value objects) rowValues body] at witness
          simpa only [renameObjects_underObject] using witness
        · rintro ⟨value, witness⟩
          refine ⟨value, ?_⟩
          rw [denote_rename_formula model (Renaming.underObject ordinaryMap)
            rowMap (Fin.cases value objects) rowValues body]
          simpa only [renameObjects_underObject] using witness
    | .allRow body => by
        funext world
        apply propext
        constructor
        · intro premise values
          have consequence := premise values
          rw [denote_rename_formula model ordinaryMap (Renaming.underRow rowMap)
            objects (Fin.cases values rowValues) body] at consequence
          simpa only [renameRows_underRow] using consequence
        · intro premise values
          have consequence := premise values
          rw [denote_rename_formula model ordinaryMap (Renaming.underRow rowMap)
            objects (Fin.cases values rowValues) body]
          simpa only [renameRows_underRow] using consequence
    | .someRow body => by
        funext world
        apply propext
        constructor
        · rintro ⟨values, witness⟩
          refine ⟨values, ?_⟩
          rw [denote_rename_formula model ordinaryMap (Renaming.underRow rowMap)
            objects (Fin.cases values rowValues) body] at witness
          simpa only [renameRows_underRow] using witness
        · rintro ⟨values, witness⟩
          refine ⟨values, ?_⟩
          rw [denote_rename_formula model ordinaryMap (Renaming.underRow rowMap)
            objects (Fin.cases values rowValues) body]
          simpa only [renameRows_underRow] using witness
end

/-- Interpret every source ordinary variable through a substitution. -/
def substitutedObjects
    (model : Model Symbol Literal)
    (substitution : Substitution Symbol Literal ordinary rows ordinary' rows')
    (objects : model.ObjectEnvironment ordinary')
    (rowValues : model.RowEnvironment rows') :
    model.ObjectEnvironment ordinary :=
  fun index => model.denoteTerm objects rowValues (substitution.object index)

/-- Interpret every source row variable through a substitution. -/
def substitutedRows
    (model : Model Symbol Literal)
    (substitution : Substitution Symbol Literal ordinary rows ordinary' rows')
    (objects : model.ObjectEnvironment ordinary')
    (rowValues : model.RowEnvironment rows') :
    model.RowEnvironment rows :=
  fun index => model.denoteSpine objects rowValues (substitution.row index)

/-- Denotation turns syntactic spine concatenation into list concatenation. -/
theorem denoteSpine_append
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (suffix : Spine Symbol Literal ordinary rows) :
    (first : Spine Symbol Literal ordinary rows) ->
      model.denoteSpineLifted objects rowValues (Spine.append first suffix) =
        model.denoteSpineLifted objects rowValues first ++
          model.denoteSpineLifted objects rowValues suffix
  | .nil => rfl
  | .term value rest => by
      change _ :: _ = (_ :: _) ++ _
      rw [denoteSpine_append model objects rowValues suffix rest]
      rfl
  | .row index rest => by
      change rowValues index ++ _ = (rowValues index ++ _) ++ _
      rw [denoteSpine_append model objects rowValues suffix rest]
      exact (List.append_assoc _ _ _).symm

@[simp] theorem substitutedObjects_underObject
    (model : Model Symbol Literal)
    (substitution :
      Substitution Symbol Literal ordinary rows ordinary' rows')
    (objects : model.ObjectEnvironment ordinary')
    (rowValues : model.RowEnvironment rows')
    (value : model.Carrier) :
    substitutedObjects model (Substitution.underObject substitution)
        (Fin.cases value objects) rowValues =
      Fin.cases value (substitutedObjects model substitution objects rowValues) := by
  funext index
  refine Fin.cases ?_ (fun previous => ?_) index
  · rfl
  · change model.denoteTermLifted (Fin.cases value objects) rowValues
        (Renaming.term Fin.succ (fun rowIndex => rowIndex)
          (substitution.object previous)) =
      model.denoteTermLifted objects rowValues (substitution.object previous)
    rw [denote_rename_term model Fin.succ (fun rowIndex => rowIndex)
      (Fin.cases value objects) rowValues (substitution.object previous)]
    rfl

@[simp] theorem substitutedRows_underObject
    (model : Model Symbol Literal)
    (substitution :
      Substitution Symbol Literal ordinary rows ordinary' rows')
    (objects : model.ObjectEnvironment ordinary')
    (rowValues : model.RowEnvironment rows')
    (value : model.Carrier) :
    substitutedRows model (Substitution.underObject substitution)
        (Fin.cases value objects) rowValues =
      substitutedRows model substitution objects rowValues := by
  funext index
  change model.denoteSpineLifted (Fin.cases value objects) rowValues
      (Renaming.spine Fin.succ (fun rowIndex => rowIndex)
        (substitution.row index)) =
    model.denoteSpineLifted objects rowValues (substitution.row index)
  rw [denote_rename_spine model Fin.succ (fun rowIndex => rowIndex)
    (Fin.cases value objects) rowValues (substitution.row index)]
  rfl

@[simp] theorem substitutedObjects_underRow
    (model : Model Symbol Literal)
    (substitution :
      Substitution Symbol Literal ordinary rows ordinary' rows')
    (objects : model.ObjectEnvironment ordinary')
    (rowValues : model.RowEnvironment rows')
    (values : List model.Carrier) :
    substitutedObjects model (Substitution.underRow substitution)
        objects (Fin.cases values rowValues) =
      substitutedObjects model substitution objects rowValues := by
  funext index
  change model.denoteTermLifted objects (Fin.cases values rowValues)
      (Renaming.term (fun objectIndex => objectIndex) Fin.succ
        (substitution.object index)) =
    model.denoteTermLifted objects rowValues (substitution.object index)
  rw [denote_rename_term model (fun objectIndex => objectIndex) Fin.succ
    objects (Fin.cases values rowValues) (substitution.object index)]
  rfl

@[simp] theorem substitutedRows_underRow
    (model : Model Symbol Literal)
    (substitution :
      Substitution Symbol Literal ordinary rows ordinary' rows')
    (objects : model.ObjectEnvironment ordinary')
    (rowValues : model.RowEnvironment rows')
    (values : List model.Carrier) :
    substitutedRows model (Substitution.underRow substitution)
        objects (Fin.cases values rowValues) =
      Fin.cases values (substitutedRows model substitution objects rowValues) := by
  funext index
  refine Fin.cases ?_ (fun previous => ?_) index
  · change values ++ [] = values
    exact List.append_nil values
  · change model.denoteSpineLifted objects (Fin.cases values rowValues)
        (Renaming.spine (fun objectIndex => objectIndex) Fin.succ
          (substitution.row previous)) =
      model.denoteSpineLifted objects rowValues (substitution.row previous)
    rw [denote_rename_spine model (fun objectIndex => objectIndex) Fin.succ
      objects (Fin.cases values rowValues) (substitution.row previous)]
    rfl

mutual
  /-- Term denotation commutes with simultaneous ordinary/row substitution. -/
  theorem denote_substitute_term
      {ordinary rows ordinary' rows' : Nat}
      (model : Model Symbol Literal)
      (substitution :
        Substitution Symbol Literal ordinary rows ordinary' rows')
      (objects : model.ObjectEnvironment ordinary')
      (rowValues : model.RowEnvironment rows') :
      (value : Term Symbol Literal ordinary rows) ->
      model.denoteTermLifted objects rowValues
          (Substitution.term substitution value) =
        model.denoteTermLifted
          (substitutedObjects model substitution objects rowValues)
          (substitutedRows model substitution objects rowValues) value
    | .var _ => rfl
    | .constant _ => rfl
    | .literal _ => rfl
    | .application operator arguments => by
        change model.applyFunction _ _ = model.applyFunction _ _
        rw [denote_substitute_term model substitution objects rowValues operator,
          denote_substitute_spine model substitution objects rowValues arguments]
    | .quote body => by
        change model.quote _ = model.quote _
        rw [denote_substitute_formula model substitution objects rowValues body]
    | .kappa body => by
        change model.kappa _ = model.kappa _
        apply congrArg model.kappa
        funext value
        rw [denote_substitute_formula model
          (Substitution.underObject substitution)
          (Fin.cases value objects) rowValues body]
        rw [substitutedObjects_underObject, substitutedRows_underObject]

  /-- Exact spine denotation commutes with simultaneous substitution. -/
  theorem denote_substitute_spine
      {ordinary rows ordinary' rows' : Nat}
      (model : Model Symbol Literal)
      (substitution :
        Substitution Symbol Literal ordinary rows ordinary' rows')
      (objects : model.ObjectEnvironment ordinary')
      (rowValues : model.RowEnvironment rows') :
      (arguments : Spine Symbol Literal ordinary rows) ->
      model.denoteSpineLifted objects rowValues
          (Substitution.spine substitution arguments) =
        model.denoteSpineLifted
          (substitutedObjects model substitution objects rowValues)
          (substitutedRows model substitution objects rowValues) arguments
    | .nil => rfl
    | .term value rest => by
        change _ :: _ = _ :: _
        rw [denote_substitute_term model substitution objects rowValues value,
          denote_substitute_spine model substitution objects rowValues rest]
    | .row index rest => by
        change model.denoteSpineLifted objects rowValues
            (Spine.append (substitution.row index)
              (Substitution.spine substitution rest)) =
          substitutedRows model substitution objects rowValues index ++
            model.denoteSpineLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) rest
        rw [denoteSpine_append model objects rowValues
          (Substitution.spine substitution rest) (substitution.row index)]
        rw [denote_substitute_spine model substitution objects rowValues rest]
        rfl

  /-- Formula intension commutes with simultaneous substitution. -/
  theorem denote_substitute_formula
      {ordinary rows ordinary' rows' : Nat}
      (model : Model Symbol Literal)
      (substitution :
        Substitution Symbol Literal ordinary rows ordinary' rows')
      (objects : model.ObjectEnvironment ordinary')
      (rowValues : model.RowEnvironment rows') :
      (body : Formula Symbol Literal ordinary rows) ->
      model.denoteFormulaLifted objects rowValues
          (Substitution.formula substitution body) =
        model.denoteFormulaLifted
          (substitutedObjects model substitution objects rowValues)
          (substitutedRows model substitution objects rowValues) body
    | .top => rfl
    | .bottom => rfl
    | .atom operator arguments => by
        funext world
        apply propext
        change model.applyRelation _ _ world <-> model.applyRelation _ _ world
        rw [denote_substitute_term model substitution objects rowValues operator,
          denote_substitute_spine model substitution objects rowValues arguments]
    | .asserted value => by
        funext world
        apply propext
        change model.holds _ world <-> model.holds _ world
        rw [denote_substitute_term model substitution objects rowValues value]
    | .equal left right => by
        funext world
        apply propext
        change (_ = _) <-> (_ = _)
        rw [denote_substitute_term model substitution objects rowValues left,
          denote_substitute_term model substitution objects rowValues right]
    | .inOperatorDomain operator position argument => by
        funext world
        apply propext
        change model.inOperatorDomainAt _ position _ world <->
          model.inOperatorDomainAt _ position _ world
        rw [denote_substitute_term model substitution objects rowValues operator,
          denote_substitute_term model substitution objects rowValues argument]
    | .tailInOperatorDomain operator firstPosition arguments => by
        funext world
        apply propext
        change model.tailInOperatorDomainFrom _ firstPosition _ world <->
          model.tailInOperatorDomainFrom _ firstPosition _ world
        rw [denote_substitute_term model substitution objects rowValues operator,
          denote_substitute_spine model substitution objects rowValues arguments]
    | .not body => by
        funext world
        apply propext
        change
          (Not (model.denoteFormulaLifted objects rowValues
            (Substitution.formula substitution body) world)) <->
          Not (model.denoteFormulaLifted
            (substitutedObjects model substitution objects rowValues)
            (substitutedRows model substitution objects rowValues) body world)
        rw [denote_substitute_formula model substitution objects rowValues body]
    | .and left right => by
        funext world
        apply propext
        change
          (model.denoteFormulaLifted objects rowValues
              (Substitution.formula substitution left) world /\
            model.denoteFormulaLifted objects rowValues
              (Substitution.formula substitution right) world) <->
          (model.denoteFormulaLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) left world /\
            model.denoteFormulaLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) right world)
        rw [denote_substitute_formula model substitution objects rowValues left,
          denote_substitute_formula model substitution objects rowValues right]
    | .or left right => by
        funext world
        apply propext
        change
          (model.denoteFormulaLifted objects rowValues
              (Substitution.formula substitution left) world \/
            model.denoteFormulaLifted objects rowValues
              (Substitution.formula substitution right) world) <->
          (model.denoteFormulaLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) left world \/
            model.denoteFormulaLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) right world)
        rw [denote_substitute_formula model substitution objects rowValues left,
          denote_substitute_formula model substitution objects rowValues right]
    | .implies left right => by
        funext world
        apply propext
        change
          (model.denoteFormulaLifted objects rowValues
              (Substitution.formula substitution left) world ->
            model.denoteFormulaLifted objects rowValues
              (Substitution.formula substitution right) world) <->
          (model.denoteFormulaLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) left world ->
            model.denoteFormulaLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) right world)
        rw [denote_substitute_formula model substitution objects rowValues left,
          denote_substitute_formula model substitution objects rowValues right]
    | .iff left right => by
        funext world
        apply propext
        change
          (model.denoteFormulaLifted objects rowValues
              (Substitution.formula substitution left) world <->
            model.denoteFormulaLifted objects rowValues
              (Substitution.formula substitution right) world) <->
          (model.denoteFormulaLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) left world <->
            model.denoteFormulaLifted
              (substitutedObjects model substitution objects rowValues)
              (substitutedRows model substitution objects rowValues) right world)
        rw [denote_substitute_formula model substitution objects rowValues left,
          denote_substitute_formula model substitution objects rowValues right]
    | .allInSpine arguments body => by
        funext world
        apply propext
        change
          (forall value,
            value ∈ model.denoteSpineLifted objects rowValues
                (Substitution.spine substitution arguments) ->
              model.denoteFormulaLifted (Fin.cases value objects) rowValues
                (Substitution.formula (Substitution.underObject substitution) body)
                world) <->
          (forall value,
            value ∈ model.denoteSpineLifted
                (substitutedObjects model substitution objects rowValues)
                (substitutedRows model substitution objects rowValues) arguments ->
              model.denoteFormulaLifted
                (Fin.cases value
                  (substitutedObjects model substitution objects rowValues))
                (substitutedRows model substitution objects rowValues) body world)
        rw [denote_substitute_spine model substitution objects rowValues arguments]
        constructor
        · intro premise value membership
          have consequence := premise value membership
          rw [denote_substitute_formula model
            (Substitution.underObject substitution)
            (Fin.cases value objects) rowValues body] at consequence
          simpa only [substitutedObjects_underObject,
            substitutedRows_underObject] using consequence
        · intro premise value membership
          have consequence := premise value membership
          rw [denote_substitute_formula model
            (Substitution.underObject substitution)
            (Fin.cases value objects) rowValues body]
          simpa only [substitutedObjects_underObject,
            substitutedRows_underObject] using consequence
    | .allObject body => by
        funext world
        apply propext
        constructor
        · intro premise value
          have consequence := premise value
          rw [denote_substitute_formula model
            (Substitution.underObject substitution)
            (Fin.cases value objects) rowValues body] at consequence
          simpa only [substitutedObjects_underObject,
            substitutedRows_underObject] using consequence
        · intro premise value
          have consequence := premise value
          rw [denote_substitute_formula model
            (Substitution.underObject substitution)
            (Fin.cases value objects) rowValues body]
          simpa only [substitutedObjects_underObject,
            substitutedRows_underObject] using consequence
    | .someObject body => by
        funext world
        apply propext
        constructor
        · rintro ⟨value, witness⟩
          refine ⟨value, ?_⟩
          rw [denote_substitute_formula model
            (Substitution.underObject substitution)
            (Fin.cases value objects) rowValues body] at witness
          simpa only [substitutedObjects_underObject,
            substitutedRows_underObject] using witness
        · rintro ⟨value, witness⟩
          refine ⟨value, ?_⟩
          rw [denote_substitute_formula model
            (Substitution.underObject substitution)
            (Fin.cases value objects) rowValues body]
          simpa only [substitutedObjects_underObject,
            substitutedRows_underObject] using witness
    | .allRow body => by
        funext world
        apply propext
        constructor
        · intro premise values
          have consequence := premise values
          rw [denote_substitute_formula model
            (Substitution.underRow substitution)
            objects (Fin.cases values rowValues) body] at consequence
          simpa only [substitutedObjects_underRow,
            substitutedRows_underRow] using consequence
        · intro premise values
          have consequence := premise values
          rw [denote_substitute_formula model
            (Substitution.underRow substitution)
            objects (Fin.cases values rowValues) body]
          simpa only [substitutedObjects_underRow,
            substitutedRows_underRow] using consequence
    | .someRow body => by
        funext world
        apply propext
        constructor
        · rintro ⟨values, witness⟩
          refine ⟨values, ?_⟩
          rw [denote_substitute_formula model
            (Substitution.underRow substitution)
            objects (Fin.cases values rowValues) body] at witness
          simpa only [substitutedObjects_underRow,
            substitutedRows_underRow] using witness
        · rintro ⟨values, witness⟩
          refine ⟨values, ?_⟩
          rw [denote_substitute_formula model
            (Substitution.underRow substitution)
            objects (Fin.cases values rowValues) body]
          simpa only [substitutedObjects_underRow,
            substitutedRows_underRow] using witness
end

/-! ## Instantiation equations used by native quantifier rules -/

@[simp] theorem substitutedObjects_replaceObject
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (value : Term Symbol Literal ordinary rows) :
    substitutedObjects model (Substitution.replaceObject value)
        objects rowValues =
      Fin.cases (model.denoteTerm objects rowValues value) objects := by
  funext index
  refine Fin.cases ?_ (fun previous => ?_) index <;> rfl

@[simp] theorem substitutedRows_replaceObject
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (value : Term Symbol Literal ordinary rows) :
    substitutedRows model (Substitution.replaceObject value)
        objects rowValues = rowValues := by
  funext index
  change rowValues index ++ [] = rowValues index
  exact List.append_nil _

@[simp] theorem substitutedObjects_replaceRow
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (arguments : Spine Symbol Literal ordinary rows) :
    substitutedObjects model (Substitution.replaceRow arguments)
        objects rowValues = objects := by
  funext index
  rfl

@[simp] theorem substitutedRows_replaceRow
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (arguments : Spine Symbol Literal ordinary rows) :
    substitutedRows model (Substitution.replaceRow arguments)
        objects rowValues =
      Fin.cases (model.denoteSpine objects rowValues arguments) rowValues := by
  funext index
  refine Fin.cases ?_ (fun previous => ?_) index
  · rfl
  · change rowValues previous ++ [] = rowValues previous
    exact List.append_nil _

theorem satisfies_instantiateObject
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (value : Term Symbol Literal ordinary rows)
    (body : Formula Symbol Literal (ordinary + 1) rows)
    (world : model.World) :
    model.satisfies objects rowValues
        (Substitution.instantiateObjectFormula value body) world <->
      model.satisfies
        (Fin.cases (model.denoteTerm objects rowValues value) objects)
        rowValues body world := by
  have naturality := congrFun
    (denote_substitute_formula model (Substitution.replaceObject value)
      objects rowValues body) world
  change model.denoteFormulaLifted objects rowValues
      (Substitution.formula (Substitution.replaceObject value) body) world <->
    model.denoteFormulaLifted
      (Fin.cases (model.denoteTerm objects rowValues value) objects)
      rowValues body world
  rw [naturality, substitutedObjects_replaceObject,
    substitutedRows_replaceObject]

theorem satisfies_instantiateRow
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (arguments : Spine Symbol Literal ordinary rows)
    (body : Formula Symbol Literal ordinary (rows + 1))
    (world : model.World) :
    model.satisfies objects rowValues
        (Substitution.instantiateRowFormula arguments body) world <->
      model.satisfies objects
        (Fin.cases (model.denoteSpine objects rowValues arguments) rowValues)
        body world := by
  have naturality := congrFun
    (denote_substitute_formula model (Substitution.replaceRow arguments)
      objects rowValues body) world
  change model.denoteFormulaLifted objects rowValues
      (Substitution.formula (Substitution.replaceRow arguments) body) world <->
    model.denoteFormulaLifted objects
      (Fin.cases (model.denoteSpine objects rowValues arguments) rowValues)
      body world
  rw [naturality, substitutedObjects_replaceRow, substitutedRows_replaceRow]

/-! ## Weakening equations used by native binder rules -/

/-- Adding a fresh ordinary value does not change a formula that has been
weakened past that value. -/
theorem satisfies_weakenObject
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (fresh : model.Carrier)
    (body : Formula Symbol Literal ordinary rows)
    (world : model.World) :
    model.satisfies (Fin.cases fresh objects) rowValues
        (Renaming.weakenObjectFormula body) world <->
      model.satisfies objects rowValues body world := by
  have objectEnvironment :
      renameObjects (Fin.cases fresh objects) Fin.succ = objects := by
    funext index
    rfl
  have rowEnvironment :
      renameRows rowValues (fun index => index) = rowValues := by
    funext index
    rfl
  have naturality := congrFun
    (denote_rename_formula model Fin.succ (fun index => index)
      (Fin.cases fresh objects) rowValues body) world
  rw [objectEnvironment, rowEnvironment] at naturality
  exact Iff.of_eq naturality

/-- Adding a fresh exact row does not change a formula that has been weakened
past that row. -/
theorem satisfies_weakenRow
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (fresh : List model.Carrier)
    (body : Formula Symbol Literal ordinary rows)
    (world : model.World) :
    model.satisfies objects (Fin.cases fresh rowValues)
        (Renaming.weakenRowFormula body) world <->
      model.satisfies objects rowValues body world := by
  have objectEnvironment :
      renameObjects objects (fun index => index) = objects := by
    funext index
    rfl
  have rowEnvironment :
      renameRows (Fin.cases fresh rowValues) Fin.succ = rowValues := by
    funext index
    rfl
  have naturality := congrFun
    (denote_rename_formula model (fun index => index) Fin.succ
      objects (Fin.cases fresh rowValues) body) world
  rw [objectEnvironment, rowEnvironment] at naturality
  exact Iff.of_eq naturality

end Model

end Mettapedia.Languages.SUMO.Native
