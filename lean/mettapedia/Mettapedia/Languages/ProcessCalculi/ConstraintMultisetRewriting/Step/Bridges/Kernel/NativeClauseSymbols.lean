import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseReadback
import Mettapedia.Languages.HOLLight.ExportCodec

/-! Expected typed syntax of the native record case theorem. This data grants no admission: the complete table must pass NativeClauseReadback against the received cache. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeClauseData

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open NativeClauseReadback

structure Operations where
  o0 : TypeOp -- hupdate
  o1 : TypeOp -- list
  o2 : TypeOp -- char
  o3 : TypeOp -- num
  o4 : TypeOp -- prod
  o5 : TypeOp -- holr_record
  o6 : TypeOp -- holtype
  o7 : TypeOp -- option
  o8 : TypeOp -- hdbterm
  o9 : TypeOp -- holterm
  c0 : Const -- nat_step
  c1 : Const -- \/
  c2 : Const -- ?
  c3 : Const -- /\
  c4 : Const -- ,
  c5 : Const -- RName
  c6 : Const -- APPEND
  c7 : Const -- CONS
  c8 : Const -- NIL
  c9 : Const -- <
  c10 : Const -- LENGTH
  c11 : Const -- EL
  c12 : Const -- holr_name
  c13 : Const -- nat_new_names
  c14 : Const -- RTyVar
  c15 : Const -- nat_tys_ok
  c16 : Const -- nat_new_rows
  c17 : Const -- fdty
  c18 : Const -- TyVar
  c19 : Const -- RTyApp
  c20 : Const -- nat_ops_live
  c21 : Const -- hlookup
  c22 : Const -- htype_list
  c23 : Const -- SOME
  c24 : Const -- ALL2
  c25 : Const -- TyApp
  c26 : Const -- RVar
  c27 : Const -- NUMERAL
  c28 : Const -- _0
  c29 : Const -- fddb
  c30 : Const -- hdbVar
  c31 : Const -- RConst
  c32 : Const -- BIT1
  c33 : Const -- hconst_list
  c34 : Const -- HTYPE_SUBST
  c35 : Const -- hdbConst
  c36 : Const -- RComb
  c37 : Const -- BIT0
  c38 : Const -- fdtm
  c39 : Const -- htypeof
  c40 : Const -- HFun
  c41 : Const -- hdbComb
  c42 : Const -- hdb
  c43 : Const -- RAbs
  c44 : Const -- TmVar
  c45 : Const -- hdbAbs
  c46 : Const -- hbind
  c47 : Const -- RRefl
  c48 : Const -- fddbs
  c49 : Const -- =:=
  c50 : Const -- RTrans
  c51 : Const -- FST
  c52 : Const -- SND
  c53 : Const -- ASCII
  c54 : Const -- F
  c55 : Const -- T
  c56 : Const -- !
  c57 : Const -- ==>
  c58 : Const -- MEM
  c59 : Const -- RMkComb
  c60 : Const -- HBool
  c61 : Const -- RAbsRule
  c62 : Const -- ~
  c63 : Const -- hdbVFREE_IN
  c64 : Const -- RBeta
  c65 : Const -- TmComb
  c66 : Const -- TmAbs
  c67 : Const -- RAssume
  c68 : Const -- REqMp
  c69 : Const -- RDeduct
  c70 : Const -- RInstType
  c71 : Const -- hdbINST
  c72 : Const -- RInst
  c73 : Const -- hdbVSUBST
  c74 : Const -- MAP
  c75 : Const -- GABS
  c76 : Const -- GEQ
  c77 : Const -- RExpectAlpha
  c78 : Const -- ALL
  c79 : Const -- RLabel
  c80 : Const -- REmit
  c81 : Const -- RDropType
  c82 : Const -- RDropTerm
  c83 : Const -- RDropThm
  c84 : Const -- RPolicy
  c85 : Const -- MAX
  c86 : Const -- <=
  c87 : Const -- RNewType
  c88 : Const -- HNewType
  c89 : Const -- NONE
  c90 : Const -- RNewConstant
  c91 : Const -- HNewConst
  c92 : Const -- RNewAxiom
  c93 : Const -- HNewAxiom
  c94 : Const -- holr_axiom_ok
  c95 : Const -- RNewDefinition
  c96 : Const -- HConstSpec
  c97 : Const -- HCLOSED
  c98 : Const -- htvars
  c99 : Const -- htyvars
  c100 : Const -- TmConst
  c101 : Const -- RNewTypedef
  c102 : Const -- HTypeDefn
  c103 : Const -- hwelltyped
  c104 : Const -- hstring_sorted
  c105 : Const -- htydef_abs
  c106 : Const -- htydef_rep

def operations? (symbols : ExportCodec.Symbols) : Option Operations := do
  let o0 ← List.lookup "hupdate" symbols.operators
  let o1 ← List.lookup "list" symbols.operators
  let o2 ← List.lookup "char" symbols.operators
  let o3 ← List.lookup "num" symbols.operators
  let o4 ← List.lookup "prod" symbols.operators
  let o5 ← List.lookup "holr_record" symbols.operators
  let o6 ← List.lookup "holtype" symbols.operators
  let o7 ← List.lookup "option" symbols.operators
  let o8 ← List.lookup "hdbterm" symbols.operators
  let o9 ← List.lookup "holterm" symbols.operators
  let c0 ← List.lookup "nat_step" symbols.constants
  let c1 ← List.lookup "\\/" symbols.constants
  let c2 ← List.lookup "?" symbols.constants
  let c3 ← List.lookup "/\\" symbols.constants
  let c4 ← List.lookup "," symbols.constants
  let c5 ← List.lookup "RName" symbols.constants
  let c6 ← List.lookup "APPEND" symbols.constants
  let c7 ← List.lookup "CONS" symbols.constants
  let c8 ← List.lookup "NIL" symbols.constants
  let c9 ← List.lookup "<" symbols.constants
  let c10 ← List.lookup "LENGTH" symbols.constants
  let c11 ← List.lookup "EL" symbols.constants
  let c12 ← List.lookup "holr_name" symbols.constants
  let c13 ← List.lookup "nat_new_names" symbols.constants
  let c14 ← List.lookup "RTyVar" symbols.constants
  let c15 ← List.lookup "nat_tys_ok" symbols.constants
  let c16 ← List.lookup "nat_new_rows" symbols.constants
  let c17 ← List.lookup "fdty" symbols.constants
  let c18 ← List.lookup "TyVar" symbols.constants
  let c19 ← List.lookup "RTyApp" symbols.constants
  let c20 ← List.lookup "nat_ops_live" symbols.constants
  let c21 ← List.lookup "hlookup" symbols.constants
  let c22 ← List.lookup "htype_list" symbols.constants
  let c23 ← List.lookup "SOME" symbols.constants
  let c24 ← List.lookup "ALL2" symbols.constants
  let c25 ← List.lookup "TyApp" symbols.constants
  let c26 ← List.lookup "RVar" symbols.constants
  let c27 ← List.lookup "NUMERAL" symbols.constants
  let c28 ← List.lookup "_0" symbols.constants
  let c29 ← List.lookup "fddb" symbols.constants
  let c30 ← List.lookup "hdbVar" symbols.constants
  let c31 ← List.lookup "RConst" symbols.constants
  let c32 ← List.lookup "BIT1" symbols.constants
  let c33 ← List.lookup "hconst_list" symbols.constants
  let c34 ← List.lookup "HTYPE_SUBST" symbols.constants
  let c35 ← List.lookup "hdbConst" symbols.constants
  let c36 ← List.lookup "RComb" symbols.constants
  let c37 ← List.lookup "BIT0" symbols.constants
  let c38 ← List.lookup "fdtm" symbols.constants
  let c39 ← List.lookup "htypeof" symbols.constants
  let c40 ← List.lookup "HFun" symbols.constants
  let c41 ← List.lookup "hdbComb" symbols.constants
  let c42 ← List.lookup "hdb" symbols.constants
  let c43 ← List.lookup "RAbs" symbols.constants
  let c44 ← List.lookup "TmVar" symbols.constants
  let c45 ← List.lookup "hdbAbs" symbols.constants
  let c46 ← List.lookup "hbind" symbols.constants
  let c47 ← List.lookup "RRefl" symbols.constants
  let c48 ← List.lookup "fddbs" symbols.constants
  let c49 ← List.lookup "=:=" symbols.constants
  let c50 ← List.lookup "RTrans" symbols.constants
  let c51 ← List.lookup "FST" symbols.constants
  let c52 ← List.lookup "SND" symbols.constants
  let c53 ← List.lookup "ASCII" symbols.constants
  let c54 ← List.lookup "F" symbols.constants
  let c55 ← List.lookup "T" symbols.constants
  let c56 ← List.lookup "!" symbols.constants
  let c57 ← List.lookup "==>" symbols.constants
  let c58 ← List.lookup "MEM" symbols.constants
  let c59 ← List.lookup "RMkComb" symbols.constants
  let c60 ← List.lookup "HBool" symbols.constants
  let c61 ← List.lookup "RAbsRule" symbols.constants
  let c62 ← List.lookup "~" symbols.constants
  let c63 ← List.lookup "hdbVFREE_IN" symbols.constants
  let c64 ← List.lookup "RBeta" symbols.constants
  let c65 ← List.lookup "TmComb" symbols.constants
  let c66 ← List.lookup "TmAbs" symbols.constants
  let c67 ← List.lookup "RAssume" symbols.constants
  let c68 ← List.lookup "REqMp" symbols.constants
  let c69 ← List.lookup "RDeduct" symbols.constants
  let c70 ← List.lookup "RInstType" symbols.constants
  let c71 ← List.lookup "hdbINST" symbols.constants
  let c72 ← List.lookup "RInst" symbols.constants
  let c73 ← List.lookup "hdbVSUBST" symbols.constants
  let c74 ← List.lookup "MAP" symbols.constants
  let c75 ← List.lookup "GABS" symbols.constants
  let c76 ← List.lookup "GEQ" symbols.constants
  let c77 ← List.lookup "RExpectAlpha" symbols.constants
  let c78 ← List.lookup "ALL" symbols.constants
  let c79 ← List.lookup "RLabel" symbols.constants
  let c80 ← List.lookup "REmit" symbols.constants
  let c81 ← List.lookup "RDropType" symbols.constants
  let c82 ← List.lookup "RDropTerm" symbols.constants
  let c83 ← List.lookup "RDropThm" symbols.constants
  let c84 ← List.lookup "RPolicy" symbols.constants
  let c85 ← List.lookup "MAX" symbols.constants
  let c86 ← List.lookup "<=" symbols.constants
  let c87 ← List.lookup "RNewType" symbols.constants
  let c88 ← List.lookup "HNewType" symbols.constants
  let c89 ← List.lookup "NONE" symbols.constants
  let c90 ← List.lookup "RNewConstant" symbols.constants
  let c91 ← List.lookup "HNewConst" symbols.constants
  let c92 ← List.lookup "RNewAxiom" symbols.constants
  let c93 ← List.lookup "HNewAxiom" symbols.constants
  let c94 ← List.lookup "holr_axiom_ok" symbols.constants
  let c95 ← List.lookup "RNewDefinition" symbols.constants
  let c96 ← List.lookup "HConstSpec" symbols.constants
  let c97 ← List.lookup "HCLOSED" symbols.constants
  let c98 ← List.lookup "htvars" symbols.constants
  let c99 ← List.lookup "htyvars" symbols.constants
  let c100 ← List.lookup "TmConst" symbols.constants
  let c101 ← List.lookup "RNewTypedef" symbols.constants
  let c102 ← List.lookup "HTypeDefn" symbols.constants
  let c103 ← List.lookup "hwelltyped" symbols.constants
  let c104 ← List.lookup "hstring_sorted" symbols.constants
  let c105 ← List.lookup "htydef_abs" symbols.constants
  let c106 ← List.lookup "htydef_rep" symbols.constants
  return ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeClauseData
