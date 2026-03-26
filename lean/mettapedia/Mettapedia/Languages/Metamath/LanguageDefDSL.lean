import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.Languages.Metamath.MMLean4Bridge

/-!
# Metamath in `languageDef!` Form (Grounded, Non-Opaque)

This is the Lean twin of `mettail-rust/languages/src/metamath.rs`, authored in
the unified DSL and intended to stay grounded to `mm-lean4` bridge semantics.
-/

namespace Mettapedia.Languages.Metamath.LanguageDefDSL

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.Languages.Metamath.MMLean4Bridge
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

private def hasSubstring (needle haystack : String) : Bool :=
  haystack.contains needle

def metamathCore : LanguageDef :=
  languageDef! {
    name : "Metamath"
    types {
      Database
      Stmt
      MathString
      ProofString
      ProofRefs
      ProofBlock
      ProofOpen
      ProofClose
      FrontDb
      FrontStmt
      FrontEnv
      FrontEntry
      FrontEntries
      CoreProg
      CoreStmt
      LowerState
      LowerKont
      LoadEnvState
      LoadEnvKont
      LinearizeState
      LinearizeKont
      CompileState
      ![label] as Label
      ![raw] as Sym
      ![proofTok] as ProofTok
      ![path] as IncludePath
    }
    terms {
      DbMore . stmt:Stmt, rest:Database |- stmt rest : Database;
      DbOne . stmt:Stmt |- stmt : Database;

      Block . body:Database |- "${" body "$}" : Stmt;
      ConstDecl . syms:MathString |- "$c" syms "$." : Stmt;
      VarDecl . syms:MathString |- "$v" syms "$." : Stmt;
      DjDecl . syms:MathString |- "$d" syms "$." : Stmt;
      IncludeDecl . path:IncludePath |- "$[" path "$]" : Stmt;

      FloatDecl . label:Label, typecode:Sym, var:Sym
        |- label "$f" typecode var "$." : Stmt;

      EssHyp . label:Label, math:MathString
        |- label "$e" math "$." : Stmt;

      Axiom . label:Label, math:MathString
        |- label "$a" math "$." : Stmt;

      Provable . label:Label, math:MathString, proof:ProofString
        |- label "$p" math "$=" proof "$." : Stmt;

      MathMore . head:Sym, tail:MathString |- head tail : MathString;
      MathOne . head:Sym |- head : MathString;

      ProofUncompressed . refs:ProofRefs |- refs : ProofString;
      ProofCompressed . openTok:ProofOpen, refs:ProofRefs, closeTok:ProofClose, block:ProofBlock
        |- openTok refs closeTok block : ProofString;

      ProofOpenTok . |- "(" : ProofOpen;
      ProofCloseTok . |- ")" : ProofClose;

      ProofRefsMore . head:ProofTok, tail:ProofRefs |- head tail : ProofRefs;
      ProofRefsOne . head:ProofTok |- head : ProofRefs;

      ProofBlockMore . head:ProofTok, tail:ProofBlock |- head tail : ProofBlock;
      ProofBlockOne . head:ProofTok |- head : ProofBlock;

      FrontDbMore . stmt:FrontStmt, rest:FrontDb
        |- "FrontDbMore" "(" stmt "," rest ")" : FrontDb;
      FrontDbOne . stmt:FrontStmt
        |- "FrontDbOne" "(" stmt ")" : FrontDb;

      FrontBlock . body:FrontDb
        |- "FrontBlock" "(" body ")" : FrontStmt;
      FrontConstDecl . syms:MathString
        |- "FrontConstDecl" "(" syms ")" : FrontStmt;
      FrontVarDecl . syms:MathString
        |- "FrontVarDecl" "(" syms ")" : FrontStmt;
      FrontDjDecl . syms:MathString
        |- "FrontDjDecl" "(" syms ")" : FrontStmt;
      FrontIncludeDecl . path:IncludePath
        |- "FrontIncludeDecl" "(" path ")" : FrontStmt;
      FrontFloatDecl . label:Label, typecode:Sym, var:Sym
        |- "FrontFloatDecl" "(" label "," typecode "," var ")" : FrontStmt;
      FrontEssHyp . label:Label, math:MathString
        |- "FrontEssHyp" "(" label "," math ")" : FrontStmt;
      FrontAxiom . label:Label, math:MathString
        |- "FrontAxiom" "(" label "," math ")" : FrontStmt;
      FrontProvable . label:Label, math:MathString, proof:ProofString
        |- "FrontProvable" "(" label "," math "," proof ")" : FrontStmt;

      FrontEntriesMore . head:FrontEntry, tail:FrontEntries
        |- "FrontEntriesMore" "(" head "," tail ")" : FrontEntries;
      FrontEntriesOne . head:FrontEntry
        |- "FrontEntriesOne" "(" head ")" : FrontEntries;

      FrontEnvNode . entries:FrontEntries
        |- "FrontEnvNode" "(" entries ")" : FrontEnv;

      FrontEntryBlock . env:FrontEnv
        |- "FrontEntryBlock" "(" env ")" : FrontEntry;
      FrontEntryConstDecl . syms:MathString
        |- "FrontEntryConstDecl" "(" syms ")" : FrontEntry;
      FrontEntryVarDecl . syms:MathString
        |- "FrontEntryVarDecl" "(" syms ")" : FrontEntry;
      FrontEntryDjDecl . syms:MathString
        |- "FrontEntryDjDecl" "(" syms ")" : FrontEntry;
      FrontEntryIncludeDecl . path:IncludePath
        |- "FrontEntryIncludeDecl" "(" path ")" : FrontEntry;
      FrontEntryFloatDecl . label:Label, typecode:Sym, var:Sym
        |- "FrontEntryFloatDecl" "(" label "," typecode "," var ")" : FrontEntry;
      FrontEntryEssHyp . label:Label, math:MathString
        |- "FrontEntryEssHyp" "(" label "," math ")" : FrontEntry;
      FrontEntryAxiom . label:Label, math:MathString
        |- "FrontEntryAxiom" "(" label "," math ")" : FrontEntry;
      FrontEntryProvable . label:Label, math:MathString, proof:ProofString
        |- "FrontEntryProvable" "(" label "," math "," proof ")" : FrontEntry;

      CoreProgOne . stmt:CoreStmt
        |- "CoreProgOne" "(" stmt ")" : CoreProg;
      CoreProgCat . left:CoreProg, right:CoreProg
        |- "CoreProgCat" "(" left "," right ")" : CoreProg;

      CoreEnterScope . |- "CoreEnterScope" : CoreStmt;
      CoreExitScope . |- "CoreExitScope" : CoreStmt;
      CoreConstDecl . syms:MathString
        |- "CoreConstDecl" "(" syms ")" : CoreStmt;
      CoreVarDecl . syms:MathString
        |- "CoreVarDecl" "(" syms ")" : CoreStmt;
      CoreDjDecl . syms:MathString
        |- "CoreDjDecl" "(" syms ")" : CoreStmt;
      CoreIncludeDecl . path:IncludePath
        |- "CoreIncludeDecl" "(" path ")" : CoreStmt;
      CoreFloatDecl . label:Label, typecode:Sym, var:Sym
        |- "CoreFloatDecl" "(" label "," typecode "," var ")" : CoreStmt;
      CoreEssHyp . label:Label, math:MathString
        |- "CoreEssHyp" "(" label "," math ")" : CoreStmt;
      CoreAxiom . label:Label, math:MathString
        |- "CoreAxiom" "(" label "," math ")" : CoreStmt;
      CoreProvable . label:Label, math:MathString, proof:ProofString
        |- "CoreProvable" "(" label "," math "," proof ")" : CoreStmt;

      Lower . db:Database |- "Lower" "(" db ")" : LowerState;
      LowerDb . db:Database, kont:LowerKont
        |- "LowerDb" "(" db "," kont ")" : LowerState;
      LowerStmt . stmt:Stmt, kont:LowerKont
        |- "LowerStmt" "(" stmt "," kont ")" : LowerState;
      ReturnDb . db:FrontDb, kont:LowerKont
        |- "ReturnDb" "(" db "," kont ")" : LowerState;
      ReturnStmt . stmt:FrontStmt, kont:LowerKont
        |- "ReturnStmt" "(" stmt "," kont ")" : LowerState;
      LowerDone . db:FrontDb
        |- "LowerDone" "(" db ")" : LowerState;

      KDone . |- "KDone" : LowerKont;
      KDbLast . kont:LowerKont
        |- "KDbLast" "(" kont ")" : LowerKont;
      KDbMore . rest:Database, kont:LowerKont
        |- "KDbMore" "(" rest "," kont ")" : LowerKont;
      KDbCons . head:FrontStmt, kont:LowerKont
        |- "KDbCons" "(" head "," kont ")" : LowerKont;
      KWrapBlock . kont:LowerKont
        |- "KWrapBlock" "(" kont ")" : LowerKont;

      LoadEnv . db:FrontDb |- "LoadEnv" "(" db ")" : LoadEnvState;
      LoadEnvDb . db:FrontDb, kont:LoadEnvKont
        |- "LoadEnvDb" "(" db "," kont ")" : LoadEnvState;
      LoadEnvStmt . stmt:FrontStmt, kont:LoadEnvKont
        |- "LoadEnvStmt" "(" stmt "," kont ")" : LoadEnvState;
      ReturnEnvDb . entries:FrontEntries, kont:LoadEnvKont
        |- "ReturnEnvDb" "(" entries "," kont ")" : LoadEnvState;
      ReturnEnvStmt . entry:FrontEntry, kont:LoadEnvKont
        |- "ReturnEnvStmt" "(" entry "," kont ")" : LoadEnvState;
      LoadEnvDone . env:FrontEnv
        |- "LoadEnvDone" "(" env ")" : LoadEnvState;

      EnvKDone . |- "EnvKDone" : LoadEnvKont;
      EnvKDbLast . kont:LoadEnvKont
        |- "EnvKDbLast" "(" kont ")" : LoadEnvKont;
      EnvKDbMore . rest:FrontDb, kont:LoadEnvKont
        |- "EnvKDbMore" "(" rest "," kont ")" : LoadEnvKont;
      EnvKDbCons . head:FrontEntry, kont:LoadEnvKont
        |- "EnvKDbCons" "(" head "," kont ")" : LoadEnvKont;
      EnvKWrapBlock . kont:LoadEnvKont
        |- "EnvKWrapBlock" "(" kont ")" : LoadEnvKont;

      Linearize . env:FrontEnv |- "Linearize" "(" env ")" : LinearizeState;
      LinearizeEntries . entries:FrontEntries, kont:LinearizeKont
        |- "LinearizeEntries" "(" entries "," kont ")" : LinearizeState;
      LinearizeEntry . entry:FrontEntry, kont:LinearizeKont
        |- "LinearizeEntry" "(" entry "," kont ")" : LinearizeState;
      ReturnCore . prog:CoreProg, kont:LinearizeKont
        |- "ReturnCore" "(" prog "," kont ")" : LinearizeState;
      LinearizeDone . prog:CoreProg
        |- "LinearizeDone" "(" prog ")" : LinearizeState;

      LinKDone . |- "LinKDone" : LinearizeKont;
      LinKEntriesMore . tail:FrontEntries, kont:LinearizeKont
        |- "LinKEntriesMore" "(" tail "," kont ")" : LinearizeKont;
      LinKCat . head:CoreProg, kont:LinearizeKont
        |- "LinKCat" "(" head "," kont ")" : LinearizeKont;
      LinKWrapBlock . kont:LinearizeKont
        |- "LinKWrapBlock" "(" kont ")" : LinearizeKont;

      Compile . db:Database
        |- "Compile" "(" db ")" : CompileState;
      CompileAfterLower . lower:LowerState
        |- "CompileAfterLower" "(" lower ")" : CompileState;
      CompileAfterEnv . envload:LoadEnvState
        |- "CompileAfterEnv" "(" envload ")" : CompileState;
      CompileAfterLinearize . lin:LinearizeState
        |- "CompileAfterLinearize" "(" lin ")" : CompileState;
      CompileDone . prog:CoreProg
        |- "CompileDone" "(" prog ")" : CompileState;
    }
    equations { }
    rewrites {
      BeginLower . |- (Lower db) ~> (LowerDb db KDone);

      LowerDbOne . |- (LowerDb (DbOne stmt) kont) ~> (LowerStmt stmt (KDbLast kont));
      LowerDbMore . |- (LowerDb (DbMore stmt rest) kont) ~> (LowerStmt stmt (KDbMore rest kont));

      LowerBlock . |- (LowerStmt (Block body) kont) ~> (LowerDb body (KWrapBlock kont));
      LowerConstDecl . |- (LowerStmt (ConstDecl syms) kont) ~> (ReturnStmt (FrontConstDecl syms) kont);
      LowerVarDecl . |- (LowerStmt (VarDecl syms) kont) ~> (ReturnStmt (FrontVarDecl syms) kont);
      LowerDjDecl . |- (LowerStmt (DjDecl syms) kont) ~> (ReturnStmt (FrontDjDecl syms) kont);
      LowerIncludeDecl . |- (LowerStmt (IncludeDecl path) kont) ~> (ReturnStmt (FrontIncludeDecl path) kont);
      LowerFloatDecl . |- (LowerStmt (FloatDecl label typecode var) kont) ~> (ReturnStmt (FrontFloatDecl label typecode var) kont);
      LowerEssHyp . |- (LowerStmt (EssHyp label math) kont) ~> (ReturnStmt (FrontEssHyp label math) kont);
      LowerAxiom . |- (LowerStmt (Axiom label math) kont) ~> (ReturnStmt (FrontAxiom label math) kont);
      LowerProvable . |- (LowerStmt (Provable label math proof) kont) ~> (ReturnStmt (FrontProvable label math proof) kont);

      ReturnDbDone . |- (ReturnDb db KDone) ~> (LowerDone db);
      ReturnStmtDbLast . |- (ReturnStmt stmt (KDbLast kont)) ~> (ReturnDb (FrontDbOne stmt) kont);
      ReturnStmtDbMore . |- (ReturnStmt stmt (KDbMore rest kont)) ~> (LowerDb rest (KDbCons stmt kont));
      ReturnDbCons . |- (ReturnDb db (KDbCons stmt kont)) ~> (ReturnDb (FrontDbMore stmt db) kont);
      ReturnDbWrapBlock . |- (ReturnDb body (KWrapBlock kont)) ~> (ReturnStmt (FrontBlock body) kont);

      BeginLoadEnv . |- (LoadEnv db) ~> (LoadEnvDb db EnvKDone);

      LoadEnvDbOne . |- (LoadEnvDb (FrontDbOne stmt) kont) ~> (LoadEnvStmt stmt (EnvKDbLast kont));
      LoadEnvDbMore . |- (LoadEnvDb (FrontDbMore stmt rest) kont) ~> (LoadEnvStmt stmt (EnvKDbMore rest kont));

      LoadEnvFrontBlock . |- (LoadEnvStmt (FrontBlock body) kont) ~> (LoadEnvDb body (EnvKWrapBlock kont));
      LoadEnvFrontConstDecl . |- (LoadEnvStmt (FrontConstDecl syms) kont) ~> (ReturnEnvStmt (FrontEntryConstDecl syms) kont);
      LoadEnvFrontVarDecl . |- (LoadEnvStmt (FrontVarDecl syms) kont) ~> (ReturnEnvStmt (FrontEntryVarDecl syms) kont);
      LoadEnvFrontDjDecl . |- (LoadEnvStmt (FrontDjDecl syms) kont) ~> (ReturnEnvStmt (FrontEntryDjDecl syms) kont);
      LoadEnvFrontIncludeDecl . |- (LoadEnvStmt (FrontIncludeDecl path) kont) ~> (ReturnEnvStmt (FrontEntryIncludeDecl path) kont);
      LoadEnvFrontFloatDecl . |- (LoadEnvStmt (FrontFloatDecl label typecode var) kont) ~> (ReturnEnvStmt (FrontEntryFloatDecl label typecode var) kont);
      LoadEnvFrontEssHyp . |- (LoadEnvStmt (FrontEssHyp label math) kont) ~> (ReturnEnvStmt (FrontEntryEssHyp label math) kont);
      LoadEnvFrontAxiom . |- (LoadEnvStmt (FrontAxiom label math) kont) ~> (ReturnEnvStmt (FrontEntryAxiom label math) kont);
      LoadEnvFrontProvable . |- (LoadEnvStmt (FrontProvable label math proof) kont) ~> (ReturnEnvStmt (FrontEntryProvable label math proof) kont);

      ReturnEnvDbDone . |- (ReturnEnvDb entries EnvKDone) ~> (LoadEnvDone (FrontEnvNode entries));
      ReturnEnvStmtDbLast . |- (ReturnEnvStmt entry (EnvKDbLast kont)) ~> (ReturnEnvDb (FrontEntriesOne entry) kont);
      ReturnEnvStmtDbMore . |- (ReturnEnvStmt entry (EnvKDbMore rest kont)) ~> (LoadEnvDb rest (EnvKDbCons entry kont));
      ReturnEnvDbCons . |- (ReturnEnvDb entries (EnvKDbCons entry kont)) ~> (ReturnEnvDb (FrontEntriesMore entry entries) kont);
      ReturnEnvDbWrapBlock . |- (ReturnEnvDb entries (EnvKWrapBlock kont)) ~> (ReturnEnvStmt (FrontEntryBlock (FrontEnvNode entries)) kont);

      BeginLinearize . |- (Linearize (FrontEnvNode entries)) ~> (LinearizeEntries entries LinKDone);

      LinearizeEntriesOne . |- (LinearizeEntries (FrontEntriesOne entry) kont) ~> (LinearizeEntry entry kont);
      LinearizeEntriesMore . |- (LinearizeEntries (FrontEntriesMore entry tail) kont) ~> (LinearizeEntry entry (LinKEntriesMore tail kont));

      LinearizeFrontEntryBlock . |- (LinearizeEntry (FrontEntryBlock (FrontEnvNode entries)) kont) ~> (LinearizeEntries entries (LinKWrapBlock kont));
      LinearizeFrontEntryConstDecl . |- (LinearizeEntry (FrontEntryConstDecl syms) kont) ~> (ReturnCore (CoreProgOne (CoreConstDecl syms)) kont);
      LinearizeFrontEntryVarDecl . |- (LinearizeEntry (FrontEntryVarDecl syms) kont) ~> (ReturnCore (CoreProgOne (CoreVarDecl syms)) kont);
      LinearizeFrontEntryDjDecl . |- (LinearizeEntry (FrontEntryDjDecl syms) kont) ~> (ReturnCore (CoreProgOne (CoreDjDecl syms)) kont);
      LinearizeFrontEntryIncludeDecl . |- (LinearizeEntry (FrontEntryIncludeDecl path) kont) ~> (ReturnCore (CoreProgOne (CoreIncludeDecl path)) kont);
      LinearizeFrontEntryFloatDecl . |- (LinearizeEntry (FrontEntryFloatDecl label typecode var) kont) ~> (ReturnCore (CoreProgOne (CoreFloatDecl label typecode var)) kont);
      LinearizeFrontEntryEssHyp . |- (LinearizeEntry (FrontEntryEssHyp label math) kont) ~> (ReturnCore (CoreProgOne (CoreEssHyp label math)) kont);
      LinearizeFrontEntryAxiom . |- (LinearizeEntry (FrontEntryAxiom label math) kont) ~> (ReturnCore (CoreProgOne (CoreAxiom label math)) kont);
      LinearizeFrontEntryProvable . |- (LinearizeEntry (FrontEntryProvable label math proof) kont) ~> (ReturnCore (CoreProgOne (CoreProvable label math proof)) kont);

      ReturnCoreDone . |- (ReturnCore prog LinKDone) ~> (LinearizeDone prog);
      ReturnCoreEntriesMore . |- (ReturnCore prog (LinKEntriesMore tail kont)) ~> (LinearizeEntries tail (LinKCat prog kont));
      ReturnCoreCat . |- (ReturnCore tailProg (LinKCat headProg kont)) ~> (ReturnCore (CoreProgCat headProg tailProg) kont);
      ReturnCoreWrapBlock . |- (ReturnCore bodyProg (LinKWrapBlock kont)) ~> (ReturnCore (CoreProgCat (CoreProgOne CoreEnterScope) (CoreProgCat bodyProg (CoreProgOne CoreExitScope))) kont);

      BeginCompile . |- (Compile db) ~> (CompileAfterLower (Lower db));

      CompileLowerBegin . |- (CompileAfterLower (Lower db)) ~> (CompileAfterLower (LowerDb db KDone));
      CompileLowerDbOneWithCons . |- (CompileAfterLower (LowerDb (DbOne cdb1c_stmt) (KDbCons cdb1c_head cdb1c_kont)))
        ~> (CompileAfterLower (LowerStmt cdb1c_stmt (KDbLast (KDbCons cdb1c_head cdb1c_kont))));
      CompileLowerDbOne . |- (CompileAfterLower (LowerDb (DbOne cdb1_stmt) cdb1_kont)) ~> (CompileAfterLower (LowerStmt cdb1_stmt (KDbLast cdb1_kont)));
      CompileLowerDbMore . |- (CompileAfterLower (LowerDb (DbMore stmt rest) kont)) ~> (CompileAfterLower (LowerStmt stmt (KDbMore rest kont)));

      CompileLowerBlock . |- (CompileAfterLower (LowerStmt (Block body) kont)) ~> (CompileAfterLower (LowerDb body (KWrapBlock kont)));
      CompileLowerConstDecl . |- (CompileAfterLower (LowerStmt (ConstDecl syms) kont)) ~> (CompileAfterLower (ReturnStmt (FrontConstDecl syms) kont));
      CompileLowerVarDecl . |- (CompileAfterLower (LowerStmt (VarDecl syms) kont)) ~> (CompileAfterLower (ReturnStmt (FrontVarDecl syms) kont));
      CompileLowerDjDecl . |- (CompileAfterLower (LowerStmt (DjDecl syms) kont)) ~> (CompileAfterLower (ReturnStmt (FrontDjDecl syms) kont));
      CompileLowerIncludeDecl . |- (CompileAfterLower (LowerStmt (IncludeDecl path) kont)) ~> (CompileAfterLower (ReturnStmt (FrontIncludeDecl path) kont));
      CompileLowerFloatDecl . |- (CompileAfterLower (LowerStmt (FloatDecl label typecode var) kont)) ~> (CompileAfterLower (ReturnStmt (FrontFloatDecl label typecode var) kont));
      CompileLowerEssHyp . |- (CompileAfterLower (LowerStmt (EssHyp label math) kont)) ~> (CompileAfterLower (ReturnStmt (FrontEssHyp label math) kont));
      CompileLowerAxiom . |- (CompileAfterLower (LowerStmt (Axiom label math) kont)) ~> (CompileAfterLower (ReturnStmt (FrontAxiom label math) kont));
      CompileLowerProvable . |- (CompileAfterLower (LowerStmt (Provable label math proof) kont)) ~> (CompileAfterLower (ReturnStmt (FrontProvable label math proof) kont));

      CompileReturnDbDone . |- (CompileAfterLower (ReturnDb db KDone)) ~> (CompileAfterLower (LowerDone db));
      CompileReturnStmtDbLast . |- (CompileAfterLower (ReturnStmt stmt (KDbLast kont))) ~> (CompileAfterLower (ReturnDb (FrontDbOne stmt) kont));
      CompileReturnStmtDbMore . |- (CompileAfterLower (ReturnStmt stmt (KDbMore rest kont))) ~> (CompileAfterLower (LowerDb rest (KDbCons stmt kont)));
      CompileReturnDbCons . |- (CompileAfterLower (ReturnDb db (KDbCons stmt kont))) ~> (CompileAfterLower (ReturnDb (FrontDbMore stmt db) kont));
      CompileReturnDbWrapBlock . |- (CompileAfterLower (ReturnDb body (KWrapBlock kont))) ~> (CompileAfterLower (ReturnStmt (FrontBlock body) kont));

      CompileLowerDone . |- (CompileAfterLower (LowerDone fdb)) ~> (CompileAfterEnv (LoadEnv fdb));
      CompileEnvBegin . |- (CompileAfterEnv (LoadEnv db)) ~> (CompileAfterEnv (LoadEnvDb db EnvKDone));

      CompileLoadEnvDbOne . |- (CompileAfterEnv (LoadEnvDb (FrontDbOne stmt) kont)) ~> (CompileAfterEnv (LoadEnvStmt stmt (EnvKDbLast kont)));
      CompileLoadEnvDbMore . |- (CompileAfterEnv (LoadEnvDb (FrontDbMore stmt rest) kont)) ~> (CompileAfterEnv (LoadEnvStmt stmt (EnvKDbMore rest kont)));

      CompileLoadEnvFrontBlock . |- (CompileAfterEnv (LoadEnvStmt (FrontBlock body) kont)) ~> (CompileAfterEnv (LoadEnvDb body (EnvKWrapBlock kont)));
      CompileLoadEnvFrontConstDecl . |- (CompileAfterEnv (LoadEnvStmt (FrontConstDecl syms) kont)) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryConstDecl syms) kont));
      CompileLoadEnvFrontVarDecl . |- (CompileAfterEnv (LoadEnvStmt (FrontVarDecl syms) kont)) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryVarDecl syms) kont));
      CompileLoadEnvFrontDjDecl . |- (CompileAfterEnv (LoadEnvStmt (FrontDjDecl syms) kont)) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryDjDecl syms) kont));
      CompileLoadEnvFrontIncludeDecl . |- (CompileAfterEnv (LoadEnvStmt (FrontIncludeDecl path) kont)) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryIncludeDecl path) kont));
      CompileLoadEnvFrontFloatDecl . |- (CompileAfterEnv (LoadEnvStmt (FrontFloatDecl label typecode var) kont)) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryFloatDecl label typecode var) kont));
      CompileLoadEnvFrontEssHyp . |- (CompileAfterEnv (LoadEnvStmt (FrontEssHyp label math) kont)) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryEssHyp label math) kont));
      CompileLoadEnvFrontAxiom . |- (CompileAfterEnv (LoadEnvStmt (FrontAxiom label math) kont)) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryAxiom label math) kont));
      CompileLoadEnvFrontProvable . |- (CompileAfterEnv (LoadEnvStmt (FrontProvable label math proof) kont)) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryProvable label math proof) kont));

      CompileReturnEnvDbDone . |- (CompileAfterEnv (ReturnEnvDb entries EnvKDone)) ~> (CompileAfterEnv (LoadEnvDone (FrontEnvNode entries)));
      CompileReturnEnvStmtDbLast . |- (CompileAfterEnv (ReturnEnvStmt entry (EnvKDbLast kont))) ~> (CompileAfterEnv (ReturnEnvDb (FrontEntriesOne entry) kont));
      CompileReturnEnvStmtDbMore . |- (CompileAfterEnv (ReturnEnvStmt entry (EnvKDbMore rest kont))) ~> (CompileAfterEnv (LoadEnvDb rest (EnvKDbCons entry kont)));
      CompileReturnEnvDbCons . |- (CompileAfterEnv (ReturnEnvDb entries (EnvKDbCons entry kont))) ~> (CompileAfterEnv (ReturnEnvDb (FrontEntriesMore entry entries) kont));
      CompileReturnEnvDbWrapBlock . |- (CompileAfterEnv (ReturnEnvDb entries (EnvKWrapBlock kont))) ~> (CompileAfterEnv (ReturnEnvStmt (FrontEntryBlock (FrontEnvNode entries)) kont));

      CompileEnvDone . |- (CompileAfterEnv (LoadEnvDone env)) ~> (CompileAfterLinearize (Linearize env));
      CompileLinearizeBegin . |- (CompileAfterLinearize (Linearize (FrontEnvNode entries))) ~> (CompileAfterLinearize (LinearizeEntries entries LinKDone));

      CompileLinearizeEntriesOne . |- (CompileAfterLinearize (LinearizeEntries (FrontEntriesOne entry) kont)) ~> (CompileAfterLinearize (LinearizeEntry entry kont));
      CompileLinearizeEntriesMore . |- (CompileAfterLinearize (LinearizeEntries (FrontEntriesMore entry tail) kont)) ~> (CompileAfterLinearize (LinearizeEntry entry (LinKEntriesMore tail kont)));

      CompileLinearizeFrontEntryBlock . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryBlock (FrontEnvNode entries)) kont)) ~> (CompileAfterLinearize (LinearizeEntries entries (LinKWrapBlock kont)));
      CompileLinearizeFrontEntryConstDecl . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryConstDecl syms) kont)) ~> (CompileAfterLinearize (ReturnCore (CoreProgOne (CoreConstDecl syms)) kont));
      CompileLinearizeFrontEntryVarDecl . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryVarDecl syms) kont)) ~> (CompileAfterLinearize (ReturnCore (CoreProgOne (CoreVarDecl syms)) kont));
      CompileLinearizeFrontEntryDjDecl . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryDjDecl syms) kont)) ~> (CompileAfterLinearize (ReturnCore (CoreProgOne (CoreDjDecl syms)) kont));
      CompileLinearizeFrontEntryIncludeDecl . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryIncludeDecl path) kont)) ~> (CompileAfterLinearize (ReturnCore (CoreProgOne (CoreIncludeDecl path)) kont));
      CompileLinearizeFrontEntryFloatDecl . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryFloatDecl label typecode var) kont)) ~> (CompileAfterLinearize (ReturnCore (CoreProgOne (CoreFloatDecl label typecode var)) kont));
      CompileLinearizeFrontEntryEssHyp . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryEssHyp label math) kont)) ~> (CompileAfterLinearize (ReturnCore (CoreProgOne (CoreEssHyp label math)) kont));
      CompileLinearizeFrontEntryAxiom . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryAxiom label math) kont)) ~> (CompileAfterLinearize (ReturnCore (CoreProgOne (CoreAxiom label math)) kont));
      CompileLinearizeFrontEntryProvable . |- (CompileAfterLinearize (LinearizeEntry (FrontEntryProvable label math proof) kont)) ~> (CompileAfterLinearize (ReturnCore (CoreProgOne (CoreProvable label math proof)) kont));

      CompileReturnCoreDone . |- (CompileAfterLinearize (ReturnCore prog LinKDone)) ~> (CompileAfterLinearize (LinearizeDone prog));
      CompileReturnCoreEntriesMore . |- (CompileAfterLinearize (ReturnCore prog (LinKEntriesMore tail kont))) ~> (CompileAfterLinearize (LinearizeEntries tail (LinKCat prog kont)));
      CompileReturnCoreCat . |- (CompileAfterLinearize (ReturnCore tailProg (LinKCat headProg kont))) ~> (CompileAfterLinearize (ReturnCore (CoreProgCat headProg tailProg) kont));
      CompileReturnCoreWrapBlock . |- (CompileAfterLinearize (ReturnCore bodyProg (LinKWrapBlock kont))) ~> (CompileAfterLinearize (ReturnCore (CoreProgCat (CoreProgOne CoreEnterScope) (CoreProgCat bodyProg (CoreProgOne CoreExitScope))) kont));

      CompileLinearizeDone . |- (CompileAfterLinearize (LinearizeDone prog)) ~> (CompileDone prog);
    }
    logic { }
    oracles { }
    congruenceCollections { }
  }

abbrev metamathLanguageDef : LanguageDef := metamathCore

def exportedRustSurface : String :=
  renderLanguageWithUserSyntax metamathCore

private def hasTypeCarrier (nm : String) (carrier : CarrierKind) : Bool :=
  metamathCore.types.any (fun t => t.name == nm && t.carrier = carrier)

def bridgeKeyOfTypeName : String → Option CarrierKey
  | "Label" => some .label
  | "Sym" => some .specSym
  | "ProofTok" => some .proofTok
  | "IncludePath" => some .includePath
  | _ => none

example : LanguageDef.validate metamathCore = [] := by
  native_decide

example : hasTypeCarrier "Label" .tokenLabel = true := by native_decide
example : hasTypeCarrier "Sym" .tokenRaw = true := by native_decide
example : hasTypeCarrier "ProofTok" .tokenProof = true := by native_decide
example : hasTypeCarrier "IncludePath" .tokenPath = true := by native_decide

example : bridgeKeyOfTypeName "Label" = some .label := rfl
example : bridgeKeyOfTypeName "Sym" = some .specSym := rfl
example : bridgeKeyOfTypeName "ProofTok" = some .proofTok := rfl
example : bridgeKeyOfTypeName "IncludePath" = some .includePath := rfl

example :
    hasSubstring "name: Metamath" exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "ConstDecl . syms:MathString |- \"$c\" syms \"$.\" : Stmt;" exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "BeginLower . |- (Lower db) ~> (LowerDb db KDone);" exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "CompileLinearizeDone . |- (CompileAfterLinearize (LinearizeDone prog)) ~> (CompileDone prog);" exportedRustSurface = true := by
  native_decide

example
    (rt : RuntimeState) (sp : SpecState)
    (h : RuntimeState.toSpecState? rt = some sp) :
    StateCorresponds rt sp := by
  exact RuntimeState.toSpecState?_sound rt sp h

end Mettapedia.Languages.Metamath.LanguageDefDSL
