module AST.AgdaSyntaxConcrete where
open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.String
open import AST.AgdaSyntaxAbstractName
open import AST.AgdaSyntaxCommon
open import AST.AgdaSyntaxFixity
open import AST.AgdaSyntaxLiteral
open import AST.AgdaSyntaxNotation
open import AST.AgdaSyntaxPosition
open import AST.AgdaTypeCheckingPositivityOccurrence
open import AST.DataEither
open import AST.DataSetInternal
open import AST.GHCIntegerType
mutual
  AsName :  Set
  AsName  = (AsNameP  (Either  Expr Name))
  
  data AsNameP ( a : Set ) : Set where
    AsNameC : a → Range → AsNameP a
  
  data BoundName : Set where
    BNameC : Name → Name → FixityP → BoundName 
  
  data Declaration : Set where
    TypeSigC : ArgInfo → Name → Expr → Declaration 
    GeneralizeC : Range → (List (TypeSignature)) → Declaration 
    FieldC : IsInstance → Name → (Arg  Expr) → Declaration 
    FunClauseC : LHS → RHS → WhereClause → Bool → Declaration 
    DataSigC : Range → Induction → Name → (List (LamBinding)) → Expr → Declaration 
    DataC : Range → Induction → Name → (List (LamBinding)) → (Maybe  Expr) → (List (TypeSignatureOrInstanceBlock)) → Declaration 
    RecordSigC : Range → Name → (List (LamBinding)) → Expr → Declaration 
    RecordC : Range → Name → (Maybe  (Ranged  Induction)) → (Maybe  HasEta) → (Maybe  (Name ×  IsInstance)) → (List (LamBinding)) → (Maybe  Expr) → (List (Declaration)) → Declaration 
    InfixC : Fixity → (List (Name)) → Declaration 
    SyntaxC : Name → Notation → Declaration 
    PatternSynC : Range → Name → (List ((Arg  Name))) → Pattern → Declaration 
    MutualC : Range → (List (Declaration)) → Declaration 
    AbstractC : Range → (List (Declaration)) → Declaration 
    PrivateC : Range → Origin → (List (Declaration)) → Declaration 
    InstanceBC : Range → (List (Declaration)) → Declaration 
    MacroC : Range → (List (Declaration)) → Declaration 
    PostulateC : Range → (List (TypeSignatureOrInstanceBlock)) → Declaration 
    PrimitiveC : Range → (List (TypeSignature)) → Declaration 
    OpenC : Range → QName → ImportDirective → Declaration 
    ImportC : Range → QName → (Maybe  AsName) → OpenShortHand → ImportDirective → Declaration 
    ModuleMacroC : Range → Name → ModuleApplication → OpenShortHand → ImportDirective → Declaration 
    ModuleC : Range → QName → (List (TypedBindings)) → (List (Declaration)) → Declaration 
    UnquoteDeclC : Range → (List (Name)) → Expr → Declaration 
    UnquoteDefC : Range → (List (Name)) → Expr → Declaration 
    PragmaC : Pragma → Declaration 
  
  data DoStmt : Set where
    DoBindC : Range → Pattern → Expr → (List (LamClause)) → DoStmt 
    DoThenC : Expr → DoStmt 
    DoLetC : Range → (List (Declaration)) → DoStmt 
  
  data Expr : Set where
    IdentC : QName → Expr 
    LitC : Literal → Expr 
    QuestionMarkC : Range → (Maybe  Nat) → Expr 
    UnderscoreC : Range → (Maybe  String) → Expr 
    RawAppC : Range → (List (Expr)) → Expr 
    AppC : Range → Expr → (NamedArg  Expr) → Expr 
    OpAppC : Range → QName → (SSet  Name) → (List ((NamedArg  (MaybePlaceholder  (OpApp  Expr))))) → Expr 
    WithAppC : Range → Expr → (List (Expr)) → Expr 
    HiddenArgC : Range → (NamedU  Expr) → Expr 
    InstanceArgC : Range → (NamedU  Expr) → Expr 
    LamC : Range → (List (LamBinding)) → Expr → Expr 
    AbsurdLamC : Range → Hiding → Expr 
    ExtendedLamC : Range → (List (LamClause)) → Expr 
    FunC : Range → (Arg  Expr) → Expr → Expr 
    PiC : Telescope → Expr → Expr 
    SetC : Range → Expr 
    PropC : Range → Expr 
    SetNC : Range → Integer → Expr 
    PropNC : Range → Integer → Expr 
    RecC : Range → RecordAssignments → Expr 
    RecUpdateC : Range → Expr → (List (FieldAssignment)) → Expr 
    LetC : Range → (List (Declaration)) → (Maybe  Expr) → Expr 
    ParenC : Range → Expr → Expr 
    IdiomBracketsC : Range → Expr → Expr 
    DoBlockC : Range → (List (DoStmt)) → Expr 
    AbsurdC : Range → Expr 
    AsC : Range → Name → Expr → Expr 
    DotC : Range → Expr → Expr 
    ETelC : Telescope → Expr 
    QuoteGoalC : Range → Name → Expr → Expr 
    QuoteContextC : Range → Expr 
    QuoteC : Range → Expr 
    QuoteTermC : Range → Expr 
    TacticC : Range → Expr → (List (Expr)) → Expr 
    UnquoteC : Range → Expr 
    DontCareC : Expr → Expr 
    EqualC : Range → Expr → Expr → Expr 
    EllipsisC : Range → Expr 
    GeneralizedC : Expr → Expr 
  
  FieldAssignment :  Set
  FieldAssignment  = (FieldAssignmentP  Expr)
  
  data FieldAssignmentP ( a : Set ) : Set where
    FieldAssignmentC : Name → a → FieldAssignmentP a
  
  ImportDirective :  Set
  ImportDirective  = (ImportDirectiveP  Name Name)
  
  data LHS : Set where
    LHSC : Pattern → (List (RewriteEqn)) → (List (WithExpr)) → LHS 
  
  LamBinding :  Set
  LamBinding  = (LamBindingP  TypedBindings)
  
  data LamBindingP ( a : Set ) : Set where
    DomainFreeC : ArgInfo → BoundName → LamBindingP a
    DomainFullC : a → LamBindingP a
  
  data LamClause : Set where
    LamClauseC : LHS → RHS → WhereClause → Bool → LamClause 
  
  data ModuleApplication : Set where
    SectionAppC : Range → (List (TypedBindings)) → Expr → ModuleApplication 
    RecordModuleIFSC : Range → QName → ModuleApplication 
  
  data ModuleAssignment : Set where
    ModuleAssignmentC : QName → (List (Expr)) → ImportDirective → ModuleAssignment 
  
  data OpApp ( e : Set ) : Set where
    SyntaxBindingLambdaC : Range → (List (LamBinding)) → e → OpApp e
    OrdinaryC : e → OpApp e
  
  data OpenShortHand : Set where
    DoOpenC : OpenShortHand 
    DontOpenC : OpenShortHand 
  
  data Pattern : Set where
    IdentPC : QName → Pattern 
    QuotePC : Range → Pattern 
    AppPC : Pattern → (NamedArg  Pattern) → Pattern 
    RawAppPC : Range → (List (Pattern)) → Pattern 
    OpAppPC : Range → QName → (SSet  Name) → (List ((NamedArg  Pattern))) → Pattern 
    HiddenPC : Range → (NamedU  Pattern) → Pattern 
    InstancePC : Range → (NamedU  Pattern) → Pattern 
    ParenPC : Range → Pattern → Pattern 
    WildPC : Range → Pattern 
    AbsurdPC : Range → Pattern 
    AsPC : Range → Name → Pattern → Pattern 
    DotPC : Range → Expr → Pattern 
    LitPC : Literal → Pattern 
    RecPC : Range → (List ((FieldAssignmentP  Pattern))) → Pattern 
    EqualPC : Range → (List ((Expr ×  Expr))) → Pattern 
    EllipsisPC : Range → Pattern 
    WithPC : Range → Pattern → Pattern 
  
  data Pragma : Set where
    OptionsPragmaC : Range → (List (String)) → Pragma 
    BuiltinPragmaC : Range → String → QName → FixityP → Pragma 
    RewritePragmaC : Range → (List (QName)) → Pragma 
    CompiledDataPragmaC : Range → QName → String → (List (String)) → Pragma 
    CompiledTypePragmaC : Range → QName → String → Pragma 
    CompiledPragmaC : Range → QName → String → Pragma 
    CompiledExportPragmaC : Range → QName → String → Pragma 
    CompiledJSPragmaC : Range → QName → String → Pragma 
    CompiledUHCPragmaC : Range → QName → String → Pragma 
    CompiledDataUHCPragmaC : Range → QName → String → (List (String)) → Pragma 
    HaskellCodePragmaC : Range → String → Pragma 
    ForeignPragmaC : Range → String → String → Pragma 
    CompilePragmaC : Range → String → QName → String → Pragma 
    StaticPragmaC : Range → QName → Pragma 
    InlinePragmaC : Range → Bool → QName → Pragma 
    ImportPragmaC : Range → String → Pragma 
    ImportUHCPragmaC : Range → String → Pragma 
    ImpossiblePragmaC : Range → Pragma 
    EtaPragmaC : Range → QName → Pragma 
    WarningOnUsageC : Range → QName → String → Pragma 
    InjectivePragmaC : Range → QName → Pragma 
    DisplayPragmaC : Range → Pattern → Expr → Pragma 
    CatchallPragmaC : Range → Pragma 
    TerminationCheckPragmaC : Range → (TerminationCheck  Name) → Pragma 
    NoPositivityCheckPragmaC : Range → Pragma 
    PolarityPragmaC : Range → Name → (List (Occurrence)) → Pragma 
    NoUniverseCheckPragmaC : Range → Pragma 
  
  RHS :  Set
  RHS  = (RHSP  Expr)
  
  data RHSP ( e : Set ) : Set where
    AbsurdRHSC : RHSP e
    RHSC : e → RHSP e
  
  RecordAssignment :  Set
  RecordAssignment  = (Either  FieldAssignment ModuleAssignment)
  
  RecordAssignments :  Set
  RecordAssignments  = (List (RecordAssignment))
  
  RewriteEqn :  Set
  RewriteEqn  = Expr
  
  Telescope :  Set
  Telescope  = (List (TypedBindings))
  
  TypeSignature :  Set
  TypeSignature  = Declaration
  
  TypeSignatureOrInstanceBlock :  Set
  TypeSignatureOrInstanceBlock  = Declaration
  
  TypedBinding :  Set
  TypedBinding  = (TypedBindingP  Expr)
  
  data TypedBindingP ( e : Set ) : Set where
    TBindC : Range → (List ((WithHiding  BoundName))) → e → TypedBindingP e
    TLetC : Range → (List (Declaration)) → TypedBindingP e
  
  TypedBindings :  Set
  TypedBindings  = (TypedBindingsP  TypedBinding)
  
  data TypedBindingsP ( a : Set ) : Set where
    TypedBindingsC : Range → (Arg  a) → TypedBindingsP a
  
  WhereClause :  Set
  WhereClause  = (WhereClauseP  (List (Declaration)))
  
  data WhereClauseP ( decls : Set ) : Set where
    NoWhereC : WhereClauseP decls
    AnyWhereC : decls → WhereClauseP decls
    SomeWhereC : Name → Access → decls → WhereClauseP decls
  
  WithExpr :  Set
  WithExpr  = Expr

{-# FOREIGN GHC AsNameP = AsNameP ( AsNameC ) #-}

{-# FOREIGN GHC BoundName = BoundName ( BNameC ) #-}

{-# FOREIGN GHC Declaration = Declaration ( TypeSigC | GeneralizeC | FieldC | FunClauseC | DataSigC | DataC | RecordSigC | RecordC | InfixC | SyntaxC | PatternSynC | MutualC | AbstractC | PrivateC | InstanceBC | MacroC | PostulateC | PrimitiveC | OpenC | ImportC | ModuleMacroC | ModuleC | UnquoteDeclC | UnquoteDefC | PragmaC ) #-}

{-# FOREIGN GHC DoStmt = DoStmt ( DoBindC | DoThenC | DoLetC ) #-}

{-# FOREIGN GHC Expr = Expr ( IdentC | LitC | QuestionMarkC | UnderscoreC | RawAppC | AppC | OpAppC | WithAppC | HiddenArgC | InstanceArgC | LamC | AbsurdLamC | ExtendedLamC | FunC | PiC | SetC | PropC | SetNC | PropNC | RecC | RecUpdateC | LetC | ParenC | IdiomBracketsC | DoBlockC | AbsurdC | AsC | DotC | ETelC | QuoteGoalC | QuoteContextC | QuoteC | QuoteTermC | TacticC | UnquoteC | DontCareC | EqualC | EllipsisC | GeneralizedC ) #-}

{-# FOREIGN GHC FieldAssignmentP = FieldAssignmentP ( FieldAssignmentC ) #-}

{-# FOREIGN GHC LHS = LHS ( LHSC ) #-}

{-# FOREIGN GHC LamBindingP = LamBindingP ( DomainFreeC | DomainFullC ) #-}

{-# FOREIGN GHC LamClause = LamClause ( LamClauseC ) #-}

{-# FOREIGN GHC ModuleApplication = ModuleApplication ( SectionAppC | RecordModuleIFSC ) #-}

{-# FOREIGN GHC ModuleAssignment = ModuleAssignment ( ModuleAssignmentC ) #-}

{-# FOREIGN GHC OpApp = OpApp ( SyntaxBindingLambdaC | OrdinaryC ) #-}

{-# FOREIGN GHC OpenShortHand = OpenShortHand ( DoOpenC | DontOpenC ) #-}

{-# FOREIGN GHC Pattern = Pattern ( IdentPC | QuotePC | AppPC | RawAppPC | OpAppPC | HiddenPC | InstancePC | ParenPC | WildPC | AbsurdPC | AsPC | DotPC | LitPC | RecPC | EqualPC | EllipsisPC | WithPC ) #-}

{-# FOREIGN GHC Pragma = Pragma ( OptionsPragmaC | BuiltinPragmaC | RewritePragmaC | CompiledDataPragmaC | CompiledTypePragmaC | CompiledPragmaC | CompiledExportPragmaC | CompiledJSPragmaC | CompiledUHCPragmaC | CompiledDataUHCPragmaC | HaskellCodePragmaC | ForeignPragmaC | CompilePragmaC | StaticPragmaC | InlinePragmaC | ImportPragmaC | ImportUHCPragmaC | ImpossiblePragmaC | EtaPragmaC | WarningOnUsageC | InjectivePragmaC | DisplayPragmaC | CatchallPragmaC | TerminationCheckPragmaC | NoPositivityCheckPragmaC | PolarityPragmaC | NoUniverseCheckPragmaC ) #-}

{-# FOREIGN GHC RHSP = RHSP ( AbsurdRHSC | RHSC ) #-}

{-# FOREIGN GHC TypedBindingP = TypedBindingP ( TBindC | TLetC ) #-}

{-# FOREIGN GHC TypedBindingsP = TypedBindingsP ( TypedBindingsC ) #-}

{-# FOREIGN GHC WhereClauseP = WhereClauseP ( NoWhereC | AnyWhereC | SomeWhereC ) #-}

 
