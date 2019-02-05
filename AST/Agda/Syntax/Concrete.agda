module AST.Agda.Syntax.Concrete where
open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Sum
import AST.Agda.Syntax.Abstract.Name as A
open import AST.Agda.Syntax.Concrete.Name
open import AST.Agda.Syntax.Common
open import AST.Agda.Syntax.Fixity
open import AST.Agda.Syntax.Literal
open import AST.Agda.Syntax.Notation
open import AST.Agda.Syntax.Position
open import AST.Agda.TypeChecking.Positivity.Occurrence
open import AST.GHC.Types
mutual
  AsName :  Set
  AsName  = (AsName'  (Expr ⊎ Name))
  
  data AsName' ( a : Set ) : Set where
    AsNameC : a → Range → AsName' a
  
  data BoundName : Set where
    BNameC : Name → Name → Fixity' → BoundName 

  {-# NO_POSITIVITY_CHECK #-}
  data Declaration : Set where
    TypeSigC : ArgInfo → Name → Expr → Declaration 
    GeneralizeC : Range → (List (TypeSignature)) → Declaration 
    FieldC : IsInstance → Name → (Arg  Expr) → Declaration 
    FunClauseC : LHS → RHS → WhereClause → Bool → Declaration 
    DataSigC : Range → Induction → Name → (List (LamBinding)) → Expr → Declaration 
    DataC : Range → Induction → Name → (List (LamBinding)) → (Maybe  Expr) → (List (TypeSignatureOrInstanceBlock)) → Declaration 
    RecordSigC : Range → Name → (List (LamBinding)) → Expr → Declaration 
    RecordC : Range → Name → (Maybe  (Ranged  Induction)) → (Maybe  HasEta) → (Maybe  (Name ×P  IsInstance)) → (List (LamBinding)) → (Maybe  Expr) → (List (Declaration)) → Declaration 
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
    OpAppC : Range → QName → (Sett  A.Name) → (List ((NamedArg  (MaybePlaceholder  (OpApp  Expr))))) → Expr 
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
  FieldAssignment  = (FieldAssignment'  Expr)
  
  data FieldAssignment' ( a : Set ) : Set where
    FieldAssignmentC : Name → a → FieldAssignment' a
  
  ImportDirective :  Set
  ImportDirective  = (ImportDirective'  Name Name)
  
  data LHS : Set where
    LHSC : Pattern → (List (RewriteEqn)) → (List (WithExpr)) → LHS 
  
  LamBinding :  Set
  LamBinding  = (LamBinding'  TypedBindings)
  
  data LamBinding' ( a : Set ) : Set where
    DomainFreeC : ArgInfo → BoundName → LamBinding' a
    DomainFullC : a → LamBinding' a
  
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
    OpAppPC : Range → QName → (Sett  A.Name) → (List ((NamedArg  Pattern))) → Pattern 
    HiddenPC : Range → (NamedU  Pattern) → Pattern 
    InstancePC : Range → (NamedU  Pattern) → Pattern 
    ParenPC : Range → Pattern → Pattern 
    WildPC : Range → Pattern 
    AbsurdPC : Range → Pattern 
    AsPC : Range → Name → Pattern → Pattern 
    DotPC : Range → Expr → Pattern 
    LitPC : Literal → Pattern 
    RecPC : Range → (List ((FieldAssignment'  Pattern))) → Pattern 
    EqualPC : Range → (List ((Expr ×P  Expr))) → Pattern 
    EllipsisPC : Range → Pattern 
    WithPC : Range → Pattern → Pattern 
  
  data Pragma : Set where
    OptionsPragmaC : Range → (List (String)) → Pragma 
    BuiltinPragmaC : Range → String → QName → Fixity' → Pragma 
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
  RHS  = (RHS'  Expr)
  
  data RHS' ( e : Set ) : Set where
    AbsurdRHSC : RHS' e
    RHSC : e → RHS' e
  
  RecordAssignment :  Set
  RecordAssignment  = (FieldAssignment ⊎ ModuleAssignment)
  
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
  TypedBinding  = (TypedBinding'  Expr)
  
  data TypedBinding' ( e : Set ) : Set where
    TBindC : Range → (List ((WithHiding  BoundName))) → e → TypedBinding' e
    TLetC : Range → (List (Declaration)) → TypedBinding' e
  
  TypedBindings :  Set
  TypedBindings  = (TypedBindings'  TypedBinding)
  
  data TypedBindings' ( a : Set ) : Set where
    TypedBindingsC : Range → (Arg  a) → TypedBindings' a
  
  WhereClause :  Set
  WhereClause  = (WhereClause'  (List (Declaration)))
  
  data WhereClause' ( decls : Set ) : Set where
    NoWhereC : WhereClause' decls
    AnyWhereC : decls → WhereClause' decls
    SomeWhereC : Name → Access → decls → WhereClause' decls
  
  WithExpr :  Set
  WithExpr  = Expr

{-# FOREIGN GHC import Agda.Syntax.Concrete #-}

{-# COMPILE GHC AsName' = data AsName' ( AsName ) #-}

{-# COMPILE GHC BoundName = data BoundName ( BName ) #-}

{-# COMPILE GHC Declaration = data Declaration ( TypeSig | Generalize | Field | FunClause | DataSig | Data | RecordSig | Record | Infix | Syntax | PatternSyn | Mutual | Abstract | Private | InstanceB | Macro | Postulate | Primitive | Open | Import | ModuleMacro | Module | UnquoteDecl | UnquoteDef | Pragma ) #-}

{-# COMPILE GHC DoStmt = data DoStmt ( DoBind | DoThen | DoLet ) #-}

{-# COMPILE GHC Expr = data Expr ( Ident | Lit | QuestionMark | Underscore | RawApp | App | OpApp | WithApp | HiddenArg | InstanceArg | Lam | AbsurdLam | ExtendedLam | Fun | Pi | Set | Prop | SetN | PropN | Rec | RecUpdate | Let | Paren | IdiomBrackets | DoBlock | Absurd | As | Dot | ETel | QuoteGoal | QuoteContext | Quote | QuoteTerm | Tactic | Unquote | DontCare | Equal | Ellipsis | Generalized ) #-}

{-# COMPILE GHC FieldAssignment' = data FieldAssignment' ( FieldAssignment ) #-}

{-# COMPILE GHC LHS = data LHS ( LHS ) #-}

{-# COMPILE GHC LamBinding' = data LamBinding' ( DomainFree | DomainFull ) #-}

{-# COMPILE GHC LamClause = data LamClause ( LamClause ) #-}

{-# COMPILE GHC ModuleApplication = data ModuleApplication ( SectionApp | RecordModuleIFS ) #-}

{-# COMPILE GHC ModuleAssignment = data ModuleAssignment ( ModuleAssignment ) #-}

{-# COMPILE GHC OpApp = data OpApp ( SyntaxBindingLambda | Ordinary ) #-}

{-# COMPILE GHC OpenShortHand = data OpenShortHand ( DoOpen | DontOpen ) #-}

{-# COMPILE GHC Pattern = data Pattern ( IdentP | QuoteP | AppP | RawAppP | OpAppP | HiddenP | InstanceP | ParenP | WildP | AbsurdP | AsP | DotP | LitP | RecP | EqualP | EllipsisP | WithP ) #-}

{-# COMPILE GHC Pragma = data Pragma ( OptionsPragma | BuiltinPragma | RewritePragma | CompiledDataPragma | CompiledTypePragma | CompiledPragma | CompiledExportPragma | CompiledJSPragma | CompiledUHCPragma | CompiledDataUHCPragma | HaskellCodePragma | ForeignPragma | CompilePragma | StaticPragma | InlinePragma | ImportPragma | ImportUHCPragma | ImpossiblePragma | EtaPragma | WarningOnUsage | InjectivePragma | DisplayPragma | CatchallPragma | TerminationCheckPragma | NoPositivityCheckPragma | PolarityPragma | NoUniverseCheckPragma ) #-}

{-# COMPILE GHC RHS' = data RHS' ( AbsurdRHS | RHS ) #-}

{-# COMPILE GHC TypedBinding' = data TypedBinding' ( TBind | TLet ) #-}

{-# COMPILE GHC TypedBindings' = data TypedBindings' ( TypedBindings ) #-}

{-# COMPILE GHC WhereClause' = data WhereClause' ( NoWhere | AnyWhere | SomeWhere ) #-}

 
