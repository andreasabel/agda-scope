module AST.AgdaSyntaxCommon where
open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.String
open import AST.AgdaSyntaxPosition
open import AST.DataIntSetInternal
open import AST.GHCTypes
open import AST.GHCWord
mutual
  data Access : Set where
    PrivateAccessC : Origin → Access 
    PublicAccessC : Access 
    OnlyQualifiedC : Access 
  
  data Arg ( e : Set ) : Set where
    ArgC : ArgInfo → e → Arg e
  
  data ArgInfo : Set where
    ArgInfoC : Hiding → Modality → Origin → FreeVariables → ArgInfo 
  
  data FreeVariables : Set where
    UnknownFVsC : FreeVariables 
    KnownFVsC : IntSet → FreeVariables 
  
  data HasEta : Set where
    NoEtaC : HasEta 
    YesEtaC : HasEta 
  
  data Hiding : Set where
    HiddenC : Hiding 
    InstanceC : Overlappable → Hiding 
    NotHiddenC : Hiding 
  
  data ImportDirectiveP ( n m : Set ) : Set where
    ImportDirectiveC : Range → (UsingP  n m) → (List ((ImportedNameP  n m))) → (List ((RenamingP  n m))) → Bool → ImportDirectiveP n m
  
  data ImportedNameP ( n m : Set ) : Set where
    ImportedModuleC : m → ImportedNameP n m
    ImportedNameC : n → ImportedNameP n m
  
  data Induction : Set where
    InductiveC : Induction 
    CoInductiveC : Induction 
  
  data IsInstance : Set where
    InstanceDefC : IsInstance 
    NotInstanceDefC : IsInstance 
  
  data MaybePlaceholder ( e : Set ) : Set where
    PlaceholderC : PositionInName → MaybePlaceholder e
    NoPlaceholderC : (Maybe  PositionInName) → e → MaybePlaceholder e
  
  data MetaId : Set where
    MetaIdC : Nat → MetaId 
  
  data Modality : Set where
    ModalityC : Relevance → Quantity → Modality 
  
  data NameId : Set where
    NameIdC : Word64 → Word64 → NameId 
  
  data Named ( name a : Set ) : Set where
    NamedC : (Maybe  name) → a → Named name a
  
  NamedArg : Set →  Set
  NamedArg a = (Arg  (NamedU  a))
  
  NamedU : Set →  Set
  NamedU  = (Named  RString)
  
  Nat :  Set
  Nat  = Int
  
  data Origin : Set where
    UserWrittenC : Origin 
    InsertedC : Origin 
    ReflectedC : Origin 
    CaseSplitC : Origin 
    SubstitutionC : Origin 
  
  data Overlappable : Set where
    YesOverlapC : Overlappable 
    NoOverlapC : Overlappable 
  
  data PositionInName : Set where
    BeginningC : PositionInName 
    MiddleC : PositionInName 
    EndC : PositionInName 
  
  data Quantity : Set where
    Quantity0C : Quantity 
    Quantity1C : Quantity 
    QuantityωC : Quantity 
  
  RString :  Set
  RString  = (Ranged  RawName)
  
  data Ranged ( a : Set ) : Set where
    RangedC : Range → a → Ranged a
  
  RawName :  Set
  RawName  = String
  
  data Relevance : Set where
    RelevantC : Relevance 
    NonStrictC : Relevance 
    IrrelevantC : Relevance 
  
  data RenamingP ( n m : Set ) : Set where
    RenamingC : (ImportedNameP  n m) → (ImportedNameP  n m) → Range → RenamingP n m
  
  data TerminationCheck ( m : Set ) : Set where
    TerminationCheckC : TerminationCheck m
    NoTerminationCheckC : TerminationCheck m
    NonTerminatingC : TerminationCheck m
    TerminatingC : TerminationCheck m
    TerminationMeasureC : Range → m → TerminationCheck m
  
  data UsingP ( n m : Set ) : Set where
    UseEverythingC : UsingP n m
    UsingC : (List ((ImportedNameP  n m))) → UsingP n m
  
  data WithHiding ( a : Set ) : Set where
    WithHidingC : Hiding → a → WithHiding a

{-# COMPILE GHC Access = data Access ( PrivateAccessC | PublicAccessC | OnlyQualifiedC ) #-}

{-# COMPILE GHC Arg = data Arg ( ArgC ) #-}

{-# COMPILE GHC ArgInfo = data ArgInfo ( ArgInfoC ) #-}

{-# COMPILE GHC FreeVariables = data FreeVariables ( UnknownFVsC | KnownFVsC ) #-}

{-# COMPILE GHC HasEta = data HasEta ( NoEtaC | YesEtaC ) #-}

{-# COMPILE GHC Hiding = data Hiding ( HiddenC | InstanceC | NotHiddenC ) #-}

{-# COMPILE GHC ImportDirectiveP = data ImportDirectiveP ( ImportDirectiveC ) #-}

{-# COMPILE GHC ImportedNameP = data ImportedNameP ( ImportedModuleC | ImportedNameC ) #-}

{-# COMPILE GHC Induction = data Induction ( InductiveC | CoInductiveC ) #-}

{-# COMPILE GHC IsInstance = data IsInstance ( InstanceDefC | NotInstanceDefC ) #-}

{-# COMPILE GHC MaybePlaceholder = data MaybePlaceholder ( PlaceholderC | NoPlaceholderC ) #-}

{-# COMPILE GHC MetaId = data MetaId ( MetaIdC ) #-}

{-# COMPILE GHC Modality = data Modality ( ModalityC ) #-}

{-# COMPILE GHC NameId = data NameId ( NameIdC ) #-}

{-# COMPILE GHC Named = data Named ( NamedC ) #-}

{-# COMPILE GHC Origin = data Origin ( UserWrittenC | InsertedC | ReflectedC | CaseSplitC | SubstitutionC ) #-}

{-# COMPILE GHC Overlappable = data Overlappable ( YesOverlapC | NoOverlapC ) #-}

{-# COMPILE GHC PositionInName = data PositionInName ( BeginningC | MiddleC | EndC ) #-}

{-# COMPILE GHC Quantity = data Quantity ( Quantity0C | Quantity1C | QuantityωC ) #-}

{-# COMPILE GHC Ranged = data Ranged ( RangedC ) #-}

{-# COMPILE GHC Relevance = data Relevance ( RelevantC | NonStrictC | IrrelevantC ) #-}

{-# COMPILE GHC RenamingP = data RenamingP ( RenamingC ) #-}

{-# COMPILE GHC TerminationCheck = data TerminationCheck ( TerminationCheckC | NoTerminationCheckC | NonTerminatingC | TerminatingC | TerminationMeasureC ) #-}

{-# COMPILE GHC UsingP = data UsingP ( UseEverythingC | UsingC ) #-}

{-# COMPILE GHC WithHiding = data WithHiding ( WithHidingC ) #-}

 
