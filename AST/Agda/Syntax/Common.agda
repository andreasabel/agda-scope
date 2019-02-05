module AST.Agda.Syntax.Common where
open import Data.Bool
open import Data.List
open import AST.Agda.Syntax.Position
open import AST.Data.IntSet.Internal
open import AST.GHC.Types
open import AST.GHC.Types as AGT

open import AST.Data.Strict.Maybe as ADSM

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
  
  data ImportDirective' ( n m : Set ) : Set where
    ImportDirectiveC : Range → (Using'  n m) → (List ((ImportedName'  n m))) → (List ((Renaming'  n m))) → Bool → ImportDirective' n m
  
  data ImportedName' ( n m : Set ) : Set where
    ImportedModuleC : m → ImportedName' n m
    ImportedNameC : n → ImportedName' n m
  
  data Induction : Set where
    InductiveC : Induction 
    CoInductiveC : Induction 
  
  data IsInstance : Set where
    InstanceDefC : IsInstance 
    NotInstanceDefC : IsInstance 
  
  data MaybePlaceholder ( e : Set ) : Set where
    PlaceholderC : PositionInName → MaybePlaceholder e
    NoPlaceholderC : (ADSM.Maybe  PositionInName) → e → MaybePlaceholder e
  
  data MetaId : Set where
    MetaIdC : Nat → MetaId 
  
  data Modality : Set where
    ModalityC : Relevance → Quantity → Modality 
  
  data NameId : Set where
    NameIdC : Word64 → Word64 → NameId 
  
  data Named ( name a : Set ) : Set where
    NamedC : (AGT.Maybe  name) → a → Named name a
  
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
  
  data Renaming' ( n m : Set ) : Set where
    RenamingC : (ImportedName'  n m) → (ImportedName'  n m) → Range → Renaming' n m
  
  data TerminationCheck ( m : Set ) : Set where
    TerminationCheckC : TerminationCheck m
    NoTerminationCheckC : TerminationCheck m
    NonTerminatingC : TerminationCheck m
    TerminatingC : TerminationCheck m
    TerminationMeasureC : Range → m → TerminationCheck m
  
  data Using' ( n m : Set ) : Set where
    UseEverythingC : Using' n m
    UsingC : (List ((ImportedName'  n m))) → Using' n m
  
  data WithHiding ( a : Set ) : Set where
    WithHidingC : Hiding → a → WithHiding a

{-# FOREIGN GHC import Agda.Syntax.Common #-}

{-# COMPILE GHC Access = data Access ( PrivateAccess | PublicAccess | OnlyQualified ) #-}

{-# COMPILE GHC Arg = data Arg ( Arg ) #-}

{-# COMPILE GHC ArgInfo = data ArgInfo ( ArgInfo ) #-}

{-# COMPILE GHC FreeVariables = data FreeVariables ( UnknownFVs | KnownFVs ) #-}

{-# COMPILE GHC HasEta = data HasEta ( NoEta | YesEta ) #-}

{-# COMPILE GHC Hiding = data Hiding ( Hidden | Instance | NotHidden ) #-}

{-# COMPILE GHC ImportDirective' = data ImportDirective' ( ImportDirective ) #-}

{-# COMPILE GHC ImportedName' = data ImportedName' ( ImportedModule | ImportedName ) #-}

{-# COMPILE GHC Induction = data Induction ( Inductive | CoInductive ) #-}

{-# COMPILE GHC IsInstance = data IsInstance ( InstanceDef | NotInstanceDef ) #-}

{-# COMPILE GHC MaybePlaceholder = data MaybePlaceholder ( Placeholder | NoPlaceholder ) #-}

{-# COMPILE GHC MetaId = data MetaId ( MetaId ) #-}

{-# COMPILE GHC Modality = data Modality ( Modality ) #-}

{-# COMPILE GHC NameId = data NameId ( NameId ) #-}

{-# COMPILE GHC Named = data Named ( Named ) #-}

{-# COMPILE GHC Origin = data Origin ( UserWritten | Inserted | Reflected | CaseSplit | Substitution ) #-}

{-# COMPILE GHC Overlappable = data Overlappable ( YesOverlap | NoOverlap ) #-}

{-# COMPILE GHC PositionInName = data PositionInName ( Beginning | Middle | End ) #-}

{-# COMPILE GHC Quantity = data Quantity ( Quantity0 | Quantity1 | Quantityω ) #-}

{-# COMPILE GHC Ranged = data Ranged ( Ranged ) #-}

{-# COMPILE GHC Relevance = data Relevance ( Relevant | NonStrict | Irrelevant ) #-}

{-# COMPILE GHC Renaming' = data Renaming' ( Renaming ) #-}

{-# COMPILE GHC TerminationCheck = data TerminationCheck ( TerminationCheck | NoTerminationCheck | NonTerminating | Terminating | TerminationMeasure ) #-}

{-# COMPILE GHC Using' = data Using' ( UseEverything | Using ) #-}

{-# COMPILE GHC WithHiding = data WithHiding ( WithHiding ) #-}

 
