{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}  -- For type equality
{-# LANGUAGE TemplateHaskell #-}


module ScopeChecker where

import Control.Monad.Trans.Maybe
import Control.Monad.Except
import Control.Monad.State

import Data.Bifunctor
import Data.Foldable (Foldable, foldMap)
import Data.Function
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH

import Text.PrettyPrint

import HierMod.Abs

-- | Access modifier.
data Access
  = Private
  | Public
  deriving Show

-- | A decoration of a thing with an access modifier.
data WithAccess a = WithAccess
  { _waAccess :: Access
  , _waThing  :: a
  }
  deriving (Show, Functor)
makeLenses ''WithAccess

-- | Qualified identifiers.
type QName = [Name]  -- non-empty

-- | Unique identifiers.
type UName = [Name]

-- | Absolute names (resolved names) in module contents.
data AName = AName
  { uname   :: UName    -- ^ The uid.
  , lineage :: Lineage  -- ^ The history how this name entered a module.
  } deriving (Show)

-- | Ignore history.
instance Eq AName where
  (==) = (==) `on` uname

instance Ord AName where
  compare = compare `on` uname

-- | Module entries come from definitions or imports.
data Lineage
  = -- | Defined here in this module.
    Defined
  | -- | Imported from another module.
    ViaOpen (Imported ())
  deriving (Show)

-- | Decorate something with import info.
data Imported a = Imported
  { importedFrom  :: UName
  , importedThing :: a
  } deriving (Show, Functor)

-- | Ignore decoration.
instance Eq a => Eq (Imported a) where
  (==) = (==) `on` importedThing

instance Ord a => Ord (Imported a) where
  compare = compare `on` importedThing

-- | Defined names.
data DName a
  = PublicDef  { dnDef :: UName }
  | PrivateDef { dnDef :: UName , dnThing :: a }
  | NoDef      { dnThing :: a }
  deriving (Show, Functor)

-- | Imported names
type IName = Imported UName

-- | Defined and publicly imported occurrences.
type DefAndPub = DName (Maybe IName)

-- | An ambiguous name.
data NameSet = NameSet
  { _def  :: DefAndPub
      -- ^ At most one definition of a 'Name' in a module.
      --   If it is private, we can have a public import of that name as well.
  , _priv :: Set IName
      -- ^ Any number of private imports.
  } deriving Show

-- | The value of a module is the names it defines.
type ModuleContent = Map Name NameSet

-- | The signature holds values for the completely defined modules.
type Signature = Map UName ModuleContent

-- | The context holds the partially defined modules up to the POV.
type Context = Stack Entry
type Entry   = (Name, ModuleContent)
type Stack a = [a]

-- | The scope checking monad.
type ScopeM = StateT ScopeState (Except ScopeError)

data ScopeError
  = NotInScopeError QName
  | AmbiguousName QName
  | ConflictPublic [Name]
  -- Internal errors (should be impossible):
  | ImpossibleUndefined UName
  | ImpossibleEmptyStack
  deriving Show

data ScopeState = ScopeState
  { _sig :: Signature
  , _cxt :: Context
  }

makeLenses ''ScopeState
makeLenses ''NameSet

-- | Checking a program.

checkProgram :: Program -> Either Doc Doc
checkProgram (Prg x ds) = bimap pretty (pretty . _sig) $
  runExcept . (`execStateT` initState) $
  checkModule' x ds
  where initState = ScopeState Map.empty []

-- | Checking a single declaration.

checkDecl :: Decl -> ScopeM ()
checkDecl = \case
  Modl x ds        -> checkModule Public x ds
  PrivateModl x ds -> checkModule Private x ds
  Open q           -> checkOpen q Private
  OpenPublic q     -> checkOpen q Public

-- | Check module and bind to x.

checkModule :: Access -> Name -> [Decl] -> ScopeM ()
checkModule acc x ds = do
  u <- checkModule' x ds
  addBind x u acc

-- | Check module, don't bind it, but return its uid.

checkModule' :: Name -> [Decl] -> ScopeM UName
checkModule' x ds = do
  newModule x
  mapM_ checkDecl ds
  closeModule

-- | Check an `open` statement and preform the import.

checkOpen :: QName -> Access -> ScopeM ()
checkOpen q acc = do
  u <- uname <$> lookupModule q
  m <- getModule u
  addContent $ keepPublicAs acc u m

-- * Components

-- | Push a new empty module onto the context.

newModule :: Name -> ScopeM ()
newModule x = push (x, emptyModule)

-- | Pop the top module, bind it in the signature, and return its uid.

closeModule :: ScopeM UName
closeModule = do
  (u, m) <- popCurrentModule
  defineModule u m
  return u

-- | Merge given content into current module.
--   Public import fails if it generates clashes with public names.

addContent :: ModuleContent -> ScopeM ()
addContent m = modifyCurrentModuleM $ \ orig -> do
  let mergeNameSets' ea eb = do { a <- ea; b <- eb; mergeNameSets a b }
  let (bad, good) =
        Map.mapEitherWithKey (\ x -> bimap (x,) id) $
          Map.unionWith mergeNameSets' (fmap Right orig) (fmap Right m)
  if Map.null bad
    then return good
    else throwError $ ConflictPublic $ map fst $ Map.toList bad

-- | Add a binding to the current module.

addBind :: Name -> UName -> Access -> ScopeM ()
addBind x u a = addContent $ Map.singleton x $ unambiguousName a $ AName u Defined
-- addBind x u a = modifyCurrentModuleM $ \ m ->
--   case Map.lookup x m of
--     -- x is not bound yet
--     Nothing -> return $ Map.insert x ns1 m
--     -- x is already bound: make sure to not shadow public.
--     Just amb ->
--       case unionMaybe amb ns1 of
--         Nothing   -> throwError $ ConflictPublic [x]
--         Just amb' -> return $ Map.insert x amb' m
--   where
--   ns1 = unambiguousName a $ AName u Defined

-- | Lookup module in current scope and return its uid.
--   Commits to the parent that contains the head.

lookupModule :: QName -> ScopeM AName
lookupModule q = foldr (lookupInContentM q) err =<< currentScope
  where
  err = throwError $ NotInScopeError q
  -- | Lookup qualified name in module content (recursively).
  lookupInContentM :: QName -> ModuleContent -> ScopeM AName -> ScopeM AName
  lookupInContentM (x:xs) m cont =
    case lookupInContent x m of
      NotInScope    -> cont
      Ambiguous us  -> throwError $ AmbiguousName q
      InScope y
        | null xs   -> return y
        | otherwise -> getModule (uname y) >>= \ m -> lookupInContentM xs m err
          -- Once the head x matched, we cannot go back.
          -- We discard the continuation, replace it by the not-in-scope error.

-- | Lookup module in current scope.  (Alternative, problematic.)
--   Does not commit on matching heads.
--   E.g. when looking for M.N where the current module
--   only defines M, but the parent M.N, this will succeed.

lookupModuleNoCommit :: QName -> ScopeM AName
lookupModuleNoCommit q = do
  maybe (throwError $ NotInScopeError q) return =<< do
    firstSuccess . map (lookupInContentM q) =<< currentScope
  where
  -- | Lookup qualified name in module content (recursively).
  lookupInContentM :: QName -> ModuleContent -> ScopeM (Maybe AName)
  lookupInContentM (x:xs) m =
    case lookupInContent x m of
      NotInScope    -> return Nothing
      Ambiguous us  -> throwError $ AmbiguousName q
      InScope y
        | null xs   -> return (Just y)
        | otherwise -> lookupInContentM xs =<< getModule (uname y)

-- | Get defined module from signature.
--   Expects to find it there.

getModule :: UName -> ScopeM ModuleContent
getModule u =
  maybe (throwError $ ImpossibleUndefined u) return =<< do
    Map.lookup u <$> use sig

-- | Prepare module for 'open'.
--   Remove private bindings and modify public bindings according to 'Access'.

keepPublicAs :: Access -> UName -> ModuleContent -> ModuleContent
keepPublicAs acc u = Map.mapMaybe $ keepPublicAs' acc u


-- * Basic data structure manipulations

emptyModule :: ModuleContent
emptyModule = Map.empty

-- | Result of lookup.

data InScope a
  = NotInScope
  | InScope a
  | Ambiguous [a]

-- | Search for a name in a module.

lookupInContent :: Name -> ModuleContent -> InScope AName
lookupInContent x = maybe NotInScope (unambiguous . nub' . toANames) . Map.lookup x
  where
  unambiguous :: [AName] -> InScope AName
  unambiguous = \case
    []  -> NotInScope
    [u] -> InScope u
    us  -> Ambiguous us

-- | Make a singleton 'NameSet'.

unambiguousName :: Access -> AName -> NameSet
unambiguousName acc (AName u lin) =
  case (acc, lin) of
   (Public , Defined)     -> NameSet (PublicDef u) Set.empty
   (Private, Defined)     -> NameSet (PrivateDef u Nothing) Set.empty
   (Public,  ViaOpen imp) -> NameSet (NoDef $ Just $ u <$ imp) Set.empty
   (Private, ViaOpen imp) -> NameSet (NoDef Nothing) $ Set.singleton $ u <$ imp

-- | Restrict NameSet for import from @y@.
--   It collapses to 'Nothing' if there are no public names.

keepPublicAs' :: Access -> UName -> NameSet -> Maybe NameSet
keepPublicAs' acc y (NameSet def _) =
  case def of
    PublicDef u           -> Just $ unambiguousName acc $ AName u $ ViaOpen $ Imported y ()
    PrivateDef _ (Just i) -> Just $ unambiguousName acc $ AName u $ ViaOpen $ Imported y ()
      where u = importedThing i
    PrivateDef _ Nothing  -> Nothing
    NoDef{}               -> Nothing


-- -- | Extending a name set fails if result would hold more than one public name
-- --   or more than one defined name.
-- addNameToSet :: Access -> AName -> NameSet -> Maybe NameSet
-- addNameToSet acc u ns = unionMaybe ns $ unambiguousName acc u

-- | Merging can fail if both sets have a public name.
--   In this case, the second public name is returned.

mergeNameSets :: NameSet -> NameSet -> Either () NameSet
mergeNameSets ns1 ns2 = maybeToEither $ unionMaybe ns1 ns2

-- * Basic name manipulation

-- ** Content of NameSet

class ToANames a where
  toANames :: a -> [AName]

  default toANames :: (Foldable t, ToANames b, t b ~ a) => a -> [AName]
  toANames = foldMap toANames

instance ToANames a => ToANames (Maybe a)
instance ToANames a => ToANames [a]
instance ToANames a => ToANames (Set a)

instance ToANames IName where
  toANames (Imported y u) = [AName u $ ViaOpen $ Imported y ()]

instance ToANames a => ToANames (DName a) where
  toANames = \case
    PublicDef u    -> [AName u Defined]
    PrivateDef u a -> AName u Defined : toANames a
    NoDef a        -> toANames a

instance ToANames NameSet where
  toANames (NameSet def pr) = toANames def ++ toANames pr

-- ** Content of NameSet including Access modifiers.

type WAName = WithAccess AName

class ToWANames a where
  toWANames :: a -> [WAName]

  default toWANames :: (Foldable t, ToWANames b, t b ~ a) => a -> [WAName]
  toWANames = foldMap toWANames

instance ToWANames a => ToWANames (Maybe a)
instance ToWANames a => ToWANames [a]
instance ToWANames a => ToWANames (Set a)

instance ToANames a => ToWANames (DName a) where
  toWANames = \case
    PublicDef u    -> [WithAccess Public $ AName u Defined]
    PrivateDef u a -> WithAccess Private (AName u Defined) :
                      (WithAccess Public <$> toANames a)
    NoDef a        -> WithAccess Public <$> toANames a

instance ToWANames NameSet where
  toWANames (NameSet def pr) = concat
    [ toWANames def
    , WithAccess Private <$> toANames pr
    ]

-- ** Joining NameSets

instance UnionMaybe DefAndPub where
  unionMaybe = curry $ \case
    -- One set is empty:
    (NoDef Nothing, def)   -> Just def
    (def, NoDef Nothing)   -> Just def
    -- No public definitions:
    (NoDef pu1, NoDef pu2) -> NoDef <$> unionMaybe pu1 pu2
    (PrivateDef u pu1, NoDef pu2) -> PrivateDef u <$> unionMaybe pu1 pu2
    (NoDef pu1, PrivateDef u pu2) -> PrivateDef u <$> unionMaybe pu1 pu2
    -- If we have public definitions, and the other set is not empty,
    -- we get two public exports, which is not legal:
    _ -> Nothing

instance UnionMaybe NameSet where
  unionMaybe (NameSet def1 pr1) (NameSet def2 pr2) =
    unionMaybe def1 def2 <&> (`NameSet` Set.union pr1 pr2)

-- * Basic monad services

-- ** Context

push :: Entry -> ScopeM ()
push e = cxt %= (e:)

pop :: ScopeM Entry
pop = do
  (e, es) <- maybe (throwError ImpossibleEmptyStack) return . List.uncons =<< use cxt
  cxt .= es
  return e

popCurrentModule :: ScopeM (UName, ModuleContent)
popCurrentModule = do
  u <- currentModule
  (u,) . snd <$> pop
  where
  currentModule :: ScopeM UName
  currentModule = reverse . map fst <$> use cxt

currentScope :: ScopeM [ModuleContent]
currentScope = map snd <$> use cxt

modifyCurrentModuleM :: (ModuleContent -> ScopeM ModuleContent) -> ScopeM ()
modifyCurrentModuleM = (cxt . lensHead . _2 %==)

-- ** Signature

defineModule :: UName -> ModuleContent -> ScopeM ()
defineModule u m = sig %= Map.insert u m

-- * Pretty printing

class Pretty a where
  pretty :: a -> Doc

instance Pretty Name where
  pretty (Name s) = text s

instance Pretty [Name] where
  pretty = hcat . punctuate "." . map pretty

instance Pretty Access where
  pretty = \case
    Private -> "private"
    Public  -> "public"

instance Pretty a => Pretty (WithAccess a) where
  pretty (WithAccess acc a) = pretty acc <+> pretty a

-- instance Pretty (Imported ()) where

instance Pretty Lineage where
  pretty = \case
    Defined -> "defined here"
    ViaOpen (Imported u ()) -> "imported from" <+> pretty u

instance Pretty AName where
  -- pretty (AName u lin) = pretty u <+> parens (pretty lin)
  pretty (AName u Defined) = pretty u
  pretty (AName u lin)     = pretty u <+> parens (pretty lin)

instance Pretty NameSet where
  pretty ns@(NameSet def pu) =
    case map pretty $ toWANames ns of  -- TODO access
      []  -> "∅"
      [d] -> d
      ds  -> braces . hcat . punctuate ", " $ ds
    -- where
    -- pub  = maybeToList . fmap (("public" <+>) . pretty) $ pu
    -- priv = map (("private" <+>) . pretty) $ Set.toList pr

instance Pretty ModuleContent where
  pretty m = vcat . map pr $ Map.toList m
    where pr (x, ns) = nest 2 $ pretty x <+> "↦" <+> pretty ns

instance Pretty Signature where
  pretty sig = vcat . map pr $ Map.toList sig
    where pr (u, m) = vcat [ "module" <+> pretty u, pretty m ]

instance Pretty ScopeError where
  pretty = \case
    NotInScopeError q     -> "Identifier " <+> pretty q <+> " is not in scope"
    AmbiguousName q       -> "Identifier " <+> pretty q <+> " is ambiguous"
    ConflictPublic [x]    -> "Name " <+> pretty x <+> " has" <+> rest
    ConflictPublic xs     -> "Names " <+> hcat (punctuate ", " $ map pretty xs) <+> " have" <+> rest
    ImpossibleUndefined u -> "Panic: couldn't find the definition of module " <+> pretty u
    ImpossibleEmptyStack  -> "Panic: unexpected empty module stack"
    where rest = "already a definition or public import"

-- * Lens tools

lensHead :: Lens' [a] a
lensHead f (a:as) = (:as) <$> f a

infix 4 %==

-- | Modify a part of the state monadically.
(%==) :: MonadState o m => Lens' o i -> (i -> m i) -> m ()
l %== f = put =<< l f =<< get

-- * Generic utilities

nub' :: Ord a => [a] -> [a]
nub' = Set.toList . Set.fromList

firstSuccess :: Monad m => [m (Maybe a)] -> m (Maybe a)
firstSuccess = \case
  []   -> return Nothing
  m:ms -> m >>= \case
    Nothing  -> firstSuccess ms
    r@Just{} -> return r

-- | Convert between error monads.

maybeToEither :: Maybe a -> Either () a
maybeToEither = \case
  Nothing -> Left ()
  Just a  -> Right a

-- | Adding to a <=1 collection may fail.

addMaybe :: a -> Maybe a -> Maybe (Maybe a)
addMaybe a Nothing = Just (Just a)
addMaybe a Just{}  = Nothing

-- | Partial semigroup.

class UnionMaybe a where
  unionMaybe :: a -> a -> Maybe a

instance UnionMaybe (Maybe a) where
  unionMaybe = \case
    Nothing -> Just
    Just a  -> addMaybe a
