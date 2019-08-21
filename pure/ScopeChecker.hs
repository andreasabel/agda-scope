{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module ScopeChecker where

import Control.Monad.Trans.Maybe
import Control.Monad.Except
import Control.Monad.State

import Data.Bifunctor
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH

import HierMod.Abs

-- | Access modifier.
data Access
  = Private
  | Public

-- | Qualified identifiers.
type QName = [Name]  -- non-empty

-- | Unique identifiers.
type AName = [Name]

-- | An ambiguous name.
data NameSet = NameSet
  { _pub  :: Maybe AName  -- ^ At most one public binding.
  , _priv :: Set AName    -- ^ Private bindings can be ambiguous.
  } deriving Show

-- | The value of a module is the names it defines.
type ModuleContent = Map Name NameSet

-- | The signature holds values for the completely defined modules.
type Signature = Map AName ModuleContent

-- | The context holds the partially defined modules up to the POV.
type Context = Stack Entry
type Entry   = (Name, ModuleContent)
type Stack a = [a]

-- | The scope checking monad.
type ScopeM = StateT ScopeState (Except ScopeError)

data ScopeError
  = NotInScope QName
  | ConflictPublic [Name]
  | ImpossibleUndefined AName
  deriving Show

data ScopeState = ScopeState
  { _sig :: Signature
  , _cxt :: Context
  }

makeLenses ''ScopeState
makeLenses ''NameSet

-- | Checking a program.

checkProgram :: Program -> Either ScopeError Signature
checkProgram (Prg x ds) = bimap id _sig . runExcept . (`execStateT` initState) $
  checkModule' x ds
  where initState = ScopeState Map.empty []

-- | Checking a single declaration.

checkDecl :: Decl -> ScopeM ()
checkDecl = \case
  Modl x ds        -> checkModule Public x ds
  PrivateModl x ds -> checkModule Private x ds
  Open q           -> checkOpen q Private
  OpenPublic q     -> checkOpen q Public

-- | Check and bind to x.
checkModule :: Access -> Name -> [Decl] -> ScopeM ()
checkModule acc x ds = do
  u <- checkModule' x ds
  addBind x u acc

-- | Check and return uid.
checkModule' :: Name -> [Decl] -> ScopeM AName
checkModule' x ds = do
  newModule x
  mapM_ checkDecl ds
  closeModule

checkOpen :: QName -> Access -> ScopeM ()
checkOpen q acc = importContent =<< do
  keepPublicAs acc <$> (getModule <=< lookupModule) q

-- * Components

newModule :: Name -> ScopeM ()
newModule x = push (x, emptyModule)

closeModule :: ScopeM AName
closeModule = do
  u <- currentModule
  m <- snd <$> pop
  defineModule u m
  return u

addBind :: Name -> AName -> Access -> ScopeM ()
addBind x u a = modifyCurrentModuleM $ \ m ->
  case Map.lookup x m of
    -- x is not bound yet
    Nothing -> return $ Map.insert x (unambiguousName a u) m
    -- x is already bound: make sure to not shadow public.
    Just amb ->
      case addNameToSet a u amb of
        Nothing   -> throwError $ ConflictPublic [x]
        Just amb' -> return $ Map.insert x amb' m

-- | Lookup module in current scope.
lookupModule :: QName -> ScopeM AName
lookupModule q = do
  maybe (throwError $ NotInScope q) return =<< do
    firstSuccess . map (lookupInContent q) =<< currentScope

-- | Lookup qualified name in module content (recursively).
lookupInContent :: QName -> ModuleContent -> ScopeM (Maybe AName)
lookupInContent (x:q) m =
  case Map.lookup x m of
    Nothing         -> return Nothing
    Just amb -> case unambiguous amb of
      Nothing       -> return Nothing
      Just u
        | null q    -> return (Just u)
        | otherwise -> lookupInContent q =<< getModule u

-- | Get defined module from signature.
getModule :: AName -> ScopeM ModuleContent
getModule u =
  maybe (throwError $ ImpossibleUndefined u) return =<< do
    Map.lookup u <$> use sig

-- | Prepare module for 'open'.
keepPublicAs :: Access -> ModuleContent -> ModuleContent
keepPublicAs acc = Map.mapMaybe $ keepPublicAs' acc

-- | Public import fails if it generates clashes with public names.
importContent :: ModuleContent -> ScopeM ()
importContent m = modifyCurrentModuleM $ \ orig -> do
    let mergeNameSets' ea eb = do { a <- ea; b <- eb; mergeNameSets a b }
    let (bad, good) =
          Map.mapEitherWithKey (\ x -> bimap (x,) id) $
            Map.unionWith mergeNameSets' (fmap Right orig) (fmap Right m)
            -- Map.merge (Map.preserveMissing) (Map.preserveMissing) (const mergeNameSets) orig m
    if Map.null bad
      then return good
      else throwError $ ConflictPublic $ map fst $ Map.toList bad


-- * Basic data structure manipulations

emptyModule = Map.empty

unambiguous :: NameSet -> Maybe AName
unambiguous (NameSet pu pr) =
  case maybeToList pu ++ Set.toList pr of
    [u] -> Just u
    _   -> Nothing

-- | A singleton 'NameSet'.
unambiguousName :: Access -> AName -> NameSet
unambiguousName Public = (`NameSet` Set.empty) . Just
unambiguousName Private = NameSet Nothing . Set.singleton

-- | NameSet collapses if there are no public names.
keepPublicAs' :: Access -> NameSet -> Maybe NameSet
keepPublicAs' acc (NameSet pu _) = unambiguousName acc <$> pu

-- | Extending a name set fails if result would hold more than one public name.
addNameToSet :: Access -> AName -> NameSet -> Maybe NameSet
addNameToSet Public  u (NameSet pu pr) = (`NameSet` pr) <$> addMaybe u pu
addNameToSet Private u (NameSet pu pr) = Just $ NameSet pu $ Set.insert u pr

-- | Merging can fail if both sets have a public name.
--   In this case, the second public name is returned.
mergeNameSets :: NameSet -> NameSet -> Either AName NameSet
mergeNameSets (NameSet pu1 pr1) (NameSet pu2 pr2) =
  case addMaybes pu1 pu2 of
    Nothing -> Left $ fromJust pu2
    Just pu -> Right $ NameSet pu $ Set.union pr1 pr2

-- * Basic monad services

push :: Entry -> ScopeM ()
push e = cxt %= (e:)

pop :: ScopeM Entry
pop = do
  (e:es) <- use cxt
  cxt .= es
  return e

currentModule :: ScopeM AName
currentModule = map fst <$> use cxt

currentScope :: ScopeM [ModuleContent]
currentScope = map snd <$> use cxt

defineModule :: AName -> ModuleContent -> ScopeM ()
defineModule u m = sig %= Map.insert u m

modifyCurrentModuleM :: (ModuleContent -> ScopeM ModuleContent) -> ScopeM ()
modifyCurrentModuleM = (cxt . lensHead . _2 %==)

-- * Lens tools

lensHead :: Lens' [a] a
lensHead f (a:as) = (:as) <$> f a

infix 4 %==

-- | Modify a part of the state monadically.
(%==) :: MonadState o m => Lens' o i -> (i -> m i) -> m ()
l %== f = put =<< l f =<< get

-- * Utils

firstSuccess :: Monad m => [m (Maybe a)] -> m (Maybe a)
firstSuccess = \case
  []   -> return Nothing
  m:ms -> m >>= \case
    Nothing  -> firstSuccess ms
    r@Just{} -> return r

-- | Add to a <=1 collection may fail.
addMaybe :: a -> Maybe a -> Maybe (Maybe a)
addMaybe a Nothing = Just (Just a)
addMaybe a Just{}  = Nothing

addMaybes :: Maybe a -> Maybe a -> Maybe (Maybe a)
addMaybes Nothing  = Just
addMaybes (Just a) = addMaybe a
