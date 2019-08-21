{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
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
  = NotInScopeError QName
  | AmbiguousName QName
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

checkModule' :: Name -> [Decl] -> ScopeM AName
checkModule' x ds = do
  newModule x
  mapM_ checkDecl ds
  closeModule

-- | Check an `open` statement and preform the import.

checkOpen :: QName -> Access -> ScopeM ()
checkOpen q acc = importContent =<< do
  keepPublicAs acc <$> (getModule <=< lookupModule) q

-- * Components

-- | Push a new empty module onto the context.

newModule :: Name -> ScopeM ()
newModule x = push (x, emptyModule)

-- | Pop the top module, bind it in the signature, and return its uid.

closeModule :: ScopeM AName
closeModule = do
  u <- currentModule
  m <- snd <$> pop
  defineModule u m
  return u

-- | Add a binding to the current module.

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
      InScope u
        | null xs   -> return u
        | otherwise -> getModule u >>= \ m -> lookupInContentM xs m err
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
      InScope u
        | null xs   -> return (Just u)
        | otherwise -> lookupInContentM xs =<< getModule u

-- | Get defined module from signature.
--   Expects to find it there.

getModule :: AName -> ScopeM ModuleContent
getModule u =
  maybe (throwError $ ImpossibleUndefined u) return =<< do
    Map.lookup u <$> use sig

-- | Prepare module for 'open'.
--   Remove private bindings and modify public bindings according to 'Access'.

keepPublicAs :: Access -> ModuleContent -> ModuleContent
keepPublicAs acc = Map.mapMaybe $ keepPublicAs' acc

-- | Merge given content into current module.
--   Public import fails if it generates clashes with public names.

importContent :: ModuleContent -> ScopeM ()
importContent m = modifyCurrentModuleM $ \ orig -> do
  let mergeNameSets' ea eb = do { a <- ea; b <- eb; mergeNameSets a b }
  let (bad, good) =
        Map.mapEitherWithKey (\ x -> bimap (x,) id) $
          Map.unionWith mergeNameSets' (fmap Right orig) (fmap Right m)
  if Map.null bad
    then return good
    else throwError $ ConflictPublic $ map fst $ Map.toList bad


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
lookupInContent x = maybe NotInScope unambiguous . Map.lookup x
  where
  unambiguous :: NameSet -> InScope AName
  unambiguous (NameSet pu pr) =
    case maybeToList pu ++ Set.toList pr of
      []  -> NotInScope
      [u] -> InScope u
      us  -> Ambiguous us

-- | Make a singleton 'NameSet'.

unambiguousName :: Access -> AName -> NameSet
unambiguousName Public = (`NameSet` Set.empty) . Just
unambiguousName Private = NameSet Nothing . Set.singleton

-- | Restrict NameSet for import.
--   It collapses to 'Nothing' if there are no public names.

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

-- ** Context

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

modifyCurrentModuleM :: (ModuleContent -> ScopeM ModuleContent) -> ScopeM ()
modifyCurrentModuleM = (cxt . lensHead . _2 %==)

-- ** Signature

defineModule :: AName -> ModuleContent -> ScopeM ()
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

instance Pretty NameSet where
  pretty (NameSet pu pr) =
    case pub ++ priv of
      []  -> "∅"
      [d] -> d
      ds  -> braces . hcat . punctuate ", " $ ds
    where
    pub  = maybeToList . fmap (("public" <+>) . pretty) $ pu
    priv = map (("private" <+>) . pretty) $ Set.toList pr

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
    ConflictPublic [x]    -> "Name " <+> pretty x <+> " has already a public definition"
    ConflictPublic xs     -> "Names " <+> hcat (punctuate ", " $ map pretty xs) <+> " have already a public definition"
    ImpossibleUndefined u -> "Panic: couldn't find the definition of module " <+> pretty u

-- * Lens tools

lensHead :: Lens' [a] a
lensHead f (a:as) = (:as) <$> f a

infix 4 %==

-- | Modify a part of the state monadically.
(%==) :: MonadState o m => Lens' o i -> (i -> m i) -> m ()
l %== f = put =<< l f =<< get

-- * Generic utilities

firstSuccess :: Monad m => [m (Maybe a)] -> m (Maybe a)
firstSuccess = \case
  []   -> return Nothing
  m:ms -> m >>= \case
    Nothing  -> firstSuccess ms
    r@Just{} -> return r

-- | Adding to a <=1 collection may fail.

addMaybe :: a -> Maybe a -> Maybe (Maybe a)
addMaybe a Nothing = Just (Just a)
addMaybe a Just{}  = Nothing

addMaybes :: Maybe a -> Maybe a -> Maybe (Maybe a)
addMaybes Nothing  = Just
addMaybes (Just a) = addMaybe a
