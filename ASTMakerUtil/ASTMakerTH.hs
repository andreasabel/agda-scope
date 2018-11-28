{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards  #-}

module ASTMakerTH where



import qualified Data.Text as T

import Control.Monad.Trans.Except
import Control.Monad.State

import Data.List
import Data.Maybe

import Language.Haskell.TH

import qualified Data.Map as DM
import qualified Data.Set as DS

import System.FilePath

import Control.Monad


type MySt = DS.Set String

type MyQ a = StateT MySt Q a

type GenAgSt = (DS.Set Language.Haskell.TH.Name,DS.Set AgD)

tshow :: (Show a) => a -> String
tshow x = case takeExtension $ show x of
  [] -> show x
  r -> tail r

ushow [] = []
ushow (x:'_':y) = x:[]
ushow (x:y) = x:(ushow y)

prettyCustom (OrigName n) = fixNames $ tshow n
prettyCustom (CustomTyvar n) = ushow $ tshow n
prettyCustom (CustomTuple 0) = "⊥"
prettyCustom t = error $ show ("prettyCustom",t)

prettyLinearType (LinearType (CustomList) xs) = "(List (" ++ (intercalate " " $ map prettyLinearType xs) ++ "))"
prettyLinearType (LinearType (CustomTuple 2) [x1,x2]) = "(" ++ prettyLinearType x1 ++ " ×  " ++ prettyLinearType x2 ++ ")"
prettyLinearType (LinearType x xs) = "(" ++ prettyCustom x ++ "  " ++ (intercalate " " $ map prettyLinearType xs) ++ ")"
prettyLinearType (LF x) = prettyCustom x

fixNames "Set" = "SSet"
fixNames a = fmap (\x -> case x of
                    '_' -> 'U'
                    t -> t
                ) a

renderAgCon (AgCon {..}) = (tshow agcName)++"C" ++ " : " ++ (intercalate " → " $ map prettyLinearType agcArgCon)

renderAgD :: AgD -> String
-- renderAgD = show
renderAgD o@(AgT {..}) = fixNames $ tshow agtName ++ " : "
  ++ ((case length agtArgs of
       0 -> id
       _ -> (flip (++) " → ")) $ (intercalate " → " $ map (\x -> "Set") agtArgs))
  ++ (intercalate " → " $ map (\x -> (case x of
             0 -> id
             1 -> (flip (++) " → ")
             _ -> (flip (++) " → ") . (((++) "(") . (flip (++) ")"))) $ intercalate " → " $ replicate x "Set") agtFtN)
  ++ " Set\n" ++
  (fixNames $ tshow agtName) ++ " " ++ 
  case agtArgs of
    [] -> ""
    xs -> (intercalate " " $ map (ushow . show . tyvarName) xs)
  ++ " = " ++ prettyLinearType agtUnderlyingType
--   ++ "\n\n-- "++ show agtFtN
renderAgD o@(AgD {..}) = "data " ++ (fixNames $ tshow agdName)
  ++ magsP ++ " : Set where\n\t" ++
  (intercalate "\n\t" $ ((map (\zz -> fixNames $ renderAgCon zz ++
                                case length $ agcArgCon zz of
                                  0 -> ""
                                  _ -> " → "
                                ++ (fixNames $ tshow agdName) ++ " " ++ mags) agdCons) ))
  where
    magsP = case agdArgs of
      [] -> ""
      ags -> " ( " ++ mags ++ " : Set )"
    mags = (intercalate " " $ map (ushow . show . tyvarName) agdArgs)
    
  -- ++ "\n\n-- " ++ show o
renderAgD _ = ""

render :: DS.Set AgD -> String
render x = intercalate "\n\n" $ map renderAgD $ DS.toList x

killdots = filter (\x -> not ((==) '.' x))

renderPragma (AgD {..}) = ("{-# COMPILE GHC "++ (fixNames $ tshow agdName) ++ " = data " ++ (fixNames $ tshow agdName) ++ " ( " ++ (intercalate " | " $ map ((flip (++) "C") . tshow . agcName) agdCons) ++ " ) #-}")
renderPragma (AgT {..}) = ""

renderModule :: Module AgD -> String
renderModule (Module m) = (intercalate "\n\n " $ (map (\(zk,zv) -> "-- split-here :module ♖"++killdots zk++" where\n"++((intercalate "\n" $ map (\x -> "open import "++x) $ DS.toList $ DS.fromList $ map (killdots . init . fst . revmodName) $ filter (\x -> not $ isInfixOf (killdots zk) (killdots x)) $ intercalate [] $ map findImports zv))++"\nmutual\n" ++(intercalate "\n" $ map (\x -> "\t"++x) $ lines (render $ DS.fromList zv)) ++ "\n\n" ++ (intercalate "\n\n" $ filter (not . (==) "") $ map renderPragma zv))) $ DM.toList m)

hask2ag'' :: String -> Q Exp
hask2ag'' typ = do
  Just tnam <- lookupTypeName typ
  let ppq = flip runStateT mempty $ hask2ag tnam
  (_,(_,pp2)) <- runQ ppq
  let pp3 = DS.filter (\x -> not $ "GHC"  `isInfixOf` (show $ getAgDName x) ) $  pp2
  --let pp = fixAgts (DS.toList pp3,[])
  -- let kk = fixAgds $ (partition (not . isAgT) pp,[])
--  let gg = (intercalate "\n\n" $ map show $ DS.toList pp3) ++ "\n\n----====----====---\n\n" ++ (render $ DS.fromList pp)
  let pp =   foldr (\za zb -> modularize za zb) mempty $ DS.toList pp3
  let gg' = (renderModule $ pp)
  let gg = gg' -- "module ztmp1 where\n\nopen import Data.List\n\n" ++ 
  [e|gg|]


isAgT (AgT {..}) = True
isAgT _ = False


prepareTyp :: Type -> StateT (GenAgSt) Q ()
prepareTyp (ConT c) = hask2ag c
prepareTyp (ListT) = return ()
prepareTyp (VarT _) = return ()
prepareTyp (TupleT _) = return ()
prepareTyp (AppT a b) = do
  prepareTyp a
  prepareTyp b
prepareTyp t = error $ show ("preparetyp", t)

prepareCon :: Con -> StateT (GenAgSt) Q ()
prepareCon (NormalC cnam cbtypes) = do
  let typs = map snd cbtypes
  mapM prepareTyp typs
  hask2ag cnam
prepareCon (RecC cnam cbtypes) = do
  let typs = map (\(_,_,a) -> a) cbtypes
  mapM prepareTyp typs
  hask2ag cnam
prepareCon t = error $ show ("prepareCon", t)


runConsumer a [] = a
runConsumer (ai:ac) (0:[]) = (ai - 1):ac
runConsumer (ai:ac) (bi:[]) = case ai - bi of
  0 -> ac
  _ -> (ai-bi):ac
runConsumer x y = error $ show ("runConsumer",x,y)

consume n = [n]

getFullType :: Type -> StateT (GenAgSt) Q ([Int])
getFullType ntyp = case ntyp of
    AppT a b -> do
      ia <- getFullType a
      ib <- getFullType b
      return $ runConsumer (ia) (ib)
    TupleT n -> return $ consume n
    ListT -> return $ consume 1
    VarT _ -> return $ consume 0
    ConT a -> do
      rnam <- lift $ reify a
      case rnam of
        TyConI ttycon -> do
          case ttycon of
            NewtypeD _ knam kvars _ kcn _ -> do
              return $ consume $ length kvars
            DataD _ knam kvars _ kcns _ -> do
              return $ consume $ length kvars
            TySynD _ _ htyp -> do
              getFullType htyp
    t -> error $ show ("getfulltype",t)
          

hask2ag :: Language.Haskell.TH.Name -> StateT (GenAgSt) Q ()
hask2ag tnam = do
  rnam <- lift $ reify tnam
  (cst1,cst2) <- get
  case DS.member (tnam) cst1 of
    True -> return ()
    False -> do
      modify (\(x,y) -> (DS.insert tnam x,y))
      case rnam of
        TyConI tycon -> do
          case tycon of
            DataD _ dnam tyvars _ cns _ -> do
              mapM prepareCon cns
              let a = AgD {agdName = dnam, agdArgs = tyvars, agdCons = map mkCon cns}
              pushDataInfo a
            NewtypeD _ dnam tyvars _ cn _ -> do
              prepareCon cn
              let a = AgD {agdName = dnam, agdArgs = tyvars, agdCons = [mkCon cn]}
              pushDataInfo a
            TySynD dnam tyvars ttyp -> do
              prepareTyp ttyp
              ftl <- getFullType ttyp
              let a = AgT {agtName = dnam, agtArgs = tyvars, agtUnderlyingType = linearizeAppT ttyp, agtFtN = ftl}
              pushDataInfo a
            _ -> error $ show ("wow implement",tycon)
        PrimTyConI pnam _ _ -> do
          let a = AgPrim {agpName = pnam}
          pushDataInfo a
        DataConI _ _ _ -> do
          return ()
        _ -> error $ show ("wow2 implement",rnam)
  return ()

pushDataInfo :: AgD -> StateT (GenAgSt) Q ()
pushDataInfo a = do
  modify (\(y,x) -> (y,DS.insert a x))

data AgCon = AgCon {agcName :: Language.Haskell.TH.Name, agcImpli :: [String],agcArgCon :: [LinearType]} deriving Show

mkCon :: Con -> AgCon
mkCon (NormalC nm btyp) = AgCon {agcName = nm, agcImpli = [], agcArgCon = map (linearizeAppT . snd)  btyp}
mkCon (RecC nm btyp) = AgCon {agcName = nm, agcImpli = [], agcArgCon = map (linearizeAppT . (\(_,_,z) -> z))  btyp}
mkCon (t) = error $ show ("mkcon",t)

data AgD =
    AgD {agdName :: Language.Haskell.TH.Name , agdArgs :: [TyVarBndr], agdCons :: [AgCon]}
  | AgT {agtName :: Language.Haskell.TH.Name , agtArgs :: [TyVarBndr], agtUnderlyingType :: LinearType,agtFtN :: [Int]}
  | AgPrim {agpName :: Language.Haskell.TH.Name}
  deriving Show



getAgDName (AgD {..}) = agdName
getAgDName (AgT {..}) = agtName
getAgDName (AgPrim {..}) = agpName

data CustomName = OrigName Language.Haskell.TH.Name | CustomTuple Int | CustomList | CustomTyvar Name deriving (Ord,Eq)

instance Show CustomName where
  show (OrigName x) = "O@" ++ show x
  show (CustomTuple n) = "T" ++ show n ++ "@"
  show (CustomList) = "L@"
  show (CustomTyvar a) = "Y@" ++ show a
  show t = error $ show ("showCustomName")
  

data LinearType = LinearType CustomName [LinearType] | LF CustomName 

instance Show LinearType where
  show (LinearType x xs) = "(" ++ show x ++ ":: " ++ (intercalate " → " $ map show xs) ++ ")"
  show (LF x) = "||"++show x

linearizeAppT :: Type -> LinearType
linearizeAppT (VarT a) = LF $ CustomTyvar a
linearizeAppT (ConT a) = LF $ OrigName a
linearizeAppT (TupleT x) = LF $ CustomTuple x
linearizeAppT (ListT) = LF $ CustomList
linearizeAppT (AppT a b) = case linearizeAppT a of
  LinearType x xs -> LinearType x (xs++[linearizeAppT b])
  LF x -> LinearType x [linearizeAppT b]
linearizeAppT t = error $ show ("linearizeappt",t)

-- convertTypeToData :: AgD -> StateT (GenAgSt) Q AgD
-- convertTypeToData t@(AgD {..}) = return t
-- convertTypeToData t@(AgPrim {..}) = return t
-- convertTypeToData t@(AgT {..}) = do
--   undefined

instance Eq (AgD) where
  a == b = getAgDName a == getAgDName b
  
instance Ord (AgD) where
  compare (a) (b) = (compare (getAgDName a) (getAgDName b)) 
  

fixAgts :: ([AgD],[AgD]) -> [AgD]
fixAgts ([],x) = x
fixAgts (x@(AgT {..}):xs,y) = case containsAgT (agtUnderlyingType) xs of
  Just j ->  fixAgts (xs++[x],y)
  Nothing -> case containsAgT (agtUnderlyingType) y of
    Just k -> fixAgts ((x {agtUnderlyingType = fixUnderly  (DS.fromList y) k agtUnderlyingType}):xs,y)
    Nothing -> fixAgts (xs,x:y)
fixAgts (x:xs,y) = fixAgts (xs,x:y)

fixUnderly :: DS.Set AgD  -> Language.Haskell.TH.Name ->  LinearType -> LinearType
fixUnderly db n o@(LinearType lt lts) | and $ (isJust $ n `customNameEq` lt):(map (\zz -> not $ isJust $ containsAgT zz $ DS.toList db) lts) = let a = head $ DS.toList $ DS.filter (\y -> getAgDName y == n) db in  jmap lts (agtUnderlyingType a) (map tyvarName $ agtArgs a)
                                      | otherwise = LinearType lt $  map (fixUnderly db n) lts
fixUnderly db n o@(LF lt) | isJust $ n `customNameEq` lt = let a = head $ DS.toList $ DS.filter (\y -> getAgDName y == n) db in  (agtUnderlyingType a)
                          | otherwise = o


tyvarName (PlainTV n)= n
tyvarName (KindedTV n _)=n

linearTypeName (LinearType n _) = n
customNameName (OrigName n)=n
customNameName t =error $ show t

jmap :: [LinearType] -> LinearType -> [Language.Haskell.TH.Name] -> LinearType
jmap lts (LinearType x y) w = LinearType x (map (jmap2 db) y)
  where
    db = DM.fromList (zip w lts)

jmap2 :: DM.Map Language.Haskell.TH.Name LinearType -> LinearType -> LinearType
jmap2 db (LinearType x y) = LinearType x $ map (jmap2 db) y
jmap2 db (LF x) = case DM.lookup (customNameName x) db of
  Nothing -> LF x
  Just j -> j


containsAgT :: LinearType ->  [AgD] -> Maybe Language.Haskell.TH.Name
containsAgT a [] = Nothing
containsAgT o@(LF a) (x:xs) = case  customNameEq (getAgDName x) a of
  Just j -> Just j
  Nothing -> containsAgT o xs
containsAgT o@(LinearType a as) (x:xs) = case  filter isJust $ (customNameEq (getAgDName x) a):(map (flip containsAgT (x:xs)) as) of
  (Just k):_ -> Just k
  [] -> containsAgT o xs

customNameEq :: Language.Haskell.TH.Name -> CustomName -> Maybe Language.Haskell.TH.Name
customNameEq a (OrigName o) | a==o = Just o
customNameEq _ _ = Nothing

fixAgds :: (([AgD],[AgD]),[AgD]) -> [AgD]
fixAgds (([],y),x) = x++y
fixAgds ((x@(AgD {..}):xs,y),r) = case filter (isJust) $ tmp of
  [] -> fixAgds ((xs,y),x:r)
  ress -> fixAgds ((xs++[newx],y),r)
  where
    tmp = map (fixCon y) agdCons
    newx = x {agdCons = (map (nothingOrig) $ zip agdCons tmp)}
fixAgds ((x:xs,y),r) = fixAgds ((xs,y),x:r)


fixCon :: [AgD] -> AgCon -> Maybe AgCon
fixCon db o@(AgCon {..}) = case filter isJust tmp of
  [] -> Nothing
  _ -> Just $ o {agcArgCon = map nothingOrig $ zip agcArgCon $ tmp}
  where
    tmp = map (fixConArg db) agcArgCon

fixConArg :: [AgD] -> LinearType -> Maybe LinearType
fixConArg db o@(LF l) = case containsAgT o db of
  Nothing -> Nothing
  Just j -> let a = head $ DS.toList $ DS.filter (\y -> getAgDName y == j) (DS.fromList db) in  Just $ jmap [o] (agtUnderlyingType a) (map tyvarName $ agtArgs a) -- good
fixConArg db o@(LinearType l ls) = case containsAgT o db of
  Nothing -> Nothing
  Just j -> case filter isJust tmp of
    [] -> let a = head $ DS.toList $ DS.filter (\y -> getAgDName y == j) (DS.fromList db) in  Just $ jmap ls (agtUnderlyingType a) (map tyvarName $ agtArgs a) -- good
    _ -> Just $ LinearType l $ (map nothingOrig $ zip ls $ map (fixConArg db) ls)
    where
      tmp = map (flip containsAgT db) ls
nothingOrig :: (a, Maybe a) -> a
nothingOrig (x,Nothing) = x
nothingOrig (x,Just y) = y


data Module a = Module (DM.Map String [a])

instance Semigroup (Module a) where
  (<>) a b = undefined
instance Monoid (Module a) where
  mempty = Module mempty

modName x = (takeWhile f x,dropWhile f x)
  where
    f = \x -> not ((==) '.' x)
revmodName x = (reverse $ dropWhile f (reverse x),reverse $ takeWhile f (reverse x))
  where
    f = \x -> not ((==) '.' x)

modularize :: AgD -> Module AgD  -> Module AgD
modularize x m = modularize' x (show $ getAgDName x) m

modularize' :: AgD -> String -> Module AgD -> (Module AgD)
modularize' s x (Module m) = case revmodName x of
  ("",lx) -> case DM.lookup "" m of
    Nothing -> Module $ DM.insert "" [s] m
    Just (a) -> Module $ DM.update (\a -> Just $ s:a) "" m
  (lxr',lx) -> case DM.lookup lxr m of
    Nothing -> Module $ DM.insert lxr [s] m
    Just (a) -> Module $ DM.update (\a -> Just (s:a)) lxr m
    where
      lxr = init lxr'


findImports :: AgD -> [String]
findImports (AgD {..}) = intercalate [] $ map findImportsAgCon agdCons
findImports (AgT {..}) = findImportsLinearType agtUnderlyingType

findImportsAgCon :: AgCon -> [String]
findImportsAgCon (AgCon {..}) = (show agcName):(intercalate [] $ map findImportsLinearType agcArgCon)


findImportsLinearType :: LinearType -> [String]
findImportsLinearType (LinearType x xs) = (findImportsCustomName x) ++ (intercalate [] $ map findImportsLinearType xs )
findImportsLinearType (LF x) = (findImportsCustomName x)


findImportsCustomName :: CustomName -> [String]
findImportsCustomName (OrigName n) | mnam == "Maybe" = ["Data+Maybe.Maybe"]
                                   | mnam == "String" = ["Data+String.String"]
                                   | mnam == "Bool" = ["Data+Bool.Bool"]
                                   | mnam == "Double" = ["♖GHC.Types.Double"]
                                   | mnam == "Char" = ["Data+Char.Char"]
                                   -- | mnam == "Array" = ["Data+Text.Array"]
                                   | mnam == "ByteArray#" = ["♖GHC.Prim.ByteArray#"]
                                   | otherwise = ["♖" ++ show n]
  where
    mnam = snd $ revmodName (show n)
findImportsCustomName (CustomList) = ["Data+List.List"]
findImportsCustomName (CustomTuple 0) = ["Data+Empty.Bot"]
findImportsCustomName (CustomTuple 2) = ["Data+Product.Prod2"]
findImportsCustomName (CustomTuple _) = []
findImportsCustomName (CustomTyvar _) = []




-- data Module a = Module (DM.Map String ((Module a), [a]))

-- instance Semigroup (Module a) where
--   (<>) a b = undefined
-- instance Monoid (Module a) where
--   mempty = Module mempty

-- modName x = (takeWhile f x,dropWhile f x)
--   where
--     f = \x -> not ((==) '.' x)

-- modularize :: AgD -> Module AgD  -> Module AgD
-- modularize x m = modularize' x (show $ getAgDName x) m

-- modularize' :: AgD -> String -> Module AgD -> (Module AgD)
-- modularize' s x (Module m) = case modName x of
--   (lx,"") -> case DM.lookup lx m of
--     Nothing -> Module $ DM.insert lx (mempty,[s]) m
--     Just (jl,jr) -> Module $ DM.update (\_ -> Just (jl,s:jr)) lx m
--   (lx,'.':lxr) -> case DM.lookup lx m of
--     Nothing -> Module $ DM.insert lx (modularize' s lxr mempty,mempty) m
--     Just (jl,jr) -> Module $ DM.update (\_ -> Just $ ((modularize' s lxr jl),jr)) lx m
