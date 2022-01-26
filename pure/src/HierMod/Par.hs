{-# OPTIONS_GHC -w #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE PartialTypeSignatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module HierMod.Par
  ( happyError
  , myLexer
  , pProgram
  , pDecl
  , pListDecl
  , pListName
  ) where

import Prelude

import qualified HierMod.Abs
import HierMod.Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.21.0

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
newtype HappyWrap7 = HappyWrap7 (HierMod.Abs.Name)
happyIn7 :: (HierMod.Abs.Name) -> (HappyAbsSyn )
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap7 x)
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn ) -> HappyWrap7
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
newtype HappyWrap8 = HappyWrap8 (HierMod.Abs.Program)
happyIn8 :: (HierMod.Abs.Program) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap8 x)
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> HappyWrap8
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
newtype HappyWrap9 = HappyWrap9 (HierMod.Abs.Decl)
happyIn9 :: (HierMod.Abs.Decl) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap9 x)
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> HappyWrap9
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
newtype HappyWrap10 = HappyWrap10 ([HierMod.Abs.Decl])
happyIn10 :: ([HierMod.Abs.Decl]) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap10 x)
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> HappyWrap10
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
newtype HappyWrap11 = HappyWrap11 ([HierMod.Abs.Name])
happyIn11 :: ([HierMod.Abs.Name]) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap11 x)
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> HappyWrap11
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x20\x00\x00\x38\x00\x00\x0e\x00\x00\x40\x00\x00\x10\x00\x00\x00\x80\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x01\x00\x40\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x02\x00\x00\x04\x00\x10\x00\x00\x08\x00\xe0\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x20\x00\x00\x10\x00\xe0\x00\x00\x00\x01\x00\x0e\x00\x00\x20\x00\xe0\x00\x00\x00\x02\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram","%start_pDecl","%start_pListDecl","%start_pListName","Name","Program","Decl","ListDecl","ListName","'.'","';'","'module'","'open'","'private'","'public'","'where'","'{'","'}'","L_Name","%eof"]
        bit_start = st Prelude.* 22
        bit_end = (st Prelude.+ 1) Prelude.* 22
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..21]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x12\x00\x05\x00\x05\x00\xfa\xff\xfa\xff\x00\x00\x15\x00\x0c\x00\x16\x00\x0e\x00\x10\x00\x10\x00\x18\x00\x13\x00\x13\x00\x17\x00\x19\x00\x1a\x00\x1c\x00\x1e\x00\x05\x00\x1d\x00\x00\x00\x00\x00\x14\x00\x00\x00\x1f\x00\x1b\x00\x05\x00\x20\x00\x05\x00\x21\x00\x05\x00\x22\x00\x00\x00\x23\x00\x00\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x28\x00\x2b\x00\x09\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2e\x00\x02\x00\x00\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x30\x00\x00\x00\x00\x00\x0b\x00\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0d\x00\x00\x00\x0f\x00\x00\x00\x11\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\x00\x00\x00\x00\xf5\xff\x00\x00\x00\x00\xfb\xff\xf2\xff\x00\x00\xf4\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf7\xff\x00\x00\xf5\xff\x00\x00\xf1\xff\xf3\xff\x00\x00\xf6\xff\x00\x00\x00\x00\xf5\xff\x00\x00\xf5\xff\x00\x00\xf5\xff\x00\x00\xfa\xff\x00\x00\xf9\xff\xf8\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x00\x00\x00\x00\x00\x00\x0a\x00\x04\x00\x04\x00\x04\x00\x03\x00\x04\x00\x05\x00\x02\x00\x03\x00\x02\x00\x03\x00\x02\x00\x03\x00\x02\x00\x03\x00\x02\x00\x03\x00\x03\x00\x01\x00\x0b\x00\x02\x00\x0b\x00\x0a\x00\x03\x00\x08\x00\xff\xff\x0b\x00\xff\xff\x07\x00\x0a\x00\x06\x00\x08\x00\x0a\x00\x07\x00\x07\x00\x0a\x00\x08\x00\x01\x00\x09\x00\x09\x00\x09\x00\x02\x00\x00\x00\x00\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x06\x00\x06\x00\x06\x00\x06\x00\x07\x00\x12\x00\x16\x00\x0b\x00\x0c\x00\x0d\x00\x08\x00\x09\x00\x08\x00\x17\x00\x08\x00\x21\x00\x08\x00\x1f\x00\x08\x00\x23\x00\x10\x00\x16\x00\xff\xff\x15\x00\xff\xff\x06\x00\x12\x00\x1f\x00\x00\x00\xff\xff\x00\x00\x1c\x00\x06\x00\x1a\x00\x1d\x00\x06\x00\x19\x00\x1e\x00\x06\x00\x21\x00\x0e\x00\x25\x00\x23\x00\x26\x00\x0d\x00\x13\x00\x10\x00\x1a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (4, 14) [
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14)
	]

happy_n_terms = 12 :: Prelude.Int
happy_n_nonterms = 5 :: Prelude.Int

happyReduce_4 = happySpecReduce_1  0# happyReduction_4
happyReduction_4 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (T_Name happy_var_1)) -> 
	happyIn7
		 (HierMod.Abs.Name happy_var_1
	)}

happyReduce_5 = happyReduce 6# 1# happyReduction_5
happyReduction_5 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut7 happy_x_2 of { (HappyWrap7 happy_var_2) -> 
	case happyOut10 happy_x_5 of { (HappyWrap10 happy_var_5) -> 
	happyIn8
		 (HierMod.Abs.Prg happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_6 = happyReduce 6# 2# happyReduction_6
happyReduction_6 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut7 happy_x_2 of { (HappyWrap7 happy_var_2) -> 
	case happyOut10 happy_x_5 of { (HappyWrap10 happy_var_5) -> 
	happyIn9
		 (HierMod.Abs.Modl happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_7 = happyReduce 7# 2# happyReduction_7
happyReduction_7 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut7 happy_x_3 of { (HappyWrap7 happy_var_3) -> 
	case happyOut10 happy_x_6 of { (HappyWrap10 happy_var_6) -> 
	happyIn9
		 (HierMod.Abs.PrivateModl happy_var_3 happy_var_6
	) `HappyStk` happyRest}}

happyReduce_8 = happySpecReduce_2  2# happyReduction_8
happyReduction_8 happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_2 of { (HappyWrap11 happy_var_2) -> 
	happyIn9
		 (HierMod.Abs.Open happy_var_2
	)}

happyReduce_9 = happySpecReduce_3  2# happyReduction_9
happyReduction_9 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_2 of { (HappyWrap11 happy_var_2) -> 
	happyIn9
		 (HierMod.Abs.OpenPublic happy_var_2
	)}

happyReduce_10 = happySpecReduce_0  3# happyReduction_10
happyReduction_10  =  happyIn10
		 ([]
	)

happyReduce_11 = happySpecReduce_1  3# happyReduction_11
happyReduction_11 happy_x_1
	 =  case happyOut9 happy_x_1 of { (HappyWrap9 happy_var_1) -> 
	happyIn10
		 ((:[]) happy_var_1
	)}

happyReduce_12 = happySpecReduce_3  3# happyReduction_12
happyReduction_12 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_1 of { (HappyWrap9 happy_var_1) -> 
	case happyOut10 happy_x_3 of { (HappyWrap10 happy_var_3) -> 
	happyIn10
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_13 = happySpecReduce_1  4# happyReduction_13
happyReduction_13 happy_x_1
	 =  case happyOut7 happy_x_1 of { (HappyWrap7 happy_var_1) -> 
	happyIn11
		 ((:[]) happy_var_1
	)}

happyReduce_14 = happySpecReduce_3  4# happyReduction_14
happyReduction_14 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_1 of { (HappyWrap7 happy_var_1) -> 
	case happyOut11 happy_x_3 of { (HappyWrap11 happy_var_3) -> 
	happyIn11
		 ((:) happy_var_1 happy_var_3
	)}}

happyNewToken action sts stk [] =
	happyDoAction 11# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (T_Name happy_dollar_dollar) -> cont 10#;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 11# tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = ((>>=))
happyReturn :: () => a -> Err a
happyReturn = (return)
happyThen1 m k tks = ((>>=)) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pProgram tks = happySomeParser where
 happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (let {(HappyWrap8 x') = happyOut8 x} in x'))

pDecl tks = happySomeParser where
 happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (let {(HappyWrap9 x') = happyOut9 x} in x'))

pListDecl tks = happySomeParser where
 happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (let {(HappyWrap10 x') = happyOut10 x} in x'))

pListName tks = happySomeParser where
 happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (let {(HappyWrap11 x') = happyOut11 x} in x'))

happySeq = happyDontSeq


type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens
#define HAPPY_ARRAY 1
#define HAPPY_GHC 1
#define HAPPY_COERCE 1
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $

#ifdef HAPPY_GHC
#  if !defined(__GLASGOW_HASKELL__)
#    error `HAPPY_GHC` is defined but this code isn't being built with GHC.
#  endif
#  define ILIT(n) n#
#  define IBOX(n) (Happy_GHC_Exts.I# (n))
#  define FAST_INT Happy_GHC_Exts.Int#
-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#  if __GLASGOW_HASKELL__ > 706
#    define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Prelude.Bool)
#    define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Prelude.Bool)
#    define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Prelude.Bool)
#  else
#    define LT(n,m) (n Happy_GHC_Exts.<# m)
#    define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#    define EQ(n,m) (n Happy_GHC_Exts.==# m)
#  endif
#  define PLUS(n,m) (n Happy_GHC_Exts.+# m)
#  define MINUS(n,m) (n Happy_GHC_Exts.-# m)
#  define TIMES(n,m) (n Happy_GHC_Exts.*# m)
#  define NEGATE(n) (Happy_GHC_Exts.negateInt# (n))
#  define IF_GHC(x) (x)
#else
#  define ILIT(n) (n)
#  define IBOX(n) (n)
#  define FAST_INT Prelude.Int
#  define LT(n,m) (n Prelude.< m)
#  define GTE(n,m) (n Prelude.>= m)
#  define EQ(n,m) (n Prelude.== m)
#  define PLUS(n,m) (n Prelude.+ m)
#  define MINUS(n,m) (n Prelude.- m)
#  define TIMES(n,m) (n Prelude.* m)
#  define NEGATE(n) (Prelude.negate (n))
#  define IF_GHC(x)
#endif

data Happy_IntList = HappyCons FAST_INT Happy_IntList

#if defined(HAPPY_ARRAY)
#  define CONS(h,t) (HappyCons (h) (t))
#else
#  define CONS(h,t) ((h):(t))
#endif

#if defined(HAPPY_ARRAY)
#  define ERROR_TOK ILIT(0)
#  define DO_ACTION(state,i,tk,sts,stk) happyDoAction i tk state sts (stk)
#  define HAPPYSTATE(i) (i)
#  define GOTO(action) happyGoto
#  define IF_ARRAYS(x) (x)
#else
#  define ERROR_TOK ILIT(1)
#  define DO_ACTION(state,i,tk,sts,stk) state i i tk HAPPYSTATE(state) sts (stk)
#  define HAPPYSTATE(i) (HappyState (i))
#  define GOTO(action) action
#  define IF_ARRAYS(x)
#endif

#if defined(HAPPY_COERCE)
#  if !defined(HAPPY_GHC)
#    error `HAPPY_COERCE` requires `HAPPY_GHC`
#  endif
#  define GET_ERROR_TOKEN(x)  (case Happy_GHC_Exts.unsafeCoerce# x of { IBOX(i) -> i })
#  define MK_ERROR_TOKEN(i)   (Happy_GHC_Exts.unsafeCoerce# IBOX(i))
#  define MK_TOKEN(x)         (happyInTok (x))
#else
#  define GET_ERROR_TOKEN(x)  (case x of { HappyErrorToken IBOX(i) -> i })
#  define MK_ERROR_TOKEN(i)   (HappyErrorToken IBOX(i))
#  define MK_TOKEN(x)         (HappyTerminal (x))
#endif

#if defined(HAPPY_DEBUG)
#  define DEBUG_TRACE(s)    (happyTrace (s)) $
happyTrace string expr = Happy_System_IO_Unsafe.unsafePerformIO $ do
    Happy_System_IO.hPutStr Happy_System_IO.stderr string
    return expr
#else
#  define DEBUG_TRACE(s)    {- nothing -}
#endif

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept ERROR_TOK tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) =
        IF_GHC(happyTcHack j IF_ARRAYS(happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

#if defined(HAPPY_ARRAY)

happyDoAction i tk st
        = DEBUG_TRACE("state: " ++ show IBOX(st) ++
                      ",\ttoken: " ++ show IBOX(i) ++
                      ",\taction: ")
          case action of
                ILIT(0)           -> DEBUG_TRACE("fail.\n")
                                     happyFail (happyExpListPerState (IBOX(st) :: Prelude.Int)) i tk st
                ILIT(-1)          -> DEBUG_TRACE("accept.\n")
                                     happyAccept i tk st
                n | LT(n,(ILIT(0) :: FAST_INT)) -> DEBUG_TRACE("reduce (rule " ++ show rule
                                                               ++ ")")
                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = IBOX(NEGATE(PLUS(n,(ILIT(1) :: FAST_INT))))
                n                 -> DEBUG_TRACE("shift, enter state "
                                                 ++ show IBOX(new_state)
                                                 ++ "\n")
                                     happyShift new_state i tk st
                                     where new_state = MINUS(n,(ILIT(1) :: FAST_INT))
   where off    = happyAdjustOffset (indexShortOffAddr happyActOffsets st)
         off_i  = PLUS(off, i)
         check  = if GTE(off_i,(ILIT(0) :: FAST_INT))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else Prelude.False
         action
          | check     = indexShortOffAddr happyTable off_i
          | Prelude.otherwise = indexShortOffAddr happyDefActions st

#endif /* HAPPY_ARRAY */

#ifdef HAPPY_GHC
indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#
#else
indexShortOffAddr arr off = arr Happy_Data_Array.! off
#endif

{-# INLINE happyLt #-}
happyLt x y = LT(x,y)

#ifdef HAPPY_GHC
readArrayBit arr bit =
    Bits.testBit IBOX(indexShortOffAddr arr ((unbox_int bit) `Happy_GHC_Exts.iShiftRA#` 4#)) (bit `Prelude.mod` 16)
  where unbox_int (Happy_GHC_Exts.I# x) = x
#else
readArrayBit arr bit =
    Bits.testBit IBOX(indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)
#endif

#ifdef HAPPY_GHC
data HappyAddr = HappyA# Happy_GHC_Exts.Addr#
#endif

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)

#if !defined(HAPPY_ARRAY)

newtype HappyState b c = HappyState
        (FAST_INT ->                    -- token number
         FAST_INT ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)

#endif

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state ERROR_TOK tk st sts stk@(x `HappyStk` _) =
     let i = GET_ERROR_TOKEN(x) in
--     trace "shifting the error token" $
     DO_ACTION(new_state,i,tk,CONS(st,sts),stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state CONS(st,sts) (MK_TOKEN(tk)`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn ERROR_TOK tk st sts stk
     = happyFail [] ERROR_TOK tk st sts stk
happySpecReduce_0 nt fn j tk st@(HAPPYSTATE(action)) sts stk
     = GOTO(action) nt j tk st CONS(st,sts) (fn `HappyStk` stk)

happySpecReduce_1 i fn ERROR_TOK tk st sts stk
     = happyFail [] ERROR_TOK tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(CONS(st@HAPPYSTATE(action),_)) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (GOTO(action) nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn ERROR_TOK tk st sts stk
     = happyFail [] ERROR_TOK tk st sts stk
happySpecReduce_2 nt fn j tk _ CONS(_,sts@(CONS(st@HAPPYSTATE(action),_))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (GOTO(action) nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn ERROR_TOK tk st sts stk
     = happyFail [] ERROR_TOK tk st sts stk
happySpecReduce_3 nt fn j tk _ CONS(_,CONS(_,sts@(CONS(st@HAPPYSTATE(action),_)))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (GOTO(action) nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn ERROR_TOK tk st sts stk
     = happyFail [] ERROR_TOK tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop MINUS(k,(ILIT(1) :: FAST_INT)) sts of
         sts1@(CONS(st1@HAPPYSTATE(action),_)) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (GOTO(action) nt j tk st1 sts1 r)

happyMonadReduce k nt fn ERROR_TOK tk st sts stk
     = happyFail [] ERROR_TOK tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k CONS(st,sts) of
        sts1@(CONS(st1@HAPPYSTATE(action),_)) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> GOTO(action) nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn ERROR_TOK tk st sts stk
     = happyFail [] ERROR_TOK tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k CONS(st,sts) of
        sts1@(CONS(st1@HAPPYSTATE(action),_)) ->
         let drop_stk = happyDropStk k stk
#if defined(HAPPY_ARRAY)
             off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st1)
             off_i = PLUS(off, nt)
             new_state = indexShortOffAddr happyTable off_i
#else
             _ = nt :: FAST_INT
             new_state = action
#endif
          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop ILIT(0) l = l
happyDrop n CONS(_,t) = happyDrop MINUS(n,(ILIT(1) :: FAST_INT)) t

happyDropStk ILIT(0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk MINUS(n,(ILIT(1)::FAST_INT)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

#if defined(HAPPY_ARRAY)
happyGoto nt j tk st =
   DEBUG_TRACE(", goto state " ++ show IBOX(new_state) ++ "\n")
   happyDoAction j tk new_state
   where off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st)
         off_i = PLUS(off, nt)
         new_state = indexShortOffAddr happyTable off_i
#else
happyGoto action j tk st = action j j tk (HappyState action)
#endif

-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist ERROR_TOK tk old_st _ stk@(x `HappyStk` _) =
     let i = GET_ERROR_TOKEN(x) in
--      trace "failing" $
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts)
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk HAPPYSTATE(action) sts stk =
--      trace "entering error recovery" $
        DO_ACTION(action,ERROR_TOK,tk,sts, MK_ERROR_TOKEN(i) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions

#if defined(HAPPY_GHC)
happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}
#endif

-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

#if defined(HAPPY_ARRAY)
{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}
#endif
{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
