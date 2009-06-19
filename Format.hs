{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}

-- A library for printing formats to strings, reminiscent of the C sprintf
-- function. This library uses Template Haskell to ensure the arguments are
-- statically well-typed. Derived from work by Oleg Kiselyov.

module Format (sprintf, sprintff, fmt, fmtq) where

--------------------------------------------------------------------------------

import Prelude hiding ((^))
import qualified Prelude (Show, show)

import Language.Haskell.TH
import Language.Haskell.TH.Quote

import Generics.EMGM (Rep)
import qualified Generics.EMGM as EMGM (Show, show)

import Data.Data (Data)
import Data.Generics.Text (gshow)

import Data.Ratio (Ratio)

--------------------------------------------------------------------------------

-- A language of format descriptors
data Fmt
  = Literal String
  | EMGMFmt
  | SYBFmt
  | StringFmt
  | ShowFmt
  | NumFmt
  | RealFmt
  | IntFmt
  | IntegerFmt
  | FloatFmt
  | DoubleFmt
  | RatioFmt
  | CharFmt
  deriving (Eq, Show)

-- Parse a character code to get a format descriptor
fmtOf :: Char -> Maybe Fmt
fmtOf c =
  case c of
    'e' -> Just EMGMFmt
    'y' -> Just SYBFmt
    's' -> Just StringFmt
    'S' -> Just ShowFmt
    'N' -> Just NumFmt
    'R' -> Just RealFmt
    'i' -> Just IntFmt
    'n' -> Just IntegerFmt
    'f' -> Just FloatFmt
    'd' -> Just DoubleFmt
    'r' -> Just RatioFmt
    'c' -> Just CharFmt
    _   -> Nothing

--------------------------------------------------------------------------------

-- Interpret a literal or a format descriptor into generated code.
expOf :: Fmt -> ExpQ
expOf (Literal s)  = [| literal s                                      |]
expOf EMGMFmt      = [| emgmFmt                                        |]
expOf SYBFmt       = [| sybFmt                                         |]
expOf StringFmt    = [| stringFmt                                      |]
expOf ShowFmt      = [| showFmt                                        |]
expOf NumFmt       = [| showFmt :: Num a => Formatter a w              |]
expOf RealFmt      = [| showFmt :: Real a => Formatter a w             |]
expOf IntFmt       = [| showFmt :: Formatter Int w                     |]
expOf IntegerFmt   = [| showFmt :: Formatter Integer w                 |]
expOf FloatFmt     = [| showFmt :: Formatter Float w                   |]
expOf DoubleFmt    = [| showFmt :: Formatter Double w                  |]
expOf RatioFmt     = [| showFmt :: Integral a => Formatter (Ratio a) w |]
expOf CharFmt      = [| showFmt :: Formatter Char w                    |]

literal :: String -> (String -> w) -> w
literal str k = k str

type Formatter a w = (String -> w) -> (a -> w)

stringFmt :: Formatter String w
stringFmt k x = k x

printFmt :: (a -> String) -> (String -> w) -> a -> w
printFmt f k x = k (f x)

emgmFmt :: (Rep EMGM.Show a) => Formatter a w
emgmFmt = printFmt EMGM.show

sybFmt :: (Data a) => Formatter a w
sybFmt = printFmt gshow

showFmt :: (Prelude.Show a) => Formatter a w
showFmt = printFmt Prelude.show

-- Composition of formatters
infixr 8 ^
(^) :: ((String -> w1) -> w1') -> ((String -> w2) -> w1) -> ((String -> w2) -> w1')
f1 ^ f2 = \k -> f1 (\s1 -> f2 (\s2 -> k (s1 ++ s2)))

-- Interpret a list of format descriptors to generate code.
interpret :: [Fmt] -> ExpQ
interpret [f]    = expOf f
interpret (f:fs) = [| $(expOf f) ^ $(interpret fs)|]

-- Parse the string into a list of literal strings and format descriptors.
parse :: String -> [Fmt]
parse input = result
  where
    (first,last) = break (=='%') input
    next =
      case last of
        ""           -> []
        '%':'%':rest -> Literal "%" : parse rest
        '%':c:rest   ->
          case fmtOf c of
            Nothing  -> error $ showString "Bad format: %" . showChar c $ ""
            Just f -> f : parse rest
    result = if null first then next else Literal first : next

--------------------------------------------------------------------------------

-- Exported functions

-- For use inside the spicing, e.g. @$(fmt "Hi!")@ generates @lit "Hi!@. Only
-- really useful if combined with 'sprintf'.
fmt :: String -> ExpQ
fmt = interpret . parse

-- For use as a quasi-quoter, e.g. @[$fmtq|Hi!|]@ generates @lit "Hi!@. Only
-- really useful if combined with 'sprintf'.
fmtq :: QuasiQuoter
fmtq = QuasiQuoter fmt (const $ error "A fmt cannot be used in a pattern.")

-- Print a formatted string with a variable number of arguments to a string. The
-- first argument is a Template Haskell spliced value using either 'fmt' or
-- 'fmtq'.
sprintf :: ((String -> String) -> a) -> a
sprintf f = f id

-- Same as 'sprintf' but used inside the splice with an extra parameter. Thus:
-- @$(sprintff "Hi!")@. Warning: The errors reported for this function may be
-- less comprehensible than those for 'sprintf'.
sprintff :: String -> ExpQ
sprintff s = [| $(fmt s) id |]

--------------------------------------------------------------------------------

-- Testing

showCode cde = runQ cde >>= putStrLn . pprint

tc1 = showCode (fmt "abc")
tc2 = showCode (fmt "Hello %e!")

test_lexFmt = and
  [ parse "Simple lit" == [Literal "Simple lit"]
  , parse "%s insert" == [StringFmt, Literal " insert"]
  , parse "insert %s here" == [Literal "insert ", StringFmt, Literal " here"]
  , parse "The value of %s is %i" == [Literal "The value of ", StringFmt, Literal " is ", IntFmt]
  , parse "A %e prints generically!" == [Literal "A ", EMGMFmt, Literal " prints generically!"]
  ]

