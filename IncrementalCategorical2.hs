{-# LANGUAGE MultiParamTypeClasses              #-}
{-# LANGUAGE FlexibleInstances                  #-}
{-# LANGUAGE FlexibleContexts                   #-}
{-# LANGUAGE ScopedTypeVariables                #-}
{-# LANGUAGE GeneralizedNewtypeDeriving         #-}
{-# LANGUAGE RankNTypes                         #-}
{-# LANGUAGE UndecidableInstances               #-}
{-# OPTIONS_GHC -Wall                           #-}

module IncrementalCategorical2 where

import Prelude hiding (succ)
import Text.Show
import Text.Read

--------------------------------------------------------------------------------
-- "Normal" fixed point
--------------------------------------------------------------------------------

newtype Mu f = In { out :: f (Mu f) }

instance (Eq (f (Mu f))) => Eq (Mu f) where
  In f == In g = f == g

instance (Ord (f (Mu f))) => Ord (Mu f) where
  In f `compare` In g = f `compare` g

instance (Show (f (Mu f))) => Show (Mu f) where
  showsPrec d (In f) = showParen (d > 10) $ showString "In " . showsPrec 11 f

instance (Read (f (Mu f))) => Read (Mu f) where
  readPrec = parens . prec 10 $ do
    Ident "In " <- lexP
    f <- step readPrec
    return (In f)

--------------------------------------------------------------------------------
-- "Attributed" fixed point
--------------------------------------------------------------------------------

-- Attribute: a triple of an inherited tag, a synthesized tag, and a functor.
data Att i s f r = Att { itag :: i, stag :: s, fun :: f r }
                   deriving (Eq, Ord, Show, Read)

-- Attributed fixed point: every recursive point is now a triple with the two
-- attributes and the original recursive point.
type AMu i s f = Mu (Att i s f)

fork :: (a -> b) -> (a -> c) -> a -> (b, c)
fork f g x = (f x, g x)

result :: AMu i s f -> (i, s)
result = fork itag stag . out

iresult :: AMu i s f -> i
iresult = fst . result

sresult :: AMu i s f -> s
sresult = snd . result

--------------------------------------------------------------------------------
-- Algebra and Coalgebra classes
--------------------------------------------------------------------------------

-- Attribute algebra
class (Functor f) => AAlgebra f i s where
  asyn :: i -> f (AMu i s f) -> (s, f (AMu i s f))

--------------------------------------------------------------------------------
-- Types for specific algebras
--------------------------------------------------------------------------------

data None = None deriving (Eq, Ord, Show, Read)

newtype Size = Size { getSize :: Int } deriving (Eq, Ord, Show, Read, Num)

newtype Sum = Sum { getSum :: Int } deriving (Eq, Ord, Show, Read, Num)

--------------------------------------------------------------------------------
-- Isomorphism between AMu and the unattributed functor
--------------------------------------------------------------------------------

ain' :: (Functor f) => (i -> f (AMu i s f) -> (s, f (AMu i s f))) -> i -> f (AMu i s f) -> AMu i s f
ain' sho i x = In (Att i s y)
  where
    (s, y) = sho i x

ain :: forall f i s. (AAlgebra f i s) => i -> f (AMu i s f) -> AMu i s f
ain = ain' asyn

-- Was: forget
aout :: AMu i s f -> (f (AMu i s f), i)
aout = fork fun itag . out

--------------------------------------------------------------------------------
-- Typical morphisms
--------------------------------------------------------------------------------

-- Catamorphism

cata' :: (Functor f) => (f a -> i -> a) -> AMu i s f -> a
cata' phi x = let (f, i) = aout x in phi (fmap (cata' phi) f) i

-- Anamorphism

-- TODO

-- Hylomorphism

-- A more general version
hylo_g' :: (Functor f) => (a -> f a) -> (g b -> b) -> (forall c. f c -> g c) -> a -> b
hylo_g' psi phi e = phi . e . fmap (hylo_g' psi phi e) . psi

hylo' :: (Functor f) => (f b -> b) -> (a -> f a) -> a -> b
hylo' phi psi = phi . fmap (hylo' phi psi) . psi

-- Paramorphism

-- This is simply a pair with record syntax to document the fields. 'inp' is
-- the original input value. 'rec' is the result of a recursive call.
data Para i s f a = Para { inp :: AMu i s f, rec :: a }

instance Functor (Para i s f) where
  fmap f (Para v a) = Para v (f a)

data Wrap i s f a = Wrap { unWrap :: f (Para i s f a), unInh :: i }

instance (Functor f) => Functor (Wrap i s f) where
  fmap f x = Wrap (fmap (fmap f) (unWrap x)) (unInh x)

para' :: (Functor f) => (f (Para i s f a) -> i -> a) -> AMu i s f -> a
para' phi = hylo' (uncurry phi . fork unWrap unInh) psi
  where
    psi x = let (f, i) = aout x in Wrap (fmap pair f) i
    pair x = Para x x

-- Zygomorphism

-- TODO

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

-- Tree functor

data NatF r = Z | S r deriving (Eq, Ord, Show, Read)

instance Functor NatF where
  fmap f n =
    case n of
      Z   -> Z
      S m -> S (f m)

-- "Normal" and "Attributed" Nat types

type  Nat     =  Mu     NatF
type ANat i s = AMu i s NatF

-- Smart constructors

zero :: (AAlgebra NatF i s) => i -> ANat i s
zero i = ain i Z

succ :: (AAlgebra NatF i s) => i -> ANat i s -> ANat i s
succ i n = ain i (S n)

-- "Library" functions

add :: (AAlgebra NatF i s) => ANat i s -> ANat i s -> ANat i s
add m = cata' phi
  where
    phi Z     _ = m
    phi (S n) i = succ i n

mul :: (AAlgebra NatF i s) => ANat i s -> ANat i s -> ANat i s
mul m = cata' phi
  where
    phi Z     i = zero i
    phi (S n) _ = add m n

fac :: (AAlgebra NatF i s) => ANat i s -> ANat i s
fac = para' phi
  where
    phi Z     i = succ i (zero i)
    phi (S p) i = mul (succ i (inp p)) (rec p)

toNat :: (Num a, AAlgebra NatF i s) => i -> a -> ANat i s
toNat i 0 = zero i
toNat i x
  | signum x == -1 = undefined
  | otherwise      = succ i (toNat i (x - 1))

fromNat :: ANat i s -> Integer
fromNat = cata' phi
  where
    phi Z     _ = 0
    phi (S n) _ = 1 + n

-- Examples

instance AAlgebra NatF None None where
  asyn _ x = (None, x)

testNat1 :: ANat None None
testNat1 = toNat None (4 :: Int)

testNat2 :: ANat None None
testNat2 = fac testNat1

instance AAlgebra NatF Size Size where
  asyn i x =
    case x of
      Z   -> (i, Z)
      S n -> (1 + sresult n, S n)

testNat3 :: ANat Size Size
testNat3 = toNat (Size 7) (4 :: Int)

--------------------------------------------------------------------------------
-- Tree
--------------------------------------------------------------------------------

-- Tree functor

data TreeF a r = Bin a r r | Tip deriving (Eq, Ord, Show, Read)

instance Functor (TreeF a) where
  fmap f t =
    case t of
      Bin a x y -> Bin a (f x) (f y)
      Tip       -> Tip

-- "Normal" and "Extended" Tree types

type  Tree     a =  Mu     (TreeF a)
type ATree i s a = AMu i s (TreeF a)

-- Smart constructors

bin :: (AAlgebra (TreeF a) i s) => i -> a -> ATree i s a -> ATree i s a -> ATree i s a
bin i a x y = ain i (Bin a x y)

tip :: (AAlgebra (TreeF a) i s) => i -> ATree i s a
tip i = ain i Tip

-- "Library" functions

-- Insert with direct recursion
insert_rec :: (Ord a, AAlgebra (TreeF a) i s) => a -> ATree i s a -> ATree i s a
insert_rec a t =
  case aout t of
    (Tip, i) ->
      bin i a (tip i) (tip i)
    (Bin b x y, i) ->
      case compare a b of
        LT -> bin i b (insert_rec a x) y
        GT -> bin i b x (insert_rec a y)
        EQ -> bin i a x y

-- Insert as a paramorphism
insert :: (Ord a, AAlgebra (TreeF a) i s) => a -> ATree i s a -> ATree i s a
insert a = para' phi
  where
    phi Tip i =
      bin i a (tip i) (tip i)
    phi (Bin b x y) i =
      case compare a b of
        LT -> bin i b (rec x) (inp y)
        GT -> bin i b (inp x) (rec y)
        EQ -> bin i a (inp x) (inp y)

toTree :: (Ord a, AAlgebra (TreeF a) i s) => i -> [a] -> ATree i s a
toTree i = foldr insert (tip i)

-- Examples

testTree :: (AAlgebra (TreeF Int) i s) => i -> ATree i s Int
testTree i = toTree i [1,9,2,8,3,7]

-- No algebra

instance AAlgebra (TreeF a) None None where
  asyn _ x = (None, x)

testTreeNone :: ATree None None Int
testTreeNone = testTree None

-- Size algebra

instance AAlgebra (TreeF a) Size Size where
  asyn (Size i) t =
    case t of
      Tip ->
        (Size i, Tip)
      Bin a x y ->
        (Size (1 + sz x + sz y), Bin a x y)
        where
          sz = getSize . sresult

testTreeSize :: Int
testTreeSize = getSize $ sresult (testTree 1 :: ATree Size Size Int)

-- Sum algebra

instance AAlgebra (TreeF Int) None Sum where
  asyn _ t =
    case t of
      Tip ->
        (0, Tip)
      Bin a x y ->
        (Sum a + sresult x + sresult y, Bin a x y)

testTreeSum :: Int
testTreeSum = getSum $ sresult $ testTree None

-- Float difference algebra

newtype DiffI = DI { avg :: Float } deriving (Eq, Ord, Show, Read)
data DiffS = DS { sumD :: Float, len :: Float, res :: Float } deriving (Eq, Ord, Show, Read)

instance AAlgebra (TreeF Float) DiffI DiffS where
  asyn i t =
    case t of
      Tip ->
        (DS { sumD = 0, len = 0, res = 0 }, Tip)
      Bin n x y ->
        (DS { sumD = n + sumD sx + sumD sy, len = 1 + len sx + len sy, res = n - avg i }, Bin n x y)
        where
          sx = sresult x
          sy = sresult y

average :: (Fractional a) => [a] -> a
average x = sum x / (fromIntegral (length x))

testTreeDiff :: (AAlgebra (TreeF Float) DiffI DiffS) => ATree DiffI DiffS Float
testTreeDiff = val
  where
    val = toTree i [1,9,2,8,3,7]
    s = sresult val
    i = DI { avg = sumD s / len s }

--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

-- List functor

data ListF a r = Cons a r | Nil  deriving (Eq, Ord, Show, Read)

instance Functor (ListF a) where
  fmap f l =
    case l of
      Cons a as -> Cons a (f as)
      Nil       -> Nil

-- "Normal" and "Extended" List types

type  List     a =  Mu     (ListF a)
type AList i s a = AMu i s (ListF a)

-- Smart constructors

cons :: (AAlgebra (ListF a) i s) => i -> a -> AList i s a -> AList i s a
cons i a as = ain i (Cons a as)

nil :: (AAlgebra (ListF a) i s) => i -> AList i s a
nil i = ain i Nil

-- "Library" functions

toList :: (AAlgebra (ListF a) i s) => i -> [a] -> AList i s a
toList i = foldr (cons i) (nil i)

-- Examples

testList :: (AAlgebra (ListF Int) i s) => i -> AList i s Int
testList i = toList i [1,9,2,8,3,7]

instance AAlgebra (ListF a) Size Size where
  asyn i l =
    case l of
      Nil       -> (i, Nil)
      Cons a as -> (1 + sresult as, Cons a as)

testListSize :: Int
testListSize = getSize $ sresult (testList 1 :: AList Size Size Int)

instance AAlgebra (ListF Int) None Sum where
  asyn _ l =
    case l of
      Nil ->
        (0, Nil)
      Cons a as ->
        (Sum a + sresult as, Cons a as)

testListSum :: Int
testListSum = getSum $ sresult (testList None :: AList None Sum Int)

