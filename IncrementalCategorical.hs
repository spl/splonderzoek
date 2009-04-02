{-# LANGUAGE MultiParamTypeClasses              #-}
{-# LANGUAGE FlexibleInstances                  #-}
{-# LANGUAGE FlexibleContexts                   #-}
{-# LANGUAGE ScopedTypeVariables                #-}
{-# LANGUAGE GeneralizedNewtypeDeriving         #-}
{-# OPTIONS_GHC -Wall                           #-}

module IncrementalCategorical where

--------------------------------------------------------------------------------
-- "Normal" fixed point and "Extended" fixed point
--------------------------------------------------------------------------------

-- Normal fixed point
newtype Mu f = In { out :: f (Mu f) }

-- Extend: a pair of a tag for the result and a functor
data Ext z f r = Ext { tag :: z, fun :: f r } deriving (Eq, Ord, Show, Read)

-- Extended fixed point: every recursive point is now a product of a result type
-- 'z' and the original recursive point.
type EMu z f = Mu (Ext z f)

emu :: z -> f (EMu z f) -> EMu z f
emu z f = In (Ext z f)

result :: EMu z f -> z
result = tag . out

--------------------------------------------------------------------------------
-- Algebra and Coalgebra classes
--------------------------------------------------------------------------------

class (Functor f) => Algebra f m where
  alg :: f m -> m

class (Functor f) => Coalgebra f m where
  coalg :: m -> f m

--------------------------------------------------------------------------------
-- Types for specific algebras
--------------------------------------------------------------------------------

newtype Size = Size { getSize :: Int } deriving (Eq, Ord, Show, Read, Num)

newtype Sum = Sum { getSum :: Int } deriving (Eq, Ord, Show, Read, Num)

--------------------------------------------------------------------------------
-- Isomorphism between EMu and the unextended functor
--------------------------------------------------------------------------------

forget :: EMu z f -> f (EMu z f)
forget = fun . out

remember :: (Algebra f z) => f (EMu z f) -> EMu z f
remember x = emu (alg (fmap result x)) x

forget_remember_id :: (Algebra f z) => f (EMu z f) -> f (EMu z f)
forget_remember_id = forget . remember

remember_forget_id :: (Algebra f z) => EMu z f -> EMu z f
remember_forget_id = remember . forget

--------------------------------------------------------------------------------
-- Isomorphism between Mu and EMu
--------------------------------------------------------------------------------

extend :: (Algebra f z) => Mu f -> EMu z f
extend = remember . fmap extend . out

contract :: (Functor f) => EMu z f -> Mu f
contract = In . fmap contract . forget

extend_contract_id :: (Algebra f z) => EMu z f -> EMu z f
extend_contract_id = extend . contract

contract_extend_id :: forall f z . (Algebra f z) => Mu f -> Mu f
contract_extend_id = contract . (extend :: Mu f -> EMu z f)

--------------------------------------------------------------------------------
-- Typical morphisms
--------------------------------------------------------------------------------

cata :: (Algebra f a) => EMu z f -> a
cata = alg . fmap cata . forget

ana :: (Algebra f z, Coalgebra f a) => a -> EMu z f
ana = remember . fmap ana . coalg

--------------------------------------------------------------------------------
-- Tree
--------------------------------------------------------------------------------

-- Tree functor

data TreeF a r = Bin a r r | Tip deriving (Eq, Ord, Show, Read)

instance Functor (TreeF a) where
  fmap f (Bin a x y) = Bin a (f x) (f y)
  fmap _ Tip         = Tip

-- "Normal" and "Extended" Tree types

type  Tree   a =  Mu   (TreeF a)

type ETree z a = EMu z (TreeF a)

-- Algebras

instance Algebra (TreeF a) Size where
  alg (Bin _ x y) = 1 + x + y
  alg Tip         = 0

instance Algebra (TreeF Int) Sum where
  alg (Bin a x y) = Sum a + x + y
  alg Tip         = 0

-- Smart constructors

bin :: (Algebra (TreeF a) z) => a -> ETree z a -> ETree z a -> ETree z a
bin a x y = remember (Bin a x y)

tip :: (Algebra (TreeF a) z) => ETree z a
tip = remember Tip

-- "Library" functions

insert :: (Ord a, Algebra (TreeF a) z) => a -> ETree z a -> ETree z a
insert a t =
  case fun (out t) of
    Tip ->
      bin a tip tip
    Bin b x y ->
      case compare a b of
        LT -> bin b (insert a x) y
        GT -> bin b x (insert a y)
        EQ -> bin a x y

toTree :: (Ord a, Algebra (TreeF a) z) => [a] -> ETree z a
toTree = foldr insert tip

-- Examples

testTree :: (Algebra (TreeF Int) z) => ETree z Int
testTree = toTree [1,9,2,8,3,7]

testTreeSize :: Int
testTreeSize = getSize $ result $ testTree

testTreeSum :: Int
testTreeSum = getSum $ result $ testTree

--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

-- List functor

data ListF a r = Cons a r | Nil  deriving (Eq, Ord, Show, Read)

instance Functor (ListF a) where
  fmap f (Cons a as) = Cons a (f as)
  fmap _ Nil         = Nil

-- "Normal" and "Extended" List types

type  List   a =  Mu   (ListF a)

type EList z a = EMu z (ListF a)

-- Algebras

instance Algebra (ListF a) Size where
  alg (Cons _ as) = 1 + as
  alg Nil         = 0

instance Algebra (ListF Int) Sum where
  alg (Cons a as) = fromIntegral a + as
  alg Nil         = 0

-- Smart constructors

cons :: (Algebra (ListF a) z) => a -> EList z a -> EList z a
cons a as = remember (Cons a as)

nil :: (Algebra (ListF a) z) => EList z a
nil = remember Nil

-- "Library" functions

toList :: (Algebra (ListF a) z) => [a] -> EList z a
toList = foldr cons nil

-- Examples

testList :: (Algebra (ListF Int) z) => EList z Int
testList = toList [1,9,2,8,3,7]

testListSize :: Int
testListSize = getSize $ result $ testList

testListSum :: Int
testListSum = getSum $ result $ testList

