{-# LANGUAGE MultiParamTypeClasses              #-}
{-# LANGUAGE FlexibleInstances                  #-}
{-# LANGUAGE FlexibleContexts                   #-}
{-# LANGUAGE ScopedTypeVariables                #-}
{-# LANGUAGE GeneralizedNewtypeDeriving         #-}
{-# LANGUAGE RankNTypes                         #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans         #-}

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

-- F-Algebra for a given functor F
class (Functor f) => Algebra f m where
  alg :: f m -> m

-- F-Coalgebra for a given functor F
class (Functor f) => Coalgebra f m where
  coalg :: m -> f m

-- F-W-Comonadic Algebras for a given functor F and comonad W
class (Functor f) => GAlgebra f w a where
  galg :: f (w a) -> a

--------------------------------------------------------------------------------
-- Types for specific algebras
--------------------------------------------------------------------------------

newtype Size = Size { getSize :: Int } deriving (Eq, Ord, Show, Read, Num)

newtype Sum = Sum { getSum :: Int } deriving (Eq, Ord, Show, Read, Num)

--------------------------------------------------------------------------------
-- Isomorphism between EMu and the unextended functor
--------------------------------------------------------------------------------

-- Was: remember
ein' :: (Functor f) => (f z -> z) -> f (EMu z f) -> EMu z f
ein' phiz x = emu (phiz (fmap result x)) x

ein :: (Algebra f z) => f (EMu z f) -> EMu z f
ein = ein' alg

-- Was: forget
eout :: EMu z f -> f (EMu z f)
eout = fun . out

ein_eout_id :: (Algebra f z) => EMu z f -> EMu z f
ein_eout_id = ein . eout

eout_ein_id :: (Algebra f z) => f (EMu z f) -> f (EMu z f)
eout_ein_id = eout . ein

--------------------------------------------------------------------------------
-- Isomorphism between Mu and EMu
--------------------------------------------------------------------------------

extend :: (Algebra f z) => Mu f -> EMu z f
extend = ein . fmap extend . out

contract :: (Functor f) => EMu z f -> Mu f
contract = In . fmap contract . eout

extend_contract_id :: (Algebra f z) => EMu z f -> EMu z f
extend_contract_id = extend . contract

contract_extend_id :: forall f z . (Algebra f z) => Mu f -> Mu f
contract_extend_id = contract . (extend :: Mu f -> EMu z f)

--------------------------------------------------------------------------------
-- Typical morphisms
--------------------------------------------------------------------------------

-- Catamorphism

cata' :: (Functor f) => (f a -> a) -> EMu z f -> a
cata' phi = phi . fmap (cata' phi) . eout

cata :: (Algebra f a) => EMu z f -> a
cata = cata' alg

-- Anamorphism

ana' :: (Functor f) => (f z -> z) -> (a -> f a) -> a -> EMu z f
ana' phiz psi = ein' phiz . fmap (ana' phiz psi) . psi

ana :: (Algebra f z, Coalgebra f a) => a -> EMu z f
ana = ana' alg coalg

-- Hylomorphism

-- A more general version
hylo_g' :: (Functor f) => (a -> f a) -> (g b -> b) -> (forall c. f c -> g c) -> a -> b
hylo_g' psi phi e = phi . e . fmap (hylo_g' psi phi e) . psi

hylo' :: (Functor f) => (f b -> b) -> (a -> f a) -> a -> b
hylo' phi psi = phi . fmap (hylo' phi psi) . psi

hylo :: forall f a b. (Algebra f b, Coalgebra f a) => a -> b
hylo = hylo' alg (coalg :: a -> f a)

-- Paramorphism

type Para z f = (,) (EMu z f)

newtype Wrap z f a = Wrap { unWrap :: f (Para z f a) }

instance (Functor f) => Functor (Wrap z f) where
  fmap f = Wrap . fmap (fmap f) . unWrap

instance Functor ((,) a) where
  fmap f x = (fst x, f (snd x))

para' :: (Functor f) => (f (Para z f a) -> a) -> EMu z f -> a
para' phi = hylo' (phi . unWrap) (Wrap . fmap pair . eout)
  where
    pair x = (x, x)

para :: (GAlgebra f (Para z f) a) => EMu z f -> a
para = para' galg

-- Zygomorphism

type Zygo = (,)

zygo' :: (Functor f) => (f a -> a) -> (f (Zygo a b) -> b) -> EMu z f -> b
zygo' chi phi = phi . fmap (fork (zygo' chi phi) (cata' chi)) . eout
  where
    fork f g x = (g x, f x)

zygo :: forall z f a b. (Algebra f a, GAlgebra f (Zygo a) b) => EMu z f -> b
zygo = zygo' (alg :: f a -> a) galg

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
bin a x y = ein (Bin a x y)

tip :: (Algebra (TreeF a) z) => ETree z a
tip = ein Tip

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
cons a as = ein (Cons a as)

nil :: (Algebra (ListF a) z) => EList z a
nil = ein Nil

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

