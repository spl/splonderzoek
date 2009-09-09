
-- This is Haskell code derived from the Bird-Meertens formulism used by Jeremy
-- Gibbons in "Upwards and downwards accumulations on trees" (1993).
--
-- See http://www.citeulike.org/user/spl/article/5486052 for the article
-- reference and links.

module Accumulations where

import Prelude hiding (last)
import Data.Char (ord)
import Data.Monoid

--------------------------------------------------------------------------------
-- 2. Notation
--------------------------------------------------------------------------------

-- product (unused in my code)
(.||) :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
(.||) f g (a, b) = (f a, g b)

infixr 9 .||

-- sum (unused in my code)
(.|) :: (a -> c) -> (b -> d) -> Either a b -> Either c d
(.|) f _ (Left a)  = Left (f a)
(.|) _ g (Right b) = Right (g b)

-- ↟
fork :: (a -> b) -> (a -> c) -> a -> (b, c)
fork f g a = (f a, g a)

-- ↡ (unused in my code, because it's replaced by constructor alternatives and
-- function arguments)
join :: (b -> a) -> (c -> a) -> Either b c -> a
join h _ (Left a)  = h a
join _ k (Right b) = k b

data Tree a
  = Leaf a -- △
  | Branch (Tree a) a (Tree a) -- ┴
  deriving (Eq, Show)

-- postfix * for Tree
instance Functor Tree where
  fmap f (Leaf a) = Leaf (f a)
  fmap f (Branch x a y) = Branch (fmap f x) (f a) (fmap f y)

-- Examples
five = Branch (Leaf 'b') 'a' (Branch (Leaf 'd') 'c' (Leaf 'e'))
five' = fmap ord five

-- Catamorphism for Tree
cataTree :: (a -> b) -> (b -> a -> b -> b) -> Tree a -> b
cataTree f _ (Leaf a) = f a
cataTree f g (Branch x a y) = g (cataTree f g x) a (cataTree f g y)

leaves = cataTree (const 1) (\u _ v -> u + v)
branches = cataTree (const 0) (\u _ v -> u + 1 + v)

--------------------------------------------------------------------------------
-- 3. Upwards accumulations
--------------------------------------------------------------------------------

subtrees :: Tree a -> Tree (Tree a)
subtrees (Leaf a)       = Leaf (Leaf a)
subtrees (Branch x a y) = Branch (subtrees x) (Branch x a y) (subtrees y)

root :: Tree a -> a
root (Leaf a) = a
root (Branch _ a _) = a

prop_subtrees1 x = root (subtrees x) == x

subtrees' :: Tree a -> Tree (Tree a)
subtrees' = cataTree (Leaf . Leaf) (\u a v -> Branch u (Branch (root u) a (root v)) v)

prop_subtrees2 x = subtrees x == subtrees' x

upwards_pass :: (Tree a -> b) -> Tree a -> Tree b
upwards_pass g = fmap g . subtrees

-- ⇑
upwards_accum :: (a -> b) -> (b -> a -> b -> b) -> Tree a -> Tree b
upwards_accum f g = fmap (cataTree f g) . subtrees

sizes = fmap size . subtrees

size = cataTree (const 1) (\u _ v -> u + 1 + v)

sizes' = upwards_accum (const 1) (\u _ v -> u + 1 + v)

prop_sizes x = sizes x == sizes' x

--------------------------------------------------------------------------------
-- 4. Downwards accumulations
--------------------------------------------------------------------------------

data Thread a
  = TLeaf a -- ♢
  | TLeft (Thread a) a -- ↙, left snoc
  | TRight (Thread a) a -- ↘, right snoc
  deriving (Eq, Show)

-- Catamorphism for Thread
cataThread :: (a -> b) -> (b -> a -> b) -> (b -> a -> b) -> Thread a -> b
cataThread f _ _ (TLeaf a)      = f a
cataThread f g h (TLeft x a)    = g (cataThread f g h x) a
cataThread f g h (TRight y a)   = h (cataThread f g h y) a

paths :: Tree a -> Tree (Thread a)
paths (Leaf a)       = Leaf (TLeaf a)
paths (Branch x a y) = Branch (fmap (left a) (paths x)) (TLeaf a) (fmap (right a) (paths y))
  where
    -- cons
    left  b = cataThread (TLeft (TLeaf b)) TLeft TRight
    right b = cataThread (TRight (TLeaf b)) TLeft TRight

downwards_pass :: (Thread a -> b) -> Tree a -> Tree b
downwards_pass g = fmap g . paths

-- ⇓
downwards_accum :: (a -> b) -> (b -> a -> b) -> (b -> a -> b) -> Tree a -> Tree b
downwards_accum f g h = fmap (cataThread f g h) . paths

downwards_pass' :: (a -> b) -> (a -> b -> b) -> (a -> b -> b) -> Tree a -> Tree b
downwards_pass' f _ _ (Leaf a)       = Leaf (f a)
downwards_pass' f g h (Branch x a y) = Branch (fmap (g a) (downwards_pass' f g h x)) (f a) (fmap (h a) (downwards_pass' f g h y))

data Daerht a
  = DLeaf a -- ♢
  | DRight a (Daerht a) -- ↗, right cons
  | DLeft a (Daerht a) -- ↖, left cons

-- Catamorphism for Daerht
cataDaerht :: (a -> b) -> (a -> b -> b) -> (a -> b -> b) -> Daerht a -> b
cataDaerht f _ _ (DLeaf a)      = f a
cataDaerht f g h (DRight a y)   = g a (cataDaerht f g h y)
cataDaerht f g h (DLeft a x)    = h a (cataDaerht f g h x)

td :: Thread a -> Daerht a
td = cataThread DLeaf right left
  where
    -- snoc
    right p a = cataDaerht (\b -> DRight b (DLeaf a)) DRight DLeft p
    left  p a = cataDaerht (\b -> DLeft b (DLeaf a)) DRight DLeft p

downwards_pass'' :: (a -> b) -> (a -> b -> b) -> (a -> b -> b) -> Tree a -> Tree b
downwards_pass'' f g h = fmap (cataDaerht f g h) . fmap td . paths

depths :: Tree a -> Tree Int
depths (Leaf a)       = Leaf 1
depths (Branch x _ y) = Branch (fmap (+1) (depths x)) 1 (fmap (+1) (depths y))

depths' :: Tree a -> Tree Int
depths' = downwards_accum (const 1) (\u _ -> u + 1) (\v _ -> v + 1)

prop_depths x = depths x == depths' x

--------------------------------------------------------------------------------
-- 5. Parallel prefix
--------------------------------------------------------------------------------

-- Non-empty list
data List a
  = One a -- ▢
  | Append (List a) (List a) -- ++

-- postfix * for List
instance Functor List where
  fmap f (One a) = One (f a)
  fmap f (Append x y) = Append (fmap f x) (fmap f y)

-- Catamorphism for List
cataList :: (a -> b) -> (b -> b -> b) -> List a -> b
cataList f _ (One a) = f a
cataList f g (Append x y) = g (cataList f g x) (cataList f g y)

last = cataList id (\u v -> v)

inits = cataList (One . One) (\u v -> Append u (fmap (Append (last u)) v))

ps :: (a -> b) -> (b -> b -> b) -> List a -> List b
ps f g = fmap (cataList f g) . inits

fringe :: Tree a -> List a
fringe = cataTree One (\u _ v -> Append u v)

-- The off-used 's' mentioned inline in the text on page 133
s f g = cataList f g . fringe

tps1 :: (a -> b) -> (b -> b -> b) -> Tree a -> Tree b
tps1 f _ (Leaf a)        = Leaf (f a)
tps1 f g (Branch x a y)  = Branch (tps1 f g x) (s f g x) (fmap (g (s f g x)) (tps1 f g y))

prop_tps1 f g x = fringe (tps1 f g x) == ps f g (fringe x)

up1 :: (a -> b) -> (b -> b -> b) -> Tree a -> Tree b
up1 f _ (Leaf a)       = Leaf (f a)
up1 f g (Branch x a y) = Branch (up1 f g x) (s f g x) (up1 f g y)

down1 :: (b -> b -> b) -> Tree b -> Tree b
down1 _ (Leaf b)       = Leaf b
down1 g (Branch x b y) = Branch (down1 g x) b (fmap (g b) (down1 g y))

prop_tps2 f g x = tps1 f g x == down1 g (up1 f g x)

sl :: (a -> b) -> (b -> b -> b) -> Tree a -> b
sl f _ (Leaf a)         = f a
sl f g (Branch x _ _)   = s f g x

up2 :: (a -> b) -> (b -> b -> b) -> Tree a -> Tree b
up2 f g = fmap (sl f g) . subtrees

s_fork_sl1 :: (a -> b) -> (b -> b -> b) -> Tree a -> (b, b)
s_fork_sl1 f g = fork (s f g) (sl f g)

-- The unnamed right component of the catamorphism for 's ↟ sl'. It doesn't seem
-- to quite match what Gibbons wrote, so I'm not fully convinced it's correct.
pairs :: (b -> b -> b) -> (b, b) -> a -> (b, b) -> (b, b)
pairs g (x, _) _ (y, _) = (g x y, x)

s_fork_sl2 :: (a -> b) -> (b -> b -> b) -> Tree a -> (b, b)
s_fork_sl2 f g = cataTree (fork f f) (pairs g)

up3 :: (a -> b) -> (b -> b -> b) -> Tree a -> Tree b
up3 f g = fmap snd . upwards_accum (fork f f) (pairs g)

down2 :: (Monoid b) => (b -> b -> b) -> Tree b -> Tree b
down2 g = fmap snd . downwards_accum (fork (const mempty) id) plus cros
  where
    plus (b, c) d = (b, g b d)
    cros (b, c) d = (c, g c d)

tps2 :: (Monoid b) => (a -> b) -> (b -> b -> b) -> Tree a -> Tree b
tps2 f g = down2 g . up3 f g

prop_tps3 f g x = tps1 f g x == tps2 f g x

