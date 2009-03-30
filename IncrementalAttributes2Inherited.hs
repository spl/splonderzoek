{-
This is the second source file for the splonderzoek blog entry dated 2008-03-30:

-}

module IncrementalAttributes2Inherited where

data Tree a i
  = Tip i
  | Bin a (Tree a i) (Tree a i) i
  deriving Show

data Alg a i
  = Alg { itip :: i -> i, ibin :: a -> i -> i }

result :: Tree a i -> i
result (Tip i)       = i
result (Bin _ _ _ i) = i

tip :: Alg a i -> i -> Tree a i
tip alg i = Tip (itip alg i)

bin :: Alg a i -> i -> a -> Tree a i -> Tree a i -> Tree a i
bin alg i x lt rt = Bin x (update i lt) (update i rt) i
  where
    update i' t =
      case t of
        Tip _ ->
          tip alg i'
        Bin x lt rt _ ->
          let s = ibin alg x i' in
          Bin x (update s lt) (update s lt) s

empty :: (Ord a) => Alg a i -> i -> Tree a i
empty = tip

singleton :: (Ord a) => Alg a i -> i -> a -> Tree a i
singleton alg i x = bin alg i x (tip alg i) (tip alg i)

insert :: (Ord a) => Alg a i -> a -> Tree a i -> Tree a i
insert alg x t =
  case t of
    Tip i ->
      singleton alg i x
    Bin y lt rt i ->
      case compare x y of
        LT -> bin alg i y (insert alg x lt) rt
        GT -> bin alg i y lt (insert alg x rt)
        EQ -> bin alg i x lt rt

fromList :: (Ord a) => Alg a i -> i -> [a] -> Tree a i
fromList alg i = foldr (insert alg) (empty alg i)

depthAlg :: Alg a Int
depthAlg = Alg (+1) (const (+1))

t1 = fromList depthAlg 0 "azbycx"

