{-
This is the first source file for the splonderzoek blog entry dated 2008-03-30:

-}

module IncrementalAttributes1Synthesized where

data Tree a s
  = Tip s
  | Bin a (Tree a s) (Tree a s) s
  deriving Show

data Alg a s
  = Alg { stip :: s, sbin :: a -> s -> s -> s }

result :: Tree a s -> s
result (Tip s)       = s
result (Bin _ _ _ s) = s

tip :: Alg a s -> Tree a s
tip alg = Tip (stip alg)

bin :: Alg a s -> a -> Tree a s -> Tree a s -> Tree a s
bin alg x lt rt = Bin x lt rt (sbin alg x (result lt) (result rt))

empty :: (Ord a) => Alg a s -> Tree a s
empty = tip

singleton :: (Ord a) => Alg a s -> a -> Tree a s
singleton alg x = bin alg x (tip alg) (tip alg)

insert :: (Ord a) => Alg a s -> a -> Tree a s -> Tree a s
insert alg x t =
  case t of
    Tip _ ->
      singleton alg x
    Bin y lt rt _ ->
      case compare x y of
        LT -> bin alg y (insert alg x lt) rt
        GT -> bin alg y lt (insert alg x rt)
        EQ -> bin alg x lt rt

fromList :: (Ord a) => Alg a s -> [a] -> Tree a s
fromList alg = foldr (insert alg) (empty alg)

heightAlg :: Alg a Integer
heightAlg = Alg 0 (\_ x y -> 1 + max x y)

t1 = fromList heightAlg "azbycx"

