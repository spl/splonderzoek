{-
This is the third source file for the splonderzoek blog entry dated 2008-03-30:

-}

module IncrementalAttributes3SynthesizedAndInherited where

data Tree a i s
  = Tip i s
  | Bin a (Tree a i s) (Tree a i s) i s
  deriving Show

data Alg a i s
  = Alg { itip :: i -> i, ibin :: a -> i -> i,
          stip :: s,      sbin :: a -> s -> s -> s }

result :: Tree a i s -> (i, s)
result (Tip i s)       = (i, s)
result (Bin _ _ _ i s) = (i, s)

iresult = fst . result
sresult = snd . result

tip :: Alg a i s -> i -> Tree a i s
tip alg i = Tip (itip alg i) (stip alg)

bin :: Alg a i s -> i -> a -> Tree a i s -> Tree a i s -> Tree a i s
bin alg i x lt rt =
  Bin x (update i lt) (update i rt) i (sbin alg x (sresult lt) (sresult rt))
  where
    update i' t =
      case t of
        Tip _ _ ->
          tip alg i'
        Bin y ylt yrt _ s ->
          let j = ibin alg y i' in
          Bin y (update j ylt) (update j yrt) j s

empty :: (Ord a) => Alg a i s -> i -> Tree a i s
empty = tip

singleton :: (Ord a) => Alg a i s -> i -> a -> Tree a i s
singleton alg i x = bin alg i x (tip alg i) (tip alg i)

insert :: (Ord a) => Alg a i s -> a -> Tree a i s -> Tree a i s
insert alg x t =
  case t of
    Tip i _ ->
      singleton alg i x
    Bin y lt rt i _ ->
      case compare x y of
        LT -> bin alg i y (insert alg x lt) rt
        GT -> bin alg i y lt (insert alg x rt)
        EQ -> bin alg i x lt rt

fromList :: (Ord a) => Alg a i s -> i -> [a] -> Tree a i s
fromList alg i = foldr (insert alg) (empty alg i)

depthAndHeightAlg :: Alg a Int Int
depthAndHeightAlg = Alg (+1) (const (+1)) 1 (\_ x y -> 1 + max x y)

t1 = fromList depthAndHeightAlg 0 "azbycx"

