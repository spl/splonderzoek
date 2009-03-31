{-
This is the fourth source file for the splonderzoek blog entry dated 2008-03-31:

http://splonderzoek.blogspot.com/2009/03/incremental-attributes.html
-}

module IncrementalAttributes4Feedback where

data Tree a i s
  = Tip i s
  | Bin a (Tree a i s) (Tree a i s) i s
  deriving Show

data Alg a i s
  = Alg { ftip :: i -> s, fbin :: a -> i -> s -> s -> (i, i, s) }

result :: Tree a i s -> (i, s)
result (Tip i s)       = (i, s)
result (Bin _ _ _ i s) = (i, s)

iresult = fst . result
sresult = snd . result

tip :: Alg a i s -> i -> Tree a i s
tip alg i = Tip i (ftip alg i)

bin :: Alg a i s -> i -> a -> Tree a i s -> Tree a i s -> Tree a i s
bin alg i x lt rt = update i (Bin x lt rt undefined undefined)
  where
    update j t =
      case t of
        Tip _ _ ->
          tip alg j
        Bin y ylt yrt _ _ ->
          let (li, ri, s) = fbin alg y j (sresult zlt) (sresult zrt)
              zlt = update li ylt
              zrt = update ri yrt
          in  Bin y zlt zrt j s

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

newtype CounterI = CI { cntI :: Int } deriving Show
data CounterS = CS { size :: Int, cntS :: Int } deriving Show

counterAlg :: Alg a CounterI CounterS
counterAlg = Alg ft fb
  where

    ft :: CounterI -> CounterS
    ft i = CS { size = 1, cntS = cntI i }

    fb :: a -> CounterI -> CounterS -> CounterS -> (CounterI, CounterI, CounterS)
    fb _ i ls rs =
      ( i                                   -- left child
      , CI { cntI = 1 + cntI i + size ls }  -- right child
      , CS { size = 1 + size ls + size rs
           , cntS = cntI i + size ls
           }
      )

t1 = fromList counterAlg (CI { cntI = 0 }) "azbycx"

newtype DiffI = DI { avg :: Float } deriving Show
data DiffS = DS { sumD :: Float, len :: Float, res :: Float } deriving Show

diffAlg :: Alg Float DiffI DiffS
diffAlg = Alg ft fb
  where

    ft :: DiffI -> DiffS
    ft i =
      DS { sumD = 0
         , len = 0
         , res = 0
         }

    fb :: Float -> DiffI -> DiffS -> DiffS -> (DiffI, DiffI, DiffS)
    fb x i ls sr =
      ( i
      , i
      , DS { sumD = x + sumD ls + sumD sr
           , len = 1 + len ls + len sr
           , res = x - avg i
           }
      )

t2 = let val = fromList diffAlg (DI { avg = a }) [1,4,1.5,3.5,2,3,2.5]
         s = sresult val
         a = sumD s / len s
     in  val

