
{-#  OPTIONS_GHC -Wall -fno-warn-missing-signatures -fno-warn-incomplete-patterns  #-}
{-#  LANGUAGE CPP  #-}
{-#  LANGUAGE StandaloneDeriving  #-}
{-#  LANGUAGE MultiParamTypeClasses  #-}
{-#  LANGUAGE TypeFamilies  #-}
{-#  LANGUAGE FunctionalDependencies  #-}
{-#  LANGUAGE FlexibleContexts  #-}
{-#  LANGUAGE FlexibleInstances  #-}
{-#  LANGUAGE TypeSynonymInstances  #-}
{-#  LANGUAGE TypeOperators  #-}
{-#  LANGUAGE UndecidableInstances  #-} --  Show (Fix ff)
{-#  LANGUAGE GADTs  #-}
{-#  LANGUAGE KindSignatures  #-}

module Draft_IFL_2009 where
import Prelude hiding (lookup, zipWith, mod)
import Data.List (genericLength)
import Data.Maybe
import Control.Monad
import Control.Arrow (second)

type family Alg tt ss :: *

class Fold tt where
  fold :: Alg tt ss -> tt -> ss

data Tree aa = Tip | Bin aa (Tree aa) (Tree aa)

type instance Alg (Tree aa) ss = (ss, aa -> ss -> ss -> ss)

instance Fold (Tree aa) where
  fold       (t, _) Tip            = t
  fold alg@  (_, b) (Bin x tL tR)  = b x (fold alg tL) (fold alg tR)

repFold :: (Fold tt) => Alg tt ss -> (tt -> tt) -> tt -> (ss, ss)
repFold alg f x = let { s = fold alg x ; x' = f x ; s' = fold alg x' } in (s, s')

empty      :: Set aa
singleton  :: aa -> Set aa
size       :: Set aa -> Int

insert     :: (Ord aa) => aa -> Set aa -> Set aa
fromList   :: (Ord aa) => [aa] -> Set aa
fold_      :: (ss, aa -> ss -> ss -> ss) -> Set aa -> ss

type Set aa = Tree aa

fromList = foldl (flip insert) empty

insert x Tip            =  singleton x
insert x (Bin y tL tR)  =  case compare x y of
                             LT  -> balance  y  (insert x tL)  tR
                             GT  -> balance  y  tL             (insert x tR)
                             EQ  -> Bin      x  tL             tR

balance x tL tR  | sL + sR <= 1  = Bin x tL tR
                 | sR >= 4 * sL  = rotateL x tL tR
                 | sL >= 4 * sR  = rotateR x tL tR
                 | otherwise     = Bin x tL tR
  where  sL  = size tL
         sR  = size tR

sizeAlg  = (0, \ _ sL sR -> 1 + sL + sR)
size     = fold sizeAlg

data Tree1 aa = Tip1 Int | Bin1 Int aa (Tree1 aa) (Tree1 aa)

size1  (Tip1  s        ) = s
size1  (Bin1  s _ _ _  ) = s

class TreeLike tt aa | tt -> aa where
  tip       :: tt
  bin       :: aa -> tt -> tt -> tt
  caseTree  :: tt -> rr -> (aa -> tt -> tt -> rr) -> rr

instance TreeLike (Tree1 aa) aa where
  tip             = Tip1  (fst sizeAlg)
  bin x tL tR     = Bin1  (snd sizeAlg x (size1 tL) (size1 tR)) x tL tR
  caseTree n t b  = case n of { Tip1 _ -> t ; Bin1 _ x tL tR -> b x tL tR }

insert1 x t = caseTree t  (singleton1 x)
                          $ \ y tL tR ->  case compare x y of
                                            LT  -> balance1    y  (insert1 x tL)  tR
                                            GT  -> balance1    y  tL              (insert1 x tR)
                                            EQ  -> bin         x  tL              tR

newtype Fix ff = In { out :: ff (Fix ff) } 

data Extt1 ss ff rr = Ext1 ss (ff rr)

type Fix1 ss ff = Fix (Extt1 ss ff)

in1   :: ss -> ff (Fix1 ss ff) -> Fix1 ss ff
out1  :: Fix1 ss ff -> ff (Fix1 ss ff)
ann   :: Fix1 ss ff -> ss

data TreeF aa rr  =  TipF | BinF aa rr rr

type TreeU aa     =  Fix1 Int (TreeF aa)

type family AlgU (ff :: * -> *) ss :: *

class IncrementalU ff where
  pullUp :: AlgU ff ss -> ff ss -> ss

type instance AlgU (TreeF aa) ss = (ss, aa -> ss -> ss -> ss)

instance IncrementalU (TreeF aa) where
  pullUp (t, _) TipF            = t
  pullUp (_, b) (BinF x sL sR)  = b x sL sR

inU :: (IncrementalU ff, Functor ff) => AlgU ff ss -> ff (Fix1 ss ff) -> Fix1 ss ff
inU alg fx = in1 (pullUp alg (fmap ann fx)) fx

instance TreeLike (TreeU aa) aa where
  tip             = inU sizeAlg TipF
  bin x tL tR     = inU sizeAlg (BinF x tL tR)
  caseTree n t b  = case out1 n of { TipF -> t ; BinF x tL tR -> b x tL tR }

type family AlgD (ff :: * -> *) ii :: *

class IncrementalD ff where
  pushDown :: AlgD ff ii -> ff ss -> ii -> ff ii

type instance AlgD (TreeF3 aa) ii = (ii -> TreeF3 aa ii, aa -> ii -> TreeF3 aa ii)

instance IncrementalD (TreeF3 aa) where
  pushDown (t, _) TipF3          = t
  pushDown (_, b) (BinF3 x _ _)  = b x

class ZipWith ff where
  zipWith :: (aa -> bb -> cc) -> ff aa -> ff bb -> ff cc

inD_ :: (IncrementalD ff, ZipWith ff) => AlgD ff ii -> ii -> ff (Fix1 ii ff) -> Fix1 ii ff
inD_ alg ini fx = in1 ini (zipWith push (pushDown alg fx ini) fx)
  where  push i  = inD_ alg i . out1

depths :: Tree aa -> Tree Int
depths Tip            = Tip
depths (Bin _ tL tR)  = Bin 1 (fmap (+1) (depths tL)) (fmap (+1) (depths tR))

depthAlg  = (const TipF3, \ x i -> let i' = 1 + i in BinF3 x i' i')
depthIni  = 1

instance TreeLike (Fix1 Int (TreeF3 aa)) aa where
  tip             = inD depthAlg depthIni TipF3
  bin x tL tR     = inD depthAlg depthIni (BinF3 x tL tR)
  caseTree n t b  = case out1 n of { TipF3 -> t ; BinF3 x tL tR -> b x tL tR }

depthOf k t = caseTree t  Nothing
                          $ \ x tL tR ->  case compare k x of
                                            EQ  -> Just (ann t)
                                            LT  -> depthOf k tL
                                            GT  -> depthOf k tR

inD :: (IncrementalD ff, ZipWith ff, Eq ii) => AlgD ff ii -> ii -> ff (Fix1 ii ff) -> Fix1 ii ff
inD alg ini fx = in1 ini (zipWith push (pushDown alg fx ini) fx)
  where  push i x  | i == ann x  = x
                   | otherwise   = inD alg i (out1 x)

data Extt2  ii ss ff rr  = Ext2 ii ss (ff rr)
type Fix2   ii ss ff     = Fix (Extt2 ii ss ff)

in2   :: ii -> ss -> ff (Fix2 ii ss ff) -> Fix2 ii ss ff
out2  :: Fix2 ii ss ff -> ff (Fix2 ii ss ff)
syn   :: Fix2 ii ss ff -> ss
inh   :: Fix2 ii ss ff -> ii

type family AlgC (ff :: * -> *) ii ss :: *

class IncrementalC ff where
  passAround :: AlgC ff ii ss -> ff ss -> ii -> (ss, ff ii)

type instance AlgC (TreeF aa) ii ss = (ii -> (ss, TreeF aa ii), aa -> ss -> ss -> ii -> (ss, TreeF aa ii))

instance IncrementalC (TreeF aa) where
  passAround (t, _) TipF            = t
  passAround (_, b) (BinF x sL sR)  = b x sL sR

inC ::  (IncrementalC ff, Functor ff, ZipWith ff, Eq ii)
        => AlgC ff ii ss -> (ss -> ii) -> ff (Fix2 ii ss ff) -> Fix2 ii ss ff
inC alg top fx = in2 ini s (zipWith push fi fx)
  where  ini      = top s
         (s, fi)  = passAround alg (fmap syn fx) ini
         push i x  | i == inh x  = x
                   | otherwise   = inC alg (const i) (out2 x)

diff :: [Float] -> [Float]
diff xs = let avg ys = sum ys / genericLength ys in map (\ x -> x - avg xs) xs

data     DiffS  = DS  { sumS :: Float, sizeS :: Float, diffS :: Float }
newtype  DiffI  = DI  { avgI :: Float }

diffAlg = (t, b)
  where  t  _          = (DS { sumS = 0, sizeS = 0, diffS = 0 }  , TipF        )
         b  x sL sR i  = (s                                      , BinF x i i  )
           where s = DS  {  sumS   = x + sumS sL + sumS sR
                         ,  sizeS  = 1 + sizeS sL + sizeS sR
                         ,  diffS  = x - avgI i }

diffFun s = DI { avgI = sumS s / sizeS s }

instance TreeLike (Fix2 DiffI DiffS (TreeF Float)) Float where
  tip             = inC diffAlg diffFun TipF
  bin x tL tR     = inC diffAlg diffFun (BinF x tL tR)
  caseTree n t b  = case out2 n of { TipF -> t ; BinF x tL tR -> b x tL tR }

diffC :: (TreeLike (Fix2 ii DiffS ff) aa, TreeLike tt Float) => Fix2 ii DiffS ff -> tt
diffC n =  caseTree n tip (\ _ tL tR -> bin (diffOf n) (diffC tL) (diffC tR))

diffOf :: Fix2 ii DiffS ff -> Float
diffOf = diffS . syn

newtype  KK aa            rr = K aa
newtype  II               rr = I rr
data     UU               rr = U
data     (ff  ::*::  gg)  rr = ff rr :*: gg rr
data     (ff  :+:    gg)  rr = L (ff rr) | R (gg rr)

type TreePF aa = UU :+: KK aa ::*:: II ::*:: II

instance TreeLike (Fix (TreePF aa)) aa where
  tip             = In (L U)
  bin x tL tR     = In (R (K x :*: I tL :*: I tR))
  caseTree n t b  = case out n of { L U -> t ; R (K x :*: I tL :*: I tR) -> b x tL tR }

type instance AlgC II ii ss = ss -> ii -> (ss, ii)

instance IncrementalC II where
  passAround f (I x) = second I . f x

type instance AlgC (II ::*:: gg) ii ss = ss -> ii -> (AlgC gg ii ss, ii)

instance (IncrementalC gg) => IncrementalC (II ::*:: gg) where
  passAround f (I x :*: y) i =  let  (g, i')  = f x i
                                     (s, gi)  = passAround g y i
                                in   (s, I i' :*: gi)

diffAlgPF = (t, bL)
  where  bL x sL iL = (bR, iL)
           where  bR sR iR = (s, iR)
          

                    where s = DS  {  sumS   = x + sumS sL + sumS sR
                                  ,  sizeS  = 1 + sizeS sL + sizeS sR
                                  ,  diffS  = x - avgI iL
                                  }
         t _ = DS { sumS = 0, sizeS = 0, diffS = 0 }

class (Functor ff) => Zipper ff where
  fill    :: Ctx ff rr -> rr -> ff rr
  first   :: (rr -> Ctx ff rr -> aa) -> ff rr -> Maybe aa
  next    :: (rr -> Ctx ff rr -> aa) -> Ctx ff rr -> rr -> Maybe aa

  fillS   :: (Zipper gg) => Ctx ff (Fix2 ii ss gg) -> ss -> ff ss
  seekI   :: Ctx ff ss -> ff ii -> ii

data family Ctx (ff :: * -> *) :: * -> *

data Locc :: * -> * -> (* -> *) -> * where
  Loc ::  (Zipper ff, IncrementalC ff, ZipWith ff, Eq ii)
          =>  AlgC ff ii ss ->  (ss -> ii) ->  Fix2 ii ss ff ->  [Ctx ff (Fix2 ii ss ff)] ->  Locc ii ss ff

enter   ::  (Zipper ff, IncrementalC ff, ZipWith ff, Eq ii)
            => AlgC ff ii ss -> (ss -> ii) -> Fix2 ii ss ff -> Locc ii ss ff
leave   :: Locc ii ss ff -> Fix2 ii ss ff
up      :: Locc ii ss ff -> Maybe (Locc ii ss ff)
down    :: Locc ii ss ff -> Maybe (Locc ii ss ff)
right   :: Locc ii ss ff -> Maybe (Locc ii ss ff)
update  :: (Functor (Ctx ff)) => (Fix2 ii ss ff -> Fix2 ii ss ff) -> Locc ii ss ff -> Locc ii ss ff

digest ::  (Zipper ff, Zipper gg, IncrementalC ff) => AlgC ff ii ss -> Ctx ff (Fix2 ii ss gg) -> ss -> ii -> (ss, ii)
digest alg c s = second (seekI c) . passAround alg (fillS c s)

data family Thread (ff :: * -> *) aa :: *

class (Functor ff) => Paths ff where
  paths :: ff aa -> ff (Thread ff aa)

data instance Thread Tree aa = T aa | TL (Thread Tree aa) aa | TR (Thread Tree aa) aa

accumD :: (Fold (Thread ff aa), Paths ff) => Alg (Thread ff aa) ss -> ff aa -> ff ss
accumD alg = fmap (fold alg) . paths

empty        = Tip
singleton x  = Bin x empty empty
fold_        = fold

empty1      :: Tree1 aa
singleton1  :: aa -> Tree1 aa
insert1     :: (Ord aa) => aa -> Tree1 aa -> Tree1 aa

empty1 = tip

singleton1 x = bin x empty1 empty1

rotateL x tL tR@(Bin _ tRL tRR)
  | size tRL < 2 * size tRR  = singleL x tL tR
  | otherwise                = doubleL x tL tR
  where
    singleL x' tA (Bin y tB            tC) = Bin y (Bin x' tA tB) tC
    doubleL x' tA (Bin y (Bin z tB tC) tD) = Bin z (Bin x' tA tB) (Bin y tC tD)

rotateR x tL@(Bin _ tLL tLR) tR
  | size tLR < 2 * size tLL  = singleR x tL tR
  | otherwise                = doubleR x tL tR
  where
    singleR x' (Bin y tA tB           ) tC = Bin y tA            (Bin x' tB tC)
    doubleR x' (Bin y tA (Bin z tB tC)) tD = Bin z (Bin y tA tB) (Bin x' tC tD)

balance1 x tL tR
  | sL + sR <= 1  = bin x tL tR
  | sR >= 4 * sL  = rotateL1 x tL tR
  | sL >= 4 * sR  = rotateR1 x tL tR
  | otherwise     = bin x tL tR
  where
    sL   = size1 tL
    sR   = size1 tR
    rotateL1 x' tL' tR'@(Bin1 _ _ tRL tRR)
      | size1 tRL < 2 * size1 tRR  = singleL1 x' tL' tR'
      | otherwise                  = doubleL1 x' tL' tR'
      where
        singleL1 x'' tA (Bin1 _ y tB tC)               = bin y (bin x'' tA tB) tC
        doubleL1 x'' tA (Bin1 _ y (Bin1 _ z tB tC) tD) = bin z (bin x'' tA tB) (bin y tC tD)
    rotateR1 x' tL'@(Bin1 _ _ tLL tLR) tR'
      | size1 tLR < 2 * size1 tLL    = singleR1 x' tL' tR'
      | otherwise                    = doubleR1 x' tL' tR'
      where
        singleR1 x'' (Bin1 _ y tA tB) tC               = bin y tA (bin x'' tB tC)
        doubleR1 x'' (Bin1 _ y tA (Bin1 _ z tB tC)) tD = bin z (bin y tA tB) (bin x'' tC tD)

-- 

deriving instance (Show aa) => Show (Tree aa)
deriving instance (Eq aa) => Eq (Tree aa)

instance Functor Tree where
  fmap _ Tip            = Tip
  fmap f (Bin x tL tR)  = Bin (f x) (fmap f tL) (fmap f tR)

deriving instance (Show aa) => Show (Tree1 aa)
deriving instance (Eq aa) => Eq (Tree1 aa)

-- 

instance Functor (TreeF aa) where
  fmap _ TipF            = TipF
  fmap f (BinF a rL rR)  = BinF a (f rL) (f rR)

instance ZipWith (TreeF aa) where
  zipWith _  TipF               TipF              = TipF
  zipWith f  (BinF x1 sL1 sR1)  (BinF _ sL2 sR2)  = BinF x1 (f sL1 sL2) (f sR1 sR2)
  zipWith _  _                  _                 = error "zipWith: mismatch!"

deriving instance (Show aa, Show rr) => Show (TreeF aa rr)
deriving instance (Eq aa, Eq rr) => Eq (TreeF aa rr)

-- 

foldFix :: (Functor ff) => (ff ss -> ss) -> Fix ff -> ss
foldFix f = f . fmap (foldFix f) . out

deriving instance (Show (ff (Fix ff))) => Show (Fix ff)
deriving instance (Eq (ff (Fix ff))) => Eq (Fix ff)

-- 

deriving instance (Show ss, Show (ff rr)) => Show (Extt1 ss ff rr)
deriving instance (Eq ss, Eq (ff rr)) => Eq (Extt1 ss ff rr)

deriving instance (Show ii, Show ss, Show (ff rr)) => Show (Extt2 ii ss ff rr)
deriving instance (Eq ii, Eq ss, Eq (ff rr)) => Eq (Extt2 ii ss ff rr)

-- 

in1 s x = In (Ext1 s x)
out1 (In (Ext1 _ x)) = x
ann (In (Ext1 s _)) = s

size2 :: TreeU aa -> Int
size2 = ann

data TreeF3 aa rr  =  TipF3
                   |  BinF3 aa rr rr
  deriving (Show, Eq)

instance ZipWith (TreeF3 aa) where
  zipWith _  TipF3               TipF3              = TipF3
  zipWith f  (BinF3 x1 sL1 sR1)  (BinF3 _ sL2 sR2)  = BinF3 x1 (f sL1 sL2) (f sR1 sR2)
  zipWith _  _                   _                  = error "zipWith: mismatch!"

depthAlg :: (Int -> TreeF3 aa Int, aa -> Int -> TreeF3 aa Int)
depthIni :: Int


val3 :: Fix1 Int (TreeF3 Char)
val3 = bin 'b' (bin 'a' tip tip) (bin 'c' tip (bin 'd' tip tip))

val3_ :: Fix1 Int (TreeF3 Char)
val3_ = bin_ 'b' (bin_ 'a' tip_ tip_) (bin_ 'c' tip_ (bin_ 'd' tip_ tip_))
  where
    tip_          = inD_ depthAlg depthIni TipF3
    bin_ x tL tR  = inD_ depthAlg depthIni (BinF3 x tL tR)

test_inD3_1 = val3 == val3_

-- 

in2 i s x = In (Ext2 i s x)
out2 (In (Ext2 _ _ x)) = x
syn (In (Ext2 _ s _)) = s
inh (In (Ext2 i _ _)) = i

-- 

data     CountS = CS { sizeOf :: Int, countOf :: Int } deriving (Eq, Show)
newtype  CountI = CI' { startOf :: Int } deriving (Eq, Show)

countAlg :: (CountI -> (CountS, TreeF aa CountI), aa -> CountS -> CountS -> CountI -> (CountS, TreeF aa CountI))
countAlg = (t, b)
  where t _ = (CS 0 0, TipF)
        b x sL sR i = (CS (1 + sizeOf sL + sizeOf sR) (startOf i + sizeOf sL), BinF x i (CI' (1 + startOf i + sizeOf sL)))

countFun :: CountS -> CountI
countFun _ = CI' 1

instance TreeLike (Fix2 CountI CountS (TreeF aa)) aa where
  tip             = inC countAlg countFun TipF
  bin x tL tR     = inC countAlg countFun (BinF x tL tR)
  caseTree n t b  = case out2 n of { TipF -> t ; BinF x tL tR -> b x tL tR }

val4 :: Fix2 CountI CountS (TreeF Char)
val4 = bin 'b' (bin 'a' tip tip) (bin 'c' tip (bin 'd' tip tip))

toPairs n = go n []
  where go t = caseTree t id (\ x tL tR -> go tL . ((x, countOf (syn t)) :) . go tR)

-- 

deriving instance Show DiffI
deriving instance Eq DiffI
deriving instance Show DiffS
deriving instance Eq DiffS

val5 :: Fix2 DiffI DiffS (TreeF Float)
val5 = bin 2 (bin 1 tip tip) (bin 3 tip (bin 4 tip tip))

-- 

infixr 6 :+:
infixr 7 :*:, ::*::

deriving instance (Eq aa) => Eq (KK aa rr)
deriving instance (Show aa) => Show (KK aa rr)
deriving instance Show (UU rr)
deriving instance Eq (UU rr)
deriving instance (Eq rr) => Eq (II rr)
deriving instance (Show rr) => Show (II rr)
deriving instance (Eq (ff rr), Eq (gg rr)) => Eq ((ff :+: gg) rr)
deriving instance (Show (ff rr), Show (gg rr)) => Show ((ff :+: gg) rr)
deriving instance (Eq (ff rr), Eq (gg rr)) => Eq ((ff ::*:: gg) rr)
deriving instance (Show (ff rr), Show (gg rr)) => Show ((ff ::*:: gg) rr)

-- 

instance Functor (KK a) where
  fmap _ (K a) = K a

instance Functor UU where
  fmap _ U = U

instance Functor II where
  fmap f (I r) = I (f r)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (L x) = L (fmap f x)
  fmap f (R y) = R (fmap f y)

instance (Functor f, Functor g) => Functor (f ::*:: g) where
  fmap f (x :*: y) = fmap f x :*: fmap f y

-- 

instance ZipWith (KK a) where
  zipWith _ (K x) (K _) = K x

instance ZipWith UU where
  zipWith _ U U = U

instance ZipWith II where
  zipWith f (I x) (I y) = I (f x y)

instance (ZipWith f, ZipWith g) => ZipWith (f :+: g) where
  zipWith f (L x) (L y) = L (zipWith f x y)
  zipWith f (R x) (R y) = R (zipWith f x y)
  zipWith _ _     _     = error "zipWith: mismatch!"

instance (ZipWith f, ZipWith g) => ZipWith (f ::*:: g) where
  zipWith f (x1 :*: y1) (x2 :*: y2) = zipWith f x1 x2 :*: zipWith f y1 y2

-- 

type family PF tt :: * -> *

class Regular tt where
  from  :: tt -> PF tt tt
  to    :: PF tt tt -> tt

-- 

impossible :: a
impossible = error "Impossible!"

-- 

type instance AlgU (KK aa) ss = aa -> ss
instance IncrementalU (KK a) where
  pullUp f (K x) = f x

type instance AlgU UU ss = ss
instance IncrementalU UU where
  pullUp f U = f

type instance AlgU II ss = ss -> ss
instance IncrementalU II where
  pullUp f (I x) = f x

type instance AlgU (ff :+: gg) ss = (AlgU ff ss, AlgU gg ss)
instance (IncrementalU f, IncrementalU g) => IncrementalU (f :+: g) where
  pullUp (f, _) (L x) = pullUp f x
  pullUp (_, g) (R x) = pullUp g x

type instance AlgU (KK aa ::*:: gg) ss = aa -> AlgU gg ss
instance (IncrementalU g) => IncrementalU (KK a ::*:: g) where
  pullUp f (K x :*: y) = pullUp (f x) y

type instance AlgU (II ::*:: gg) ss = ss -> AlgU gg ss
instance (IncrementalU g) => IncrementalU (II ::*:: g) where
  pullUp f (I x :*: y) = pullUp (f x) y

foldF :: (Regular a, IncrementalU (PF a), Functor (PF a)) => AlgU (PF a) r -> a -> r
foldF f = pullUp f . fmap (\ x -> foldF f x) . from

-- 

type instance AlgD (KK aa) ii = ()
instance IncrementalD (KK aa) where
  pushDown _ (K x) _ = K x

type instance AlgD UU ii = ()
instance IncrementalD UU where
  pushDown _ U _ = U

type instance AlgD II ii = ii -> ii
instance IncrementalD II where
  pushDown f (I _) i = I (f i)

type instance AlgD (ff :+: gg) ii = (AlgD ff ii, AlgD gg ii)
instance (IncrementalD ff, IncrementalD gg) => IncrementalD (ff :+: gg) where
  pushDown (f, _) (L x) = L . pushDown f x
  pushDown (_, g) (R y) = R . pushDown g y

type instance AlgD (KK aa ::*:: gg) ii = aa -> AlgD gg ii
instance (IncrementalD gg) => IncrementalD (KK aa ::*:: gg) where
  pushDown f (K x :*: y) = (:*:) (K x) . pushDown (f x) y

type instance AlgD (II ::*:: gg) ii = ii -> (ii, AlgD gg ii)
instance (IncrementalD gg) => IncrementalD (II ::*:: gg) where
  pushDown f (I _ :*: y) i1 = let (i2, g) = f i1 in I i2 :*: pushDown g y i1

-- 

type instance AlgC (KK aa) ii ss = aa -> ii -> ss
instance IncrementalC (KK aa) where
  passAround f (K x) i = (f x i, K x)

type instance AlgC UU ii ss = ii -> ss
instance IncrementalC UU where
  passAround f U i = (f i, U)

type instance AlgC (KK aa ::*:: gg) ii ss = aa -> AlgC gg ii ss
instance (IncrementalC gg) => IncrementalC (KK aa ::*:: gg) where
  passAround f (K x :*: y) = second (K x :*:) . passAround (f x) y

type instance AlgC (ff :+: gg) ii ss = (AlgC ff ii ss, AlgC gg ii ss)
instance (IncrementalC ff, IncrementalC gg) => IncrementalC (ff :+: gg) where
  passAround (f  , _  ) (L  x) = second L  . passAround f  x
  passAround (_  , g  ) (R  x) = second R  . passAround g  x

-- 

diffAlgPF :: AlgC (TreePF Float) DiffI DiffS

instance TreeLike (Fix2 DiffI DiffS (TreePF Float)) Float where
  tip             = inC diffAlgPF diffFun (L U)
  bin x tL tR     = inC diffAlgPF diffFun (R (K x :*: I tL :*: I tR))
  caseTree n t b  = case out2 n of { L U -> t ; R (K x :*: I tL :*: I tR) -> b x tL tR }

val6 :: Fix2 DiffI DiffS (TreePF Float)
val6 = bin 2 (bin 1 tip tip) (bin 3 tip (bin 4 tip tip))

tmap :: (TreeLike tt1 aa, TreeLike tt2 bb) => (aa -> bb) -> tt1 -> tt2
tmap f t = caseTree t tip (\ x tL tR -> bin (f x) (tmap f tL) (tmap f tR))

-- 

countAlg' :: AlgC (TreePF aa) CountI CountS
countAlg' = (t, bL)
  where  t _ = CS 0 0
         bL _ sL iL = (bR, iL)
           where bR sR iR = (s, iR')
                   where s = CS (1 + sizeOf sL + sizeOf sR) (startOf iL + sizeOf sL)
                         iR' = CI' (1 + startOf iR + sizeOf sL)

instance TreeLike (Fix2 CountI CountS (TreePF aa)) aa where
  tip             = inC countAlg' countFun (L U)
  bin x tL tR     = inC countAlg' countFun (R (K x :*: I tL :*: I tR))
  caseTree n t b  = case out2 n of { L U -> t ; R (K x :*: I tL :*: I tR) -> b x tL tR }

val6b :: Fix2 CountI CountS (TreePF Char)
val6b = bin 'x' (bin 'w' (bin 'v' tip tip) tip) (bin 'y' tip (bin 'z' tip tip))

-- 

data instance Ctx (KK a) rr
data instance Ctx UU rr
data instance Ctx II rr = CI
data instance Ctx (ff :+: gg) rr = CL (Ctx ff rr)
                                 | CR (Ctx gg rr)
data instance Ctx (ff ::*:: gg) rr = C1 (Ctx ff rr) (gg rr)
                                   | C2 (ff rr) (Ctx gg rr)

-- 

instance Functor (Ctx (KK a)) where
  fmap _ _ = impossible

instance Functor (Ctx UU) where
  fmap _ _ = impossible

instance Functor (Ctx II) where
  fmap _ CI = CI

instance (Functor (Ctx f), Functor (Ctx g)) => Functor (Ctx (f :+: g)) where
  fmap f (CL c) = CL (fmap f c)
  fmap f (CR c) = CR (fmap f c)

instance (Functor f, Functor g, Functor (Ctx f), Functor (Ctx g))
         => Functor (Ctx (f ::*:: g)) where
  fmap f (C1 c y) = C1 (fmap f c) (fmap f y)
  fmap f (C2 x c) = C2 (fmap f x) (fmap f c)

-- 

instance Show (Ctx (KK a) r) where show _ = impossible
instance Show (Ctx UU r) where show _ = impossible
deriving instance (Show r) => Show (Ctx II r)
deriving instance (Show (Ctx f r), Show (Ctx g r)) => Show (Ctx (f :+: g) r)
deriving instance (Show (f r), Show (g r), Show (Ctx f r), Show (Ctx g r)) => Show (Ctx (f ::*:: g) r)

-- 

instance Eq (Ctx (KK a) r) where _ == _ = True
instance Eq (Ctx UU r) where _ == _ = True
deriving instance Eq (Ctx II r)
deriving instance (Eq (Ctx f r), Eq (Ctx g r)) => Eq (Ctx (f :+: g) r)
deriving instance (Eq (f r), Eq (g r), Eq (Ctx f r), Eq (Ctx g r)) => Eq (Ctx (f ::*:: g) r)

-- 

instance IncrementalC (Ctx (KK aa)) where
  passAround _ _ _ = impossible

instance IncrementalC (Ctx UU) where
  passAround _ _ _ = impossible

type instance AlgC (Ctx II) ii ss = ii -> ss
instance IncrementalC (Ctx II) where
  passAround f CI i = (f i, CI)

type instance AlgC (Ctx (ff :+: gg)) ii ss = (AlgC (Ctx ff) ii ss, AlgC (Ctx gg) ii ss)
instance (IncrementalC (Ctx ff), IncrementalC (Ctx gg)) => IncrementalC (Ctx (ff :+: gg)) where
  passAround (f, _) (CL c) = second CL . passAround f c
  passAround (_, g) (CR c) = second CR . passAround g c

type instance AlgC (Ctx (ff ::*:: gg)) ii ss = (AlgC (Ctx ff) ii ss, ss -> AlgC gg ii ss, AlgC ff ii ss, ss -> AlgC (Ctx gg) ii ss)
instance (IncrementalC ff, IncrementalC gg, IncrementalC (Ctx ff), IncrementalC (Ctx gg)) => IncrementalC (Ctx (ff ::*:: gg)) where
  passAround (fc, g, _, _) (C1 c y) i =
    let  (sc, ci) = passAround fc c i
         (sy, yi) = passAround (g sc) y i
    in   (sy, C1 ci yi)
  passAround (_, _, f, gc) (C2 x c) i =
    let  (sx, xi) = passAround f x i
         (sc, ci) = passAround (gc sx) c i
    in   (sc, C2 xi ci)

-- 

instance Zipper (KK aa) where
  fill _ _ = impossible
  first _ _ = Nothing
  next _ _ _ = Nothing
  fillS _ _ = impossible
  seekI _ _ = impossible

instance Zipper UU where
  fill _ _ = impossible
  first _ _ = Nothing
  next _ _ _ = Nothing
  fillS _ _ = impossible
  seekI _ _ = impossible

instance Zipper II where
  fill _ x = I x
  first f (I r)  = Just (f r CI)
  next _ _ _ = Nothing
  fillS _ s = I s
  seekI _ (I i) = i

instance (Zipper ff, Zipper gg) => Zipper (ff :+: gg) where
  fill (CL c) x = L (fill c x)
  fill (CR c) y = R (fill c y)
  first f (L x) = first (\ foc -> f foc . CL) x
  first f (R y) = first (\ foc -> f foc . CR) y
  next f (CL c) x = next  (\ foc -> f foc . CL) c x
  next f (CR c) y = next  (\ foc -> f foc . CR) c y
  fillS (CL c) s = L (fillS c s)
  fillS (CR c) s = R (fillS c s)
  seekI (CL c) (L x) = seekI c x
  seekI (CR c) (R y) = seekI c y

instance (Zipper ff, Zipper gg, IncrementalC ff, IncrementalC gg) => Zipper (ff ::*:: gg) where
  fill (C1 c y) x = fill c x :*: y
  fill (C2 x c) y = x :*: fill c y
  first f (x :*: y) =
    first (\ foc c -> f foc (C1 c y)) x `mplus` first (\ foc c -> f foc (C2 x c)) y
  next f (C1 c y) x =
    next (\ foc c' -> f foc (C1 c' y )) c x `mplus` first (\ foc c' -> f foc (C2 (fill c x) c')) y
  next f (C2 x c) y =
    next (\ foc c' -> f foc (C2 x  c')) c y
  fillS (C1 c y) s = fillS c s :*: fmap syn y
  fillS (C2 x c) s = fmap syn x :*: fillS c s
  seekI (C1 c _) (x :*: _) = seekI c x
  seekI (C2 _ c) (_ :*: y) = seekI c y

-- 

focus :: Locc ii ss ff -> Fix2 ii ss ff
focus (Loc _ _ foc _) = foc

instance (Show ii, Show ss, Show (ff (Fix2 ii ss ff)), Show (Fix2 ii ss ff), Show (Ctx ff (Fix2 ii ss ff))) => Show (Locc ii ss ff) where
  show (Loc _ _ foc cs) = "(Loc (" ++ show foc ++ ") " ++ show cs ++ ")"

instance (Eq ii, Eq ss, Eq (ff (Fix2 ii ss ff)), Eq (Fix2 ii ss ff), Eq (Ctx ff (Fix2 ii ss ff))) => Eq (Locc ii ss ff) where
  Loc _ _ foc1 cs1 == Loc _ _ foc2 cs2 = foc1 == foc2 && cs1 == cs2

-- 

enter alg fun foc = Loc alg fun foc []

--  Works for Diff and Count algebras and all test cases
up (Loc _   _   _   []    )  = Nothing
up (Loc alg fun foc (c:cs))  = Just (Loc alg fun foc' cs)
  where
    fun' s | null cs    = fun s    --  top-level
           | otherwise  = inh foc  --  every other level
    foc' = inC alg fun' (fill c foc)

leave (Loc _ _ foc []) = foc
leave loc              = leave (fromJust (up loc))

leaveM :: (Eq ii, ZipWith ff, Monad m) => Locc ii ss ff -> m (Fix2 ii ss ff)
leaveM = return . leave

down (Loc alg fun foc cs) =
  first (\ foc' c -> Loc alg fun foc' (c:cs)) (out2 foc)

--  See note for 'update'.
pushCtxs ::  (Functor (Ctx ff), ZipWith ff, Eq ii, Zipper ff, IncrementalC ff)
             => AlgC ff ii ss -> ss -> ii -> [Ctx ff (Fix2 ii ss ff)] -> (ss, ii, [Ctx ff (Fix2 ii ss ff)])
pushCtxs _   s     i     []     = (s, i, [])
pushCtxs alg s_bot i_top (c:cs) = (s_top, i_bot, c':cs')
  where
    (s, i_bot) = digest alg c s_bot i
    c' = fmap (inC alg (const i) . out2) c
    (s_top, i, cs') = pushCtxs alg s i_top cs

right (Loc _   _   _   []    ) = Nothing
right (Loc alg fun foc (c:cs)) = next (\ foc' c' -> Loc alg fun foc' (c':cs)) c foc

--  Works for given Diff algebra, but may not work with algebras that pass
--  values between siblings. I fmap over each context, so there is only an 'i'
--  coming from the top of the context, not the siblings. This seems to work for
--  Count, so I'm not sure how to show that it doesn't work.
update mod (Loc alg fun foc cs) = Loc alg fun foc2 cs1
  where
    foc1 = mod foc
    (s, i, cs1) = pushCtxs alg (syn foc1) (fun s) cs
    foc2 = inC alg (const i) (out2 foc1)

updateM f = return . update f

on :: (Fix2 ii ss ff -> Fix2 ii ss ff) -> Locc ii ss ff -> Fix2 ii ss ff
on f (Loc _ _ foc _) = f foc

-- 

val7 = enter diffAlgPF diffFun val6
test_zipper_1 = val7 == fromJust (return val7 >>= down >>= up)
test_zipper_2 = val7 == fromJust (return val7 >>= down >>= down >>= up >>= up)
test_zipper_3 = val7 == fromJust (return val7 >>= down >>= right >>= up)
test_zipper_4 = focus val7 == fromJust (return val7 >>= down >>= right >>= down >>= leaveM)
test_zipper_5 = val7 == update id val7
val7b = enter diffAlgPF diffFun (bin 1 tip tip :: Fix2 DiffI DiffS (TreePF Float))
test_zipper_6 = Just val7b == (return val7b >>= down >>= updateM id >>= up)
test_zipper_7 = bin 2 (bin 1 tip tip) (bin 0 tip tip) == fromJust (return val7 >>= down >>= right >>= updateM (const (bin 0 tip tip)) >>= leaveM)
val7c = enter countAlg' countFun val6b
test_zipper_8 = val7c == fromJust (return val7c >>= down >>= up)
test_zipper_9 = val7c == fromJust (return val7c >>= down >>= right >>= up)
test_zipper_10 = val7c == fromJust (return val7c >>= down >>= down >>= right >>= up >>= up)
test_zipper_11 = bin 'x' (bin 'w' tip tip) (bin 'y' tip (bin 'z' tip tip)) == fromJust (return val7c >>= down >>= down >>= updateM (const tip) >>= leaveM)

--  The following should return True.
test_zipper
  =  test_zipper_1
  && test_zipper_2
  && test_zipper_3
  && test_zipper_4
  && test_zipper_5
  && test_zipper_6
  && test_zipper_7
  && test_zipper_8
  && test_zipper_9
  && test_zipper_10
  && test_zipper_11

-- 

type instance Alg (Thread Tree aa) ss = (aa -> ss, ss -> aa -> ss, ss -> aa -> ss)

instance Fold (Thread Tree aa) where
  fold       (t, _, _) (T x)     = t x
  fold alg@  (_, l, _) (TL t x)   = l (fold alg t) x
  fold alg@  (_, _, r) (TR t x)  = r (fold alg t) x

deriving instance (Show aa) => Show (Thread Tree aa)
deriving instance (Eq aa) => Eq (Thread Tree aa)

instance Paths Tree where
  paths Tip           = Tip
  paths (Bin x tL tR) = Bin (T x) (fmap (lt x) (paths tL)) (fmap (rt x) (paths tR))
    where
      lt y = fold (TL (T y), TL, TR)
      rt y = fold (TR (T y), TL, TR)
