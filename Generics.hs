{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}
module Generics where

import Data.Kind

import GHC.Generics as GHC
import Generics.SOP as SOP
import Generics.SOP.Type.Metadata as SOP.T

data Tree a =
    None
  | One a
  | Join (Tree a) (Tree a)

class IsTree t where
  cataTree ::
       r None
    -> (forall a . r (One a))
    -> (forall t1 t2 . (IsTree t1, IsTree t2) => r t1 -> r t2 -> r (Join t1 t2))
    -> r t

class AsTree c xs where
  viewTree ::
       Proxy c
    -> r '[]
    -> (forall a . c a => r '[a])
    -> (forall ys zs rs . (AsTree c ys, AsTree c zs, Split rs rs ~ '(ys, zs)) => r ys -> r zs -> r rs)
    -> r xs

instance IsTree None where
  cataTree none _one _join = none

instance AsTree c '[] where
  viewTree _p none _one _join = none

instance IsTree (One a) where
  cataTree _none one _join = one

instance c a => AsTree c '[a] where
  viewTree _p _none one _join = one

instance (IsTree t1, IsTree t2) => IsTree (Join t1 t2) where
  cataTree none one join =
    join (cataTree none one join) (cataTree none one join)

instance (AsTree c ys, AsTree c zs, Split (x1 : x2 : xs) (x1 : x2 : xs) ~ '(ys, zs)) => AsTree c (x1 : x2 : xs) where
  viewTree p none one join =
    join (viewTree p none one join) (viewTree p none one join)

type family ToTree (xs :: [a]) :: Tree a where
  ToTree '[]  = None
  ToTree '[a] = One a
  ToTree xs   = Join' (Split xs xs)

type family Join' (pair :: ([a], [a])) :: Tree a where
  Join' '(xs, ys) = Join (ToTree xs) (ToTree ys)

type family Split (single :: [a]) (double :: [a]) :: ([a], [a]) where
  Split (x : xs) (_ : _ : ys) = AddFst x (Split xs ys)
  Split xs       _            = '( '[], xs)

type family AddFst (x :: a) (pair :: ([a], [a])) :: ([a], [a]) where
  AddFst x p = '(x : Fst p, Snd p)

type family Fst (pair :: (a, b)) :: a where
  Fst '(a, b) = a

type family Snd (pair :: (a, b)) :: b where
  Snd '(a, b) = b

type GRep a = GRepFromCodeData (DatatypeInfoOf a) (Code a)

type family GRepFromCodeData (d :: SOP.T.DatatypeInfo) (xss :: [[Type]]) where
  GRepFromCodeData (SOP.T.ADT m d cs) xss =
    D1 (MetaData d m "" False) (GRepFromCodeSum (ToTree cs) (ToTree xss))
  GRepFromCodeData (SOP.T.Newtype m d c) xss =
    D1 (MetaData d m "" True) (GRepFromCodeSum (ToTree '[c]) (ToTree xss))

type family GRepFromCodeSum (c :: Tree SOP.T.ConstructorInfo) (xs :: Tree [Type]) :: Type -> Type where
  GRepFromCodeSum None None                 = V1
  GRepFromCodeSum (One c) (One x)           = GRepFromCodeConstr c x
  GRepFromCodeSum (Join c1 c2) (Join x1 x2) = GRepFromCodeSum c1 x1 :+: GRepFromCodeSum c2 x2

type family GRepFromCodeConstr (c :: SOP.T.ConstructorInfo) (xs :: [Type]) :: Type -> Type where
  GRepFromCodeConstr (SOP.T.Constructor c) xs =
    C1 (MetaCons c PrefixI False) (GRepFromCodeProd (ToTree xs))
  GRepFromCodeConstr (SOP.T.Infix c a f) xs =
    C1 (MetaCons c (InfixI a f) False) (GRepFromCodeProd (ToTree xs))
  GRepFromCodeConstr (SOP.T.Record c fs) xs =
    C1 (MetaCons c PrefixI True) (GRepFromCodeRecord (ToTree fs) (ToTree xs))

type family GRepFromCodeProd (c :: Tree Type) :: Type -> Type where
  GRepFromCodeProd None         = U1
  GRepFromCodeProd (One c)      = S1 (MetaSel Nothing NoSourceUnpackedness NoSourceStrictness DecidedLazy) (Rec0 c)
  GRepFromCodeProd (Join c1 c2) = GRepFromCodeProd c1 :*: GRepFromCodeProd c2

type family GRepFromCodeRecord (f :: Tree SOP.T.FieldInfo) (xs :: Tree Type) :: Type -> Type where
  GRepFromCodeRecord None None = U1
  GRepFromCodeRecord (One ('SOP.T.FieldInfo f)) (One x) =
    S1 (MetaSel (Just f) NoSourceUnpackedness NoSourceStrictness DecidedLazy) (Rec0 x)
  GRepFromCodeRecord (Join f1 f2) (Join x1 x2) = GRepFromCodeRecord f1 x1 :*: GRepFromCodeRecord f2 x2

gfrom :: forall a x . (GFromToData (SOP.DatatypeInfoOf a) (Code a), SOP.Generic a) => a -> GRep a x
gfrom = gfromData (Proxy @(SOP.DatatypeInfoOf a)) . unSOP . SOP.from

gto :: forall a x . (GFromToData (SOP.DatatypeInfoOf a) (Code a), SOP.Generic a) => GRep a x -> a
gto = SOP.to . SOP . gtoData (Proxy @(SOP.DatatypeInfoOf a))

class GFromToData (d :: SOP.T.DatatypeInfo) (xss :: [[Type]]) where
  gfromData :: Proxy d -> NS (NP I) xss -> GRepFromCodeData d xss x
  gtoData   :: Proxy d -> GRepFromCodeData d xss x -> NS (NP I) xss

instance GFromToSum cs xss => GFromToData (SOP.T.ADT m d cs) xss where
  gfromData _p ns     = M1 (gfromSum (Proxy @cs) ns)
  gtoData   _p (M1 r) = gtoSum (Proxy @cs) r

instance GFromToSum '[c] xss => GFromToData (SOP.T.Newtype m d c) xss where
  gfromData _p ns     = M1 (gfromSum (Proxy @'[c]) ns)
  gtoData   _p (M1 r) = gtoSum (Proxy @'[c]) r

class GFromToSum (cs :: [SOP.T.ConstructorInfo]) (xss :: [[Type]]) where
  gfromSum :: Proxy cs -> NS (NP I) xss -> GRepFromCodeSum (ToTree cs) (ToTree xss) x
  gtoSum   :: Proxy cs -> GRepFromCodeSum (ToTree cs) (ToTree xss) x -> NS (NP I) xss

instance GFromToSum '[] '[] where
  gfromSum _p ns = case ns of {}
  gtoSum   _p r  = case r of {}

instance GFromToConstr c xs => GFromToSum '[c] '[xs] where
  gfromSum _p (Z x) = gfromConstr (Proxy @c) x
  gfromSum _p (S y) = case y of {}
  gtoSum   _p r     = Z (gtoConstr (Proxy @c) r)

instance
  ( Splittable (x1 : x2 : xs) (x1 : x2 : xs)
  , Split (x1 : x2 : xs) (x1 : x2 : xs) ~ '(ys, zs)
  , Split (c1 : c2 : cs) (c1 : c2 : cs) ~ '(ds, es)
  , GFromToSum ds ys
  , GFromToSum es zs
  ) => GFromToSum (c1 : c2 : cs) (x1 : x2 : xs) where
  gfromSum _p ns =
    case splitSum (Proxy @(x1 : x2 : xs)) ns of
      Left s -> L1 (gfromSum (Proxy @ds) s)
      Right s -> R1 (gfromSum (Proxy @es) s)
  gtoSum _p (L1 s) = joinSum (Proxy @(x1 : x2 : xs)) (Left (gtoSum (Proxy @ds) s))
  gtoSum _p (R1 s) = joinSum (Proxy @(x1 : x2 : xs)) (Right (gtoSum (Proxy @es) s))

class GFromToConstr (c :: SOP.T.ConstructorInfo) (xs :: [Type]) where
  gfromConstr :: Proxy c -> NP I xs -> GRepFromCodeConstr c xs x
  gtoConstr   :: Proxy c -> GRepFromCodeConstr c xs x -> NP I xs

instance GFromToProd xs => GFromToConstr (SOP.T.Constructor c) xs where
  gfromConstr _p np = M1 (gfromProd np)
  gtoConstr _p (M1 r) = gtoProd r

instance GFromToProd xs => GFromToConstr (SOP.T.Infix c a f) xs where
  gfromConstr _p np = M1 (gfromProd np)
  gtoConstr _p (M1 r) = gtoProd r

instance GFromToRecord fs xs => GFromToConstr (SOP.T.Record c fs) xs where
  gfromConstr _p np = M1 (gfromRecord (Proxy @fs) np)
  gtoConstr _p (M1 r) = gtoRecord (Proxy @fs) r

class GFromToProd (xs :: [Type]) where
  gfromProd :: NP I xs -> GRepFromCodeProd (ToTree xs) x
  gtoProd :: GRepFromCodeProd (ToTree xs) x -> NP I xs

instance GFromToProd '[] where
  gfromProd Nil = U1
  gtoProd U1 = Nil

instance GFromToProd '[x] where
  gfromProd (I x :* Nil) = M1 (K1 x)
  gtoProd (M1 (K1 x)) = I x :* Nil

instance
  ( Splittable (x1 : x2 : xs) (x1 : x2 : xs)
  , Split (x1 : x2 : xs) (x1 : x2 : xs) ~ '(ys, zs)
  , GFromToProd ys
  , GFromToProd zs
  ) => GFromToProd (x1 : x2 : xs) where
  gfromProd np =
    case splitProd (Proxy @(x1 : x2 : xs)) np of
      (p1, p2) -> gfromProd p1 :*: gfromProd p2
  gtoProd (p1 :*: p2) =
    joinProd (Proxy @(x1 : x2 : xs)) (gtoProd p1, gtoProd p2)

class GFromToRecord (fs :: [SOP.T.FieldInfo]) (xs :: [Type]) where
  gfromRecord :: Proxy fs -> NP I xs -> GRepFromCodeRecord (ToTree fs) (ToTree xs) x
  gtoRecord :: Proxy fs -> GRepFromCodeRecord (ToTree fs) (ToTree xs) x -> NP I xs

instance GFromToRecord '[] '[] where
  gfromRecord _p Nil = U1
  gtoRecord _p U1 = Nil

instance GFromToRecord '[ 'SOP.T.FieldInfo f] '[x] where
  gfromRecord _p (I x :* Nil) = M1 (K1 x)
  gtoRecord _p (M1 (K1 x)) = I x :* Nil

instance
  ( Splittable (x1 : x2 : xs) (x1 : x2 : xs)
  , Split (x1 : x2 : xs) (x1 : x2 : xs) ~ '(ys, zs)
  , Split (f1 : f2 : fs) (f1 : f2 : fs) ~ '(ds, es)
  , GFromToRecord ds ys
  , GFromToRecord es zs
  ) => GFromToRecord (f1 : f2 : fs) (x1 : x2 : xs) where
  gfromRecord _p np =
    case splitProd (Proxy @(x1 : x2 : xs)) np of
      (p1, p2) -> gfromRecord (Proxy @ds) p1 :*: gfromRecord (Proxy @es) p2
  gtoRecord _p (p1 :*: p2) =
    joinProd (Proxy @(x1 : x2 : xs)) (gtoRecord (Proxy @ds) p1, gtoRecord (Proxy @es) p2)

type PairEta p = p ~ '(Fst p, Snd p)

class (PairEta (Split xs rs)) => Splittable xs rs where
  splitSum :: (Split xs rs ~ '(ys, zs)) => Proxy rs -> NS f xs -> Either (NS f ys) (NS f zs)
  joinSum :: (Split xs rs ~ '(ys, zs)) => Proxy rs -> Either (NS f ys) (NS f zs) -> NS f xs
  splitProd :: (Split xs rs ~ '(ys, zs)) => Proxy rs -> NP f xs -> (NP f ys, NP f zs)
  joinProd :: (Split xs rs ~ '(ys, zs)) => Proxy rs -> (NP f ys, NP f zs) -> NP f xs

instance Splittable xs rs => Splittable (x : xs) (r1 : r2 : rs) where
  splitSum _ (Z x)  = Left (Z x)
  splitSum _ (S ns) =
    case splitSum (Proxy @rs) ns of
      Left  s -> Left (S s)
      Right s -> Right s

  joinSum _ (Left (Z x)) = Z x
  joinSum _ (Left (S s)) = S (joinSum (Proxy @rs) (Left s))
  joinSum _ (Right s)    = S (joinSum (Proxy @rs) (Right s))

  splitProd _ (x :* xs) =
    let
      (ys, zs) = splitProd (Proxy @rs) xs
    in
      (x :* ys, zs)

  joinProd _ (x :* ys, zs) = x :* joinProd (Proxy @rs) (ys, zs)

instance Splittable xs '[r1] where
  splitSum _ ns = Right ns
  joinSum _ (Left ns) = case ns of {}
  joinSum _ (Right ns) = ns
  splitProd _ np = (Nil, np)
  joinProd _ (Nil, np) = np

instance Splittable xs '[] where
  splitSum _ ns = Right ns
  joinSum _ (Left ns) = case ns of {}
  joinSum _ (Right ns) = ns
  splitProd _ np = (Nil, np)
  joinProd _ (Nil, np) = np



{-
instance GFromSum '[] where
  gfromSum x = case x of {}

instance GFromProd x => GFromSum '[x] where
  gfromSum (Z x) = gfromProd x

class GFromProd xs where
  gfromProd :: NP I xs -> GRepFromCodeProd (ToTree xs) x

class SplitSum xs ys where
  splitSum :: (Split xs ys ~ '(ps, qs)) => NS f xs -> Either (NS f ps) (NS f qs)
-}

{-
newtype GFromSumType x xss = MkGFromSumType { unGFromSumType :: NS (NP I) xss -> GRepFromCodeSum (ToTree xss) x }

gfromSum :: AsTree (AsTree Top) xss => NS (NP I) xss -> GRepFromCodeSum (ToTree xss) x
gfromSum = unGFromSumType $
  viewTree
    (Proxy @(AsTree Top))
    (MkGFromSumType (\ x -> case x of {}))
    (MkGFromSumType (\ (Z x) -> gfromProd x))
    (\ (MkGFromSumType f1) (MkGFromSumType f2) -> MkGFromSumType (\ x -> _))

splitSum :: (Split xs xs ~ '(ys, zs)) => NS f xs -> Either (NS f ys) (NS f zs)
splitSum = undefined

splitProduct :: (Split xs xs ~ '(ys, zs)) => NP f xs -> (NP f ys, NP f ys)
splitProduct = undefined

newtype GFromProdType x xs = MkGFromProdType { unGFromProdType :: NP I xs -> GRepFromCodeProd (ToTree xs) x }

gfromProd :: AsTree Top xs => NP I xs -> GRepFromCodeProd (ToTree xs) x
gfromProd = _
-}
