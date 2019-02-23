{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
{-# OPTIONS_GHC -dsuppress-all #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Test where

import           Test.Inspection
import           Data.Coerce
import qualified Generics.SOP                   as SOP
import           Generics.SOP.TH
import qualified GHC.Generics                   as GHC
import           GHCGenericsFromSOP

data EnumType = One | Two | Three
  deriving GHC.Generic

data Record = MkRecord { field1, field2, field3, field4, field5 :: ()}
  deriving GHC.Generic

data List a = Cons a (List a) | Nil
  deriving GHC.Generic

deriveGeneric ''EnumType
deriveGeneric ''Record
deriveGeneric ''List

recordToDirect, recordToSOP :: GHC.Rep Record a -> Record
recordToDirect = GHC.to
recordToSOP = toSOP

recordFromDirect, recordFromSOP :: Record -> GHC.Rep Record a
recordFromDirect = GHC.from
recordFromSOP = fromSOP

fromSOP :: forall a x . _ => a -> GHC.Rep a x
fromSOP = coerce $ GHC.from @(FromSOPGeneric a)

toSOP :: forall a x . _ => GHC.Rep a x -> a
toSOP = coerce $ GHC.to @(FromSOPGeneric a)

enumFromDirect, enumFromSOP :: EnumType -> GHC.Rep EnumType a
enumFromDirect = GHC.from
enumFromSOP    = fromSOP

enumToDirect, enumToSOP :: GHC.Rep EnumType a -> EnumType
enumToDirect = GHC.to
enumToSOP = toSOP

listToDirect, listToSOP :: GHC.Rep (List Int) x -> List Int
listToDirect = GHC.to
listToSOP = toSOP

listFromDirect, listFromSOP :: List Int -> GHC.Rep (List Int) x
listFromDirect = GHC.from
listFromSOP = fromSOP

inspect $ 'recordToDirect   ==- 'recordToSOP
inspect $ 'recordFromDirect ==- 'recordFromSOP
inspect $ 'enumFromDirect ==- 'enumFromSOP
inspect $ 'enumToDirect ==- 'enumToSOP
inspect $ 'listToDirect ==- 'listToSOP
inspect $ 'listFromDirect ==- 'listFromSOP

main = putStrLn "All inspection tests have passed at compile time"
