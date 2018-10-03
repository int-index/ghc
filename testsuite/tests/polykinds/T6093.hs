{-# LANGUAGE GADTs, RankNTypes, PolyKinds #-}
module T6093 where

import Data.Kind (Type)

-- Polymorphic kind recursion
data R :: forall k. k -> Type where
    MkR :: R f -> R (f ())

data IOWitness (a :: k) = IOW

data Ty :: forall k. k -> Type where
  SimpleTy :: IOWitness a -> Ty a
  ConstructedTy :: Ty f -> Ty a -> Ty (f a)
