{-# LANGUAGE GADTs, ExistentialQuantification, KindSignatures, RankNTypes #-}

-- Succeeds (needs the (Ord a) in TypeSet 
-- c.f. gadt21.hs

-- However, it's a useful test because it unearthed a bug
-- in free-variable-finding

module Expr where

import Data.Kind (Type)
import Data.Set (Set)

data Ty a where
    TyInt     :: Ty Int
    TySet     :: Ord a => Ty a -> Ty (Set a)
    TyFun     :: Ty a -> Ty b -> Ty (a -> b)

data Expr :: Type -> Type where
    Const :: Ty a -> a -> Expr a

data DynExpr = forall a. DynExpr (Expr a)

withOrdDynExpr :: DynExpr -> (forall a. Ord a => Expr a -> b) -> Maybe b
withOrdDynExpr (DynExpr e@(Const (TySet _) _)) f = Just (f e)
withOrdDynExpr (DynExpr e@(Const TyInt _)) f = Just (f e)
withOrdDynExpr _ _ = Nothing
