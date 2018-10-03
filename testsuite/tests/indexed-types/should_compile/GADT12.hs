{-# LANGUAGE TypeFamilies, GADTs, ScopedTypeVariables, KindSignatures #-}
{-# LANGUAGE EmptyDataDecls #-}

-- Tests whether a type signature can refine a type
-- See the definition of bug2a

module ShouldCompile where

import Data.Kind (Type)

data Typed
data Untyped

type family TU a b :: Type
type instance TU Typed b = b
type instance TU Untyped b = ()

-- A type witness type, use eg. for pattern-matching on types
data Ty a where
    TyInt     :: Ty Int
    TyBool    :: Ty Bool
    TyString  :: Ty String
    TyList    :: Ty t -> Ty [t]

data Expr :: Type -> Type -> Type {- tu a -} where
    Const :: Ty a -> a -> Expr tu (TU tu a)
    Var2  :: a -> TU tu (Ty a) -> Expr tu (TU tu a)

bug1 :: Expr Typed Bool -> ()
bug1 (Const TyBool False) = ()

bug2a :: Expr Typed Bool -> ()
bug2a (Var2 x (TyBool :: Ty Bool)) = ()

bug2c :: Expr Typed Bool -> ()
bug2c (Var2 x TyBool) = ()

bug2b :: Expr Typed (TU Typed Bool) -> ()
bug2b (Var2 x TyBool) = ()

