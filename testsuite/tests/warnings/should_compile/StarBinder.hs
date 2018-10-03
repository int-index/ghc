{-# LANGUAGE TypeOperators, TypeFamilies #-}
{-# OPTIONS -fno-warn-star-is-type #-}

module X (type (X.*)) where

type family (*) a b where { (*) a b = Either b a }
