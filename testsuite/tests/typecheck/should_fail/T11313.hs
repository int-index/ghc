{-# LANGUAGE TypeApplications #-}

module T11313 where

import Data.Kind

x = fmap @Type

-- test error message output, which was quite silly before
