-----------------------------------------------------------------------------
-- $Id: DriverPhases.hs,v 1.5 2001/02/27 12:36:37 rrt Exp $
--
-- GHC Driver
--
-- (c) Simon Marlow 2000
--
-----------------------------------------------------------------------------

module DriverPhases (
   Phase(..),
   startPhase,		-- :: String -> Phase
   phaseInputExt, 	-- :: Phase -> String

   haskellish_file,
   haskellish_suffix,
   cish_file,
   cish_suffix
 ) where

import DriverUtil

-----------------------------------------------------------------------------
-- Phases

{-
   Phase of the           | Suffix saying | Flag saying   | (suffix of)
   compilation system     | ``start here''| ``stop after''| output file
   
   literate pre-processor | .lhs          | -             | -
   C pre-processor (opt.) | -             | -E            | -
   Haskell compiler       | .hs           | -C, -S        | .hc, .s
   C compiler (opt.)      | .hc or .c     | -S            | .s
   assembler              | .s  or .S     | -c            | .o
   linker                 | other         | -             | a.out
-}

data Phase 
	= MkDependHS	-- haskell dependency generation
	| Unlit
	| Cpp
	| Hsc
	| Cc
	| HCc		-- Haskellised C (as opposed to vanilla C) compilation
#ifdef ILX
	| Ilx           -- .NET extended IL
#endif
	| Mangle	-- assembly mangling, now done by a separate script.
	| SplitMangle	-- after mangler if splitting
	| SplitAs
	| As
	| Ln 
  deriving (Eq, Show)

-- the first compilation phase for a given file is determined
-- by its suffix.
startPhase "lhs"   = Unlit
startPhase "hs"    = Cpp
startPhase "hspp"  = Hsc
startPhase "hc"    = HCc
startPhase "c"     = Cc
startPhase "raw_s" = Mangle
startPhase "s"     = As
startPhase "S"     = As
startPhase "o"     = Ln
startPhase _       = Ln	   -- all unknown file types

-- the output suffix for a given phase is uniquely determined by
-- the input requirements of the next phase.
phaseInputExt Unlit       = "lhs"
phaseInputExt Cpp         = "lpp"	-- intermediate only
phaseInputExt Hsc         = "hspp"
phaseInputExt HCc         = "hc"
phaseInputExt Cc          = "c"
#ifdef ILX
phaseInputExt Ilx         = "ilx"
#endif
phaseInputExt Mangle      = "raw_s"
phaseInputExt SplitMangle = "split_s"	-- not really generated
phaseInputExt As          = "s"
phaseInputExt SplitAs     = "split_s"   -- not really generated
phaseInputExt Ln          = "o"
phaseInputExt MkDependHS  = "dep"

haskellish_suffix = (`elem` [ "hs", "hspp", "lhs", "hc" ])
cish_suffix       = (`elem` [ "c", "s", "S" ])  -- maybe .cc et al.??

haskellish_file f = haskellish_suffix suf where (_,suf) = splitFilename f
cish_file f       = cish_suffix suf       where (_,suf) = splitFilename f

