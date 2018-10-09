a :: Double; a = 1 / 2 / 2
a_scc_ann  = 1 / {-# SCC "ann" #-} 2 / 2
a_hpc_ann  = 1 / {-# GENERATED "ann" 1:1-1:1 #-} 2 / 2
a_core_ann = 1 / {-# CORE "ann" #-} 2 / 2

a_scc_hpc_ann =
  1 / {-# SCC "ann" #-}
      {-# GENERATED "ann" 1:1-1:1 #-}
      2 / 2
a_scc_core_ann =
  1 / {-# SCC "ann" #-}
      {-# CORE "ann" #-}
      2 / 2
a_scc_hpc_core_ann =
  1 / {-# SCC "ann" #-}
      {-# GENERATED "ann" 1:1-1:1 #-}
      {-# CORE "ann" #-}
      2 / 2

-- Annotations must have no effect on the values.
prop = a == a_scc_ann &&
       a == a_hpc_ann &&
       a == a_core_ann &&
       a == a_scc_hpc_ann &&
       a == a_scc_core_ann &&
       a == a_scc_hpc_core_ann

-- so 'prop' must be True.
main = do
  putStrLn $
    if prop then "OK"
            else "SCC/GENERATED/CORE annotation changes \
                 \the meaning of an expression :-("
  print a
