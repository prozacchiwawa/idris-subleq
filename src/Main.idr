import SignedNat
import Memory
import Subleq

mem : Memory False 3 (Memory False 2 (Memory False 5 Unit))
mem = MWord False 3 (MWord False 2 (MEnd False 5))

s : SubleqMachine 0 (Memory False 3 (Memory False 2 (Memory False 5 Unit)))
s = (SLQ 0 mem)

main : IO ()
main = do
  let
    s2 = step s
    pc = getPCOf s2

  putStrLn ("Next location " ++ show pc)
