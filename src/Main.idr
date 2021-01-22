import SignedNat
import Memory
import Subleq

ret : Nat
ret = 51

a : Nat
a = 52

b : Nat
b = 53

iter : Nat
iter = 54

one : Nat
one = 55

tmp : Nat
tmp = 56

-- https://github.com/tron1point0/subleq/blob/master/fib.asm
mem :
  (ret : Nat) ->
  (a : Nat) ->
  (b : Nat) ->
  (iter : Nat) ->
  (one : Nat) ->
  (tmp : Nat) ->
  (Memory False tmp
  (Memory False tmp -- tmp = 0
  (Memory False 3
  (Memory False a
  (Memory False tmp -- tmp -= a
  (Memory False 6
  (Memory False tmp
  (Memory False ret -- ret -= tmp
  (Memory False 9
  (Memory False tmp -- add b ret
  (Memory False tmp -- tmp = 0
  (Memory False 12
  (Memory False b
  (Memory False tmp -- tmp -= b
  (Memory False 15
  (Memory False tmp
  (Memory False ret -- ret -= tmp
  (Memory False 18
  (Memory False tmp -- b = a
  (Memory False tmp -- tmp = 0
  (Memory False 21
  (Memory False b
  (Memory False b   -- b = 0
  (Memory False 24
  (Memory False a
  (Memory False tmp -- tmp -= a
  (Memory False 27
  (Memory False tmp
  (Memory False b   -- b -= tmp
  (Memory False 30
  (Memory False tmp -- a = ret
  (Memory False tmp -- tmp = 0
  (Memory False 33
  (Memory False a
  (Memory False a -- a = 0
  (Memory False 36
  (Memory False ret
  (Memory False tmp -- tmp -= ret
  (Memory False 39
  (Memory False tmp
  (Memory False a -- a -= tmp
  (Memory False 42
  (Memory False one
  (Memory False iter -- iter -= 1, goto 48 if <= 0
  (Memory False 48
  (Memory False tmp
  (Memory False tmp -- tmp = 0, loop
  (Memory False 0
  (Memory False tmp
  (Memory False tmp
  (Memory False 48
  (Memory False 0 -- ret
  (Memory False 0 -- a
  (Memory False 1 -- b
  (Memory False 5 -- iter
  (Memory False 1 -- one
  (Memory False 0 -- tmp
  Unit
  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))
mem ret a b iter one tmp =
  (MWord False tmp
  (MWord False tmp -- tmp = 0
  (MWord False 3
  (MWord False a
  (MWord False tmp -- tmp -= a
  (MWord False 6
  (MWord False tmp
  (MWord False ret -- ret -= tmp
  (MWord False 9
  (MWord False tmp -- add b ret
  (MWord False tmp -- tmp = 0
  (MWord False 12
  (MWord False b
  (MWord False tmp -- tmp -= b
  (MWord False 15
  (MWord False tmp
  (MWord False ret -- ret -= tmp
  (MWord False 18
  (MWord False tmp -- b = a
  (MWord False tmp -- tmp = 0
  (MWord False 21
  (MWord False b
  (MWord False b   -- b = 0
  (MWord False 24
  (MWord False a
  (MWord False tmp -- tmp -= a
  (MWord False 27
  (MWord False tmp
  (MWord False b   -- b -= tmp
  (MWord False 30
  (MWord False tmp -- a = ret
  (MWord False tmp -- tmp = 0
  (MWord False 33
  (MWord False a
  (MWord False a -- a = 0
  (MWord False 36
  (MWord False ret
  (MWord False tmp -- tmp -= ret
  (MWord False 39
  (MWord False tmp
  (MWord False a -- a -= tmp
  (MWord False 42
  (MWord False one
  (MWord False iter -- iter -= 1, goto 48 if <= 0
  (MWord False 48
  (MWord False tmp
  (MWord False tmp -- tmp = 0, loop
  (MWord False 0
  (MWord False tmp
  (MWord False tmp
  (MWord False 48
  (MWord False 0 -- ret
  (MWord False 0 -- a
  (MWord False 1 -- b
  (MWord False 5 -- iter
  (MWord False 1 -- one
  (MEnd False 0 -- tmp
  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))

s :
  (ret : Nat) ->
  (a : Nat) ->
  (b : Nat) ->
  (iter : Nat) ->
  (one : Nat) ->
  (tmp : Nat) ->
  (SubleqMachine 0
  (Memory False tmp
  (Memory False tmp -- tmp = 0
  (Memory False 3
  (Memory False a
  (Memory False tmp -- tmp -= a
  (Memory False 6
  (Memory False tmp
  (Memory False ret -- ret -= tmp
  (Memory False 9
  (Memory False tmp -- add b ret
  (Memory False tmp -- tmp = 0
  (Memory False 12
  (Memory False b
  (Memory False tmp -- tmp -= b
  (Memory False 15
  (Memory False tmp
  (Memory False ret -- ret -= tmp
  (Memory False 18
  (Memory False tmp -- b = a
  (Memory False tmp -- tmp = 0
  (Memory False 21
  (Memory False b
  (Memory False b   -- b = 0
  (Memory False 24
  (Memory False a
  (Memory False tmp -- tmp -= a
  (Memory False 27
  (Memory False tmp
  (Memory False b   -- b -= tmp
  (Memory False 30
  (Memory False tmp -- a = ret
  (Memory False tmp -- tmp = 0
  (Memory False 33
  (Memory False a
  (Memory False a -- a = 0
  (Memory False 36
  (Memory False ret
  (Memory False tmp -- tmp -= ret
  (Memory False 39
  (Memory False tmp
  (Memory False a -- a -= tmp
  (Memory False 42
  (Memory False one
  (Memory False iter -- iter -= 1, goto 48 if <= 0
  (Memory False 48
  (Memory False tmp
  (Memory False tmp -- tmp = 0, loop
  (Memory False 0
  (Memory False tmp
  (Memory False tmp
  (Memory False 48
  (Memory False 0 -- ret
  (Memory False 0 -- a
  (Memory False 1 -- b
  (Memory False 5 -- iter
  (Memory False 1 -- one
  (Memory False 0 -- tmp
  Unit
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
s ret a b iter one tmp = SLQ 0 (mem ret a b iter one tmp)

main : IO ()
main = do
  let
    s_end = step (s ret a b iter one tmp)
    pc = getPCOf s_end

  putStrLn ("Next location " ++ show pc)
