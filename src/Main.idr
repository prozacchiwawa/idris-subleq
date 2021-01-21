import SignedNat
import Memory
import Subleq

ret : Nat
ret = 48

a : Nat
a = 49

b : Nat
b = 50

iter : Nat
iter = 51

one : Nat
one = 52

tmp : Nat
tmp = 53

return : Nat
return = 45

-- https://github.com/tron1point0/subleq/blob/master/fib.asm
mem :
  (ret : Nat) ->
  (a : Nat) ->
  (b : Nat) ->
  (iter : Nat) ->
  (one : Nat) ->
  (tmp : Nat) ->
  (return : Nat) ->
  (Memory False a
  (Memory False tmp -- tmp -= a
  (Memory False 3
  (Memory False tmp
  (Memory False ret -- ret -= tmp
  (Memory False 6
  (Memory False tmp -- add b ret
  (Memory False tmp -- tmp = 0
  (Memory False 9
  (Memory False b
  (Memory False tmp -- tmp -= b
  (Memory False 12
  (Memory False tmp
  (Memory False ret -- ret -= tmp
  (Memory False 15
  (Memory False one
  (Memory False iter
  (Memory False return
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
  (Memory False tmp
  (Memory False tmp -- tmp = 0, jmp 0
  (Memory False 0
  (Memory False tmp
  (Memory False tmp -- halt
  (Memory False 45
  (Memory False 0 -- ret
  (Memory False 0 -- a
  (Memory False 0 -- b
  (Memory False 5 -- iter
  (Memory False 1 -- one
  (Memory False 0 -- tmp
  Unit
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))
mem ret a b iter one tmp return =
  (MWord False a
  (MWord False tmp -- tmp -= a
  (MWord False 3
  (MWord False tmp
  (MWord False ret -- ret -= tmp
  (MWord False 6
  (MWord False tmp -- add b ret
  (MWord False tmp -- tmp = 0
  (MWord False 9
  (MWord False b
  (MWord False tmp -- tmp -= b
  (MWord False 12
  (MWord False tmp
  (MWord False ret -- ret -= tmp
  (MWord False 15
  (MWord False one
  (MWord False iter
  (MWord False return
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
  (MWord False tmp
  (MWord False tmp -- tmp = 0, jmp 0
  (MWord False 0
  (MWord False tmp
  (MWord False tmp -- halt
  (MWord False 45
  (MWord False 0 -- ret
  (MWord False 0 -- a
  (MWord False 0 -- b
  (MWord False 5 -- iter
  (MWord False 1 -- one
  (MEnd False 0 -- tmp
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))

s :
  (ret : Nat) ->
  (a : Nat) ->
  (b : Nat) ->
  (iter : Nat) ->
  (one : Nat) ->
  (tmp : Nat) ->
  (return : Nat) ->
  (SubleqMachine 0
  (Memory False a
  (Memory False tmp -- tmp -= a
  (Memory False 3
  (Memory False tmp
  (Memory False ret -- ret -= tmp
  (Memory False 6
  (Memory False tmp -- add b ret
  (Memory False tmp -- tmp = 0
  (Memory False 9
  (Memory False b
  (Memory False tmp -- tmp -= b
  (Memory False 12
  (Memory False tmp
  (Memory False ret -- ret -= tmp
  (Memory False 15
  (Memory False one
  (Memory False iter
  (Memory False return
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
  (Memory False tmp
  (Memory False tmp -- tmp = 0, jmp 0
  (Memory False 0
  (Memory False tmp
  (Memory False tmp -- halt
  (Memory False 45
  (Memory False 0 -- ret
  (Memory False 0 -- a
  (Memory False 0 -- b
  (Memory False 5 -- iter
  (Memory False 1 -- one
  (Memory False 0 -- tmp
  Unit
  )))))))))))))))))))))))))))))))))))))))))))))))))))))))
s ret a b iter one tmp return = SLQ 0 (mem ret a b iter one tmp return)

main : IO ()
main = do
  let
    s_end = step (step (s ret a b iter one tmp return))
    pc = getPCOf s_end

  putStrLn ("Next location " ++ show pc)
