# A Subleq machine in idris: encoding a whole program state in a type

Subleq.SubleqMachine pc mem encodes the full state of the computer in its type, so it should
be possible to ask idris to prove things about the state of the machine after each step, or
after a bunch of steps.

This is the most significant work I've done in idris, and contains some elements that are
likely reusable: the Memory could likely be adapted to store any values with consistent
types ... I might look at making a contrib of just that part in the form of a library into
which an equality can be plugged in.

SignedNat may sound weird but it accomplishes a few things; its type encodes its value along
with the runtime representation and the form of operations such as subtract and greater
are built so that idris can determine the outcomes with ease.  These are built in the form
of interfaces and implementations that force the induction to be visible.  In practice, this
has allowed me to use SignedNat and its various operations without incuring proof obligations
instead, I've got implementation obligations, and as a bonus, the compiler diagnostics are
very clear about those.

Memory is a mess.  I had to basically create it two and 2/3 times or so (once to compute the
type, once to compute the value, and almost a full third time to prove that the resulting
type and runtime value are described in the same way with type variables in the same places.
It does work (no holes in the proofs either) and I believe I've done that soundly.  This
allows the subleq machine to know what the memory state is at the type level so that each
step can predict the next state of the machine at the type level.  The only thing that isn't
in ram in this model is the program counter, whose value depends on the value to store at
each step.

Subleq itself contains a full unrolling of the obligations needed, but at this level, I was
happily spared having to implement most of it more than once since I didn't need to do any
recursion here.  I buried all the recursion in SignedNat and Memory.

## Resources for subleq machines:

- [https://github.com/davidar/subleq](https://github.com/davidar/subleq)

## Stuff on youtube that inspired this:

- [SUBLEQ - A One Instruction Set Computer (OISC)](https://www.youtube.com/watch?v=o0e7_U7ZmBM)
