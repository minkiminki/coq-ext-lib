Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.

Section MONADZERO.
  Class MonadZero@{i j} (m : Type@{i} -> Type@{j}) : Type :=
    { mzero : forall {T: Type@{i}}, m T }.
End MONADZERO.

Section ZeroFuncs.
  Universe i j.
  Context {m : Type@{i} -> Type@{j}}.
  Context {Monad_m : Monad m}.
  Context {Zero_m : MonadZero m}.

  Definition assert (b : bool) : m unit :=
    if b then ret tt else mzero.

End ZeroFuncs.
