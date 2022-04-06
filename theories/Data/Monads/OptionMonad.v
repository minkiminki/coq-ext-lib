Require Import ExtLib.Structures.Monads.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Local Open Scope monad_scope.

Polymorphic Global Instance Monad_option : Monad option :=
{ ret  := @Some
; bind := fun _ _ c1 c2 => match c1 with
                             | None => None
                             | Some v => c2 v
                           end
}.

Polymorphic Global Instance Zero_option : MonadZero option :=
{ mzero := @None }.

Polymorphic Global Instance Plus_option : MonadPlus option :=
{ mplus _A _B aM bM :=
    match aM with
    | None => liftM inr bM
    | Some a => Some (inl a)
    end
}.

Polymorphic Global Instance Exception_option : MonadExc unit option :=
{ raise _ _   := None
; catch _ c h := match c with
                 | None   => h tt
                 | Some x => Some x
                 end
}.

Section Trans.
  Universe i j.
  Variable m : Type@{i} -> Type@{j}.

  Inductive optionT a := mkOptionT { unOptionT : m (option a) }.

  Context {M : Monad@{i j} m}.

  Global Instance Monad_optionT : Monad optionT :=
  { ret _A := fun x => mkOptionT (ret (Some x))
  ; bind _A _B aMM f := mkOptionT
      (aM <- unOptionT aMM ;;
       match aM with
       | None => ret None
       | Some a => unOptionT (f a)
       end)
  }.

  Global Instance Zero_optionT : MonadZero optionT :=
  { mzero _A := mkOptionT (ret None) }.

  Polymorphic Global Instance MonadT_optionT : MonadT optionT m :=
  { lift _A aM := mkOptionT (liftM ret aM) }.

  Polymorphic Global Instance State_optionT {T} (SM : MonadState T m) : MonadState T optionT :=
  { get := lift get
  ; put v := lift (put v)
  }.

  Polymorphic Instance Plus_optionT_right : MonadPlus optionT :=
  { mplus _A _B a b :=
      mkOptionT (bind (unOptionT b) (fun b =>
        match b with
          | None =>
            bind (unOptionT a) (fun a =>
                                  match a with
                                    | None => ret None
                                    | Some a => ret (Some (inl a))
                                  end)
          | Some b => ret (Some (inr b))
        end))
  }.

  Polymorphic Instance Plus_optionT_left : MonadPlus optionT :=
  { mplus _A _B a b :=
      mkOptionT (bind (unOptionT a) (fun a =>
        match a with
          | None =>
            bind (unOptionT b) (fun b =>
                                  match b with
                                    | None => ret None
                                    | Some b => ret (Some (inr b))
                                  end)
          | Some a => ret (Some (inl a))
        end))
  }.

  Polymorphic Global Instance Plus_optionT : MonadPlus optionT := Plus_optionT_left.

  Polymorphic Global Instance Reader_optionT {T} (SM : MonadReader T m) : MonadReader T optionT :=
  { ask := lift ask
  ; local _T v cmd := mkOptionT (local v (unOptionT cmd))
  }.

  Polymorphic Global Instance OptionTErros : MonadExc unit optionT :=
  { raise _u _A := mzero
  ; catch _A aMM f := mkOptionT
      (aM <- unOptionT aMM ;;
       match aM with
       | None => unOptionT (f tt)
       | Some x => ret (Some x)
       end)
  }.

End Trans.

Arguments mkOptionT {m} {a} (_).
Arguments unOptionT {m} {a} (_).
