Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section ReaderType.
  Variable S : Type.
  Universe i j.

  Record reader (t : Type@{i}) : Type@{j} := mkReader
  { runReader : S -> t }.

  Global Instance Monad_reader : Monad reader :=
  { ret  := fun _ v => mkReader (fun _ => v)
  ; bind := fun _ _ c1 c2 =>
    mkReader (fun s =>
      let v := runReader c1 s in
      runReader (c2 v) s)
  }.

  Global Instance MonadReader_reader : MonadReader S reader :=
  { ask := mkReader (fun x => x)
  ; local := fun _ f cmd => mkReader (fun x => runReader cmd (f x))
  }.

  Variable m : Type@{i} -> Type@{j}.

  Record readerT (t : Type@{i}) : Type@{j} := mkReaderT
  { runReaderT : S -> m t }.

  Variable M : Monad@{i j} m.

  Polymorphic Global Instance Monad_readerT : Monad readerT :=
  { ret := fun _ x => mkReaderT (fun s => @ret _ M _ x)
  ; bind := fun _ _ c1 c2 =>
    mkReaderT (fun s =>
      @bind _ M _ _ (runReaderT c1 s) (fun v =>
        runReaderT (c2 v) s))
  }.

  Polymorphic Global Instance MonadReader_readerT : MonadReader S readerT :=
  { ask := mkReaderT (fun x => ret x)
  ; local := fun _ f cmd => mkReaderT (fun x => runReaderT cmd (f x))
  }.

  Polymorphic Global Instance MonadT_readerT : MonadT readerT m :=
  { lift := fun _ c => mkReaderT (fun _ => c)
  }.

  Polymorphic Global Instance MonadZero_readerT (MZ : MonadZero m) : MonadZero readerT :=
  { mzero := fun _ => lift mzero }.

  Polymorphic Global Instance MonadState_readerT T (MS : MonadState T m) : MonadState T readerT :=
  { get := lift get
  ; put := fun x => lift (put x)
  }.

  Polymorphic Global Instance MonadWriter_readerT T (Mon : Monoid T) (MW : MonadWriter Mon m) : MonadWriter Mon readerT :=
  { tell := fun v => lift (tell v)
  ; listen := fun _ c => mkReaderT (fun s => listen (runReaderT c s))
  ; pass := fun _ c => mkReaderT (fun s => pass (runReaderT c s))
  }.

  Polymorphic Global Instance MonadExc_readerT {E} (ME : MonadExc E m) : MonadExc E readerT :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkReaderT (fun s => catch (runReaderT c s) (fun x => runReaderT (h x) s))
  }.

  Polymorphic Global Instance MonadPlus_readerT {MP:MonadPlus m} : MonadPlus readerT :=
  { mplus _A _B mA mB := mkReaderT (fun r => mplus (runReaderT mA r)
                                                   (runReaderT mB r))
  }.


  Polymorphic Global Instance MonadFix_readerT (MF : MonadFix m) : MonadFix readerT :=
  { mfix := fun _ _ r x =>
    mkReaderT (fun s => mfix2 _ (fun f x => runReaderT (r (fun x => mkReaderT (f x)) x)) x s)
  }.

End ReaderType.

Arguments mkReaderT {S} {m} {t} _.
Arguments MonadWriter_readerT {S} {m} {T} {Mon} (_).


Global Instance MonadReader_lift_readerT T S m (R : MonadReader T m) : MonadReader T (readerT S m) :=
{ ask := mkReaderT (fun _ => ask)
; local := fun _ f c =>
  mkReaderT (fun s => local f (runReaderT c s))
}.
