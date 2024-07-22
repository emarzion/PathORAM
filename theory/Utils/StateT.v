Require Import POram.Utils.Classes.
Import MonadNotation.

Definition StateT (S : Type) (M : Type -> Type) (X : Type) : Type :=
  S -> M (X * S)%type.

Definition StateT_ret {S} {M} `{Monad M} {X} :
  X -> StateT S M X :=
  fun x s => mreturn (x, s).

Definition StateT_bind {S} {M} `{Monad M} {X Y} :
  StateT S M X ->
  (X -> StateT S M Y) ->
  StateT S M Y :=
  fun mx f s =>
    mbind (mx s) (fun '(x, s') => f x s').

Global Instance StateT_Monad {M} {S} `{Monad M} : Monad (StateT S M) := {|
  mreturn A := StateT_ret;
  mbind X Y := StateT_bind
  |}.

Definition get {S M} `{Monad M}: StateT S M S :=
  fun s => mreturn(s,s). 

Definition put {S M} `{Monad M} (st : S) :
  StateT S M unit := fun s => mreturn(tt, st).

Definition liftT {S M} `{Monad M} {A} (m : M A) : StateT S M A :=
    fun st =>
    a <- m ;; mreturn (a, st).

Definition state_plift {S} {M} `{Monad M} `{PredLift M} {X} (Pre Post : S -> Prop) (P : X -> Prop) (R : X -> S -> Prop) :
  StateT S M X -> Prop :=
  fun mx =>
    forall s, Pre s -> plift (fun '(x, s') => P x /\ R x s' /\ Post s') (mx s).

Definition triv {X} : X -> Prop :=
  fun _ => True.

Definition triv2 {X Y} : X -> Y -> Prop :=
  fun _ _ => True.

(*
 * state_prob_bind is analogous to the sequencing rule in Hoare Logic
 *)
Lemma state_plift_bind {S X Y} {M} `{Monad M} `{PredLift M} {Pre : S -> Prop}
      (Mid : S -> Prop) {Post : S -> Prop} (P: X -> Prop) {Q: Y -> Prop} {R : X -> S -> Prop} {T : Y -> S -> Prop}
      {mx : StateT S M X} {f : X -> StateT S M Y} : 
  state_plift Pre Mid P R mx ->
  (forall x, P x -> state_plift Mid Post Q T (f x)) ->
  state_plift Pre Post Q T (mbind mx f).
Proof.
  intros.
  unfold state_plift. intros.
  eapply plift_bind; eauto.
  intros.
  destruct x.
  apply H3; tauto.
Qed.

Lemma state_plift_ret {S X} {M} `{Monad M} `{PredLift M} {Pre : S -> Prop} {P : X -> Prop} {x : X}:
  P x -> state_plift Pre Pre P triv2 (mreturn x).
Proof.
  intros.
  unfold state_plift. intros.
  apply plift_ret.
  repeat split; auto.
Qed.

Lemma state_plift_get {S} {M} `{Monad M} `{PredLift M} {Pre : S-> Prop} :
  state_plift Pre Pre Pre triv2 get.
Proof.
  intros s Hs.
  apply plift_ret.
  repeat split; auto.
Qed.

Lemma state_plift_put {S} {M} `{PredLift M} {Pre Pre' : S -> Prop} : forall s,
  Pre' s -> state_plift Pre Pre' triv triv2 (put s).
Proof.
  intros s Hs ? ?.
  apply plift_ret.
  repeat split; auto.
Qed.

Lemma state_plift_liftT {S} {M} `{PredLift M} {Pre : S -> Prop}
  {X} {P : X -> Prop} : forall (m : M X),
  plift P m ->
  state_plift Pre Pre P triv2 (liftT m).
Proof.
  intros m Hm.
  intros s Hs.
  eapply plift_bind; eauto.
  intros x Hx.
  apply plift_ret.
  repeat split; auto.
Qed.

Lemma state_plift_weaken {S} {M} `{PredLift M} {X}
  {Pre : S -> Prop} (Post : S -> Prop) {Post' : S -> Prop}
  (P : X -> Prop) (R : X -> S -> Prop) :
  has_weakening M -> forall m,
  (forall s, Post s -> Post' s) ->
  state_plift Pre Post P R m ->
  state_plift Pre Post' P R m.
Proof.
  intros HM m HPostPost' Hm s Hs.
  eapply HM; [| apply Hm; auto].
  intros [x s'] [Hx [Hs' Hxs']]; auto.
Qed.
