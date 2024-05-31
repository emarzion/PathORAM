Require Import Coq.Logic.Eqdep_dec.

Module Type StateMonad.

  Parameter state : forall (S X : Type), Type.

  Definition State (S X : Type) := S -> state S X.

  Parameter ret : forall {S X : Type}, X -> State S X.

  Parameter bind : forall {S X Y}, State S X -> (X -> State S Y) -> State S Y. 

  Parameter get : forall {S}, State S S.

  Parameter put : forall {S}, S -> State S unit.

End StateMonad.

Module Type RAM (M : StateMonad).
  Parameter K : Type.
  Parameter V : Type.

  (* Wrapped value type, specific to implementation *)
  Parameter Vw : Type -> Type.

  (* Inner implementation of RAM (TODO move or something) *)
  Parameter S : Type.

  (* Read and write operations *)
  Parameter read : K -> M.State S (Vw V).
  Parameter write : K -> V -> M.State S (Vw V).

  (* Escape the monad *)
  Parameter get_payload : M.state S (Vw V) -> option V.

  (* RAM laws (TODO maybe add uniform syntax here, and maybe change if not quite right) *)
  Axiom read_read :
    forall (k : K) (s : S), 
      get_payload ((M.bind (read k) (fun _ => read k)) s) =
      get_payload ((M.bind (read k) (fun v => M.ret v)) s). 

  (* TODO remaining laws
write(key,value) ; read(key)  == write(key,value) ; return(value) -- read-write law
v1 <- read(key1) ; v2 <- read(key2) ; f(v1,v2) == v2 <- read(key2) ; v1 <- read(key1) ; f(v1,v2) -- read-commute law (doesn't require key1 =/= key2)
v <- read(key1); write(key2,value); f(v) == write(key2,value) ; v <- read(key1) ; f(v) -- read-write-commute law (requires key1 =/= key2)
write(key1,value1) ; write(key2,value2) == write(key2,value2) ; write(key1,value1) -- write-commute law (requires key1 =/= key2)
  *)

  (* TODO how does it relate to lens laws? *)
End RAM.