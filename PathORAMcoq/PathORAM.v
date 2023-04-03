Require Import List.
Import ListNotations.
From Coq Require Import Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Even.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat. 
Require Import Coq.Program.Wf.
Require Import Streams.
Require Import Coq.ZArith.Zdiv.


Require Import  ExtLib.Data.Monads.StateMonad ExtLib.Structures.Monads.
Search Monad.
Import MonadLetNotation.
Open Scope monad_scope.

Section Utils.

End Utils.

Section Tree.
(* (***************************************) *)
(* (*************** STASH *****************) *)
(* (***************************************) *)


(* Section STASH. *)
  Definition concatStash {A} (stsh : list (prod nat A)) (a : list (prod nat A)) := stsh ++ a.

  Inductive BlockEntry : Type := BV(f s: nat).

  Definition BlockEntry_fst (be : BlockEntry) : nat :=
    match be with
    | BV f _ => f
    end.
      
  Fixpoint readBlockFromStash (stsh : list BlockEntry) (bID : nat) : option nat :=
    match stsh with
    | [] => None
    | h :: t => match h with
              | BV f s => if Nat.eqb f bID
                        then Some s
                        else readBlockFromStash t bID
              end
                
    end.
  
  
  Fixpoint updateStash(bID: nat) (dataN: nat)(stsh: list BlockEntry): list BlockEntry :=
    match stsh with
    | [] => []
    | (BV id data) :: t => if Nat.eqb bID id
                       then (BV id dataN) :: updateStash bID dataN t
                       else updateStash bID dataN t
    end.
      
  Fixpoint popStash (stsh: list BlockEntry) (sublist: list BlockEntry) : list BlockEntry :=
    match sublist with
    | [] => stsh
    | (BV k v) :: t =>
        match stsh with
        | [] => []
        | (BV bID data) :: xs =>
            if Nat.eqb k bID
            then xs
            else popStash stsh t
        end
    end.

                         
  
(* End STASH. *)



  
  Inductive PBTree (A: Type) : Type :=
  | Leaf (idx: nat) (val: A)
  | Node (idx: nat) (val: A) (l r: PBTree A).

  Arguments Leaf {_} _ _.
  Arguments Node {_} _ _ _ _.

  Fixpoint getHeight {A: Type} (root: PBTree A) : nat :=
    match root with
    | Leaf _ _ => 0
    | Node _ _ l r => S (max (getHeight l) (getHeight r))
    end.


  Fixpoint isPBTree {A} (t : PBTree A) : Prop :=
    match t with
    | Leaf _ _ => True
    | Node _ _ l r => getHeight l = getHeight r
                     /\ (isPBTree l) /\( isPBTree r)
    end.
  
                       
  Fixpoint buildPBTlevelOrder {A} (def_a : A) (label : nat) (ht : nat) : PBTree A :=
    match ht with
    | 0 => Leaf label def_a
    | S ht' => Node label def_a
                      (buildPBTlevelOrder def_a (2 * label + 1) ht')
                      (buildPBTlevelOrder def_a (2 * label + 2) ht')
    end.
  
  Definition PBTree1 {A} : PBTree (list A) := buildPBTlevelOrder [] 0 3.

  Compute PBTree1.
  
  Inductive Dir := L | R.

  Lemma div2 : forall (n : nat), PeanoNat.Nat.div2 n  < S n.
  Proof.
    fix IH 1.
    intro n. case n.
    - constructor.
    - intro n0. case n0.
      + constructor. constructor.
      + intro n1. specialize (IH n1). simpl.
        apply Lt.lt_n_S.
        apply PeanoNat.Nat.lt_lt_succ_r. apply IH.
  Defined.

  Program Fixpoint getPath (lfIdx : nat) {measure lfIdx} : list Dir :=
    match lfIdx with
    | 0 => []
    | S idx => if Nat.even idx
              then [L] ++ getPath (PeanoNat.Nat.div2 idx)
              else [R] ++ getPath (PeanoNat.Nat.div2 idx)
    end.
  Next Obligation.
    apply div2.
    Qed.
  Next Obligation.
  apply div2.
  Defined.

  Compute getPath 9.
  Definition p9 := getPath 9.

  Compute getPath 12.
  Definition p12 := getPath 12.

  Fixpoint buildNodeLevelDict {A} (root: PBTree A) (currL : nat) : list (prod nat nat) :=
    match root with
    | Leaf idx val => [pair idx currL]
    | Node idx val l r =>
        [pair idx currL] ++ buildNodeLevelDict l (S currL)  ++ buildNodeLevelDict r (S currL)
    end.

  Compute buildNodeLevelDict PBTree1 0.

  Fixpoint writeAtPath {A} (root : PBTree A)
           (path : list Dir) (data : A) : PBTree A :=
    match root with
    | Leaf idx val =>
        match path with
        | [] => Leaf idx data
        | _ => Leaf idx val (* path longer than height of tree*)
        end
    | Node idx val l r =>
        match path with
        | [] => Node idx data l r
        | L :: path' => Node idx val (writeAtPath l path' data) r
        | R :: path' => Node idx val l (writeAtPath r path' data)
        end
    end.

  Compute writeAtPath PBTree1 p12 [1;2;3].
  Compute writeAtPath PBTree1 p9 [4;5;6].
  Compute writeAtPath PBTree1 (getPath 4) [5;5;5]. (* 4 and 5 seem to be flipped *)
  
  Definition writeToNode {A} (root : PBTree A) (lfIdx : nat) (tgtl : nat) (data : A) : PBTree A :=
    writeAtPath root (firstn tgtl (getPath lfIdx)) data. 

  Compute PBTree1.
  Compute writeToNode PBTree1 9 2 [0; 1; 2].
  
  (* Definition of rand comes from Yves Bertot *)
  CoFixpoint rand (seed n1 n2 : Z) : Stream Z :=
    let seed' := Zmod seed n2 in Cons seed' (rand (seed' * n1) n1 n2).           
  (* find a definition of one-way function with unique inputs *)
  
  Fixpoint takeS {X} n (str : Stream X) : list X :=
    match n with
    | 0 => []
    | S m => match str with
            | Cons x str' => x :: takeS m str'
            end
    end.

  Compute  takeS 60(rand 475 919 953).
  Definition first60 := takeS 60(rand 475 919 953).

  Definition md_tot := fun x => Zmod x 15.

  Compute List.map Z.to_nat (List.map md_tot first60).
  Definition randSeq := List.map Z.to_nat (List.map md_tot first60).

  Fixpoint modNodesTotal (randList : list Z) : list nat :=
    List.map Z.to_nat(List.map md_tot randList).

  Fixpoint indexed_list {X} (start : nat) (l : list X) : list (nat * X) :=
    match l with
    | [] => []
    | h :: t => (start, h) :: indexed_list (S start) t
    end.

  Compute indexed_list 0 randSeq.
  Definition position_map := indexed_list 0 randSeq.

  Fixpoint posMpLookUp {X} (psmp: list (nat * X)) (id: nat) : option X :=
    match psmp with
    | [] => None
    | (k, v) :: t => if Nat.eqb k id
                   then Some v
                   else posMpLookUp t id
    end.
      
      
  Fixpoint aggregation_helper (key : nat)(val : nat)(l : list (nat * (list nat))):
    list (nat * (list nat)) :=
    match l with
    | [] => [(key, [val])]
    | (n, al) :: t => if Nat.eqb n key
                  then (key, val :: al) :: t 
                  else (n, al) :: aggregation_helper key val t
    end.
           
  Fixpoint aggregation (l : list (nat * nat)): list (nat * (list nat)):=
    match l with
    | [] =>  []
    | (b, n) :: t => aggregation_helper n b (aggregation t)
    end.

  Compute aggregation [(1, 3); (2,3); (8, 3); (4, 4); (5,4)].
  Definition n_bl_pair := aggregation [(1, 3); (2,3); (8, 3); (4, 4); (5,4)].

  Fixpoint makeNZeros (n : nat) : list nat :=
    match n with
    | O => []
    | S n' => O :: makeNZeros n'
    end.

  Compute makeNZeros 10.


  Fixpoint takeL {A} n (l : list A) : list A :=
    match n with
    | O => []
    | S m => match l with
            | [] => []
            | h :: t => h :: takeL m t 
            end
    end.

  Compute takeL 4 [1;2;3].
  
  Fixpoint takeFromIdx {A} (n : nat) (l : list A)  : list A :=
    match l with
    | [] => []
    | h :: t => match n with
              | O => h :: t
              | S m => takeFromIdx m t
              end
    end.

  Compute takeFromIdx 2 [1; 2; 3;4].
  
  
  Fixpoint pairGen {A} (l : list(nat * list nat)) (rt : PBTree A ): list (nat * nat) :=
    match l with
    | [] => []
    | (n, bs) :: t => match rt with
                    | Leaf idx _ => if Nat.eqb n idx
                                   then List.combine bs (makeNZeros (List.length bs))
                                                     (* expand this n's bs *)
                                   else pairGen t rt (* recurse  *)
                    | Node idx _ l r => if Nat.eqb n idx
                                       then List.combine bs (makeNZeros (List.length bs))
                                                         (* expand this n's bs *)
                                       else pairGen t rt  (* recurse  *)
                    end
    end.

  Compute pairGen n_bl_pair (Leaf 3 3).
  Compute takeL 2 (pairGen n_bl_pair (Leaf 3 3)). 

  Check writeAtPath.

  Definition initialT A := (PBTree A, list(nat * nat)).

  Print option.

  (* define type of the initialzation function; needs to talk to Big T*)
  Inductive initialType A : Type :=
  | TreeStash : PBTree A -> list(nat * nat) -> initialType A.
    
  
  Fixpoint initializeTree (rt : PBTree (list (nat * nat))) (stsh : list (nat * nat))
           (l : list(nat * list nat)): option(initialType (list (nat * nat))) :=
    
    match rt with
    | Leaf idx val =>
        let data := pairGen l rt in
        match data with
        | [] => None
        | h :: t => let dataH := takeL 4 data in
                  let dataT := takeFromIdx 4 data in
                  let newStsh := stsh ++ dataT in
                  Some(TreeStash (list(nat * nat))(writeAtPath rt (getPath idx) dataH) newStsh)
        end
    | Node idx val lc rc =>
        let data := pairGen l rt in
        match data with
        | [] => let dataH := takeL 4 data in
               let dataT := takeFromIdx 4 data in
               let newStsh := stsh ++ dataT in
               Some(TreeStash (list (nat * nat))(writeAtPath rt (getPath idx) dataH) newStsh)
        | h :: t => match initializeTree lc stsh l with
                  | Some x => Some x 
                  | None => initializeTree rc stsh l
                  end
        end
    end.

  Program Fixpoint getPath' (lfIdx : nat) {measure lfIdx} : list nat :=
    match lfIdx with
    | 0 => [0]
    | S idx => if Nat.even idx
              then [S idx] ++ getPath' (PeanoNat.Nat.div2 idx)
              else [S idx] ++ getPath' (PeanoNat.Nat.div2 idx)
    end.
  Next Obligation.
    apply div2.
    Qed.
  Next Obligation.
    apply div2.
    Defined.

  Compute rev(getPath' 11).                

  Fixpoint clearPath (rt: PBTree (list (nat * nat ))) (l : list nat): PBTree (list(nat * nat)) := 
    match l with
    | [] => rt
    | h :: t => match rt with
              | Leaf idx val => if Nat.eqb h idx
                             then Leaf idx []
                             else Leaf idx val
                                       
              | Node idx val lc rc => if Nat.eqb h idx
                                     then Node idx [] (clearPath lc t) (clearPath rc t)
                                     else Node idx val (clearPath lc t) (clearPath rc t) 
              end
    end.
  
  Compute writeAtPath PBTree1 (getPath 5) [5;5;5].
  Compute clearPath PBTree1 (rev(getPath' 11)).
  Compute rev(getPath' 11).  

  Inductive  NodeData: Type := Data:(nat * list BlockEntry) -> NodeData .

  Fixpoint getNodeAtLevel (lvl: nat) (l: list nat) (rt: PBTree (list BlockEntry)): option NodeData:=
    match lvl with
    | O => match l with
          | [] => None
          | h :: t => match rt with
                    | Leaf idx val => if Nat.eqb idx h
                                     then Some (Data (idx, val))
                                     else None
                    | Node idx val lc rc => if Nat.eqb idx h
                                           then Some (Data (idx, val))
                                           else
                                             match getNodeAtLevel lvl t lc with
                                             | None => getNodeAtLevel lvl t rc
                                             | Some x => Some x
                                             end
                    end
          end
    | S m => match l with
            | [] => None
            | h :: t => match rt with
                      |Leaf idx val => if Nat.eqb idx h
                                      then Some (Data (idx, val))
                                      else None
                      |Node idx val lc rc => if Nat.eqb idx h
                                            then Some (Data(idx, val))
                                            else
                                              match getNodeAtLevel lvl t lc with
                                              | None => getNodeAtLevel lvl t rc
                                              | Some x => Some x
                                              end
                      end
            end
    end.

  Fixpoint ReadnPopNodes (rt: PBTree (list BlockEntry)) (l: list nat) (stsh: list BlockEntry) : list BlockEntry :=
    match l with
    | [] => []
    | h :: t => match rt with
              | Leaf idx val => if Nat.eqb h idx
                               then stsh ++ val
                               else stsh 
              | Node idx val lc rc => if Nat.eqb h idx
                                     then stsh ++ val 
                                     else stsh 
              end
    end.

  Scheme Equality for list.
  Scheme Equality for prod.

  Print list_beq.
  (* Definition pairEqL A B := TODO *)
  Fixpoint posMapLookUp (bID : nat) (posMap : list(nat * nat)) :option nat :=
    match posMap with
    | [] => None
    | h :: t => if Nat.eqb (fst h) bID
              then Some (snd h)
              else posMapLookUp bID t
    end.
                
  Fixpoint retSomeVal (x : option nat) : nat :=
    match x with
    | None => 0
    | Some n => n
    end.

  Fixpoint eqListPair (l1 : list BlockEntry) (l2 :  list BlockEntry) : bool :=
    match l1 with
    | [] => match l2 with
           | [] => true
           | h :: t => false
           end
    | x :: xs => match x with
               | (BV f s) => 
                   match l2 with
                   | [] => false 
                   | h :: t => match h with
                             | (BV f' s') => if (andb (Nat.eqb f f') (Nat.eqb s s'))
                                       then eqListPair xs t
                                       else false
                             end
                   end
                     
               end
    end.
      
               
      
  Fixpoint NodeDataEq (n1: NodeData) (n2: NodeData) : bool :=
    match n1 with
    | Data (x, y) =>
        match n2 with
        | Data (a, b) => if Nat.eqb x a
                        then eqListPair y b
                        else false
        end
    end.
  


  Fixpoint getCandidateBlocksHelper (rt: PBTree(list BlockEntry)) (l: list nat)
           (lvl: nat)(bID: nat)(stsh: list BlockEntry): option BlockEntry:=
    match getNodeAtLevel lvl l rt with (* P(x, l) *)
    | None => None
    | Some val =>
        match getNodeAtLevel lvl (getPath' (retSomeVal(posMapLookUp bID position_map))) rt with (* P(position[a'],l) *)
        | None => None
        | Some val' => if NodeDataEq val val'
                      then match readBlockFromStash stsh bID with
                           | Some n => Some(BV bID n)
                           | _ => None
                           end
                      else None
        end
    end.
                                 
  Fixpoint getCandidateBlocks (rt: PBTree(list BlockEntry)) (l: list nat) (lvl: nat) (stsh: list BlockEntry) : list BlockEntry :=
    match stsh with
    | [] => []
    | (BV bid bdata) :: t =>
        match getCandidateBlocksHelper rt l lvl bid stsh with
        | None =>  (getCandidateBlocks rt l lvl t)
        | Some v => v :: (getCandidateBlocks rt l lvl t)
        end                     
    end.

End Tree.

Section PathORAM.
  Definition nodesTotal := 60.
  Definition nodeCap := 4.
  (* Definition stashInit := []. *)

  Inductive Op :=
  | Rd
  | Wr.

  Fixpoint leb (n m : nat) : bool :=
  match n with
  | O =>true
  | S n' =>
      match m with
      | O => false
      | S m' =>leb n' m'
      end
  end.

  Definition getWriteBackBlocks (rt : PBTree(list BlockEntry))(c: nat) (l: list nat) (lvl: nat)(stsh: list BlockEntry): list BlockEntry :=
    match List.length(stsh) with
    | O => let candidateBlocks := @nil BlockEntry in
          let writeBackSize := O in
          []
    | S m => let candidateBlocks := getCandidateBlocks rt l lvl stsh in
            if  leb c (List.length(candidateBlocks)) 
            then let writeBackSize := c in
                 takeL c candidateBlocks
            else let writeBackSize := List.length(candidateBlocks) in
                 takeL c candidateBlocks
    end.
  
  Check Monad_state.



  (* Definition incr_counter : state nat unit := *)
  (*   let* curr := get in *)
  (*   put (S curr). *)

  (* Definition stateful_bubble : Z -> state nat Z := *)
  (*   fun x => *)
  (*     let* _ := incr_counter in *)
  (*     ret (2 * x)%Z. *)


 (* st--stash:tree pair *)  

  Definition st_rand := prod (Stream Z)(prod(list BlockEntry)(PBTree(list BlockEntry))).

  Definition writeBacks (leafIdx : nat)(lIDs: list nat) (lvl: nat) : state st_rand unit :=
    let* (stream, (stsh, tr)) := get in
    let writeBackBlocks := getWriteBackBlocks tr leafIdx lIDs lvl stsh in
    let updateStash := popStash stsh writeBackBlocks in
    let newTree := writeToNode tr leafIdx lvl writeBackBlocks in
    put (stream, (updateStash, newTree)).
  Print state.

  Fixpoint access_rec (leafIdx: nat) (lIDs : list nat) (lvl: nat): state st_rand unit :=
    match lvl with
    | O => writeBacks leafIdx lIDs O 
    | S m => let* _ := writeBacks leafIdx lIDs lvl in
            access_rec leafIdx lIDs m 
    end.
Set Printing All.
  Print writeBacks.
  Print access_rec.
  Definition LEVEL := 3.

  Definition option_get {T} (o : option T) (defaultT : T) : T :=
    match o with
    | Some val => val
    | None => defaultT
    end.

  Fixpoint posMapUpdate (posMap: list(nat * nat)) (nID: nat) (random: nat) : list(nat * nat) :=
    match posMap with
    | [] => []
    | (b, n) :: t => if Nat.eqb b nID
                   then (b, random) :: (posMapUpdate t nID random)
                   else (b, n) :: (posMapUpdate t nID random)
    end.
      
  Definition get_random_nat (_ : unit) : state st_rand nat :=
    let* (stream, (stsh, tr)) := get in
    let (random, stream') :=
      match stream with
      | Cons r s => (r, s)
      end
    in
    let* _ := put (stream', (stsh, tr)) in
    ret (Z.to_nat (md_tot random)).
                     
                              
  (* lfIdx is always some val
   move this to its own section*)

    Definition access (op : Op) (bID : nat) (dataN : option nat) : state st_rand nat :=
    let lfIdx_o := posMapLookUp bID position_map in
    let lfidx := option_get lfIdx_o 0 in (* prove lfidx will not be None*)
    let* random_nat := get_random_nat tt in
    let position_map' := posMapUpdate position_map lfidx random_nat  in
    let* (stream, (stsh, tr)) := get in

    let* _ := put(stream, ((ReadnPopNodes tr (getPath' lfidx) stsh), tr)) in
    let dataOld := readBlockFromStash stsh bID in
    match op with
    | Wr => let toPopstsh := updateStash bID (option_get dataN 0) stsh in
           let* _ := put(stream, (toPopstsh, tr)) in
           let* _ := access_rec lfidx (getPath' lfidx) LEVEL in
           ret (option_get dataOld O)
    | Rd => let* _ := access_rec lfidx (getPath' lfidx) LEVEL in
           ret (option_get dataOld O)
    end.
  
End PathORAM.


Section PathORAM.
  Definition ValEq (a : nat) (b : nat): Prop := eq_nat a b.

  Definition twoAccesses(blockId: nat ) (data: nat) : state st_rand nat :=
    let* (stream, (stsh, tr)) := get in
    let* _ := access Wr blockId (Some data) in
    access Rd blockId None.
  Unset Printing All.


  (* From QuickChick Require Import QuickChick. *)
  (* Import QcDefaultNotation. Open Scope qc_scope. *)
  
  Lemma reflect_eq: forall (bID: nat), (bID =? bID) = true.
  Proof.
    intros.
    induction bID.
    - eauto.
    - simpl. apply IHbID.
  Qed.

  Lemma posMapLookUp_some: forall (posMap: list(nat * nat)) (bID: nat) (kv: (nat * nat)),
      eq_nat (fst kv) bID -> In kv posMap ->
      exists v, posMapLookUp bID posMap = Some v.
  Proof.
    intros.
    destruct kv. simpl in *. revert bID n n0 H H0.
    induction posMap; intros.
    - inversion H0.
    - simpl in H0.
      destruct H0 eqn:separate.
      + subst. simpl. destruct (n =? bID) eqn: cond.
        * exists n0. reflexivity. 
        * apply beq_nat_false in cond.  
        eapply eq_nat_is_eq in H.
        rewrite H in cond. contradiction.
      + simpl. destruct (n =? bID) eqn: cond.
        subst; simpl. 
        * apply beq_nat_true in cond. 
          destruct a. simpl. destruct ( Nat.eq_dec n1 bID).
          rewrite e.
          pose proof (reflect_eq bID).
          rewrite H0. exists n2. auto.
          destruct_with_eqn (n1 =? bID). exists n2. auto.
          specialize (IHposMap bID n n0 H i). apply IHposMap.
        * apply beq_nat_false in cond. 
          destruct a. simpl. destruct ( Nat.eq_dec n1 bID).
          rewrite e.
          pose proof (reflect_eq bID).
          rewrite H1. exists n2. auto.
          destruct_with_eqn (n1 =? bID). exists n2. auto.
          specialize (IHposMap bID n n0 H i). apply IHposMap.
  Qed.          
      
  
            
  Lemma readBlockFromStash_some:
    forall (stsh : list BlockEntry) (bID: nat) (kv : BlockEntry), 
      eq_nat (BlockEntry_fst kv) bID -> In kv stsh ->
      exists v, readBlockFromStash stsh bID = Some v.
  Proof.
    intros.
    destruct kv. simpl in *. revert bID f s H H0.
    induction stsh; intros.
    - inversion H0.
    - simpl in H0.
      destruct H0 eqn:separate.
      + subst. simpl. destruct (f =? bID) eqn: cond.
        * exists s. reflexivity. 
        * apply beq_nat_false in cond.  
        eapply eq_nat_is_eq in H.
        rewrite H in cond. contradiction.
      + simpl. destruct a.
        destruct (f0 =? bID) eqn: cond.
        subst; simpl. 
        * apply beq_nat_true in cond.
          exists s0. auto.
        * apply beq_nat_false in cond.
          
          destruct ( Nat.eq_dec f0 bID). contradiction.
          specialize (IHstsh bID f s H i).
          auto.
  Qed.          

  
  Theorem PathORAM_simulates_RAM: forall (s0 : st_rand)(data: nat)(blockId: nat),
      let ReadOut :=
        (let twoAccesses :=
           (let* _ := (access Wr blockId (Some data)) in
            access Rd blockId None) in
         fst (runState twoAccesses s0)
        ) in ValEq data ReadOut. 
  Proof.
    unfold ValEq.
    intros. remember  (access Wr blockId (@Some nat data)) as wrAcc. 
    unfold bind.
    Unset Printing All.
    destruct s0.
    destruct p.
    remember (access Rd blockId None) as rdAcc.
    simpl.
    unfold access in HeqwrAcc.
    
  Admitted.

  (* Branching off: Take Chris suggestion and show that the sequence tokens are unique from each other.  *)
  
  (* Theorem PathORAMIsSecure : *)
  (*   forall (y : list Access) (z : list Access),  *)
  (*    comp_indistinguish (getPos(fold_LM y)) (getPos(fold_LM z)).  *)
  
End PathORAM.
