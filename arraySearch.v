(* 
ПРОЕКТ 2. Выполнили: Осокин Захар,    381602
                   & Ческина Наталья, 381605

Определить, встречается ли число в массиве. 
Нужно дать следующее определение

Fixpoint search (n x : nat) : bool := …

и доказать

Theorem searchSpec :
forall n x, (exists i, i < n /\ array i = x) <-> search n x = true.
*)

Require Import Arith.
Require Import Omega.
Require Import Bool.
Import Nat Peano.

Section search.

(************** Для bdestruct *******************)
Hint Resolve ltb_spec0 leb_spec0 eqb_spec : bdestruct.

Ltac bdestr X H :=
  let e := fresh "e" in
   evar (e : Prop);
   assert (H : reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H | H];
       [ | try first [apply nlt_ge in H | apply nle_gt in H]]].

(* Boolean destruct *)

Tactic Notation "bdestruct" constr(X) := let H := fresh in bdestr X H.

Tactic Notation "bdestruct" constr(X) "as" ident(H) := bdestr X H.
(************** Для bdestruct *******************)

Variable array : nat -> nat.

(* search n x определяет встречается ли число x в массиве
   до элемента с индексом n включительно *)
Fixpoint search (n x : nat) : bool :=
match n with
| 0 => false
| S k => if array k =? x then true else search k x
end.

Theorem searchSpec :
forall n x, (exists i, i < n /\ array i = x) <-> search n x = true.
Proof.
split; intro H. 
+ destruct H as [i H]. destruct H as [H1 H2].
  induction n as [| n IH].
  * omega.
  * simpl. bdestruct (array n =? x).
    - auto.
    - assert (H3 := lt_succ_r). specialize (H3 i n). 
      apply H3 in H1. apply le_lt_or_eq in H1.
      destruct H1 as [H4 | H5].
        apply IH in H4. apply H4.
        subst i. omega.
+ induction n as [| n IH].
  * simpl in H. discriminate H.
  * simpl in H. bdestruct (array n =? x).
    - exists n. split. auto. apply H0.
    - apply IH in H. 
      destruct H as [y H]. destruct H as [H1 H2].
      exists y. split.
      apply lt_lt_succ_r in H1. apply H1.
      apply H2.
Qed.
End search.
