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
(* assert (H1 := nlt_0_r). *)
induction n as [| n IH]. 
+ simpl search. intros. split.
++ intro. destruct H as [i H]. omega.
(* CHECKPOINT *)
++ intro. discriminate H.
+ simpl search. intros. split.
++ intro. destruct H as [i H]. bdestruct (array n =? x) as H2.
+++ trivial.
+++ apply IH. exists i. destruct H as [H H3]. split.
* apply lt_n_Sm_le in H. assert (H1 : i = n) by omega. apply le_lt_or_eq in H.

Admitted.
Qed.
End search.