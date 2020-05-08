Require Import Arith.
Require Import Omega.
Import Nat Peano.


Section ArrayMax.

(* Моделирует массив. array i есть i-й элемент. Подразумевается,
что индексы не превосходят некоторый параметр n
(n есть длина массива + 1) *)

Variable array : nat -> nat.

(* arrayMax n возвращает max(array 0, ..., array n) *)
Fixpoint arrayMax (n : nat) : nat :=
match n with
| 0 => array 0
| S k => max (arrayMax k) (array n)
end.

Compute arrayMax 1.

Theorem arrayMaxSpec1 :
  forall n i, i <= n -> array i <= arrayMax n.
Proof.
induction n as [| n IH].
* intros i H. rewrite le_0_r in H.
  rewrite H. apply le_refl.
* intros i H. simpl.
assert (H1 := max_le_iff). 
specialize (H1 (arrayMax n) (array (S n)) (array i)). 
rewrite H1. clear H1. 
specialize (IH i).
assert (H2 : i <= n \/ i = S n) by omega. clear H. destruct H2. 
- auto.
- right. rewrite H. auto.
Qed.

(* Функция arrayMax берет результат из массива *)

Lemma max_variants : forall m n, max m n = m \/ max m n = n.
Proof.
intros m n. assert (H:=le_ge_cases n m). destruct H.
+ apply Max.max_l in H. left. apply H.
+ apply Max.max_r in H. right. apply H.
Qed.

Theorem arraуMaxSpec2 :
  forall n, exists i, i <= n /\ array i = arrayMax n.
Proof.
induction n as [| n IH].
* exists 0. simpl. split; trivial.
* simpl. assert (H := max_variants). specialize (H (arrayMax n) (array (S n))).
destruct H.
  - destruct IH as [i IH]. destruct IH as [H1 H1'].  exists i. split.
    + omega. 
    + rewrite H1'. rewrite eq_sym_iff. trivial.
  - exists (S n). split.
    + trivial.
    + rewrite eq_sym_iff. trivial.
Qed.

End ArrayMax.

Section darrayMax.

(* Моделирует двумерный массив. darray i j есть элемент, стоящий в i-ой строке и j-ом стоблце.
Подразумевается, что индексы не превосходят некоторый параметр n
n есть длина массива + 1 *)

Variable darray : nat -> nat -> nat.


Fixpoint darrayMax (m n : nat) : nat :=
match m with
| 0 => arrayMax (darray 0) n
| S k => max (darrayMax k n) (arrayMax (darray m) n)
end.


Theorem darrayMaxSpec1 :
  forall m n i j, i <= n /\ j <= m -> darray j i <= darrayMax m n.
Proof.
induction m as [| m IH]; intros n i j H; destruct H as [H1 H2].
* rewrite le_0_r in H2. rewrite H2.
  apply arrayMaxSpec1. apply H1.
* simpl. rewrite max_le_iff.
  assert (H4 : j <= m \/ j = S m) by omega. clear H2. destruct H4.
- auto.
- right. rewrite H. apply arrayMaxSpec1. apply H1.
Qed.


Theorem darraуMaxSpec2 :
  forall m n, exists j i, j <= m /\ i <= n /\ 
              darray j i = darrayMax m n.
Proof.
intros m n. induction m as [| m IH].
* exists 0. 
  assert (H:=arraуMaxSpec2 (darray 0) n).
  destruct H as [i H].  destruct H as [H1 H2].
  exists i. split; trivial. split; trivial.
* destruct (max_variants (darrayMax m n) 
    (arrayMax (darray (S m)) n)) as [H3 | H3].
  - destruct IH as (j & i & IH1 & IH2 & IH3).
    exists j, i; repeat split; auto. simpl. now rewrite H3.
  - clear IH. simpl.
    rewrite H3. assert (H:=arraуMaxSpec2 (darray (S m)) n).
    destruct H as [i H]. exists (S m). exists i. split; auto.
Qed.
End darrayMax.
