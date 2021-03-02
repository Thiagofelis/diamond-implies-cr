Definition rewriting (A : Type) := A -> A -> Prop.
Axiom A : Type.
Axiom r : rewriting A.

Inductive path : A -> A -> Type :=
| refl (a : A) : path a a
| trs  {a b c : A} : path a b -> r b c -> path a c.

Fixpoint size {a b : A} (p : path a b) : nat :=
  match p with
  | refl _ => 0
  | trs p' _ => 1 + (size p')
  end.

    
Theorem diamond_implies_CR :
  forall (diam : forall (x y z : A), r x y -> r x z -> exists w, (r y w) /\ (r z w))
    (a b c : A) (p1 : path a b) (p2 : path a c),
  exists (d : A) (p1' : path b d) (p2' : path c d),
    size p1 = size p2' /\ size p2 = size p1'.
Proof.
  intros. induction p1. (* induction on a --> b *)
  -exists c. exists p2. exists (refl c). split; reflexivity.
  -rename c0 into b'. pose (H := IHp1 p2). destruct H. destruct H. destruct H. destruct H. clear IHp1.
   generalize dependent c.
   assert (exists d (p1' : path b' d) (p2' : r x d), size p1' = size x0). 
   +induction x0.
    ++intros. rename a0 into b. exists b'. exists (refl _). exists r0. reflexivity.
    ++rename b into x'. rename a0 into b. pose (H := IHx0 p1 r0).
      destruct H. destruct H. destruct H. pose (H0:= diam _ _ _ x2 r1).
      destruct H0. destruct H0.
      exists x3. exists (trs x1 H0). exists H1. simpl. rewrite H. reflexivity.
   +intros. destruct H. destruct H. destruct H.
    exists x2. exists x3. exists (trs x1 x4). split.
    ++simpl. rewrite H0. reflexivity.
    ++rewrite H. apply H1.
Qed.

