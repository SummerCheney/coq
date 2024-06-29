(* S.4 集的存在性 *)
Require Export S_3.

Module S4.

(*子集公理III  如果x是一个集，存在一个集y 使得对于每个z,假定z⊂x,则z∈y. *)
Axiom AxiomIII : forall x,
  Ensemble x -> exists y, Ensemble y /\ (forall z, z⊂x -> z∈y).


(* 定理33  如果x是一个集 同时z⊂x,则z是一个集*)
Theorem Theorem33 : forall x z,
  Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros. apply AxiomIII in H. (* destruct H. *)destruct H as [y[]]. 
  apply H1 in H0. unfold Ensemble. exists y. auto.
Qed.


(* 定理34  Φ=∩μ 同时 μ=∪μ *)
Theorem Theorem34 : Φ = ∩μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem16 in H. contradiction.
  - apply AxiomII in H. destruct H. apply H0.
    apply Theorem19. generalize (Theorem26 z). intros. 
    apply Theorem33 in H1. auto. auto.
Qed.


Theorem Theorem34' : μ = ∪μ.
Proof.
  intros; apply AxiomI; split; intros. apply Theorem19 in H.
  - apply AxiomII. split. auto. 
    apply AxiomIII in H. destruct H. destruct H. exists x. split.
    apply H0. unfold Included. auto. 
    apply Theorem19. auto.
  - pose proof (Theorem26' (∪ μ) ). apply H0. auto.
 (*  - apply AxiomII in H. destruct H. apply Theorem19. auto. *)
Qed.

(* 定理35  如果x ≠ Φ，那么∩x是集 *)

Lemma Property_NotEmpty : forall x,
  x ≠ Φ <-> exists z, z ∈ x.
Proof.
  intros; assert (x = Φ <-> ~ (exists y, y∈x)).
  { split; intros.
    - intro. destruct H0. rewrite H in H0. apply Theorem16 in H0. apply H0.
    - apply AxiomI; split; intros.
      + elim H. exists z. auto.
      + apply Theorem16 in H0. contradiction. }
  split; intros.
  - apply L_inverse with (B:= ~(exists y, y∈x)) in H0. 
    apply NNPP' in H0. apply H0. apply H.
  - apply L_inverse with (A:=(~ (exists y, y∈x))); auto.
    destruct H; split; auto.
Qed. 


Theorem Theorem35 : forall x,
  x ≠ Φ -> Ensemble (∩x).
Proof.
  intros. apply Property_NotEmpty in H. destruct H. assert (Ensemble x0).
  { unfold Ensemble. exists x. apply H. }
  apply Theorem32 in H.
  destruct H; apply Theorem33 in H1; auto. 
Qed.


(* 定义36  pow(x)={y:y⊂x} *)
Definition PowerSet x : Class :=\{ λ y, y ⊂ x \}.

Notation "pow( x )":=(PowerSet x)( at level 0, right associativity).


(* 定理37  μ=pow(μ)*)
Theorem Theorem37: μ=pow(μ).
Proof.
  apply Theorem27. split.
  - unfold Included. intros. apply AxiomII. split.
    + apply Theorem19. auto.
    + apply Theorem26'.
  - apply Theorem26'.
Qed.

(* 定理38 如果x是一个集,则pow(x)是一个集,同时对每个y, y ⊂ x 当且仅当 y属于pow(x)*)
Theorem Theorem38 : forall x y,
  Ensemble x -> Ensemble pow(x) /\ (y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros. intros; split; intros.
  - apply AxiomIII in H. (* destruct H. destruct H. *) destruct H,H.
    assert( pow(x)⊂ x0).
    { unfold Included. intros. apply AxiomII in H1. destruct H1.
      apply H0 in H2. auto. }
    apply Theorem33 in H1; auto.
  - split; intros.
    + apply AxiomII. split. apply Theorem33 in H0; auto. auto.
    + apply AxiomII in H0. destruct H0. auto.
Qed.


(* 为证明Lemma_N,引入引理LL *)
Lemma LL : forall A: Prop, A -> A /\ A.
Proof.
  intros. split; tauto.
Qed.


(*一个不是集的类*)
Lemma Lemma_N:  ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  generalize (classic (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \})).
  intros; destruct H.
  - apply LL in H. destruct H. apply AxiomII in H. destruct H. contradiction.
  - intro. elim H. apply AxiomII. split; auto. 
Qed.


(* 定理39  μ不是集 *)
Theorem Theorem39 : ~ Ensemble μ.
Proof.
  intro. generalize (Theorem26' \{ λ x, x ∉ x \}). intros. 
  apply Theorem33 in H0. apply Lemma_N in H0. auto. auto.
Qed.


(* Theorem Theorem39'' : ~ μ ∈ μ.
Proof.
  intro. apply AxiomII in H. destruct H. apply Theorem39 in H. auto.
Qed. *)


(* 定义40  {x}={z: 如果x∈μ 则z=x} *)
Definition Singleton x : Class := \{ λ z, x∈μ -> z=x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).


(* 定理41 如果x是一个集，对于每个y,y∈{x} 当且仅当y=x.*)
Theorem Theorem41 : forall x, Ensemble x -> (forall y, y ∈ [x] <-> y=x).
Proof.
  intros. intros; split; intros.
  - apply AxiomII in H0. destruct H0. apply H1. apply Theorem19. auto.
  - apply AxiomII. split. rewrite H0. auto. intro. auto.
Qed.


(* 定理42 如果x是一个集，那么{x}是集 *)
Theorem Theorem42 : forall x, Ensemble x ->  Ensemble [x].
Proof.
  intros. apply LL in H. destruct H. apply Theorem33 with (x:= pow(x)).
  - apply Theorem38 in H. auto. auto. (*class原因? y?*)
  - unfold Included. intros. apply Theorem38 with (y:=z) in H. (* with使用*)
    destruct H. apply H2. apply AxiomII in H1. destruct H1.
    apply Theorem19 in H0. apply H3 in H0. rewrite H0.
    unfold Included. auto.
Qed.


(* 定理43  [x]=μ当且仅当x不是一个集*)
Theorem Theorem43 : forall x, [x] = μ <-> ~ Ensemble x.
Proof.
  intros; split; intros.
  - intro. apply Theorem42 in H0. rewrite H in H0. apply Theorem39 in H0. auto.
  - apply AxiomI. intros; split; intros.
    + apply AxiomII in H0. destruct H0. apply Theorem19. auto.
    + apply AxiomII. split. apply Theorem19 in H0. auto. intro. 
      apply Theorem19 in H1. contradiction.
Qed.


Theorem Theorem42' : forall x, Ensemble [x] -> Ensemble x.
Proof.
  intros. destruct ( classic(Ensemble x )). auto.
  apply Theorem43 in H0. rewrite H0 in H.  apply Theorem39 in H. contradiction.
Qed.


(* 定理44  如果x是一个集，则∩[x]=x同时∪[x]=x；如果x不是一个集，则∩[x]=0同时∪[x]=u *)
Theorem Theorem44 : forall x, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  intros. split.
  - apply AxiomI. intros; split; intros.
    + apply AxiomII in H0. destruct H0. apply H1. 
      apply Theorem41 with (y:=x)in H. apply H. auto.
    + apply AxiomII. split. unfold Ensemble. exists x. auto. 
      intros. apply AxiomII in H1. destruct H1. apply Theorem19 in H. 
      apply H2 in H. rewrite H. auto.
  - apply AxiomI. intros; split; intros.
    + apply AxiomII in H0. destruct H0. destruct H1. destruct H1. 
      apply AxiomII in H2. destruct H2. apply Theorem19 in H. apply H3 in H.
      rewrite H in H1. auto.
    + apply AxiomII. split. unfold Ensemble. exists x. auto.
      exists x. split; auto. apply AxiomII. split; auto.
Qed.

Theorem Theorem44' : forall x, ~ Ensemble x -> ∩[x] = Φ /\ ∪[x] = μ.
Proof.
  intros. apply Theorem43 in H. split.
  - rewrite H. rewrite Theorem34. auto. 
  - rewrite H.  rewrite <- Theorem34'. auto.
Qed.


(*并集公理 如果x是一个集同时y是一个集,则x∪y也是一个集*)
Axiom AxiomIV : forall x y,
    Ensemble x /\ Ensemble y -> Ensemble (x ∪ y).

Corollary AxiomIV' : forall x y,
  Ensemble( x ∪ y) -> Ensemble x /\ Ensemble y.
Proof.
  intros. split.
  - assert (x ⊂ (x∪y)).
    { unfold Included. intros. apply Theorem4. tauto. }
    apply Theorem33 in H0; auto.
  - assert (y ⊂ (x∪y)).
    { unfold Included; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
Qed.


(* 定义45 {xy}={x}∪{y} *)
Definition Unordered x y : Class := [x]∪[y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).


(* 定理46 如果x是一个集同时y是一个集，则{xy}是一个集，同时z∈{xy}当且仅当z=x,或者z=y;{xy}
=μ 当且仅当x不是一个集或者y不是一个集  *)

Theorem Theorem46 : forall x y z,
  Ensemble x /\ Ensemble y -> Ensemble [x|y] /\ (z ∈ [x|y] <-> (z=x \/ z=y)).
Proof.
   split; intros; destruct H.
  - apply Theorem42 in H,H0. apply AxiomIV. auto.
  - split; intros.
    + apply AxiomII in H1; destruct H1, H2; apply AxiomII in H2; destruct H2. 
      * left. apply H3. apply Theorem19 in H. auto.
      * right. apply H3. apply Theorem19 in H0. auto.
    + apply AxiomII; split.
      * destruct H1. rewrite <- H1 in H; auto. rewrite <- H1 in H0; auto.
      * destruct H1.
        -- left. apply AxiomII; split; rewrite  <- H1 in H; auto.
        -- right; apply AxiomII; split; rewrite <- H1 in H0; auto.
Qed.

Theorem Theorem46' : forall x y,
  [x|y] = μ  <-> ~ Ensemble x \/ ~ Ensemble y.
Proof.
  unfold Unordered. split; intros.
  - assert (Ensemble([x]∪[y]) <-> Ensemble [x] /\ Ensemble [y]).
    { split. apply AxiomIV'. apply AxiomIV. } (*try 拓展？*)
    generalize (not_and_or' (Ensemble [x]) (Ensemble [y])); intros.
     apply LL in H0. destruct H0. apply L_inverse in H0.
    apply H1 in H0. destruct H0.
    + left. assert (Ensemble [x] <-> Ensemble x).
      { split. try apply Theorem42'. try apply Theorem42. }
      apply L_inverse in H3; auto.
    + right. assert (Ensemble [y] <-> Ensemble y).
      { split. try apply Theorem42'. try apply Theorem42. }
      apply L_inverse in H3; auto.
    + intro. rewrite H in H3. apply Theorem39 in H3. auto.
  - destruct H. 
    + apply Theorem43 in H; rewrite H;
      generalize (Theorem6 μ [y]); intro; rewrite H0; apply Theorem20.
    + apply Theorem43 in H. rewrite H. apply Theorem20.
Qed.


(* 定理47 如果x与y是两个集，则 ∩{xy}=x∩y 同时 ∪{xy}=x∪y; 如果x或者y不是一个集，
则∩{xy}=Φ同时∪{xy}=μ*)

Theorem Theorem47 : forall x y,
  Ensemble x /\ Ensemble y -> ∩[x|y] = x ∩ y /\ ∪[x|y] = x ∪ y.
Proof.
  split;intros.
  - apply AxiomI; split;intros.
    + apply Theorem4'; split; apply AxiomII in H0; destruct H0.
      * apply H1. apply AxiomII. split. tauto. left. apply AxiomII.
        split. tauto. eauto.
      * apply H1. apply AxiomII. split. tauto. right. apply AxiomII.
        split. tauto. eauto.
    + apply Theorem4' in H0. destruct H0. assert (Ensemble z). 
      { unfold Ensemble. exists x. auto. }  apply AxiomII; split.
      * auto.
      * intros. apply AxiomII in H3. destruct H3. destruct H4.
        -- apply AxiomII in H4; destruct H4. destruct H.
           apply Theorem19 in H; apply H5 in H; rewrite H; auto.
        -- apply AxiomII in H4; destruct H4. destruct H.
           apply Theorem19 in H6; apply H5 in H6; rewrite H6; auto.
  - apply AxiomI; split;intros.
    + apply Theorem4.  apply AxiomII in H0; destruct H0,H1,H1.
      apply AxiomII in H2. destruct H2. destruct H3.
      * left. apply AxiomII in H3. destruct H3. destruct H.
        apply Theorem19 in H; apply H4 in H. rewrite <- H. auto.
      * right. apply AxiomII in H3. destruct H3. destruct H.
        apply Theorem19 in H5. apply H4 in H5. rewrite <- H5. auto.
    + apply Theorem4 in H0. apply AxiomII. split; destruct H0.  
      * unfold Ensemble. exists x. auto.
      * unfold Ensemble. exists y. auto.
      * exists x. split. auto. apply AxiomII. split. tauto. left. 
        apply AxiomII. split. tauto. destruct H. apply Theorem19 in H. auto.
      * exists y. split. auto. apply AxiomII. split. tauto. right. 
        apply AxiomII. split. tauto. destruct H. apply Theorem19 in H. auto.
Qed.

Theorem Theorem47' : forall x y,
  ~ Ensemble x \/ ~ Ensemble y -> ∩[x|y] = Φ /\ ∪[x|y] = μ.
Proof.
  intros; split; apply Theorem46' in H.
  - rewrite H. rewrite Theorem34. auto.
  - rewrite H. rewrite <- Theorem34'. auto.
Qed. 

End S4.

Export S4. 































