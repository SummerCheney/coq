(* S.5 序偶：关系 *)
Require Export S_4.

Module S5.

(* 定义48 (x,y)={{x}{xy}} *)
Definition Ordered x y: Class := [[x]|[x|y]].
Notation "[ x , y ]":= (Ordered x y) (at level 0).

(* 定理49 (x,y)是一个集当且仅当x是一个集同时y是一个集；如果(x,y)不是一个集，则(x,y)=μ *)
Theorem Theorem49 : forall x y,
  Ensemble [ x , y ] <-> Ensemble x /\ Ensemble y.
Proof.
  intros; split; intros.
  - unfold Ordered in H. unfold Unordered in H. apply AxiomIV' in H.
    destruct H. split.
    + apply Theorem42' in H; apply Theorem42' in H; auto.
    + apply Theorem42' in H0. apply AxiomIV' in H0. destruct H0.
      apply Theorem42' in H1. auto.
  - destruct H. unfold Ordered. unfold Unordered. 
    apply AxiomIV; split.
    + apply Theorem42. apply Theorem42. auto.
    + apply Theorem42. apply Theorem46; auto.
Qed.

Theorem Theorem49' : forall x y,
  ~ Ensemble [ x , y ] -> [ x , y ] = μ.
Proof.
  intros; generalize Theorem39; intros. (*结论有~ 考虑逆否*)
  apply L_inverse with (B:= Ensemble x /\ Ensemble y) in H.
  apply not_and_or' in H. apply Theorem46' in H. rewrite <- H in H0.
  unfold Ordered. apply Theorem46'. auto. apply Theorem49.
Qed.


(* 定理50 如果x与y均为集，则∪(x,y)={xy},∩(x,y)={x},∪∩(x,y)=x,∩∩(x,y)=x,∪∪(x,y)=x∪y
同时∩∪(x,y)=x∩y *)
Lemma Lemma50 : forall x y,
  Ensemble x /\ Ensemble y -> Ensemble [x] /\ Ensemble [x|y].
Proof.
  intros. split.
  - apply Theorem42. tauto.
  - apply Theorem46 in H. auto. auto.
Qed.
  

Theorem Theorem50 : forall x y,
  Ensemble x /\ Ensemble y -> (∪[ x , y ] = [x|y]) /\ (∩[ x , y ] = [x]) /\
(∪(∩[ x , y ]) = x) /\ (∩(∩[ x , y ]) = x) /\ (∪(∪[ x , y ]) = x ∪ y) /\
(∩(∪[ x , y ]) = x ∩ y).
Proof.
  intros. apply LL in H. destruct H. repeat split; repeat unfold Ordered; 
  apply Lemma50 in H; apply Theorem47 in H; destruct H.
  - rewrite H1. apply AxiomI; split; intros.
    + apply Theorem4 in H2. elim H2; intros. apply Theorem4. tauto. auto.
      (* elim把前提范围放大的感觉*)
    + apply Theorem4. tauto.
  - rewrite H. apply AxiomI; split; intros.
    + apply Theorem4' in H2. tauto.
    + apply Theorem4'. split. auto. apply Theorem4. tauto.
  - rewrite H. apply AxiomI; split; intros.
    + apply AxiomII in H2. destruct H2,H3,H3. apply Theorem4' in H4. 
      destruct H4. apply AxiomII in H4. destruct H4. rewrite <- H6; auto.
      apply Theorem19. tauto.
    + apply AxiomII. split. 
      * unfold Ensemble. exists x. auto.
      * exists x. split. auto. apply Theorem4'. split.
        -- apply AxiomII; split; destruct H0; auto.
        -- apply Theorem4. left. apply AxiomII; split; destruct H0; auto.
  - rewrite H. apply AxiomI; split; intros.
    + apply AxiomII in H2. destruct H2. apply H3. (*实例*)
      apply Theorem4'. split.
      * apply AxiomII. split. tauto. auto.
      * apply Theorem4. left. apply AxiomII. split. tauto. auto.
    + apply AxiomII. split.
      * unfold Ensemble. exists x. auto.
      * intros. apply Theorem4' in H3. destruct H3. apply AxiomII in H3.
        destruct H3. rewrite H5; auto. apply Theorem19. tauto.
  - rewrite H1. apply AxiomI; split; intros.
    + apply AxiomII in H2. destruct H2. destruct H3,H3. apply Theorem4 in H4.
      destruct H4.
      * apply AxiomII in H4. destruct H4. apply AxiomII. split. auto.
        left. rewrite <- H5; auto. apply Theorem19. tauto.
      * apply AxiomII in H4. destruct H4. destruct H5.
        -- apply AxiomII in H5. destruct H5. apply AxiomII. split. auto.
           left. rewrite <- H6; auto. apply Theorem19. tauto.
        -- apply AxiomII in H5. destruct H5. apply AxiomII. split. auto.
           right. rewrite <- H6; auto. apply Theorem19. tauto.
    + apply AxiomII. apply Theorem4 in H2. split.
      * destruct H2. unfold Ensemble. exists x. auto. 
        unfold Ensemble. exists y. auto. 
      * destruct H2.
        -- exists x. split. auto. apply Theorem4. left. apply AxiomII.
           split. tauto. intros. auto.
        -- exists y. split. auto. apply Theorem4. right. apply Theorem4.
            right. apply AxiomII. split. tauto. intros. auto.
  - rewrite H1. apply AxiomI; split; intros.
    + apply AxiomII in H2. destruct H2. apply Theorem4'. split.
      * apply H3. apply Theorem4. left. apply AxiomII. split. tauto. intros.
        auto.
      * apply H3. apply Theorem4. right. apply Theorem4. right. apply AxiomII.
        split. tauto. intros. auto.
    + apply Theorem4' in H2. destruct H2. apply AxiomII. split.
      * unfold Ensemble. exists x. auto.
      * intros. apply Theorem4 in H4. destruct H4.
        -- apply AxiomII in H4. destruct H4. rewrite H5; auto. 
           apply Theorem19. tauto.
        -- apply Theorem4 in H4. destruct H4. apply AxiomII in H4. 
           destruct H4. rewrite H5. auto. apply Theorem19. tauto. 
           apply AxiomII in H4. destruct H4. rewrite H5. auto. 
           apply Theorem19. tauto.
Qed.

Lemma Lemma50' : forall x y,
  ~ Ensemble x \/ ~ Ensemble y -> ~ Ensemble [x] \/ ~ Ensemble [x|y].
Proof.
  intros; elim H; intros. 
  - left. apply Theorem43 in H0. rewrite H0. apply Theorem39.
  - right. apply Theorem46' in H. rewrite H. apply Theorem39.
Qed.

(* 定理50‘ 如果x或者y不是一个集，则∪∩(x,y)= Φ,∩∩(x,y)=μ,∪∪(x,y)=μ,∩∪(x,y)= Φ *)
Theorem Theorem50' : forall x y,
  ~ Ensemble x \/ ~ Ensemble y -> (∪(∩[ x , y ])= Φ) /\ (∩(∩[ x , y])= μ)/\
(∪(∪[ x , y ])= μ) /\ (∩(∪[ x , y])=  Φ).
Proof.
  intros; apply Lemma50' in H; apply Theorem47' in H; destruct H.
  repeat split; unfold Ordered.
  - rewrite H. apply Theorem24'.
  - rewrite H. apply Theorem24.
  - rewrite H0. rewrite <- Theorem34'. auto.
  - rewrite H0. rewrite <- Theorem34. auto.
Qed.


(* 定义51 z的1st坐标=∩∩z *)

Definition First z := ∩∩z.


(* 定义52 z的2nd坐标=(∩∪z)∪(∪∪z)~(∪∩z) *)

Definition Second z := (∩∪z)∪(∪∪z)~(∪∩z).


(* 定理53  μ的2nd坐标=μ *)
Lemma Lemma53 : μ ~ Φ = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H. tauto.
  - apply Theorem4'. split. auto.  apply AxiomII. split; apply Theorem19 in H;
    auto.  apply Theorem16.
Qed.
 
Theorem Theorem53 : Second μ = μ.
Proof.
  intros; unfold Second.
  rewrite <- Theorem34'. rewrite <- Theorem34. rewrite Theorem24'.
  rewrite <- Theorem34'. rewrite  Lemma53. apply Theorem20.
Qed.


(* 定理54 如果x与y均为集,(x,y)的1st坐标=x,同时(x,y)的2nd坐标=y.如果x或y不是集，
则(x,y)的1st坐标=μ同时(x,y)的2nd坐标=μ *)
Lemma Lemma54 : forall x y,
  (x ∪ y) ~ x = y ~ x.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H. apply Theorem4'. destruct H. split.
    + apply Theorem4 in H. apply AxiomII in H0. destruct H0. destruct H.
      contradiction. auto.
    + auto.
  - apply Theorem4'. apply Theorem4' in H. destruct H. split.
    + apply Theorem4. right. auto.
    + auto.
Qed. 

Theorem Theorem54 : forall x y,
  Ensemble x /\ Ensemble y -> First [ x , y ] = x /\ Second [ x , y ] = y.
Proof.
  intros. apply Theorem50 in H. destruct H,H0,H1,H2,H3. split.
  - unfold First. apply H2.
  - unfold Second. rewrite H1. rewrite H3. rewrite H4. rewrite Lemma54.
    unfold Setminus. rewrite Theorem6'. rewrite <- Theorem8. 
    rewrite Property_μ. rewrite Theorem20'. auto.
Qed.

Theorem Theorem54' : forall x y,
  ~ Ensemble x \/ ~ Ensemble y -> First [ x , y ] = μ /\ Second [ x , y ] = μ.
Proof.
  intros. apply Theorem50' in H. destruct H,H0,H1. split.
  - unfold First. apply H0.
  - unfold Second. rewrite H. rewrite H1. rewrite H2. rewrite Lemma53.
    apply Theorem20.
Qed.
 
  
(* 定理55 如果x与y均为集,同时(x,y)=(u,v),则z=x同时y=v *)
Theorem Theorem55 : forall x y u v,
  Ensemble x /\ Ensemble y -> ([ x , y ] = [ u , v ] <-> x = u /\ y = v).
Proof.
  intros; split; intros. apply LL in H. destruct H. apply Theorem49 in H.
  apply Theorem54 in H1.
  - rewrite H0 in H. apply Theorem49 in H. apply Theorem54 in H. 
    rewrite <-H0 in H. destruct H,H1. split.
    + rewrite H1 in H. auto.
    + rewrite H3 in H2. auto.
  - destruct H0. rewrite H0. rewrite H1. auto.
Qed.


(* 定义56 r是一个关系当且仅当对于r的每个元z存在x与y使得z=(x,y) *)
Definition Relation r : Prop :=
  forall z, z∈r -> exists x y, z = [ x , y ].



(* 定义57 r∘s={u:对于某个x，某个y及某个z,u=(x,z),(x,y)∈s同时(y,z)∈r} *)

(* { (x,y) : ... } *)

Parameter Classifier_P : (Class -> Class -> Prop) -> Class.

Notation "\{\ P \}\" := \{ λ z, exists x y, z = [x,y] /\ P x y \}
  (at level 0).


Axiom AxiomII_P : forall (a b: Class) (P: Class -> Class -> Prop),
  [a,b] ∈ \{\ P \}\ <-> Ensemble [a,b] /\ (P a b).

Axiom Property_P : forall (z: Class) (P: Class -> Class -> Prop),
  z ∈ \{\ P \}\ -> (exists a b, z = [a,b]) /\ z ∈ \{\ P \}\.

Axiom Property_P' : forall (z: Class) (P: Class -> Class -> Prop),
  (forall a b, z = [a,b] -> z ∈ \{\ P \}\) -> z ∈ \{\ P \}\. 

Ltac PP H a b := apply Property_P in H; destruct H as [[a [b H]]];
  rewrite H in *.

Ltac PP' H a b:= apply Property_P'; intros a b H; rewrite H in *. 

Definition Composition r s : Class :=
 \{\ λ x z, exists y, [x,y]∈s /\ [y,z]∈r \}\.

Notation "r ∘ s" := (Composition r s) (at level 50, no associativity).

Definition Composition' r s : Class :=
  \{ λ u, exists x y z, u = [x,z] /\ [x,y] ∈ s /\ [y,z] ∈ r \}.


(* 定理58  (r∘s)∘t=r∘(s∘t) *)
Theorem Theorem58: forall r s t,
  (r ∘ s) ∘ t =  r ∘ (s ∘ t).
Proof.
  intros; apply AxiomI; split; intros.
  - (* apply Property_P in H. destruct H as [[a [b]]]. (* 不懂*) 
    rewrite H in *.   *)
    PP H a b. apply AxiomII_P in H0. (* destruct H0 as [y H1]. destruct H1.
    destruct H0. *)  destruct H0,H1 as [y H1],H1. (*拆到了H1.*)
    apply AxiomII_P in H2. destruct H2,H3,H3. apply AxiomII_P. split. auto.
    exists x; split; try tauto; apply AxiomII_P; split;unfold Ensemble; eauto.
    assert (Ensemble [a,y]); unfold Ensemble; eauto.
    assert (Ensemble [y,x]); unfold Ensemble; eauto. apply Theorem49 in H5;
    apply Theorem49 in H6. destruct H5,H6; apply Theorem49; auto.
  - PP H a b. apply AxiomII_P in H0. destruct H0,H1 as [y H1], H1. 
    apply AxiomII_P in H1. destruct H1,H3,H3. apply AxiomII_P. split. auto.
    exists x; split; try tauto; apply AxiomII_P; split;unfold Ensemble; eauto.
    assert (Ensemble [a,x]); unfold Ensemble; eauto.
    assert (Ensemble [y,b]); unfold Ensemble; eauto. apply Theorem49 in H5;
    apply Theorem49 in H6. destruct H5,H6; apply Theorem49; auto.
Qed.


(* 定理59  r∘(s∪t)=r∘s∪r∘t,同时r∘(s∩t)⊂r∩s∘r∩t *)
Theorem Theorem59:   forall r s t,
  Relation r /\ Relation s -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t) /\ 
  r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof. 
  intros; split.
  - intros; apply AxiomI; split; intros.
    + PP H0 a b. apply AxiomII_P in H1. destruct H1. 
      destruct H2 as [y H2]; (*对比上一个“集”的区别 y在这的作用*) destruct H2.
    apply Theorem4. apply Theorem4 in H2; destruct H2. 
      * left; apply AxiomII_P; split; auto. exists y. tauto.
      * right; apply AxiomII_P; split; auto. exists y. tauto.
    + apply Theorem4 in H0; destruct H0; PP H0 a b; apply AxiomII_P;
      apply AxiomII_P in H1.
      * destruct H1. destruct H2 as [y[]]. (*可与源代码对比*)
        split; auto. exists y; split; auto. apply Theorem4. tauto.
      * destruct H1. destruct H2 as [y[]]. (*可与源代码对比*)
        split; auto. exists y; split; auto. apply Theorem4. tauto.
  - unfold Included. intros. PP H0 a b. apply AxiomII_P in H1. destruct H1.
    destruct H2 as [y[]]. apply Theorem4'. split.
    + apply AxiomII_P; split; auto. exists y; split; auto.
      apply Theorem4' in H2. tauto.
    + apply AxiomII_P; split; auto. exists y; split; auto.
      apply Theorem4' in H2. tauto.
Qed.


(* 定义60  r ⁻¹={[x,y]:[y,x]∈r} *)

Definition Inverse r : Class := \{\ λ x y, [y,x]∈r \}\.
Notation "r ⁻¹" := (Inverse r)(at level 5).


(* 定理61  (r ⁻¹)⁻¹=r *)

Lemma Lemma61 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble [y,x].
Proof.
  intros; split; intros.
  - apply Theorem49. apply Theorem49 in H. tauto.
  - apply Theorem49. apply Theorem49 in H. tauto.
Qed.


Theorem Theorem61 : forall r,
  Relation r -> (r ⁻¹)⁻¹ = r. (*数学过程*)
Proof.
  intros; apply AxiomI; split; intros.
  - PP H0 a b. apply AxiomII_P in H1. destruct H1. apply AxiomII_P in H2.
    destruct H2. auto.
  - unfold Relation in H. apply LL in H0; destruct H0. apply H in H1.
    destruct H1 as [a [b H1]]. rewrite H1. apply AxiomII_P. split.
    unfold Ensemble; exists r; rewrite H1 in H0; auto.
    apply AxiomII_P. split. apply Lemma61. unfold Ensemble. exists r.
    rewrite H1 in H0. auto. rewrite <- H1. auto.
Qed.


(* 定理62  (r∘s)⁻¹=(s⁻¹)∘(r⁻¹) *)

Theorem Theorem62 : forall (r s: Class),
  (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros; apply AxiomI; split; intros.
  - PP H a b. apply AxiomII_P in H0. destruct H0. 
    apply AxiomII_P; split; auto. apply AxiomII_P in H1. destruct H1,H2,H2.
    exists x. split. 
    + apply AxiomII_P; split; auto. apply Lemma61. unfold Ensemble. exists r.
      auto.
    + apply AxiomII_P; split; auto. apply Lemma61. unfold Ensemble. exists s.
      auto.
  - PP H a b. apply AxiomII_P in H0. destruct H0,H1,H1.
    apply AxiomII_P; split; auto. apply AxiomII_P in H1,H2.
    apply AxiomII_P. split.
    + apply Lemma61. auto.
    + exists x; split; tauto. 
Qed.


End S5.

Export S5.
























