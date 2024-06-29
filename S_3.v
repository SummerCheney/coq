(* S.3 类的初等代数 *)
Require Export S_2.

(* Require Export Classical.  *)

Module S3.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").


(* 定义2  x∪y= {z:z∈x∪z∈y} *)

Definition Union x y := \{ λ z, z∈x \/ z∈y \}.

Notation "x ∪ y":= (Union x y)(at level 65,right associativity).


(* 定义3  x∩y= {z:z∈x∩z∈y} *)

Definition Intersection x y :=\{λ z, z∈x /\ z∈y \}.

Notation "x ∩ y":= (Intersection x y) (at level 60,right associativity).


(* 定理4  z∈x∪y当且仅当z∈x或者z∈y;z∈x∩y当且仅当z∈x同时z∈y *)

Theorem Theorem4 : forall x y z, z∈x \/ z∈y <-> z ∈ (x ∪ y).
Proof.
  intros; split; intros.
  - apply AxiomII. split. destruct H. 
    unfold Ensemble. exists x. apply H.
    unfold Ensemble. exists y. apply H.
    apply H.
  - apply AxiomII in H. apply H.
Qed.

Theorem Theorem4': forall x y z,
  z∈x /\ z∈y <-> z ∈ (x ∩ y).
Proof.
  intros;split;intros.
  - apply AxiomII. split. destruct H.
    unfold Ensemble. exists x. apply H.
    apply H.
  - apply AxiomII in H. apply H.
Qed.


(* 定理5  x∪x=x 同时 x∩x=x*)

 Theorem Theorem5 : forall x, x ∪ x = x.
Proof.
  intro. apply AxiomI. split; intro.
  - apply Theorem4 in H. tauto.
  -  apply Theorem4. auto.
Qed.


Theorem Theorem5' : forall x,
  x ∩ x = x.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H. apply H.
  - apply Theorem4'. split. apply H. apply H.
Qed.


(* 定理6  x∪y=y∪x 同时 x∩y=y∩x *)

Theorem Theorem6: forall x y,
  x ∪ y = y ∪ x.
Proof.
  intros; apply AxiomI. split; intros.
  - apply Theorem4 in H. apply Theorem4. destruct H.
    + right. apply H.
    + left. apply H.
  - apply Theorem4 in H. apply Theorem4. destruct H.
    + right. apply H.
    + left. apply H.
Qed.

Theorem Theorem6': forall x y,
  x ∩ y = y ∩ x.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H. apply Theorem4'. split. apply H. apply H.
  - apply Theorem4' in H. apply Theorem4'. split. apply H. apply H.
Qed.


(* 定理7  (x∪y)∪z=x∪(y∪z)同时(x∩y)∩z=x∩(y∩z) *)

Theorem Theorem7 : forall x y z,
  (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4. apply Theorem4 in H. destruct H.
    + apply Theorem4 in H. destruct H.
      left. apply H.
      right. apply Theorem4. left. apply H.
    + right. apply Theorem4. right. apply H.
  - apply Theorem4. apply Theorem4 in H. destruct H.
    + left. apply Theorem4. left. apply H.
    + apply Theorem4 in H. destruct H.
      left. apply Theorem4. right. apply H.
      right. apply H.
Qed.

Theorem Theorem7' : forall x y z, 
  (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H. apply Theorem4'. destruct H. split.
      apply Theorem4' in H. destruct H. apply H.
      apply Theorem4' in H. destruct H. apply Theorem4'. split. apply H1.
      apply H0.
  - apply Theorem4' in H. apply Theorem4'. destruct H. split.
      apply Theorem4'. split. apply H. apply Theorem4' in H0. 
      destruct H0. apply H0.
      apply Theorem4' in H0. destruct H0. apply H1.
Qed.


(* 定理8  x∩(y∪z)=(x∩y)∪(x∩z)同时x∪(y∩z)=(x∪y)∩(x∪z) *)

Theorem Theorem8 : forall x y z, 
  x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4. apply Theorem4' in H. destruct H. apply Theorem4 in H0. 
      destruct H0.
    + left. apply Theorem4'. split. apply H. apply H0.
    + right. apply Theorem4'. split. apply H. apply H0.
  - apply Theorem4 in H. apply Theorem4'. destruct H.
    + apply Theorem4' in H. destruct H. split. apply H. apply Theorem4. 
        left. apply H0.
    + apply Theorem4' in H. destruct H. split. apply H. apply Theorem4.
        right. apply H0.
Qed.

Theorem Theorem8' : forall x y z,
  x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4 in H. apply Theorem4'. destruct H.
    + split. apply Theorem4; left; apply H. apply Theorem4. left. apply H.
    + apply Theorem4' in H. destruct H. split. apply Theorem4. right.
      apply H. apply Theorem4. right. apply H0.
  - apply Theorem4' in H. apply Theorem4. destruct H. apply Theorem4 in H,H0.
    destruct H,H0.
    + left. apply H. 
    + left. apply H.
    + left. apply H0. 
    + right. apply Theorem4'. split. apply H. apply H0.
Qed.


(* 定义9  x∉y当且仅当x∈y不真 *)

Definition NotIn x y: Prop := ~x ∈ y.

Notation "x ∉ y" :=(NotIn x y)(at level 10).


(* 定义10  ¬x={y：y∉x} *)

Definition Complement x : Class :=\{λ y, y ∉ x \}.

Notation "¬ x" :=(Complement x)(at level 5,right associativity).


(* 为便于证明定理11及后续定理，自此引入排中律*)

Axiom classic : forall p, p \/ ~ p. 

 
(* 定理11  ¬ (¬ x) = x *)

Theorem Theorem11 : forall x,
  ¬ (¬ x) = x.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H.
    destruct (classic (z ∈ x)).
    + apply H1.
    + unfold NotIn in H0. unfold not in H0. elim H0. apply AxiomII. (* auto. *) 
      split. apply H. apply H1.
  - apply AxiomII. split. 
    + unfold Ensemble. exists x. apply H.
    + unfold NotIn. intro. apply AxiomII in H0. destruct H0. contradiction.
Qed.


Fact not_or_and': forall P Q, ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  intros. split.
  - intro. unfold not in H. apply H. left. apply H0.
  - intro. unfold not in H. apply H. right. auto.
(*   intros; split; intros.
  - unfold not in H. intro. apply H. auto.
  - unfold not in H. intro. apply H. auto.  *)
Qed.


Fact not_and_or': forall P Q, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros. destruct (classic P).
  - right. intro. elim H. tauto.
  - left. auto.
Qed.


(* 逆否命题 （A <-> B）->(~ A) ->(~ B)*)

Proposition L_inverse : forall (A B : Prop),
  (A <-> B) -> (~ A) ->(~B).
Proof.
  unfold not. intros. apply H in H1. apply H0 in H1. apply H1.
Qed.


(* 定理12  De Morgan律   ¬(x∪y)=(¬x)∩(¬y),同时¬(x∩y)=(¬x)∪(¬y) *)

Theorem Theorem12 : forall x y,
  ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H.  destruct H. unfold NotIn in H0.
    apply L_inverse with(B := z ∈ x \/ z ∈ y ) in H0.
    + apply Theorem4'. split. 
      * apply AxiomII. split. apply H. intro. elim H0. left. apply H1. 
        (* apply not_or_and in H0. *) 
        (* Print not_or_and. *)
     (*  Locate not_or_and. *) 
      * apply AxiomII. split. apply H. 
        (* apply not_or_and in H0. *)intro. elim H0. tauto.
    + split; apply Theorem4. (* 注：先split *) 
  - apply AxiomII in H. destruct H. apply AxiomII. split.
    + apply H.    
    + unfold NotIn. destruct H0. apply L_inverse with(A := z ∈ x \/ z ∈ y ).
      * split; apply Theorem4.
      * apply AxiomII in H0,H1. destruct H0, H1. 
        (*  apply and_not_or.  *)
        intro. elim H2. destruct H4. tauto. contradiction.
Qed.

Theorem Theorem12' : forall x y, 
  ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H. unfold NotIn in H0.
    apply L_inverse with(B := z ∈ x /\ z ∈ y ) in H0.
    + apply Theorem4. destruct ( classic (z ∈ x) ).
      * right. apply AxiomII. split. apply H. intro. elim H0. tauto.
      * left. apply AxiomII. split. auto. auto.     
    + split; apply Theorem4'.
  - apply AxiomII in H. destruct H. destruct H0.
     apply AxiomII. split. auto. unfold NotIn. 
     apply L_inverse with(A := z ∈ x /\ z ∈ y ).
    + split; apply Theorem4'.
    + intro. destruct H1. apply AxiomII in H0. destruct H0. contradiction.
    + apply AxiomII. split. apply H. unfold NotIn. intro. 
      apply Theorem4' in H1. destruct H1. apply AxiomII in H0. destruct H0. 
      contradiction.
Qed.


(* 定义13  x~y=x∩(¬ y) *)

Definition Setminus x y : Class := x ∩ (¬ y).

Notation " x ~ y" := (Setminus x y) (at level 50, left associativity).


(* 定理14  x∩(y~z)=(x∩y)~z *)

Theorem Theorem14 : forall x y z,
   x ∩ (y ~ z)= (x ∩ y) ~ z.
Proof.
(*   intros. unfold Setminus. rewrite Theorem7'. auto. *)
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H. destruct H0.
    apply AxiomII. split.
    + apply H.
    + split.
      * apply AxiomII. split. apply H. split. apply H0. apply AxiomII in H1.
         destruct H1. tauto.
      * apply AxiomII in H1. destruct H1. destruct H2. auto.
  - apply AxiomII in H. destruct H. destruct H0. apply AxiomII. split.
    apply Theorem4' in H0. destruct H0. apply H. apply Theorem4' in H0.
    destruct H0. split. auto. apply AxiomII. split. apply H. split;
    auto. 
Qed.


(* 定义(不等于)  x≠y 当且仅当 x=y 不真 *)

Definition  Inequality (x y: Class) : Prop := ~ (x = y).

Notation "x ≠ y" := (Inequality x y) (at level 70).



(* 推论  x≠y当且仅当y≠x *)

Corollary Property_Ineq : forall x y, (x ≠ y) <-> (y ≠ x).
Proof.
  intros; split; intros; unfold Inequality;
  unfold Inequality in H; auto. (*能直接auto*)
(* About not_eq_sym.  *)
(*   intros; split; intros. intro; apply H; auto. intro; apply H.  *)
Qed.


(* 定义15  Φ={x:x≠x} *)

Definition Φ : Class := \{ λ x, x ≠ x \}.


(* 定理16  x∉Φ *)

Theorem Theorem16 : forall x,
  x∉Φ.
Proof.
  intros. unfold NotIn. (*  intros.  *) intro.
  apply AxiomII in H. destruct H. contradiction. 
Qed.

 
(* 定理17  Φ∪x=x同时Φ∩x=Φ *)

Theorem Theorem17 : forall x, 
  Φ ∪ x = x.
Proof. 
  intros; apply AxiomI; split; intros.
  - apply Theorem4 in H. destruct H. apply Theorem16 in H. contradiction.
    auto.
  - apply Theorem4. tauto.
Qed.

Theorem Theorem17' : forall x, 
  Φ ∩ x = Φ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H. destruct H. auto.
  - apply Theorem4'. split.
    + auto.
    + apply Theorem16 in H. contradiction.
Qed.


Lemma LL : forall A: Prop, A -> A /\ A.
Proof.
  intros. split; tauto.
Qed.

Theorem Theorem14' : forall x y z,
    x ∩ z = Φ -> x ∪ (y ~ z)= (x ∪ y) ~ z.
Proof. 
  intros. intros; apply AxiomI; split; intros.
  - apply AxiomII in H0. destruct H0. destruct H1.
    + apply AxiomII. split. auto. split.
      * apply Theorem4. tauto.
      * apply AxiomII. split. auto. intro. 
        assert( z0 ∈ Φ). {rewrite <- H. apply Theorem4'. auto. }
        apply Theorem16 in H3. auto.
    + apply Theorem4'. split.
      * apply Theorem4' in H1. destruct H1. apply Theorem4. tauto.
      * apply Theorem4' in H1. tauto.
  - apply Theorem4' in H0. apply Theorem4.  destruct H0. apply Theorem4 in H0.
    destruct H0. left. auto. right. apply Theorem4'; auto.
Qed.


(* 定义18  μ={x:x=x} *)

Definition μ : Class :=\{λ x, x = x \}.


(* 推论  对任意x,x ∪ (¬ x) = μ.*)

Corollary Property_μ : forall x,
  x ∪ (¬ x) = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H. apply AxiomII. destruct H. destruct H0.
    + auto.
    +(* auto. *) split. auto. auto.
  - apply AxiomII. apply AxiomII in H. split. tauto. 
    generalize( classic ( z ∈ x )); intros; destruct H0.
    + tauto.
    + right. apply AxiomII. destruct H. tauto.
Qed.


(* 定理19  x∈μ当且仅当x是一个集 *) 

Theorem Theorem19 : forall x,
  x ∈ μ <-> Ensemble x.
Proof.
  intros; split; intros.
  - apply AxiomII in H. tauto. 
  - apply AxiomII. auto.
Qed.


(* 定理20  x∪μ=μ同时x∩μ=x *)

Theorem Theorem20 : forall x,
  x ∪ μ = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H. destruct H0.
    + apply Theorem19. auto.
    + auto.
  - apply AxiomII. split.
    + apply Theorem19 in H. auto.
    + tauto.
Qed.

Theorem Theorem20' : forall x,
  x ∩ μ = x.
Proof. 
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H. tauto.
  - apply Theorem4'. split. auto. apply Theorem19. unfold Ensemble. 
    exists x. apply H.
Qed.


(* 定理21  ¬ Φ = μ 同时 ¬ μ = Φ *)

Theorem Theorem21 : ¬ Φ = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem19. unfold Ensemble. exists ¬ Φ. apply H.
  - apply Theorem19 in H. apply AxiomII. split. apply H. apply Theorem16.
Qed.

Theorem Theorem21': ¬ μ = Φ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H. apply Theorem19 in H. contradiction.
  - apply AxiomII in H. destruct H. apply Theorem19 in H. contradiction.
Qed.


(* 定义22  ∩x={z: 对于每个y,如果y∈x,则 z∈y} *)

Definition Element_I x : Class := \{ λ z, forall y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x)(at level 66).



(* 定义23  ∪x={z: 对于某个y,z∈y同时y∈x} *)

Definition Element_U x : Class := \{ λ z, exists y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x)(at level 66).


(* 定理24  ∩Φ=μ同时∪Φ=Φ *)

Theorem Theorem24 :  ∩ Φ = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H. apply Theorem19. apply H.
  - apply AxiomII. split.
    + unfold Ensemble. exists μ. apply H.
    + (*intro.*) intros. apply Theorem16 in H0. contradiction.
Qed.

Theorem Theorem24' : ∪ Φ = Φ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H. destruct H0. destruct H0.
    apply Theorem16 in H1. contradiction.
  - apply Theorem16 in H. contradiction.
Qed.


(* Theorem Theorem24'' : ~ Φ ∈ Φ.
Proof.
   intro. apply AxiomII in H. destruct H. contradiction.
Qed.  *)


(* 定义25  x⊂y当且仅当对于每个z，如果z∈x，则z∈y *)

Definition Included x y : Prop := forall z, z∈x -> z∈y.

Notation "x ⊂ y" := (Included x y) (at level 70).


(* Theorem Theorem24'' : Φ ⊂ Φ.
Proof.
  unfold Included. intros. auto.
Qed. 
  *)

(* Theorem Theorem24''' : μ ⊂ μ.
Proof.
  unfold Included. intros. auto.  
Qed. *) 

(* 定理26  Φ ⊂ x 同时 x ⊂ μ  *)

Theorem Theorem26 : forall x, Φ ⊂ x .
Proof.
  intros. unfold Included. intros. apply Theorem16 in H. contradiction.
Qed.

Theorem Theorem26' : forall x, x ⊂ μ.
Proof.
  intros. unfold Included. intros. apply Theorem19. unfold Ensemble. exists x.
  auto.
Qed.


(* 定理27  x=y 当且仅当 x ⊂ y 同时 y ⊂ x *)
     
Theorem Theorem27 : forall x y, (x = y) <-> (x ⊂ y) /\ (y ⊂ x).
Proof.
  intros; split; intros.
  - split; unfold Included; intros. rewrite <- H. auto. rewrite H. auto. 
  - destruct H. unfold Included in H,H0. apply AxiomI. intros; split; intros. 
    auto. auto.
Qed.


(* 定理28  x ⊂ y 且 y ⊂ z 则 x ⊂ z *)

Theorem Theorem28 : forall x y z, (x ⊂ y) /\ (y ⊂ z) -> (x ⊂ z).
Proof.
  intros. destruct H. unfold Included in *. intros. auto.
Qed.


(* 定理29  x ⊂ y 当且仅当 x ∪ y = y *)

Theorem Theorem29 : forall x y, x ⊂ y <-> (x ∪ y) = y.
Proof.
  intros; split; intros.
  - apply AxiomI. intros; split; intros.
    + apply AxiomII in H0. destruct H0. destruct H1.
      unfold Included in H. auto.
      auto.  
    + apply AxiomII. split. 
      unfold Ensemble. exists y.
      auto. tauto.
  - unfold Included. intros. apply AxiomI with (z:=z) in H. apply H.
    apply Theorem4. tauto.
Qed. 
    

(* 定理30  x ⊂ y 当且仅当 x ∩ y = x *)

Theorem Theorem30 : forall x y, x ⊂ y <-> (x ∩ y) = x.
Proof.
  intros; split; intros.
  - apply AxiomI. intros; split; intros.
    + apply Theorem4' in H0. destruct H0. auto.
    + apply Theorem4'. split. auto. unfold Included in H. auto.
  - unfold Included. intros. apply AxiomI with (z:=z) in H. apply H in H0.
    apply Theorem4' in H0. tauto.
Qed.


(* 定理31  如果 x ⊂ y 则 ∪x ⊂ ∪y 同时 ∩y ⊂ ∩x *)

Theorem Theorem31 : forall x y, (x ⊂ y) -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  intros. split.
  - unfold Included. intros. apply AxiomII. apply AxiomII in H0.
    destruct H0. split.
    + auto.
    + destruct H1. destruct H1. exists x0. split. auto. unfold Included in H.
      apply H in H2. auto.
  - unfold Included. intros. apply AxiomII. apply AxiomII in H0. 
    destruct H0. split.
    + auto.
    + unfold Included in H. auto. (*H 带 y0*)
Qed.


(* 定理32  如果 x ∈ y 则 x ⊂ ∪y 同时 ∩y ⊂ x *)
Theorem Theorem32 : forall x y, (x ∈ y) -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros. split.
  - unfold Included. intros. apply AxiomII. split.
    + unfold Ensemble. exists x. auto.
    + exists x. auto.
  - unfold Included. intros. apply AxiomII in H0. destruct H0. auto.
Qed.


(* 定义真包含 *)

Definition ProperIncluded x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperIncluded x y) (at level 70).

Corollary Property_ProperIncluded : forall x y,
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros. destruct (classic (x=y)).
  - tauto.
  - left. unfold ProperIncluded. tauto.
Qed.


(* 以下4个引理 皆用作证明推论Property_ProperIncluded'*)
Lemma imply_to_and' : forall P Q:Prop, ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros. destruct (classic P).
  - split. auto. intro. elim H. intros. auto.
  - elim H. intros. contradiction. 
Qed.

Lemma NNPP': forall p, ~ ~ p -> p.
Proof.
  intros. destruct (classic p). apply H0. contradiction. (*H和H0矛盾*)
Qed.


Lemma not_all_not_ex' :forall P:Class -> Prop,
 ~ (forall n, ~ P n) ->  exists n, P n.
Proof.
  intros. apply NNPP'. intro. apply H.
  intro. intro. apply H0. exists n. auto.
Qed.
  
Lemma not_all_ex_not' : forall P:Class -> Prop, 
  ~ (forall n, P n) -> exists n, ~ P n.
Proof.
  intros.
  apply not_all_not_ex' with (P:=fun x => ~ P x). intro. apply H.
  intro. apply NNPP'. auto.
Qed.


Corollary Property_ProperIncluded' : forall x y,
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperIncluded in H; destruct H.
  apply L_inverse with (B:= (x ⊂ y /\ y ⊂ x)) in H0.
  apply not_and_or' in H0. destruct H0. contradiction.
  unfold Included in H0. apply not_all_ex_not' in H0. destruct H0.
  apply imply_to_and' in H0. exists x0. auto. apply Theorem27. 
Qed.


Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intro; split; intros.
  - apply Theorem27; split; auto.
    apply Property_ProperIncluded in H. destruct H.
    apply Property_ProperIncluded' in H. destruct H. destruct H.
    assert (x0 ∈ (x ~ y)).
    { unfold Setminus. apply Theorem4'. split. auto. 
       apply AxiomII. split. unfold Ensemble. exists x. auto. 
      auto. }
    rewrite H0 in H2. apply Theorem16 in H2. contradiction.
    apply Theorem27 in H. destruct H. auto.
  - unfold Setminus. apply AxiomI; split;intros.
    + rewrite H0 in H1. apply AxiomII in H1. destruct H1. destruct H2.
     apply AxiomII in H3. destruct H3. contradiction.
    + apply Theorem16 in H1. contradiction.
Qed.

End S3.

Export S3.   
    








