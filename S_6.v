(* S.6 函数 *)
Require Export S_5.

Module S6.

(* 定义63 f是一个函数当且仅当f是一个关系且对每一个x,y,z如果(x,y)∈f且
(x,z)∈f,则y=z *)
Definition Function f : Prop :=
  Relation f /\ ( forall x y z, [x,y] ∈ f /\ [x,z]∈ f -> y = z).
(* 先定义f是一个关系 关系是序偶对组成的集合，方便用序偶来表示映射 ；
后面强调函数的单值性 ，允许多对一，但不允许一对多*)


(* 定理64 如果f是一个函数同时g也是一个函数，则f和g的合成也是一个函数 *)
Theorem Theorem64: forall f g,
  Function f /\ Function g -> Function ( f ∘ g ).
Proof.
  intros. destruct H.
  unfold Function in *. destruct H,H0. split.
  - unfold Relation. intros. 
    apply Property_P in H3 as [[a[b]]]. eauto. (*1*)
  - intros. destruct H3. 
    apply AxiomII_P in H3 as [H3[x0[]]].
    apply AxiomII_P in H4 as [H4[x1[]]].   
    assert (x0 = x1). { apply H2 with x. auto. } 
    apply H1 with x0. rewrite <- H9 in H8. auto.
Qed.


(* 定义65 f的定义域={x:存在y,(x,y)∈f} *)
Definition Domain f : Class :=\{ λ x, exists y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).
(* f的定义域：f的序偶的第一坐标组成的类 *)

(* 定义域性质*)
Corollary Property_dom: forall x y f,
  [x,y] ∈ f -> x ∈ dom( f ).
Proof.
  intros. apply AxiomII; split; eauto.
  assert (Ensemble [x,y]). { unfold Ensemble. eauto. }
  apply Theorem49 in H0; tauto.
Qed.


(* 定义66 f的值域={y:存在x,(x,y)∈f} *)
Definition Range f : Class :=\{ λ y, exists x, [x,y] ∈ f \}.

Notation "ran( f )":= (Range f)(at level 5).
(* f的值域：f的序偶的第二坐标组成的类 *)

(* 值域的性质 *)
Corollary Property_ran : forall x y f,
  [x,y] ∈ f -> y ∈ ran( f ).
Proof.
  intros. apply AxiomII; split; eauto.
  assert (Ensemble [x,y]). {unfold Ensemble. eauto. }
  apply Theorem49 in H0; tauto.
Qed.


(* 定理67 μ的定义域=μ同时μ的值域=μ *)
Theorem Theorem67: dom( μ ) = μ /\ ran( μ ) = μ.
Proof.
  split.
  - apply AxiomI; split; intros.
    + apply AxiomII in H as []. apply Theorem19 in H; auto.
    + apply Theorem19 in H. apply AxiomII; split; auto.
      assert (Ensemble z).
      { auto. }
      exists z. apply Theorem19. apply Theorem49; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H as []. apply Theorem19 in H; auto.
    + apply Theorem19 in H. apply AxiomII; split; auto.
      assert (Ensemble Φ). 
      { pose proof (Theorem26 z). apply Theorem33 in H0; auto. }
      exists Φ. apply Theorem19. apply Theorem49; auto.
Qed.


(*
(* ∩改为∪ *)
(* 定义68  f(x)=∪{y:[x,y]∈f} *)
Definition Value f x : Class := ∪ \{ λ y, [x,y] ∈ f \}.

Notation "f [ x ]" := (Value f x)(at level 5).
(* f(x)就是 所有以x为第一坐标的序偶的第二坐标的类的∪ *)

Lemma test : forall x f,
  x ∈ μ -> x ∉ (dom( f )) -> f [x] = Φ.
Proof.
  intros. destruct (classic (f [x] = Φ)).
  - auto.
  - assert (\{ λ y, [x,y] ∈ f \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H2 as [].
      apply Property_dom in H3. contradiction.
      apply Theorem16 in H2. destruct H2. }
    unfold Value. rewrite H2. apply Theorem24'.
Qed.


Corollary Property_Value : forall f x,
  Function f -> x ∈ dom( f ) -> [x,f[x]] ∈ f. 
Proof.
  intros. unfold Function in H. destruct H.
  apply AxiomII in H0 as [H0[]]. 
  assert (x0 = f[x]). 
  { apply AxiomI; split; intros.
    - apply AxiomII; split.
      unfold Ensemble; eauto.
      exists x0. split; auto. apply AxiomII. split; auto.
      assert (Ensemble ([x, x0])).
      { unfold Ensemble. eauto. }
      apply Theorem49 in H4. tauto.
    - apply AxiomII in H3 as [H3[y[]]].
      apply AxiomII in H5 as [].
      assert (x0 = y).
      { apply H1 with x. auto. }
      rewrite H7; auto. }
  rewrite <- H3; auto.
Qed. 


Lemma test1 : forall x f g,
  Function f -> Function g -> x ∈ μ -> x ∉ (dom( f )) -> 
  g = (f ∪ [[x,Φ]]) -> ( forall y, f [y] = g [y] ).
Proof.
  intros. destruct (classic (y ∈ dom(f))). rewrite H3.
  apply AxiomI; split; intros.
  - apply AxiomII; split. 
    unfold Ensemble; eauto.
    exists f [y]. split; auto.
    apply AxiomII; split. apply AxiomII in H5 as [H5[x0[]]].
    apply AxiomII in H7 as [].
    pose proof (Property_Value f y H H4).
    unfold Function in H. destruct H.
    assert (x0 = f [y]).
    { apply H10 with y. tauto. }
    rewrite <- H11; auto.
    apply Theorem4. left.
    pose proof (Property_Value f y H H4); auto.
  - apply AxiomII in H5 as [H5[x0[]]].
    apply AxiomII in H7 as [].
    apply Theorem4 in H8. destruct H8.
    + apply AxiomII; split.
      unfold Ensemble; eauto.
      exists x0; split; auto. apply AxiomII; tauto.
    + apply AxiomII; split. unfold Ensemble. eauto.
      exists x0. split; auto.
      apply AxiomII; split; auto.            
      assert (Ensemble Φ).
      { pose proof (Theorem26 x0). apply Theorem33 in H9; auto. }
      assert (Ensemble ([x,Φ])).
      { apply Theorem49. split. apply Theorem19. apply H1. auto. }
      apply Theorem41 in H8; auto.
      assert (Ensemble y). 
      { unfold Ensemble. eauto. }
      apply Theorem55 in H8 as []; auto. 
      rewrite H8 in H4. contradiction.
  - apply AxiomI; split; intros.
    + rewrite H3. apply AxiomII; split.
      unfold Ensemble. eauto.
      exists f [y]. split; auto.
      apply AxiomII; split.
      apply AxiomII in H5 as [H5[y0[]]].
      apply AxiomII in H7 as [].
      assert (Ensemble ([y,y0])).
      { unfold Ensemble. eauto. }
      apply Theorem49 in H9 as []. apply Theorem19 in H9.
      apply test in H4; auto. rewrite H4.
      pose proof (Theorem26 z). apply Theorem33 in H11; auto.
      apply Theorem4. right. apply Theorem19 in H1.
      assert (Ensemble Φ).
      { pose proof (Theorem26 x). apply Theorem33 in H6; auto. }
      assert (Ensemble ([x,Φ])).
      { apply Theorem49. auto. }
      apply Theorem41; auto. apply Theorem55.
      apply AxiomII in H5 as [H5[y0[]]].
      apply AxiomII in H9 as []. 
      assert (Ensemble ([y,y0])).
      { unfold Ensemble; eauto. }
      apply Theorem49 in H11 as [].
      split; auto. apply Theorem19 in H11.
      pose proof (test y f H11 H4). rewrite H13; auto.
      split. apply AxiomII in H5 as [H5[x0[]]].
      apply AxiomII in H9 as []. elim H4.
      apply Property_dom in H10; auto.
      apply AxiomII in H5 as [H5[y0[]]].
      apply AxiomII in H9 as []. 
      assert (Ensemble ([y,y0])).
      { unfold Ensemble; eauto. }
      apply Theorem49 in H11 as []. apply Theorem19 in H11.
      pose proof (test y f H11 H4). auto.
    + rewrite H3 in H5. apply AxiomII in H5 as [H5[y0[]]].
      apply AxiomII in H7 as [].
      apply Theorem4 in H8. destruct H8.
      apply AxiomII; split.
      unfold Ensemble; eauto.
      exists y0; split; auto. apply AxiomII; split; auto.
      assert (Ensemble Φ).
      { pose proof (Theorem26 x). apply Theorem19 in H1.
        apply Theorem33 in H9; auto. }
      assert (Ensemble ([x,Φ])).
      { apply Theorem49. apply Theorem19 in H1. auto. }
      apply Theorem41 in H8; auto. apply Theorem55 in H8 as [].
      rewrite H8. pose proof (test x f H1 H2). rewrite H12.
      rewrite H11 in H6. auto.
      split; auto. rewrite <- H8 in H10. apply Theorem49 in H10.
      tauto.
Qed.
*)


(* 定义68  f(x)=∩{y:[x,y]∈f} *)
Definition Value f x : Class := ∩ \{ λ y, [x,y] ∈ f \}.

Notation "f [ x ]" := (Value f x)(at level 5).

(* 值的性质一 *)
Corollary Property_Value : forall f x,
  Function f -> x ∈ dom( f ) -> [x,f[x]] ∈ f. 
Proof.
  intros. unfold Function in H. destruct H.
  apply AxiomII in H0 as [H0[]]. 
  assert (x0 = f[x]). 
  { apply AxiomI; split; intros.
    - apply AxiomII; split.
      unfold Ensemble; eauto.
      intros. apply AxiomII in H4 as [_ H4].
      assert (x0 = y).
      { apply H1 with x; auto. }
      rewrite <- H5; auto.
    - apply AxiomII in H3 as [].
      apply H4. apply AxiomII. split; auto.
      assert (Ensemble ([x,x0])).
      { unfold Ensemble; eauto. }
      apply Theorem49 in H5; tauto. }
  rewrite <- H3; auto.
Qed.


(* 定理69 如果x不属于f的定义域，则f(x)=μ；如果x∈f的定义域，则f(x)∈μ.*)
Theorem Theorem69: forall x f,
  ( x ∉ (dom( f )) -> f[x] = μ ) /\ ( x ∈ dom( f ) -> (f[x]) ∈  μ ).
Proof.
  split. intros. Check Theorem35.
  - assert (\{ λ y, [x,y] ∈ f \} = Φ).
    { apply AxiomI; split; intros. 
      apply AxiomII in H0 as [].
      elim H. apply Property_dom in H1. auto. 
      apply Theorem16 in H0. destruct H0. }
    unfold Value. rewrite H0. apply Theorem24.
  - intros. apply AxiomII in H as [H0[]]. (*3*) unfold Value.
    assert (~(\{ λ y, [x,y] ∈ f \} = Φ)).
    { intro. assert (x0 ∈ (\{ λ y, [x, y] ∈ f \})).
      { apply AxiomII; split; auto.
        assert (Ensemble ([x,x0])).
        { unfold Ensemble; eauto. }
       apply Theorem49 in H2. tauto. }
    rewrite H1 in H2. apply Theorem16 in H2. auto. }
    apply Theorem35 in H1. apply Theorem19. auto.
Qed.


(* 值的性质 二 *)
Corollary Property_Value' : forall f x,
  Function f -> f[x] ∈ ran(f) -> [x,f[x]] ∈ f.
Proof.
  intros. apply Property_Value; auto.
  apply AxiomII in H0 as [H0[]].
  apply Theorem19 in H0. (* 4排中律思路 *) 
  destruct (classic ((x ∈ dom( f)))); auto.
  apply Theorem69 in H2.
  assert (Ensemble f [x]).
  { unfold Ensemble. eauto. }
  rewrite H2 in H3. apply Theorem39 in H3. destruct H3.
Qed.


(* 定理70 如果f是一个函数，则f={[x,y]:y=f[x]} *)
(* 如果f是函数，那么f是有所有x和x有值的y的序偶组成的 *)
Theorem Theorem70 : forall f,
  Function f -> f = \{\ λ x y, y = f[x] \}\. 
Proof.
  intros. apply AxiomI; split; intros.
  - PP' H1 a b. apply AxiomII_P; split. 
    unfold Ensemble; eauto.
    pose proof H. unfold Function in H. destruct H.
    apply H3 with a; split; eauto.
    apply Property_Value; auto.
    apply AxiomII; split.
    assert (Ensemble ([a,b])).
    {unfold Ensemble; eauto. }
    apply Theorem49 in H4; tauto.
    eauto. (* 完成 y= f(x)部分 *)
  - PP H0 a b. apply AxiomII_P in H1 as []. (* 5反证法思路 *)
    rewrite H2. apply Property_Value; auto.
    apply NNPP'. intro. apply Theorem69 in H3.
    rewrite H3 in H2. rewrite H2 in H1.
    apply Theorem49 in H1 as []. apply Theorem39 in H4.
    auto.
Qed. 


(* 定理71 如果f与g都是函数，则f=g的充要条件是对于每个x,f(x)=g(x). *)
Theorem Theorem71: forall f g,
  Function f /\ Function g -> ( f = g <-> forall x, f[x] = g[x]). 
Proof.
  intros. destruct H. split; intros.
  - rewrite H1. auto.
  - apply Theorem70 in H,H0. apply AxiomI; split; intros.
    + rewrite H in H2. PP H2 a b.
      rewrite H0. apply AxiomII_P. apply AxiomII_P in H3 as [].
      split; auto. rewrite H1 in H4. auto.
    + rewrite H0 in H2. PP H2 a b.
      rewrite H. apply AxiomII_P. apply AxiomII_P in H3 as [].
      split; auto. rewrite <- H1 in H4. auto.
Qed.


(*
Lemma xx : forall x, Ensemble (∪x) -> Ensemble x.
Proof.
  intros. pose proof H. apply Theorem38 in H0; auto.
  assert (x ⊂ pow( ∪ x)).
  { unfold Included. intros. apply AxiomII; split.
    exists x; auto.
    unfold Included. intros. apply AxiomII; split.
    exists z; auto. exists z; auto. }
  apply Theorem33 in H1; auto.
Qed.
*)


(*
Axiom AxiomVVI :  forall f,
  Function f -> Ensemble dom( f ) -> Ensemble (∪(ran( f ))).

(* 代换公理 如果f是一个函数同时f的定义域是一个集，则f的值域是一个集 *)
Theorem AxiomV : forall f,
  Function f -> Ensemble dom( f ) -> Ensemble ran( f ).
Proof.
  intros.
  assert (Function (\{\ λ x z, x ∈ dom(f) /\ z = [f[x]] \}\)).
  { unfold Function. split. unfold Relation. 
    intros. PP H1 a b. 
    exists a, b. auto.
    intros. destruct H1. 
    apply AxiomII_P in H1 as [H1[]].
    apply AxiomII_P in H2 as [H2[]].
    rewrite H4,H6. auto. } (*证明新序偶对的类 是函数*)
  assert (dom(f) = dom(\{\ λ x z, x ∈ dom(f) /\ z = [f[x]] \}\)).
  { apply AxiomI; split; intros. assert (Ensemble z).
    { exists dom(f); auto. }
    apply AxiomII; split; auto. exists ([f[z]]).
    pose proof H2. apply Property_Value,Property_ran in H4; auto.
    assert (Ensemble f[z] /\ Ensemble ([f[z]])) as [].
    { split; [ |apply Theorem42]; exists ran(f); auto. }
    apply AxiomII_P; split; auto. apply Theorem49; auto.
    apply AxiomII in H2 as [_[]]. apply AxiomII_P in H2; tauto. }
  rewrite H2 in H0. (*证明新函数的定义域和函数f的定义域相同*)
  apply AxiomVVI in H1; auto. (*达成使用公理VVI的条件，后续完成类的元的交是集到类是集的转换*)
  assert ((∪ ran( \{\ λ x z,x ∈ dom( f) /\ z = [f [x]] \}\)) = ran( f)).
  { apply AxiomI; split; intros.
    apply AxiomII in H3 as [H3[y[]]].
    apply AxiomII in H5 as [H5[]]. 
    apply AxiomII_P in H6 as [H6[]].
    rewrite H8 in H5. apply Theorem42' in H5.
    rewrite H8 in H4. apply Theorem41 in H4; auto. (*1*)
    apply Property_Value in H7; auto.
    rewrite <- H4 in H7.
    apply Property_ran in H7; auto.
    apply AxiomII. split.
    unfold Ensemble; eauto. apply AxiomII in H3 as [H3[]].
    pose proof H4. 
    apply Property_dom,Property_Value in H5; auto.
    pose proof H5.
    apply Property_ran in H6; auto.
    exists [f[x]]. split. 
    apply Theorem41. exists ran(f); auto.
    destruct H. apply (H7 x); auto.
    assert (Ensemble ([f[x]])).
    { apply Theorem42; auto. exists ran(f); auto. }
    apply AxiomII; split; auto. exists x. 
    apply Property_dom in H4. apply AxiomII_P; repeat split; auto.
    apply Theorem49; split; auto. exists dom(f); auto. }
  rewrite <- H3; auto.
Qed.

    
Theorem AxiomVI : forall x,
  Ensemble x -> Ensemble (∪x).
Proof.
  intros. assert (Function (\{\ λ u v, u ∈ x /\ v = u \}\)).
  { unfold Function. repeat split.
    unfold Relation. intros.
    PP H0 a b. exists a, b. auto.
    intros. destruct H0. apply AxiomII_P in H0 as [H0[]].
    apply AxiomII_P in H1 as [H1[]].
    rewrite H3,H5. auto. } (*证明新序偶对的类 是函数*)
  assert (dom( \{\ λ u v, u ∈ x /\ v = u \}\) = x).
    { apply AxiomI; split; intros.
      apply AxiomII in H1 as [H1[]].
      apply AxiomII_P in H2. tauto.
      apply AxiomII; split. exists x; auto.
      exists z. apply AxiomII_P; repeat split; auto.
      apply Theorem49; split; auto; exists x; auto. }
  rewrite <- H1 in H. (*证明新函数的定义域等于x*)
  apply AxiomVVI in H; auto. (*达成使用公理VVI的条件*)
  assert ((∪ ran( \{\ λ u v, u ∈ x /\ v = u \}\)) = (∪x)). (*新函数的值域是x*)
  { apply AxiomI; split; intros. 
    apply AxiomII in H2 as [H2[x0[]]].
    apply AxiomII in H4 as [H4[]].
    apply AxiomII_P in H5 as [H5[]].
    apply AxiomII. split; auto.
    exists x0. split; auto. rewrite H7. auto.
    apply AxiomII; split. exists (∪x); auto.
    apply AxiomII in H2 as [H2[x0[]]].
    exists x0; split; auto.
    apply AxiomII; split. exists x. auto.
    exists x0. apply AxiomII_P; repeat split.
    assert (Ensemble x0). 
    { exists x; auto. }
    apply Theorem49. split; auto. auto. }
  rewrite <- H2; auto.
Qed.
*)


(*
(* 代换公理 如果f是一个函数同时f的定义域是一个集，则f的值域是一个集 *)
Axiom AxiomV : forall f,
  Function f -> Ensemble dom( f ) -> Ensemble ran( f ).


(* 合并公理 如果x是一个集，则∪x 也是一个集 *)
Axiom AxiomVI : forall x,
  Ensemble x -> Ensemble (∪ x).

Theorem AxiomVVI: forall f,
  Function f -> Ensemble (dom(f)) -> Ensemble (∪(ran(f))).
Proof.
  intros. apply AxiomV in H0; auto.
  apply AxiomVI in H0; auto.
Qed.
*)


(*
Axiom AxiomVVI :  forall f,
  Function f -> Ensemble dom( f ) -> Ensemble (∪(ran( f ))).

Theorem AxiomVVI' : forall d f,
  Ensemble d -> (forall a, a ∈ d ->  Ensemble f[a])-> 
  Ensemble (∪(\{ λ y, exists a, a ∈ d /\ y = f[a] \})).
Proof.
  intros. 
  assert (Function (\{\ λ a y, a ∈ d /\ y = f[a] \}\)).
  { unfold Function. split. unfold Relation. 
    intros. PP H1 m n. apply AxiomII_P in H2 as [].
    exists m, n. auto.
    intros. destruct H1. 
    apply AxiomII_P in H1 as [H1[]].
    apply AxiomII_P in H2 as [H2[]].
    rewrite H4,H6. auto. }
  assert (d = dom(\{\ λ a y, a ∈ d /\ y = f[a] \}\)).
  { apply AxiomI; split; intros. 
    apply AxiomII; split. exists d; auto.
    exists f[z]. apply AxiomII_P.
    repeat split; auto. apply Theorem49; split.
    exists d; auto. apply H0; auto.
    apply AxiomII in H2 as [H2[]].
    apply AxiomII_P in H3. tauto. }
  rewrite H2 in H. apply AxiomVVI in H; auto.
  assert (( ran( \{\ λ a y, a ∈ d /\ y = f [a] \}\)) = 
          ( \{ λ y, exists a, a ∈ d /\ y = f[a] \})).
  { apply AxiomI; split; intros. 
    apply AxiomII in H3 as [H3[]].
    apply AxiomII_P in H4 as [H4[]].
    apply AxiomII; split; auto.
    exists x; auto.
    apply AxiomII. split.
    exists \{ λ y, exists a : Class, a ∈ d /\ y = f [a] \}; auto.
    apply AxiomII in H3 as [H3[x[]]].
    exists x. apply AxiomII_P. repeat split; auto.
    apply Theorem49. split; auto. exists d. auto. }
  rewrite H3 in H. auto.
Qed.
*)


(*
Axiom AxiomVVI' : forall d f,
  Ensemble d -> (forall a, a ∈ d ->  Ensemble f[a])-> 
  Ensemble (∪(\{ λ y, exists a, a ∈ d /\ y = f[a] \})).

Theorem AxiomVVI :  forall f,
  Function f -> Ensemble dom( f ) -> Ensemble (∪(ran( f ))).
Proof.
  intros. apply (AxiomVVI' dom(f) f) in H0.
  assert (( \{ λ y, exists a, a ∈ dom( f) 
  /\ y = f [a] \}) = ( ran( f))).
  { apply AxiomI; split; intros.
    apply AxiomII in H1 as [H1[x[]]].
    apply Property_Value in H2; auto.
    apply Property_ran in H2. rewrite H3. auto.
    apply AxiomII in H1 as [H1[]].
    apply AxiomII; split; auto.
    exists x. pose proof H2.
    apply Property_dom in H2. pose proof H2.
    apply Property_Value in H2; auto.
    split; auto.
    destruct H. apply H5 with x; split; auto. }
  rewrite H1 in H0; auto.
  intros. apply Property_Value in H1; auto.
  assert (Ensemble ([a,f [a]])).
  { exists f; auto. }
  apply Theorem49 in H2. tauto.
Qed. 
*)


(* 定义72 x × y={[u,v]: u ∈ x /\ v ∈ y} *)
Definition Cartesian x y : Class := \{\ λ u v, u∈x /\ v∈y \}\.

Notation "x × y" := (Cartesian x y)(at level 2, right associativity).


(* 定理73 如果u与y均为集，则[u]×y也是集*)
Theorem Theorem73 : forall u y,
  Ensemble u /\ Ensemble y -> Ensemble ([u] × y).
Proof.
  intros. destruct H. 
  assert (exists f, Function f /\ dom(f)= y /\ ran(f)=[u] × y ).
  { exists (\{\ λ w z, w ∈ y /\ z = [u,w] \}\).
    repeat split.
    - unfold Relation. intros. apply Property_P in H1 as [].
      auto.
    - intros. destruct H1. apply AxiomII_P in H1 as [H1[]].
      apply AxiomII_P in H2 as [H2[]].
      rewrite H4,H6; auto.
    - apply AxiomI; split; intros.
      apply AxiomII in H1 as [H1[]]. (*6*)
      apply AxiomII_P in H2; tauto.
      apply AxiomII; split. unfold Ensemble; eauto.
      exists [u,z]. apply AxiomII_P.
      split; auto. apply Theorem49; split.
      unfold Ensemble; eauto. apply Theorem49; split; auto.
      unfold Ensemble; eauto.
    - apply AxiomI; split; intros.
      apply AxiomII in H1 as [H1[]].
      apply AxiomII_P in H2 as [H2[]].
      rewrite H4. unfold Cartesian.
      apply AxiomII_P; split.
      apply Theorem49; split; auto.
      unfold Ensemble; eauto. split.
      apply Theorem41; auto. auto.
      PP H1 a b. apply AxiomII_P in H2 as [H2[]].
      apply AxiomII; split; auto. 
      exists b. apply AxiomII_P. repeat split; auto.
      apply Theorem49; split; auto.
      unfold Ensemble. eauto.
      apply Theorem41 in H3; auto. rewrite H3. auto. }
  destruct H1,H1,H2. rewrite <- H2 in H0. 
  apply AxiomV in H1; auto. rewrite H3 in H1; auto.
Qed.


(* 定理74 如果x与y均为集，则 x×y 也是集 *)
Theorem Theorem74 : forall x y, 
  Ensemble x /\ Ensemble y -> Ensemble x × y.
Proof.
  intros. pose proof H as H'. destruct H.
  assert (exists f, Function f /\ dom(f)= x 
  /\ ran( f ) = \{ λ z, (exists u, u ∈ x /\ z = [u] × y) \}).
  { exists (\{\ λ u z, u ∈ x /\ z = [u] × y \}\).
    repeat split.
    - unfold Relation; intros. PP H1 a b. eauto.
    - intros. destruct H1.
      apply AxiomII_P in H1 as [H1[]].
      apply AxiomII_P in H2 as [H2[]].
      rewrite H4,H6; auto.
    - apply AxiomI; split; intros.
      apply AxiomII in H1 as [H1[]].
      apply AxiomII_P in H2; tauto.
      apply AxiomII; split. unfold Ensemble; eauto.
      exists [z] × y. apply AxiomII_P; repeat split; auto.
      apply Theorem49; split. unfold Ensemble. eauto.
      apply Theorem73; auto. split.
      unfold Ensemble. eauto. auto.     
    - apply AxiomI; split; intros.
      apply AxiomII in H1 as [H1[]].
      apply AxiomII_P in H2 as [H2[]].
      apply AxiomII; split; auto.
      exists x0. auto.
      apply AxiomII in H1 as [H1[x0[]]]. 
      apply AxiomII; split; auto.
      exists x0. apply AxiomII_P; split; auto.
      apply Theorem49; split; auto.
      unfold Ensemble. eauto. }
    destruct H1,H1,H2. rewrite <- H2 in H. 
    apply AxiomV in H1; auto. apply AxiomVI in H1.
    rewrite H3 in H1. 
    assert (∪ \{ λ z,( exists u, u ∈ x /\ z = [u] × y) \} 
    = x × y).
    { apply AxiomI; split; intros.
      apply AxiomII in H4 as [H4[y0[]]].
      apply AxiomII in H6 as [H6[u[]]].
      rewrite H8 in H5. PP H5 a b.
      apply AxiomII_P in H9 as [H9[]].
      apply AxiomII_P; repeat split; auto.
      apply AxiomII in H10 as [].
      rewrite H12. auto. apply Theorem26' with x; auto.
      PP H4 a b. apply AxiomII_P in H5 as [H5[]].
      assert (Ensemble a). 
      { unfold Ensemble. eauto. } 
      apply AxiomII; split; auto. 
      exists [a] × y. split. apply AxiomII_P; repeat split; auto.
      apply Theorem41; auto.     
      apply AxiomII; split. apply Theorem73. auto.
      exists a. split; auto. }
    rewrite H4 in H1; auto.
Qed.
    

(* 定理75 如果f是一个函数同时f的定义域是一个集，则f是一个集 *)
Theorem Theorem75 : forall  f, Function f /\ Ensemble dom( f ) 
  -> Ensemble f.
Proof.
  intros. destruct H. pose proof H.
  apply AxiomV in H; auto.
  assert (Ensemble dom(f) ×  ran(f)).
  { apply Theorem74; auto. }
  assert (f ⊂ (dom(f) × ran(f))).
  { unfold Included. intros. 
    apply Theorem70 in H1. (*思路*) rewrite H1 in H3.
    PP H3 a b. apply AxiomII_P in H4 as [].
    apply AxiomII_P; repeat split; auto.
    apply AxiomII; split. apply Theorem49 in H4 as []. tauto.
    exists b. rewrite H1. apply AxiomII_P; auto.
    apply AxiomII; split. apply Theorem49 in H4 as []. tauto.
    exists a. rewrite H1. apply AxiomII_P; auto. }
  pose proof (Theorem33 (dom( f)) × (ran( f)) f H2 H3).
  auto.
Qed.
  

(* 定义76 Exponent y x = {f:f是一个函数，f的定义域=x 同时f的值域⊂y} *)
Definition Exponent y x : Class :=
  \{ λ f, (Function f /\ dom( f ) = x /\ (ran( f )) ⊂ y) \}.


(* 定理77 如果x与y均为集，则 Exponent y x 也是集*)
Theorem Theorem77: forall x y,
  Ensemble x /\ Ensemble y -> Ensemble (Exponent y x).
Proof.
  intros. pose proof H. apply Theorem74 in H.
  assert ((Exponent y x) ⊂ pow(x × y)).
  { unfold Included. intros. 
    apply AxiomII in H1 as [H1[H2[]]].
    apply AxiomII; split; auto. unfold Included; intros.
    apply Theorem70 in H2. rewrite H2 in H5.
    PP H5 a b. apply AxiomII_P in H6 as [].
    apply AxiomII_P; repeat split; auto.
    rewrite <- H3. apply AxiomII; split.
    apply Theorem49 in H6; tauto.
    exists b. rewrite H2. apply AxiomII_P; auto.
    unfold Included in H4. apply H4. apply AxiomII; split.
    apply Theorem49 in H6; tauto.
    exists a. rewrite H2. apply AxiomII_P. auto. }
  assert (Ensemble pow( x × y)).
  { apply Theorem38 in H; auto. }
  apply (Theorem33 pow( x × y) (Exponent y x) H2 H1).
Qed.


(* 定义78 f在x上，当且仅当f为一函数同时x=f的定义域 *)
Definition On f x : Prop :=  (Function f /\ dom( f ) = x).


(* 定义79 f到y，当且仅当f是一个函数同时f的值域⊂y *)
Definition To f y : Prop := (Function f /\ (ran(f)) ⊂ y). 


(* 定义80 f到y上，当且仅当f是一个函数同时f的值域=y *)
Definition Onto f y : Prop := (Function f /\ ran(f) = y).


End S6.

Export S6.












  