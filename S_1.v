(**S.1 分类公理图示 *)

Module S1.

(* 定义初始 " 类( Class)" ,元素和集合的类型都是 Class *)

Parameter Class : Type.


(* ∈：属于 x∈y : In x y *)

Parameter In : Class ->Class ->Prop.

Notation "x ∈ y":=(In x y) (at level 10).


(* 外延公理Ⅰ 对于每个x与y，x=y成立的充分必要条件是对每一个z当且仅当z∈x时，z∈y *)
 
Axiom AxiomI : forall x y, x=y <->(forall z, z∈x <-> z ∈ y).


(* 定义1  x为一集当且仅当对于某一y，x∈y *)

Definition Ensemble x := exists y, x ∈ y.


End S1.

Export S1.
