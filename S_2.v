(**S.2 分类公理图示续 *)

Require Export S_1.

Module S2.

(* {...:...} *)

Parameter Classifier : forall P: Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P) (at level 0).


(*分类公理图示Ⅱ  *)

Axiom AxiomII : forall b P, b ∈ \{ P \} <-> Ensemble b /\ (P b).


End S2.

Export S2.