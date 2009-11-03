(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt Zcompare Zorder ZArith_dec
 DecidableType2 OrderedType2 OrderedType2Facts.

Local Open Scope Z_scope.

(** * DecidableType structure for binary integers *)

Module Z_as_MiniDT <: MiniDecidableType.
 Definition t := Z.
 Definition eq_dec := Z_eq_dec.
End Z_as_MiniDT.

Module Z_as_DT <: UsualDecidableType := Make_UDT Z_as_MiniDT.

(** Note that [Z_as_DT] can also be seen as a [DecidableType]
    and a [DecidableTypeOrig]. *)



(** * OrderedType structure for binary integers *)

Module Z_as_OT <: OrderedTypeFull.
 Include Z_as_DT.
 Definition lt := Zlt.
 Definition le := Zle.
 Definition compare := Zcompare.

 Instance lt_strorder : StrictOrder Zlt.
 Proof. split; [ exact Zlt_irrefl | exact Zlt_trans ]. Qed.

 Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) Zlt.
 Proof. repeat red; intros; subst; auto. Qed.

 Lemma le_lteq : forall x y, x <= y <-> x < y \/ x=y.
 Proof.
 unfold le, lt, Zle, Zlt. intros.
 rewrite <- Zcompare_Eq_iff_eq.
 destruct (x ?= y); intuition; discriminate.
 Qed.

 Lemma compare_spec : forall x y, Cmp eq lt x y (Zcompare x y).
 Proof.
 intros; unfold compare.
 destruct (Zcompare x y) as [ ]_eqn; constructor; auto.
 apply Zcompare_Eq_eq; auto.
 apply Zgt_lt; auto.
 Qed.

End Z_as_OT.

(* Note that [Z_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for integers *)

Module ZOrder := OTF_to_OrderTac Z_as_OT.
Ltac z_order :=
 change (@eq Z) with ZOrder.OrderElts.eq in *;
 ZOrder.order.

(** Note that [z_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)
