(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and Wensheng Yu                  *)
(**********************************************************************)

(** Sequential_Compactness_Theorem *)

Require Export Archimedean_Theorems2.

Definition BoundedSeq x:= IsSeq x /\
  (∃ M, M ∈ RC /\ (∀ n, n ∈ Nat -> |(x[n])| ≤ M)).

Proposition not_ex_all_not2 :
 ∀ U P, ~ (∃ m n : U, P m n) -> ∀ m n : U, ~ (P m n).
Proof.
  intros. intro. elim H; eauto.
Qed.

Fact Finite_single1 : Finite ([1]).
Proof.
  assert(1 ∈ RC); auto. apply finsin; eauto.
Qed.

Fact Fin_Empty' : Finite Φ.
Proof.
  pose proof Finite_single1. apply (@finsub [1] Φ); auto.
Qed.
     
Fact Fin_Empty : ∀ A, ~ No_Empty A -> Finite A.
Proof.
  intros. unfold No_Empty in H. 
  assert(A = Φ). 
  { Absurd. elim H. apply AxiomVII in H0. destruct H0, H0. exists x; auto. }
  rewrite H0. apply Fin_Empty'.
Qed.

Section Fin_Fun.

Variable f : Class.

Hypothesis H0 : Function f.
Hypothesis H1 : Finite f.

Let h := \{\ λ u v, u ∈ dom(f) /\ v = [First(v), Second(v)] 
  /\ First(v) = u /\ Second(v) = f[u]\}\.
  
Proposition Functionh_LemmaFin_Fun : Function (h).
Proof.
  intros. split; intros. apply poisre.
  apply AxiomII' in H as [H[H3[H4[H5]]]] , H2 as [H2[H7[H8[H9]]]].
  rewrite H4, H8, H5, H6, H9, H10; auto.
Qed.

Proposition Functionh_inverse_LemmaFin_Fun : Function (h⁻¹).
Proof.
  intros. split; intros. apply poisre.
  apply AxiomII in H as [H[x0[y0[H3]]]], H2 as [H2[x1[x2[H5]]]].
  appA2H H4. appA2H H6. destruct H7 as [y3[x3[H7[H9[H10[H11]]]]]].
  destruct H8 as [x4[y4[H8[H13[H14[H15]]]]]].                 
  subst. apply MKT49b in H, H2, H4, H6. destruct H, H2, H4, H6.
  apply MKT55 in H3, H5, H7, H8; auto. destruct H3, H5, H7, H8.
  subst; auto.
Qed.
          
Proposition domh_LemmaFin_Fun : dom(h) = dom(f).
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H2 as [_[]]; auto.
  - New H. New H. apply AxiomII in H3 as [H3[y]].
    apply AxiomII; split; auto.
    exists [z, f[z]]. appA2G.
    + apply Property_Value, Property_ran in H2; auto.
      assert(Ensemble f [z]); unfold Ensemble; eauto.
    + apply Property_Value, Property_ran in H2; auto.
      assert(Ensemble f [z]); unfold Ensemble; eauto.
      exists z. exists [z, f[z]]. split; auto. split; auto. 
      assert(([z, f [z]]) ¹ = z). { apply MKT54a; auto. }
      assert(([z, f [z]]) ² = f [z]). { apply MKT54b; auto. }
      repeat split; auto. rewrite H7, H6; auto.
Qed.

Proposition ranh_LemmaFin_Fun : ran(h) = \{ λ z, z = [First(z), Second(z)] /\ 
  First(z) ∈ dom(f) /\ Second(z) = f[First(z)] \}.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H as [H[x]]. appA2H H2. 
    destruct H3 as [x0[y[H3[H4[H5[H6]]]]]]. appA2G.
    apply MKT49b in H2. destruct H2. apply MKT55 in H3; auto.
    destruct H3. subst. split; auto.
  - appA2H H. destruct H2, H3. appA2G. exists(First (z)). appA2G.
    exists(First (z)). exists(z). split; auto.
Qed.

Proposition Equf_domf_LemmaFin_Fun : f ≈ dom(f).
Proof.
  apply MKT146. red. exists h. split.
  - red. split; auto. apply Functionh_LemmaFin_Fun. 
    apply Functionh_inverse_LemmaFin_Fun.
  - split.
    + pose proof domh_LemmaFin_Fun. rewrite H; auto.
    + pose proof ranh_LemmaFin_Fun. rewrite H. apply AxiomI. intros; split.
      * intros. appA2H H2. destruct H3, H4. rewrite H3. 
        apply Property_Value in H4; auto. rewrite H5; auto.
      * intros. appA2G. New H0. red in H3. destruct H3. red in H3. 
        rename H4 into H4'.
        pose proof H3 z H2. destruct H4 as [x[y]].
        assert(Ensemble z); unfold Ensemble; eauto. New H5.
        rewrite H4 in H6. apply MKT49b in H6. destruct H6.
        pose proof MKT54a x y H6 H7. pose proof MKT54b x y H6 H7.
        rewrite <- H4 in H8, H9. rewrite <- H8 in H4. rewrite <- H9 in H4.
        rewrite H4 in H2. pose proof @Property_dom ((z)¹) ((z)²) f H2; auto. 
        pose proof @Property_ran ((z)¹) ((z)²) f H2; auto. 
        split; auto. split; auto.
        apply (H4'  ((z) ¹) ((z) ²) (f [(z) ¹])) in H2; auto.
        apply Property_Value; auto.
Qed.

Proposition Fin_Fun : Finite dom(f).
Proof.
  intros. New H1. unfold Finite in H. red. 
  assert(Ensemble f). { apply Property_Finite; auto. }
  assert(Ensemble dom(f)). { apply fdme; auto. }
  assert(f ≈ dom(f)). { apply Equf_domf_LemmaFin_Fun. }
  apply MKT154 in H4; auto. rewrite H4 in H; auto.
Qed.

End Fin_Fun.

Fact Infinite_Nat_Lemma1 : P[ω] = ω.
Proof.
  pose proof MKT165. apply MKT156 in H; tauto.
Qed.

Fact Infinite_Nat_Lemma3 : ∀ A, ~ Finite A <-> ω ∈ P[A] \/ ω = P[A].
Proof.
  split; intros.
  - TF (Ensemble A).
    + assert (P[A] ∈ R).
      { apply Property_PClass,AxiomII in H0 as [_[]]; auto. }
      New MKT138. apply AxiomII in H1 as [_], H2 as [_].
      apply (@ MKT110 ω) in H1 as [H1|[]]; auto. contradiction.
    + assert (A ∉ dom(P)).
      { rewrite MKT152b. intro. apply H0,MKT19; auto. }
      apply MKT69a in H1. rewrite H1. left. New MKT138. apply MKT19; eauto.
  - intro. unfold Finite in H0. destruct H.
    apply (MKT102 ω P[A]); auto. rewrite H in H0.
    apply (MKT101 P[A]); auto.
Qed.

Fact Infinite_Nat_Lemma4 : ∀ A B, Finite B -> A ≈ B -> Finite A.
Proof.
  intros. New H. apply Property_Finite in H1.
  New H0. apply eqvp in H2; auto. apply MKT154 in H0; auto.
  unfold Finite. rewrite H0; auto.
Qed.

Fact Infinite_Nat_Lemma5 : ∀ A B, ~ Finite B -> A ≈ B -> ~ Finite A.
Proof.
  intros. intro. apply MKT146, Infinite_Nat_Lemma4 in H0; auto.
Qed.

Fact Infinite_Nat : ~ Finite Nat.
Proof.
  assert (~ Finite ω).
  { apply Infinite_Nat_Lemma3. rewrite Infinite_Nat_Lemma1; auto. }
  assert(Nat = ω ~ One). { unfold Nat; auto. }
  assert(ω =  Nat ∪ One). 
  { unfold Union. rewrite H0. apply AxiomI; intros; split; intros.
    - appA2G. TF(z ∈ One); auto.
    - appA2H H1. destruct H2.
      + unfold Setminus in H2. apply MKT4' in H2. destruct H2; auto.
      + pose proof MKT135a. pose proof @MKT134 Φ H3. 
        assert(One ∈ ω). { unfold One; auto. }
        pose proof Property_W. unfold Ordinal in H6. destruct H6.
        unfold Full in H7. apply H7 in H5. unfold Included in H5.
        apply H5; auto. }
   Absurd. apply NNPP' in H2. elim H. rewrite H1. apply MKT168; auto.
   unfold One, PlusOne. assert(Ensemble Φ); auto. New H3. apply finsin in H4.
   assert(Finite Φ). { apply (@finsub Nat Φ); auto. } apply MKT168; auto.
Qed.

Lemma AllSeqInFinite : ∀ a, IsSeq a -> ~ Finite a.
Proof.
  intros; intro. destruct H. New H. rename H2 into H2'. destruct H, H1.
  assert(Finite dom(a)). { apply Fin_Fun; auto. }
  rewrite H1 in H4. apply Infinite_Nat; auto.
Qed. 

Fact unfold_Ordered: ∀ z f, Ensemble z -> Function f -> z ∈ f 
  -> z = [(z) ¹, (z) ²].
Proof.
  intro z. intro f. intros. red in H0. destruct H0. red in H0. 
  pose proof H0 z H1. destruct H3 as [x[y]]. 
  assert(Ensemble z); unfold Ensemble; eauto. New H4.
  rewrite H3 in H5. apply MKT49b in H5. destruct H5.
  pose proof MKT54a x y H5 H6. pose proof MKT54b x y H5 H6.
  rewrite <- H3 in H7, H8. rewrite <- H7 in H3. rewrite <- H8 in H3; auto.
Qed.

Fact Seq_eq_SeqEnsemble : ∀ a, IsSeq a 
  -> a = \{ λ z , ∃ n , n ∈ Nat /\ z = [n, (a [n])] \}.
Proof.
  intros. red in H. destruct H, H0. 
  apply AxiomI; intros; split; intros.
  - appA2G. assert(Ensemble z); unfold Ensemble; eauto. New H.
    apply (unfold_Ordered z a) in H4; auto. New H3. rewrite H4 in H5.
    apply MKT49b in H5. destruct H5. exists (First z). New H2. 
    rewrite H4 in H7. New H7. apply Property_dom in H7. rewrite <- H0.
    split; auto. apply Property_Value in H7; auto. red in H. destruct H.
    apply (H9 (z) ¹ (z) ² a [(z) ¹]) in H8; auto. rewrite <- H8; auto.
  - appA2H H2. destruct H3 as [n[H3]]. subst. 
    assert(Ensemble n); unfold Ensemble; eauto. New H2.
    apply MKT49b in H5. rewrite <- H0 in H3. destruct H5.
    apply Property_Value; auto.
Qed.

Fact SeqEnsemble_eq_SeqFam : ∀ a, IsSeq a 
  -> \{ λ z , ∃ n , n ∈ Nat /\ z = [n, (a [n])] \} 
    = ∪ (\{ λ z ,∃ r, r ∈ (ran(a)) 
      /\ z = \{ λ z1, z1 ∈ a /\ Second z1 = r \} \}).
Proof.
  intros. unfold Element_U. apply AxiomI; intros; split; intros.
  - appA2G. appA2H H0. destruct H1 as [n[H1]].
    exists(\{ λ z1 : Class,z1 ∈ a /\ (z1) ² = a[n] \}).
    New H. red in H3. destruct H3, H4. New H1. rewrite <- H4 in H6.
    New H6. apply Property_Value in H6; auto. New H6. rewrite <- H2 in H6.
    rename H6 into Hz. apply Property_ran in H8. rename H8 into Ha1.
    New H0. rewrite H2 in H6. apply MKT49b in H6. destruct H6.
    apply (MKT54b n a[n]) in H8; auto. rewrite <- H2 in H8. rename H8 into Hz2.
    pose proof EnNat. rewrite <- H4 in H8. apply MKT75 in H8; auto.
    rename H8 into Ha2. clear H3 H4 H5 H6 H7.
    split.
    + appA2G. 
    + appA2G. 
      apply (MKT33 a \{ λ z1 : Class,z1 ∈ a /\ (z1) ² = a [n] \}); auto.
      unfold Included; intros. appA2H H3. destruct H4; auto.
  - appA2G. appA2H H0. destruct H1 as [Y[H1]]. appA2H H2. 
    destruct H3 as [r[H3]]. subst. appA2H H1. destruct H4.
    exists(First z). subst. red in H. destruct H, H5. New H.
    apply (unfold_Ordered z a) in H7; auto. rewrite H7 in H4.
    New H4. apply Property_dom in H8. New H8. apply Property_Value in H9; auto.
    red in H. destruct H. pose proof H10 _ _ _ H4 H9.
    rewrite <- H5. rewrite <- H11. split; auto.
Qed.

Fact Seq_eq_SeqFam : ∀ a, IsSeq a -> a = ∪ (\{ λ z ,∃ r, r ∈ (ran(a)) 
  /\ z = \{ λ z1, z1 ∈ a /\ Second z1 = r \} \}).
Proof.
  intros. pose proof Seq_eq_SeqEnsemble. pose proof SeqEnsemble_eq_SeqFam.
  New H. New H. apply H0 in H2. apply H1 in H3. rewrite <- H2 in H3; auto.
Qed.

Section Fin_Ran.

Variable f : Class.
Hypothesis Hf : IsSeq f.
Hypothesis H1 : Finite ran(f).

Proposition Hf1 : Function f.
Proof.
  red in Hf. destruct Hf; auto.
Qed.

(* Let A := ran(f). *)
Let B := \{ λ z,∃r : Class,
  r ∈ ran(f) /\ z = \{ λ z1, z1 ∈ f /\ (z1) ² = r \} \}.
Let h := \{\ λ u v, u ∈ ran(f) /\ v = \{ λ z, z ∈ f /\ (z) ² = u \} \}\.

Proposition Functionh_LemmaFin_Ran : Function (h).
Proof.
  intros. split; intros. apply poisre.
  apply AxiomII' in H as [H[H2]] , H0 as [H0[H4]]. subst; auto.
Qed.

Proposition Functionh_inverse_LemmaFin_Ran : Function (h⁻¹).
Proof.
  intros. split; intros. apply poisre. pose proof Hf1 as Hf1.
  apply AxiomII in H as [H[x0[y0[H2]]]], H0 as [H0[x1[x2[H4]]]].
  appA2H H3. appA2H H5. destruct H6 as [y3[x3[H6[H8]]]]. 
  destruct H7 as [x4[y4[H7[H10]]]].
  subst. apply MKT49b in H, H0, H3, H5. destruct H, H0, H3, H5.
  apply MKT55 in H2, H4, H6, H7; auto. destruct H2, H4, H6, H7.
  subst; auto. New H10. apply Einr in H2; auto. destruct H2 as [n[H2]].
  New H2. apply Property_Value in H6; auto. subst.
  assert(([n, f[n]]) ∈ \{ λ z0, z0 ∈ f /\ (z0) ² = f[n] \}).
  { appA2G. split; auto. apply MKT54b; auto. unfold Ensemble; eauto. }
  assert(∀z : Class,z ∈ \{ λ z0 : Class, z0 ∈ f /\ (z0) ² = y3 \} 
    <-> z ∈ \{ λ z0 : Class, z0 ∈ f /\ (z0) ² = f[n] \}).
  { pose proof AxiomI 
    (\{ λ z, z ∈ f /\ (z) ² = y3 \}) (\{ λ z, z ∈ f /\ (z) ² = f[n] \}).
    destruct H7. apply H7; auto. }
  apply H7 in H4. appA2H H4. destruct H14. rewrite MKT54b in H15; auto. 
  unfold Ensemble; eauto.
Qed.

Proposition domh_LemmaFin_Ran : dom(h) = ran(f).
Proof.
   pose proof Hf1 as H0. apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H2 as [_[]]; auto.
  - New H. New H. apply AxiomII in H3 as [H3[y]].
    apply AxiomII; split; auto.
    exists (\{ λ z1, z1 ∈ f /\ (z1) ² = z \}). appA2G.
    + apply MKT49a; auto. 
      red in Hf. destruct Hf, H6. pose proof EnNat. rewrite <- H6 in H8.
      apply MKT75 in H8; auto.
      apply (MKT33 f \{ λ z1, z1 ∈ f /\ (z1) ² = z \}); auto.
      unfold Included; intros. appA2H H9. destruct H10; auto.
Qed.

Proposition ranh_LemmaFin_Ran : 
  ran(h) = \{ λ z, ∃ u, u ∈ dom(h) /\ z = \{ λ z, z ∈ f /\ (z) ² = u \} \}.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H. destruct H as [H[x]]. appA2H H0. 
    destruct H2 as [x0[y[H3[H4]]]]. appA2G.
    apply MKT49b in H0. destruct H0. apply MKT55 in H3; auto.
    destruct H3. subst. rewrite domh_LemmaFin_Ran. exists x0. split; auto.
  - appA2H H. destruct H0 as [x[H0]]. apply (@Property_ran x z h); auto.
    New H0. rewrite domh_LemmaFin_Ran in H3.
    assert(h[x] = z).
    { New H2. pose proof Functionh_LemmaFin_Ran.
      apply Property_Value in H0; auto. appA2H H0; auto.
      destruct H6 as [x0[hx0[H6[H8]]]]. apply MKT49b in H0. destruct H0.
      apply MKT55 in H6; auto. destruct H6. subst; auto. }
    rewrite <- H4. pose proof Functionh_LemmaFin_Ran.
    apply Property_Value; auto.
Qed.

Proposition Equf_domf_LemmaFin_Ran : B ≈ ran(f).
Proof.
  apply MKT146. red. exists h. split.
  - red. split; auto. apply Functionh_LemmaFin_Ran. 
    apply Functionh_inverse_LemmaFin_Ran.
  - split.
    + pose proof domh_LemmaFin_Ran. rewrite H; auto.
    + pose proof ranh_LemmaFin_Ran. rewrite H. apply AxiomI. intros; split.
      * intros. appA2H H0. destruct H2, H2. appA2G. exists x.
        rewrite <- domh_LemmaFin_Ran. split; auto.
      * intros. appA2G. appA2H H0. destruct H2 as [r[H2]]. exists r.
        rewrite domh_LemmaFin_Ran. split; auto.
Qed.

Proposition Fin_Ran : Finite B.
Proof.
  intros. New H1. unfold Finite in H. red. 
  assert(Ensemble ran(f)). { apply Property_Finite; auto. }
  assert(Ensemble B). 
  { apply (MKT33 ran(h) B); auto.
    - pose proof Functionh_LemmaFin_Ran. pose proof domh_LemmaFin_Ran.
      rewrite <- H3 in H0. New H2. apply MKT75, frne in H2; auto.
    - unfold Included; intros. appA2H H2. destruct H3 as [r[H3]].
      rewrite ranh_LemmaFin_Ran. appA2G. exists r. 
      rewrite domh_LemmaFin_Ran. split; auto. }
  pose proof Equf_domf_LemmaFin_Ran.
  apply MKT154 in H3; auto. rewrite <- H3 in H; auto.
Qed.

End Fin_Ran.
  
Lemma SL1: ∀ a, BoundedSeq a -> Finite ran(a) 
  -> ∃ y, y ∈ ran(a) /\ ~ Finite \{ λ z, z ∈ a /\ Second z = y \}.
Proof.
  intro a. intro H'. intros. Absurd.
  assert(∀ y, ~ (y ∈ ran(a) /\ ~ Finite \{ λ z, z ∈ a /\ Second z = y \})).
  { intros. Absurd. elim H0. clear H0. apply NNPP' in H1. exists y.
    destruct H1; split; auto. } clear H0. 
  assert (∀ y, (y ∈ ran(a) -> Finite \{ λ z, z ∈ a /\ Second z = y \})).
  { intros; pose proof (H1 y).
    apply property_not in H2; destruct H2; try tauto.
    apply property_not'; auto. } clear H1.
  New H0.
  assert (Finite (∪ (\{ λ z ,∃ r, r ∈ (ran(a)) 
    /\ z = \{ λ z1, z1 ∈ a /\ Second z1 = r \} \}))).
  { apply MKT169; auto.
    - clear H1 H0. red in H'. destruct H'. New H. 
      pose proof Fin_Ran a H0 H; auto.
    - intros. appA2H H2. destruct H3, H3. rewrite H4; auto. }
  assert (Finite a).
  { red in H'. destruct H'. apply Seq_eq_SeqFam in H3. rewrite H3; auto. }
  red in H'. destruct H' as []. apply AllSeqInFinite in H3; auto.
  elim H3; auto.
Qed.


Corollary Fin_Included : ∀ A B, Ensemble A -> Ensemble B 
  -> A ⊂ B -> Finite B -> Finite A.
Proof.
  intros. apply (@finsub B A); auto.
Qed.

Fact Fin_OneNat : ∀ n, n ∈ Nat -> Finite n.
Proof.
  intros. assert(Ensemble n); unfold Ensemble; eauto.
  assert(n ∈ ω). { unfold Nat in H. 
    unfold Setminus in H. apply MKT4' in H. destruct H; auto. }
  pose proof MKT164. unfold Included in H2. New H1. apply H2 in H1. 
  apply MKT156 in H1. destruct H1. red. rewrite H4; auto.
Qed.

Fact NtoR8 : ∀ x y, x ∈ Nat -> y ∈ Nat -> (x ≤ y)%Nat -> NtoR x ≤ NtoR y.
Proof.
  intros. red. destruct H1.
  - left. apply NtoR3; auto.
  - right. apply NtoR1; auto.
Qed.

Fact NtoR8' : ∀ x y, x ∈ Nat -> y ∈ Nat -> NtoR x ≤ NtoR y -> (x ≤ y)%Nat.
Proof.
  intros. destruct H1.
  - left. apply NtoR3'; auto.
  - right. apply NtoR1'; auto.
Qed.

Fact Fin_FinNat : ∀ n, n ∈ Nat 
  -> Finite \{ λ z, z ∈ Nat /\ NtoR z ≤ NtoR n \}.
Proof.
  apply Mathematical_Induction_Nat.
  - assert(One ∈ Nat); auto. assert(Ensemble One );unfold Ensemble; eauto.
    apply finsin in H0.
    assert(\{ λ z, z ∈ Nat /\ NtoR z ≤ NtoR One \} = [One]).
    { apply AxiomI; intros; split; intros.
      + appA2H H1. destruct H2. assert(Ensemble z); unfold Ensemble; eauto.
        appA2G; intros. New H2. apply FAT24 in H2. New H6.
        apply (@FAT10 z One) in H6; auto. destruct H6; auto. destruct H6. 
        * apply NtoR3 in H6; auto. apply @legRf in H3; auto; contradiction.
        * apply legNf in H2; auto; contradiction.
      + appA2H H1. appA2G. assert(One ∈ μ); unfold Ensemble; eauto. 
        apply H2 in H3. subst. split; auto. red; right; auto. }
    rewrite H1; auto.
  - intros. assert(\{ λ z, z ∈ Nat /\ NtoR z ≤ NtoR (k + One)%Nat \} =
    \{ λ z, z ∈ Nat /\ NtoR z ≤ NtoR k \} ∪ [(k + One)%Nat]).
    { apply AxiomI; intros; split; intros.
      + appA2H H1. appA2G. destruct H2, H3.
        * left. appA2G. split; auto. apply NtoR3', FAT26a, NtoR8 in H3; auto.
        * right. appA2G; intros. apply NtoR1'; auto.
      + appA2H H1. appA2G. destruct H2.
        * appA2H H2. destruct H3. split; auto. 
          apply NtoR8', FAT26b in H4; auto. apply NtoR8; auto.
        * appA2H H2. assert((k + One)%Nat ∈ Nat); auto.
          assert(Ensemble (k + One)%Nat). { unfold Ensemble; eauto. }
          assert((k + One)%Nat ∈ μ); auto. apply H3 in H6. subst.
          split; auto. right; auto. }
    rewrite H1. apply MKT168; auto. assert((k + One)%Nat ∈ Nat); auto.
    apply finsin;unfold Ensemble; eauto.
Qed.

Lemma SL2 : ∀ a, BoundedSeq a -> Finite ran(a) -> ∃ N, N ∈ Nat 
  /\ (∀ n, n ∈ Nat -> (∃ m, m ∈ Nat /\ NtoR m > NtoR n /\ a[m] = a[N])).
Proof.
  intro a. intro H'. intro H. pose proof SL1 a H' H. 
  destruct H0 as [r [H0 H1 ]]. red in H'. destruct H'. New H2. destruct H2, H5.
  New H0. apply Einr in H7; auto. destruct H7 as [N[H7]]. subst r.
  exists N. rewrite H5 in H7. split; auto. intros. Absurd; elim H1.
  assert(Ensemble \{ λ z, z ∈ a /\ (z) ² = a [N] \}).
  { pose proof EnNat. rewrite <- H5 in H10. apply MKT75 in H10; auto.
    apply (MKT33 a \{ λ z, z ∈ a /\ (z) ² = a [N] \}); auto.
    unfold Included; intros. appA2H H11. destruct H12; auto. }
  assert(Ensemble \{ λ z, z ∈ a /\ ~ NtoR (z) ¹ > NtoR n \}).
  { pose proof EnNat. rewrite <- H5 in H11. apply MKT75 in H11; auto.
    assert(\{ λ z, z ∈ a \} ⊂ a).
    { unfold Included; intros. appA2H H12; auto. } 
    New H12. apply (MKT33 a \{ λ z, z ∈ a\}) in H13; auto.
    apply (MKT33 \{ λ z, z ∈ a\} \{ λ z, z ∈ a /\ ~ NtoR (z) ¹ > NtoR n \}); 
    auto. unfold Included; intros. appA2H H14. destruct H15; auto. appA2G. }
  apply Fin_Included with (\{ λ z, z ∈ a /\ (~(NtoR(First z)>NtoR n))\});auto.
  - red; intros. appA2H H12. destruct H13. appA2G. split; auto. intro. 
    elim H9. exists (z) ¹. pose proof unfold_Ordered z a H12 H2 H13. New H13.
    rewrite H16 in H17. New H17. apply Property_dom in H18. New H18. 
    apply Property_Value in H19; auto. red in H2. destruct H2.
    pose proof H20 (z) ¹ (z) ² a [(z) ¹] H17 H19. rewrite <- H5. 
    rewrite <- H14, H21. repeat split; auto. 
  - assert(forall z, z ∈ a -> (z) ¹ ∈ Nat). 
    { intros. assert(Ensemble z); unfold Ensemble; eauto.
      pose proof unfold_Ordered z a H13 H2 H12. rewrite H14 in H12.
      apply Property_dom in H12. rewrite H5 in H12; auto. }
    rename H12 into Hz.
    assert(\{ λ z, z ∈ a /\ ~ NtoR (z) ¹ > NtoR n \} 
      ⊂ \{ λ z, z ∈ a /\ NtoR (z) ¹ ≤ NtoR n \}).
    { unfold Included; intros. appA2H H12. destruct H13. appA2G.
      split; auto. apply Notle; auto. }
    apply (@finsub \{ λ z, z ∈ a /\ NtoR (z) ¹ ≤ NtoR n \} 
      \{ λ z, z ∈ a /\ ~ NtoR (z) ¹ > NtoR n \}); auto. clear H12.
    pose proof Fin_FinNat.
    apply (Infinite_Nat_Lemma4 \{ λ z, z ∈ a /\ NtoR (z) ¹ ≤ NtoR n \}
    \{ λ z, z ∈ Nat /\ NtoR z ≤ NtoR n \}); auto. clear H12.
    unfold Equivalent.
    exists(\{\ λ u v, u ∈ a /\ NtoR (u) ¹ ≤ NtoR n /\ v = (u) ¹ \}\).
    assert(Function \{ λ z, ∃x y : Class,
      z = [x, y] /\ x ∈ a /\ NtoR (x) ¹ ≤ NtoR n /\ y = (x) ¹ \}).
    { red. split; intros.
      - apply poisre.
      - apply AxiomII' in H12 as [H12[H14[H15]]], H13 as [H13[H17[H18]]].
        subst; auto. }
    assert(Function \{ λ z, ∃x y : Class,
      z = [x, y] /\ x ∈ a /\ NtoR (x) ¹ ≤ NtoR n /\ y = (x) ¹ \} ⁻¹).
    { red. split; intros.
      - apply poisre.
      - appA2H H13. destruct H15 as [x0[y0[H15]]].
        appA2H H16. destruct H17 as [y1[x1[H17[H18[H19]]]]].
        appA2H H14. destruct H21 as [x2[y2[H21]]].
        appA2H H22. destruct H23 as [y3[x3[H23[H24[H25]]]]].
        subst. apply MKT49b in H13, H14, H16, H22. destruct H13, H14, H16, H22.
        apply MKT55 in H15, H17, H21, H23; auto. destruct H15, H17, H21, H23.
        subst; auto. New H18. New H24. apply unfold_Ordered in H15; auto.
        apply unfold_Ordered in H17; auto. rewrite H15 in H18. 
        rewrite H17 in H24. rewrite H32 in H18, H15. 
        red in H2. destruct H2 as [_].
        apply (H2 (y3) ¹ (y1) ² (y3) ²) in H18; auto. 
        rewrite H18 in H15. subst; auto. }
    split; auto. split; auto. split.
    + apply AxiomI; split; intros.
      * appA2H H14. destruct H15. appA2H H15. 
        destruct H16 as [z1[x1[H16[H17[H18]]]]]. apply MKT49b in H15.
        destruct H15. apply MKT55 in H16; auto. destruct H16. subst. appA2G.
      * appA2H H14. destruct H15. appA2G. exists (z) ¹. appA2G. exists z.
        exists (z) ¹. split; auto.
    + apply AxiomI; split; intros.
      * appA2H H14. destruct H15. appA2H H15. 
        destruct H16 as [z1[x1[H16[H17[H18]]]]]. apply MKT49b in H15.
        destruct H15. apply MKT55 in H16; auto. destruct H16. subst. appA2G.
      * appA2H H14. destruct H15. appA2G. exists ([z, a[z]]).
        rewrite <- H5 in H15. New H15. apply Property_Value in H17; auto. 
        assert(Ensemble ([z, a [z]])); unfold Ensemble; eauto. appA2G. 
        exists ([z, a[z]]). exists z. split; auto. 
        New H15. split; auto. apply MKT49b in H18. destruct H18. 
        apply (MKT54a z a[z]) in H18; auto. rewrite H18. split; auto.
Qed.

Fact Leq_P2 : ∀ x y, x ∈ RC -> y ∈ RC -> x ≤ y -> y ≤ x -> x = y.
Proof.
  intros. destruct H1; auto.
  pose proof (@legRf y x). MP. contradiction.
Qed.

Global Hint Resolve Leq_P2: core. 

Definition upper_RC X := 
  \{ λ r, r ∈ RC /\ (∀r0 : Class,r0 ∈ X -> (r0 < r)%RC) \}.

Lemma RC_divide : ∀X, X ⊂ RC -> X <> Φ ->
  (∃ y, y∈ RC /\ (∀x ,x ∈ X -> (x < y)%RC)) ->
  divide (RC ~ (upper_RC X)) (upper_RC X).
Proof.
  intros. destruct H1 as [y []]. repeat split.
  - red. intros. appA2H H3. tauto.
  - red. intros. appA2H H3. tauto.
  - intro. assert (exists x, x ∈ X). apply NEexE; auto.
    destruct H4. assert (x∈(RC ~ upper_RC X)).
    { apply AxiomII; split. eauto. split; auto.
      appA2G. intro. appA2H H5. destruct H6. apply H7 in H4.
      assert (x = x). auto. CordR. }
    rewrite H3 in H5. eapply MKT16; eauto.
  - intro. assert (y∈(upper_RC X)). { appA2G. }
    rewrite H3 in H4. eapply MKT16; eauto.
  - red. intros. destruct (classic (a ∈ upper_RC X)); auto.
  - red. intros. assert ((b < a)%RC -> False).
    { intro. appA2H H4. destruct H6. appA2H H3.
      destruct H8. appA2H H9. destruct H10.
      apply AxiomII. split. eauto. split; auto.
      intros. pose proof H10. apply H in H10. apply H7 in H11.
      pose proof @FAT171 r0 b a.
      apply H12; auto. } appA2H H3. destruct H6. appA2H H7.
      pose proof H4. appA2H H9. destruct H10 as [? _].
      destruct (@FAT167 a b) as [?|[?|?]]; auto. rewrite H11 in H8.
      contradiction. apply H5 in H11. contradiction.
Qed.

Theorem Completeness : ∀ X Y, X ⊂ RC -> Y ⊂ RC -> X <> Φ -> Y <> Φ
    -> (∀ x y, x ∈ X -> y ∈ Y -> x ≤ y) -> ∃ c, c ∈ RC
    /\ (∀ x y, x ∈ X -> y ∈ Y -> (x ≤ c /\ c ≤ y)).
Proof.
  intros. destruct (classic (X∩Y = Φ)) as [em|nem].
  { pose proof FAT205a. pose proof RC_divide _ H H1.
  assert (divide (RC ~ upper_RC X) (upper_RC X)). {
    apply H5. assert (exists y, y ∈ Y). { apply NEexE; auto. }
    destruct H6 as [y ?]. exists y. split; auto.
    intros. destruct (@FAT167 x y); auto.
    - assert (x∈X ∩ Y). { appA2G. split; subst; auto. }
      rewrite em in H9. pose proof (@MKT16 x). destruct H10; auto.
    - destruct H8; auto. pose proof H3 _ _ H7 H6.
      destruct H9; CordR. }
  apply H4 in H6. destruct H6 as [e []].
  exists e. split; auto. intros. destruct H7.
  pose proof @FAT167. assert (Hx: x ∈ RC). auto.
  assert (Hy: y∈RC); auto. pose proof H11 x e Hx H6.
  pose proof H11 e y H6 Hy. split.
  - destruct H12; auto. right; auto. destruct H12.
    + apply H10 in H12; auto. appA2H H12. destruct H14.
      apply H15 in H8; auto. assert (x=x); auto. CordR.
    + left; auto.
  - destruct H13; auto. right; auto.
    destruct H13. pose proof H13 as Hey.
    + apply H7 in H13; auto. appA2H H13. destruct H14.
      appA2H H15. destruct H16. apply AxiomII. split.
      eauto. split; auto. intros. pose proof H3 _ _ H16 H9.
      assert ((r0 < y)%RC \/ (r0 = y)%RC).
      { auto. } destruct H18; auto.
      assert (y ∈ X ∩ Y). { appA2G. subst; auto. } rewrite em in H19.
      pose proof (@MKT16 y). contradiction.
    + left; auto. }
  assert (exists c, c ∈ X ∩ Y). { apply NEexE; auto. }
  destruct H4 as [c ?]. appA2H H4. destruct H5.
  exists c. split; auto.
Qed.

Definition Lower X c := X ⊂ RC /\ c ∈ RC /\ (∀ x, x ∈ X -> c ≤ x).

Definition Inf1 X i := Lower X i /\ (∀ i1, i1 ∈ RC -> i < i1
  -> (∃ x1, x1 ∈ X /\ x1 < i1)).

Definition Inf2 X i := Max (\{ λ u, Lower X u \}) i.

Corollary Order_Co1 : ∀ x y, x ∈ RC -> y ∈ RC -> x < y \/ y < x \/ x = y.
Proof.
  intros. pose proof H. apply (Leq_P4 x y) in H1 as []; auto;
  destruct (classic (x = y)); auto; [left|right; left].
  - red in H1. destruct H1; auto. apply H2 in H1; contradiction.
  - red in H1. destruct H1; auto. apply sym, H2 in H1; contradiction.
Qed.

Corollary Inf_Corollary : ∀ X i, Inf1 X i <-> Inf2 X i.
Proof.
  split; intros; destruct H.
  - destruct H as [H[]]. repeat split. unfold Included; intros.
    apply AxiomII in H3 as [_[_[]]]; auto. apply AxiomII; split;
    eauto. split; auto. intros. apply AxiomII in H3 as [H3[H4[]]].
    pose proof H5. apply (Order_Co1 x i) in H7 as [H7|[|]]; auto.
    + left; auto. 
    + apply H0 in H7 as [x1[]]; auto.
    pose proof H7. apply H6 in H7. apply legRf in H7; auto; contradiction.
    + right; auto.
  - destruct H0. apply AxiomII in H0 as [H0[H2[]]].
    repeat split; auto. intros. apply NNPP; intro.
    assert (∀ x1, x1 ∈ X -> i1 ≤ x1).
    { intros. apply NNPP; intro. elim H7. exists x1. split; auto.
      pose proof H5. apply (Order_Co1 x1 i1) in H10 as [H10|[|]];
      auto. apply NotleR; auto. apply NotleR; auto. }
    assert (i1 ∈ \{ λ u, Lower X u \}).
    { apply AxiomII; split; eauto. split; auto. }
    apply H1 in H9. apply legRf in H9; auto; contradiction.
Qed.

Corollary Max_Corollary : ∀ X c1 c2, Max X c1 -> Max X c2 -> c1 = c2.
Proof.
  intros. destruct H as [H[]],H0 as [H0[]].
  pose proof H1. pose proof H3. apply H2 in H5.
  apply H4 in H6. apply Leq_P2; auto.
Qed.

Theorem InfT : ∀ X, X ⊂ RC -> X <> Φ -> (∃ c, Lower X c)
  -> exists ! i, Inf1 X i.
Proof.
  intros. destruct H1 as [x]. set (Y := \{ λ u, Lower X u \}).
  assert (Y <> Φ).
  { apply NEexE. exists x. apply AxiomII; split; auto.
    destruct H1 as [_[]]. eauto. }
  assert (Y ⊂ RC).
  { unfold Included; intros. apply AxiomII in H3 as [_[_[]]]; auto. }
  assert (∃ c, c ∈ RC /\ (∀ y x, y ∈ Y -> x ∈ X
    -> (y ≤ c /\ c ≤ x))) as [c[]].
  { apply Completeness; auto. intros. apply AxiomII in H4
    as [_[_[]]]; auto. }
  assert (c ∈ Y).
  { apply AxiomII; split; eauto. repeat split; auto. intros.
    apply NEexE in H2 as [y]. apply (H5 y x0) in H6; tauto. }
  assert (Inf2 X c).
  { repeat split; auto. intros. apply NEexE in H0 as [x1].
    apply (H5 x0 x1) in H7; tauto. }
  exists c. split. apply Inf_Corollary; auto. intros.
  apply Inf_Corollary in H8. apply (Max_Corollary Y); auto.
Qed.

Definition NtoR_Ens E := \{ λ u, ∃ n, n ∈ E /\ u = NtoR n \}.

Proposition Nat_P7 : ∀ E, E ⊂ Nat -> E <> Φ -> ∃ n, Min (NtoR_Ens E) n.
Proof.
  intros. assert (∃ n, Lower (NtoR_Ens E) n).
  { exists 1. repeat split; unfold Included; auto.
    - intros. appA2H H1. destruct H2, H2. subst. unfold Included in H.
      apply H in H2. apply NtoRRC; auto.
    - intros. appA2H H1. destruct H2, H2. subst. unfold Included in H.
      apply H in H2. New H2. rename H3 into Hx0. apply FAT24 in H2; auto.
      assert(1 = NtoR One); auto. rewrite H3. apply NtoR8; auto. }
  assert(NtoR_Ens E ⊂ RC) as HE1. 
  { unfold Included; intros. appA2H H2. destruct H3, H3. subst.
    unfold Included in H. apply H in H3. apply NtoRRC; auto. }
  assert(NtoR_Ens E ≠ Φ) as HE2.
  { assert(Ensemble E). { apply (MKT33 Nat E); auto. }
    assert(∃ x, x ∈ E). 
    { Absurd. assert(∀ x, ~ x ∈ E). 
      { intros. Absurd. apply NNPP' in H4. elim H3. exists x; auto. }
      clear H3. elim H0. apply AxiomI; split; intros. 
      apply H4 in H3; contradiction. apply MKT16 in H3; contradiction. }
    destruct H3. assert(∃ y, y ∈ NtoR_Ens E ). 
    { exists (NtoR x). unfold NtoR_Ens. appA2G. }
    destruct H4. Absurd. apply NNPP' in H5. rewrite H5 in H4. 
    apply MKT16 in H4; contradiction. }
  apply InfT in H1 as [e[H1 _]]; unfold Included; auto.
  destruct (classic (e ∈ NtoR_Ens E)). exists e. repeat split;
  unfold Included; intros; auto.
  destruct H1 as [[_[]]]; auto.
  assert (∀ x, x ∈ NtoR_Ens E -> e < x).
  { intros. destruct H1 as [[_[]]]. New H3. apply H4 in H6. destruct H6; auto.
    subst. apply H2 in H3; contradiction. }
  assert (e ∈ RC). { destruct H1 as [[_[]]]; auto. }
  assert (e < e + 1); auto. 
  destruct H1. apply H6 in H5 as [m[]]; auto.
  exists m. repeat split; unfold Included; intros; auto.
  assert (m ∈ RC /\ x ∈ RC) as []. { split; auto. }
  pose proof H9. apply (Order_Co1 x m) in H11 as [H11|[|]]; auto.
  - assert (x + 1 ≤ m). 
    { appA2H H5. appA2H H8. destruct H12 as [m1[]], H13 as [x1[]]. subst.
      rewrite <- NtoROne. rewrite NtoR2; auto. apply NtoR8; auto.
      apply NtoR3' in H11; auto. apply FAT25a; auto. }
    assert (x + 1 < e + 1). { apply (FAT172 (x + 1) m (e + 1)); auto. }
    assert (x < e). { apply (FAT188c1 x e 1); auto. }
    apply H3 in H8. apply lgRf in H14; auto; contradiction.
  - left; auto. 
  - right; auto.
Qed.

Fact Nat_hasMin : ∀ M, M ⊂ Nat -> M <> Φ 
  -> ∃ m, m ∈ M /\ (∀ x, x ∈ M -> NtoR m ≤ NtoR x).
Proof.
  intros. New H. apply Nat_P7 in H1; auto. destruct H1 as [m].
  unfold Min in H1. destruct H1, H2. New H2. rename H4 into Hm1.
  appA2H H2. destruct H4 as [mNat[H4]].
  exists mNat. split; auto. intros. 
  assert(x ∈ Nat). { unfold Included in H. apply H; auto. }
  assert(NtoR x ∈ NtoR_Ens M). { appA2G. } rewrite <- H5. apply H3; auto.
Qed.

Theorem SCT_Finite : ∀ a, BoundedSeq a -> Finite ran(a) 
  -> ∃ b, (SubSeq a b) /\ Conv_Seq b.
Proof.
  intros. pose proof SL1 a H H0. pose proof SL2 a H H0. destruct H2 as [N[H2]].
  (* b *)
  set (\{\ λ u v, u ∈ Nat /\ v = a[N] \}\) as b. exists b.
  assert(IsSeq a) as IsSeq_a. { red in H. destruct H; auto. }
  assert(IsSeq b) as IsSeq_b.
  { red. split.
    + red. split. apply poisre. intros. appA2H H4. appA2H H5.
      apply MKT49b in H4, H5. destruct H4, H5.
      destruct H6 as [x1[y1[H6[H10]]]]. destruct H7 as [x2[y2[H7[H12]]]].
      apply MKT55 in H6, H7; auto. destruct H6, H7. subst; auto.
    + split.
      * apply AxiomI; intros; split; intros; auto.
        ++ appA2H H4. destruct H5 as [y]. appA2H H5. 
           destruct H6 as [z1[y1[H6[H7]]]]. apply MKT49b in H5 as [].
           apply MKT55 in H6 as []; auto. subst; auto.
        ++ appA2G. exists(a [N]). appA2G. apply MKT49a. 
           unfold Ensemble; eauto. pose proof anRC a z IsSeq_a H4.
           unfold Ensemble; eauto.
      * unfold Included; intros. appA2H H4. destruct H5. appA2H H5.
        destruct H6 as [x1[z1[H6[H7]]]]. apply MKT49b in H5 as [].
        apply MKT55 in H6 as []; auto. subst. apply anRC; auto. } split. 
  - red. split; auto. split; auto.
    set (\{\ λ u v, u ∈ Nat /\ v ∈ Nat /\ NtoR v > NtoR u /\ a[v] = a[N] 
      /\ (∀ v2, v2 ∈ Nat -> NtoR v2 > NtoR u -> a[v2] = a[N] 
      -> NtoR v ≤ NtoR v2) \}\) as h.
    rename H into Ha1. rename H0 into Ha2. rename H2 into HN1.
    rename H1 into H1'. rename H3 into H3'.
    assert(Function (h)) as Functionh.
    { split; intros. apply poisre. 
      appA2H H. destruct H1 as [x0[y0[H1[H2[H3[H4[H5]]]]]]]. appA2H H0.
      destruct H7 as [x1[y1[H7[H8[H9[H10[H11]]]]]]].
      subst. apply MKT49b in H, H0. destruct H. destruct H0 as [H0].
      apply MKT55 in H1, H7; auto. destruct H1, H7.
      subst. apply NtoR1'; auto. }
    assert(dom(h) = Nat) as domh.
    { apply AxiomI; split; intros.
      - apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [_[]]; auto.
      - New H. appA2G.
        assert(∃v, v ∈ Nat /\ NtoR v > NtoR z /\ a [v] = a [N] 
          /\ (∀ v2, v2 ∈ Nat -> NtoR v2 > NtoR z -> a [v2] = a [N] 
          -> NtoR v ≤ NtoR v2)).
        { pose proof Nat_hasMin.
          set(\{ λ u, u ∈ Nat /\ NtoR u > NtoR z /\ a [u] = a [N]\}) as M.
          assert(M ⊂ Nat).
          { unfold Included; intros. appA2H H2. destruct H3; auto. }
          assert(M ≠ Φ).
          { apply H3' in H0. destruct H0, H0. assert(x ∈ M). { appA2G. }
          apply NEexE; eauto. }
          apply H1 in H3; auto. destruct H3 as [m], H3. appA2H H3. 
          destruct H5, H6. exists m. repeat split; auto. intro m2; intros. 
          apply H4; auto. appA2G. }
        destruct H1 as [v]. exists v. appA2G. apply MKT49a; auto.
        unfold Ensemble; eauto. destruct H1. unfold Ensemble; eauto. }
    assert(ran(h) ⊂ Nat) as ranh.
    { unfold Included; intros. appA2H H. destruct H0. appA2H H0.
      destruct H1 as [x1[z1[H1[H2[H3[H4[H5]]]]]]]. apply MKT49b in H0 as [].
      apply MKT55 in H1 as []; auto. subst; auto. }
    assert(Function (h) /\ dom(h) = Nat /\ ran(h) ⊂ Nat) as h_is_Function.
    {  pose proof Functionh. pose proof domh. pose proof ranh.
       split; auto. }
   (* g *)
    set (∩(\{ λ f, Function f /\ dom(f) = Nat /\ ran(f) ⊂ Nat /\ f[One] = N 
      /\ (∀ n, n ∈ Nat -> f[(n + One)%Nat] = h[(f[n])]) \})) as g.
    assert(∃ u, Ensemble u /\ \{ λ f, 
      Function f /\ dom(f) = Nat /\ ran(f) ⊂ Nat /\ f[One] = N  
      /\ (∀ n, n ∈ Nat -> f[(n + One)%Nat] = h[(f[n])]) \} = [u]) as g_uni.
    { destruct h_is_Function as [H[H0]]. 
      assert ( exists ! u, Function u /\ dom(u) = Nat
        /\ ran(u) ⊂ Nat /\ u[One] = N /\ (∀ n, n ∈ Nat 
        -> u[(n + One)%Nat] = h[(u[n])])) as [u[[H2[H3[H4[]]]]]].
      { New H. pose proof a0b0_in_RC. pose proof Ensemble_RC_RC.
        apply (RecursionNex' (N) Nat h) in H2; auto. }
      exists u. assert (Ensemble u).
      { apply MKT75; auto. rewrite H3. apply EnNat. }
      split; auto. apply AxiomI; split; intros.
      apply AxiomII in H9 as [H9[H10[H11[H12[]]]]].
      apply MKT41; auto. symmetry. apply H7; auto. 
      apply MKT41 in H9; auto. rewrite H9.
      apply AxiomII; repeat split; auto; destruct H2; auto. }
    assert(Function g /\ dom(g) = Nat /\ ran(g) ⊂ Nat /\ g[One] = N
      /\ (∀ n, n ∈ Nat -> g[(n + One)%Nat] = h[(g[n])])) as g_is_Function.
    { destruct g_uni as [u[]]. unfold g. rewrite H0. New H.
      apply MKT44 in H1 as []. rewrite H1.
      assert (u ∈ [u]). { apply MKT41; auto. }
      rewrite <- H0 in H3. apply AxiomII in H3 as [_[H3[H4[H5[]]]]]; auto. }
    exists g. split.
    + red. destruct g_is_Function. split; auto. intros. destruct H0, H4, H5.
      New H1. New H2. rewrite H0 in H7, H8. 
      set (P := fun x2 => NtoR x1 < NtoR x2 -> NtoR g [x1] < NtoR g [x2]).
      assert (∀ n, n ∈ Nat -> P n).
      { apply Mathematical_Induction_Nat; unfold P; intros.
        * New H7. apply FAT24 in H10; auto. apply NtoR8 in H10; auto.
          apply (@legRf (NtoR One) (NtoR x1)) in H10; auto; contradiction. 
        * New H9. apply H6 in H12. rewrite H12. New H9. rewrite <- H0 in H13.
          apply Property_Value, Property_ran in H13; auto. New H4. 
          unfold Included in H14. New H13. apply H14 in H15; auto. 
          rewrite <- domh in H15. apply Property_Value in H15; auto.
          appA2H H15. destruct H16 as [gk[hgk[H16[H17[H18[H19[H20]]]]]]].
          apply MKT49b in H15 as []; auto. apply MKT55 in H16 as []; auto.
          destruct (@FAT167 (NtoR x1) (NtoR k)) as [H24 | [H24 | H24]]; auto.
          -- apply NtoR1' in H24; auto. rewrite H24, H16. rewrite H16 in H23.
             rewrite H23; auto.
          -- apply NtoR3', FAT25a, NtoR8, @legRf in H24; auto; contradiction.
          -- apply H10 in H24. rewrite <- H23 in H19, H18. 
             rewrite <- H16 in H19, H17. 
             apply Property_Value, Property_ran in H1; auto. red in H4. 
             apply H4 in H1; auto. apply (@FAT171 (NtoR g [x1]) 
             (NtoR g [k]) (NtoR h [g [k]])); auto. }
      unfold P in H9. apply H9; auto.
    + destruct g_is_Function, H0, H1, H2. repeat split; auto. 
      apply Mathematical_Induction_Nat.
      * rewrite H2. assert(One ∈ Nat); auto. red in IsSeq_b. 
        destruct IsSeq_b, H6. rewrite <- H6 in H4.
        apply Property_Value in H4; auto. appA2H H4.
        destruct H8 as [x1[y1[H8[H9]]]]. apply MKT49b in H4 as []; auto. 
        apply MKT55 in H8 as []; auto. rewrite H12, H10; auto.
      * intros. New H4. apply H3 in H6. rewrite H6.
        New H4. rewrite <- H0 in H7. 
        apply Property_Value, Property_ran in H7; auto. red in H1.
        apply H1 in H7. rewrite <- domh in H7. 
        apply Property_Value in H7; auto. appA2H H7.
        destruct H8 as [x[y[H8[H9[H10[H11[H12]]]]]]].
        apply MKT49b in H7 as []; auto. apply MKT55 in H8 as []; auto.
        rewrite H15, H12. assert((k + One)%Nat ∈ Nat); auto.
        red in IsSeq_b. destruct IsSeq_b, H18. rewrite <- H18 in H16.
        apply Property_Value in H16; auto. appA2H H16.
        destruct H20 as [x1[y1[H20[H21]]]]. apply MKT49b in H16 as []; auto. 
        apply MKT55 in H20 as []; auto. rewrite H24; auto.
  - red. exists a[N]. red. split; auto. split. apply anRC; auto.
    intros. exists One. split; auto. intros. New IsSeq_b. destruct H8, H9.
    rewrite <- H9 in H6. apply Property_Value in H6; auto. appA2H H6.
    apply MKT49b in H6 as []; auto. destruct H11 as [x[y[H11[H13]]]].
    apply MKT55 in H11 as []; auto. subst. rewrite H14. 
    rewrite xminx, Zabs; auto. 
Qed.

Fact NotFinite_is_No_Empty : ∀ S, ~ Finite S -> ∃ x, x ∈ S.
Proof.
  intros. Absurd. elim H. clear H.
  assert(S = Φ). { Absurd. elim H0. apply NEexE in H. auto. }
  rewrite H. pose proof Finite_single1. 
  assert(Φ ⊂ [1]). { red. intros. apply MKT16 in H2; contradiction. }
  apply (@finsub [1] Φ) in H1; auto.
Qed.

Lemma SL3 : ∀ a, BoundedSeq a -> ~ Finite ran(a) 
  -> ∀ e, e ∈ RC -> AccumulationPoint e ran(a) 
  -> ∀ n k, n ∈ Nat -> k ∈ RC -> k > 0 
  -> ∃ m, m ∈ Nat /\ NtoR n < NtoR m 
     /\ a[m] ∈ ］ (e - k) , (k + e) ［ /\ a[m] ∈ ran( a) /\ a[m] ∈ RC.
Proof.
  intro a. intro Ha1. intro Ha2.
  intro e. intro H. intro H0. intros. apply Cor_acc in H0. red in H0. New H2. 
  apply H0 in H4; auto. red in Ha1. New Ha1. destruct H5. red in H5. 
  destruct H5, H7. Absurd. elim H4. clear H4 H6.
  assert (Finite \{ λ z, ∃ m, m ∈ Nat /\ NtoR m ≤ NtoR n /\ z = a[m] \}).
  { set(A := \{ λ m, m ∈ Nat /\ NtoR m ≤ NtoR n \}).
    set(\{\ λ u v, u ∈ A /\ v = a [u] \}\) as h.
    assert(Ensemble A).
    { apply (MKT33 Nat A); auto. unfold Included; intros. appA2H H4. 
      destruct H6; auto. }
    assert(Finite A).
    { apply Fin_FinNat; auto. }
    assert(Function h).
    { intros. split; intros. apply poisre.
      apply AxiomII' in H10 as [H10[]], H11 as [H11[]]. subst; auto. }
    assert(dom(h) = A).
    { apply AxiomI; split; intros.
      - appA2H H11. destruct H12. apply AxiomII' in H12 as [H12[]]; auto.
      - appA2H H11. destruct H12. appA2G. exists a[z]. 
        assert(Ensemble ([z, a [z]])).
        { apply MKT49a; auto. unfold Ensemble. exists RC. destruct Ha1. 
          apply anRC; auto. }
        appA2G. exists z. exists a[z]. repeat split; auto. appA2G. }
    assert(Ensemble h).
    { apply MKT75; auto. rewrite H11; auto. }
    New H6. rename H13 into FA. rewrite <- H11 in H6. 
    apply MKT160_Cor in H6; auto. apply (@finsub ran(h)
      \{ λ z, ∃m : Class,m ∈ Nat /\ NtoR m ≤ NtoR n /\ z = a [m] \}); auto.
    unfold Included; intros. appA2H H13. destruct H14 as [m[H14[]]]. subst.
    assert(m ∈ dom(h)). { rewrite H11. appA2G. }
    New H16. apply Property_Value in H17; auto. New H17. rename H18 into Hh.
    appA2H H17. apply MKT49b in H17 as []. destruct H18 as [m1[hm1[H18[]]]].
    apply MKT55 in H18 as []; auto. subst. rewrite <- H21. 
    apply Property_ran in Hh; auto. }
    apply (@finsub 
      \{ λ z, ∃m : Class,m ∈ Nat /\ NtoR m ≤ NtoR n /\ z = a [m] \} 
      \{ λ z, z ∈ ］ (e - k), (k + e) ［ /\ z ∈ ran( a) /\ z ∈ RC \}); auto.
    unfold Included; intros. appA2H H6. destruct H10, H11.
    appA2G. New H11. appA2H H11. destruct H14 as [x]. New H14. 
    apply Property_dom in H15. New H15. apply Property_Value in H16; auto.
    red in H5. destruct H5 as [_ H5]. apply (H5 x z a[x]) in H16; auto.
    exists x. New H15. rewrite H7 in H15. repeat split; auto. Absurd.
    elim H9. exists x. apply NotleR in H18; auto. rewrite <- H16.
    repeat split; auto.
Qed.

Lemma He2 : ∀ a, BoundedSeq a -> ~ Finite ran(a) -> 
  ∀ e, AccumulationPoint e ran(a) -> e ∈ RC.
Proof.
  intros; apply (AccumulationPoint_Core ran(a) e); auto.
Qed.


Lemma SCT_InFinite_Lemma : ∀ a, BoundedSeq a -> ~ Finite ran(a) -> 
  ∀ e, AccumulationPoint e ran(a) -> ∃ b, SubSeq a b /\ Conv_Seq b.
Proof.
  intro a. intro Ha1. intro Ha2. intro e. intro He1. 
  New He1. apply He2 in H; auto.
  pose proof SL3 a Ha1 Ha2 e H He1.
  assert((One + One)%Nat ∈ Nat); auto. assert(1 ∈ RC); auto. 
  apply (H0 One 1) in H2; auto. destruct H2 as [N[H2[H3[H4[H5]]]]].
  (* h *)
  set (\{\ λ u v, u ∈ Nat /\ v ∈ Nat /\ NtoR v > NtoR u 
  /\ a[v] ∈ ］ (e - 1/(NtoR u)) , (1/(NtoR u) + e)［ 
  /\ (∀ v2, v2 ∈ Nat -> NtoR v2 > NtoR u 
    -> a[v2] ∈ ］ (e - 1/(NtoR u)) , (1/(NtoR u) + e)［ 
    -> NtoR v ≤ NtoR v2) \}\) as h. 
  assert(Function (h)) as Functionh.
  { split; intros. apply poisre. apply AxiomII' in H7, H8.
    destruct H7, H9, H10, H11, H12, H8, H14, H15, H16, H17. New H10. New H15.
    apply (H18 y) in H19; auto. apply H13 in H20; auto. 
    apply Leq_P2, NtoR1' in H20; auto. }
  assert(dom(h) = Nat) as domh.
  { apply AxiomI; split; intros.
    - appA2H H7. destruct H8. apply AxiomII' in H8. destruct H8 as [_[]]; auto.
    - New H7. appA2G. 
      assert(∃v, v ∈ Nat /\ NtoR v > NtoR z 
      /\ a [v] ∈ ］ (e - 1 / NtoR z), (1 / NtoR z + e) ［
      /\ (∀ v2, v2 ∈ Nat -> NtoR v2 > NtoR z 
      -> a [v2] ∈ ］ (e - 1 / NtoR z), (1 / NtoR z + e) ［
      -> NtoR v ≤ NtoR v2)).
      { pose proof Nat_hasMin. 
        set(\{ λ u, u ∈ Nat /\ NtoR u > NtoR z 
        /\ a [u] ∈ ］ (e - 1 / NtoR z), (1 / NtoR z + e) ［\}) as M.
        assert(M ⊂ Nat).
        { unfold Included; intros. appA2H H10. destruct H11; auto. }
        assert(M ≠ Φ).
        { apply (H0 z (1/(NtoR z))) in H8; auto. 
          destruct H8, H8, H11, H12, H13. assert(x ∈ M). { appA2G. }
          apply NEexE; eauto. apply FAT24, NtoR8 in H8; auto.
          assert(1 ≤ NtoR z); auto. assert(0 < 1); auto. 
          assert(0 ≤ 1 /\ 1 < NtoR z \/ 0 < 1 /\ 1 ≤ NtoR z).
          { right; split; auto. }
          apply (FAT172 0 1 (NtoR z)) in H13; auto. apply divRC1; auto.  }
          apply H9 in H11; auto. destruct H11 as [m], H11. appA2H H11. 
          destruct H13, H14. exists m. repeat split; auto. intro m2; intros. 
          apply H12; auto. appA2G. }
        destruct H9, H9. exists x. appA2G. exists z. exists x. split; auto. }
  assert(ran(h) ⊂ Nat) as ranh.
  { unfold Included; intros. appA2H H7. destruct H8. 
    apply AxiomII' in H8 as [_[_[]]]; auto. }
  assert(Function (h) /\ dom(h) = Nat /\ ran(h) ⊂ Nat) as h_is_Function.
  {  split; auto. }
  (* g *)
  set (∩(\{ λ f, Function f /\ dom(f) = Nat /\ ran(f) ⊂ Nat 
    /\ f[One] = h[(One + One)%Nat] 
    /\ (∀ n, n ∈ Nat -> f[(n + One)%Nat] = h[(f[n])]) \})) as g.
  assert(∃ u, Ensemble u /\ \{ λ f, 
    Function f /\ dom(f) = Nat /\ ran(f) ⊂ Nat /\ f[One] = h[(One + One)%Nat]  
    /\ (∀ n, n ∈ Nat -> f[(n + One)%Nat] = h[(f[n])]) \} = [u]) as g_uni.
  { destruct h_is_Function as [H7[H8]]. 
    assert ( exists ! u, Function u /\ dom(u) = Nat
      /\ ran(u) ⊂ Nat /\ u[One] = h[(One + One)%Nat] /\ (∀ n, n ∈ Nat 
      -> u[(n + One)%Nat] = h[(u[n])])) as [u[[H10[H11[H12[]]]]]].
    { New H. pose proof a0b0_in_RC. pose proof Ensemble_RC_RC.
      assert(h[(One + One)%Nat] ∈ Nat) as HOne.
      { rewrite <- domh in H1. apply Property_Value in H1; auto.
        apply AxiomII' in H1 as [_[_[]]]; auto. }
      apply (RecursionNex' (h[(One + One)%Nat]) Nat h) in HOne; auto. }
    exists u. assert (Ensemble u).
    { apply MKT75; auto. rewrite H11. apply EnNat. }
    split; auto. apply AxiomI; split; intros.
    apply AxiomII in H17 as [H17[H18[H19[H20[]]]]].
    apply MKT41; auto. symmetry. apply H15; auto. 
    apply MKT41 in H17; auto. rewrite H17.
    apply AxiomII; repeat split; auto; destruct H10; auto. }
  assert(Function g /\ dom(g) = Nat /\ ran(g) ⊂ Nat 
    /\ g[One] = h[(One + One)%Nat]
    /\ (∀ n, n ∈ Nat -> g[(n + One)%Nat] = h[(g[n])])) as g_is_Function.
  { destruct g_uni as [u[]]. unfold g. rewrite H8. New H7.
    apply MKT44 in H9 as []. rewrite H9.
    assert (u ∈ [u]). { apply MKT41; auto. }
    rewrite <- H8 in H11. apply AxiomII in H11 as [_[H11[H12[H13[]]]]]; auto. }
  assert(StrictMonoInc_Fun g) as StrictMonoInc_Fun_g.
  { red. destruct g_is_Function. split; auto. intros. destruct H8, H12, H13.
      New H9. New H10. rewrite H8 in H15, H16. 
      set (P := fun x2 => NtoR x1 < NtoR x2 -> NtoR g [x1] < NtoR g [x2]).
      assert (∀ n, n ∈ Nat -> P n).
      { apply Mathematical_Induction_Nat; unfold P; intros.
        * New H15. apply FAT24 in H18; auto. apply NtoR8 in H18; auto.
          apply (@legRf (NtoR One) (NtoR x1)) in H18; auto; contradiction. 
        * New H17. apply H14 in H20. rewrite H20. New H17. rewrite <- H8 in H21.
          apply Property_Value, Property_ran in H21; auto. New H12. 
          unfold Included in H22. New H21. apply H22 in H23; auto. 
          rewrite <- domh in H23. apply Property_Value in H23; auto.
          appA2H H23. destruct H24 as [gk[hgk[H24[H25[H26[H27[H28]]]]]]].
          apply MKT49b in H23 as []; auto. apply MKT55 in H24 as []; auto.
          destruct (@FAT167 (NtoR x1) (NtoR k)) as [H32 | [H32 | H32]]; auto.
          -- apply NtoR1' in H32; auto. rewrite H32, H24. rewrite H24 in H31.
             rewrite H31; auto.
          -- apply NtoR3', FAT25a, NtoR8, @legRf in H32; auto; contradiction.
          -- apply H18 in H32. rewrite <- H31 in H27, H26. 
             rewrite <- H24 in H27, H25. 
             apply Property_Value, Property_ran in H9; auto. red in H12. 
             apply H12 in H9; auto. apply (@FAT171 (NtoR g [x1]) 
             (NtoR g [k]) (NtoR h [g [k]])); auto. }
      unfold P in H17. apply H17; auto. }
  assert(∀n, n ∈ Nat -> NtoR h[n] > NtoR n) as Hh1.
  { set (P := fun n => NtoR h [n] > NtoR n).
    assert (∀ n, n ∈ Nat -> P n).
    { apply Mathematical_Induction_Nat.
      - unfold P. assert(One ∈ Nat); auto. rewrite <- domh in H7.
        apply Property_Value, AxiomII' in H7; auto. 
        destruct H7 as [_[_[_[]]]]; auto.
      - unfold P. intros. assert((k + One)%Nat ∈ Nat); auto.
        rewrite <- domh in H9. apply Property_Value, AxiomII' in H9; auto. 
        destruct H9 as [_[_[_[]]]]; auto. }
    unfold P in H7; auto. }
  assert(∀n, n ∈ Nat -> NtoR g[n] > NtoR n + 1) as Hg1.
  { set (P := fun n => NtoR g [n] > NtoR n + 1).
    assert (∀ n, n ∈ Nat -> P n).
    { apply Mathematical_Induction_Nat.
      - unfold P. destruct g_is_Function, H8, H9, H10. rewrite H10.
        assert((One + One)%Nat ∈ Nat); auto. apply Hh1 in H12. 
        assert(NtoR (One + One)%Nat = NtoR One + 1).
        { rewrite <- NtoR2; auto. } rewrite <- H13; auto.
      - unfold P. intros. assert((k + One)%Nat ∈ Nat); auto.
        destruct StrictMonoInc_Fun_g. rewrite <- NtoR2; auto.
        assert(NtoR k + NtoR One + 1 = NtoR k + 1 + 1); auto.
        rewrite H12. clear H12. destruct g_is_Function, H13, H14, H15.
        New H7. New H9. rename H17 into H7'. rename H18 into H9'.
        rewrite <- H13 in H9, H7. New H7. 
        assert(NtoR k < NtoR (k + One)%Nat). { rewrite <- NtoR2; auto. }
        apply (H11 k (k + One)%Nat) in H17; auto.
        assert(g[k] ∈ Nat). { apply Property_Value, Property_ran in H7; auto. }
        assert(NtoR g [k] ∈ RC). { apply NtoRRC; auto. }
        assert(NtoR g [(k + One)%Nat] ∈ RC). 
        { apply NtoRRC. apply Property_Value, Property_ran in H9; auto. }
        assert(NtoR g [k] ≥ NtoR k + 1 + 1).
        { assert(1 = NtoR One); auto. rewrite H22, NtoR2, NtoR2; auto. 
          apply Nat_P4; auto. rewrite <- NtoR2, <- NtoR2, <- NtoR2, <- H22
          ; auto. apply (FAT188c2 (NtoR k + 1) (NtoR g [k]) 1); auto. }
        apply (FAT172 (NtoR k + 1 + 1) (NtoR g [k]) 
        (NtoR g [(k + One)%Nat])); auto. }
    unfold P in H7; auto. }
  (* b *)
  set (\{\ λ u v, u ∈ Nat /\ v = a[g[u]] \}\) as b. 
  assert(IsSeq a) as IsSeq_a. { red in Ha1. destruct Ha1; auto. }
  assert(IsSeq b) as IsSeq_b.
  { red. split.
    + red. split. apply poisre. intros. appA2H H7. appA2H H8.
      apply MKT49b in H7, H8. destruct H7, H8.
      destruct H9 as [x1[y1[H9[H13]]]]. destruct H10 as [x2[y2[H10[H15]]]].
      apply MKT55 in H9, H10; auto. destruct H9, H10. subst; auto.
    + split.
      * apply AxiomI; intros; split; intros; auto.
        ++ appA2H H7. destruct H8 as [y]. appA2H H8. 
           destruct H9 as [z1[y1[H9[H10]]]]. apply MKT49b in H8 as [].
           apply MKT55 in H9 as []; auto. subst; auto.
        ++ appA2G. exists(a [g[z]]). appA2G. apply MKT49a. 
           unfold Ensemble; eauto. assert(g[z] ∈ Nat).
           { destruct g_is_Function, H9, H10. rewrite <- H9 in H7.
             apply Property_Value, Property_ran in H7; auto. } 
           pose proof anRC a (g[z]) IsSeq_a H8. unfold Ensemble; eauto.
      * unfold Included; intros. appA2H H7. destruct H8. appA2H H8.
        destruct H9 as [x1[z1[H9[H10]]]].  apply MKT49b in H8 as [].
        apply MKT55 in H9 as []; auto. subst. apply anRC; auto.
        destruct g_is_Function, H11, H12, H13. rewrite <- H11 in H10.
        apply Property_Value, Property_ran in H10; auto. }
  (* exists b. *)
  exists b. split. 
  - red. split; auto. split; auto. exists g. split; auto.
    destruct g_is_Function, H8, H9, H10. split; auto. split; auto. 
    apply Mathematical_Induction_Nat.
    * assert(One ∈ Nat); auto. red in IsSeq_b. 
      destruct IsSeq_b, H14. rewrite <- H14 in H12.
      apply Property_Value in H12; auto. appA2H H12.
      destruct H16 as [x1[y1[H16[H17]]]]. apply MKT49b in H12 as []; auto. 
      apply MKT55 in H16 as []; auto. subst. rewrite H18; auto.
    * intros. New H12. apply H11 in H14. rewrite H14. New H12. rewrite <- H8 
      in H15. apply Property_Value, Property_ran in H15; auto. red in H9.
      apply H9 in H15. rewrite <- domh in H15. apply Property_Value in H15; 
      auto. appA2H H15. destruct H16 as [x[y[H16[H17[H18[H19[H20]]]]]]].
      apply MKT49b in H15 as []; auto. apply MKT55 in H16 as []; auto.
      rewrite H23. assert((k + One)%Nat ∈ Nat); auto. red in IsSeq_b. destruct 
      IsSeq_b, H26. rewrite <- H26 in H24. apply Property_Value in H24; auto. 
      appA2H H24. destruct H28 as [x1[y1[H29[H30]]]]. apply MKT49b in H24 as []; 
      auto. apply MKT55 in H29 as []; auto. rewrite H32; auto. subst. 
      rewrite H28, H14; auto.
  - red. exists e. red. split; auto. split; auto. intros. assert(1/ε ∈ RC); 
    auto. New H9. apply ArchimedeanLemma1 in H10. destruct H10 as [N0[]]. 
    exists N0. split; auto. intros. destruct IsSeq_b as [H14[]]. New H12. 
    rewrite <- H15 in H17. New H17. apply Property_Value in H18; auto. New H18. 
    appA2H H19. destruct H20 as [n1[bn1[H20[]]]]. apply MKT49b in H19 as []; 
    auto. apply MKT55 in H20 as []; auto. subst. rewrite H22. rewrite H22 in 
    H23. destruct g_is_Function, H24, H25. rewrite <- H24 in H21. destruct H26.
    assert((n1 - One)%Nat ∈ Nat) as Hn1. 
    { New H10. apply (@FAT24 N0) in H28. apply NtoR3' in H13; auto. 
      assert((One ≤ N0)%Nat /\ (N0 < n1)%Nat \/ (One < N0)%Nat /\ 
      (N0 ≤ n1)%Nat). { left; split; auto. } 
      apply(@FAT16 One N0 n1) in H29; auto. }
    New Hn1. apply H27 in H28.
    assert((n1 - One + One)%Nat = n1). 
    { rewrite (FAT6 (n1 - One)%Nat One); auto. apply MinNEx; auto. 
      New H10. apply (@FAT24 N0) in H29. apply NtoR3' in H13; auto. 
      assert((One ≤ N0)%Nat /\ (N0 < n1)%Nat \/ (One < N0)%Nat /\ 
      (N0 ≤ n1)%Nat). { left; split; auto. } 
      apply(@FAT16 One N0 n1) in H30; auto.  }
    rewrite H29 in H28. rewrite H28.
    assert(g [(n1 - One)%Nat] ∈ dom(h)). { rewrite domh. rewrite <- H24 in Hn1. 
    apply Property_Value, Property_ran in Hn1; auto. }
    apply Property_Value in H30; auto. apply AxiomII' in H30.
    destruct H30, H31, H32, H33, H34. appA2H H34. destruct H36, H37, H38, H39.
    set(a [h [g [(n1 - One)%Nat]]]) as x0.
    pose proof Hg1. New Hn1. apply H41 in H42.
    assert(NtoR (n1 - One)%Nat + 1 = NtoR n1).
    { assert(1 = NtoR One); auto. rewrite H43, NtoR2, H29; auto. } 
    rewrite H43 in H42.
    clear H43. apply (@FAT171 (1 / ε) (NtoR N0) (NtoR n1)) in H11; auto.
    assert(1 > 0); auto. apply (divRC1 1 ε) in H43; auto.
    apply divRC2 in H11; auto. rewrite divRC7 in H11; auto.
    assert(a [g [n1]] ∈ RC). { apply anRC; auto. 
    apply Property_Value, Property_ran in H21; auto. }
    apply (@FAT171 (| x0 - e |) (1 / NtoR n1) ε); auto.
    apply Ab1; auto. split. 
    + set(NtoR g [(n1 - One)%Nat]) as y0. set( NtoR n1) as z0.
      assert(e - 1 / y0 < x0); auto. assert(y0 > z0); auto.
      assert(x0 ∈ RC). apply anRC; auto. 
      assert(y0 ∈ RC). apply NtoRRC; auto.
      assert(z0 ∈ RC). apply NtoRRC; auto.
      assert((1 / y0) ∈ RC). { apply divRc3; auto. Absurd. apply NNPP' in H50;
      rewrite H50 in H46; apply ng0 in H12; apply lgRf in H12; auto. }
      assert(- (1 / y0) ∈ RC); auto. 
      assert(z0 > 0). apply ng0; auto. assert(y0 > 0). apply ng0; auto.
      assert(1 / z0 > 1 / y0). apply (divRC2 y0 z0); auto. 
      assert(- (1 / y0) > - (1 / z0)). 
      { apply (FAT203c (1 / z0) (1 / y0) (- (1))) in H54; auto. 
        rewrite FAT195b in H54; auto. rewrite FAT195b in H54; auto. }
      assert(- (1 / y0) < x0 - e). { apply (FAT188c1 (-(1 / y0)) (x0 - e) e); auto.
        rewrite MincEx1, FAT175; auto. }
      apply (@FAT171 (- (1 / z0)) (- (1 / y0)) (x0 - e)); auto.
    + set(NtoR g [(n1 - One)%Nat]) as y0. set( NtoR n1) as z0.
      assert(x0 < 1 / y0 + e); auto. assert(y0 > z0); auto.
      assert(x0 ∈ RC). apply anRC; auto. 
      assert(y0 ∈ RC). apply NtoRRC; auto.
      assert(z0 ∈ RC). apply NtoRRC; auto.
      assert((1 / y0) ∈ RC). { apply divRc3; auto. Absurd. apply NNPP' in H50;
      rewrite H50 in H46; apply ng0 in H12; apply lgRf in H12; auto. }
      assert(z0 > 0). apply ng0; auto. assert(y0 > 0). apply ng0; auto.
      assert(1 / z0 > 1 / y0). apply (divRC2 y0 z0); auto. 
      assert(x0 - e < 1 / y0). { apply (FAT188c1 (x0 - e) (1 / y0) e); auto.
        rewrite MincEx1; auto. }
      apply (@FAT171 (x0 - e) (1 / y0) (1 / z0)); auto. 
Qed.

Corollary Ab1' : ∀ x y, x ∈ RC -> y ∈ RC -> |y| ≤ x <-> -x ≤ y /\ y ≤ x.
Proof.
  split.
  - intros. red in H1. destruct H1.
    + apply Ab1 in H1; auto. destruct H1. split. left; auto. left; auto.
    + subst. TF(y ≤ 0).
      * New H1. apply AbNRC0 in H1; auto. rewrite H1, FAT177; auto. split.
        right; auto. destruct H2. left; auto. subst; right; auto.
      * apply NotleR in H1; auto. New H1. apply AbPRC in H1; auto.
        rewrite H1; auto. split. left; auto. right; auto.
  - intros. destruct H1. TF(y < 0).
    + rewrite AbNRC; auto.
    + apply Notle in H3; auto. rewrite AbPRC0; auto.
Qed.

Lemma SCT_AccumulationPoint_Lemma : ∀ a, BoundedSeq a -> ~ Finite (ran(a)) -> 
  (∃ e, AccumulationPoint e ran(a)).
Proof.
  intro a. intro H. intro H0. red in H. destruct H, H1, H1. 
  assert( ~ ran(a) = [0]) as Ha.
  { Absurd. elim H0. apply NNPP' in H3. rewrite H3. apply finsin; auto. }
  assert(∃ n, n ∈ Nat /\ ~ a [n] = 0).
  { New H. destruct H3, H4. rewrite<- H4. Absurd.
    assert(∀ n, n ∈ dom( a) -> a [n] = 0).
    { intros. Absurd. elim H6. exists n. split; auto. }
    set(\{ λ z, exists n, z = a[n] /\ n ∈ Nat \}) as A.
    assert(ran(a) = A).
    { apply AxiomI; split; intros.
      - appA2G. New H8. appA2H H9. destruct H10. New H10.
        apply Property_dom in H11. New H11. apply Property_Value in H12; auto.
        destruct H3. apply (H13 x0 z a[x0]) in H10; auto. exists x0.
        rewrite H4 in H11. split; auto.
      - appA2H H8. destruct H9 as [x0[]]. subst. New H10. rewrite <- H4 in H10.
        New H10. apply Property_Value, Property_ran in H11; auto. }
    assert(A = [0]).
    { apply AxiomI; split; intros.
      - appA2G; intros. appA2H H9. destruct H11, H11. rewrite <- H4 in H12.
        apply H7 in H12. subst; auto.
      - appA2H H9. assert(0 ∈ μ); auto. apply H10 in H11. subst. appA2G. 
        rewrite H4 in H7. assert(One ∈ Nat); auto. apply H7 in H11. 
        exists One. split; auto. }
    rewrite H9 in H8. apply Ha in H8; contradiction. }
  destruct H3 as [n[H3]]. New H3. apply H2 in H5. New H3.
  apply (anRC a) in H6; auto. New H6. apply Ab8 in H7; auto.
  assert(| a [n] | ∈ RC); auto. apply si2' in H7.
  assert(0 ≤ | a [n] | /\ | a [n] | < x \/ 0 < | a [n] | /\ | a [n] | ≤ x). 
  { right. split; auto. }
  apply (FAT172 0 (|a [n]|) x) in H9; auto.
  apply (APT _ (-x) x); auto.
  - red. destruct H, H10. repeat split; auto; intros. appA2H H12. destruct H13.
    New H13. 
    apply Property_dom in H13. New H13. apply Property_Value in H15; auto.
    destruct H. New H15. apply Property_ran in H17. unfold Included in H11.
    apply H11 in H17. apply (H16 x1 x0 a[x1]) in H15; auto. subst. 
    rewrite H10 in H13. apply H2, Ab1' in H13 as []; auto.
  - red. destruct H, H10. repeat split; auto; intros. appA2H H12. destruct H13.
    New H13. 
    apply Property_dom in H13. New H13. apply Property_Value in H15; auto.
    destruct H. New H15. apply Property_ran in H17. unfold Included in H11.
    apply H11 in H17. apply (H16 x1 x0 a[x1]) in H15; auto. subst. 
    rewrite H10 in H13. apply H2, Ab1' in H13 as []; auto.
Qed.

Theorem SCT_InFinite : ∀ a, BoundedSeq a -> ~ Finite (ran(a)) -> 
  (∃ b, SubSeq a b /\ Conv_Seq b).
Proof. 
  intro a. intro H. intro H0. pose proof SCT_AccumulationPoint_Lemma a H H0. destruct H1 as [e].
  pose proof SCT_InFinite_Lemma a H H0 e H1; auto.
Qed.

Theorem Theorem2_10 : ∀ a, BoundedSeq a -> (∃ b, SubSeq a b /\ Conv_Seq b).
Proof.
  intros. TF(Finite ran(a)).
  - apply SCT_Finite; auto.
  - apply (SCT_InFinite a); eauto.
Qed.