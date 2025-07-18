Require Export Fsub.EffectExclusion.Fsub_LetSum_Soundness.

(*** Properties from Wikipedia *)
Lemma meet_commutative : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_meet Q1 Q2) (qua_meet Q2 Q1).
Proof with eauto 4 using subqual_reflexivity.
  intros * Wf1 Wf2 SubQ.
  eapply subqual_meet_intro...
Qed.

Lemma join_commutative : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_join Q1 Q2) (qua_join Q2 Q1).
Proof with eauto 4 using subqual_reflexivity.
  intros * Wf1 Wf2 SubQ.
  eapply subqual_join_elim...
Qed.

Lemma UNl : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_base top) (qua_join Q1 Q2) ->
  subqual E (qua_meet Q1 Q2) (qua_base bot) ->
  subqual E Q2 (qua_negate Q1).
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE WfQ1 WfQ2 S1 S2.
  eapply subqual_transitivity with (Q := (qua_meet Q2 (qua_base top)))...
  eapply subqual_transitivity with (Q := (qua_meet Q2 (qua_join Q1 (qua_negate Q1))))...
  eapply subqual_meet_intro...
  eapply subqual_transitivity.
    eapply subqual_dist...
  eapply subqual_join_elim...
  eapply subqual_transitivity.
    eapply meet_commutative...
  eapply subqual_transitivity.
    eapply S2...
  eapply subqual_bot...
Qed.

Lemma UNr : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_base top) (qua_join Q1 Q2) ->
  subqual E (qua_meet Q1 Q2) (qua_base bot) ->
  subqual E (qua_negate Q1) Q2.
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE WfQ1 WfQ2 S1 S2.
  eapply subqual_transitivity with (Q := (qua_meet (qua_negate Q1) (qua_base top)))...
    eapply subqual_meet_intro...
  eapply subqual_transitivity with (Q := (qua_meet (qua_negate Q1) (qua_join Q1 Q2)))...
    eapply subqual_meet_intro...
  eapply subqual_transitivity.
    eapply subqual_dist...
  eapply subqual_join_elim...
  eapply subqual_transitivity.
    eapply meet_commutative...
  eapply subqual_transitivity.
    eapply subqual_negate_elim...
  eapply subqual_bot...
Qed.

Lemma DNl : forall E Q,
  wf_env E ->
  wf_qua E Q ->
  subqual E Q (qua_negate (qua_negate Q)).
Proof with eauto 4.
  intros * WfE WfQ.
  unshelve epose proof (subqual_negate_elim E Q _ _)...
  unshelve epose proof (subqual_negate_intro E Q _ _)...
  unshelve epose proof (subqual_negate_elim E (qua_negate Q) _ _)...
  unshelve epose proof (subqual_negate_intro E (qua_negate Q) _ _)...

  unshelve epose proof (UNl E (qua_negate Q) Q _ _ _ _ _)...
    eapply subqual_trans; [|eapply join_commutative]...
    eapply subqual_trans; [eapply meet_commutative|]...
Qed.

Lemma DNr : forall E Q,
  wf_env E ->
  wf_qua E Q ->
  subqual E (qua_negate (qua_negate Q)) Q.
Proof with eauto 4.
  intros * WfE WfQ.
  unshelve epose proof (subqual_negate_elim E Q _ _)...
  unshelve epose proof (subqual_negate_intro E Q _ _)...
  unshelve epose proof (subqual_negate_elim E (qua_negate Q) _ _)...
  unshelve epose proof (subqual_negate_intro E (qua_negate Q) _ _)...

  unshelve epose proof (UNr E (qua_negate Q) Q _ _ _ _ _)...
    eapply subqual_transitivity; [|eapply join_commutative]...
    eapply subqual_transitivity; [eapply meet_commutative|]...
Qed.

#[export] Hint Resolve DNl DNr : core.

Lemma A1 : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_base top) (qua_join Q1 (qua_join (qua_negate Q1) Q2)).
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE Wf1 Wf2.
  eapply subqual_transitivity with (Q := (qua_join Q2 (qua_join Q1 (qua_negate Q1))))...
  eapply subqual_join_elim...
    eapply subqual_join_inr...
  eapply subqual_join_elim...
    eapply subqual_join_inl...
Qed.

Lemma A2 : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_meet Q1 (qua_meet (qua_negate Q1) (qua_negate Q2))) (qua_base bot).
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE Wf1 Wf2.
  unshelve epose proof (subqual_negate_elim _ Q1 _ _)...
  eapply subqual_transitivity; [| eapply H]...
  eapply subqual_meet_intro...
    eapply subqual_meet_eliml...
    eapply subqual_meet_elimr...
Qed.

Lemma B1 : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_base top) (qua_join (qua_join Q1 Q2) (qua_meet (qua_negate Q1) (qua_negate Q2))).
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE Wf1 Wf2.
  eapply subqual_transitivity with (Q := (qua_meet (qua_base top) (qua_base top)))...
  unshelve epose proof (A1 E (qua_negate Q1) Q2 _ _ _)...
  unshelve epose proof (A1 E (qua_negate Q2) Q1 _ _ _)...
  eapply subqual_transitivity.
    eapply subqual_meet_intro.
    eapply subqual_meet_eliml; [| auto]. eapply H.
    eapply subqual_meet_elimr; [auto |]. eapply H0.
  eapply subqual_transitivity
    with (Q := (qua_meet (qua_join (qua_join Q1 Q2) (qua_negate Q1)) (qua_join (qua_join Q1 Q2) (qua_negate Q2))))...
    eapply subqual_meet_intro.
      eapply subqual_meet_eliml...
      eapply subqual_join_elim...
      eapply subqual_join_inl...
      eapply subqual_join_elim...
      eapply subqual_meet_elimr...
      eapply subqual_join_elim...
      eapply subqual_join_inl...
      eapply subqual_join_elim...
  (* (Q1 \/ Q2 \/ -Q1) /\ (Q1 \/ Q2 /\ -Q2)*)
  eapply subqual_transitivity.
    eapply subqual_dist_dual...
    eapply subqual_reflexivity...
    econstructor...
Qed.

Lemma C1 : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_meet (qua_join Q1 Q2) (qua_meet (qua_negate Q1) (qua_negate Q2))) (qua_base bot).
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE Wf1 Wf2.
  eapply subqual_transitivity with (Q := (qua_join (qua_base bot) (qua_base bot)))...
  unshelve epose proof (A2 E Q1 Q2 _ _ _) as A2Q1...
  unshelve epose proof (A2 E Q2 Q1 _ _ _) as A2Q2...
  eapply subqual_transitivity.
  2 : {
    eapply subqual_join_elim.
    eapply subqual_join_inl; [exact A2Q1 |]...
    eapply subqual_join_inr; [| exact A2Q2]...
  }
  eapply subqual_transitivity.
    eapply meet_commutative...
  eapply subqual_transitivity.
    eapply subqual_dist...
  eapply subqual_join_elim...
  {
    eapply subqual_transitivity.
    eapply meet_commutative...
    eapply subqual_join_inl...
  }
  {
    eapply subqual_join_inr...
    eapply subqual_transitivity.
    eapply meet_commutative...
    eapply subqual_meet_intro...
    eapply subqual_meet_eliml...
    eapply subqual_meet_elimr...
    eapply meet_commutative...
  }
Qed.

Lemma DMg1 : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_negate (qua_join Q1 Q2)) (qua_meet (qua_negate Q1) (qua_negate Q2)).
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE Wf1 Wf2.
  unshelve epose proof (B1 E Q1 Q2 _ _ _)...
  unshelve epose proof (C1 E Q1 Q2 _ _ _)...
  unshelve epose proof (UNl _ _ _ _ _ _ H H0)...
  unshelve epose proof (UNr _ _ _ _ _ _ H H0)...
Qed.

Lemma B2 : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_meet (qua_meet Q1 Q2) (qua_join (qua_negate Q1) (qua_negate Q2))) (qua_base bot) .
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE Wf1 Wf2.
  eapply subqual_transitivity with (Q := (qua_join (qua_base bot) (qua_base bot)))...
  unshelve epose proof (subqual_dist E 
    (qua_meet Q1 Q2)
    (qua_negate Q1) (qua_negate Q2) _ _ _ _)...
  eapply subqual_transitivity...
  eapply subqual_join_elim;
    eapply subqual_join_inr...
  {
    unshelve epose proof (A2 E Q1 Q2 _ _ _)...
    eapply subqual_transitivity with (Q := qua_meet (qua_meet (qua_negate Q1) Q1) Q2)...
    eapply subqual_meet_intro...
    * eapply subqual_meet_intro...
      eapply subqual_meet_eliml...
    * eapply subqual_meet_eliml...
    * eapply subqual_meet_eliml...
      eapply subqual_transitivity.
      eapply meet_commutative...
      eapply subqual_negate_elim...
  }
  {
    unshelve epose proof (A2 E Q1 Q2 _ _ _)...
    eapply subqual_transitivity with (Q := qua_meet (qua_meet (qua_negate Q2) Q2) Q2)...
    eapply subqual_meet_intro...
    * eapply subqual_meet_intro...
      eapply subqual_meet_eliml...
    * eapply subqual_meet_eliml...
    * eapply subqual_meet_eliml...
      eapply subqual_transitivity.
      eapply meet_commutative...
      eapply subqual_negate_elim...
  }
Qed.


Notation "⊤" := (qua_base top).
Notation "⊥" := (qua_base bot).
Notation "¬* Q" := (qua_negate Q) (at level 70).

Lemma C2 : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_base top) (qua_join (qua_meet Q1 Q2) (qua_join (qua_negate Q1) (qua_negate Q2))).
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE Wf1 Wf2.
  eapply subqual_transitivity with (Q := (qua_meet (qua_base top) (qua_base top)))...
  unshelve epose proof (A1 E Q1 (qua_negate Q2) _ _ _) as A1Q1...
  unshelve epose proof (A1 E Q2 (qua_negate Q1) _ _ _) as A1Q2...
  eapply subqual_transitivity
    with (Q := qua_meet (qua_join (qua_join (qua_negate Q1) (qua_negate Q2)) Q1)
                        (qua_join (qua_join (qua_negate Q1) (qua_negate Q2)) Q2)).
  {
    eapply subqual_meet_intro.
    eapply subqual_meet_eliml...
      eapply subqual_transitivity.
      exact A1Q1...
      eapply subqual_join_elim...
      eapply subqual_join_inr...
      eapply subqual_join_elim...
      eapply subqual_join_inl...
      eapply subqual_join_inl...     
    eapply subqual_meet_elimr...
    eapply subqual_transitivity.
      eapply A1Q2...
      eapply subqual_join_elim...
      eapply subqual_join_inr...
      eapply subqual_join_elim...
      eapply subqual_join_inl...
      eapply subqual_join_inl...
  }

  eapply subqual_transitivity.
    eapply subqual_dist_dual... 
  eapply subqual_transitivity.
    eapply join_commutative...
  eapply subqual_reflexivity...
  econstructor...
Qed.

Lemma DMg2 : forall E Q1 Q2,
  wf_env E ->
  wf_qua E Q1 ->
  wf_qua E Q2 ->
  subqual E (qua_negate (qua_meet Q1 Q2)) (qua_join (qua_negate Q1) (qua_negate Q2)).
Proof with eauto 4 using subqual_reflexivity.
  intros * WfE Wf1 Wf2.
  unshelve epose proof (B2 E Q1 Q2 _ _ _)...
  unshelve epose proof (C2 E Q1 Q2 _ _ _)...
  unshelve epose proof (UNl _ _ _ _ _ _ H0 H)...
  unshelve epose proof (UNr _ _ _ _ _ _ H0 H)...
Qed.
