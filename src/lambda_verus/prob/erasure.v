(** Scheduler-forcing lemmas from clutch's [con_prob_lang/erasure.v],
    made generic in the [conLanguage].  The scheduler class is trivial
    ([λ _ _ _ _, True]) instead of tape-oblivious, so the erasure
    lemmas hold for every scheduler. *)
From clutch.prob Require Import distribution couplings mdp.
From clutch.common Require Import con_language sch_erasable.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

Section erasure.
Context {Λ : conLanguage}.

Local Definition force_first_thread_scheduler `{Hcountable:Countable sch_int_σ} (sch : scheduler (con_lang_mdp Λ) sch_int_σ) (num:nat) (initial: sch_int_σ)
  :=
  Build_scheduler {|
      scheduler_f '(ζ, ρ) :=
        match ζ with
        | None => dret (Some initial, num)
        | Some ζ' => dmap (λ '(ζ', ac), (Some ζ', ac)) (sch (ζ', ρ))
        end
    |}.

 

Local Lemma force_first_thread_scheduler_pexec_lemma `{Hcountable:Countable sch_int_σ} ζ ρ (sch : scheduler (con_lang_mdp Λ) sch_int_σ) num initial n :
  dmap (λ ρ, ρ.2.1) (sch_pexec sch n (ζ, ρ)) =
  dmap (λ ρ, ρ.2.1) (sch_pexec (force_first_thread_scheduler sch num initial) n (Some ζ, ρ)).
Proof.
  revert ζ ρ.
  induction n.
  - intros. rewrite !sch_pexec_O/=. by rewrite !dmap_dret.
  - intros. rewrite !sch_pexec_Sn. rewrite {2}/force_first_thread_scheduler/scheduler_f.
    rewrite /sch_step_or_final /=.
    case_match.
    + rewrite !dret_id_left. naive_solver.
    + rewrite /sch_step /=. destruct sch. simpl.
      rewrite /dmap -!dbind_assoc'.
      apply dbind_ext_right.
      intros [].
      rewrite dret_id_left.
      rewrite -!dbind_assoc'.
      apply dbind_ext_right.
      intros. 
      rewrite !dret_id_left.
      rewrite /dmap in IHn. naive_solver.
Qed.

Local Lemma force_first_thread_scheduler_pexec_lemma' `{Hcountable:Countable sch_int_σ} e1 e es1 σ1 (sch : scheduler (con_lang_mdp Λ) sch_int_σ) num initial n :
  (e::es1)!!num=Some e1 ->
  to_val e = None ->
  to_val e1 = None ->
  dmap (λ ρ, ρ.2.1) (prim_step e1 σ1 ≫= λ '(e', s, l), sch_pexec sch n (initial, (<[num:=e']> (e::es1) ++ l, s))) =
  dmap (λ ρ, ρ.2.1) (sch_pexec (force_first_thread_scheduler sch num initial) (S n) (None, (e::es1, σ1))).
Proof.
  intros H Hv Hv'.
  rewrite /force_first_thread_scheduler sch_pexec_Sn.
  rewrite /sch_step_or_final/=.
  rewrite Hv /sch_step -!dbind_assoc'/= dret_id_left Hv H Hv' /dmap -!dbind_assoc'.
  apply dbind_ext_right.
  intros [[]].
  rewrite !dret_id_left.
  epose proof force_first_thread_scheduler_pexec_lemma as K.
  rewrite /dmap in K.
  erewrite K.
  repeat f_equal.
Qed.

Lemma prim_coupl_step_prim_pexec_sch_erasable `{Hcountable:Countable sch_int_σ} e n es1 σ1 ζ e1 (num:nat) μ (sch : scheduler (con_lang_mdp Λ) sch_int_σ) :
  sch_erasable (λ _ _ _ _, True) μ σ1 ->
  (e::es1)!!num=Some e1 ->
  to_val e = None ->
  to_val e1 = None ->
  Rcoupl
    (dmap (λ ρ, ρ.2.1) (prim_step e1 σ1 ≫= λ '(e', s, l), sch_pexec sch n (ζ, (<[num:=e']> (e::es1) ++ l, s))))
    (dmap (λ ρ, ρ.2.1) (μ ≫= (λ σ2, prim_step e1 σ2 ≫= λ '(e', s, l), sch_pexec sch n (ζ, (<[num:=e']> (e::es1) ++ l, s)))))
    eq.
Proof.
  intros H1 H2 H3 H4.
  erewrite force_first_thread_scheduler_pexec_lemma'; try done.
  eapply Rcoupl_eq_trans.
  - erewrite <-H1; last done.
    apply Rcoupl_eq.
  - rewrite /dmap -!dbind_assoc. eapply Rcoupl_dbind; last apply Rcoupl_eq.
    intros ??->.
    apply Rcoupl_eq_sym.
    unshelve epose proof force_first_thread_scheduler_pexec_lemma' as K; try done.
    rewrite /dmap in K. rewrite K; first apply Rcoupl_eq; done.
Qed. 

 


Local Lemma force_first_thread_scheduler_lemma `{Hcountable:Countable sch_int_σ} ζ ρ (sch : scheduler (con_lang_mdp Λ) sch_int_σ) num initial n :
  sch_exec sch n (ζ, ρ) = sch_exec (force_first_thread_scheduler sch num initial) n (Some ζ, ρ).
Proof.
  revert ζ ρ.
  induction n.
  - intros. by rewrite /sch_exec.
  - intros. rewrite !sch_exec_Sn. rewrite {2}/force_first_thread_scheduler/scheduler_f.
    rewrite /sch_step_or_final /=.
    case_match.
    + rewrite !dret_id_left. naive_solver.
    + rewrite /sch_step /=. destruct sch. simpl.
      rewrite /dmap -!dbind_assoc'.
      apply dbind_ext_right.
      intros [].
      rewrite dret_id_left.
      rewrite -!dbind_assoc'.
      apply dbind_ext_right.
      intros. 
      by rewrite !dret_id_left.
Qed.

Local Lemma force_first_thread_scheduler_lemma' `{Hcountable:Countable sch_int_σ} e1 e es1 σ1 (sch : scheduler (con_lang_mdp Λ) sch_int_σ) num initial n :
  (e::es1)!!num=Some e1 ->
  to_val e = None ->
  to_val e1 = None ->
  (prim_step e1 σ1 ≫= λ '(e', s, l), sch_exec sch n (initial, (<[num:=e']> (e::es1) ++ l, s))) = sch_exec (force_first_thread_scheduler sch num initial) (S n) (None, (e::es1, σ1)).
Proof.
  intros H Hv Hv'.
  rewrite /force_first_thread_scheduler{2}/sch_exec.
  simpl.
  rewrite Hv /sch_step -!dbind_assoc'/= dret_id_left Hv H Hv' /dmap -!dbind_assoc'.
  apply dbind_ext_right.
  intros [[]].
  rewrite !dret_id_left.
  erewrite force_first_thread_scheduler_lemma.
  repeat f_equal.
Qed.


Lemma prim_coupl_step_prim_sch_erasable `{Hcountable:Countable sch_int_σ} e n es1 σ1 ζ e1 (num:nat) μ (sch : scheduler (con_lang_mdp Λ) sch_int_σ) :
  sch_erasable (λ _ _ _ _, True) μ σ1 ->
  (e::es1)!!num=Some e1 ->
  to_val e = None ->
  to_val e1 = None ->
  Rcoupl
    (prim_step e1 σ1 ≫= λ '(e', s, l), sch_exec sch n (ζ, (<[num:=e']> (e::es1) ++ l, s)))
    (μ ≫= (λ σ2, prim_step e1 σ2 ≫= λ '(e', s, l), sch_exec sch n (ζ, (<[num:=e']> (e::es1) ++ l, s))))
    eq.
Proof.
  intros H1 H2 H3 H4.
  apply sch_erasable_sch_erasable_val in H1.
  erewrite force_first_thread_scheduler_lemma'; try done.
  eapply Rcoupl_eq_trans.
  - erewrite <-H1; last done.
    apply Rcoupl_eq.
  - eapply Rcoupl_dbind; last apply Rcoupl_eq.
    intros ??->.
    apply Rcoupl_eq_sym.
    rewrite force_first_thread_scheduler_lemma'; try done.
    apply Rcoupl_eq.
Qed.

End erasure.
