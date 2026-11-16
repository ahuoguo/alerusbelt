(** From probabilistic adequacy to safety of every reachable
    configuration, and hence data-race freedom.

    [lrust_wp_safety] is quantitative and scheduler-based: under every
    mass-1 scheduler the non-stuck mass is at least [1 - ε].  VerusBelt's
    race-freedom argument ([races.v]) instead needs the qualitative
    [safe_from]: every non-value thread of every [thread_step]-reachable
    configuration is reducible.  We bridge the two:

    - [path_sch] is the deterministic scheduler that replays a given
      list of thread indices.  A reachable configuration with a stuck
      thread is reached by [path_sch] with positive probability, and
      stepping the stuck thread then loses that mass; with [ε = 0] this
      contradicts adequacy ([follows_stuck_mass]).
    - The MDP stops as soon as the main thread returns, whereas
      [thread_step] (like Iris's [erased_step]) keeps running the forked
      threads.  So we run [e] wrapped as [e ;; loop]: the wrapped main
      thread never returns, and every [thread_step] path of [e] is
      replayed by the wrapped program ([rtc_thread_step_wrap]).

    [lrust_wp_safe_from]: a WP for [e] (with no error credits) gives
    [safe_from ([e], σ0)], hence, by [safe_from_nonracing], race freedom
    of every reachable configuration. *)
From stdpp Require Import gmap.
From Stdlib Require Import Reals Psatz Classical.
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import distribution mdp.
From clutch.common Require Import con_language con_ectx_language.
From lrust.prob Require Import adequacy.
From lrust.lang Require Import races adequacy proofmode notation.
Set Default Proof Using "Type".

Local Open Scope R.

Local Notation cfg := (list expr * state)%type.

(** * Replaying a path with a deterministic scheduler *)

Definition path_sch : scheduler (con_lang_mdp lrust_lang) (list nat) :=
  {| scheduler_f := λ '(js, _), dret (tail js, default 0%nat (head js)) |}.

Lemma path_sch_mass_1 : sch_mass_1 path_sch.
Proof. intros [??]. simpl. apply dret_mass. Qed.

(** [follows c is c']: the MDP goes from [c] to [c'] with positive
    probability when the threads [js] are scheduled in turn. *)
Fixpoint follows (c : cfg) (js : list nat) (c' : cfg) : Prop :=
  match js with
  | [] => c = c'
  | i :: js => ∃ c1, con_lang_mdp_step lrust_lang i c c1 > 0 ∧ follows c1 js c'
  end.

Lemma follows_app c js1 c1 js2 c2 :
  follows c js1 c1 → follows c1 js2 c2 → follows c (js1 ++ js2) c2.
Proof.
  revert c. induction js1 as [|i js1 IH]; intros c; simpl; [by intros ->|].
  intros (c' & Hs & Hf) Hf2. eexists. split; [done|]. by eapply IH.
Qed.

Lemma follows_pexec c js rest c' :
  follows c js c' →
  sch_pexec path_sch (length js) (js ++ rest, c) (rest, c') > 0.
Proof.
  revert c. induction js as [|i js IH]; intros c Hf; simpl in *.
  - subst. rewrite sch_pexec_O dret_1_1 //; lra.
  - destruct Hf as (c1 & Hs & Hf).
    rewrite sch_pexec_Sn. apply dbind_pos. exists (js ++ rest, c1). split; [by apply IH|].
    rewrite sch_step_or_final_not_final.
    + rewrite /sch_step. apply dbind_pos. exists (js ++ rest, i). split.
      * apply dmap_pos. exists c1. split; [done|]. done.
      * simpl. rewrite dret_1_1 //; lra.
    + intros Hfin. pose proof (to_final_is_final (δ:=con_lang_mdp lrust_lang) c Hfin i c1) as H0.
      simpl in H0. lra.
Qed.

Lemma not_final_main (t : list expr) σ :
  ¬ is_final ((t, σ) : mdpstate (con_lang_mdp lrust_lang)) →
  mbind to_val (t !! 0%nat) = None.
Proof.
  rewrite /is_final /= /con_lang_mdp_to_final /=.
  destruct (t !! 0%nat) as [e|]; simpl; [|done].
  destruct (to_val e); [|done]. intros H. by destruct H.
Qed.

(** Stepping a stuck thread of a non-final configuration loses all mass. *)
Lemma stuck_step_mass_0 t σ j e :
  ¬ is_final ((t, σ) : mdpstate (con_lang_mdp lrust_lang)) →
  t !! j = Some e → to_val e = None → irreducible e σ →
  SeriesC (sch_pexec path_sch 1 ([j], (t, σ))) = 0.
Proof.
  intros Hnf Hj Hv Hirr.
  apply SeriesC_0. intros b.
  apply Rle_antisym; [|apply pmf_pos]. apply Rnot_gt_le. intros Hpos.
  rewrite sch_pexec_1 sch_step_or_final_not_final // in Hpos.
  rewrite /sch_step in Hpos. apply dbind_pos in Hpos as ([s a] & Hpos & Hsch).
  simpl in Hsch. apply dret_pos in Hsch. simplify_eq.
  apply dmap_pos in Hpos as (c' & -> & Hstep).
  simpl in Hstep. rewrite /con_lang_mdp_step (not_final_main _ _ Hnf) Hj Hv in Hstep.
  apply dmap_pos in Hstep as ([[??]?] & _ & Hstep).
  rewrite (Hirr _) in Hstep. lra.
Qed.

Lemma follows_stuck_mass c0 js t σ j e :
  SeriesC (sch_pexec path_sch (length js + 1) (js ++ [j], c0)) >= 1 →
  follows c0 js (t, σ) →
  ¬ is_final ((t, σ) : mdpstate (con_lang_mdp lrust_lang)) →
  t !! j = Some e → to_val e = None → reducible e σ.
Proof.
  intros Hmass Hf Hnf Hj Hv.
  destruct (classic (reducible e σ)) as [|Hirr]; [done|exfalso].
  apply not_reducible in Hirr.
  set (μ := sch_pexec path_sch (length js) (js ++ [j], c0)).
  set (b0 := (([j] : list nat), ((t, σ) : mdpstate (con_lang_mdp lrust_lang)))).
  assert (μ b0 > 0) as Hb0 by apply follows_pexec, Hf.
  rewrite sch_pexec_plus dbind_mass -/μ in Hmass.
  assert (SeriesC (λ a, μ a * SeriesC (sch_pexec path_sch 1 a))
          <= SeriesC (λ a, μ a - (if bool_decide (b0 = a) then μ b0 else 0))) as Hle.
  { apply SeriesC_le.
    - intros a. split; [apply Rmult_le_pos; [apply pmf_pos|apply SeriesC_ge_0'; intros; apply pmf_pos]|].
      case_bool_decide as Ha.
      + subst a. rewrite /b0 (stuck_step_mass_0 t σ j e) //. lra.
      + rewrite Rminus_0_r. rewrite -{2}(Rmult_1_r (μ a)).
        apply Rmult_le_compat_l; [apply pmf_pos|apply pmf_SeriesC].
    - apply (ex_seriesC_le _ μ); [|apply pmf_ex_seriesC].
      intros a. pose proof (pmf_pos μ a). case_bool_decide; subst; lra. }
  rewrite SeriesC_minus in Hle; [|apply pmf_ex_seriesC|apply ex_seriesC_singleton'].
  rewrite SeriesC_singleton' in Hle.
  pose proof (pmf_SeriesC μ). lra.
Qed.

(** * Wrapping the main thread so that it never returns *)

Definition loop_fn : val := rec: "loop" [] := "loop" [].
Definition wrap_ctx : list ectx_item := [AppRCtx (λ: [<>], loop_fn [])%V [] []].
Definition wrap (e : expr) : expr := fill wrap_ctx e.
Definition wrap_tp (t : list expr) : list expr :=
  match t with [] => [] | e :: t => wrap e :: t end.

Lemma wrap_not_val e : to_val (wrap e) = None.
Proof. done. Qed.

Lemma wrap_tp_not_final t σ :
  t ≠ [] → ¬ is_final ((wrap_tp t, σ) : mdpstate (con_lang_mdp lrust_lang)).
Proof.
  destruct t as [|e t]; [done|]. intros _.
  rewrite /is_final /= /con_lang_mdp_to_final /=. by intros [? ?].
Qed.

Lemma wrap_reducible e σ : to_val e = None → reducible (wrap e) σ → reducible e σ.
Proof.
  intros Hv [[[e2 σ2] efs] Hs]. rewrite /wrap in Hs.
  apply (con_ectx_language.prim_step_iff (Λ:=lrust_ectx_lang)) in Hs as (K' & e1' & e2' & HK & _ & Hs).
  edestruct (con_ectx_language.step_by_val (Λ:=lrust_ectx_lang) wrap_ctx K' e e1')
    as [K'' ->]; eauto using con_ectx_language.val_head_stuck.
  rewrite -con_ectx_language.fill_comp in HK. apply (inj _) in HK. subst e.
  eexists (fill K'' e2', σ2, efs). rewrite -con_ectx_language.fill_prim_step.
  - by apply con_ectx_language.head_prim_step.
  - by eapply con_ectx_language.val_head_stuck.
Qed.

Lemma thread_step_wrap t σ t' σ' :
  t ≠ [] → thread_step (t, σ) (t', σ') →
  t' ≠ [] ∧ ∃ i, follows (wrap_tp t, σ) [i] (wrap_tp t', σ').
Proof.
  intros Hne (t1 & t2 & e & e' & efs & Ht & Ht' & Hs). simpl in *. subst t t'.
  split; [by destruct t1|].
  pose proof (con_language.val_stuck _ _ _ Hs) as Hv.
  destruct t1 as [|x t1]; simpl.
  - exists 0%nat. eexists. split; [|done].
    rewrite /con_lang_mdp_step /=.
    apply dmap_pos. exists (wrap e', σ', efs). split; [done|].
    rewrite /wrap -con_ectx_language.fill_prim_step //.
  - exists (S (length t1)). eexists. split; [|done].
    rewrite /con_lang_mdp_step /=.
    rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag /= Hv.
    apply dmap_pos. exists (e', σ', efs). split; [|done].
    f_equal. rewrite insert_app_r_alt; [|lia]. rewrite Nat.sub_diag /=.
    by rewrite -app_assoc.
Qed.

Lemma rtc_thread_step_wrap e σ0 c :
  rtc thread_step ([e], σ0) c →
  c.1 ≠ [] ∧ ∃ js, follows ([wrap e], σ0) js (wrap_tp c.1, c.2).
Proof.
  revert c. apply rtc_ind_r.
  - split; [done|]. by exists [].
  - intros [t1 σ1] [t2 σ2] _ Hstep [Hne (js & Hf)].
    destruct (thread_step_wrap _ _ _ _ Hne Hstep) as [Hne' (i & Hfi)].
    split; [done|]. exists (js ++ [i]). by eapply follows_app.
Qed.

(** The wrapped program never returns, so any WP for [e] gives one for
    [wrap e] with any postcondition. *)
Lemma wp_wrap `{!lrustGS Σ} e Φ :
  WP e {{ _, True }} ⊢ WP wrap e {{ Φ }}.
Proof.
  iIntros "He". rewrite /wrap.
  iApply (wp_bind (fill wrap_ctx)).
  iApply (wp_wand with "He"). iIntros (v) "_ /=".
  wp_lam. iLöb as "IH". rewrite /loop_fn. wp_rec. iApply "IH".
Qed.

(** * Safety of every reachable configuration *)

Theorem lrust_wp_safe_from `{!lrustGpreS Σ} (e : expr) (K : nat) :
  (∀ `{!lrustGS Σ}, ⊢ £ K -∗ time_ctx -∗ WP e {{ _, True }}) →
  safe_from ([e], (∅, false)).
Proof.
  intros Hwp t σ e' Hrtc Hin Hv.
  destruct (rtc_thread_step_wrap _ _ _ Hrtc) as [Hne (js & Hf)]. simpl in *.
  apply list_elem_of_lookup in Hin as [j Hj].
  (* the mass bound for the wrapped program under [path_sch] *)
  assert (SeriesC (sch_pexec path_sch (length js + 1)
                     (js ++ [j], ([wrap e], (∅, false)))) >= 1 - 0) as Hmass.
  { apply (lrust_wp_safety (Σ := Σ) (js ++ [j]) path_sch (wrap e) _ 0 K (λ _, False));
      [lra|apply path_sch_mass_1|].
    intros ?. iIntros "£ TIME _". iApply wp_wrap. iApply (Hwp with "£ TIME"). }
  rewrite Rminus_0_r in Hmass.
  destruct j as [|j].
  - (* the main thread: stuck in [e] iff stuck in [wrap e] *)
    destruct t as [|e0 t]; [done|]. simpl in Hj. simplify_eq.
    apply wrap_reducible; [done|].
    eapply (follows_stuck_mass _ js (wrap_tp (e' :: t)) σ 0%nat); try done.
    by apply wrap_tp_not_final.
  - destruct t as [|e0 t]; [done|].
    eapply (follows_stuck_mass _ js (wrap_tp (e0 :: t)) σ (S j)); try done.
    by apply wrap_tp_not_final.
Qed.

(** VerusBelt's statement, for concurrent probabilistic λRust: every
    configuration reachable from a program with a WP is race-free, and
    none of its threads is stuck. *)
Corollary lrust_wp_nonracing_safe `{!lrustGpreS Σ} (e : expr) (K : nat) t σ :
  (∀ `{!lrustGS Σ}, ⊢ £ K -∗ time_ctx -∗ WP e {{ _, True }}) →
  rtc thread_step ([e], (∅, false)) (t, σ) →
  nonracing_threadpool t σ ∧ (∀ e', e' ∈ t → is_Some (to_val e') ∨ reducible e' σ).
Proof.
  intros Hwp Hrtc. pose proof (lrust_wp_safe_from e K Hwp) as Hsafe.
  split; [by eapply safe_from_nonracing|].
  intros e' Hin. destruct (to_val e') eqn:Hv; [by left|right].
  by eapply Hsafe.
Qed.
