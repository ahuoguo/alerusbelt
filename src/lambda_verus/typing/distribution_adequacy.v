(** Distribution adequacy at the AlerusBelt typing layer, for
    concurrent prophetic λRust under every scheduler.

    Port of the sequential AlerusBelt [typing/distribution_adequacy.v].
    Differences: [typed_instr] now carries the prophecy context and a
    π-indexed postcondition, and executions are scheduler-indexed
    ([sch_exec]/[sch_lim_exec]), so the result is: a typed EPT sampler
    returns a [μ]-distributed value under every scheduler that lets it
    return almost surely. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum mdp.
From lrust.prob Require Import weakestpre.
From lrust.lifetime Require Import lifetime_full.
From lrust.lang Require Import adequacy distribution_adequacy proofmode notation.
From lrust.typing Require Import type programs rand_ubig soundness.
Set Default Proof Using "Type".

Local Open Scope R.

(** ** The EPT specification, as a typed instruction

    [ept_typed μ e] is the AlerusBelt model of a Verus sampler signature

    ```rust
      fn sample(Tracked(c): Tracked<ErrorCreditResource>,
                Ghost(Err): Ghost<spec_fn(V) -> real>)
        -> (Tracked<ErrorCreditResource>)
        requires c@ =~= Value { car: <expectation of Err under μ> },
                 forall |v| 0real <= Err(v) <= 1real,
        ensures  out@ =~= Value { car: Err(v) },
    ```

    same shape as [type_rand_ubig_instr].  [Err] is a meta-level
    function: it does not depend on the prophecy assignment π (Verus's
    [Ghost] is non-prophetic). *)
Definition ept_typed (Σ : gFunctors) (μ : distr val) (e : expr) : Prop :=
  ∀ (Err : val → R) (l : loc),
    (∀ v, 0 <= Err v <= 1) →
    ∀ `{!typeG Σ},
      ∃ tr : predl_trans [at_locₛ (trackedₛ unitₛ)] [at_locₛ (trackedₛ unitₛ)],
        (∀ π, tr (λ _ _ _, True) -[(l, ())] ⊤ π) ∧
        typed_instr [] [] (InvCtx [] static AtomicClosed)
          +[#l ◁ ↯_T (SeriesC (λ v, μ v * Err v))]
          e
          (λ v, +[#l ◁ ↯_T (Err v)])
          tr.

(** A typed spec that also returns the sampled value in its output
    context (the Verus signature [-> ((v, out): (V, Tracked<…>))])
    meets [ept_typed] by dropping the head entry. *)
Lemma typed_instr_drop_head `{!typeG Σ} {𝔄l 𝔅 𝔅l}
    E L I (T : tctx 𝔄l) e (t : val → tctx_elt 𝔅) (T' : val → tctx 𝔅l) tr :
  typed_instr E L I T e (λ v, t v +:: T' v) tr →
  typed_instr E L I T e T' (λ post, tr (λ '(_ -:: bl), post bl)).
Proof.
  intros Hinstr tid post mask iκs xl.
  iIntros "LFT TIME PROPH UNIQ E L I T Obs".
  iApply (pgl_wp_wand with "[-]").
  { iApply (Hinstr tid (λ '(_ -:: bl), post bl) mask iκs xl
             with "LFT TIME PROPH UNIQ E L I T Obs"). }
  iIntros (v) "H". iDestruct "H" as ([b bl]) "(L & I & [_ T] & Obs)".
  iExists bl. by iFrame.
Qed.

(** ** Typing-layer adequacy entry point

    [lrust_wp_pgl] hands the caller a bare [lrustGS Σ]; a WP coming out
    of the typing layer also needs the lifetime, prophecy and uniq
    contexts and an [invctx].  This allocates them, as
    [type_soundness_credit] does. *)
Theorem type_wp_pgl `{!typePreG Σ} `{Countable sch_int_state}
    (ζ : sch_int_state) (sch : scheduler (con_lang_mdp lrust_lang) sch_int_state)
    (e : expr) n (ε : R) (φ : val → Prop) :
  (0 <= ε) →
  (∀ `{!typeG Σ} (tid : thread_id),
      llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      (* the [cnaInv_logicG] instance of the [typeG], not of [typePreG] *)
      @invctx_interp Σ _ _ _ (@type_cnaInv_logicΣ Σ (@uniq_inG Σ type_uniqG))
        tid ⊤ [] (InvCtx [] static AtomicClosed) -∗
      ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (sch_exec sch n (ζ, ([e], (∅, false) : state))) φ ε.
Proof.
  intros Hε Hwp.
  apply (lrust_wp_pgl ζ sch e n ε 1%nat φ Hε).
  intros ?. iIntros "£ #TIME Hcr".
  iMod (llft_alloc with "£") as (?) "#LFT".
  iMod proph_init as (?) "#PROPH"; first done.
  iMod uniq_init as (Huniq) "#UNIQ"; first done. set (Htype := TypeG Σ _ _ _ _ _ _ _).
  iMod (@invctx_alloc Σ _ _ _ (@type_cnaInv_logicΣ Σ (uniq_inG (uniqG := Huniq))) ⊤)
    as (tid) "Hinvctx".
  iApply (Hwp Htype tid with "LFT TIME PROPH UNIQ Hinvctx Hcr").
Qed.

(** From the typed EPT spec to a WP. *)
Section ept_wp.
  Context `{!typeG Σ}.

  Lemma ept_typed_wp_gen (εin : R) (Err : val → R) (l : loc) e tid
      (tr : predl_trans [at_locₛ (trackedₛ unitₛ)] [at_locₛ (trackedₛ unitₛ)]) :
    (∀ π, tr (λ _ _ _, True) -[(l, ())] ⊤ π) →
    typed_instr [] [] (InvCtx [] static AtomicClosed)
      +[#l ◁ ↯_T εin] e (λ v, +[#l ◁ ↯_T (Err v)]) tr →
    llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    invctx_interp tid ⊤ [] (InvCtx [] static AtomicClosed) -∗
    ↯ εin -∗ WP e {{ v, ↯ (Err v) }}.
  Proof.
    iIntros (Htr Hinstr) "LFT TIME PROPH UNIQ Hinv Hcr".
    iApply fupd_pgl_wp. iMod persistent_time_receipt_0 as "#⧖0". iModIntro.
    iApply (pgl_wp_wand with "[-]").
    { iApply (Hinstr tid (λ _ _ _, True%type) ⊤ [] -[(l, ())]
               with "LFT TIME PROPH UNIQ [] [] Hinv [Hcr] []").
      - by rewrite /elctx_interp.
      - by rewrite /llctx_interp big_sepL_nil.
      - iSplit; last done. rewrite /tctx_elt_interp /=.
        iExists (LitV (LitLoc l)), 0%nat. iSplit; first done. iFrame "⧖0".
        rewrite /ty_own /=. by iFrame.
      - by iApply proph_obs_true. }
    iIntros (v) "H". iDestruct "H" as ([[l' []] []]) "(_ & _ & [Hc _] & _)".
    rewrite /tctx_elt_interp /=.
    iDestruct "Hc" as (w d Hev) "[_ [Hcr _]]". by rewrite /ty_own /=.
  Qed.

  Lemma ept_typed_wp (μ : distr val) (e : expr) (Err : val → R) (l : loc) tid :
    (∀ v, 0 <= Err v <= 1) →
    ept_typed Σ μ e →
    llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    invctx_interp tid ⊤ [] (InvCtx [] static AtomicClosed) -∗
    ↯ (SeriesC (λ v, μ v * Err v)) -∗
    WP e {{ v, ↯ (Err v) }}.
  Proof.
    intros HErr Hept.
    destruct (Hept Err l HErr _) as (tr & Htr & Hinstr).
    by apply (ept_typed_wp_gen _ _ l e tid tr).
  Qed.
End ept_wp.

Section adequacy.
  Set Default Proof Using "All".
  Context `{!typePreG Σ} `{Countable sch_int_state}.
  Context (ζ : sch_int_state) (sch : scheduler (con_lang_mdp lrust_lang) sch_int_state).
  Context (μ : distr val) (e : expr).
  Hypothesis Hept : ept_typed Σ μ e.

  (** The [pgl] upper bound a typed EPT spec yields: the sampler returns
      [target] with probability at most [μ target], under [sch]. *)
  Lemma ept_pgl_lim (target : val) :
    pgl (sch_lim_exec sch (ζ, ([e], (∅, false) : state))) (λ w, target ≠ w) (μ target).
  Proof.
    (* Instantiate the EPT spec at the indicator of [target]: the whole
       budget [μ target] is refunded on the single outcome we want to
       exclude, so [↯ 1] rules it out. *)
    set (Err := λ w, if bool_decide (target = w) then 1 else 0).
    assert (∀ v, 0 <= Err v <= 1) as HErr.
    { intros v. rewrite /Err. case_bool_decide; lra. }
    assert (SeriesC (λ v, μ v * Err v) = μ target) as Hexp.
    { rewrite (SeriesC_ext _ (λ v, if bool_decide (v = target) then μ target else 0)).
      - apply SeriesC_singleton.
      - intros v. rewrite /Err. do 2 case_bool_decide; subst; try done; lra. }
    rewrite /pgl. apply sch_lim_exec_continuous_prob. intros n.
    apply (type_wp_pgl ζ sch e n (μ target) (λ w, target ≠ w) (pmf_pos μ target)).
    intros Htype tid. iIntros "LFT TIME PROPH UNIQ Hinv Hcr".
    iApply (pgl_wp_wand with "[-]").
    { rewrite -Hexp.
      iApply (ept_typed_wp μ e Err ((1%positive, 0%Z) : loc) tid HErr Hept
               with "LFT TIME PROPH UNIQ Hinv Hcr"). }
    iIntros (v) "Hcr". rewrite /Err. case_bool_decide; subst.
    - iExFalso. iApply (ec_contradict with "Hcr"). lra.
    - done.
  Qed.

  (** ** Distribution adequacy for a typed sampler

      An [ept_typed] derivation plus almost-sure return under [sch]
      (external, e.g. from Verus's [decreases] clause discharged by
      credit amplification) pins the return distribution to [μ]. *)
  Theorem type_distribution_adequacy :
    SeriesC (sch_lim_exec sch (ζ, ([e], (∅, false) : state))) = 1%R →
    SeriesC μ = 1%R ∧ ∀ v, sch_lim_exec sch (ζ, ([e], (∅, false) : state)) v = μ v.
  Proof.
    intros Hterm.
    apply distribution_adequacy_of_pgl.
    - intros target. apply ept_pgl_lim.
    - apply Rle_ge, Req_le. symmetry. exact Hterm.
  Qed.
End adequacy.
