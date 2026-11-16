(** The AlerusBelt headline example: a prophetic mutable borrow, a
    spawned thread and an error credit in one typed program.

    In Verus-like syntax:

        fn headline(Tracked(c): Tracked<ErrorCreditResource>)   // c = ↯(1/2)
        {
            let mut v: Box<int> = Box::new(0);
            {
                let r = &mut *v;                  // prophetic borrow: *v after
                                                  // the borrow is the prophecy ^r
                let (n, Tracked(c')) = rand(2, c); // n ∈ {0,1}; refund ↯1 on n = 0
                proof { if n != 1 { ec_contradict(&c') } }
                *r = n;
            }                                     // borrow ends: ^r resolved to n
            let b = *v == 1;
            let h = thread::spawn(move || assert(b));   // concurrency
        }

    The spawned [assert(b)] is UB unless [b]; that it is safe needs all
    three features at once: the error credit rules out [n = 0], and the
    prophecy of the borrow carries [*r = n] back to [*v] when the borrow
    ends.  [headline_safe]: under every scheduler of mass 1 the program
    gets stuck with probability at most 1/2; with the credit spent on
    [n = 0], the typed derivation is a genuine proof that the assertion
    holds on the [n = 1] branch. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum mdp.
From lrust.prob Require Import adequacy.
From lrust.lang Require Import notation lifting proofmode tactics lang heap race_adequacy.
From lrust.lang.lib Require Import spawn.
From lrust.typing Require Import type type_context programs rand_ubig soundness
                                   function cont own bool int uninit product
                                   borrow uniq_bor spawn mod_ty.
From lrust.typing.examples Require Import assert coin_flip.
Set Default Proof Using "Type".

Definition headline : expr :=
  (let: "p" := new [ #1 ] in
   let: "z" := #0 in
   "p" <- "z" ;;
   Newlft ;;
   let: "r" := UniqBor in
   let: "n" := rand #2 in
   "p" <- "n" ;;
   Endlft ;;
   let: "x" := !"p" in
   let: "one" := #1 in
   let: "b" := ("x" = "one") in
   letalloc: "bb" <- "b" in
   let: "spawn" := typing.spawn.spawn assert in
   letcall: "h" := "spawn" ["bb"] in
   loop_fn [])%E.

Section headline.
  Context `{!typeG Σ, !spawnG Σ}.

  (** What the typing context knows when [rand] returns [1]: the
      blocked [*v] will hold what the borrow [r] prophesies. *)
  Definition headline_inv :
      predl_trans' [Zₛ; at_locₛ (trackedₛ unitₛ); uniq_borₛ Zₛ;
                    blockedₛ (at_locₛ Zₛ); Zₛ] unitₛ :=
    λ post '(n -:: _ -:: m -:: b -:: _) mask π,
      n = 1%Z ∧ (blockedπ b π).2 = (vπ m π).2.

  (** The unit type is [Send] (a [mod_ty] of the empty product). *)
  Local Instance unit_ty_send : Send ()%T.
  Proof.
    apply mod_ty_send; [| |apply _]; intros x x' _; by destruct x, x'.
  Qed.

  (** [main] ends in a loop instead of returning (like a server's main
      thread), so that every scheduler keeps running the spawned thread:
      the MDP of the adequacy theorem stops when [main] returns.  A loop is
      safe for any transformer. *)
  Lemma typed_body_loop {𝔄l 𝔅} E L I (C : cctx 𝔅) (T : tctx 𝔄l) tr :
    ⊢ typed_body E L I C T (loop_fn [])%E tr.
  Proof.
    iIntros (tid xl mask post iκs) "_ _ _ _ _ _ _ _ _ _".
    iLöb as "IH". rewrite /loop_fn. wp_rec. iApply "IH".
  Qed.

  (** [assert_type], at the [fn<()>] binder form [spawn_type] expects. *)
  Lemma assert_type_unit :
    typed_val assert
      ((fn<()>(∅; bool_ty) → ())
         (λ (c: ~~ ()) 𝛷 '-[(l, b)], λ mask π, b ∧ ∀ ret, 𝛷 ret mask π))
      (assert, ()).
  Proof.
    match goal with |- typed_val _ (fn ?f _) _ =>
      replace f with (λ _ : (), FP ∅ +[bool_ty] ()%T AtomicClosed) end.
    - apply assert_type.
    - fun_ext. by intros [].
  Qed.

  Lemma headline_typed (l : loc) :
    ⊢ typed_body (𝔄l := [at_locₛ (trackedₛ unitₛ)]) (𝔅 := unitₛ) [] []
                 (InvCtx [] static AtomicClosed) []
                 +[#l ◁ ↯_T (1/2)] headline (λ _ _ _ _, True%type).
  Proof using spawnG0 typeG0 Σ.
    rewrite /headline.
    iApply (typed_body_impl with "[]"); last first. {
    iApply (type_new 1 with "[]"). { lia. } iIntros (v_p). simpl_subst.
    iApply type_int. iIntros (v_z). simpl_subst.
    iApply type_assign. { solve_typing. } { apply write_own; trivial. }
        { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
    iApply (type_newlft []). iIntros (κ).
    iApply (type_let with "[]").
      { eapply (type_uniqbor_instr _ _ _ _ _ int κ); solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (v_r). simpl_subst.
    (* bring the credit to the head of the context *)
    iApply (typed_body_tctx_incl _ _ _ (#l ◁ ↯_T (1/2) +:: _)).
    { do 3 eapply tctx_extract_elt_further. apply tctx_extract_elt_here_exact. }
    iApply (type_rand_case_tr 2 (1/2) flip_ε2 #l "n" _ _ _ _ _ _
              (λ n, if (n =? 1)%nat then headline_inv else λ _ _ _ _, True%type)).
    { lia. } { apply flip_ε2_bounded. } { apply flip_SeriesC_le. }
    iIntros (m Hm).
    destruct (Nat.eqb_spec m 1) as [-> | Hne]; last first.
    { assert (m = 0)%nat as -> by lia. change (flip_ε2 0) with 1%R.
      iApply type_credit_contradict_after_rand. }
    change (flip_ε2 1) with 0%R. simpl_subst. simpl.
    iApply (typed_body_impl with "[]"); last first. {
    (* *r = n, through the prophetic borrow *)
    iApply type_assign. { solve_typing. } { apply write_uniq. solve_typing. }
        { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
    (* the borrow ends: its prophecy is resolved and [*v] unblocked *)
    iApply (type_endlft_unblock _ _ _ _ κ). { solve_typing. }
    { eapply unblock_tctx_cons_just. eapply unblock_tctx_cons_just.
      eapply unblock_tctx_cons_unblock; [solve_typing|].
      eapply unblock_tctx_cons_just. apply unblock_tctx_nil. }
    (* b := ( *v == 1 ) *)
    iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ int); trivial.
        * apply int_stack_okay.
        * apply read_own_copy. apply int_copy. }
      { solve_typing. } { reflexivity. }
    iIntros (v_x). simpl_subst.
    iApply type_int. iIntros (v_one). simpl_subst.
    iApply type_int_eq. { solve_typing. } iIntros (v_b). simpl_subst.
    iApply (type_letalloc_1 bool_ty). { solve_typing. } 2: { trivial. }
        { eapply (_: ∀ x, x ≡ x). } iIntros (v_bb). simpl_subst.
    (* h := thread::spawn(move || assert(b)) *)
    iApply (type_let with "[]").
      { pose proof (spawn_type (ℭ := ()%ST) () (λ _ _ _ _, True%type) assert _
                      bool_ty ()%T assert assert_type_unit) as Hsp.
        cbv zeta in Hsp. apply Hsp. }
      { solve_typing. } { reflexivity. }
    iIntros (v_spawn). simpl_subst.
    match goal with |- context [ function.fn ?fp ?spec ] =>
      set (FP0 := fp); set (SP0 := spec) end.
    iApply (@type_letcall Σ typeG0 () [boolₛ] (at_locₛ (join_handleₛ ()%ST)) ()%ST
                _ _ _ () FP0 SP0).
      { solve_typing. } { apply lctx_ictx_alive_nil. solve_typing. }
      { solve_typing. } { solve_typing. }
    iIntros (v_h). simpl_subst.
    iApply (typed_body_loop _ _ _ _ _ (λ _ _ _ _, True%type)). }
    (* The verification condition of the [n = 1] branch. *)
    intros post xl mask π Hinv.
    destruct xl as (n & cl & m & b & zz & []).
    rewrite /headline_inv /= in Hinv.
    rewrite /compose /trans_tail /=.
    destruct m as [[[[[ml x0] ξi] md] mg] midx].
    destruct b as [[bx bξ] bζ].
    simpl in *. destruct Hinv as [-> Hinv].
    intros [[[[[ml' x0'] ξi'] md'] mg'] midx'] (Hl & Hx & Hξ) Hres.
    intros (n' & cl' & [lo vo] & zz' & []) (Hn' & Hcl & Hb & Hz & _).
    simpl in *. subst.
    (* The prophecy chain: the unblocked [*v] is what [b] prophesied, which
       is the borrow's future, which [Endlft] resolved to its current
       value [1].  (The two names of the borrow's prophecy variable differ
       only in a proof of inhabitation.) *)
    assert (vo = 1%Z) as ->.
    { rewrite Hb /= in Hinv. rewrite Hinv -Hres.
      by rewrite (proof_irrel
        (@to_inh_syn_type (Zₛ * (positiveₛ * positiveₛ))%ST (x0, (1%positive, 1%positive)))
        (@to_inh_syn_type (Zₛ * (positiveₛ * positiveₛ))%ST (1%Z, (1%positive, 1%positive)))). }
    (* the spawned [assert(b)] gets [b = true] *)
    rewrite /trans_upper /=. intros z Hz l0 a' <-.
    split; [split|done]; [done|by intros []].
  }
    (* The outer verification condition: the borrow's creation gives
       [headline_inv] to the [n = 1] branch. *)
    intros post [cl []] mask π _.
    rewrite /compose /trans_tail /trans_upper /=.
    intros l0 junk z Hz m b _ _ Hfut _ n Hn.
    destruct (Nat.eqb_spec n 1) as [->|]; [|done].
    rewrite /headline_inv /=. split; [done|exact Hfut].
    Unshelve. intros; reflexivity.
  Qed.
End headline.

(** Every scheduler of mass 1 keeps the whole program (the main thread and
    the spawned [assert(b)]) from getting stuck with probability at least
    1/2: an instance of [type_soundness_credit] with the [↯ (1/2)] budget.
    The bound is the credit; the spawned assertion's success on the
    [n = 1] branch comes from the prophecy of the borrow. *)
Theorem headline_safe `{!typePreG Σ, !spawnG Σ} `{Countable sch_int_state}
    (ζ : sch_int_state) (sch : scheduler (con_lang_mdp lrust_lang) sch_int_state) (n : nat) :
  sch_mass_1 sch →
  (SeriesC (sch_pexec sch n (ζ, ([headline], (∅, false)))) >= 1/2)%R.
Proof.
  intros Hmass.
  cut (SeriesC (sch_pexec sch n (ζ, ([headline], (∅, false)))) >= 1 - 1/2)%R; [lra|].
  apply (type_soundness_credit ζ sch (𝔅 := unitₛ) (λ _ _ _ _, True%type)
           (λ _ _ _, True%type) (1/2)%R headline n Hmass); [lra|done|].
  intros ? l. iApply headline_typed.
Qed.

Print Assumptions headline_safe.
