(** * Atomic invariants

  Ported from VerusBelt ([typing/atomic_inv.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The original holds the invariant's contents in an Iris invariant, so
  opening it yields a [▷] and the whole file is organised around the credits
  that strip it; here the contents are a *formula* held by a non-atomic
  invariant of [nola.verus_halt.na_inv_fork] whose world satisfaction is a
  component of [verus_halt_wsat], so opening is later-free and credit-free.  The
  cancellable layer ([external_na_inv], [Active]) is rebuilt on top of that.

  *** Not ported: [typed_atomic_lock].

  It acquires the global atomic lock, whose implementation is a spin loop
  with no total-WP proof - see the note in [typing/programs_util_atomic.v].
  [typed_atomic_unlock] is fine and is ported. *)

From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From Stdlib.Logic Require Import Classical_Prop PropExtensionality
  FunctionalExtensionality.
From lrust.typing_total Require Export type.
From lrust.typing_total Require Import type_context programs
  programs_util_own own ghost tracked shr_bor product
  inv_context lft_contexts.
From nola.verus_halt Require Import na_inv_fork.
(** Nola's [util]: ours belongs to the partial stack; see
  [typing_total/model.v]. *)
From nola.verus_halt.util Require Import atomic_lock_counter.
From nola.verus_halt.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
From lrust.lang Require Import total_wsat.
Import GuardNotation ModwNotation TglWpwNotation.
(** Our [util] last, so that its [SemiIso] wins the name over Nola's; see
  [typing_total/type.v]. *)
From lrust.util Require Import basic.
(** [ctx_wp], for the [lrustTotGS] instance: this file states weakest
  preconditions.  See the head of [typing_total/ctx_wp.v]. *)
From lrust.typing_total Require Import ctx_wp.
Unset Default Proof Using.
(** [iris.prelude.options] sets [Default Goal Selector "!"], which rejects a
  bare tactic while more than one goal is focused.  It reaches a ported file
  through our imports and not through Nola's, so Nola's proofs - written
  against the default [1], "act on the first goal" - would otherwise need a
  focus fix every few lemmas.  Restoring [1] is a lint setting, not a
  soundness one. *)
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Implicit Type 𝔄 𝔅: syn_type.

Section atomic_invariants.
  Context `{!typeG FML Σ}.

  (** [atomic_threadpool], not Nola's [atomic_pool_name]: that is the name
    its [send_wsat] is built from, and ours is vacuous with concurrency
    stripped.  [typing_total/inv_context.v]'s [ATOMIC_POOL] makes the same
    choice. *)
  Definition null_tid : thread_id := atomic_threadpool.

  (** ** The cancellable layer, rebuilt over later-free non-atomic
    invariants *)

  Definition Active (γ: gname) : iProp Σ := own γ (Excl ()).

  Lemma Active_alloc : ⊢ |==> ∃ γ, Active γ.
  Proof. by iApply own_alloc. Qed.
  Lemma Active_2_no γ : Active γ -∗ Active γ -∗ False.
  Proof. iIntros "A B". by iDestruct (own_valid_2 with "A B") as %?. Qed.

  (** The formula constructors an atomic invariant's ghost assertion names *)
  Class AtomicInvFml := {
    active_fml : gname → FML $oi Σ;
    active_fml_sem γ : bor_sem (active_fml γ) ⊣⊢ Active γ;
    obs_fml : Prop → FML $oi Σ;
    obs_fml_sem φ : bor_sem (obs_fml φ) ⊣⊢ ⌜φ⌝;
    na_inv_tok_fml : namespace → FML $oi Σ → FML $oi Σ;
    na_inv_tok_fml_sem N Px :
      bor_sem (na_inv_tok_fml N Px) ⊣⊢ na_inv_tok ATOMIC_POOL N Px;
    (** The original's closer is a wand over the world satisfaction, which
      cannot be a formula: it would mention [bor_sem] at *every* formula.
      Following Nola's [obor_tok] ([nola.iris.borrow]), an opened invariant
      is a token of plain ghost ownership instead. *)
    na_otok_fml : namespace → FML $oi Σ → FML $oi Σ;
    na_otok_fml_sem N Px :
      bor_sem (na_otok_fml N Px) ⊣⊢ na_otok ATOMIC_POOL N Px;
    handle_fml : coPset → FML $oi Σ;
    handle_fml_sem c :
      bor_sem (handle_fml c) ⊣⊢ atomic_lock_handle atomic_lock_ctr_name c;
  }.
  Context `{!AtomicInvFml}.

  #[export] Instance na_inv_tok_fml_persistent N Px :
    Persistent (bor_sem (na_inv_tok_fml N Px)).
  Proof. rewrite na_inv_tok_fml_sem. exact _. Qed.

  Definition external_na_inv (γ: gname) (N: namespace) (Px : FML $oi Σ)
    : iProp Σ := na_inv_tok ATOMIC_POOL N (Px ∨ active_fml γ)%FML.

  #[export] Instance external_na_inv_persistent γ N Px :
    Persistent (external_na_inv γ N Px).
  Proof. exact _. Qed.

  Lemma external_na_inv_body_sem γ Px :
    bor_sem (Px ∨ active_fml γ)%FML ⊣⊢ bor_sem Px ∨ Active γ.
  Proof. by rewrite or_fml_sem active_fml_sem. Qed.

  (** The token for an atomic invariant this thread has opened *)
  Definition atomic_closer (γ: gname) (N: namespace) (Px : FML $oi Σ)
    : iProp Σ := na_otok ATOMIC_POOL N (Px ∨ active_fml γ)%FML.
  Definition atomic_closer_fml (γ: gname) (N: namespace) (Px : FML $oi Σ)
    : FML $oi Σ := na_otok_fml N (Px ∨ active_fml γ)%FML.
  Lemma atomic_closer_fml_sem γ N Px :
    bor_sem (atomic_closer_fml γ N Px) ⊣⊢ atomic_closer γ N Px.
  Proof. apply na_otok_fml_sem. Qed.

  (** Close an atomic invariant with its open token.  This is the original's
    closer, now a lemma rather than a stored wand. *)
  Lemma atomic_close {γ N Px F} :
    atomic_closer γ N Px -∗ (bor_sem Px ∨ Active γ) -∗
    na_own ATOMIC_POOL F =[verus_halt_wsat]=∗ na_own ATOMIC_POOL (F ∪ ↑N).
  Proof.
    iIntros "otok body pool W".
    iDestruct (wsat_split (W':=na_inv_wsat ATOMIC_POOL bor_sem) with "W")
      as "[Wn Wr]".
    iDestruct (na_inv_tok_close with "otok [body] pool Wn")
      as "(_ & pool & Wn)".
    { by rewrite external_na_inv_body_sem. }
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wn Wr") as "$".
    by iFrame "pool".
  Qed.

  Lemma external_na_inv_alloc N Px :
    bor_sem Px =[verus_halt_wsat]=∗ ∃ γ, external_na_inv γ N Px ∗ Active γ.
  Proof.
    iIntros "Px W". iMod Active_alloc as (γ) "A".
    iDestruct (na_inv_tok_alloc (p:=ATOMIC_POOL) (sm:=bor_sem)
      (Px ∨ active_fml γ)%FML N with "[Px]") as "T".
    { rewrite external_na_inv_body_sem. by iLeft. }
    iDestruct (bupdw_incl (W:=verus_halt_wsat) with "T") as "T'".
    iMod ("T'" with "W") as "[$ #tok]". iModIntro. iExists γ. by iFrame "A".
  Qed.

  (** Open an atomic invariant, knowing from a guard that it is not
    cancelled.  The original needs [↑nainvN ∪ F ⊆ E1] and later credits for
    the [▷] the Iris invariant introduces; here the guard is opened against
    [Wguard] and the invariant against [na_inv_wsat], which are different
    components of [verus_halt_wsat]. *)
  Lemma external_na_inv_acc_strong {G} γ N Px F :
    ↑N ⊆ F →
    external_na_inv γ N Px -∗ (G &&{Wguard}&&> Active γ) -∗ G -∗
    na_own ATOMIC_POOL F =[verus_halt_wsat]=∗
      na_own ATOMIC_POOL (F ∖ ↑N) ∗ G ∗ bor_sem Px ∗ atomic_closer γ N Px.
  Proof.
    move=> NF. iIntros "#inv #g G pool W".
    rewrite (na_own_subset NF). iDestruct "pool" as "[poolN pool]".
    iDestruct (wsat_split (W':=na_inv_wsat ATOMIC_POOL bor_sem) with "W")
      as "[Wn Wr]".
    iDestruct (na_inv_tok_open (sm:=bor_sem) (F:=(↑N:coPset))
      with "inv poolN Wn") as "(body & empty & otok & Wn)"; [done|].
    iEval (rewrite external_na_inv_body_sem) in "body".
    iDestruct "body" as "[Px|A]"; last first.
    { iDestruct (wsat_split (W':=Wguard) with "Wr") as "[Wg Wr']".
      iDestruct (guard_acc with "g G Wg") as "[A' _]".
      iDestruct (Active_2_no with "A A'") as "[]". }
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wn Wr") as "W".
    iModIntro. by iFrame "W pool G Px otok".
  Qed.

  Lemma external_na_inv_cancel γ N Px F :
    ↑N ⊆ F →
    external_na_inv γ N Px -∗ Active γ -∗
    na_own ATOMIC_POOL F =[verus_halt_wsat]=∗ bor_sem Px ∗ na_own ATOMIC_POOL F.
  Proof.
    move=> NF. iIntros "#inv A pool W".
    iMod (external_na_inv_acc_strong γ N Px F NF with "inv [] A pool W")
      as "(W & pool & A & Px & close)"; [iApply guard_refl|].
    iMod (atomic_close with "close [A] pool W") as "[W pool]"; [by iRight|].
    have ->: ((F ∖ ↑N) ∪ ↑N) = F.
    { rewrite difference_union_L union_comm_L.
      by apply subseteq_union_1_L. }
    iModIntro. by iFrame "W Px".
  Qed.

  (** ** The atomic invariant type

    [Send ty] is decided with excluded middle, exactly as in the original:
    for a non-[Send] type the contents can never leave the owning thread, and
    for a [Send] one they are kept at the null pool. *)
  Definition atomic_inv_body {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) (c: ~~ℭ)
      (tid: thread_id) : FML $oi Σ :=
    exs_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
      ex_fml (λ tid' : thread_id,
        (ty.(ty_ghox) x' d' g' tid' ∗
         obs_fml (pred (syn_abstract x') c) ∗
         pure_fml ((Send ty ∧ tid' = null_tid) ∨
                   (¬ Send ty ∧ tid = tid')))%FML)))).

  Lemma atomic_inv_body_sem {𝔄 ℭ} (ty: type 𝔄) pred (c: ~~ℭ) tid :
    bor_sem (atomic_inv_body ty pred c tid) ⊣⊢
      ∃ (x': ~~𝔄) (d' g': nat) (tid': thread_id),
        ty_gho ty x' d' g' tid' ∗ ⌜pred (syn_abstract x') c⌝ ∗
        ⌜(Send ty ∧ tid' = null_tid) ∨ (¬ Send ty ∧ tid = tid')⌝.
  Proof.
    rewrite /atomic_inv_body exs_fml_sem. apply bi.exist_proper=> x'.
    rewrite ex_fml_sem. apply bi.exist_proper=> d'.
    rewrite ex_fml_sem. apply bi.exist_proper=> g'.
    rewrite ex_fml_sem. apply bi.exist_proper=> tid'.
    by rewrite !bor_sep_sem obs_fml_sem pure_fml_sem.
  Qed.
  Lemma atomic_inv_body_sem_2 {𝔄 ℭ} (ty: type 𝔄) pred (c: ~~ℭ) tid
      x' d' g' tid' :
    ty_gho ty x' d' g' tid' -∗ ⌜pred (syn_abstract x') c⌝ -∗
    ⌜(Send ty ∧ tid' = null_tid) ∨ (¬ Send ty ∧ tid = tid')⌝ -∗
      bor_sem (atomic_inv_body ty pred c tid).
  Proof.
    rewrite atomic_inv_body_sem. iIntros "? ? %".
    iExists x', d', g', tid'. by iFrame.
  Qed.

  Program Definition atomic_inv_ty {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop)
      : type (invₛ ℭ) := {|
    ty_size := 0;
    ty_lev := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_persx x d g tid := empty_fml;
    ty_ghox x d g tid := match x with (N, γ, c) =>
      (active_fml γ ∗
       na_inv_tok_fml N (atomic_inv_body ty pred c tid ∨ active_fml γ))%FML
      end;
    ty_phys x tid := [];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> ?? ty pred sem Hsm *. by iIntros "$". Qed.
  Next Obligation. move=> ?? ty pred sem Hsm *. by iIntros "$". Qed.
  (** The [guard_proph] obligation is gone with the field; see [typing_total/type.v]. *)
  Next Obligation.
    move=> ?? ty pred sem Hsm *. rewrite (empty_sem_at Hsm). exact _.
  Qed.
  Next Obligation. move=> *. iIntros "_". by iApply empty_fml_sem_2. Qed.

  Lemma atomic_inv_ty_gho {𝔄 ℭ} (ty: type 𝔄) pred N γ (c: ~~ℭ) d g tid :
    ty_gho (atomic_inv_ty ty pred) (N, γ, c) d g tid ⊣⊢
      Active γ ∗ external_na_inv γ N (atomic_inv_body ty pred c tid).
  Proof. rewrite /ty_gho /= bor_sep_sem active_fml_sem na_inv_tok_fml_sem //. Qed.

  Program Definition atomic_closer_ty {𝔄 ℭ} (κ: lft) (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop)
      : type (invₛ ℭ) := {|
    ty_size := 0;
    ty_lev := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_persx x d g tid := empty_fml;
    ty_ghox x d g tid := match x with (N, γ, c) =>
      (handle_fml (↑N) ∗
       atomic_closer_fml γ N (atomic_inv_body ty pred c tid))%FML end;
    ty_phys x tid := [];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> ??? ty pred sem Hsm *. by iIntros "$". Qed.
  Next Obligation. move=> ??? ty pred sem Hsm *. by iIntros "$". Qed.
  (** The [guard_proph] obligation is gone with the field; see [typing_total/type.v]. *)
  Next Obligation.
    move=> ??? ty pred sem Hsm *. rewrite (empty_sem_at Hsm). exact _.
  Qed.
  Next Obligation. move=> *. iIntros "_". by iApply empty_fml_sem_2. Qed.

  Lemma atomic_closer_ty_gho {𝔄 ℭ} κ (ty: type 𝔄) pred N γ (c: ~~ℭ) d g tid :
    ty_gho (atomic_closer_ty κ ty pred) (N, γ, c) d g tid ⊣⊢
      atomic_lock_handle atomic_lock_ctr_name (↑N) ∗
      atomic_closer γ N (atomic_inv_body ty pred c tid).
  Proof.
    rewrite /ty_gho /= bor_sep_sem handle_fml_sem atomic_closer_fml_sem //.
  Qed.

  (** [atomic_inv_ty_resolve] removed along with [resolve]: it resolves a type's
    prophecies, and there are none. *)

  (** The body does not mention [tid] when [ty] is [Send]: the right
    disjunct of its side condition is then absurd.  The original can argue
    this up to [⊣⊢] because an Iris invariant is proper in its content; here
    the invariant holds a *formula*, so the two bodies have to be equal, and
    they are - by propositional and functional extensionality. *)
  Local Lemma atomic_inv_body_send_irrel {𝔄 ℭ} (ty: type 𝔄) pred (c: ~~ℭ)
      tid tid' :
    Send ty → atomic_inv_body ty pred c tid = atomic_inv_body ty pred c tid'.
  Proof.
    move=> Hsend. rewrite /atomic_inv_body. f_equal. fun_ext=> x'.
    f_equal. fun_ext=> d'. f_equal. fun_ext=> g'. f_equal. fun_ext=> tid''.
    do 3 f_equal. apply propositional_extensionality.
    split; move=> [?|[Hns _]]; by [left|exfalso; apply Hns].
  Qed.

  Local Lemma gho_equiv_of_send {𝔄 ℭ} (ty: type 𝔄) pred
      (x: ~~(invₛ ℭ)) d g tid tid' :
    Send ty →
    ty_gho (atomic_inv_ty ty pred) x d g tid ⊣⊢
      ty_gho (atomic_inv_ty ty pred) x d g tid'.
  Proof.
    move=> Hsend. destruct x as [[N γ] c].
    by rewrite !atomic_inv_ty_gho
      (atomic_inv_body_send_irrel ty pred c tid tid' Hsend).
  Qed.

  Lemma atomic_inv_ty_send {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) :
    Send ty → Send (atomic_inv_ty ty pred).
  Proof.
    move=> Hsend. split; [done|]. move=> tid tid' x d g G κs.
    rewrite (gho_equiv_of_send ty pred x d g tid tid' Hsend).
    iIntros "_ _ lfts _ G gho $ !>". iExists x, 0%nat.
    rewrite Nat.add_0_r. by iFrame "lfts G gho".
  Qed.

  Lemma atomic_inv_ty_sync {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) :
    Send ty → Sync (atomic_inv_ty ty pred).
  Proof.
    move=> Hsend tid tid' [[N γ] c] d g. split; [done|].
    rewrite /= (atomic_inv_body_send_irrel ty pred c tid tid' Hsend).
    by split.
  Qed.

  (** The typing rules for the global atomic lock are gone:
    [typed_atomic_unlock], [typed_atomic_inv_alloc], [_destroy], [_open]
    and [_close], together with the [GlobalAtomicLock] /
    [GlobalAtomicUnlock] terms they are stated over.  This language has
    no concurrency and so no global lock; what is kept above is the
    *formula* layer - [AtomicInvFml], [atomic_inv_body] and the closers -
    which [typing_total/model_inst.v] needs to inhabit the constructor
    signature.  Compare [typing_total/pcell.v]. *)

End atomic_invariants.
