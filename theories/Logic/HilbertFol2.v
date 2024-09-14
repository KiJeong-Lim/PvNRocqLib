Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.Vector.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.

Import FolNotations.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := L.In.

Module FolHilbert.

Infix "⊢" := proves : type_scope.

Section HENKIN.

Context {L : language}.

#[local] Notation L' := (augmented_language L Henkin_constants).

#[local] Notation hatom := (ivar + Henkin_constants)%type.

#[local] Notation hsubst := (hatom -> trm L').

#[local] Existing Instance constant_symbols_similarity_instance.

#[local] Existing Instance trm_similarity_instance.

#[local] Existing Instance trms_similarity_instance.

#[local] Existing Instance frm_similarity_instance.

#[local] Existing Instance subst_similarity_instance.

(* Lemma proves_substitutivity' (sigma : hsubst) (Gamma : ensemble (frm L')) (p : frm L')
  (PROVE : Gamma ⊢ p)
  : E.image (hsubst_frm sigma) Gamma ⊢ hsubst_frm sigma p.
Proof.
  assert (EQ1 : E.image (hsubst_frm sigma) Gamma == E.image (subst_frm (twilight sigma)) (E.image twilight_frm Gamma)).
  { intros z. s!. split; intros [q [-> IN]].
    - exists (twilight_frm q); split.
      + eapply twilight_frm_lemma.
      + done!.
    - rewrite E.in_image_iff in IN. destruct IN as [p' [-> IN]]. exists p'. split.
      + symmetry. eapply twilight_frm_lemma.
      + done!.
  }
  rewrite EQ1. rewrite twilight_frm_lemma. eapply proves_substitutivity. clear EQ1.
  assert (empty_proof_intro : forall q : frm L', proof [] q -> E.empty ⊢ q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)).
  assert (PROVE : E.fromList ps ⊢ p).
  { exists ps. split. done. econstructor. exact PF. }
  clear PF. clear sigma. revert Gamma p INCL PROVE. induction ps as [ | q ps IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L', ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. induction PF; i.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + enough (HACK : forall phi : trms L' (function_arity_table L' f) -> trms L' (function_arity_table L' f) -> frm L', forall Gamma : ensemble (frm L'),
        forall phi_a_b : forall a, forall b, forall PROVES : pairwise_equal Gamma (twilight_trms a) (twilight_trms b), Gamma ⊢ twilight_frm (phi a b),
        (* forall phi_eq : forall ts, forall ts', twilight_frm (phi ts ts') = phi (twilight_trms ts) (twilight_trms ts'), *)
        Gamma ⊢ twilight_frm (eqns_imp (prod_rec (fun _ : trms L' (function_arity_table L' f) * trms L' (function_arity_table L' f) => frm L') phi (varcouples (function_arity_table L' f))) (function_arity_table L' f))
      ).
      { unfold Fun_eqAxm. eapply HACK.
        - simpl. ii. do 2 rewrite twilight_trm_unfold with (t := Fun_trm _ _). eapply proves_eqn_fun. exact PROVES.
        (* - ii. reflexivity. *)
      }
      simpl. induction (function_arity_table L f) as [ | n IH]; simpl; ii.
      * eapply phi_a_b. tauto.
      * exploit (IH (fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
        { ii. eapply phi_a_b. split; trivial. do 2 rewrite twilight_trms_unfold with (ts := S_trms _ _ _). unfold head. }
        { intros H. destruct (varcouples n) as [lhs rhs] eqn: H_OBS; simpl in *. eapply for_Imp_I. eapply extend_proves. 2: exact H. done!. }
    (* enough (HACK : forall phi : trms L' (function_arity_table L' f) -> trms L' (function_arity_table L' f) -> frm L', forall Gamma : ensemble (frm L'),
        forall phi_a_b : forall a, forall b, forall PROVES : pairwise_equal Gamma (twilight_trms a) (twilight_trms b), Gamma ⊢ twilight_frm (phi a b),
        (* forall phi_eq : forall ts, forall ts', twilight_frm (phi ts ts') = phi (twilight_trms ts) (twilight_trms ts'), *)
        Gamma ⊢ twilight_frm (eqns_imp (prod_rec (fun _ : trms L' (function_arity_table L' f) * trms L' (function_arity_table L' f) => frm L') phi (varcouples (function_arity_table L' f))) (function_arity_table L' f))
      ).
      { unfold Fun_eqAxm. eapply HACK.
        - simpl. ii. do 2 rewrite twilight_trm_unfold with (t := Fun_trm _ _). eapply proves_eqn_fun. exact PROVES.
        (* - ii. reflexivity. *)
      }
      simpl. induction (function_arity_table L f) as [ | n IH]; simpl; ii.
      * eapply phi_a_b. tauto.
      * exploit (IH (fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
        { ii. eapply phi_a_b. split; trivial. do 2 rewrite twilight_trms_unfold with (ts := S_trms _ _ _). unfold head. admit. }
        { intros H. destruct (varcouples n) as [lhs rhs] eqn: H_OBS; simpl in *. eapply for_Imp_I.  } *)
    (* enough (HACK : forall phi : trms L' (function_arity_table L' f) -> trms L' (function_arity_table L' f) -> frm L',
        forall phi_a_b : forall a, forall b, forall PROVES : pairwise_equal E.empty a b, E.empty ⊢ phi a b,
        E.empty ⊢ twilight_frm (eqns_imp (prod_rec (fun _ : trms L' (function_arity_table L' f) * trms L' (function_arity_table L' f) => frm L') phi (varcouples (function_arity_table L' f))) (function_arity_table L' f))
      ).
      { unfold Fun_eqAxm. eapply HACK. ii. eapply proves_eqn_fun. exact PROVES. }
      simpl. induction (function_arity_table L f) as [ | n IH]; simpl; ii.
      * eapply phi_a_b. *)
    + admit.
Admitted. *)

(* Lemma proves_substitutivity' (sigma : hsubst) (Gamma : ensemble (frm L')) (p : frm L')
  (PROVE : Gamma ⊢ p)
  : E.image (hsubst_frm sigma) Gamma ⊢ hsubst_frm sigma p.
Proof.
  assert (empty_proof_intro : forall q : frm L', proof [] q -> E.empty ⊢ q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)). rename sigma into s.
  assert (PROVE : E.fromList ps ⊢ p).
  { exists ps. split. done. econstructor. exact PF. }
  clear PF. revert Gamma p INCL PROVE s. induction ps as [ | q ps IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L', ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. revert s. induction PF; i.
    + pose proof (ps_spec p (or_introl eq_refl)) as [].
    + eapply for_Imp_E with (p := hsubst_frm s p).
      * eapply IHPF1. intros p' H_in. eapply ps_spec with (q := p'). rewrite in_app_iff. done!.
      * eapply IHPF2. intros p' H_in. eapply ps_spec with (q := p'). rewrite in_app_iff. done!.
    + simpl. eapply for_All_I.
      * intros p' H_in. inv H_in.
      * eapply IHPF. intros p' H_in. pose proof (ps_spec p' H_in) as [].
    + simpl. eapply empty_proof_intro. eapply IMP1.
    + simpl. eapply empty_proof_intro. eapply IMP2.
    + simpl. eapply empty_proof_intro. eapply CP.
    + simpl. eapply empty_proof_intro. set (chi := hchi_frm s (All_frm x p)). set (s' := cons_hsubst (inl x) (Var_trm chi) s).
      erewrite subst_hsubst_compat_in_frm with (sigma := one_hsubst (inl x) t) (p := p). 2: eapply to_hsubst_one_subst. rewrite hcompose_one_hsubst_frm.
      enough (ENOUGH : hsubst_frm (one_hsubst (inl chi) (hsubst_trm s t)) (hsubst_frm s' p) = hsubst_frm (cons_hsubst (inl x) (hsubst_trm s t) s) p).
      { rewrite <- ENOUGH. erewrite <- subst_hsubst_compat_in_frm with (sigma := one_hsubst (inl chi) (hsubst_trm s t)). 2: eapply to_hsubst_one_subst. eapply FA1. }
      unfold s'. rewrite <- hcompose_one_hsubst_frm. do 2 rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. intros u u_free.
      destruct u as [u | u]; unfold hsubst_compose, one_hsubst, cons_hsubst, nil_hsubst; simpl.
      * destruct (eqb (inl u) (inl x)) as [ | ] eqn: H_OBS.
        { rewrite hsubst_trm_unfold. unfold eqb. destruct (eq_dec (inl chi) (inl chi)) as [EQ2 | NE2]; done!. }
        { rewrite hsubst_trm_unfold with (t := Var_trm u). erewrite <- subst_hsubst_compat_in_trm with (s := one_subst chi (hsubst_trm s t)).
          - eapply subst_nil_trm. intros w w_free. rewrite eqb_spec in H_OBS. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w chi) as [EQ3 | NE2]; trivial.
            assert (claim1 : occurs_free_in_frm (inl u) (All_frm x p) = true).
            { subst w. simpl. rewrite andb_true_iff, negb_true_iff, eqb_neq. tauto. }
            subst w. apply hchi_frm_not_free with (sigma := s) in claim1. fold chi in claim1. congruence.
          - intros [z | z]. simpl. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec z chi) as [EQ1 | NE1].
            + subst z. unfold eqb. destruct (eq_dec (inl chi) (inl chi)) as [EQ3 | NE3]; done!.
            + unfold eqb. destruct (eq_dec (inl z) (inl chi)) as [EQ3 | NE3]; done!.
            + unfold eqb. destruct (eq_dec (inr z) (inl chi)) as [EQ3 | NE3]; done!.
        }
      * rewrite hsubst_trm_unfold with (t := Con_trm _). erewrite <- subst_hsubst_compat_in_trm with (s := one_subst chi (hsubst_trm s t)).
        { eapply subst_nil_trm. intros w w_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w chi) as [EQ2 | NE2]; trivial.
          assert (claim1 : occurs_free_in_frm (inr u) (All_frm x p) = true).
          { subst w. simpl. rewrite andb_true_iff. tauto. }
          subst w. apply hchi_frm_not_free with (sigma := s) in claim1. fold chi in claim1. congruence.
        }
        { intros [z | z]; simpl; trivial. unfold one_subst, cons_subst, nil_subst. unfold eqb.
          destruct (eq_dec z chi) as [EQ2 | NE2], (eq_dec (inl z) (inl chi)) as [EQ3 | NE3]; done!.
        }
    + simpl. set (chi := hchi_frm s (All_frm x p)). replace (hsubst_frm (cons_hsubst (inl x) (Var_trm chi) s) p) with (hsubst_frm s p).
      * eapply empty_proof_intro. eapply FA2. red. eapply frm_is_fresh_in_hsubst_iff with (z := chi) (sigma := s) (p := p). unfold frm_is_fresh_in_hsubst.
        rewrite L.forallb_forall. intros u u_free. autounfold with simplication_hints. rewrite negb_true_iff. eapply hchi_frm_not_free. red in NOT_FREE. simpl. s!. destruct u as [u | u].
        { rewrite occurs_free_in_frm_iff. rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in *. split; trivial. rewrite eqb_neq. congruence. }
        { rewrite occurs_free_in_frm_iff. split; trivial. }
      * eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. intros [u | u] u_free.
        { unfold cons_hsubst. destruct (eqb (inl u) (inl x)) as [ | ] eqn: H_OBS; trivial. rewrite eqb_eq in H_OBS. hinv H_OBS. red in NOT_FREE. rewrite occurs_free_in_frm_iff in u_free. rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in u_free. congruence. }
        { unfold cons_hsubst. reflexivity. }
    + set (n := 1 + last_ivar_frm (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))).
      replace (hsubst_frm s (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))) with (subst_frm (fun z : ivar => if le_lt_dec n z then Var_trm z else s (inl z)) (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))).
      * eapply for_Imp_E. eapply subst_frm_close_frm. clearbody n. induction n as [ | n IH]; simpl; i.
        { eapply empty_proof_intro. eapply FA3. }
        { eapply for_All_I. done. exact IH. }
      * rewrite subst_hsubst_compat_in_frm with (sigma := (fun z : hatom => match z with inl z => if le_lt_dec n z then Var_trm z else s (inl z) | inr z => s (inr z) end)).
        { eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. intros u u_free. destruct u as [u | u]; trivial.
          destruct (le_lt_dec n u) as [LE | LT]; trivial. pose proof (claim1 := @last_ivar_frm_gt L' (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q))) u). rewrite occurs_free_in_frm_iff in u_free. rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in u_free. rewrite u_free in claim1. discriminate claim1. lia.
        }
        { intros [z | z].
          - unfold to_hsubst. destruct (le_lt_dec n z) as [LE | LT]; trivial.
          - unfold to_hsubst. 
        }
Qed. *) 

End HENKIN.

End FolHilbert.
