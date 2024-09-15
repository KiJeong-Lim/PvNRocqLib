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

Lemma Fun_eqAxm_HC_free (f : L'.(function_symbols))
  : forall c : Henkin_constants, HC_occurs_in_frm c (Fun_eqAxm f) = false.
Proof.
  enough (HACK : forall phi : trms L' _ -> trms L' _ -> frm L', forall c,
    forall phi_a_b : forall a, forall b, forall claim : HC_occurs_in_trms c a = false /\ HC_occurs_in_trms c b = false, HC_occurs_in_frm c (phi a b) = false,
    HC_occurs_in_frm c ((nat_rec (fun _ => frm L') (prod_rec (fun _ => frm L') phi (varcouples (function_arity_table L' f))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (function_arity_table L' f))) = false
  ).
  { ii. unfold Fun_eqAxm. eapply HACK. ii. now s!. }
  induction (function_arity_table L' f) as [ | n IH]; simpl; ii.
  - rewrite phi_a_b; trivial. split; trivial.
  - s!. split. split; trivial. exploit (IH (fun ts : trms L' n => fun ts' : trms L' n => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite phi_a_b; trivial.
    + intros claim. simpl. destruct (varcouples n) as [lhs rhs] eqn: H_OBS; simpl in *. eapply claim.
Qed.

Lemma Rel_eqAxm_HC_free (R : L'.(relation_symbols))
  : forall c : Henkin_constants, HC_occurs_in_frm c (Rel_eqAxm R) = false.
Proof.
  enough (HACK : forall phi : trms L' _ -> trms L' _ -> frm L', forall c,
    forall phi_a_b : forall a, forall b, forall claim : HC_occurs_in_trms c a = false /\ HC_occurs_in_trms c b = false, HC_occurs_in_frm c (phi a b) = false,
    HC_occurs_in_frm c ((nat_rec (fun _ => frm L') (prod_rec (fun _ => frm L') phi (varcouples (relation_arity_table L' R))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (relation_arity_table L' R))) = false
  ).
  { ii. unfold Rel_eqAxm. eapply HACK. ii. now s!. }
  induction (relation_arity_table L' R) as [ | n IH]; simpl; ii.
  - rewrite phi_a_b; trivial. split; trivial.
  - s!. split. split; trivial. exploit (IH (fun ts : trms L' n => fun ts' : trms L' n => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite phi_a_b; trivial.
    + intros claim. simpl. destruct (varcouples n) as [lhs rhs] eqn: H_OBS; simpl in *. eapply claim.
Qed.

Lemma twilight_Fun_eqAxm (f : L'.(function_symbols))
  : E.empty ⊢ twilight_frm (Fun_eqAxm f).
Proof.
  rewrite untwilight_frm. 2: exact (Fun_eqAxm_HC_free f). set (n := L'.(function_arity_table) f + L'.(function_arity_table) f). set (s := fun z : ivar => Var_trm (z * 2)).
  replace (subst_frm s (Fun_eqAxm f)) with (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) (Fun_eqAxm f)).
  - eapply for_Imp_E with (p := close_from 0 n (Fun_eqAxm f)). eapply subst_frm_close_frm with (n := n) (s := s) (p := Fun_eqAxm f).
    clearbody n. clear s. induction n as [ | n IH]; simpl.
    + exists []. split. done. econs. exact (EQN_FUN f).
    + eapply for_All_I. done. exact IH.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. destruct (le_lt_dec n z) as [LE | LT]; trivial. rewrite Fun_eqAxm_free_vars in FREE. lia.
Qed.

Lemma twilight_Rel_eqAxm (R : L'.(relation_symbols))
  : E.empty ⊢ twilight_frm (Rel_eqAxm R).
Proof.
  rewrite untwilight_frm. 2: exact (Rel_eqAxm_HC_free R). set (n := L'.(relation_arity_table) R + L'.(relation_arity_table) R). set (s := fun z : ivar => Var_trm (z * 2)).
  replace (subst_frm s (Rel_eqAxm R)) with (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) (Rel_eqAxm R)).
  - eapply for_Imp_E with (p := close_from 0 n (Rel_eqAxm R)). eapply subst_frm_close_frm with (n := n) (s := s) (p := Rel_eqAxm R).
    clearbody n. clear s. induction n as [ | n IH]; simpl.
    + exists []. split. done. econs. exact (EQN_REL R).
    + eapply for_All_I. done. exact IH.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. destruct (le_lt_dec n z) as [LE | LT]; trivial. rewrite Rel_eqAxm_free_vars in FREE. lia.
Qed.

#[local] Opaque Nat.mul Nat.div "mod".

Lemma proves_substitutivity' (sigma : hsubst) (Gamma : ensemble (frm L')) (p : frm L')
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
    + eapply for_Imp_E; [eapply IHPF1 | eapply IHPF2]; intros q'; specialize ps_spec with (q := q'); ss!.
    + simpl. eapply for_All_I. done. eapply IHPF. done.
    + simpl. eapply empty_proof_intro. eapply IMP1.
    + simpl. eapply empty_proof_intro. eapply IMP2.
    + simpl. eapply empty_proof_intro. eapply CP.
    + simpl. erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity.
      replace (hsubst_frm (to_hsubst (one_subst x t)) p) with (hsubst_frm (one_hsubst (inl x) t) p).
      * enough (WTS : (twilight_frm (hsubst_frm (one_hsubst (inl x) t) p)) ≡ (subst_frm (one_subst (2 * x) (twilight_trm t)) (twilight_frm p))).
        {  rewrite WTS. eapply empty_proof_intro. eapply FA1. }
        eapply twilight_frm_one_hsubst.
      * eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. ii. unfold one_hsubst, cons_hsubst, nil_hsubst. unfold to_hsubst. unfold one_subst, cons_subst, nil_subst.
        destruct z as [z | z].
        { destruct (eqb _ _) as [ | ] eqn: H_OBS1; destruct (eq_dec _ _) as [EQ2 | NE2]; trivial.
          - rewrite eqb_eq in H_OBS1. hinv H_OBS1.
          - rewrite eqb_neq in H_OBS1. done!.
        }
        { destruct (eqb _ _) as [ | ] eqn: H_OBS; trivial. rewrite eqb_eq in H_OBS. hinv H_OBS. }
    + simpl. eapply empty_proof_intro. eapply FA2.
      red. rewrite Nat.mul_comm. rewrite <- twilight_frm_fvs. exact NOT_FREE.
    + simpl. eapply empty_proof_intro. eapply FA3.
    + eapply proves_reflexivity.
    + eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := twilight_trm (Var_trm 1)); eapply for_ByHyp; done!.
    + eapply twilight_Fun_eqAxm.
    + eapply twilight_Rel_eqAxm.
  - eapply for_Imp_E with (p := twilight_frm q).
    + change (E.image twilight_frm Gamma ⊢ twilight_frm (Imp_frm q p)). eapply IH.
      * intros p' H_in. done!.
      * rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (q :: ps)).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. rewrite E.in_image_iff. exists q. split; trivial. eapply INCL. simpl. left. trivial.
Qed.

End HENKIN.

End FolHilbert.
