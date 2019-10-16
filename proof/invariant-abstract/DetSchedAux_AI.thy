(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory DetSchedAux_AI
imports DetSchedInvs_AI
begin

context begin interpretation Arch .
requalify_facts
  invoke_untyped_st_tcb_at
  init_arch_objects_typ_at
  init_arch_objects_pred_tcb_at
  init_arch_objects_cur_thread
end

lemmas [wp] =
  init_arch_objects_typ_at
  init_arch_objects_pred_tcb_at
  init_arch_objects_cur_thread

lemma set_cap_valid_sched_pred[wp]:
  "set_cap cap slot \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: set_cap_def obj_at_kh_kheap_simps vs_all_heap_simps
               wp: set_object_wp get_object_wp)

crunches create_cap, cap_insert
  for valid_sched_pred[wp]: "valid_sched_pred_strong P::'z::state_ext state \<Rightarrow> _"
  (wp: dxo_wp_weak crunch_wps)

crunches update_cdt_list
  for valid_sched_pred[wp]: "valid_sched_pred_strong P"
  (wp: dxo_wp_weak crunch_wps)

lemma (in pspace_update_eq) test_sc_refill_max_eq[iff]:
  "test_sc_refill_max t (f s) = test_sc_refill_max t s"
  using pspace by (simp add: test_sc_refill_max_def)

lemma store_word_offs_valid_sched_pred[wp]:
  "store_word_offs ptr offs v \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: store_word_offs_def wp: dmo_valid_sched_pred)

lemma set_mrs_valid_sched_pred[wp]:
  "set_mrs thread buf msgs \<lbrace>valid_sched_pred_strong P\<rbrace>"
  apply (wpsimp simp: set_mrs_def wp: zipWithM_x_inv' set_object_wp)
  by (auto simp: vs_all_heap_simps obj_at_kh_kheap_simps)

global_interpretation set_mrs: valid_sched_pred_locale _ "set_mrs r t mrs"
  by unfold_locales wp

lemma set_cap_test_sc_refill_max[wp]:
 "\<lbrace>test_sc_refill_max t\<rbrace> set_cap c p \<lbrace>\<lambda>rv. test_sc_refill_max t\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: test_sc_refill_max_def obj_at_def
       | intro impI conjI | rule_tac x=scp in exI)+
  done

global_interpretation set_cap: valid_sched_pred_locale _ "set_cap c p"
  by unfold_locales wp

crunch_ignore (del: create_cap_ext)

global_interpretation create_cap: valid_sched_pred_locale _ "create_cap type bits untyped is_device slot"
  by unfold_locales wp

global_interpretation cap_insert: valid_sched_pred_locale _ "cap_insert new_cap src_slot dest_slot"
  by unfold_locales wp

locale DetSchedAux_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes init_arch_objects_valid_idle[wp]:
    "\<And>t p n s r. init_arch_objects t p n s r \<lbrace>\<lambda>s::'state_ext state. valid_idle s\<rbrace>"
  assumes init_arch_objects_valid_sched_pred[wp]:
    "\<And>t p n s r P. init_arch_objects t p n s r \<lbrace>valid_sched_pred_strong P::'state_ext state \<Rightarrow> _\<rbrace>"

lemmas mapM_x_defsym = mapM_x_def[symmetric]

context DetSchedAux_AI begin

sublocale init_arch_objects: valid_sched_pred_locale _ "init_arch_objects t p n s r"
  by unfold_locales (rule init_arch_objects_valid_sched_pred)

crunches invoke_untyped
  for valid_sched_pred_misc[wp]:
      "\<lambda>s::'state_ext state. P (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                               (ready_queues s) (release_queue s) (scheduler_action s)
                               (last_machine_time_of s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv
   simp: detype_def whenE_def unless_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: do_machine_op)

end

lemma init_arch_objects_tcb_heap[wp]:
  "init_arch_objects t p n s r \<lbrace>\<lambda>s. P (tcbs_of s)\<rbrace>"
  apply (rule pred_map_heap_lift[where heap=tcbs_of and P=P and R=\<top>, simplified])
  apply (rule rsubst[where P="\<lambda>t. _ \<lbrace>t\<rbrace>", OF _ ext], rename_tac ref)
   apply (rule_tac N=N and P="\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> P tcb" and p=ref in init_arch_objects_obj_at_non_arch)
   apply (clarsimp simp: non_arch_obj_def)
  apply (rule_tac f=N in arg_cong)
  by (auto simp: obj_at_kh_kheap_simps pred_map_simps vs_heap_simps)

lemma init_arch_objects_sc_heap[wp]:
  "init_arch_objects t p n s r \<lbrace>\<lambda>s. P (scs_of s)\<rbrace>"
  apply (rule pred_map_heap_lift[where heap=scs_of and P=P and R=\<top>, simplified])
  apply (rule rsubst[where P="\<lambda>t. _ \<lbrace>t\<rbrace>", OF _ ext], rename_tac ref)
   apply (rule_tac N=N and P="\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> P sc" and p=ref in init_arch_objects_obj_at_non_arch)
   apply (clarsimp simp: non_arch_obj_def)
  apply (rule_tac f=N in arg_cong)
  by (auto simp: obj_at_kh_kheap_simps pred_map_simps vs_heap_simps)

lemma delete_objects_etcb_at[wp]:
  "delete_objects a b \<lbrace>\<lambda>s. etcb_at P t s\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wpsimp simp: detype_def wrap_ext_det_ext_ext_def)
  apply (simp add: pred_map_simps vs_heap_simps etcb_at'_def)
  done

declare delete_objects_st_tcb_at[wp]

crunches reset_untyped_cap
  for etcb_at[wp]: "etcb_at P t :: 'z::state_ext state \<Rightarrow> _"
  (wp: preemption_point_inv mapME_x_inv_wp crunch_wps
   simp: unless_def)

lemma foldr_kh_eq:
  "foldr (\<lambda>p kh. kh(p \<mapsto> ko')) ptrs kh t = Some ko \<Longrightarrow>
  if t \<in> set ptrs then ko = ko' else kh t = Some ko"
  by (simp add: foldr_fun_upd_value split: if_splits)

lemma TCB_default_objectD[dest!]:
  "\<lbrakk>  TCB tcb = default_object t dev c dm; t \<noteq> Untyped \<rbrakk> \<Longrightarrow> tcb = default_tcb dm"
  by (simp add: default_object_def split: apiobject_type.splits)

declare tcb_state_merge_tcb_state_default[simp]

lemma retype_region_etcb_at[wp]:
  "\<lbrace>etcb_at P t\<rbrace> retype_region a b c d dev \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace> "
  apply (simp add: retype_region_def)
  apply wp
  apply (clarsimp simp add: pred_tcb_at_def obj_at_def simp del: fun_upd_apply)
  apply (clarsimp simp:  etcb_at'_def etcb_of_def pred_map_simps vs_heap_simps)
  apply (drule foldr_kh_eq)
  apply (auto simp: etcb_of_def split: if_split_asm option.splits elim!: rsubst[where P=P])
  done

lemma etcb_at_def2:
  "etcb_at P t s \<equiv> tcb_at t s \<longrightarrow> obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> P (etcb_of tcb)) t s"
  by (auto simp add: atomize_eq etcb_at'_def obj_at_kh_kheap_simps pred_map_simps vs_heap_simps is_tcb)

lemma retype_region_etcb_at_other:
  assumes ptrv: "t \<notin> set (retype_addrs ptr' ty n us)"
  shows "\<lbrace>\<lambda>s. N (etcb_at P t s)\<rbrace> retype_region ptr' n us ty dev \<lbrace>\<lambda>r s. N (etcb_at P t s)\<rbrace>"
  unfolding etcb_at_def2 imp_conv_disj
  by (intro hoare_vcg_disj_lift_N[of N] retype_region_obj_at_other[OF assms])

lemma retype_region_etcb_at':
  "\<lbrace>\<lambda>s. etcb_at P t s
        \<and> obj_at \<top> t s
        \<and> valid_objs s
        \<and> pspace_aligned s
        \<and> (\<exists>sz. pspace_no_overlap (up_aligned_area ptr sz) s
                \<and> range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
  retype_region ptr n us ty dev
  \<lbrace>\<lambda>rv. etcb_at P t\<rbrace>"
  apply (rule_tac S="t \<notin> set (retype_addrs ptr ty n us)" in hoare_gen_asm'')
   subgoal using pspace_no_overlap_obj_not_in_range retype_addrs_subset_ptr_bits by blast
  by (wpsimp wp: retype_region_etcb_at_other)

context DetSchedAux_AI begin
lemma invoke_untyped_etcb_at:
  "\<lbrace>\<lambda>s::'state_ext state. etcb_at P t s\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (cases ui)
  apply (simp add: invoke_untyped_def whenE_def flip: mapM_x_def split del: if_split)
  apply (wpsimp wp: mapM_x_wp'
            create_cap.cspace_pred_tcb_at[where P=Not]
            hoare_convert_imp[OF create_cap.cspace_pred_tcb_at[where P=Not]]
            hoare_convert_imp[OF _ init_arch_objects_valid_sched_pred]
         | wp_once hoare_drop_impE_E)+
  done
end

lemma invoke_untyped_non_cspace_obj_at:
  assumes non_cspace: "cspace_agnostic_pred P"
  assumes non_arch: "\<forall>ko. P ko \<longrightarrow> non_arch_obj ko"
  shows "\<lbrace>\<lambda>s. obj_at P t s
              \<and> ex_nonz_cap_to t s
              \<and> ct_active s
              \<and> scheduler_action s = resume_cur_thread
              \<and> valid_untyped_inv ui s
              \<and> invs s\<rbrace>
         invoke_untyped ui
         \<lbrace>\<lambda>rv s. obj_at P t s\<rbrace>"
  apply wp_pre
   apply (rule invoke_untyped_Q
          ; wpsimp wp: retype_region_obj_at_other3
                       init_arch_objects_obj_at_non_arch[OF non_arch]
                       create_cap.cspace_agnostic_obj_at[OF non_cspace]
                       set_cap.cspace_agnostic_obj_at[OF non_cspace]
                       reset_untyped_cap_obj_at[OF non_cspace]
          ; fastforce)
  apply (cases ui; clarsimp simp: cte_wp_at_caps_of_state obj_at_def)
  by (frule (2) descendants_of_empty_untyped_range[where p=t]; clarsimp)

lemma invoke_untyped_bound_sc_tcb_at:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P t s
        \<and> ex_nonz_cap_to t s
        \<and> ct_active s
        \<and> scheduler_action s = resume_cur_thread
        \<and> valid_untyped_inv ui s
        \<and> invs s\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P t s\<rbrace>"
  by (auto intro!: invoke_untyped_non_cspace_obj_at simp: pred_tcb_at_def cspace_agnostic_pred_def)

lemma invoke_untyped_sc_at_pred_n:
  "\<lbrace>\<lambda>s. sc_at_pred_n N proj P scp s
        \<and> ex_nonz_cap_to scp s
        \<and> ct_active s
        \<and> scheduler_action s = resume_cur_thread
        \<and> valid_untyped_inv ui s
        \<and> invs s\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>rv s. sc_at_pred_n N proj P scp s\<rbrace>"
  by (auto intro!: invoke_untyped_non_cspace_obj_at simp: sc_at_pred_n_def cspace_agnostic_pred_def)

lemma cur_time_detype[simp]:
  "cur_time (detype r s) = cur_time s"
  by (simp add: detype_def)

crunches retype_region
  for cur_time[wp]: "\<lambda>s. P (cur_time s)"

lemma retype_region_sc_at_pred_n:
  "\<lbrace>\<lambda>s. sc_at_pred_n N proj P p s
        \<and> (pspace_no_overlap (up_aligned_area ptr' sz) s
        \<and> range_cover ptr' sz (obj_bits_api ty us) n
        \<and> valid_objs s
        \<and> pspace_aligned s)\<rbrace>
   retype_region ptr' n us ty dev
   \<lbrace>\<lambda>rv. sc_at_pred_n N proj P p\<rbrace>"
  by (wpsimp simp: sc_at_pred_n_def[abs_def] wp: retype_region_obj_at_other3; fastforce)

lemma retype_region_bound_sc_obj_tcb_at:
  "\<lbrace>\<lambda>s. bound_sc_obj_tcb_at (P (cur_time s)) t s
        \<and> pspace_no_overlap (up_aligned_area ptr' sz) s
        \<and> range_cover ptr' sz (obj_bits_api ty us) n
        \<and> valid_objs s
        \<and> pspace_aligned s\<rbrace>
   retype_region ptr' n us ty dev
   \<lbrace>\<lambda>rv s. bound_sc_obj_tcb_at (P (cur_time s)) t s\<rbrace>"
  by (rule bound_sc_obj_tcb_at_lift'[where g=cur_time]
      ; wpsimp wp: retype_region_sc_at_pred_n retype_region_st_tcb_at
      ; fastforce)

lemmas reset_untyped_cap_sched_context_at =
  reset_untyped_cap_obj_at[where P'="\<lambda>obj. \<exists>sc n. obj = SchedContext sc n \<and> P' sc" for P'
                           , simplified cnode_agnostic_pred_def tcb_cnode_agnostic_pred_def, simplified]

lemma preemption_point_cur_time[wp]:
  "preemption_point \<lbrace>\<lambda>s. P (cur_time s)\<rbrace>"
  by (wpsimp simp: preemption_point_def do_extended_op_def
               wp: OR_choiceE_weak_wp hoare_drop_imps)

lemma reset_untyped_cap_cur_time[wp]:
  "reset_untyped_cap slot \<lbrace>\<lambda>s. P (cur_time s)\<rbrace>"
  by (wpsimp simp: reset_untyped_cap_def delete_objects_def
               wp: mapME_x_inv_wp hoare_drop_imps)

lemma reset_untyped_cap_bound_sc_obj_tcb_at:
  "\<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (cur_time s)) t s)
        \<and> cte_wp_at is_untyped_cap slot s
        \<and> (\<forall>cap. caps_of_state s slot = Some cap
                  \<longrightarrow> t \<notin> cap_range cap
                       \<and> bound_sc_tcb_at (case_option True (\<lambda>scp. scp \<notin> cap_range cap)) t s)\<rbrace>
   reset_untyped_cap slot
   \<lbrace>\<lambda>rv s. N (bound_sc_obj_tcb_at (P (cur_time s)) t s)\<rbrace>"
  apply (rule bound_sc_obj_tcb_at_lift_strong'[where g=cur_time], wpsimp)
  apply (rule hoare_vcg_ex_lift_N_pre_conj)
  apply (rule validI; elim conjE rsubst[of N])
  by (intro conj_cong2
      ; erule use_valid_inv[OF _ reset_untyped_cap_pred_tcb_at]
              use_valid_inv[OF _ reset_untyped_cap_sc_at_pred_n]
      ; clarsimp simp: cte_wp_at_caps_of_state pred_tcb_at_def obj_at_def)

(* FIXME: Move to Invariants_AI *)
lemma sym_ref_tcb_sc: "\<lbrakk> sym_refs (state_refs_of s); kheap s tp = Some (TCB tcb);
   tcb_sched_context tcb = Some scp \<rbrakk> \<Longrightarrow>
  \<exists>sc n. kheap s scp = Some (SchedContext sc n) \<and> sc_tcb sc = Some tp"
  apply (drule sym_refs_obj_atD[rotated, where p=tp])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def get_refs_def2 elim!: sym_refsE)
  apply (drule_tac x="(scp, TCBSchedContext)" in bspec)
   apply fastforce
  apply (clarsimp simp: obj_at_def)
  apply (case_tac koa; clarsimp simp: get_refs_def2)
  done

(* FIXME: move? *)
lemma idle_thread_idle_thread_ptr:
  "valid_idle s \<Longrightarrow> idle_thread s = idle_thread_ptr"
  by (simp add: valid_idle_def)

(* FIXME: move? *)
lemma ex_nonz_cap_to_iff_not_idle_thread_ptr:
  "\<lbrakk> kheap s t = Some (TCB tcb); tcb_sched_context tcb = Some sc_ptr; invs s \<rbrakk>
    \<Longrightarrow> ex_nonz_cap_to t s \<longleftrightarrow> t \<noteq> idle_thread_ptr"
  apply (rule iffI)
   apply (rule idle_thread_idle_thread_ptr[THEN subst, OF invs_valid_idle], assumption)
   apply (erule contrapos_pn[where Q="ex_nonz_cap_to _ _"]; simp)
   apply (rule idle_no_ex_cap[OF invs_valid_global_refs invs_valid_objs]; assumption)
  apply (rule if_live_then_nonz_cap_invs, assumption+)
  apply (frule thread_not_idle_implies_sc_not_idle; clarsimp simp: live_def)
  done

lemma bound_sc_obj_tcb_at_False_ex_nonz_cap_to_iff_not_idle_thread_ptr:
  "\<lbrakk> bound_sc_obj_tcb_at P t s; invs s \<rbrakk> \<Longrightarrow> ex_nonz_cap_to t s \<longleftrightarrow> t \<noteq> idle_thread_ptr"
  by (clarsimp simp: vs_all_heap_simps ex_nonz_cap_to_iff_not_idle_thread_ptr
              split: option.splits)

lemma ex_nonz_cap_to_tcb_implies_ex_nonz_cap_to_sc:
  "\<lbrakk> invs s; ex_nonz_cap_to t s; kheap s t = Some (TCB tcb); tcb_sched_context tcb = Some sc_ptr \<rbrakk>
   \<Longrightarrow> ex_nonz_cap_to sc_ptr s"
  apply (frule sym_refsE[where x=t and y=sc_ptr and tp=SCTcb, OF invs_sym_refs]
         ; clarsimp simp add: in_state_refs_of_iff
         ; case_tac ko
         ; clarsimp simp: get_refs_def2)
  by (clarsimp simp: live_def live_sc_def ex_nonz_cap_to_iff_not_idle_thread_ptr
                     if_live_then_nonz_cap_invs)

lemma ex_nonz_cap_to_not_idle_sc_ptr:
  "\<lbrakk> invs s; ex_nonz_cap_to scp s \<rbrakk> \<Longrightarrow> scp \<noteq> idle_sc_ptr"
  by (frule invs_valid_global_refs, frule invs_valid_objs, frule (1) idle_sc_no_ex_cap, auto)

lemma bound_sc_obj_tcb_at_nonz_cap_lift:
  assumes I: "\<And>s. I s \<Longrightarrow> invs s"
  assumes bound_sc:
    "\<And>P. \<lbrace>\<lambda>s. bound_sc_tcb_at P t s \<and> ex_nonz_cap_to t s \<and> I s\<rbrace>
          f \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  assumes sc_refill_cfg:
    "\<And>scp. \<lbrace>\<lambda>s. sc_refill_cfg_sc_at P scp s \<and> ex_nonz_cap_to scp s \<and> I s\<rbrace>
            f \<lbrace>\<lambda>rv. sc_refill_cfg_sc_at P scp\<rbrace>"
  shows "\<lbrace>\<lambda>s. bound_sc_obj_tcb_at P t s \<and> ex_nonz_cap_to t s \<and> I s\<rbrace>
         f \<lbrace>\<lambda>rv. bound_sc_obj_tcb_at P t\<rbrace>"
  apply (rule bound_sc_obj_tcb_at_lift_strong, rule validI, elim exE conjE)
  apply (frule I)
  apply (clarsimp simp: pred_tcb_at_def sc_at_ppred_def obj_at_def)
  apply (frule (3) ex_nonz_cap_to_tcb_implies_ex_nonz_cap_to_sc)
  apply (frule_tac scp=p in ex_nonz_cap_to_not_idle_sc_ptr, assumption)
  apply (frule use_valid, rule_tac P="\<lambda>scpo. scpo = Some p" in bound_sc; clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (frule use_valid, rule_tac scp=p in sc_refill_cfg; clarsimp simp: sc_at_ppred_def obj_at_def)
  done

lemma (in DetSchedAux_AI) invoke_untyped_bound_sc_obj_tcb_at[wp]:
  "\<lbrace>\<lambda>s::'state_ext state. bound_sc_obj_tcb_at (P (cur_time s)) t s
        \<and> ex_nonz_cap_to t s
        \<and> ct_active s
        \<and> scheduler_action s = resume_cur_thread
        \<and> valid_untyped_inv ui s
        \<and> invs s\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>rv s. bound_sc_obj_tcb_at (P (cur_time s)) t s\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f=cur_time, rotated], wpsimp)
  by (rule bound_sc_obj_tcb_at_nonz_cap_lift; wpsimp wp: invoke_untyped_sc_at_pred_n)

lemma set_cap_obj_at_impossible_cur_time:
  "\<lbrace>\<lambda>s. P (obj_at (P' (cur_time s)) p s) \<and> (\<forall>ko. P' (cur_time s) ko \<longrightarrow> caps_of ko = {})\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. P (obj_at (P' (cur_time s)) p s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def)
  apply (subgoal_tac "\<forall>sz cs. well_formed_cnode_n sz cs \<longrightarrow> \<not> P' (cur_time s) (CNode sz cs)")
   apply (subgoal_tac "\<forall>tcb. \<not> P' (cur_time s) (TCB tcb)")
    apply (clarsimp simp: fun_upd_def[symmetric] wf_cs_insert dom_def)
    apply auto[1]
   apply (auto simp:caps_of_def cap_of_def ran_tcb_cnode_map wf_cs_ran_nonempty)
  done

lemma do_machine_op_obj_at_cur_time:
  "\<lbrace>\<lambda>s. P (obj_at (Q (cur_time s)) p s)\<rbrace> do_machine_op f \<lbrace>\<lambda>_ s. P (obj_at (Q (cur_time s)) p s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_time], wpsimp+)

lemma retype_region_obj_at_other_cur_time:
  assumes ptrv: "ptr \<notin> set (retype_addrs ptr' ty n us)"
  shows "\<lbrace>\<lambda>s. obj_at (P (cur_time s)) ptr s\<rbrace> retype_region ptr' n us ty dev \<lbrace>\<lambda>r s. obj_at (P (cur_time s)) ptr s\<rbrace>"
  by (intro hoare_lift_Pf[where f=cur_time and P="\<lambda>ct. obj_at (P ct) ptr" ]
            retype_region_obj_at_other[OF assms] retype_region_cur_time)

lemma retype_region_obj_at_other2_cur_time:
  "\<lbrace>\<lambda>s. ptr \<notin> set (retype_addrs ptr' ty n us)
       \<and> obj_at (P (cur_time s)) ptr s\<rbrace> retype_region ptr' n us ty dev \<lbrace>\<lambda>rv s. obj_at (P (cur_time s)) ptr s\<rbrace>"
  by (rule hoare_assume_pre) (wpsimp wp: retype_region_obj_at_other_cur_time)

lemma retype_region_obj_at_other3_cur_time:
  "\<lbrace>\<lambda>s. pspace_no_overlap_range_cover ptr sz s \<and> obj_at (P (cur_time s)) p s \<and> range_cover ptr sz (obj_bits_api ty us) n
           \<and> valid_objs s \<and> pspace_aligned s\<rbrace>
     retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv s. obj_at (P (cur_time s)) p s\<rbrace>"
  apply (rule hoare_pre)
   apply (rule retype_region_obj_at_other2_cur_time)
  apply clarsimp
  apply (drule subsetD [rotated, OF _ retype_addrs_subset_ptr_bits])
   apply simp
  apply (drule(3) pspace_no_overlap_obj_not_in_range)
  apply (simp add: field_simps)
  done

crunches update_cdt_list, set_cdt
  for st_tcb_at[wp]: "\<lambda>s. P (st_tcb_at t ts s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at T t s)"

lemma set_cap_ko_at_Endpoint[wp]:
  "set_cap cap slot \<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (fastforce simp: obj_at_def)
  done

lemma set_cdt_list_wp:
  "\<lbrace>\<lambda>s. P (cdt_list_update (\<lambda>_. cdtl) s)\<rbrace> set_cdt_list cdtl \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding set_cdt_list_def
  by wpsimp

global_interpretation set_cdt: schedulable_ipc_queues_pred_locale _ "set_cdt f"
  by unfold_locales (rule schedulable_ipc_queues_pred_lift'; wpsimp simp: sc_at_ppred_def)

lemma valid_blocked_thread_default_object_update:
  assumes v: "valid_blocked_thread_kh except nq nr queues rlq sa ct kh t"
  assumes t: "type \<noteq> Untyped"
  shows "valid_blocked_thread_kh except nq nr queues rlq sa ct (kh(p \<mapsto> default_object type dev o_bits dm)) t"
  using v
  by (cases type)
     (auto simp: t valid_blocked_thread_def
                 pred_map_simps opt_map_simps map_join_simps vs_heap_simps
                 default_object_def default_sched_context_def sc_active_def)

lemma valid_blocked_fold_update:
  "\<lbrakk> valid_blocked_except_set_kh S queues rlq sa ct kh; type \<noteq> Untyped \<rbrakk> \<Longrightarrow>
  valid_blocked_except_set_kh S queues rlq sa ct (foldr (\<lambda>p kh. kh(p \<mapsto> default_object type dev o_bits dm)) ptrs kh)"
  apply (induct ptrs; clarsimp simp: valid_blocked_except_set_2_def)
  by (drule spec, erule (1) valid_blocked_thread_default_object_update)

lemma retype_region_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> retype_region a b c d dev \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: retype_region_def)
  apply wp
  apply (clarsimp simp del: fun_upd_apply)
  apply (blast intro: valid_blocked_fold_update)
  done

lemma delete_objects_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> delete_objects a b \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wpsimp simp: detype_def wrap_ext_det_ext_ext_def do_machine_op_def)
  by (fastforce simp: valid_blocked_defs pred_map_simps opt_map_simps map_join_simps vs_heap_simps
               split: option.splits)

crunch valid_blocked[wp]: reset_untyped_cap "valid_blocked::'z::state_ext state \<Rightarrow> _"
  (wp: preemption_point_inv mapME_x_inv_wp crunch_wps simp: unless_def)

crunches retype_region, delete_objects
  for cur_sc[wp]: "\<lambda>(s). P (cur_sc s)"
  (simp: detype_def)

lemma reset_untyped_cap_cur_sc[wp]:
  "reset_untyped_cap slot \<lbrace>(\<lambda>s. P (cur_sc s))\<rbrace>"
  unfolding reset_untyped_cap_def
  by (wpsimp wp: mapME_x_wp_inv preemption_point_inv get_cap_wp)

lemma delete_objects_not_bound_sc_tcb_at[wp]:
  "delete_objects d f \<lbrace>\<lambda>s. \<not> bound_sc_tcb_at P t s\<rbrace>"
  unfolding delete_objects_def
  by (wpsimp wp: )

lemma reset_untyped_not_bound_sc_tcb_at[wp]:
  "reset_untyped_cap slot \<lbrace>\<lambda>s. \<not> bound_sc_tcb_at P t s\<rbrace>"
  unfolding reset_untyped_cap_def
  by (wpsimp wp: mapME_x_wp_inv preemption_point_inv hoare_drop_imp)

lemma cur_sc_chargeable_invoke_untypedE_R:
  "\<lbrace>cur_sc_tcb_only_sym_bound\<rbrace>
   invoke_untyped i
   -, \<lbrace>\<lambda>rv. cur_sc_tcb_only_sym_bound\<rbrace>"
  unfolding invoke_untyped_def
  apply wpsimp
    apply (rule valid_validE_E)
    apply (clarsimp simp: cur_sc_tcb_only_sym_bound_def tcb_at_kh_simps[symmetric])
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
      apply (rule valid_validE, wps)
      apply wpsimp
     apply wpsimp
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
     apply (rule valid_validE, wps)
     apply wpsimp
    apply wpsimp
   apply wpsimp
  apply clarsimp
  apply (simp only: cur_sc_tcb_only_sym_bound_def tcb_at_kh_simps[symmetric])
  done

context DetSchedAux_AI begin
lemma invoke_untyped_valid_blocked[wp]:
  "invoke_untyped ui \<lbrace>valid_blocked::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding invoke_untyped_def
  by (wpsimp wp: crunch_wps mapME_x_inv_wp simp: mapM_x_defsym crunch_simps unless_def)
end

lemma etcb_at_tcb_at_pred_map:
  "\<lbrakk> etcb_at P ref s; tcb_at ref s \<rbrakk> \<Longrightarrow> pred_map P (etcbs_of s) ref"
  by (fastforce elim!: etcb_at'_pred_map
                 simp: obj_at_kh_kheap_simps pred_map_simps vs_heap_simps is_tcb)

lemmas etcb_at_pred_tcb_at_pred_map =
  etcb_at_tcb_at_pred_map[OF _ pred_tcb_at_tcb_at[where P=Q for Q]]

(* FIXME: move *)
lemma heap_eq_x_pred_map_eq_lift:
  assumes "\<And>y. pred_map_eq y heap x = pred_map_eq y heap' x"
  shows "heap x = heap' x"
  apply (rule option_eqI)
   subgoal using assms by (fastforce simp: pred_map_eq_def pred_map_def)
  subgoal for y using assms[of y] by (fastforce simp: pred_map_eq_def pred_map_def)
  done

(* FIXME: move *)
lemma heap_eq_x_pred_map_lift:
  assumes "\<And>P. pred_map P heap x = pred_map P heap' x"
  shows "heap x = heap' x"
  using assms by (auto simp: pred_map_eq_def intro: heap_eq_x_pred_map_eq_lift[where x=x])

(* FIXME: move *)
lemma pred_map_compose':
  "pred_map P (map_project f m) = pred_map (P \<circ> f) m"
  by (fastforce simp: pred_map_compose)

lemma tcb_ready_times_of_eq_bound_sc_obj_tcb_at_lift:
  assumes "\<And>rt. bound_sc_obj_tcb_at (\<lambda>sc. sc_ready_time sc = rt) t s
                 = bound_sc_obj_tcb_at (\<lambda>sc. sc_ready_time sc = rt) t s'"
  shows "tcb_ready_times_of s t = tcb_ready_times_of s' t"
  apply (rule heap_eq_x_pred_map_eq_lift[where x=t], rename_tac rt)
  apply (clarsimp simp: tcb_sc_refill_cfgs_2_def sc_ready_times_2_def pred_map_eq_def pred_map_compose')
  apply (rule rsubst[where P="\<lambda>P. bound_sc_obj_tcb_at P t s = bound_sc_obj_tcb_at P t s'"])
  apply (rule_tac rt=rt in assms)
  by fastforce

\<comment> \<open>Used for retyping Untyped memory, including ASID pool creation. Retyping may destroy objects
    if the Untyped memory is reset. But under the invariants, destruction can only occur for objects
    which are not referenced by any caps.\<close>
lemma valid_sched_tcb_state_preservation_gen:
  assumes I: "\<And>s. I s \<Longrightarrow> ct_active s \<and> invs s"
  assumes st_tcb: "\<And>P t. \<lbrace>st_tcb_at P t and ex_nonz_cap_to t and I\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  assumes not_ipc_queued: "\<And>t. \<lbrace>\<lambda>s. \<not> st_tcb_at ipc_queued_thread_state t s \<and> I s\<rbrace>
                                f \<lbrace>\<lambda>_ s. \<not> st_tcb_at ipc_queued_thread_state t s\<rbrace>"
  assumes etcb_at:
    "\<And>P t. \<lbrace>etcb_at P t and I\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at (Not \<circ> inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  assumes bound_sc:
    "\<And>P t. \<lbrace>\<lambda>s. bound_sc_tcb_at P t s \<and> ex_nonz_cap_to t s \<and> I s\<rbrace> f \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  assumes sc_refill_cfg:
    "\<And>P p. \<lbrace>\<lambda>s. sc_refill_cfg_sc_at P p s \<and> ex_nonz_cap_to p s \<and> I s\<rbrace> f \<lbrace>\<lambda>rv. sc_refill_cfg_sc_at P p\<rbrace>"
  assumes cur_time: "\<And>P. \<lbrace>\<lambda>s. P (cur_time s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_time s)\<rbrace>"
  assumes cur_thread: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  assumes idle_thread: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  assumes valid_blocked: "\<lbrace>valid_blocked\<rbrace> f \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  assumes valid_idle: "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  assumes machine_time: "\<And>P. f \<lbrace>\<lambda>s. P (last_machine_time_of s)\<rbrace>"
  assumes valid_others:
    "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) (ready_queues s) (cur_domain s) (release_queue s)\<rbrace>
          f \<lbrace>\<lambda>r s. P (scheduler_action s) (ready_queues s) (cur_domain s) (release_queue s)\<rbrace>"
  shows "\<lbrace>valid_sched and I\<rbrace> f \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule validI, clarsimp simp: valid_sched_def)
  apply (frule I, elim conjE, frule invs_valid_idle, frule invs_iflive)
  apply (frule use_valid
         , rule_tac P="\<lambda>act ready dom release. act = scheduler_action s \<and> ready = ready_queues s
                                              \<and> dom = cur_domain s \<and> release = release_queue s"
           in valid_others
         , simp)
  apply (frule use_valid, rule_tac P="\<lambda>ct. ct = cur_time s" in cur_time, simp)
  apply (frule use_valid, rule_tac P="\<lambda>ct. ct = cur_thread s" in cur_thread, simp)
  apply (frule use_valid, rule_tac P="\<lambda>it. it = idle_thread s" in idle_thread, simp)
  apply (frule use_valid, rule_tac P="\<lambda>mt. mt = last_machine_time_of s" in machine_time, simp)
  apply (frule use_valid[OF _ valid_blocked], assumption)
  apply (frule use_valid[OF _ valid_idle], assumption)
  apply (rule_tac V="valid_ready_qs s'" in revcut_rl)
   subgoal for s rv s'
   apply (clarsimp simp: valid_ready_qs_def
                         pred_map2'_pred_maps obj_at_kh_kheap_simps[symmetric] pred_tcb_at_eq_commute)
   apply (drule spec | elim conjE exE | drule (1) bspec)+
   apply (rename_tac scp)
   apply (frule (1) runnable_nonz_cap_to)
   apply (frule use_valid[OF _ st_tcb], fastforce)
   apply (frule pred_map_etcb_at, frule use_valid[OF _ etcb_at], fastforce)
   apply (frule_tac s=s' and P'="Not \<circ> inactive" in st_tcb_weakenE, fastforce)
   apply (frule use_valid[OF _ bound_sc], fastforce)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def etcb_at_pred_tcb_at_pred_map)
   apply (frule (3) ex_nonz_cap_to_tcb_implies_ex_nonz_cap_to_sc)
   apply (frule use_valid, rule_tac p=scp in sc_refill_cfg, simp)
   by simp
  apply (rule_tac V="valid_release_q s'" in revcut_rl)
   subgoal for s rv s'
   apply (clarsimp simp: valid_release_q_def)
   apply (clarsimp simp: valid_release_q_def pred_map2'_pred_maps obj_at_kh_kheap_simps[symmetric]
                         pred_tcb_at_eq_commute)
   apply (rule conjI, clarsimp)
    apply (drule (1) bspec, elim conjE exE, rename_tac scp)
    apply (frule (1) runnable_nonz_cap_to)
    apply (frule use_valid[OF _ st_tcb], fastforce)
    apply (frule use_valid[OF _ bound_sc], fastforce)
    apply (clarsimp simp: pred_tcb_at_def[unfolded obj_at_def])
    apply (frule (3) ex_nonz_cap_to_tcb_implies_ex_nonz_cap_to_sc)
    apply (frule use_valid, rule_tac p=scp in sc_refill_cfg, simp)
    apply simp
   apply (erule sorted_release_q_2_eq_lift[THEN iffD1, rotated])
   apply (drule (1) bspec, clarsimp)
   apply (rule_tac V="\<exists>rt. bound_sc_obj_tcb_at (\<lambda>sc. sc_ready_time sc = rt) t s" in revcut_rl
          , fastforce simp: obj_at_kh_kheap_simps vs_all_heap_simps, clarsimp)
   apply (frule (1) runnable_nonz_cap_to)
   apply (frule use_valid,
          (rule_tac t=t and I=I and P="\<lambda>sc. sc_ready_time sc = rt" in bound_sc_obj_tcb_at_nonz_cap_lift
           ; simp add: I bound_sc sc_refill_cfg), simp)
   apply (rule tcb_ready_times_of_eq_bound_sc_obj_tcb_at_lift)
   by (auto simp: vs_all_heap_simps)
  apply (rule_tac V="valid_sched_action s'" in revcut_rl)
   subgoal for s rv s'
   apply (clarsimp simp: valid_sched_action_def is_activatable_def weak_valid_sched_action_def
                         switch_in_cur_domain_def in_cur_domain_def
                         pred_map2'_pred_maps obj_at_kh_kheap_simps[symmetric] pred_tcb_at_eq_commute)
   apply (case_tac "\<exists>t. scheduler_action s = switch_thread t"; clarsimp)
    subgoal for t scp
    apply (frule (1) runnable_nonz_cap_to)
    apply (frule use_valid[OF _ st_tcb], fastforce)
    apply (frule use_valid[OF _ etcb_at], fastforce)
    apply (frule_tac s=s' and P'="Not \<circ> inactive" in st_tcb_weakenE, fastforce)
    apply (frule use_valid[OF _ bound_sc], fastforce)
    apply (clarsimp simp: pred_tcb_at_def[unfolded obj_at_def])
    apply (frule (3) ex_nonz_cap_to_tcb_implies_ex_nonz_cap_to_sc)
    apply (frule use_valid, rule_tac p=scp in sc_refill_cfg, simp)
    by simp
   apply (simp add: ct_in_state_def)
   apply (frule (1) runnable_nonz_cap_to[unfolded runnable_eq])
   apply (frule use_valid[OF _ st_tcb], fastforce)
   by (elim pred_tcb_weakenE disjE; fastforce)
  apply (rule_tac V="ct_in_cur_domain s'" in revcut_rl)
   subgoal for s rv s'
   apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_def)
   apply (simp add: ct_in_state_def)
   apply (frule (1) runnable_nonz_cap_to[unfolded runnable_eq])
   apply (frule use_valid[OF _ st_tcb], fastforce)
   apply (frule use_valid[OF _ etcb_at], fastforce)
   apply (frule_tac s=s' and P'="Not \<circ> inactive" in st_tcb_weakenE, fastforce)
   by simp
  apply (rule_tac V="valid_idle_etcb s'" in revcut_rl)
   subgoal for s rv s'
   apply (clarsimp simp: valid_idle_etcb_def)
   apply (frule use_valid[OF _ etcb_at], fastforce, erule mp)
   by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (rule_tac V="schedulable_ipc_queues s'" in revcut_rl)
   subgoal for s rv s'
   apply (simp add: schedulable_ipc_queues_defs
                    pred_map2'_pred_maps obj_at_kh_kheap_simps[symmetric] pred_tcb_at_eq_commute)
   apply (erule allEI, rule impI)
   apply ((rule_tac V="st_tcb_at ipc_queued_thread_state t s" in revcut_rl, rule ccontr
           , frule use_valid, rule_tac t=t in not_ipc_queued); simp)
   apply (frule (1) st_tcb_ex_cap, (case_tac st; clarsimp simp: ipc_queued_thread_state_def))
   apply (erule disjEI, (frule use_valid[OF _ bound_sc]; fastforce))
   apply (elim exE conjE, rename_tac p)
   apply (frule use_valid[OF _ bound_sc], fastforce)
   apply (clarsimp simp: pred_tcb_at_def[unfolded obj_at_def])
   apply (frule (3) ex_nonz_cap_to_tcb_implies_ex_nonz_cap_to_sc)
   apply (frule use_valid, rule_tac p=p in sc_refill_cfg, simp)
   by simp
  by simp

(* sorted_release_q lemmas *)
(* FIXME: I don't think these belong here, and are probably unnecessary once we
          have stronger rules in DetSchedSchedule_AI. *)
(*
crunches set_thread_state_act
for sorted_release_q[wp]: "sorted_release_q::det_state \<Rightarrow> _"
 (wp: crunch_wps hoare_drop_imp simp: crunch_simps)

lemma set_thread_state_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q and not_in_release_q tp and valid_release_q\<rbrace>
      set_thread_state tp st
   \<lbrace>\<lambda>rv. sorted_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_thread_state_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_release_q_def not_in_release_q_def
        split: option.splits dest!: get_tcb_SomeD)
  by solve_sorted_release_q

lemma set_simple_ko_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q and valid_release_q\<rbrace> set_simple_ko C ref new
            \<lbrace>\<lambda>_. sorted_release_q\<rbrace> "
  apply (clarsimp simp: set_simple_ko_def)
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: partial_inv_def a_type_def split: kernel_object.splits)
  apply (clarsimp simp: valid_release_q_def)
  by (intro conjI impI allI; clarsimp; solve_sorted_release_q)

lemma update_sk_obj_ref_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q and valid_release_q\<rbrace> update_sk_obj_ref C f ref new
            \<lbrace>\<lambda>_. sorted_release_q\<rbrace> "
  by (wpsimp simp: update_sk_obj_ref_def)

lemma set_sc_replies_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q and valid_release_q\<rbrace>
   set_sc_obj_ref sc_replies_update ref list \<lbrace>\<lambda>_. sorted_release_q\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  by (clarsimp simp: valid_release_q_def obj_at_def) solve_sorted_release_q

lemma sc_replies_update_tcb_ready_time_inv'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
       set_sc_obj_ref sc_replies_update scptr new
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

lemma set_simple_ko_tcb_ready_time_inv'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
       set_simple_ko f ptr ep
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def set_object_def
                  wp: get_object_wp)
  by (safe; clarsimp simp: partial_inv_def a_type_def obj_at_def
                   tcb_ready_time_ep_update[simplified obj_at_def is_ep fun_upd_def]
                   tcb_ready_time_reply_update[simplified obj_at_def is_reply fun_upd_def]
                   tcb_ready_time_ntfn_update[simplified obj_at_def is_ntfn fun_upd_def]
           split: option.splits if_split_asm kernel_object.splits)

crunches store_word_offs,create_cap_ext,set_cdt,do_machine_op,cap_insert_ext
for tcb_ready_time_inv'[wp]: "\<lambda>s. P (tcb_ready_time t s)"

lemma set_cap_tcb_ready_time_inv'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
       set_cap cap slot
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_cap_def set_object_def wp: get_object_wp)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

lemma thread_set_valid_release_ready_time_inv'[wp]:
  "\<lbrakk> \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
    thread_set f tptr
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (clarsimp simp: thread_set_def)
  apply (wpsimp simp: set_object_def)
  by (fastforce elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                simp: get_tcb_def tcb_ready_time_def split: option.splits)

lemma set_mrs_tcb_ready_time_inv'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
    set_mrs thread buf msgs
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_mrs_def set_object_def zipWithM_x_mapM wp: mapM_wp' get_object_wp
                split_del: if_split)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

crunches set_simple_ko, set_cap, set_mrs,create_cap_ext
for tcb_ready_time_inv[wp]: "\<lambda>s. P (tcb_ready_time t s)(tcb_ready_time t' s)"
  (rule: release_queue_cmp_lift)

lemma sc_replies_update_tcb_ready_time_inv[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)(tcb_ready_time t' s)\<rbrace>
       set_sc_obj_ref sc_replies_update scptr new
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)(tcb_ready_time t' s)\<rbrace>"
  by (rule hoare_lift_Pf3[where f="\<lambda>s. tcb_ready_time t' s"]; wpsimp)

lemma thread_set_valid_release_ready_time_inv[wp]:
  "\<lbrakk>\<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (tcb_ready_time t s)(tcb_ready_time t' s)\<rbrace>
    thread_set f tptr
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)(tcb_ready_time t' s)\<rbrace>"
  by (rule release_queue_cmp_lift; wpsimp)

crunches cap_insert
for tcb_ready_time_inv'[wp]: "\<lambda>s::det_state. P (tcb_ready_time t s)"
  (wp: crunch_wps simp: crunch_simps)

crunches create_cap, update_cdt
  for tcb_ready_time_inv'[wp]: "\<lambda>s::det_state. P (tcb_ready_time t s)"
  and sorted_release_q[wp]: "\<lambda>s::det_state. sorted_release_q s"
  and valid_release_q[wp]: "\<lambda>s::det_state. valid_release_q s"
    (wp: crunch_wps simp: crunch_simps)

crunches set_untyped_cap_as_full
for valid_release_q[wp]: valid_release_q

lemma cap_insert_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace>
   cap_insert new_cap src_slot dest_slot \<lbrace>\<lambda>_ . valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: cap_insert_def update_sched_context_def set_object_def
                  wp: get_object_wp hoare_drop_imp simp_del: fun_upd_apply)
*)

lemma invoke_untyped_valid_idle:
  "\<lbrace>invs and ct_active
         and valid_untyped_inv ui
         and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (strengthen invs_valid_idle) (wpsimp wp: invoke_untyp_invs)

(* FIXME: move to arch assumption in Retype_AI *)
lemma hyp_live_default_object:
  "ty \<noteq> Untyped \<Longrightarrow> \<not> hyp_live (default_object ty dev us dm)"
  by (cases ty; simp add: ARM.hyp_live_def)

(* FIXME: move to Retype_AI *)
lemma live0_default_object:
  "ty \<noteq> Untyped \<Longrightarrow> \<not> live0 (default_object ty dev us dm)"
  by (cases ty
      ; simp add: live_ntfn_def live_sc_def live_reply_def
                  default_object_def default_tcb_def default_ep_def default_notification_def
                  default_ntfn_def default_sched_context_def default_reply_def)

(* FIXME: move to Retype_AI *)
lemma live_default_object:
  notes pre = hyp_live_default_object live0_default_object
  assumes "ty \<noteq> Untyped"
  shows "\<not> live (default_object ty dev us dm)"
  using pre[where dev=dev and us=us and dm=dm, OF assms]
  by (simp only: live_def split: kernel_object.splits; simp)

(* FIXME: move to Untyped_AI *)
lemma retype_region_obj_at_live_ex:
  assumes live: "\<forall>ko. P ko \<longrightarrow> live ko"
  shows "\<lbrace>\<lambda>s. N (obj_at P p s)
              \<and> pspace_aligned s
              \<and> valid_objs s
              \<and> (\<exists>sz. pspace_no_overlap (up_aligned_area ptr sz) s
                      \<and> range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
         retype_region ptr n us ty dev
         \<lbrace>\<lambda>rv s. N (obj_at P p s)\<rbrace>"
  unfolding retype_region_def foldr_upd_app_if
  apply (wpsimp simp: retype_region_def)
  apply (erule rsubst[of N])
  apply (rule iffI)
   apply (frule (3) pspace_no_overlap_obj_not_in_range
          , frule retype_addrs_subset_ptr_bits
          , erule contrapos_np[where Q="p \<in> _"]
          , erule subsetD
          , erule contrapos_np[where Q="obj_at _ _ _"])
   apply (clarsimp simp: obj_at_def retype_addrs_def)
  by (clarsimp simp: obj_at_def live_default_object
              dest!: live[THEN spec, THEN mp]
              split: if_splits)

lemma retype_region_obj_at_live:
  assumes live: "\<forall>ko. P ko \<longrightarrow> live ko"
  shows "\<lbrace>\<lambda>s. N (obj_at P p s)
              \<and> pspace_aligned s
              \<and> valid_objs s
              \<and> pspace_no_overlap (up_aligned_area ptr sz) s
              \<and> range_cover ptr sz (obj_bits_api ty us) n\<rbrace>
         retype_region ptr n us ty dev
         \<lbrace>\<lambda>rv s. N (obj_at P p s)\<rbrace>"
  by (wpsimp wp: retype_region_obj_at_live_ex[OF live]) fastforce

(* FIXME: move *)
lemma preemption_point_obj_at:
  "preemption_point \<lbrace>\<lambda>s. N (obj_at P p s)\<rbrace>"
  by (wpsimp simp: preemption_point_def wp: OR_choiceE_weak_wp dxo_wp_weak)

(* FIXME: move *)
lemma is_untyped_cap_UntypedCap:
  "is_untyped_cap (UntypedCap dev base sz free)"
  by simp

(* FIXME: move to Untyped_AI *)
lemma reset_untyped_cap_obj_at_live:
  assumes csp: "cspace_agnostic_pred P"
  assumes live: "\<forall>ko. P ko \<longrightarrow> live ko"
  shows "\<lbrace>\<lambda>s. N (obj_at P p s)
              \<and> cte_wp_at is_untyped_cap slot s
              \<and> descendants_of slot (cdt s) = {}
              \<and> invs s\<rbrace>
         reset_untyped_cap slot
         \<lbrace>\<lambda>rv s. N (obj_at P p s)\<rbrace>"
  apply (wpsimp wp: set_cap.cspace_agnostic_obj_at[OF csp]
                    mapME_x_wp' get_cap_wp hoare_drop_imp preemption_point_obj_at
              simp: reset_untyped_cap_def delete_objects_def)
  apply (erule rsubst[of N]; rule iffI; clarsimp simp: cte_wp_at_caps_of_state)
  apply (case_tac cap
         ; clarsimp simp: obj_at_def free_index_of_def bits_of_def
         ; rename_tac dev base sz free ko
         ; drule live[THEN spec, THEN mp])
  apply (frule (2) if_live_then_nonz_cap_invs)
  apply (frule (3) descendants_of_empty_untyped_range[OF _ _ _ is_untyped_cap_UntypedCap])
  by simp

(* FIXME: move to Untyped_AI *)
lemma invoke_untyped_obj_at_live:
  assumes csp: "cspace_agnostic_pred P"
  assumes live: "\<forall>ko. P ko \<longrightarrow> live ko"
  shows
  "\<lbrace>\<lambda>s. N (obj_at P p s)
        \<and> invs s
        \<and> ct_active s
        \<and> valid_untyped_inv ui s
        \<and> scheduler_action s = resume_cur_thread\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>rv s. N (obj_at P p s)\<rbrace>"
  by (wpsimp wp: invoke_untyped_Q
                 reset_untyped_cap_obj_at_live[OF csp live]
                 retype_region_obj_at_live_ex[OF live]
                 init_arch_objects_obj_at_live[OF live]
                 create_cap.cspace_agnostic_obj_at[OF csp]
                 set_cap.cspace_agnostic_obj_at[OF csp]
           simp: cte_wp_at_caps_of_state
          split: untyped_invocation.splits
      | fastforce)+

(* FIXME: move to Untyped_AI *)
lemma invoke_untyped_pred_tcb_at_live:
  assumes live: "\<forall>tcb. P (proj (tcb_to_itcb tcb)) \<longrightarrow> live (TCB tcb)"
  shows
  "\<lbrace>\<lambda>s. N (pred_tcb_at proj P p s)
        \<and> invs s
        \<and> ct_active s
        \<and> valid_untyped_inv ui s
        \<and> scheduler_action s = resume_cur_thread\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>rv s. N (pred_tcb_at proj P p s)\<rbrace>"
  unfolding pred_tcb_at_def using live
  by (auto intro!: invoke_untyped_obj_at_live simp: cspace_agnostic_pred_def tcb_to_itcb_def)

lemma ipc_queued_thread_state_live:
  "ipc_queued_thread_state (tcb_state tcb) \<Longrightarrow> live (TCB tcb)"
  by (cases "tcb_state tcb"; simp add: ipc_queued_thread_state_def live_def)

lemma (in DetSchedAux_AI) invoke_untyped_valid_sched:
  "\<lbrace>valid_sched and invs and ct_active and valid_untyped_inv ui and
    (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>rv . valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply wp_pre
   apply (rule_tac I="invs and ct_active and valid_untyped_inv ui and
                      (\<lambda>s. scheduler_action s = resume_cur_thread)"
            in valid_sched_tcb_state_preservation_gen)
               apply simp
              apply (wpsimp wp: invoke_untyped_st_tcb_at)
             apply (wpsimp wp: invoke_untyped_pred_tcb_at_live simp: ipc_queued_thread_state_live)
            apply (wpsimp wp: invoke_untyped_etcb_at)
           apply wpsimp
          apply (wpsimp wp: invoke_untyped_sc_at_pred_n)
         apply wp
        apply wp
       apply wp
      apply wp
     apply (wp invoke_untyped_valid_idle)
    apply wp
   apply (rule hoare_lift_Pf[where f=scheduler_action, OF _ invoke_untyped_valid_sched_pred_misc])
   apply (rule hoare_lift_Pf[where f=ready_queues, OF _ invoke_untyped_valid_sched_pred_misc])
   apply (rule hoare_lift_Pf[where f=cur_domain, OF _ invoke_untyped_valid_sched_pred_misc])
   apply (rule invoke_untyped_valid_sched_pred_misc)
  by clarsimp

\<comment> \<open>Miscellaneous\<close>

lemma weak_valid_sched_action_switch_thread_is_schedulable:
  "\<lbrakk>weak_valid_sched_action s; scheduler_action s = switch_thread thread\<rbrakk> \<Longrightarrow>
     is_schedulable_opt thread (in_release_queue thread s) s = Some True"
  by (auto simp: weak_valid_sched_action_def is_schedulable_opt_def in_release_queue_def
                 obj_at_kh_kheap_simps pred_map_simps map_join_simps vs_heap_simps
          split: option.splits )

lemma valid_sched_action_weak_valid_sched_action:
  "valid_sched_action s \<Longrightarrow> weak_valid_sched_action s"
  by (simp add: valid_sched_action_def)

lemmas valid_sched_weak_valid_sched_action =
  valid_sched_valid_sched_action[THEN valid_sched_action_weak_valid_sched_action]

lemmas valid_sched_switch_thread_is_schedulable =
  weak_valid_sched_action_switch_thread_is_schedulable[OF valid_sched_weak_valid_sched_action]

lemma simple_sched_act_not[simp]:
  "simple_sched_action s \<Longrightarrow> scheduler_act_not t s"
  by (clarsimp simp: simple_sched_action_def scheduler_act_not_def)

lemma set_tcb_queue_wp:
  "\<lbrace>\<lambda>s. P (ready_queues_update (\<lambda>qs d p. if d = t \<and> p = prio then queue else qs d p) s)\<rbrace>
   set_tcb_queue t prio queue
   \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: set_tcb_queue_def) (auto elim!: rsubst[of P])

lemma get_tcb_queue_wp: "\<lbrace>\<lambda>s. P (ready_queues s t p) s\<rbrace> get_tcb_queue t p \<lbrace>P\<rbrace>"
  by (wpsimp simp: get_tcb_queue_def)

lemma get_tcb_queue_inv[wp]:
  "get_tcb_queue t p \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp wp: get_tcb_queue_wp)

lemma enqueue_distinct[intro!]: "distinct queue \<Longrightarrow> distinct (tcb_sched_enqueue thread queue)"
  by (simp add: tcb_sched_enqueue_def)

lemma is_activatable_trivs[iff]:
  "is_activatable_2 ct (switch_thread t) kh"
  "is_activatable_2 ct choose_new_thread kh"
  by (simp_all add: is_activatable_def)

lemma weak_valid_sched_action_trivs[iff]:
  "weak_valid_sched_action_2 except curtime resume_cur_thread rq tcb_sts tcb_scps sc_refill_cfgs"
  "weak_valid_sched_action_2 except curtime choose_new_thread rq tcb_sts tcb_scps sc_refill_cfgs"
  by (simp_all add: weak_valid_sched_action_def)

lemma switch_in_cur_domain_trivs[iff]:
  "switch_in_cur_domain_2 resume_cur_thread ekh cdom"
  "switch_in_cur_domain_2 choose_new_thread ekh cdom"
  by (simp_all add: switch_in_cur_domain_def)

lemma ct_in_cur_domain_2_trivs[iff]:
  "ct_in_cur_domain_2 thread thread' (switch_thread t) cdom ekh"
  "ct_in_cur_domain_2 thread thread' choose_new_thread cdom ekh"
  by (simp_all add: ct_in_cur_domain_2_def)

lemma valid_sched_action_triv[iff]:
  "valid_sched_action_2 weak_vsa except curtime choose_new_thread ct cdom rlq ekh tcb_sts tcb_scps sc_refill_cfgs"
  by (simp add: valid_sched_action_def)

lemma simple_sched_action_trivs[iff]:
  "simple_sched_action_2 resume_cur_thread"
  "simple_sched_action_2 choose_new_thread"
  by (simp_all add: simple_sched_action_def)

lemma scheduler_act_not_trivs[iff]:
  "scheduler_act_not_2 resume_cur_thread t"
  "scheduler_act_not_2 choose_new_thread t"
  by (simp_all add: scheduler_act_not_def)

lemma ko_at_etcbD:
  "ko_at (TCB tcb) t s \<Longrightarrow> etcbs_of s t = Some (etcb_of tcb)"
  by (simp add: obj_at_def vs_heap_simps)

lemma etcb_of_eq:
  "(etcb_of t = etcb_of t') = (tcb_priority t = tcb_priority t' \<and> tcb_domain t = tcb_domain t')"
  by (simp add: etcb_of_def)

lemmas thread_get_prio_wp = thread_get_wp' [where f=tcb_priority]
lemmas thread_get_dom_wp = thread_get_wp' [where f=tcb_domain]

(* FIXME: remove, since now redundant with vs_all_heap_simps *)
lemma etcbs_of_update_unrelated:
  "\<lbrakk> kh ref = Some (TCB tcb); etcb_of tcb = etcb_of tcb' \<rbrakk> \<Longrightarrow>
  etcbs_of_kh (\<lambda>r. if r = ref then Some (TCB tcb') else kh r) = etcbs_of_kh kh"
  by (auto simp: vs_all_heap_simps)

(* FIXME: remove, since now redundant with vs_all_heap_simps *)
lemma etcbs_of_update_state:
  "get_tcb ref s = Some tcb \<Longrightarrow>
  etcbs_of_kh (\<lambda>r. if r = ref then Some (TCB (tcb_state_update f tcb)) else kheap s r) = etcbs_of_kh (kheap s)"
  by (auto simp: vs_all_heap_simps obj_at_kh_kheap_simps)

(* FIXME: remove, since now redundant with vs_all_heap_simps *)
lemma etcbs_of_arch_state:
  "get_tcb ref s = Some tcb \<Longrightarrow>
  etcbs_of_kh (\<lambda>r. if r = ref then Some (TCB (tcb_arch_update f tcb)) else kheap s r) = etcbs_of_kh (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

lemma ct_in_q_valid_blocked_ct_upd:
  "\<lbrakk>ct_in_q s; valid_blocked s\<rbrakk> \<Longrightarrow> valid_blocked (s\<lparr>cur_thread := thread\<rparr>)"
  by (auto simp: valid_blocked_defs ct_in_q_def runnable_eq_active)

lemma valid_ready_qs_trivial[simp]:
  "valid_ready_qs_2 (\<lambda>_ _. []) ctime etcbs tcb_sts tcb_scps sc_refill_cfgs"
  by (simp add: valid_ready_qs_def)

lemma sorted_release_trivial[simp]: "sorted_release_q_2 tcb_sc_refill_cfgs []"
  by (simp add: sorted_release_q_def)

lemma valid_release_trivial[simp]: "valid_release_q_2 [] tcb_sts tcb_scps sc_refill_cfgs"
  by (simp add: valid_release_q_def)

lemma ct_not_in_q_trivial[simp]: "ct_not_in_q_2 (\<lambda>_ _. []) sa ct"
  by (simp add: ct_not_in_q_def not_queued_2_def)

lemma st_tcb_at_get_lift:
  "get_tcb thread s = Some y \<Longrightarrow> test (tcb_state y) \<Longrightarrow> st_tcb_at test thread s"
  by (simp add: ct_in_state_def st_tcb_def2)

lemmas det_ext_simps[simp] = select_switch_det_ext_ext_def unwrap_ext_det_ext_ext_def

(* FIXME: remove unused *)
(*
lemma next_thread_update:
  assumes a: "P(next_thread queues)"
  assumes b: "P t"
  shows
    "P(next_thread (queues((p :: word8) := t # (queues prio))))"
proof -
  have imp_comp[simp]: "\<And>P Q. {x. P x \<longrightarrow> Q x} = {x. \<not> P x} \<union> {x. Q x}" by blast
  { assume c: "{prio. queues prio \<noteq> []} = {}"
    from a b c have ?thesis
      by (simp add: next_thread_def max_non_empty_queue_def)
  }
  moreover
  { assume d: "{prio. queues prio \<noteq> []} \<noteq> {}"
    from a b have ?thesis
      apply (clarsimp simp: next_thread_def
                            max_non_empty_queue_def
                            Max_insert[OF finite_word d])
      apply (clarsimp simp add: max_def)
      done
  }
  ultimately show ?thesis by blast
qed
*)

lemma next_thread_queued: "queues p \<noteq> [] \<Longrightarrow> \<exists>p. next_thread queues \<in> set (queues p)"
  apply (clarsimp simp: next_thread_def max_non_empty_queue_def)
  apply (rule_tac x="Max {prio. queues prio \<noteq> []}" in exI)
  apply (rule Max_prop)
   apply simp
  apply blast
  done

lemma etcbs_of'_non_tcb_update:
  "\<lbrakk> kh ref = Some obj'; a_type obj = a_type obj'; a_type obj \<noteq> ATCB \<rbrakk> \<Longrightarrow>
   etcbs_of_kh (\<lambda>a. if a = ref then Some obj else kh a) = etcbs_of_kh kh"
  by (cases obj; cases obj'; clarsimp simp: vs_all_heap_simps)

lemma ct_not_in_q_def2:
  "ct_not_in_q_2 queues sa ct \<equiv> sa = resume_cur_thread \<longrightarrow> (\<forall>d p. ct \<notin> set (queues d p))"
  by (fastforce simp add: ct_not_in_q_def not_queued_2_def)

lemma ball_mapM_scheme:  (* maybe move? is this generic enough? *)
  assumes x: "\<And>t t'. \<lbrace> \<lambda>s. Q t' s \<and> t' \<noteq> t \<rbrace> f t \<lbrace> \<lambda>_. Q t' \<rbrace>"
  and y:  "\<And>t. \<lbrace> Q t and P \<rbrace> f t \<lbrace>\<lambda>_. P \<rbrace>"
  shows "distinct xs \<Longrightarrow> \<lbrace> (\<lambda>s. \<forall>t\<in>set xs. Q t s) and P\<rbrace> mapM (\<lambda>t. f t) xs \<lbrace>\<lambda>_. P\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  apply (wpsimp wp: hoare_vcg_ball_lift x y)
  done

lemma ball_mapM_x_scheme:
  assumes x: "\<And>t t'. \<lbrace> \<lambda>s. Q t' s \<and> t' \<noteq> t \<rbrace> f t \<lbrace> \<lambda>_. Q t' \<rbrace>"
  and y:  "\<And>t. \<lbrace> Q t and P \<rbrace> f t \<lbrace>\<lambda>_. P \<rbrace>"
  shows "distinct xs \<Longrightarrow> \<lbrace> (\<lambda>s. \<forall>t\<in>set xs. Q t s) and P\<rbrace> mapM_x (\<lambda>t. f t) xs \<lbrace>\<lambda>_. P\<rbrace>"
  by (subst mapM_x_mapM) (wp ball_mapM_scheme x y)

lemma ball_filterM_scheme:
  assumes x: "\<And>t t'. \<lbrace> \<lambda>s. Q t' s \<and> t' \<noteq> t \<rbrace> f t \<lbrace> \<lambda>_. Q t' \<rbrace>"
  and y:  "\<And>t. \<lbrace> Q t and P \<rbrace> f t \<lbrace>\<lambda>_. P \<rbrace>"
  shows "distinct xs \<Longrightarrow> \<lbrace> (\<lambda>s. \<forall>t\<in>set xs. Q t s) and P\<rbrace> filterM f xs \<lbrace>\<lambda>_. P\<rbrace>"
  by (subst filterM_mapM) (wpsimp wp: ball_mapM_scheme[where Q=Q] x y)

(* FIXME: Move *)
lemma st_tcb_reply_state_refs:
  "\<lbrakk>valid_objs s; sym_refs (state_refs_of s); st_tcb_at ((=) (BlockedOnReply rp)) thread s\<rbrakk>
  \<Longrightarrow> \<exists>reply. (kheap s rp = Some (Reply reply) \<and> reply_tcb reply = Some thread)"
  apply (frule (1) st_tcb_at_valid_st2)
  apply (drule (1) sym_refs_st_tcb_atD[rotated])
  apply (clarsimp simp: get_refs_def2 obj_at_def valid_tcb_state_def is_reply
                  split: thread_state.splits if_splits)
  done

(* FIXME move *)
lemma set_filter_all[simp]: "set (filter (\<lambda>x. P x) xs @ filter (\<lambda>x. \<not> P x) xs) = set xs" by auto

(* FIXME move *)
lemma mapM_length_eq:
  "\<lbrace>\<top>\<rbrace> mapM f xs \<lbrace>\<lambda>rv. K (length xs = length rv)\<rbrace>"
  apply (induct xs, wpsimp simp: mapM_Nil)
  by (wpsimp simp: mapM_Cons mapM_def sequence_def|assumption)+

(* FIXME move *)
lemma mapM_wp_inv_length:
  "(\<And>x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv s. P s \<and> (length xs = length rv)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_vcg_conj_lift[OF _ mapM_length_eq[simplified]])
   apply (wpsimp wp: mapM_wp_inv, auto)
  done

(* FIXME move *)
lemma length_eq_pair_in_set_zip:
  "length qs = length r \<Longrightarrow> x \<in> set qs \<Longrightarrow> \<exists>b. (x, b) \<in> set (zip qs r)"
  apply (induct qs arbitrary: r; simp)
  apply (safe; case_tac r; fastforce)
  done

lemma in_release_queue_in_release_q:
  "in_release_queue t = in_release_q t"
  by (clarsimp simp: in_release_queue_def in_release_q_def)

(* FIXME: Move *)
lemma distinct_takeWhle:
   "\<lbrakk>distinct ls; t \<in> set (takeWhile P ls)\<rbrakk>
    \<Longrightarrow> t \<notin> set (drop (length (takeWhile P ls)) ls)"
  apply (subst dropWhile_eq_drop[symmetric])
  apply (subgoal_tac "distinct ((takeWhile P ls) @ (dropWhile P ls))")
   apply (simp only: distinct_append, fastforce)
  apply fastforce
  done

(* FIXME: Move *)
lemma distinct_not_in_takeWhile:
   "\<lbrakk>distinct ls; t \<in> set ls; t \<notin> set (takeWhile P ls)\<rbrakk>
    \<Longrightarrow> t \<in> set (drop (length (takeWhile P ls)) ls)"
  apply (subst dropWhile_eq_drop[symmetric])
  apply (subgoal_tac "distinct ((takeWhile P ls) @ (dropWhile P ls))")
   apply (simp only: distinct_append, elim conjE)
   apply (subgoal_tac "set ls = set (takeWhile P ls) \<union> set (dropWhile P ls)")
    apply fastforce
   apply (subst takeWhile_dropWhile_id[symmetric, of _ P])
   apply (subst set_append, auto)
  done

(* FIXME: Move *)
lemma dropWhile_dropped_P:
  "\<lbrakk>x \<in> set queue; x \<notin> set (dropWhile P queue)\<rbrakk> \<Longrightarrow> P x"
  by (induction queue arbitrary: x; fastforce split: if_split_asm)

(* FIXME: Move *)
lemma takeWhile_taken_P:
  "x \<in> set (takeWhile P queue) \<Longrightarrow> P x"
  by (induction queue arbitrary: x; fastforce split: if_split_asm)

(* FIXME: remove *)
lemmas hoare_vcg_imp_lift''
  = hoare_vcg_imp_lift_N[where N="\<lambda>P. P" and P=P' and Q=P and P'=Q' and Q'=Q for P' P Q' Q]

(* FIXME: move *)
lemma valid_objs_SendEP_distinct:
  "valid_objs s
   \<Longrightarrow> (kheap s epptr = Some (Endpoint (SendEP epqueue)))
   \<Longrightarrow> distinct epqueue"
  apply (clarsimp simp: valid_objs_def dom_def valid_obj_def)
  apply (fastforce simp: valid_ep_def)
  done

(* FIXME: move *)
lemma valid_objs_RecvEP_distinct:
  "valid_objs s
   \<Longrightarrow> (kheap s epptr = Some (Endpoint (RecvEP epqueue)))
   \<Longrightarrow> distinct epqueue"
  apply (clarsimp simp: valid_objs_def dom_def valid_obj_def)
  apply (fastforce simp: valid_ep_def)
  done

(* FIXME: move *)
lemma valid_objs_WaitingNtfn_distinct:
  "valid_objs s
   \<Longrightarrow> (kheap s xa = Some (Notification notif))
   \<Longrightarrow> ntfn_obj notif = WaitingNtfn x2
   \<Longrightarrow> distinct x2"
  apply (clarsimp simp: valid_objs_def dom_def valid_obj_def)
  apply (fastforce simp: valid_ntfn_def)
  done

lemma valid_sched_not_runnable_not_in_release_q:
  "\<lbrakk>valid_sched s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_in_release_q tptr s"
  by (auto simp: valid_sched_def valid_release_q_def obj_at_kh_kheap_simps
                 not_queued_def not_in_release_q_def vs_all_heap_simps)

lemma valid_sched_not_runnable_not_queued:
  "\<lbrakk>valid_sched s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_queued tptr s"
  apply (clarsimp simp: valid_sched_def valid_ready_qs_def obj_at_kh_kheap_simps
                        not_queued_def vs_all_heap_simps runnable_eq_active)
  by fastforce

lemma valid_blocked_except_set_no_active_sc_sum:
  "valid_blocked_except_set {tcbptr} s
   \<Longrightarrow> \<not> active_sc_tcb_at tcbptr s
   \<Longrightarrow> valid_blocked s"
  by (auto simp: valid_blocked_defs)

lemma not_not_in_eq_in: "\<not> not_in_release_q t s \<longleftrightarrow> in_release_queue t s"
  by (clarsimp simp: in_release_queue_def not_in_release_q_def)

lemma valid_blocked_except_set_in_release_queue_sum:
  "valid_blocked_except_set {tcbptr} s
   \<Longrightarrow> in_release_queue tcbptr s
   \<Longrightarrow> valid_blocked s"
  apply (clarsimp simp: valid_blocked_defs)
  apply (case_tac "t = tcbptr")
   apply (fastforce iff: not_not_in_eq_in[symmetric])
  apply (drule_tac x=t in spec; simp)
  done

lemma schedulable_unfold2:
  "((is_schedulable_opt tp b s) = Some X)
   \<Longrightarrow> tcb_at tp s
   \<Longrightarrow> (X = (st_tcb_at runnable tp s \<and> active_sc_tcb_at  tp s \<and> \<not>b))"
  by (clarsimp simp: is_schedulable_opt_def obj_at_kh_kheap_simps vs_all_heap_simps
              split: option.splits)

lemma test_sc_refill_max_detype[simp]:
  "(test_sc_refill_max t (detype S s))
    = (test_sc_refill_max t s \<and> t \<notin> S)"
  by (clarsimp simp add: test_sc_refill_max_def detype_def)

lemma bound_sc_obj_tcb_at_detype:
  "bound_sc_obj_tcb_at (P s) t (detype S s)
    \<longleftrightarrow> bound_sc_obj_tcb_at (P s) t s
        \<and> bound_sc_tcb_at (case_option True (\<lambda>scp. scp \<notin> S)) t s
        \<and> t \<notin> S"
  by (fastforce simp: pred_map2'_pred_maps vs_all_heap_simps obj_at_kh_kheap_simps)

lemmas bound_sc_obj_tcb_at_cur_time_detype[simp] =
  bound_sc_obj_tcb_at_detype[where P="\<lambda>s. P (cur_time s)" for P]

(* FIXME: move *)
lemma clear_um_cur_time[iff]:
  "cur_time (clear_um S s) = cur_time s"
  by (simp add: clear_um_def)

lemma bound_sc_obj_tcb_at_kh_update_kh_trivial[simp]:
  assumes "\<And>sc n tcb. Some ` {SchedContext sc n, TCB tcb} \<inter> {kh p, Some ko'} = {}"
  shows "bound_sc_obj_tcb_at_kh P (kh(p \<mapsto> ko')) t = bound_sc_obj_tcb_at_kh P kh t"
  using assms
  by (auto simp: pred_map2'_pred_maps vs_all_heap_simps
         intro!: ex_cong[where Q=\<top>, simplified] conj_cong[OF refl])

lemmas bound_sc_obj_tcb_at_kh_update_kh_trivial'[simp] =
  bound_sc_obj_tcb_at_kh_update_kh_trivial[unfolded fun_upd_def]

lemma typ_at_pred_tcb_at_lift:
  assumes typ_lift: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>r s. P (typ_at T p s)\<rbrace>"
  assumes pred_lift: "\<And>P. \<lbrace>pred_tcb_at proj P t\<rbrace> f \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> pred_tcb_at proj P t s\<rbrace> f \<lbrace>\<lambda>r s. \<not> pred_tcb_at proj P t s\<rbrace>"
  apply (simp add: valid_def obj_at_def pred_tcb_at_def)
  apply clarsimp
  apply (case_tac "kheap s t")
   apply (cut_tac P="\<lambda>x. \<not> x" and p=t and T="ATCB" in typ_lift)
   apply (simp add: valid_def obj_at_def)
   apply force
  apply (cut_tac P="\<lambda>x. x" and p=t and T="a_type aa" in typ_lift)
  apply (cut_tac P="\<lambda>t. \<not> P t" in pred_lift)
  apply (simp add: valid_def obj_at_def pred_tcb_at_def)
  apply (drule_tac x=s in spec)
  apply simp
  apply (drule_tac x="(a,b)" in bspec)
   apply simp
  apply simp
  apply (subgoal_tac "a_type aa = ATCB")
   apply (erule a_type_ATCBE)
   apply simp
   apply force
  apply simp
  done

lemma pred_map_f_kheap_detype:
  assumes "\<And>ko. f (\<lambda>x. if x \<in> S then None else kheap s x) scp = Some ko
                 \<longleftrightarrow> f (kheap s) scp = Some ko \<and> scp \<notin> S"
  shows "pred_map P (f (kheap (detype S s))) scp \<longleftrightarrow> pred_map P (f (kheap s)) scp \<and> scp \<notin> S"
  by (auto simp: detype_def pred_map_simps assms split: if_splits)

lemma pred_map_sc_refill_cfgs_of_detype[simp]:
  "pred_map P (sc_refill_cfgs_of (detype S s)) scp \<longleftrightarrow> pred_map P (sc_refill_cfgs_of s) scp \<and> scp \<notin> S"
  by (rule pred_map_f_kheap_detype; simp add: vs_all_heap_simps)

lemma pred_map_tcb_scps_of_detype[simp]:
  "pred_map P (tcb_scps_of (detype S s)) t \<longleftrightarrow> pred_map P (tcb_scps_of s) t \<and> t \<notin> S"
  by (rule pred_map_f_kheap_detype; simp add: vs_all_heap_simps)

lemma pred_map_tcb_sts_of_detype[simp]:
  "pred_map P (tcb_sts_of (detype S s)) t \<longleftrightarrow> pred_map P (tcb_sts_of s) t \<and> t \<notin> S"
  by (rule pred_map_f_kheap_detype; simp add: vs_all_heap_simps)

lemma pred_map_etcbs_of_detype[simp]:
  "pred_map P (etcbs_of (detype S s)) t \<longleftrightarrow> pred_map P (etcbs_of s) t \<and> t \<notin> S"
  by (rule pred_map_f_kheap_detype; simp add: vs_all_heap_simps)

declare clear_um.pspace[iff]

lemma ct_runnable_ct_not_blocked[elim!]:
  "ct_active s \<Longrightarrow> ct_not_blocked s"
  by (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def split: thread_state.splits)

end
