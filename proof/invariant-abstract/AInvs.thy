(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
The main theorem
*)

theory AInvs
imports "./$L4V_ARCH/ArchAInvsPre"
begin

lemma st_tcb_at_nostate_upd:
  "\<lbrakk> get_tcb t s = Some y; tcb_state y = tcb_state y' \<rbrakk> \<Longrightarrow>
  st_tcb_at P t' (s \<lparr>kheap := kheap s(t \<mapsto> TCB y')\<rparr>) = st_tcb_at P t' s"
  by (clarsimp simp add: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma pred_tcb_at_upd_apply:
  "pred_tcb_at proj P t (s\<lparr>kheap := p'\<rparr>) =
  pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(t := p' t)\<rparr>)"
  by (simp add: pred_tcb_at_def obj_at_def)

lemma thread_set_tcb_arch_is_schedulable_bool[wp]:
  "\<lbrace>\<lambda>s. is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s\<rbrace>
     thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set us (tcb_arch tcb)\<rparr>) t
   \<lbrace>\<lambda>rv s. is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s\<rbrace>"
  apply (simp add: thread_set_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp simp: set_object_def)
  apply (fastforce simp: is_schedulable_bool_def test_sc_refill_max_def get_tcb_def ko_atD
                         in_release_queue_def
                  split: option.splits )
  done

text \<open>The top-level invariance\<close>

lemma akernel_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s) \<and>
        scheduler_action s = resume_cur_thread \<and>
        is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s\<rbrace>
     (call_kernel e)
   \<lbrace>\<lambda>rv s. (invs s \<and> (ct_running s \<or> ct_idle s))\<rbrace>"
  unfolding call_kernel_def
  apply (wpsimp wp: activate_invs check_budget_invs charge_budget_invs is_schedulable_wp
                    update_time_stamp_invs hoare_drop_imps hoare_vcg_all_lift hoare_vcg_if_lift2)
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

(*FIXME: should have (scheduler_action s = resume_cur_thread) as a postcondition*)
lemma kernel_entry_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s) \<and>
        scheduler_action s = resume_cur_thread \<and>
        is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s\<rbrace>
  (kernel_entry e us) :: (user_context,unit) s_monad
  \<lbrace>\<lambda>rv s. invs s \<and> (ct_running s \<or> ct_idle s)\<rbrace>"
  apply (simp add: kernel_entry_def)
  apply (wp akernel_invs thread_set_invs_trivial thread_set_ct_in_state select_wp
            static_imp_wp hoare_vcg_disj_lift
         | clarsimp simp add: tcb_cap_cases_def)+
  done

lemma device_update_invs:
  "\<lbrace>invs and (\<lambda>s. (dom ds) \<subseteq>  (device_region s))\<rbrace> do_machine_op (device_memory_update ds)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: do_machine_op_def device_memory_update_def simpler_modify_def select_f_def
                   gets_def get_def bind_def valid_def return_def)
  apply (clarsimp simp: invs_def valid_state_def valid_irq_states_def valid_machine_state_def
                        cur_tcb_def pspace_respects_device_region_def cap_refs_respects_device_region_def
                  cong: user_mem_dom_cong
              simp del: split_paired_All)
  apply (clarsimp cong: device_mem_dom_cong simp:cap_range_respects_device_region_def
              simp del: split_paired_All split_paired_Ex)
  apply (intro conjI)
     apply fastforce
    apply fastforce
   apply (clarsimp simp del: split_paired_All split_paired_Ex)
   apply (drule_tac x = "(a,b)" in spec)
   apply (erule notE)
   apply (erule cte_wp_at_weakenE)
   apply clarsimp
   apply (fastforce split: if_splits) (* takes 20 secs *)
  apply (clarsimp simp: cur_sc_tcb_def)
  done

crunch device_state_inv[wp]: user_memory_update "\<lambda>ms. P (device_state ms)"

(* FIXME: move or delete *)
lemma dom_restrict_plus_eq:
  "a \<inter> b \<union> b = b"
  by auto

lemma user_memory_update[wp]:
  "\<lbrace>\<lambda>s. P (device_region s) \<rbrace> do_machine_op (user_memory_update a)
   \<lbrace>\<lambda>rv s. P (device_region s)\<rbrace>"
  by (simp add: do_machine_op_def user_memory_update_def simpler_modify_def
                valid_def bind_def gets_def return_def get_def select_f_def)

lemma do_user_op_invs:
  "\<lbrace>invs and ct_running\<rbrace>
   do_user_op f tc
   \<lbrace>\<lambda>_. invs and ct_running\<rbrace>"
  apply (simp add: do_user_op_def split_def)
  apply (wp device_update_invs)
  apply (wp select_wp dmo_invs | simp add:dom_restrict_plus_eq)+
  apply (clarsimp simp: user_memory_update_def simpler_modify_def
                        restrict_map_def invs_def cur_tcb_def
                 split: option.splits if_split_asm)
  apply (frule ptable_rights_imp_frame)
     apply fastforce+
  apply (clarsimp simp: valid_state_def device_frame_in_device_region)
  done

end
