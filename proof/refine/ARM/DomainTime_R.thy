(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DomainTime_R
imports
  ADT_H
begin

text \<open>Preservation of domain time remaining over kernel invocations;
        invariance of domain list validity
\<close>

context begin interpretation Arch . (*FIXME: arch_split*)

(* abstract and haskell have identical domain list fields *)
abbreviation
  valid_domain_list' :: "'a kernel_state_scheme \<Rightarrow> bool"
where
  "valid_domain_list' \<equiv> \<lambda>s. valid_domain_list_2 (ksDomSchedule s)"

lemmas valid_domain_list'_def = valid_domain_list_2_def

(* first, crunching valid_domain_list' over the kernel - it is never changed *)

crunches sendFaultIPC, handleFault, replyFromKernel, setDomain, sendSignal,
         finaliseCap, finaliseCap, capSwapForDelete
  for ksDomSchedule_inv[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: getObject_inv loadObject_default_inv crunch_wps hoare_vcg_all_lift whileM_inv
   simp: crunch_simps if_apply_def2 unless_def o_def assertE_def)

lemma finaliseSlot_ksDomSchedule_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s) \<rbrace> finaliseSlot param_a param_b \<lbrace>\<lambda>_ s. P (ksDomSchedule s)\<rbrace>"
  by (wp finaliseSlot_preservation | clarsimp)+

crunch ksDomSchedule_inv[wp]: invokeTCB "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps checkCap_inv finaliseSlot'_preservation simp: if_apply_def2 crunch_simps)

crunch ksDomSchedule_inv[wp]: doReplyTransfer "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps transferCapsToSlots_pres1
   simp: unless_def crunch_simps
   ignore: transferCapsToSlots)

crunch ksDomSchedule_inv[wp]: cancelBadgedSends "\<lambda>s. P (ksDomSchedule s)"
  (simp: filterM_mapM crunch_simps
     wp: crunch_wps hoare_unless_wp)

crunch ksDomSchedule_inv[wp]: createNewObjects "\<lambda>s. P (ksDomSchedule s)"
  (simp: crunch_simps zipWithM_x_mapM wp: crunch_wps hoare_unless_wp)

crunch ksDomSchedule_inv[wp]: preemptionPoint "\<lambda>s. P (ksDomSchedule s)"
  (simp: whenE_def ignore_del: preemptionPoint)

crunch ksDomSchedule_inv[wp]: performARMMMUInvocation "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps getObject_cte_inv getASID_wp
   simp: unless_def)

crunch ksDomSchedule_inv[wp]: performInvocation "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps zipWithM_x_inv cteRevoke_preservation mapME_x_inv_wp hoare_vcg_all_lift
   simp: unless_def crunch_simps filterM_mapM)

crunch ksDomSchedule_inv[wp]: schedule "\<lambda>s. P (ksDomSchedule s)"
  (ignore: setNextPC threadSet simp: crunch_simps bitmap_fun_defs
   wp: whileM_inv findM_inv hoare_drop_imps)

crunch ksDomSchedule_inv[wp]: activateThread "\<lambda>s. P (ksDomSchedule s)"
  (simp: crunch_simps wp: crunch_wps)

crunches receiveSignal, getNotification, receiveIPC, lookupReply, mcsIRQ
  for ksDomSchedule_inv[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: hoare_drop_imps simp: crunch_simps)

lemma handleRecv_ksDomSchedule_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s) \<rbrace> handleRecv b e \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  unfolding handleRecv_def
  by (rule hoare_pre)
     (wp hoare_drop_imps | simp add: crunch_simps split del: if_split | wpc)+

context
notes if_cong [cong]
begin
crunch ksDomSchedule_inv[wp]: handleEvent "\<lambda>s. P (ksDomSchedule s)"
  (wp: syscall_valid' crunch_wps ignore: syscall)
end

lemma callKernel_ksDomSchedule_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s) \<rbrace> callKernel e \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  unfolding callKernel_def
  by (rule hoare_pre)
     (wp | simp add: if_apply_def2)+


(* now we handle preservation of domain time remaining, which most of the kernel does not change *)

crunches setExtraBadge, cteInsert
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps)

crunch ksDomainTime[wp]: transferCapsToSlots "\<lambda>s. P (ksDomainTime s)"

crunches doIPCTransfer, possibleSwitchTo
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: constOnFailure)

crunches sendFaultIPC, handleFault, replyFromKernel
  for ksDomainTime_inv[wp]: "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps whileM_inv hoare_vcg_all_lift simp: crunch_simps)

crunch ksDomainTime_inv[wp]: setDomain "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch ksDomainTime_inv[wp]: sendSignal "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps gts_wp' simp: crunch_simps simp: unless_def o_def)

crunch ksDomainTime_inv[wp]: deleteASID "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps setObject_ksPSpace_only getObject_inv loadObject_default_inv
       updateObject_default_inv
   simp: crunch_simps)

crunch ksDomainTime_inv[wp]: finaliseCap "\<lambda>s. P (ksDomainTime s)"
  (simp: crunch_simps assertE_def
     wp: setObject_ksPSpace_only getObject_inv loadObject_default_inv crunch_wps hoare_vcg_all_lift)

crunch ksDomainTime_inv[wp]: cancelBadgedSends "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps setObject_ksPSpace_only getObject_inv loadObject_default_inv
       updateObject_default_inv hoare_unless_wp
   simp: filterM_mapM crunch_simps)

crunch ksDomainTime_inv[wp]: capSwapForDelete "\<lambda>s. P (ksDomainTime s)"
  (simp: crunch_simps)

lemma finaliseSlot_ksDomainTime_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomainTime s) \<rbrace> finaliseSlot param_a param_b \<lbrace>\<lambda>_ s. P (ksDomainTime s)\<rbrace>"
  by (wp finaliseSlot_preservation | clarsimp)+

crunch ksDomainTime_inv[wp]: invokeTCB "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps checkCap_inv finaliseSlot'_preservation simp: if_apply_def2 crunch_simps)

crunch ksDomainTime_inv[wp]: doReplyTransfer "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps transferCapsToSlots_pres1
   simp: crunch_simps
   ignore: transferCapsToSlots)

crunch ksDomainTime_inv[wp]: createNewObjects "\<lambda>s. P (ksDomainTime s)"
  (simp: crunch_simps zipWithM_x_mapM
   wp: crunch_wps hoare_unless_wp)

crunch ksDomainTime_inv[wp]: performARMMMUInvocation "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps getObject_cte_inv getASID_wp setObject_ksPSpace_only updateObject_default_inv
   simp: unless_def)

crunch ksDomainTime_inv[wp]: preemptionPoint "\<lambda>s. P (ksDomainTime s)"
  (simp: whenE_def ignore_del: preemptionPoint)

crunches activateThread, lookupReply
  for ksDomainTime_inv[wp]: "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps)

(* Does not hold for all of performInvocation (invokeSchedControlConfigure) *)
crunches invokeUntyped, invokeSchedContext, invokeCNode, performIRQControl, invokeIRQHandler
  for ksDomainTime_inv[wp]:  "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps zipWithM_x_inv cteRevoke_preservation mapME_x_inv_wp hoare_vcg_all_lift
   simp: unless_def crunch_simps filterM_mapM)

crunches receiveSignal, getNotification, receiveIPC
  for ksDomainTime_inv[wp]: "\<lambda>s. P (ksDomainTime s)"
  (wp: hoare_drop_imps simp: crunch_simps)

lemma handleRecv_ksDomainTime_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomainTime s) \<rbrace> handleRecv b e \<lbrace>\<lambda>_ s. P (ksDomainTime s) \<rbrace>"
  unfolding handleRecv_def
  by (rule hoare_pre)
     (wp hoare_drop_imps | simp add: crunch_simps split del: if_split | wpc)+

crunches doUserOp, getIRQState, chooseThread, handleYield
  for ksDomainTime_inv[wp]: "(\<lambda>s. P (ksDomainTime s))"
  (wp: crunch_wps select_wp)

crunches handleHypervisorFault
  for ksDomainTime_inv[wp]: "(\<lambda>s. P (ksDomainTime s))"
  (wp: syscall_valid' ignore: syscall)

lemma nextDomain_domain_time_left'[wp]:
  "\<lbrace> valid_domain_list' \<rbrace>
   nextDomain
   \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<rbrace>"
   unfolding nextDomain_def Let_def
   apply (wpsimp simp: valid_domain_list'_def dschLength_def)
   apply (simp only: all_set_conv_all_nth)
   apply (erule_tac x="Suc (ksDomScheduleIdx s) mod length (ksDomSchedule s)" in allE)
   apply clarsimp
   sorry (* FIXME RT: not true, need overflow protection in valid_domain_list_2. Also usToMs should be ms_to_us *)

(* if domain time is up, scheduler must run *)
abbreviation domain_time_sched :: "kernel_state \<Rightarrow> bool" where
  "domain_time_sched s \<equiv> ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread"

lemma handleInterrupt_valid_domain_time:
  "\<lbrace>\<lambda>s.  0 < ksDomainTime s \<rbrace>
   handleInterrupt i
   \<lbrace>\<lambda>_.  domain_time_sched\<rbrace>"
   apply (simp add: handleInterrupt_def)
   apply (case_tac "maxIRQ < i"; simp)
    subgoal by (wp hoare_false_imp) simp
   apply (rule_tac B="\<lambda>_ s. 0 < ksDomainTime s" in hoare_seq_ext[rotated])
    apply (rule hoare_pre, wp, simp)
   apply (rename_tac st)
   apply (case_tac st, simp_all)
    (* IRQSignal : no timer tick, trivial preservation of ksDomainTime *)
    apply (rule_tac Q="\<lambda>_ s. 0 < ksDomainTime s" in hoare_post_imp, clarsimp)
    apply (rule hoare_pre, (wp | wpc)+)
     apply (rule_tac Q="\<lambda>_ s. 0 < ksDomainTime s" in hoare_post_imp, clarsimp)
     apply wp
    (* IRQTimer : tick occurs *) (* IRQReserved : trivial *)
    apply (wp
          | clarsimp simp: handleReservedIRQ_def setReprogramTimer_def
          | wp (once) hoare_vcg_imp_lift)+
  done

crunches setNextInterrupt, getReprogramTimer
  for ksDomainTime_inv[wp]:  "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps
   simp: crunch_simps)

lemma scheduleChooseNewThread_domainTime[wp]:
  "\<lbrace> valid_domain_list' \<rbrace>
   scheduleChooseNewThread
   \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<rbrace>"
  unfolding scheduleChooseNewThread_def
  by (wpsimp simp: word_neq_0_conv)

lemma schedule_domain_time_left':
  "\<lbrace> valid_domain_list' and domain_time_sched \<rbrace>
   ThreadDecls_H.schedule
   \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<rbrace>"
  unfolding schedule_def
  apply wpsimp
  sorry (* FIXME RT: this might need code change
  apply (wpsimp wp: threadGet_wp)
       apply (rule_tac Q="\<lambda>_. valid_domain_list'" in hoare_post_imp, clarsimp)
       apply (wp | clarsimp | wp (once) hoare_drop_imps)+
  done *)

lemma handleEvent_ksDomainTime_inv:
  "\<lbrace>\<lambda>s. P (ksDomainTime  s) \<and> e \<noteq> Interrupt \<rbrace>
   handleEvent e
   \<lbrace>\<lambda>_ s. P (ksDomainTime s) \<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def)
             apply (wp hv_inv'|simp add: handleEvent_def cong: if_cong|wpc)+
  sorry (* FIXME RT: needs rephrasing or code change for invokeSchedControl *)

lemma callKernel_domain_time_left:
  "\<lbrace> (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) \<rbrace>
   callKernel e
   \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<rbrace>"
  including no_pre
  unfolding callKernel_def
  supply word_neq_0_conv[simp]
  apply (case_tac "e = Interrupt")
   apply (simp add: handleEvent_def)
   apply (rule hoare_pre)
   apply ((wp schedule_domain_time_left' handleInterrupt_valid_domain_time
          | wpc | simp)+)[1]
    apply (rule_tac Q="\<lambda>_ s. 0 < ksDomainTime s \<and> valid_domain_list' s" in hoare_post_imp)
     apply fastforce
  sorry (*
    apply wp
   apply simp
  (* non-interrupt case; may throw but does not touch ksDomainTime in handleEvent *)
  apply simp
  apply ((wp schedule_domain_time_left' handleInterrupt_valid_domain_time
          | simp add: if_apply_def2)+)[1]
   apply (rule_tac Q="\<lambda>_ s. valid_domain_list' s \<and> 0 < ksDomainTime s" in hoare_post_imp)
    apply fastforce
   apply wp
  apply simp
  apply (rule hoare_pre)
   apply (rule_tac Q="\<lambda>_ s. valid_domain_list' s \<and> 0 < ksDomainTime s"
            in NonDetMonadVCG.hoare_post_impErr[rotated 2], assumption)
    apply (wp handleEvent_ksDomainTime_inv | clarsimp)+
  done *)

end

end
